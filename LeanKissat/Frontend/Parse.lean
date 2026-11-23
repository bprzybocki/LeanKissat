import LeanKissat.Core.Basic
import LeanKissat.Util.U32Vec

/-!
# DIMACS parser (port of `parse.c`)

The C parser is a single function reading bytes through a 1 MiB buffer with `goto`s
between header and body states. Here it is a resumable byte-level state machine:
the input is read in 1 MiB chunks (`IO.FS.Stream.read`), each chunk is fed to a pure
function, and the parser state is carried across chunk boundaries. Header bytes go
through a generic (slow) `headerStep`; once the `p cnf` line is complete the remaining
bytes of every chunk are consumed by the tight tail-recursive `bodyLoop`, which keeps
its whole state in scalar arguments.

Parsed literals are passed to a `DimacsSink` (generic accumulator, specialised at the
call site), mirroring `kissat_reserve` after the header and `kissat_add` per literal.
`flatSink` collects them into a `FlatCnf` (flat little-endian `UInt32` buffer, viewable
as a `U32Vec`, `0`-terminated clauses).

Error messages and their line numbers match C exactly, including C's quirk that only
errors raised through the `NONL` macro update the line number: all other errors report
line `1` (C returns before `*lineno_ptr` is written; see `ParseError.plain`).

Not ported: embedded options (`EMBEDDED` is not compiled in the default build),
compressed input (`popen`), the `parse` profiler and `kissat_defrag_watches`.
-/

namespace LeanKissat.Frontend

variable {α : Type}

/-- Parsing modes (`strictness` in `parse.h`): `--relaxed`, default, `--strict`. -/
inductive Strictness where
  | relaxed
  | normal
  | pedantic
  deriving BEq, Repr, Inhabited, DecidableEq

/-- A parse error: line number as reported by C and the message. -/
structure ParseError where
  line : UInt64
  msg : String
  deriving Repr, Inhabited

namespace ParseError
/-- An error returned in C by a plain `return "..."`. C does not update `*lineno_ptr`
  there, which was initialised to `1`, so such errors always report line 1. -/
@[inline] def plain (msg : String) : ParseError := ⟨1, msg⟩
end ParseError

/-- Where parsed data goes. `header vars clauses` is called once after the `p cnf` line
  (C: `kissat_reserve (solver, variables)`), `add lit` for every literal and every
  terminating `0` (C: `kissat_add`). -/
structure DimacsSink (α : Type) where
  header : α → UInt32 → UInt64 → α
  add : α → Int32 → α

/-- The parsed `p cnf <variables> <clauses>` header. -/
structure DimacsHeader where
  variables : UInt32
  clauses : UInt64
  deriving Repr, Inhabited

/-- Result of a successful parse. -/
structure ParseResult (α : Type) where
  header : DimacsHeader
  /-- Largest variable index occurring in a clause (can exceed the header in
    `--relaxed` mode). C's `max_var` (used for the witness) is `header.variables`. -/
  maxIdx : UInt32
  /-- Number of clauses (terminating zeros) parsed. -/
  parsed : UInt64
  /-- Final line number (C `lineno`). -/
  lineno : UInt64
  /-- Number of bytes read (`file.bytes`). -/
  bytes : Nat
  sink : α

/-- Outcome of parsing: success, or an error together with the header if it had
  already been parsed (C prints the "parsed 'p cnf ...' header" message before it). -/
inductive ParseOutcome (α : Type) where
  | ok (r : ParseResult α)
  | error (e : ParseError) (header : Option DimacsHeader) (bytes : Nat)

/-! ## Parser state -/

-- Parser modes. Header modes are `< 20`, body modes `≥ 20`.
namespace Mode
def hLine : UInt8 := 0        -- start of a header line (loop head in C)
def hCR : UInt8 := 1          -- '\r' at start of header line
def hcStart : UInt8 := 2      -- after 'c', skipping blanks
def hcBody : UInt8 := 3       -- inside header comment
def hcCR : UInt8 := 4         -- '\r' inside header comment
def pSpace : UInt8 := 5       -- after 'p'
def pC : UInt8 := 6           -- after 'p ' (blanks unless pedantic), expect 'c'
def pN : UInt8 := 7           -- expect 'n'
def pF : UInt8 := 8           -- expect 'f'
def pSpace2 : UInt8 := 9      -- expect ' ' after 'p cnf'
def pVarStart : UInt8 := 10   -- expect first digit of variables
def pVars : UInt8 := 11       -- digits of variables
def pVarsCR : UInt8 := 12     -- '\r' after variables
def pClsStart : UInt8 := 13   -- expect first digit of clauses
def pCls : UInt8 := 14        -- digits of clauses
def pClsWS : UInt8 := 15      -- blanks after clauses
def pClsCR : UInt8 := 16      -- '\r' after clauses
def bStart : UInt8 := 20      -- body: between tokens
def bCR : UInt8 := 21         -- body: '\r'
def bComment : UInt8 := 22    -- body: comment between tokens
def bMinus : UInt8 := 23      -- body: after '-'
def bDigits : UInt8 := 24     -- body: digits of a literal
def bLitCR : UInt8 := 25      -- body: '\r' terminating a literal
def bLitComment : UInt8 := 26 -- body: comment terminating a literal
end Mode

/-- Resumable parser state (all C locals of `parse_dimacs`). -/
structure PState where
  mode : UInt8 := Mode.hLine
  lineno : UInt64 := 1
  first : Bool := true
  variables : UInt64 := 0
  clauses : UInt64 := 0
  parsed : UInt64 := 0
  idx : UInt64 := 0
  neg : Bool := false
  /-- C `lit != 0`, i.e. the last added literal was not a terminating zero. -/
  lastNonZero : Bool := false
  maxIdx : UInt64 := 0
  /-- Header complete. -/
  headerDone : Bool := false
  deriving Inhabited

/-- Configuration (constant during parsing). -/
structure PConfig where
  pedantic : Bool
  relaxed : Bool

/-- Result of feeding bytes. -/
inductive Step (α : Type) where
  | cont (st : PState) (acc : α)
  /-- error before the header was complete -/
  | err (e : ParseError)
  /-- error after the header `p cnf variables clauses` -/
  | errH (e : ParseError) (variables clauses : UInt64)

def nl : UInt8 := 10
def cr : UInt8 := 13
@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
@[inline] def isBlank (c : UInt8) : Bool := c == 32 || c == 9

def TRY_RELAXED : String := "(try '--relaxed' parsing)"
def CR_ERR : String := "expected new-line after carriage-return"

/-- `EXTERNAL_MAX_VAR` as `UInt64`. -/
def maxVar64 : UInt64 := (EXTERNAL_MAX_VAR : Nat).toUInt64

def uint64Max : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- `10 * v + d` if it does not exceed `max` (C's two-step overflow check
  `max / 10 < v` / `max - d < 10 * v`), assuming `v ≤ max`. -/
@[inline] def accumDigit (max v : UInt64) (d : UInt8) : Option UInt64 :=
  if max / 10 < v then none
  else
    let v := v * 10
    let d := (d - 48).toUInt64
    if max - d < v then none else some (v + d)

/-- Header byte step. `nonl` is the line number reported by C's `NONL` macro for the
  current byte (the line number *before* counting this byte's new-line). -/
@[specialize] def headerStep (cfg : PConfig) (header : α → UInt32 → UInt64 → α) (st : PState) (acc : α)
    (ch : UInt8) : Step α :=
  let nonl := st.lineno
  let st := if ch == nl then { st with lineno := st.lineno + 1 } else st
  let m := st.mode
  if m == Mode.hLine then
    if ch == 112 /- 'p' -/ then .cont { st with mode := Mode.pSpace } acc
    else
      let st := { st with first := false }
      if ch == cr then .cont { st with mode := Mode.hCR } acc
      else if ch == nl then
        if cfg.pedantic then .err ⟨nonl, "unexpected empty line"⟩ else .cont st acc
      else if ch == 99 /- 'c' -/ then .cont { st with mode := Mode.hcStart } acc
      else .err (.plain "expected 'c' or 'p' at start of line")
  else if m == Mode.hCR then
    if ch != nl then .err (.plain CR_ERR)
    else if cfg.pedantic then .err ⟨nonl, "unexpected empty line"⟩
    else .cont { st with mode := Mode.hLine } acc
  else if m == Mode.hcStart then
    if ch == nl then .cont { st with mode := Mode.hLine } acc
    else if ch == cr then .cont { st with mode := Mode.hcCR } acc
    else if isBlank ch then .cont st acc
    else .cont { st with mode := Mode.hcBody } acc
  else if m == Mode.hcBody then
    if ch == nl then .cont { st with mode := Mode.hLine } acc
    else if ch == cr then .cont { st with mode := Mode.hcCR } acc
    else .cont st acc
  else if m == Mode.hcCR then
    if ch != nl then .err (.plain CR_ERR) else .cont { st with mode := Mode.hLine } acc
  else if m == Mode.pSpace then
    if ch != 32 then .err ⟨nonl, "expected space after 'p'"⟩
    else .cont { st with mode := Mode.pC } acc
  else if m == Mode.pC then
    if !cfg.pedantic && isBlank ch then .cont st acc
    else if ch != 99 then .err ⟨nonl, "expected 'c' after 'p '"⟩
    else .cont { st with mode := Mode.pN } acc
  else if m == Mode.pN then
    if ch != 110 then .err ⟨nonl, "expected 'n' after 'p c'"⟩
    else .cont { st with mode := Mode.pF } acc
  else if m == Mode.pF then
    -- (sic) C message says 'n'
    if ch != 102 then .err ⟨nonl, "expected 'n' after 'p cn'"⟩
    else .cont { st with mode := Mode.pSpace2 } acc
  else if m == Mode.pSpace2 then
    if ch != 32 then .err ⟨nonl, "expected space after 'p cnf'"⟩
    else .cont { st with mode := Mode.pVarStart } acc
  else if m == Mode.pVarStart then
    if !cfg.pedantic && isBlank ch then .cont st acc
    else if !isDigit ch then .err ⟨nonl, "expected digit after 'p cnf '"⟩
    else .cont { st with mode := Mode.pVars, variables := (ch - 48).toUInt64 } acc
  else if m == Mode.pVars then
    if isDigit ch then
      match accumDigit maxVar64 st.variables ch with
      | some v => .cont { st with variables := v } acc
      | none => .err (.plain "maximum variable too large")
    else if ch == cr then .cont { st with mode := Mode.pVarsCR } acc
    else if ch == nl then .err ⟨nonl, "unexpected new-line after maximum variable"⟩
    else if ch != 32 then .err (.plain "expected space after maximum variable")
    else .cont { st with mode := Mode.pClsStart } acc
  else if m == Mode.pVarsCR then
    if ch != nl then .err (.plain CR_ERR)
    else .err ⟨nonl, "unexpected new-line after maximum variable"⟩
  else if m == Mode.pClsStart then
    if !cfg.pedantic && isBlank ch then .cont st acc
    else if !isDigit ch then .err (.plain "expected number of clauses after maximum variable")
    else .cont { st with mode := Mode.pCls, clauses := (ch - 48).toUInt64 } acc
  else if m == Mode.pCls || m == Mode.pClsWS then
    if m == Mode.pCls && isDigit ch then
      match accumDigit uint64Max st.clauses ch with
      | some v => .cont { st with clauses := v } acc
      | none => .err (.plain "number of clauses too large")
    else if !cfg.pedantic && isBlank ch then .cont { st with mode := Mode.pClsWS } acc
    else if ch == cr then .cont { st with mode := Mode.pClsCR } acc
    else if ch != nl then .err (.plain "expected new-line after parsing number of clauses")
    else
      .cont { st with mode := Mode.bStart, headerDone := true }
        (header acc st.variables.toUInt32 st.clauses)
  else if m == Mode.pClsCR then
    if ch != nl then .err (.plain CR_ERR)
    else
      .cont { st with mode := Mode.bStart, headerDone := true }
        (header acc st.variables.toUInt32 st.clauses)
  else .err (.plain "internal parser error: unexpected header mode")

/-- Checks done by C after a literal has been terminated; `nonl` is the line number
  `NONL` reports. `none` if the literal is accepted. -/
@[inline] def litError? (cfg : PConfig) (variables clauses parsed idx nonl : UInt64) :
    Option ParseError :=
  if !cfg.relaxed && idx > variables then
    some ⟨nonl, "maximum variable index exceeded " ++ TRY_RELAXED⟩
  else if idx == 0 && !cfg.relaxed && parsed == clauses then
    some (.plain ("too many clauses " ++ TRY_RELAXED))
  else none

/-- External literal from sign and index (`idx ≤ EXTERNAL_MAX_VAR`). -/
@[inline] def mkLit (neg : Bool) (idx : UInt64) : Int32 :=
  let l := idx.toUInt32.toInt32
  if neg then -l else l

/-- Hot loop over the body bytes `buf[i:]`. All state lives in arguments. Returns
  `.cont` with the state at the end of the chunk, or `.err`. -/
@[specialize] def bodyLoop (cfg : PConfig) (add : α → Int32 → α) (variables clauses : UInt64)
    (buf : ByteArray) (i : Nat) (mode : UInt8) (idx : UInt64) (neg : Bool)
    (lineno parsed : UInt64) (lastNonZero : Bool) (maxIdx : UInt64) (acc : α) : Step α :=
  if h : i < buf.size then
    let ch := buf[i]
    let nonl := lineno
    let lineno := if ch == nl then lineno + 1 else lineno
    if mode == Mode.bDigits && isDigit ch then
      match accumDigit maxVar64 idx ch with
      | some v => bodyLoop cfg add variables clauses buf (i+1) mode v neg lineno parsed
          lastNonZero maxIdx acc
      | none => .errH (.plain "variable index too large") variables clauses
    else if (mode == Mode.bDigits && (ch == 32 || ch == nl || ch == 9)) ||
        ((mode == Mode.bLitComment || mode == Mode.bLitCR) && ch == nl) then
      -- the literal terminated by this byte: C's checks, then `kissat_add`
      match litError? cfg variables clauses parsed idx nonl with
      | some e => .errH e variables clauses
      | none =>
        let l := mkLit neg idx
        let parsed := if idx == 0 then parsed + 1 else parsed
        let maxIdx := if idx > maxIdx then idx else maxIdx
        bodyLoop cfg add variables clauses buf (i+1) Mode.bStart 0 false lineno parsed
          (idx != 0) maxIdx (add acc l)
    else if mode == Mode.bDigits then
      if ch == cr then
        bodyLoop cfg add variables clauses buf (i+1) Mode.bLitCR idx neg lineno parsed
          lastNonZero maxIdx acc
      else if ch == 99 then
        bodyLoop cfg add variables clauses buf (i+1) Mode.bLitComment idx neg lineno parsed
          lastNonZero maxIdx acc
      else .errH (.plain "expected white space after literal") variables clauses
    else if mode == Mode.bStart then
      if ch == 32 || ch == nl || ch == 9 then
        bodyLoop cfg add variables clauses buf (i+1) mode idx neg lineno parsed
          lastNonZero maxIdx acc
      else if isDigit ch then
        bodyLoop cfg add variables clauses buf (i+1) Mode.bDigits (ch - 48).toUInt64 false
          lineno parsed lastNonZero maxIdx acc
      else if ch == 45 /- '-' -/ then
        bodyLoop cfg add variables clauses buf (i+1) Mode.bMinus 0 true lineno parsed
          lastNonZero maxIdx acc
      else if ch == cr then
        bodyLoop cfg add variables clauses buf (i+1) Mode.bCR idx neg lineno parsed
          lastNonZero maxIdx acc
      else if ch == 99 then
        bodyLoop cfg add variables clauses buf (i+1) Mode.bComment idx neg lineno parsed
          lastNonZero maxIdx acc
      else .errH (.plain "expected digit or '-'") variables clauses
    else if mode == Mode.bMinus then
      if ch == nl then .errH ⟨nonl, "unexpected new-line after '-'"⟩ variables clauses
      else if !isDigit ch then .errH (.plain "expected digit after '-'") variables clauses
      else if ch == 48 then .errH (.plain "expected non-zero digit after '-'") variables clauses
      else
        bodyLoop cfg add variables clauses buf (i+1) Mode.bDigits (ch - 48).toUInt64 true
          lineno parsed lastNonZero maxIdx acc
    else if mode == Mode.bComment then
      let mode := if ch == nl then Mode.bStart else mode
      bodyLoop cfg add variables clauses buf (i+1) mode idx neg lineno parsed
        lastNonZero maxIdx acc
    else if mode == Mode.bLitComment then
      bodyLoop cfg add variables clauses buf (i+1) mode idx neg lineno parsed
        lastNonZero maxIdx acc
    else if mode == Mode.bCR then
      if ch != nl then .errH (.plain CR_ERR) variables clauses
      else
        bodyLoop cfg add variables clauses buf (i+1) Mode.bStart idx neg lineno parsed
          lastNonZero maxIdx acc
    else if mode == Mode.bLitCR then
      .errH (.plain CR_ERR) variables clauses
    else .errH (.plain "internal parser error: unexpected body mode") variables clauses
  else
    .cont { mode, lineno, variables, clauses, parsed, idx, neg, lastNonZero, maxIdx,
            first := false, headerDone := true } acc
termination_by buf.size - i

/-- Feed the bytes `buf[i:]`. -/
@[specialize] def feed (cfg : PConfig) (header : α → UInt32 → UInt64 → α) (add : α → Int32 → α) (buf : ByteArray) (i : Nat)
    (st : PState) (acc : α) : Step α :=
  if h : i < buf.size then
    if st.mode ≥ Mode.bStart then
      bodyLoop cfg add st.variables st.clauses buf i st.mode st.idx st.neg st.lineno
        st.parsed st.lastNonZero st.maxIdx acc
    else
      match headerStep cfg header st acc buf[i] with
      | .cont st acc => feed cfg header add buf (i+1) st acc
      | r => r
  else .cont st acc
termination_by buf.size - i

/-- End of the body (C: after the main loop): trailing zero / missing clause checks. -/
def finishBody (cfg : PConfig) (st : PState) (acc : α) : Step α :=
  if st.lastNonZero then .errH (.plain "trailing zero missing") st.variables st.clauses
  else if !cfg.relaxed && st.parsed < st.clauses then
    if st.parsed + 1 == st.clauses then .errH (.plain ("one clause missing " ++ TRY_RELAXED)) st.variables st.clauses
    else .errH (.plain ("more than one clause missing " ++ TRY_RELAXED)) st.variables st.clauses
  else .cont st acc

/-- Handle end-of-file in the given state (C reads `EOF`). -/
@[specialize] def atEOF (cfg : PConfig) (add : α → Int32 → α) (st : PState) (acc : α) : Step α :=
  let m := st.mode
  let lineno := st.lineno
  if m == Mode.hLine then
    .err (.plain (if st.first then "empty file" else "end-of-file before header"))
  else if m == Mode.hCR || m == Mode.hcCR || m == Mode.pVarsCR || m == Mode.pClsCR
      || m == Mode.bCR || m == Mode.bLitCR then
    if m ≥ Mode.bStart then .errH (.plain CR_ERR) st.variables st.clauses
    else .err (.plain CR_ERR)
  else if m == Mode.hcStart || m == Mode.hcBody then
    .err (.plain "end-of-file in header comment")
  else if m == Mode.pSpace then .err ⟨lineno, "expected space after 'p'"⟩
  else if m == Mode.pC then .err ⟨lineno, "expected 'c' after 'p '"⟩
  else if m == Mode.pN then .err ⟨lineno, "expected 'n' after 'p c'"⟩
  else if m == Mode.pF then .err ⟨lineno, "expected 'n' after 'p cn'"⟩
  else if m == Mode.pSpace2 then .err ⟨lineno, "expected space after 'p cnf'"⟩
  else if m == Mode.pVarStart then .err ⟨lineno, "expected digit after 'p cnf '"⟩
  else if m == Mode.pVars then
    .err (.plain "unexpected end-of-file while parsing maximum variable")
  else if m == Mode.pClsStart then
    .err (.plain "expected number of clauses after maximum variable")
  else if m == Mode.pCls then
    .err (.plain "unexpected end-of-file while parsing number of clauses")
  else if m == Mode.pClsWS then
    .err (.plain "unexpected end-of-file after parsing number of clauses")
  else if m == Mode.bStart then finishBody cfg st acc
  else if m == Mode.bComment then
    if cfg.pedantic then .errH (.plain "unexpected end-of-file in comment after header") st.variables st.clauses
    else finishBody cfg st acc
  else if m == Mode.bMinus then .errH (.plain "unexpected end-of-file after '-'") st.variables st.clauses
  else if m == Mode.bDigits || m == Mode.bLitComment then
    if cfg.pedantic then
      if m == Mode.bLitComment then
        .errH (.plain "unexpected end-of-file in comment after literal") st.variables st.clauses
      else if st.idx != 0 then .errH (.plain "unexpected end-of-file after literal") st.variables st.clauses
      else .errH (.plain "unexpected end-of-file after trailing zero") st.variables st.clauses
    else
      match litError? cfg st.variables st.clauses st.parsed st.idx lineno with
      | some e => .errH e st.variables st.clauses
      | none =>
        let st := { st with
          parsed := if st.idx == 0 then st.parsed + 1 else st.parsed
          lastNonZero := st.idx != 0
          maxIdx := if st.idx > st.maxIdx then st.idx else st.maxIdx
          mode := Mode.bStart }
        finishBody cfg st (add acc (mkLit st.neg st.idx))
  else .errH (.plain "internal parser error: unexpected mode at end-of-file") st.variables st.clauses

/-- Size of read chunks (C: `size_buffer = 1 << 20`). -/
def chunkSize : Nat := 1 <<< 20

/-- Upper bound on the number of chunks read; only there to make the read loop
  structurally recursive (2^44 chunks = 16 EiB, never reached). -/
def maxChunks : Nat := 1 <<< 44

/-- Turn a final `Step` into a `ParseOutcome`. -/
def Step.toOutcome (r : Step α) (bytes : Nat) : ParseOutcome α :=
  match r with
  | .err e => .error e none bytes
  | .errH e v c => .error e (some ⟨v.toUInt32, c⟩) bytes
  | .cont fin res =>
    .ok { header := ⟨fin.variables.toUInt32, fin.clauses⟩, maxIdx := fin.maxIdx.toUInt32,
          parsed := fin.parsed, lineno := fin.lineno, bytes, sink := res }

/-- Read loop: read a chunk, feed it, recurse; at end-of-file run `atEOF`. Written as
  explicit (structural, fuel-bounded) recursion rather than a `for` loop with mutable
  variables: in the latter the early `return` keeps the previous accumulator alive
  across `feed`, which made every chunk copy the whole accumulator. -/
@[specialize] def readLoop (stream : IO.FS.Stream) (cfg : PConfig)
    (header : α → UInt32 → UInt64 → α) (add : α → Int32 → α) :
    (fuel : Nat) → PState → α → Nat → IO (ParseOutcome α)
  | 0, _, _, bytes => pure (.error (.plain "input too large") none bytes)
  | fuel+1, st, acc, bytes => do
    -- C (`fread`) treats read errors (e.g. reading a directory) as end-of-file
    let buf ← try stream.read chunkSize.toUSize catch _ => pure .empty
    if buf.size == 0 then
      return (atEOF cfg add st acc).toOutcome bytes
    let bytes := bytes + buf.size
    match feed cfg header add buf 0 st acc with
    | .cont st acc => readLoop stream cfg header add fuel st acc bytes
    | r => return r.toOutcome bytes

/-- Port of `kissat_parse_dimacs` / `parse_dimacs` (parse.c): parse DIMACS from a stream,
  reading it in 1 MiB chunks, feeding the header to `header` and literals to `add`. -/
@[specialize] def parseStreamWith (stream : IO.FS.Stream) (strict : Strictness)
    (header : α → UInt32 → UInt64 → α) (add : α → Int32 → α) (init : α) : IO (ParseOutcome α) :=
  let cfg : PConfig := { pedantic := strict == .pedantic, relaxed := strict == .relaxed }
  readLoop stream cfg header add maxChunks {} init 0

/-- Parse a pure byte array (e.g. for tests); same semantics as `parseStream`. -/
@[specialize] def parseBytesWith (bytes : ByteArray) (strict : Strictness)
    (header : α → UInt32 → UInt64 → α) (add : α → Int32 → α) (init : α) : ParseOutcome α :=
  let cfg : PConfig := { pedantic := strict == .pedantic, relaxed := strict == .relaxed }
  match feed cfg header add bytes 0 {} init with
  | .cont st acc => (atEOF cfg add st acc).toOutcome bytes.size
  | r => r.toOutcome bytes.size

/-- `parseStreamWith` with a `DimacsSink` (inlined so that the sink functions are
  specialised into the parser loops). -/
@[inline] def parseStream (stream : IO.FS.Stream) (strict : Strictness) (sink : DimacsSink α)
    (init : α) : IO (ParseOutcome α) :=
  parseStreamWith stream strict sink.header sink.add init

/-- `parseBytesWith` with a `DimacsSink`. -/
@[inline] def parseBytes (bytes : ByteArray) (strict : Strictness) (sink : DimacsSink α)
    (init : α) : ParseOutcome α :=
  parseBytesWith bytes strict sink.header sink.add init

/-! ## Flat clause representation -/

/-- All literals in input order, each clause terminated by `0`, stored as the
  two's-complement bit patterns of the `Int32` literals. -/
structure FlatCnf where
  /-- little-endian bytes of the literals (the `U32Vec` encoding) -/
  data : ByteArray := .empty
  numLits : Nat := 0
  numClauses : Nat := 0
  hsize : data.size = 4 * numLits := by simp

instance : Inhabited FlatCnf := ⟨{}⟩

/-- The literals as a `U32Vec` (no copy). -/
@[inline] def FlatCnf.lits (f : FlatCnf) : U32Vec := ⟨f.data, f.numLits, by rw [f.hsize]; exact Nat.le_refl _⟩

/-- Append a literal (`0` ends a clause). Pushes the four bytes directly (cheaper
  than `U32Vec.push`, which grows the buffer and then overwrites it). -/
@[inline] def FlatCnf.add (f : FlatCnf) (l : Int32) : FlatCnf :=
  let v := l.toUInt32
  { data := (((f.data.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push
      (v >>> 24).toUInt8
    numLits := f.numLits + 1
    numClauses := if l == 0 then f.numClauses + 1 else f.numClauses
    hsize := by simp [ByteArray.size_push, f.hsize]; omega }

/-- Sink collecting a `FlatCnf`. -/
@[inline] def flatSink : DimacsSink FlatCnf where
  header := fun f _ _ => f
  add := FlatCnf.add

/-- Sink that ignores everything (parse-only benchmarking). -/
def nullSink : DimacsSink Unit where
  header := fun _ _ _ => ()
  add := fun _ _ => ()

/-- Literal `i` of a `FlatCnf`. -/
@[inline] def FlatCnf.lit! (f : FlatCnf) (i : Nat) : Int32 := (f.lits.get! i).toInt32

/-- Convert to an array of clauses (`0` terminators removed). -/
def FlatCnf.toClauses (f : FlatCnf) : Array (Array Int32) := Id.run do
  let mut res : Array (Array Int32) := Array.emptyWithCapacity f.numClauses
  let mut cur : Array Int32 := #[]
  for i in [0:f.lits.size] do
    let l := f.lit! i
    if l == 0 then
      res := res.push cur
      cur := #[]
    else cur := cur.push l
  return res

/-- Render a parse error like `application.c`: `<path>:<line>: parse error: <msg>`. -/
def ParseError.render (e : ParseError) (path : String) : String :=
  s!"{path}:{e.line}: parse error: {e.msg}"

/-- Open `path` (or read `<stdin>` if `none`) and parse it. -/
@[specialize] def parseFileWith (path : Option String) (strict : Strictness) (header : α → UInt32 → UInt64 → α) (add : α → Int32 → α)
    (init : α) : IO (ParseOutcome α) := do
  match path with
  | none => parseStreamWith (← IO.getStdin) strict header add init
  | some p =>
    let h ← IO.FS.Handle.mk p .read
    parseStreamWith (IO.FS.Stream.ofHandle h) strict header add init

/-- `parseFileWith` with a `DimacsSink`. -/
@[inline] def parseFile (path : Option String) (strict : Strictness) (sink : DimacsSink α)
    (init : α) : IO (ParseOutcome α) :=
  parseFileWith path strict sink.header sink.add init

end LeanKissat.Frontend
