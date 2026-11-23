import LeanKissat.Core.OptionsTable
import LeanKissat.Frontend.Parse

/-!
# Command line options (port of `options.c`, `config.c`, `format.c` (values) and the
option handling part of `application.c`)

The port corresponds to a default build *without* proof support and *without*
compression support (C: `NPROOFS` and no `KISSAT_HAS_COMPRESSION`), i.e. second file
arguments are rejected and `-f` forces reading files which look compressed.
Not supported (see `unsupportedOptions`): `-o <file>` (writing the simplified DIMACS),
proof options (`--binary`, `<proof>` argument), `--embedded`, `-l` (no `LOGGING`).
-/

namespace LeanKissat.Frontend

open LeanKissat

/-- C `INT_MAX` / `INT_MIN`. -/
def INT_MAX : Int := 2147483647
def INT_MIN : Int := -2147483648

/-- An option table entry (`opt` in `options.h`). -/
structure Opt where
  name : String
  value : Nat
  low : Nat
  high : Nat
  description : String
  deriving Inhabited, Repr

/-- All options in table (alphabetical) order. -/
def optTable : Array Opt :=
  optionTable.map fun (n, v, l, h, d) => ⟨n, v, l, h, d⟩

/-- Port of `kissat_options_has` (options.c). -/
def optionsHas (name : String) : Option Opt := optTable.find? (·.name == name)

/-- Get an option value by name (`kissat_options_get`, `0` if unknown). -/
def _root_.LeanKissat.Options.getD (o : Options) (name : String) : Nat := (o.get? name).getD 0

/-- Port of `kissat_options_set_opt` / `kissat_set_option`: set with clamping to the
  option range. Unknown names are ignored (C returns 0). -/
def _root_.LeanKissat.Options.setClamped (o : Options) (name : String) (value : Int) : Options :=
  match optionsHas name with
  | none => o
  | some opt =>
    let v : Nat := if value < opt.low then opt.low else if value > opt.high then opt.high
      else value.toNat
    (o.set? name v).getD o

/-! ## Option values -/

/-- `max = -(unsigned) INT_MIN = 2^31` in `kissat_parse_option_value`. -/
private def maxAbs : Nat := 2147483648

private def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- Digit loop of `kissat_parse_option_value`: returns accumulated value and rest
  (starting with the first non-digit). -/
private def parseDigits (res : Nat) : List Char → Option (Nat × List Char)
  | c :: cs =>
    if isDigitC c then
      if maxAbs / 10 < res then none
      else
        let res := res * 10
        let d := digitVal c
        if maxAbs - d < res then none
        else
          let res := res + d
          if res == 0 then none -- invalid '00'
          else parseDigits res cs
    else some (res, c :: cs)
  | [] => some (res, [])

/-- Repeated multiplication with C's overflow check `max / base < res`. Division by
  zero yields `0` as on ARM64 (C: undefined; only reachable for base `0`). -/
private def mulPow (res base : Nat) : Nat → Option Nat
  | 0 => some res
  | k+1 => if maxAbs / base < res then none else mulPow (res * base) base k

/-- Port of `kissat_parse_option_value` (options.c): accepts `true`, `false`, and
  `[-]<digits>[e<digit>|^<digits>]` with C's quirks, range `[INT_MIN, INT_MAX]`. -/
def parseOptionValue (s : String) : Option Int :=
  if s == "true" then some 1
  else if s == "false" then some 0
  else
    let cs := s.toList
    let (neg, cs) := match cs with
      | '-' :: r => (true, r)
      | r => (false, r)
    match cs with
    | c :: cs =>
      if !isDigitC c then none else
      match parseDigits (digitVal c) cs with
      | none => none
      | some (res, rest) =>
        let res? : Option Nat :=
          match rest with
          | [] => some res
          | 'e' :: rest =>
            match rest with
            | d :: rest =>
              if !isDigitC d then none
              else if res != 0 then
                if !rest.isEmpty then none -- exactly one digit
                else mulPow res 10 (digitVal d)
              else if rest.all isDigitC then some res -- '0e123123'
              else none
            | [] => none
          | '^' :: rest =>
            match rest with
            | d :: rest =>
              if !isDigitC d then none
              else
                let base := res
                let exp? : Option Nat :=
                  if base < 2 then
                    if rest.all isDigitC then some (digitVal d) else none
                  else match rest with
                    | [] => some (digitVal d)
                    | d2 :: rest2 =>
                      if isDigitC d2 then
                        if !rest2.isEmpty then none -- at most two digits
                        else
                          let e := digitVal d * 10 + digitVal d2
                          if e == 0 then none else some e -- '2^00' invalid
                      else none
                match exp? with
                | none => none
                | some exp =>
                  if exp != 0 then mulPow res base (exp - 1)
                  else if base != 0 then some 1 -- '3^0'
                  else none -- '0^0'
            | [] => none
          | _ => none
        match res? with
        | none => none
        | some res =>
          if !neg && res == maxAbs then none
          else some (if neg then -(res : Int) else res)
    | [] => none

/-- Port of `kissat_parse_option_name` (options.c): if `arg` is `--<name>=<val>` return
  `<val>`, if it is `--no-<name>` return `"0"`. -/
def parseOptionName (arg name : String) : Option String :=
  if !arg.startsWith "--" then none
  else
    let p := arg.drop 2
    if p.startsWith "no-" then
      if p.drop 3 == name then some "0" else none
    else if p.startsWith (name ++ "=") then some (p.drop (name.length + 1)).toString
    else none

/-- `kissat_options_max_name_buffer_size`. -/
def maxNameBufferSize : Nat := 32

/-- Port of `kissat_options_parse_arg` (options.c): `--name=value` (range checked),
  `--name` (value 1) and `--no-name` (value 0). -/
def optionsParseArg (arg : String) : Option (String × Int) :=
  if !arg.startsWith "--" then none
  else
    let name := (arg.drop 2).toString
    match name.splitOn "=" with
    | [_] =>
      if name.startsWith "no-" then
        let n := (name.drop 3).toString
        match optionsHas n with
        | some o => if o.low > 0 then none else some (n, 0)
        | none => none
      else
        match optionsHas name with
        | some o => if o.high < 1 then none else some (name, 1)
        | none => none
    | n :: _ =>
      if n.length ≥ maxNameBufferSize then none
      else
        match optionsHas n with
        | none => none
        | some o =>
          match parseOptionValue (name.drop (n.length + 1)).toString with
          | none => none
          | some v => if v < o.low || v > o.high then none else some (n, v)
    | [] => none

/-! ## Configurations (`config.c`) -/

def TARGET_SAT : Nat := 2
def RESTARTINT_SAT : Nat := 50
def STABLE_UNSAT : Nat := 0

/-- Port of `kissat_has_configuration`. -/
def hasConfiguration (name : String) : Bool :=
  name == "basic" || name == "default" || name == "plain" || name == "sat" || name == "unsat"

private def setPlainOptions (o : Options) : Options :=
  [("bumpreasons", 0), ("chrono", 0), ("compact", 0), ("eagersubsume", 0),
   ("jumpreasons", 0), ("otfs", 0), ("preprocess", 0), ("reorder", 0), ("rephase", 0),
   ("restartreusetrail", 0), ("simplify", 0), ("stable", 2), ("tumble", 0)].foldl
    (fun o (n, v) => o.setClamped n v) o

/-- Port of `kissat_set_configuration`. -/
def setConfiguration (o : Options) (name : String) : Options :=
  if name == "basic" then
    ((setPlainOptions o).setClamped "restart" 0 |>.setClamped "reduce" 0).setClamped "minimize" 0
  else if name == "plain" then setPlainOptions o
  else if name == "sat" then
    (o.setClamped "target" TARGET_SAT).setClamped "restartint" RESTARTINT_SAT
  else if name == "unsat" then o.setClamped "stable" STABLE_UNSAT
  else o

/-- Port of `kissat_configuration_usage`. -/
def configurationUsage : List String :=
  let fmt (n d : String) := "  --" ++ n.pushn ' ' (8 - n.length) ++ " " ++ d
  [ fmt "basic" "basic CDCL solving ('--plain' but no restarts, minimize, reduce)",
    fmt "default" "default configuration",
    fmt "plain" "plain CDCL solving without advanced techniques",
    fmt "sat" s!"target satisfiable instances ('--target={TARGET_SAT} --restartint={RESTARTINT_SAT}')",
    fmt "unsat" s!"target unsatisfiable instances ('--stable={STABLE_UNSAT}')" ]

/-! ## Value formatting (`format.c`) -/

private def isPow2 (w : Nat) : Bool := w != 0 && (w &&& (w - 1)) == 0

private def countTrailingZeros10 (w : Nat) (fuel : Nat) : Nat × Nat :=
  match fuel with
  | 0 => (w, 0)
  | f+1 => if w % 10 == 0 && w != 0 then
      let (r, l) := countTrailingZeros10 (w / 10) f
      (r, l + 1)
    else (w, 0)

/-- Port of `format_count` (format.c). -/
def formatCount (w : Nat) : String :=
  if w ≥ 128 && isPow2 w then s!"2^{w.log2}"
  else if w ≥ 1000 && w % 1000 == 0 then
    let (r, l) := countTrailingZeros10 w 64
    s!"{r}e{l}"
  else toString w

/-- Port of `kissat_format_value` (format.c). -/
def formatValue (boolean : Bool) (value : Int) : String :=
  if boolean then (if value != 0 then "true" else "false")
  else if value == INT_MAX then "INT_MAX"
  else if value == INT_MIN then "INT_MIN"
  else if value < 0 then "-" ++ formatCount value.natAbs
  else formatCount value.toNat

/-- `FORMAT_OPTION_LIMIT`. -/
private def formatOptionLimit (v : Nat) : String :=
  if (v : Int) == INT_MAX then "." else formatValue false v

/-- Port of `kissat_options_usage` (options.c). -/
def optionsUsage : List String :=
  optTable.toList.map fun o =>
    let b := o.low == 0 && o.high == 1
    let buffer := if b then s!"--{o.name}=<bool>"
      else s!"--{o.name}={formatOptionLimit o.low}..{formatOptionLimit o.high}"
    "  " ++ buffer.pushn ' ' (26 - buffer.length) ++ " " ++
      s!"{o.description} [{formatValue b o.value}]"

/-- Port of `kissat_print_option_range_list` (options.c). -/
def optionRangeList : List String :=
  let ignored := ["quiet", "reduce", "reluctant", "rephase", "restart"]
  (optTable.toList.filter fun o => !ignored.contains o.name).map fun o =>
    s!"{o.name} {o.low} {o.value} {o.high}"

/-! ## Application options (`application.c`) -/

/-- Everything `parse_options` in `application.c` collects. -/
structure AppConfig where
  options : Options := {}
  inputPath : Option String := none
  force : Bool := false
  /-- `--time=<seconds>`, `0` if not set (only recorded; enforcing is the solver's job). -/
  time : Nat := 0
  /-- `--conflicts=<limit>`, `-1` if not set. -/
  conflicts : Int := -1
  /-- `--decisions=<limit>`, `-1` if not set. -/
  decisions : Int := -1
  strict : Strictness := .normal
  partialWitness : Bool := false
  witness : Bool := true
  /-- `--color` (`some true`) / `--no-color` (`some false`); colors are never printed. -/
  colors : Option Bool := none
  deriving Inhabited

/-- Options which must be the single (or first) argument. -/
def singleFirstOptions : List String :=
  ["-h", "--help", "--banner", "--build", "--copyright", "--compiler", "--id", "--range",
   "--version"]

/-- Kissat options / command line features not supported by this port. -/
def unsupportedOptions : List (String × String) :=
  [("<proof>", "second file argument (DRAT proof output; no proof support)"),
   ("--binary / --no-binary", "proof format (no proof support)"),
   ("-o <file>", "writing the simplified formula in DIMACS"),
   ("--embedded", "embedded options (not compiled in the default build)"),
   ("-l", "logging (not compiled in the default build)"),
   ("compressed input", "'.gz', '.bz2', '.xz', '.lzma', '.7z', '.Z' decompression")]

/-- `LONG_TRUE_OPTION`. -/
private def longTrue (arg name : String) : Bool :=
  arg == "--" ++ name || arg == "--" ++ name ++ "=1" || arg == "--" ++ name ++ "=true"

/-- Port of `kissat_file_readable` (file.c): `stat` succeeds and the file can be opened. -/
def fileReadable (path : String) : IO Bool := do
  if !(← System.FilePath.pathExists path) then return false
  try
    let _ ← IO.FS.Handle.mk path .read
    return true
  catch _ =>
    -- directories exist but can not be opened as files; C's `access (R_OK)` says yes
    return (← System.FilePath.isDir path)

private def hasSuffix (s suffix : String) : Bool := s.endsWith suffix

/-- `match_signature` (file.c). -/
private def matchSignature (path : String) (sig : List UInt8) : IO Bool := do
  try
    let h ← IO.FS.Handle.mk path .read
    let bytes ← h.read sig.length.toUSize
    return bytes.toList == sig
  catch _ => return false

/-- Port of `kissat_looks_like_a_compressed_file` (file.c). -/
def looksLikeCompressed (path : String) : IO Bool := do
  let sigs : List (String × List UInt8) :=
    [(".bz2", [0x42, 0x5A, 0x68]), (".gz", [0x1F, 0x8B]),
     (".lzma", [0x5D, 0x00, 0x00, 0x80, 0x00]), (".7z", [0x37, 0x7A, 0xBC, 0xAF, 0x27, 0x1C]),
     (".xz", [0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00]), (".Z", [0x1F, 0x9D, 0x90])]
  for (suf, sig) in sigs do
    if hasSuffix path suf then
      if ← matchSignature path sig then return true
  return false

/-- State of the option loop (locals of `parse_options`). -/
private structure OptState where
  app : AppConfig := {}
  strictOption : Option String := none
  configuration : Option String := none
  forceOption : Option String := none
  conflictsOption : Option String := none
  decisionsOption : Option String := none
  /-- C never assigns `time_option`, so "multiple '--time'" never triggers. -/
  timeOption : Option String := none

private def q (s : String) : String := "'" ++ s ++ "'"

/-- One argument of `parse_options`; `i` is the 1-based index. -/
private def parseArg (st : OptState) (i : Nat) (arg : String) : IO (Except String OptState) := do
  let app := st.app
  if singleFirstOptions.contains arg then
    return .error s!"option {q arg} only allowed as {if i == 1 then "single" else "first"} argument"
  if arg == "-f" || longTrue arg "force" || longTrue arg "forced" then
    if app.force then
      let fo := st.forceOption.getD ""
      if fo == arg then return .error s!"multiple {q fo} options"
      else return .error s!"{q fo} and {q arg} have the same effect"
    return .ok { st with app := { app with force := true }, forceOption := some arg }
  if longTrue arg "relax" || longTrue arg "relaxed" then
    if let some so := st.strictOption then
      if app.strict != .relaxed then return .error s!"can not combine contradictory {q so} and {q arg}"
      else if so == arg then return .error s!"multiple {q so} options"
      else return .error s!"{q so} and {q arg} have the same effect"
    return .ok { st with app := { app with strict := .relaxed }, strictOption := some arg }
  if longTrue arg "strict" || longTrue arg "stricter" || longTrue arg "pedantic" then
    if let some so := st.strictOption then
      if app.strict != .pedantic then return .error s!"can not combine contradictory {q so} and {q arg}"
      else if so == arg then return .error s!"multiple {q so} options"
      else return .error s!"{q so} and {q arg} have the same effect"
    return .ok { st with app := { app with strict := .pedantic }, strictOption := some arg }
  if arg == "-n" then return .ok { st with app := { app with witness := false } }
  if arg == "-q" then return .ok { st with app := { app with options := app.options.setClamped "quiet" 1 } }
  if arg == "-s" then
    return .ok { st with app := { app with options := app.options.setClamped "statistics" 1 } }
  if arg == "-v" then
    let v := app.options.verbose
    let v : Int := if v < INT_MAX then v + 1 else v
    return .ok { st with app := { app with options := app.options.setClamped "verbose" v } }
  if arg == "--color" || arg == "--colors" || arg == "--colour" || arg == "--colours" then
    return .ok { st with app := { app with colors := some true } }
  if arg == "--no-color" || arg == "--no-colors" || arg == "--no-colour" || arg == "--no-colours" then
    return .ok { st with app := { app with colors := some false } }
  if let some valstr := parseOptionName arg "time" then
    match parseOptionValue valstr with
    | some val =>
      if val > 0 then
        if let some to := st.timeOption then return .error s!"multiple {q to} and {q arg}"
        -- C: `alarm (val)`; here the limit is only recorded and passed to the solver
        return .ok { st with app := { app with time := val.toNat } }
      else return .error s!"invalid argument in {q arg} (try '-h')"
    | none => return .error s!"invalid argument in {q arg} (try '-h')"
  if let some valstr := parseOptionName arg "conflicts" then
    match parseOptionValue valstr with
    | some val =>
      if val ≥ 0 then
        if let some co := st.conflictsOption then return .error s!"multiple {q co} and {q arg}"
        return .ok { st with app := { app with conflicts := val }, conflictsOption := some arg }
      else return .error s!"invalid argument in {q arg} (try '-h')"
    | none => return .error s!"invalid argument in {q arg} (try '-h')"
  if let some valstr := parseOptionName arg "decisions" then
    match parseOptionValue valstr with
    | some val =>
      if val ≥ 0 then
        if let some d := st.decisionsOption then return .error s!"multiple {q d} and {q arg}"
        return .ok { st with app := { app with decisions := val }, decisionsOption := some arg }
      else return .error s!"invalid argument in {q arg} (try '-h')"
    | none => return .error s!"invalid argument in {q arg} (try '-h')"
  if arg == "--partial" then return .ok { st with app := { app with partialWitness := true } }
  if arg.startsWith "--" && hasConfiguration (arg.drop 2).toString then
    if let some c := st.configuration then
      return .error s!"multiple configurations {q c} and {q arg}"
    return .ok { st with app := { app with options := setConfiguration app.options (arg.drop 2).toString },
                         configuration := some arg }
  if arg.startsWith "--" then
    match optionsParseArg arg with
    | none => return .error s!"invalid long option {q arg} (try '-h')"
    | some (n, v) => return .ok { st with app := { app with options := app.options.setClamped n v } }
  -- DEVIATION: '-o <file>' (write simplified DIMACS) is not supported.
  if arg == "-o" then return .error "option '-o' (writing DIMACS) not supported by this port"
  if arg == "-l" then return .error s!"invalid short option {q arg} (configured without '-l' or '-g')"
  if arg.startsWith "-" && arg.length > 1 then return .error s!"invalid short option {q arg} (try '-h')"
  if let some ip := app.inputPath then
    -- NPROOFS build
    return .error s!"two file arguments {q ip} and {q arg} without proof support (try '-h')"
  if !(← fileReadable arg) then return .error s!"can not read {q arg}"
  return .ok { st with app := { app with inputPath := some arg } }

private def parseArgs (st : OptState) (i : Nat) : List String → IO (Except String OptState)
  | [] => pure (.ok st)
  | a :: as => do
    match ← parseArg st i a with
    | .error e => pure (.error e)
    | .ok st => parseArgs st (i + 1) as

/-- Port of `parse_options` (application.c) for all arguments after the program name.
  Returns the error message (printed as `kissat: error: <msg>`, exit code 1) or the
  configuration. -/
def parseOptions (args : List String) : IO (Except String AppConfig) := do
  match ← parseArgs {} 1 args with
  | .error e => return .error e
  | .ok st =>
    let app := st.app
    if !app.force then
      if let some p := app.inputPath then
        if ← looksLikeCompressed p then
          return .error s!"reading apparently compressed {q p} not supported (use '-f' to force reading without decompression)"
    if app.options.quiet != 0 then
      if app.options.statistics != 0 then
        return .error "can not use '--quiet' ('-q') with '--statistics' ('-s')"
      if app.options.verbose != 0 then
        return .error "can not use '--quiet' ('-q') with '--verbose' ('-v')"
    return .ok app

end LeanKissat.Frontend
