import LeanKissat.Search.Compact
import LeanKissat.Util.Radix

/-
Garbage collection of the clause arena (`collect.c`). The non-compacting functions
(`compact = false`) are kept separate from the compacting variants (suffix `Map`,
`compact = true`, used together with `compact.c`, see `Compact.lean`).

The non-compacting functions are written as recursive loops (for the proofs). Checked
preconditions (C `assert`s, or facts implied by the C invariants) set `notPorted`
when they fail, so the solver stops with `unknown`.
-/
namespace LeanKissat
namespace Solver

/-- Port of `kissat_reset_last_learned` (internal.c). -/
def resetLastLearned (s : Solver) : Solver :=
  { s with lastLearned := #[INVALID_REF, INVALID_REF, INVALID_REF, INVALID_REF] }

/-- Port of `kissat_map_literal` (inline.h) for `map = false`. -/
@[inline] def mapLiteralNoCompact (lit : Lit) : Lit := lit

/-- Loop of `flush_watched_clauses_by_literal` (collect.c), `compact = false`, over the
  watch list `ws` of `lit` from position `p`; the kept watches are pushed to `out`.

  Deviation: large watches of clauses before `start` are kept even if `lit` is fixed at
  the root level (C drops them). After `kissat_flush_and_mark_reason_clauses` the trail
  holds no root-level literal, so the watch list of a root-level fixed literal is never
  visited again by propagation and the difference is not observable; keeping the
  watches keeps every live large clause watched by its first two literals. -/
def flushLoop (lit : Lit) (litFixed : Value) (start : Ref) (ws : WVec) (s : Solver) (out : WVec)
    (p : Nat) : Solver × WVec :=
  if h : p < ws.size then
    let head := ws[p]
    if watchIsBinary head then
      let other := watchLit head
      if vTrue litFixed || vTrue (s.fixedValue other) then
        flushLoop lit litFixed start ws (if lit < other then s.deleteBinary lit other else s) out (p + 1)
      else
        flushLoop lit litFixed start ws s (out.push (binaryWatch other)) (p + 1)
    else
      let tail := ws.get! (p + 1)
      if watchRef tail < start then
        flushLoop lit litFixed start ws s ((out.push head).push tail) (p + 2)
      else
        flushLoop lit litFixed start ws s out (p + 2)
  else (s, out)
termination_by ws.size - p

/-- Port of `flush_watched_clauses_by_literal` (collect.c), `compact = false`. -/
def flushWatchedClausesByLiteral (s : Solver) (lit : Lit) (start : Ref) : Solver :=
  let r := flushLoop lit (s.fixedValue lit) start (s.watchesOf lit) s WVec.empty 0
  r.1.modifyWatches lit (fun _ => r.2)

/-- Loop of `flush_all_watched_clauses` (collect.c) over the variables `[i, n)`. -/
def flushAllLoop (start : Ref) (n : Nat) (s : Solver) (i : Nat) : Solver :=
  if i < n then
    let lit := LIT (UInt32.ofNat i)
    flushAllLoop start n
      ((s.flushWatchedClausesByLiteral lit start).flushWatchedClausesByLiteral (NOT lit) start) (i + 1)
  else s
termination_by n - i

/-- Port of `flush_all_watched_clauses` (collect.c), `compact = false`. -/
def flushAllWatchedClauses (s : Solver) (start : Ref) : Solver :=
  flushAllLoop start s.vars.toNat s 0

/-- Port of `update_large_reason` (collect.c). -/
def updateLargeReason (s : Solver) (forced : Lit) (dst : Ref) : Solver :=
  let fidx := IDX forced
  let s := if s.reasonIdx fidx != dst then
      { s with asg := { s.asg with aReason := s.asg.aReason.set! fidx.toNat dst } }
    else s
  { s with arena := s.arena.setReason dst false }

/-- Checked precondition of moving the reason of `forced` away from the clause at `old`:
  C asserts `forced != INVALID_LIT` and `!a->binary`, and the reason is `old`. -/
@[inline] def reasonMoves (s : Solver) (forced : Lit) (old : Ref) : Bool :=
  forced != INVALID_LIT && IDX forced < s.vars &&
    !s.isBinaryReason (IDX forced) && s.reasonIdx (IDX forced) == old

/-- `update_large_reason` for a reason clause moved from `old` to `dst` (checked). -/
def updateLargeReasonFrom (s : Solver) (forced : Lit) (old dst : Ref) : Solver :=
  if s.reasonMoves forced old then s.updateLargeReason forced dst else { s with notPorted := true }

/-- Loop of `get_forced` (collect.c). -/
def getForcedLoop (s : Solver) (dst : Ref) (n : Nat) (i : Nat) : Lit :=
  if i < n then
    let lit := s.arena.lit dst i
    if vTrue (s.value lit) then lit else getForcedLoop s dst n (i + 1)
  else INVALID_LIT
termination_by n - i

/-- Port of `get_forced` (collect.c). -/
def getForced (s : Solver) (dst : Ref) : Lit := s.getForcedLoop dst (s.arena.size dst).toNat 0

/-- `update_first_reducible` (collect.c) with `end` given as ward index. -/
def updateFirstReducibleEnd (s : Solver) (endRef : Ref) (first : Option Ref) : Solver :=
  match first with
  | none => { s with firstReducible := INVALID_REF }
  | some r => if r ≥ endRef then { s with firstReducible := INVALID_REF } else { s with firstReducible := r }

/-- `update_last_irredundant` (collect.c) with `end` given as ward index. -/
def updateLastIrredundantEnd (s : Solver) (endRef : Ref) (last : Option Ref) : Solver :=
  match last with
  | none => { s with lastIrredundant := INVALID_REF }
  | some r => if endRef ≤ r then { s with lastIrredundant := INVALID_REF } else { s with lastIrredundant := r }

/-- Copy the header word 0 and set size/searched/shrunken of a clause at `dst`. -/
@[inline] def _root_.LeanKissat.Arena.copyWord0 (a : Arena) (dst src : Ref) : Arena :=
  a.setWord0 dst (a.word0 src)

/-- State of the sparse sweep loop. -/
structure SweepState where
  dst : Ref
  firstRedundant : Option Ref := none
  firstReducible : Option Ref := none
  lastIrredundant : Option Ref
  flushed : UInt64 := 0

/-- `last_irredundant` update for the clause at `src` that disappears. -/
@[inline] def SweepState.dropLast (st : SweepState) (src first : Ref) : SweepState :=
  if st.lastIrredundant == some src then
    { st with lastIrredundant := if first == 0 then none else some first }
  else st

/-- State of the literal loop of `sparse_sweep_garbage_clauses`. -/
structure SweepLits where
  words : U32Vec
  qpos : Nat
  mfirst : Lit := INVALID_LIT
  msecond : Lit := INVALID_LIT
  forced : Lit := INVALID_LIT
  other : Lit := INVALID_LIT
  nonFalse : Nat := 0

/-- `lit` is false at the root level (C: `value < 0 && !level`). -/
@[inline] def rootF (s : Solver) (x : Lit) : Bool := vFalse (s.value x) && s.level' x == 0
/-- `lit` is true at the root level (C: `value > 0 && !level`). -/
@[inline] def rootT (s : Solver) (x : Lit) : Bool := vTrue (s.value x) && s.level' x == 0

/-- Keep the literal `lit` with value `tmp` (body of the literal loop of
  `sparse_sweep_garbage_clauses`). -/
@[inline] def SweepLits.keep (L : SweepLits) (tmp : Value) (lit : Lit) : SweepLits :=
  let L := if vTrue tmp then
      { L with forced := if L.nonFalse == 0 then lit else INVALID_LIT, nonFalse := L.nonFalse + 1 }
    else if vFalse tmp then { L with other := lit } else L
  let L := if L.mfirst == INVALID_LIT then { L with mfirst := lit }
    else if L.msecond == INVALID_LIT then { L with msecond := lit } else L
  { L with words := L.words.set! L.qpos lit, qpos := L.qpos + 1 }

/-- Literal loop of `sparse_sweep_garbage_clauses` (collect.c), `compact = false`: the
  literals at `[srcBase + i, srcBase + n)` that are not false at the root level are
  copied to `qpos`. Returns `false` at the first root-level true literal (the words
  written so far are kept, as in C). -/
def sweepLits (s : Solver) (srcBase n : Nat) (L : SweepLits) (i : Nat) : Bool × SweepLits :=
  if i < n then
    let lit := L.words.get! (srcBase + i)
    let tmp := s.value lit
    if s.rootF lit then sweepLits s srcBase n L (i + 1)
    else if s.rootT lit then (false, L)
    else sweepLits s srcBase n (L.keep tmp lit) (i + 1)
  else (true, L)
termination_by n - i

/-- A swept clause that became binary (collect.c). -/
def sweepBinary (s : Solver) (dst src : Ref) (L : SweepLits) : Solver :=
  let s := INC! s clauses_binary
  let s := if s.arena.redundant dst then DEC! s clauses_redundant else DEC! s clauses_irredundant
  let s := s.watchBinary L.mfirst L.msecond
  if s.arena.reason dst then
    -- C asserts `other != INVALID_LIT`, `forced != INVALID_LIT` and `!a->binary`
    if s.reasonMoves L.forced src && L.other != INVALID_LIT then
      let fidx := IDX L.forced
      let s := s.setABit fidx ABits.binary true
      { s with asg := { s.asg with aReason := s.asg.aReason.set! fidx.toNat L.other } }
    else { s with notPorted := true }
  else s

/-- A swept clause that stays large (collect.c). -/
def sweepLarge (s : Solver) (dst src : Ref) (newSize : Nat) (L : SweepLits) (st : SweepState) :
    Solver × SweepState :=
  -- C: `assert (2 < new_size)`
  let s := if newSize < 3 then { s with notPorted := true } else s
  let s := { s with arena := ((s.arena.setSize dst (UInt32.ofNat newSize)).setShrunken dst false).setSearched dst 2 }
  let s := if s.arena.reason dst then s.updateLargeReasonFrom L.forced src dst else s
  let nextDst := s.arena.nextClause dst
  let st := if s.arena.redundant dst then
      { st with firstReducible := if st.firstReducible.isNone then some dst else st.firstReducible,
                firstRedundant := if st.firstRedundant.isNone then some dst else st.firstRedundant }
    else { st with lastIrredundant := some dst }
  (s, { st with dst := nextDst })

/-- Sweep the clause at `src` (body of `sparse_sweep_garbage_clauses`). -/
def sweepClause (s : Solver) (first : Ref) (st : SweepState) (src : Ref) : Solver × SweepState :=
  if s.arena.garbage src then (s, st.dropLast src first) else
  let oldSize := (s.arena.size src).toNat
  let dst := st.dst
  let a := s.arena.copyWord0 dst src
  let r := sweepLits s (Arena.litPos src 0) oldSize { words := a.words, qpos := Arena.litPos dst 0 } 0
  let L := r.2
  let s := { s with arena := { words := L.words } }
  if !r.1 then
    let s := if s.arena.redundant dst then DEC! s clauses_redundant else DEC! s clauses_irredundant
    (s, st.dropLast src first)
  else
    let newSize := L.qpos - Arena.litPos dst 0
    if newSize == 2 then (s.sweepBinary dst src L, st.dropLast src first)
    else s.sweepLarge dst src newSize L st

/-- Clause loop of `sparse_sweep_garbage_clauses` (collect.c).
  -- FUEL: every clause occupies at least one ward, so the arena size bounds the
  number of iterations. -/
def sweepLoop (s : Solver) (first endRef : Ref) (st : SweepState) (src : Ref) : Nat → Solver × SweepState
  | 0 => (s, st)
  | fuel + 1 =>
    if src ≥ endRef then (s, st) else
    let next := s.arena.nextClause src
    let r := s.sweepClause first st src
    sweepLoop r.1 first endRef r.2 next fuel

/-- Port of `sparse_sweep_garbage_clauses` (collect.c), `compact = false`.
  Returns the reference from which redundant clauses have to be moved to the end
  (or `INVALID_REF`). -/
def sparseSweepGarbageClauses (s : Solver) (start : Ref) : Ref × Solver :=
  let endRef : Ref := UInt32.ofNat s.arena.sizeWards
  let st0 : SweepState :=
    { dst := start,
      lastIrredundant := if start != 0 then
        (if s.lastIrredundant == INVALID_REF then none else some s.lastIrredundant) else none }
  let r := sweepLoop s start endRef st0 start s.arena.sizeWards
  let st := r.2
  let dst := st.dst
  let s := ((r.1.updateFirstReducibleEnd dst st.firstReducible).updateLastIrredundantEnd dst
    st.lastIrredundant).resetLastLearned
  let res :=
    match st.firstRedundant, st.lastIrredundant with
    | some fr, some li => if fr < li then fr else INVALID_REF
    | _, _ => INVALID_REF
  (res, { s with arena := { words := s.arena.words.shrink (4 * dst.toNat) } })

/-- Loop of `copyClauseWords`. -/
def copyWordsLoop (src : U32Vec) (srcBase q n : Nat) (w : U32Vec) (i : Nat) : U32Vec :=
  if i < n then copyWordsLoop src srcBase q n (w.set! (q + i) (src.get! (srcBase + i))) (i + 1) else w
termination_by n - i

/-- Copy the words `[srcBase, srcBase + n)` of `srcWords` to word index `q`. -/
def copyClauseWords (a : Arena) (srcWords : U32Vec) (srcBase q n : Nat) : Arena :=
  { words := copyWordsLoop srcWords srcBase q n a.words 0 }

/-- Copy the clause at ward `p` of `old` to ward `q` and update its reason. -/
def moveClause (old : U32Vec) (s : Solver) (p q wards : Nat) : Solver :=
  let s := { s with arena := copyClauseWords s.arena old (4 * p) (4 * q) (4 * wards) }
  let qr := UInt32.ofNat q
  if s.arena.reason qr then s.updateLargeReasonFrom (s.getForced qr) (UInt32.ofNat p) qr else s

/-- First loop of `move_redundant_clauses_to_the_end` (collect.c): irredundant clauses
  are moved down to `q`, redundant ones collected.
  -- FUEL: every clause occupies at least one ward. -/
def moveIrrLoop (old : U32Vec) (endRef : Nat) (s : Solver) (lastIrr : Option Ref) (reds : Array Nat)
    (p q : Nat) : Nat → Solver × Option Ref × Array Nat × Nat
  | 0 => (s, lastIrr, reds, q)
  | fuel + 1 =>
    if p ≥ endRef then (s, lastIrr, reds, q) else
    let wards := wardsOfClause (old.get! (4 * p + 2)).toNat
    if (old.get! (4 * p) &&& ClauseHeader.redundantBit) != 0 then
      moveIrrLoop old endRef s lastIrr (reds.push p) (p + wards) q fuel
    else
      moveIrrLoop old endRef (moveClause old s p q wards) (some (UInt32.ofNat q)) reds (p + wards) (q + wards) fuel

/-- Second loop of `move_redundant_clauses_to_the_end` (collect.c). -/
def moveRedLoop (old : U32Vec) (s : Solver) (first : Option Ref) (q : Nat) : List Nat → Solver × Option Ref × Nat
  | [] => (s, first, q)
  | r :: rs =>
    let wards := wardsOfClause (old.get! (4 * r + 2)).toNat
    moveRedLoop old (moveClause old s r q wards) (if first.isNone then some (UInt32.ofNat q) else first)
      (q + wards) rs

/-- Port of `move_redundant_clauses_to_the_end` (collect.c). -/
def moveRedundantClausesToTheEnd (s : Solver) (ref : Ref) : Solver :=
  -- INC (moved): METRIC
  let s := s.markReasonClauses ref true
  let endRef := s.arena.sizeWards
  let old := s.arena.words      -- copy of the region (C: malloc'ed buffer)
  let lastIrr := if s.lastIrredundant == INVALID_REF then none else some s.lastIrredundant
  let r1 := moveIrrLoop old endRef s lastIrr #[] ref.toNat ref.toNat endRef
  let r2 := moveRedLoop old r1.1 none r1.2.2.2 r1.2.2.1.toList
  let q := r2.2.2
  ((r2.1.updateFirstReducibleEnd (UInt32.ofNat q) r2.2.1).updateLastIrredundantEnd (UInt32.ofNat q)
    r1.2.1).resetLastLearned

/-- Rewatch the clause at `ref` (body of `rewatch_clauses`). -/
def rewatchClause (s : Solver) (ref : Ref) : Solver :=
  let size := (s.arena.size ref).toNat
  let words := sortLiterals s.asg.values (fun idx => s.asg.aLevel.get! idx.toNat)
    s.arena.words (Arena.litPos ref 0) size
  let s := { s with arena := ({ words := words } : Arena).setSearched ref 2 }
  let l0 := s.arena.lit ref 0
  let l1 := s.arena.lit ref 1
  (s.watchBlocking l0 l1 ref).watchBlocking l1 l0 ref

/-- Port of `rewatch_clauses` (collect.c). -/
def rewatchClauses (s : Solver) (start : Ref) : Solver :=
  (s.arena.chain start s.arena.sizeWards).foldl rewatchClause s

/-! ### Compacting variants (`compact = true`) -/

/-- Port of `flush_watched_clauses_by_literal` (collect.c), `compact = true`:
  binary watches are mapped and the watch list is moved to `watches[mlit]`. -/
def flushWatchedClausesByLiteralMap (s : Solver) (lit : Lit) (start : Ref) : Solver := Id.run do
  let litValue := s.value lit
  let litFixed : Value := if litValue != 0 && s.level' lit == 0 then litValue else 0
  let mlit := s.mapLiteral lit
  let ws := s.watchesOf lit
  let mut s := s.modifyWatches lit (fun _ => WVec.empty)
  let mut out := WVec.empty
  let mut p := 0
  for _ in [0:ws.size] do
    if p ≥ ws.size then break
    let head := ws.get! p
    p := p + 1
    if watchIsBinary head then
      let other := watchLit head
      let otherValue := s.value other
      let otherFixed : Value := if otherValue != 0 && s.level' other == 0 then otherValue else 0
      let mother := s.mapLiteral other
      if vTrue litFixed || vTrue otherFixed || mother == INVALID_LIT then
        if lit < other then s := s.deleteBinary lit other
      else
        out := out.push (binaryWatch mother)
    else
      let tail := ws.get! p
      p := p + 1
      if litFixed == 0 then
        let ref := watchRef tail
        if ref < start then
          out := (out.push head).push tail
  if mlit == INVALID_LIT then return s.modifyWatches lit (fun _ => out)
  if litFixed != 0 then return s.modifyWatches lit (fun _ => out)
  if mlit < lit then
    -- `*mlit_watches = *lit_watches; memset (lit_watches, 0, ...)`
    return s.modifyWatches mlit (fun _ => out)
  return s.modifyWatches lit (fun _ => out)

/-- Port of `flush_all_watched_clauses` (collect.c), `compact = true`. -/
def flushAllWatchedClausesMap (s : Solver) (start : Ref) : Solver := Id.run do
  let mut s := s
  for i in [0:s.vars.toNat] do
    let lit := LIT (UInt32.ofNat i)
    s := s.flushWatchedClausesByLiteralMap lit start
    s := s.flushWatchedClausesByLiteralMap (NOT lit) start
  return s

/-- Port of `sparse_sweep_garbage_clauses` (collect.c), `compact = true`
  (literals are mapped with `kissat_map_literal`).
  -- FUEL: every clause occupies at least one ward, so the arena size bounds the
  number of iterations. -/
def sparseSweepGarbageClausesMap (s : Solver) (start : Ref) : Ref × Solver := Id.run do
  let endRef : Ref := UInt32.ofNat s.arena.sizeWards
  let begin : Ref := 0
  let first := start
  let mut st : SweepState :=
    { dst := first,
      lastIrredundant := if start != 0 then
        (if s.lastIrredundant == INVALID_REF then none else some s.lastIrredundant) else none }
  let mut s := s
  let mut src := first
  for _ in [0:s.arena.sizeWards] do
    if src ≥ endRef then break
    if s.arena.garbage src then
      let next := s.arena.nextClause src
      if st.lastIrredundant == some src then
        st := { st with lastIrredundant := if first == begin then none else some first }
      src := next
      continue
    let next := s.arena.nextClause src
    let oldSize := (s.arena.size src).toNat
    let srcBase := Arena.litPos src 0
    let dst := st.dst
    s := { s with arena := s.arena.copyWord0 dst src }
    let mut qpos := Arena.litPos dst 0
    let mut mfirst := INVALID_LIT
    let mut msecond := INVALID_LIT
    let mut forced := INVALID_LIT
    let mut other := INVALID_LIT
    let mut nonFalse := 0
    let mut satisfied := false
    for i in [0:oldSize] do
      if satisfied then continue
      let lit := s.arena.words.get! (srcBase + i)
      let tmp := s.value lit
      let level := if tmp != 0 then s.level' lit else INVALID_LEVEL
      if vFalse tmp && level == 0 then
        st := { st with flushed := st.flushed + 1 }
      else if vTrue tmp && level == 0 then
        satisfied := true
      else
        let mlit := s.mapLiteral lit
        if vTrue tmp then
          forced := if nonFalse == 0 then lit else INVALID_LIT
          nonFalse := nonFalse + 1
        else if vFalse tmp then
          other := lit
        if mfirst == INVALID_LIT then mfirst := mlit
        else if msecond == INVALID_LIT then msecond := mlit
        s := { s with arena := { words := s.arena.words.set! qpos mlit } }
        qpos := qpos + 1
    if satisfied then
      if s.arena.redundant dst then s := DEC! s clauses_redundant
      else s := DEC! s clauses_irredundant
      if st.lastIrredundant == some src then
        st := { st with lastIrredundant := if first == begin then none else some first }
      src := next
      continue
    let newSize := qpos - Arena.litPos dst 0
    if newSize == 2 then
      s := INC! s clauses_binary
      let redundant := s.arena.redundant dst
      if redundant then s := DEC! s clauses_redundant
      else s := DEC! s clauses_irredundant
      s := s.watchBinary mfirst msecond
      if s.arena.reason dst then
        let fidx := IDX forced
        s := s.setABit fidx ABits.binary true
        s := { s with asg := { s.asg with aReason := s.asg.aReason.set! fidx.toNat other } }
      if st.lastIrredundant == some src then
        st := { st with lastIrredundant := if first == begin then none else some first }
    else
      s := { s with arena := ((s.arena.setSize dst (UInt32.ofNat newSize)).setShrunken dst false).setSearched dst 2 }
      if s.arena.reason dst then s := s.updateLargeReason forced dst
      let nextDst := s.arena.nextClause dst
      if s.arena.redundant dst then
        if st.firstReducible.isNone then st := { st with firstReducible := some dst }
        if st.firstRedundant.isNone then st := { st with firstRedundant := some dst }
      else
        st := { st with lastIrredundant := some dst }
      st := { st with dst := nextDst }
    src := next
  let dst := st.dst
  s := s.updateFirstReducibleEnd dst st.firstReducible
  s := s.updateLastIrredundantEnd dst st.lastIrredundant
  s := s.resetLastLearned
  let res :=
    match st.firstRedundant, st.lastIrredundant with
    | some fr, some li => if fr < li then fr else INVALID_REF
    | _, _ => INVALID_REF
  s := { s with arena := { words := s.arena.words.shrink (4 * dst.toNat) } }
  return (res, s)

/-- Port of `kissat_compacting` (collect.c). -/
def compacting (s : Solver) : Bool :=
  if s.options.compact == 0 then false
  else
    let inactive := s.vars - s.active
    let limit : UInt32 := ((UInt64.ofNat s.options.compactlim).toFloat / 1e2 *
      (UInt64.ofNat s.vars.toNat).toFloat).toUInt32
    inactive > limit

/-- Port of `kissat_sparse_collect` (collect.c), compacting path. -/
def sparseCollectCompact (s : Solver) (start : Ref) : Solver :=
  let (vars, mfixed, s) := s.compactLiterals
  let s := s.flushAllWatchedClausesMap start
  let (move, s) := s.sparseSweepGarbageClausesMap start
  let s := s.finalizeCompacting vars mfixed
  let s := if move != INVALID_REF then s.moveRedundantClausesToTheEnd move else s
  s.rewatchClauses start

/-- Port of `kissat_sparse_collect` (collect.c). -/
def sparseCollect (s : Solver) (compact : Bool) (start : Ref) : Solver :=
  if compact then s.sparseCollectCompact start else
  -- INC (garbage_collections), INC (sparse_gcs): METRIC
  let s := s.flushAllWatchedClauses start
  let r := s.sparseSweepGarbageClauses start
  -- Checked: irredundant clauses after the first redundant one are only produced by
  -- procedures that are not ported (elimination, vivification, ...), so
  -- `move_redundant_clauses_to_the_end` is not needed here.
  if r.1 != INVALID_REF then { r.2 with notPorted := true } else
  r.2.rewatchClauses start

end Solver
end LeanKissat
