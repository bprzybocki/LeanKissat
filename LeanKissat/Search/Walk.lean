import LeanKissat.Search.Warmup

/-
Local search (`walk.c`) and the dense-mode switch it needs (`dense.c`:
`kissat_enter_dense_mode` with saved irredundant binaries,
`kissat_resume_sparse_mode` without flushing eliminated literals, `watch.c`:
`kissat_flush_large_connected`, `kissat_watch_large_clauses`).

Representation of the walker (C → Lean):
* `counter *counters` (`{count, pos}`) → two parallel arrays `counts` and `poss`
  (`Array UInt32`, which is faster than the byte-packed `U32Vec` for this random access).
* `tagged *refs` (`ref:31`, `binary:1`) → `U32Vec` of words `ref ||| binary <<< 31`.
* `litpairs *binaries` → flat `U32Vec` (`lits[0]`, `lits[1]` at `2*i`, `2*i+1`).
* `solver->values` during walking → `Walker.values` (the solver's values are left
  untouched; C swaps the pointer and restores it in `release_walker`).
* the walker watch lists (`kissat_push_large_watch` of counter references, one word
  each) → `WalkCtx.watches`, the solver's watch array taken out of the state.
* `doubles scores` → `FloatArray` scratch buffer indexed from 0 per pick.
The fields that change in the flip loop are in `Walker`, the read-only ones in
`WalkCtx`.
-/
namespace LeanKissat
namespace Solver

/-! ### `dense.c` / `watch.c` helpers -/

/-- Port of `flush_large_watches` (dense.c) with `irredundant != 0`: removes all
  watches, deletes satisfied and duplicated binary clauses and returns the remaining
  binary clauses (`lit < other`) as a flat literal-pair stack. -/
def flushLargeWatchesIrredundant (s : Solver) : U32Vec × Solver := Id.run do
  let mut irr := U32Vec.empty
  let mut marks := s.marks
  let mut wss := s.watches
  let mut s := { s with marks := .empty, watches := #[] }
  for l in [0:2 * s.vars.toNat] do
    let lit := UInt32.ofNat l
    let litValue := s.value lit
    let ws := wss[l]!
    -- `memset (watches, 0, sizeof *watches)`
    wss := wss.set! l WVec.empty
    let mut marked : Array Lit := #[]
    let mut p := 0
    for _ in [0:ws.size] do
      if p ≥ ws.size then break
      let w := ws.get! p
      p := p + 1
      if watchIsBinary w then
        let other := watchLit w
        let otherValue := s.value other
        if litValue == 0 && otherValue == 0 then
          if marks.get! other.toNat != 0 then
            if lit < other then s := s.deleteBinary lit other
          else
            marks := marks.set! other.toNat 1
            marked := marked.push other
            if lit < other then irr := (irr.push lit).push other
        else
          if lit < other then s := s.deleteBinary lit other
      else
        p := p + 1
    for o in marked do
      marks := marks.set! o.toNat 0
  -- `kissat_release_vectors`: no observable effect
  return (irr, { s with marks := marks, watches := wss })

/-- Port of `kissat_flush_large_connected` (watch.c): keep only binary watches
  (all other watches are one-word large watches in non-watching mode). -/
def flushLargeConnected (s : Solver) : Solver := Id.run do
  let mut wss := s.watches
  let s := { s with watches := #[] }
  for l in [0:2 * s.vars.toNat] do
    let ws := wss[l]!
    wss := wss.set! l WVec.empty
    let mut q := 0
    let mut ws := ws
    for p in [0:ws.size] do
      let w := ws.get! p
      if watchIsBinary w then
        ws := ws.set! q w
        q := q + 1
    wss := wss.set! l (ws.shrink q)
  return { s with watches := wss }

/-- Port of `resume_watching_irredundant_binaries` (dense.c). -/
def resumeWatchingIrredundantBinaries (s : Solver) (irr : U32Vec) : Solver := Id.run do
  let mut wss := s.watches
  let s := { s with watches := #[] }
  for i in [0:irr.size / 2] do
    let first := irr.get! (2 * i)
    let second := irr.get! (2 * i + 1)
    wss := wss.modify first.toNat (·.push (binaryWatch second))
    wss := wss.modify second.toNat (·.push (binaryWatch first))
  return { s with watches := wss }

/-- Port of `kissat_watch_large_clauses` (watch.c). -/
def watchLargeClauses (s : Solver) : Solver := Id.run do
  let mut wss := s.watches
  let mut arena := s.arena
  let s := { s with watches := #[], arena := {} }
  for ref in arena.clauseRefsFrom 0 do
    if arena.garbage ref then continue
    let size := (arena.size ref).toNat
    let words := sortLiterals s.asg.values (fun idx => s.asg.aLevel.get! idx.toNat)
      arena.words (Arena.litPos ref 0) size
    arena := { words := words }
    arena := arena.setSearched ref 2
    let l0 := arena.lit ref 0
    let l1 := arena.lit ref 1
    wss := wss.modify l0.toNat (fun w => (w.push (blockingWatch l1)).push (largeWatch ref))
    wss := wss.modify l1.toNat (fun w => (w.push (blockingWatch l0)).push (largeWatch ref))
  return { s with watches := wss, arena := arena }

/-- Port of `kissat_resume_sparse_mode` (dense.c) for `flush_eliminated = false`
  and saved irredundant binaries. -/
def resumeSparseMode (s : Solver) (irr : U32Vec) : Solver :=
  if s.inconsistent then s else
  let s := s.flushLargeConnected
  let s := { s with watching := true }
  let s := s.resumeWatchingIrredundantBinaries irr
  let s := s.watchLargeClauses
  -- `kissat_reset_propagate`
  let s := { s with propagate := 0 }
  if s.probing then (s.probingPropagate none true).1 else s.searchPropagate.1

/-! ### The walker -/

def LD_MAX_WALK_REF : Nat := 31
def MAX_WALK_REF : UInt64 := 0x7FFFFFFF
def INVALID_BEST_TRAIL_POS : UInt32 := UINT_MAX
def WALK_BINARY_BIT : UInt32 := 0x80000000

/-- Read-only part of `struct walker`. -/
structure WalkCtx where
  watches : Array WVec
  refs : U32Vec
  binaries : U32Vec
  arena : U32Vec
  table : FloatArray
  exponents : Nat
  epsilon : Float
  vars : UInt32

/-- The part of `struct walker` modified during local search. `steps` is
  `statistics.walk_steps`, kept here and written back at the end. -/
structure Walker where
  values : ByteArray
  counts : Array UInt32
  poss : Array UInt32
  unsat : Array UInt32
  trail : Array UInt32
  bestValues : ByteArray
  scores : FloatArray
  random : UInt64
  flipped : UInt64
  steps : UInt64
  bestTrailPos : UInt32
  current : UInt32
  minimum : UInt32

/-- `0.0` (closed constant). -/
def fzero : Float := 0.0

/-- `cbvals` (walk.c). -/
def cbvals : Array (Float × Float) :=
  #[(0.0, 2.00), (3.0, 2.50), (4.0, 2.85), (5.0, 3.70), (6.0, 5.10), (7.0, 7.40)]

/-- Port of `fit_cbval` (walk.c). -/
def fitCbval (size : Float) : Float := Id.run do
  let num := cbvals.size
  let mut i := 0
  for _ in [0:num] do
    if i + 2 < num && ((cbvals[i]!).1 > size || (cbvals[i + 1]!).1 < size) then
      i := i + 1
    else break
  let x2 := (cbvals[i + 1]!).1
  let x1 := (cbvals[i]!).1
  let y2 := (cbvals[i + 1]!).2
  let y1 := (cbvals[i]!).2
  let dx := x2 - x1
  let dy := y2 - y1
  return dy * (size - x1) / dx + y1

/-- The two loops of `init_score_table` (walk.c): `table[i] = base^i` (iterated
  products) while non-zero, and `epsilon` the last non-zero entry.
  -- FUEL: `cb ≥ 2` (every `cbvals` segment and its extrapolation is ≥ 2 for sizes
  ≥ 0), so `base ≤ 0.5` and the products reach `0` after at most 1075 steps
  (binary64 underflow); 4096 is never exhausted. -/
def scoreTable (base : Float) : FloatArray × Float := Id.run do
  let mut table := FloatArray.mk #[]
  let mut next : Float := 1
  let mut epsilon : Float := 1
  for _ in [0:4096] do
    if next == 0 then break
    epsilon := next
    table := table.push next
    next := epsilon * base
  return (table, epsilon)

/-- `break_value` loop: number of counters with `count == 1`. -/
@[inline] def breakCount (ws : WVec) (counts : Array UInt32) : UInt32 :=
  ws.data.foldl (fun res ref => res + (counts[ref.toNat]! == 1).toUInt32) 0

/-- Result of the first loop of `pick_literal`. -/
structure PickAcc where
  scores : FloatArray
  sum : Float
  picked : Lit
  steps : UInt64

/-- First loop of `pick_literal` (walk.c), including `break_value` and
  `scale_score`. Literals are `src[off + j]` for `j < size`. -/
def pickScores (ctx : WalkCtx) (values : ByteArray) (counts : Array UInt32) (src : U32Vec)
    (off size j : Nat) (k : Nat) (scores : FloatArray) (sum : Float) (picked : Lit)
    (steps : UInt64) : PickAcc :=
  if _h : j < size then
    let lit := src.get! (off + j)
    if values.get! lit.toNat == 0 then
      pickScores ctx values counts src off size (j + 1) k scores sum picked steps
    else
      let ws := ctx.watches[(NOT lit).toNat]!
      let breaks := breakCount ws counts
      let steps := steps + 1 + UInt64.ofNat ws.size
      let score := if breaks.toNat < ctx.exponents then ctx.table.get! breaks.toNat
        else ctx.epsilon
      let scores := if k < scores.size then scores.set! k score else scores.push score
      pickScores ctx values counts src off size (j + 1) (k + 1) scores (sum + score) lit
        steps
  else ⟨scores, sum, picked, steps⟩
termination_by size - j

/-- Second loop of `pick_literal` (walk.c). -/
def pickSecond (values : ByteArray) (src : U32Vec) (off size : Nat) (scores : FloatArray)
    (threshold : Float) (j k : Nat) (sum : Float) (picked : Lit) : Lit :=
  if h : j < size then
    let lit := src.get! (off + j)
    if values.get! lit.toNat == 0 then
      pickSecond values src off size scores threshold (j + 1) k sum picked
    else
      let sum := sum + scores.get! k
      if threshold < sum then lit
      else pickSecond values src off size scores threshold (j + 1) (k + 1) sum picked
  else picked
termination_by size - j

/-- Counters, unsatisfied stack and steps threaded through `make_clauses` and
  `break_clauses`. -/
structure FlipAcc where
  counts : Array UInt32
  poss : Array UInt32
  unsat : Array UInt32
  steps : UInt64

/-- Loop of `make_clauses` (walk.c) including `pop_unsat`. -/
def makeLoop (ws : WVec) (i : Nat) (counts poss unsat : Array UInt32) (steps : UInt64) :
    FlipAcc :=
  if h : i < ws.size then
    let ref := ws[i]
    let c := counts[ref.toNat]!
    let counts := counts.set! ref.toNat (c + 1)
    if c != 0 then makeLoop ws (i + 1) counts poss unsat (steps + 1)
    else
      let pos := poss[ref.toNat]!
      let other := unsat.back!
      let unsat := unsat.pop
      if other != ref then
        let poss := poss.set! other.toNat pos
        let unsat := unsat.set! pos.toNat other
        makeLoop ws (i + 1) counts poss unsat (steps + 2)
      else makeLoop ws (i + 1) counts poss unsat (steps + 1)
  else ⟨counts, poss, unsat, steps⟩
termination_by ws.size - i

/-- Loop of `break_clauses` (walk.c) including `push_unsat`. -/
def breakLoop (ws : WVec) (i : Nat) (counts poss unsat : Array UInt32) (steps : UInt64) :
    FlipAcc :=
  if h : i < ws.size then
    let ref := ws[i]
    let c := counts[ref.toNat]! - 1
    let counts := counts.set! ref.toNat c
    if c != 0 then breakLoop ws (i + 1) counts poss unsat (steps + 1)
    else
      let poss := poss.set! ref.toNat (UInt32.ofNat unsat.size)
      breakLoop ws (i + 1) counts poss (unsat.push ref) (steps + 1)
  else ⟨counts, poss, unsat, steps⟩
termination_by ws.size - i

/-- The literal-saving loop of `save_walker_trail` (walk.c). -/
def saveTrailValues (trail : Array UInt32) (best : Nat) (bestValues : ByteArray) : ByteArray :=
  Id.run do
  let mut bv := bestValues
  for i in [0:best] do
    let lit := trail[i]!
    bv := bv.set! (IDX lit).toNat (if NEGATED lit then VAL_FALSE else VAL_TRUE)
  return bv

/-- The shifting part of `save_walker_trail (..., keep = true)`. -/
def shiftTrail (trail : Array UInt32) (best : Nat) : Array UInt32 := Id.run do
  let mut t := trail
  let n := trail.size
  for p in [best:n] do
    t := t.set! (p - best) t[p]!
  return t.shrink (n - best)

/-- Trail part of the walker, as updated by `push_flipped` / `update_best`. -/
structure WalkTrail where
  trail : Array UInt32
  bestTrailPos : UInt32
  bestValues : ByteArray

/-- Port of `push_flipped` (walk.c). -/
@[noinline] def pushFlipped (vars : UInt32) (t : WalkTrail) (flipped : Lit) : WalkTrail :=
  match t with
  | ⟨trail, bestTrailPos, bestValues⟩ =>
  if bestTrailPos == INVALID_BEST_TRAIL_POS then ⟨trail, bestTrailPos, bestValues⟩
  else
    let sizeTrail := trail.size
    let limit := vars / 4 + 1
    if sizeTrail < limit.toNat then ⟨trail.push flipped, bestTrailPos, bestValues⟩
    else if bestTrailPos != 0 then
      let bestValues := saveTrailValues trail bestTrailPos.toNat bestValues
      let trail := shiftTrail trail bestTrailPos.toNat
      ⟨trail.push flipped, 0, bestValues⟩
    else ⟨trail.shrink 0, INVALID_BEST_TRAIL_POS, bestValues⟩

/-- Port of `save_all_values` (walk.c). -/
def saveAllValues (vars : UInt32) (values bestValues : ByteArray) : ByteArray := Id.run do
  let mut bv := bestValues
  for idx in [0:vars.toNat] do
    let v := values.get! (2 * idx)
    if v != 0 then bv := bv.set! idx v
  return bv

/-- Port of `update_best` (walk.c) without the minimum update. -/
@[noinline] def updateBest (vars : UInt32) (values : ByteArray) (t : WalkTrail) : WalkTrail :=
  match t with
  | ⟨trail, bestTrailPos, bestValues⟩ =>
  if bestTrailPos == INVALID_BEST_TRAIL_POS then
    ⟨trail, 0, saveAllValues vars values bestValues⟩
  else ⟨trail, UInt32.ofNat trail.size, bestValues⟩

/-- Port of `local_search_step` (walk.c) with `pick_literal` and `flip_literal`. -/
def walkStep (ctx : WalkCtx) (w : Walker) : Walker :=
  match w with
  | { values, counts, poss, unsat, trail, bestValues, scores, random, flipped, steps,
      bestTrailPos, current, minimum } =>
  -- INC (flipped): STATISTIC
  let flipped := flipped + 1
  -- pick_literal
  let pos := (flipped % current.toUInt64).toNat
  let flipped := flipped + 1
  let cref := unsat[pos]!
  let tag := ctx.refs.get! cref.toNat
  let binary := tag &&& WALK_BINARY_BIT != 0
  let ref := tag &&& ~~~WALK_BINARY_BIT
  let src := if binary then ctx.binaries else ctx.arena
  let off := if binary then 2 * ref.toNat else Arena.litPos ref 0
  let size := if binary then 2 else (ctx.arena.get! (Arena.base ref + 2)).toNat
  match pickScores ctx values counts src off size 0 0 scores fzero INVALID_LIT 0 with
  | ⟨scores, sum, picked, pickSteps⟩ =>
  let (rnd, random) := Generator.pickDouble random
  let threshold := sum * rnd
  let picked := pickSecond values src off size scores threshold 0 0 fzero picked
  -- flip_literal
  let notPicked := NOT picked
  let values := (values.set! picked.toNat VAL_TRUE).set! notPicked.toNat VAL_FALSE
  match makeLoop ctx.watches[picked.toNat]! 0 counts poss unsat 1 with
  | ⟨counts, poss, unsat, makeSteps⟩ =>
  match breakLoop ctx.watches[notPicked.toNat]! 0 counts poss unsat 1 with
  | ⟨counts, poss, unsat, breakSteps⟩ =>
  let steps := steps + pickSteps + makeSteps + breakSteps
  let current := UInt32.ofNat unsat.size
  match pushFlipped ctx.vars ⟨trail, bestTrailPos, bestValues⟩ picked with
  | t =>
  let better := current < minimum
  let minimum := if better then current else minimum
  match (if better then updateBest ctx.vars values t else t) with
  | ⟨trail, bestTrailPos, bestValues⟩ =>
  { values, counts, poss, unsat, trail, bestValues, scores, random, flipped, steps,
    bestTrailPos, current, minimum }

/-- The loop of `local_search_round` (walk.c). `TERMINATED (walk_terminated_1)` only
  reads `termination.flagged`, which cannot change inside the pure core (checked
  once by the caller). Every step adds at least one to `walk_steps` (both
  `make_clauses` and `break_clauses` start with `steps = 1`); the runtime check
  `st < w.steps` is therefore always true and only serves the termination proof. -/
def walkRound (ctx : WalkCtx) (limit : UInt64) (w : Walker) : Walker :=
  if _hl : w.steps < limit then
    if w.minimum != 0 then
      let st := w.steps
      let w' := walkStep ctx w
      if _h : st < w'.steps then walkRound ctx limit w' else w'
    else w
  else w
termination_by limit.toNat - w.steps.toNat
decreasing_by
  have h1 := UInt64.lt_iff_toNat_lt.mp _hl
  have h2 := UInt64.lt_iff_toNat_lt.mp _h
  dsimp only [st, w'] at h2
  omega

/-- Port of `walking_phase` (walk.c): `init_walker`, `init_walker_limit`,
  `local_search_round`, `save_final_minimum`, `release_walker` and the dense mode
  switch around it. -/
def walkingPhase (s : Solver) : Solver := Id.run do
  let s := INC! s walks
  -- kissat_enter_dense_mode (solver, &irredundant)
  let (irr, s) := s.flushLargeWatchesIrredundant
  let mut s := { s with watching := false }
  -- init_walker
  let clauses := s.binirrClauses
  let random : UInt64 := s.random ^^^ s.stats.walks
  let vars := s.vars.toNat
  let mut values := ByteArray.mk (Array.replicate (2 * vars) 0)
  let mut bestValues := ByteArray.mk (Array.replicate vars 0)
  -- import_decision_phases (INC (walk_decisions): METRIC)
  for i in [0:vars] do
    let idx := UInt32.ofNat i
    if !s.isActive idx then continue
    let v : Value := if s.decidePhase idx then VAL_TRUE else VAL_FALSE
    bestValues := bestValues.set! i v
    values := (values.set! (2 * i) v).set! (2 * i + 1) v.neg
  let n := clauses.toNat
  let mut counts : Array UInt32 := Array.replicate n 0
  let mut poss : Array UInt32 := Array.replicate n 0
  let mut refs := U32Vec.replicate n 0
  let mut unsat : Array UInt32 := #[]
  let mut wss := s.watches
  s := { s with watches := #[] }
  -- connect_binary_counters
  let mut cref : Nat := 0
  let mut wsize : Float := 0
  for b in [0:irr.size / 2] do
    let first := irr.get! (2 * b)
    let second := irr.get! (2 * b + 1)
    let fv := values.get! first.toNat
    let sv := values.get! second.toNat
    if fv == 0 || sv == 0 then continue
    refs := refs.set! cref (WALK_BINARY_BIT ||| UInt32.ofNat b)
    let cw := largeWatch (UInt32.ofNat cref)
    wss := wss.modify first.toNat (·.push cw)
    wss := wss.modify second.toNat (·.push cw)
    let count := (vTrue fv).toUInt32 + (vTrue sv).toUInt32
    counts := counts.set! cref count
    if count == 0 then
      poss := poss.set! cref (UInt32.ofNat unsat.size)
      unsat := unsat.push (UInt32.ofNat cref)
    cref := cref + 1
  wsize := wsize + 2.0 * (UInt64.ofNat cref).toFloat
  -- connect_large_counters
  let lastIrr := s.lastIrredundant
  for c in s.arena.clauseRefsFrom 0 do
    if lastIrr != INVALID_REF && c > lastIrr then break
    if s.arena.garbage c then continue
    if s.arena.redundant c then continue
    let csize := (s.arena.size c).toNat
    let mut satisfied := false
    for i in [0:csize] do
      if vTrue (s.value (s.arena.lit c i)) then
        satisfied := true
        break
    if satisfied then
      s := s.markClauseAsGarbage c
      continue
    refs := refs.set! cref c
    let cw := largeWatch (UInt32.ofNat cref)
    let mut count : UInt32 := 0
    let mut sz : UInt32 := 0
    for i in [0:csize] do
      let lit := s.arena.lit c i
      let v := values.get! lit.toNat
      if v == 0 then continue
      wss := wss.modify lit.toNat (·.push cw)
      sz := sz + 1
      if vTrue v then count := count + 1
    counts := counts.set! cref count
    if count == 0 then
      poss := poss.set! cref (UInt32.ofNat unsat.size)
      unsat := unsat.push (UInt32.ofNat cref)
    cref := cref + 1
    wsize := wsize + sz.toFloat
  let initial := UInt32.ofNat unsat.size
  let size := kissatAverage wsize clauses.toFloat
  -- init_score_table
  let cb := if s.stats.walks &&& 1 != 0 then fitCbval size else 2.0
  let base := 1 / cb
  let (table, epsilon) := scoreTable base
  -- init_walker_limit: SET_EFFORT_LIMIT (limit, walk, walk_steps)
  let oldLimit := s.stats.walk_steps
  let ticks := s.stats.search_ticks
  let last := if s.probing then s.last.ticksProbe else s.last.ticksEliminate
  let reference := ticks - last
  let minEffort : UInt64 := (1e6 * (UInt64.ofNat s.options.mineffort).toFloat).toUInt64
  let reference := if reference < minEffort then minEffort else reference
  let effort := (UInt64.ofNat s.options.walkeffort).toFloat * 1e-3
  let delta : UInt64 := (effort * reference.toFloat).toUInt64
  let (limit, o) := addOverflow oldLimit delta
  if o then s := { s with overflowed := true }
  let ctx : WalkCtx :=
    { watches := wss, refs := refs, binaries := irr, arena := s.arena.words, table := table,
      exponents := table.size, epsilon := epsilon, vars := s.vars }
  let w : Walker :=
    { values := values, counts := counts, poss := poss, unsat := unsat, trail := #[],
      bestValues := bestValues, scores := FloatArray.mk #[], random := random, flipped := 0,
      steps := oldLimit, bestTrailPos := 0, current := initial, minimum := initial }
  -- local_search_round
  let w := if s.terminationFlagged || o then w else walkRound ctx limit w
  s := { s with stats := s.stats.set Counters.idx_walk_steps w.steps }
  -- save_final_minimum (INC (walk_improved): STATISTIC)
  if w.minimum != initial then
    let bv :=
      if w.bestTrailPos == 0 || w.bestTrailPos == INVALID_BEST_TRAIL_POS then w.bestValues
      else saveTrailValues w.trail w.bestTrailPos.toNat w.bestValues
    -- export_best_values: memcpy (saved, best, VARS)
    let mut saved := s.asg.phaseSaved
    s := { s with asg := { s.asg with phaseSaved := .empty } }
    for i in [0:vars] do
      saved := saved.set! i (bv.get! i)
    s := { s with asg := { s.asg with phaseSaved := saved } }
  -- release_walker; kissat_resume_sparse_mode (solver, false, &irredundant)
  s := { s with watches := ctx.watches }
  return s.resumeSparseMode irr

/-- Port of `kissat_walking` (walk.c). -/
def walking (s : Solver) : Bool :=
  let lastIrr := if s.lastIrredundant == INVALID_REF then UInt64.ofNat s.arena.sizeWards
    else s.lastIrredundant.toUInt64
  if lastIrr > MAX_WALK_REF then false
  else s.binirrClauses ≤ MAX_WALK_REF

/-- Port of `kissat_walk` (walk.c). -/
def walk (s : Solver) : Solver :=
  if !s.walking then s else
  let s := if s.options.warmup != 0 then s.warmup else s
  s.walkingPhase

end Solver
end LeanKissat
