import LeanKissat.Search.Collect

/-
Learned clause reduction (`reduce.c`) and `kissat_flush_and_mark_reason_clauses`
(`trail.c`), `kissat_backtrack_propagate_and_flush_trail` (`backtrack.c`).
-/
namespace LeanKissat
namespace Solver

/-- Port of `kissat_backtrack_propagate_and_flush_trail` (backtrack.c). C asserts that
  propagation does not find a conflict (checked). -/
def backtrackPropagateAndFlushTrail (s : Solver) : Solver :=
  if s.level != 0 then
    let s := s.backtrackInConsistentState 0
    let r := if s.probing then s.probingPropagate none true else s.searchPropagate
    if r.2.isSome then { r.1 with notPorted := true } else r.1
  else s

/-- Port of `kissat_flush_and_mark_reason_clauses` (trail.c). -/
def flushAndMarkReasonClauses (s : Solver) (start : Ref) : Bool × Solver :=
  if s.asg.unflushed != 0 then (true, s.backtrackPropagateAndFlushTrail)
  else (true, s.markReasonClauses start true)

/-- A reducible candidate: `rank` and reference. -/
structure Reducible where
  rank : UInt64
  ref : Ref
  deriving Inhabited

/-- Index of the first redundant clause of `refs` at or after `k` (first loop of
  `collect_reducibles`). -/
def skipIrredundant (a : Arena) (refs : Array Ref) (k : Nat) : Nat :=
  if h : k < refs.size then
    if a.redundant refs[k] then k else skipIrredundant a refs (k + 1)
  else k
termination_by refs.size - k

/-- Candidate loop of `collect_reducibles` (reduce.c). -/
def collectLoop (refs : Array Ref) (tier1 tier2 : UInt32) (s : Solver) (reds : Array Reducible)
    (i : Nat) : Solver × Array Reducible :=
  if h : i < refs.size then
    let c := refs[i]
    if !s.arena.redundant c || s.arena.garbage c then collectLoop refs tier1 tier2 s reds (i + 1) else
    let used := s.arena.used c
    let s := if used != 0 then { s with arena := s.arena.setUsed c (used - 1) } else s
    if s.arena.reason c then collectLoop refs tier1 tier2 s reds (i + 1) else
    let glue := s.arena.glue c
    if (glue ≤ tier1 && used != 0) || (glue ≤ tier2 && used ≥ MAX_USED - 1) then
      collectLoop refs tier1 tier2 s reds (i + 1)
    else
      -- C: `~c->size` is a 32-bit complement (zero-extended); `~c->glue` is an `int`
      -- complement, of which only the low 32 bits survive the shift by 32.
      let negSize : UInt64 := (~~~(s.arena.size c)).toUInt64
      let negGlue : UInt64 := (~~~glue).toUInt64
      collectLoop refs tier1 tier2 s (reds.push { rank := negSize ||| (negGlue <<< 32), ref := c }) (i + 1)
  else (s, reds)
termination_by refs.size - i

/-- The candidates of `collect_reducibles` from the first redundant clause `refs[k]`. -/
def collectFrom (refs : Array Ref) (k : Nat) (s : Solver) : Option (Array Reducible) × Solver :=
  let tier1 := s.tier1Limit
  let tier2 := max tier1 s.tier2Limit
  let r := collectLoop refs tier1 tier2 s #[] k
  if r.2.isEmpty then (none, r.1) else (some r.2, r.1)

/-- Port of `collect_reducibles` (reduce.c). -/
def collectReducibles (s : Solver) (start : Ref) : Option (Array Reducible) × Solver :=
  let refs := s.arena.clauseRefsFrom start
  let k := skipIrredundant s.arena refs 0
  if k ≥ refs.size then (none, { s with firstReducible := INVALID_REF }) else
  collectFrom refs k { s with firstReducible := refs[k]! }

/-- Marking loop of `mark_less_useful_clauses_as_garbage` (reduce.c). The candidates
  are redundant clauses at or after `start` that are not reasons (checked). -/
def markGarbageLoop (start : Ref) (reds : Array Reducible) (n : Nat) (s : Solver) (i : Nat) : Solver :=
  if i < n then
    let r := reds[i]!.ref
    let s := if start ≤ r && s.arena.redundant r && !s.arena.reason r then s.markClauseAsGarbage r
      else { s with notPorted := true }
    markGarbageLoop start reds n s (i + 1)
  else s
termination_by n - i

/-- Port of `mark_less_useful_clauses_as_garbage` (reduce.c). -/
def markLessUsefulClausesAsGarbage (s : Solver) (start : Ref) (reds : Array Reducible) : Solver :=
  let high := (UInt64.ofNat s.options.reducehigh).toFloat * 0.1
  let low := (UInt64.ofNat s.options.reducelow).toFloat * 0.1
  let percent :=
    if low < high then
      let delta := high - low
      high - delta / Float.log10 ((s.stats.reductions + 9).toFloat)
    else low
  let fraction := percent / 100.0
  let size := reds.size
  let target := ((UInt64.ofNat size).toFloat * fraction).toUInt64.toNat
  -- clauses_reduced*: STATISTIC
  markGarbageLoop start reds (min target size) s 0

/-- `target` is `0` or the reference of a clause reached from `r` (checked precondition
  of `kissat_reduce`: `first_reducible` is a clause reference). -/
def _root_.LeanKissat.Arena.reaches (a : Arena) (target : Ref) : Ref → Nat → Bool
  | _, 0 => false
  | r, fuel + 1 =>
    if r == target then true
    else if r < target && Decidable.decide (r.toNat < a.sizeWards) then a.reaches target (a.nextClause r) fuel
    else false

/-- The watch lists of the literals `j ≥ 2 * vars` (up to the capacity) are empty: checked
  precondition of the garbage collection (not checked in C, where `flush_all_watched_clauses`
  only visits the lists of the variables). -/
def unusedWatchesEmpty (s : Solver) (j : Nat) : Bool :=
  if h : j < s.watches.size then (s.watches[j].size == 0) && s.unusedWatchesEmpty (j + 1) else true
termination_by s.watches.size - j

/-- Body of `kissat_reduce` from `start` (reduce.c). -/
def reduceFrom (s : Solver) (compact : Bool) (start : Ref) : Solver :=
  let r := s.flushAndMarkReasonClauses start
  let s := r.2
  if !r.1 then s else
  -- a checked condition failed (the solver stops with `unknown`)
  if s.notPorted then s else
  if !s.arena.reaches start 0 (s.arena.sizeWards + 1) || !s.unusedWatchesEmpty (2 * s.vars.toNat) then
    { s with notPorted := true } else
  let r := s.collectReducibles start
  match r.1 with
  | some reds =>
    (r.2.markLessUsefulClausesAsGarbage start (Radix.radixSortArray64 (·.rank) reds)).sparseCollect compact start
  | none =>
    if compact then r.2.sparseCollect compact start else r.2.markReasonClauses start false

/-- `UPDATE_CONFLICT_LIMIT (reduce, reductions, SQRT, false)` (reduce.c). -/
def updateReduceLimit (s : Solver) : Solver :=
  let delta := s.updateConflictLimitDelta s.options.reduceint s.stats.reductions kSqrt false
    -- CLAMP: `reduceint ≥ 2` and `sqrt (reductions) ≥ 1`
    (UInt64.ofNat s.options.reduceint)
  let (lim, s3) := s.conflictsPlus delta
  { s3 with limits := { s3.limits with reduceConflicts := lim } }

/-- Port of `kissat_reduce` (reduce.c). -/
def reduce (s : Solver) : UInt32 × Solver :=
  let s := (INC! s reductions).computeAndSetTierLimits
  let compact := s.compacting
  let start := if compact then 0 else s.firstReducible
  let s := if start != INVALID_REF then s.reduceFrom compact start else s
  let s := s.classify
  let s := if !s.inconsistent then s.updateReduceLimit else s
  let s := { s with last := { s.last with conflictsReduce := s.stats.conflicts } }
  (if s.inconsistent then 20 else 0, s)

end Solver
end LeanKissat
