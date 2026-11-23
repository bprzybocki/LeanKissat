import LeanKissat.Search.Backtrack
import LeanKissat.Core.Limits

/-
Decisions (`decide.c`).
-/
namespace LeanKissat
namespace Solver

/-- `INITIAL_PHASE` (decide.h) as a C `value`. -/
@[inline] def initialPhase (s : Solver) : Value := if s.options.phase != 0 then 1 else 0xFF

/-- Pop assigned variables off the score heap (`largest_score_unassigned_variable`).
  -- FUEL: bounded by the heap size; each iteration pops one element. -/
def largestScoreLoop (s : Solver) (fuel : Nat) : UInt32 × Solver :=
  match fuel with
  | 0 => (s.scores.maxHeap, s)
  | fuel + 1 =>
    let res := s.scores.maxHeap
    if s.value (LIT res) != 0 then
      let (_, h) := s.scores.popMax
      largestScoreLoop { s with scores := h } fuel
    else (res, s)

/-- Port of `largest_score_unassigned_variable` (decide.c, static). -/
def largestScoreUnassignedVariable (s : Solver) : UInt32 × Solver :=
  largestScoreLoop s (s.scores.sizeHeap + 1)

/-- Port of `kissat_start_random_sequence` (decide.c). -/
def startRandomSequence (s : Solver) : Solver :=
  if s.options.randec == 0 then s
  else if s.stable && s.options.randecstable == 0 then s
  else if !s.stable && s.options.randecfocused == 0 then s
  else if s.randec != 0 then s
  else
    let s := INC! s random_sequences
    let count := s.stats.random_sequences
    let length : UInt32 := ((UInt64.ofNat s.options.randeclength).toFloat * kLogn count).toUInt32
    let s := { s with randec := length }
    -- UPDATE_CONFLICT_LIMIT (randec, random_sequences, LOGN, false)
    if s.inconsistent then s else
    let delta := s.updateConflictLimitDelta s.options.randecint count kLogn false 0
    let (lim, s) := s.conflictsPlus delta
    { s with limits := { s.limits with randecConflicts := lim } }

/-- One draw of the random number generator. -/
def randomDraw (s : Solver) : UInt32 × Solver :=
  let (r, rng) := Generator.nextRandom32 s.random
  (r, { s with random := rng })

/-- The `for (;;)` loop of `next_random_decision`.
  -- FUEL: `2^64` draws. The generator is a full-period LCG modulo `2^64`
  (Hull–Dobell), so within one period its upper 32 bits take every value and every
  index `< VARS ≤ 2^32` is drawn; hence the loop finds the (existing, since
  `unassigned > 0`) active unassigned variable before running out. Out of fuel
  returns `INVALID_IDX` (falls back to the heuristic decision). -/
def randomPickLoop (s : Solver) (fuel : Nat) : UInt32 × Solver :=
  match fuel with
  | 0 => (INVALID_IDX, s)
  | fuel + 1 =>
    let (r, s) := s.randomDraw
    let idx := r % s.vars
    if !s.isActive idx then randomPickLoop s fuel
    else if s.value (LIT idx) != 0 then randomPickLoop s fuel
    else (idx, s)

/-- Start (or continue) a random decision sequence: `none` if no random decision is made. -/
def randomStart (s : Solver) : Option Solver :=
  if s.randec == 0 then
    if s.level > 1 then none
    else if s.stats.conflicts < s.limits.randecConflicts then none
    else some s.startRandomSequence
  else some s

/-- Port of `next_random_decision` (decide.c, static). -/
def nextRandomDecision (s : Solver) : UInt32 × Solver :=
  if s.vars == 0 then (INVALID_IDX, s)
  else if s.warming then (INVALID_IDX, s)
  else if s.options.randec == 0 then (INVALID_IDX, s)
  else if s.stable && s.options.randecstable == 0 then (INVALID_IDX, s)
  else if !s.stable && s.options.randecfocused == 0 then (INVALID_IDX, s)
  else
    match s.randomStart with
    | none => (INVALID_IDX, s)
    | some s => randomPickLoop s (2 ^ 64)

/-- Port of `kissat_next_decision_variable` (decide.c). -/
def nextDecisionVariable (s : Solver) : UInt32 × Solver :=
  let (res, s) := s.nextRandomDecision
  if res == INVALID_IDX then
    if s.stable then
      -- INC (score_decisions): METRIC
      s.largestScoreUnassignedVariable
    else
      -- INC (queue_decisions): STATISTIC
      let (res, q) := s.queue.lastEnqueuedUnassigned s.asg.values
      (res, { s with queue := q })
  else
    -- INC (random_decisions): STATISTIC
    (res, s)

/-- Port of `kissat_decide_phase` (decide.c). Returns `true` for positive phase. -/
def decidePhase (s : Solver) (idx : UInt32) : Bool :=
  let force := s.options.forcephase != 0
  let useTarget :=
    if force then false
    else if s.options.target == 0 then false
    else s.stable || s.options.target > 1
  let useSaved := !force && s.options.phasesaving != 0
  let res : Value :=
    if !s.stable then
      match (s.stats.switched >>> 1) &&& 7 with
      | 1 => s.initialPhase
      | 3 => s.initialPhase.neg
      | _ => 0
    else 0
  let res := if res == 0 && useTarget then s.phaseTarget.get! idx.toNat else res
  let res := if res == 0 && useSaved then s.asg.phaseSaved.get! idx.toNat else res
  let res := if res == 0 then s.initialPhase else res
  !vFalse res

/-- The counter and level increment at the start of `kissat_decide`. -/
def decideStart (s : Solver) : Solver :=
  let s := if s.warming then INC! s warming_decisions
    else INC! s decisions  -- {stable,focused}_decisions: METRIC
  { s with level := s.level + 1 }

/-- The decision on variable `idx` in `kissat_decide`. -/
def decideOn (s : Solver) (idx : UInt32) : Solver :=
  -- ASSERT (checked): C asserts that the decision variable is unassigned
  -- (`kissat_assign`); if it is not, stop with `unknown`.
  if idx ≥ s.vars || s.value (LIT idx) != 0 then { s with notPorted := true } else
  let lit := LIT idx
  let lit := if s.decidePhase idx then lit else NOT lit
  let s := s.pushFrame lit
  s.assignDecision lit

/-- Port of `kissat_decide` (decide.c). -/
def decide (s : Solver) : Solver :=
  let s := s.decideStart
  let (idx, s) := s.nextDecisionVariable
  s.decideOn idx

/-- Port of `kissat_internal_assume` (decide.c). -/
def internalAssume (s : Solver) (lit : Lit) : Solver :=
  let s := { s with level := s.level + 1 }
  (s.pushFrame lit).assignDecision lit

end Solver
end LeanKissat
