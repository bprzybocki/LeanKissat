import LeanKissat.Search.Walk

/-
Rephasing (`rephase.c`).
-/
namespace LeanKissat
namespace Solver

/-- Port of `rephase_best` (rephase.c). INC (rephased_best): METRIC. -/
def rephaseBest (s : Solver) : Solver := Id.run do
  let best := s.phaseBest
  let mut saved := s.asg.phaseSaved
  let mut s := { s with asg := { s.asg with phaseSaved := .empty } }
  for i in [0:s.vars.toNat] do
    let b := best.get! i
    if b != 0 then saved := saved.set! i b
  s := { s with asg := { s.asg with phaseSaved := saved } }
  return s

/-- Set all saved phases to `v` (`rephase_original` / `rephase_inverted`). -/
def rephaseConstant (s : Solver) (v : Value) : Solver := Id.run do
  let mut saved := s.asg.phaseSaved
  let mut s := { s with asg := { s.asg with phaseSaved := .empty } }
  for i in [0:s.vars.toNat] do
    saved := saved.set! i v
  s := { s with asg := { s.asg with phaseSaved := saved } }
  return s

/-- `INITIAL_PHASE` (decide.h) as a signed value. -/
@[inline] def initialPhaseValue (s : Solver) : Value :=
  if s.options.phase != 0 then VAL_TRUE else VAL_FALSE

/-- Port of `reset_phases` (rephase.c) with the schedule
  `best, walking, inverted, best, walking, original`. -/
def resetPhases (s : Solver) : Solver := Id.run do
  let count := s.stats.rephased
  let select := (count - 1) % 6
  let mut s := s
  let mut isBest := false
  if select == 0 || select == 3 then
    s := s.rephaseBest
    isBest := true
  else if select == 1 || select == 4 then
    -- rephase_walking (INC (rephased_walking): METRIC)
    s := s.walk
  else if select == 2 then
    -- rephase_inverted (INC (rephased_inverted): METRIC)
    s := s.rephaseConstant s.initialPhaseValue.neg
  else
    -- rephase_original (INC (rephased_original): METRIC)
    s := s.rephaseConstant s.initialPhaseValue
  -- memcpy (solver->phases.target, solver->phases.saved, VARS)
  let saved := s.asg.phaseSaved
  let mut target := s.phaseTarget
  s := { s with phaseTarget := .empty }
  for i in [0:s.vars.toNat] do
    target := target.set! i (saved.get! i)
  s := { s with phaseTarget := target }
  -- UPDATE_CONFLICT_LIMIT (rephase, rephased, NLOG3N, false)
  if !s.inconsistent then
    let delta := s.updateConflictLimitDelta s.options.rephaseint s.stats.rephased
      (kNlogpown · 3) false
      -- CLAMP: `rephaseint ≥ 10` and `n log³ n ≥ 1` for `n = rephased ≥ 1`
      (UInt64.ofNat s.options.rephaseint)
    let (lim, s') := s.conflictsPlus delta
    s := { s' with limits := { s'.limits with rephaseConflicts := lim } }
  s := { s with targetAssigned := 0 }
  if isBest then s := { s with bestAssigned := 0 }
  return s

/-- Port of `kissat_rephase` (rephase.c). -/
def rephase (s : Solver) : Solver :=
  let s := s.backtrackPropagateAndFlushTrail
  let s := INC! s rephased
  s.resetPhases

end Solver
end LeanKissat
