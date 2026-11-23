import LeanKissat.Search.Reduce

/-
Warming up saved phases by unit propagation (`warmup.c`) with beyond-conflict
propagation (`propbeyond.c`, i.e. `proplit.h` with
`CONTINUE_PROPAGATING_AFTER_CONFLICT`).
-/
namespace LeanKissat
namespace Solver

/-- Port of `propagate_literals_beyond_conflicts` (propbeyond.c): propagate all trail
  literals from position `i`, ignoring conflicts (`INC (warming_conflicts)` is a
  STATISTIC).
  -- FUEL: `bound` is the trail capacity (`vars`); the invariant
  `trail.size ≤ vars` guarantees the guard `i < bound` never stops early. -/
def propagateBeyondLoop (bound : Nat) (s : Solver) (i : Nat) : Solver × Nat :=
  if _h : i < s.asg.trail.size ∧ i < bound then
    let lit := s.asg.trail.get! i
    let (s, _) := s.propagateLiteral none true lit
    propagateBeyondLoop bound s (i + 1)
  else (s, i)
termination_by bound - i

/-- Port of `kissat_propagate_beyond_conflicts` (propbeyond.c). -/
def propagateBeyondConflicts (s : Solver) : Solver :=
  let s := { s with ticks := 0 }
  let saved := s.propagate
  let (s, i) := propagateBeyondLoop s.vars.toNat s s.propagate
  let s := { s with propagate := i }
  let propagated := UInt64.ofNat (i - saved)
  -- ADD (ticks, ...): STATISTIC
  let s := ADD! s propagations propagated
  ADD! s warming_propagations propagated

/-- The `while (solver->unassigned)` loop of `kissat_warmup`.
  -- FUEL: every iteration makes one decision, which assigns a variable, so at most
  `unassigned` iterations are needed (`fuel = unassigned + 1` initially).
  `TERMINATED (warmup_terminated_1)` only reads `termination.flagged`, which cannot
  change inside the pure core. -/
def warmupLoop (s : Solver) (fuel : Nat) : Solver :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    if s.asg.unassigned == 0 || s.terminationFlagged then s
    else warmupLoop s.decide.propagateBeyondConflicts fuel

/-- Port of `kissat_warmup` (warmup.c). -/
def warmup (s : Solver) : Solver :=
  let s := { s with warming := true }
  let s := INC! s warmups
  let s := warmupLoop s (s.asg.unassigned.toNat + 1)
  let s := s.backtrackWithoutUpdatingPhases 0
  { s with warming := false }

end Solver
end LeanKissat
