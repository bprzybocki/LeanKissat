import LeanKissat.Search.Propagate

/-
Backtracking (`backtrack.c`), phase saving (`phases.c`), reason marking (`trail.c`).
-/
namespace LeanKissat
namespace Solver

/-- `save_phases` (phases.c): copy non-zero values of positive literals. -/
def savePhases (values phases : ByteArray) (vars : Nat) : ByteArray := Id.run do
  let mut phases := phases
  for idx in [0:vars] do
    let v := values.get! (2 * idx)
    if v != 0 then phases := phases.set! idx v
  return phases

/-- `kissat_save_best_phases`. -/
def saveBestPhases (s : Solver) : Solver :=
  let p := s.phaseBest
  let s := { s with phaseBest := .empty }
  { s with phaseBest := savePhases s.asg.values p s.vars.toNat }

/-- `kissat_save_target_phases`. -/
def saveTargetPhases (s : Solver) : Solver :=
  let p := s.phaseTarget
  let s := { s with phaseTarget := .empty }
  { s with phaseTarget := savePhases s.asg.values p s.vars.toNat }

/-- Port of `kissat_update_target_and_best_phases` (backtrack.c, static). -/
def updateTargetAndBestPhases (s : Solver) : Solver :=
  if s.probing || !s.stable then s else
  let assigned := s.assignedCount
  let s := if s.targetAssigned < assigned then
      let s := { s with targetAssigned := assigned }
      let s := s.saveTargetPhases
      s -- INC (target_saved): METRIC
    else s
  if s.bestAssigned < assigned then
    let s := { s with bestAssigned := assigned }
    let s := s.saveBestPhases
    s -- INC (best_saved): METRIC
  else s

/-- The unassign/compact loop of `kissat_backtrack_without_updating_phases`,
  on the assignment record `a`; heap/queue updates go to `s`. -/
def backtrackLoop (a : Asg) (s : Solver) (newLevel : UInt32) (p q stop : Nat) : Asg × Solver × Nat :=
  if h : p < stop then
    let lit := a.trail.get! p
    let idx := IDX lit
    let level := a.aLevel.get! idx.toNat
    if level ≤ newLevel then
      let a := { a with
        aTrail := a.aTrail.set! idx.toNat (UInt32.ofNat q)
        trail := a.trail.set! q lit }
      backtrackLoop a s newLevel (p + 1) (q + 1) stop
    else
      let notLit := NOT lit
      let a := { a with
        values := (a.values.set! lit.toNat 0).set! notLit.toNat 0
        unassigned := a.unassigned + 1 }
      let s := if s.stable then
          if !s.scores.contains idx then { s with scores := s.scores.push idx } else s
        else { s with queue := s.queue.addUnassignedBack idx }
      backtrackLoop a s newLevel (p + 1) q stop
  else (a, s, q)
termination_by stop - p

/-- Port of `kissat_backtrack_without_updating_phases` (backtrack.c). -/
def backtrackWithoutUpdatingPhases (s : Solver) (newLevel : UInt32) : Solver :=
  if s.level == newLevel then s else
  let newFrame := newLevel.toNat + 1
  let newEnd := (s.frameTrailAt (UInt32.ofNat newFrame)).toNat
  let s := s.shrinkFrames newFrame
  let a := s.asg
  let s := { s with asg := {} }
  match backtrackLoop a s newLevel newEnd newEnd a.trail.size with
  | (a, s, q) =>
    { s with asg := { a with trail := a.trail.shrink q }, level := newLevel, propagate := newEnd }

/-- Port of `kissat_backtrack_in_consistent_state`. -/
def backtrackInConsistentState (s : Solver) (newLevel : UInt32) : Solver :=
  s.updateTargetAndBestPhases.backtrackWithoutUpdatingPhases newLevel

/-- Port of `kissat_backtrack_after_conflict`. -/
def backtrackAfterConflict (s : Solver) (newLevel : UInt32) : Solver :=
  let s := if s.level != 0 then s.backtrackWithoutUpdatingPhases (s.level - 1) else s
  s.updateTargetAndBestPhases.backtrackWithoutUpdatingPhases newLevel

/-- Loop of `kissat_mark_reason_clauses` / `kissat_unmark_reason_clauses` (trail.c) over
  the trail positions `[i, n)`. -/
def markReasonLoop (start : Ref) (mark : Bool) (n : Nat) (s : Solver) (i : Nat) : Solver :=
  if i < n then
    let idx := IDX (s.asg.trail.get! i)
    let ref := s.reasonIdx idx
    -- C asserts `a->level > 0` (checked)
    let s := if s.levelIdx idx == 0 then { s with notPorted := true }
      else if s.isBinaryReason idx || ref == DECISION_REASON || ref < start then s
      else { s with arena := s.arena.setReason ref mark }
    markReasonLoop start mark n s (i + 1)
  else s
termination_by n - i

/-- Port of `kissat_mark_reason_clauses` / `kissat_unmark_reason_clauses` (trail.c). -/
def markReasonClauses (s : Solver) (start : Ref) (mark : Bool) : Solver :=
  markReasonLoop start mark s.asg.trail.size s 0

end Solver
end LeanKissat
