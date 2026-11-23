import LeanKissat.Core.Watch

/-
Assignments: `inlineassign.h`, `fastassign.h`, `assign.c`.
-/
namespace LeanKissat
namespace Solver

/-- The assignment-record part of `kissat_fast_assign` (inlineassign.h). The
  root-level part (`kissat_mark_fixed_literal`, which does not read or write
  the assignment record) is done by the caller (`Solver.assign`). -/
@[noinline] def _root_.LeanKissat.Asg.assign (a : Asg) (probing : Bool) (level : UInt32) (binary : Bool)
    (lit : Lit) (reason : UInt32) : Asg :=
  -- PERF: written branch-free (masks instead of `if`): a branch here makes the
  -- compiler rebuild the record instead of updating it in place.
  let notLit := NOT lit
  let idx := IDX lit
  let root : UInt32 := (level == 0).toUInt32
  let fixReason : UInt32 := root &&& ((reason == UNIT_REASON).toUInt32 ^^^ 1)
  let fixMask : UInt32 := 0 - fixReason
  let binaryBit : UInt32 := binary.toUInt32 &&& (fixReason ^^^ 1)
  let reason := reason ^^^ ((reason ^^^ UNIT_REASON) &&& fixMask)
  let trailPos := UInt32.ofNat a.trail.size
  let neg : UInt8 := (lit &&& 1).toUInt8
  let newPhase : UInt8 := 1 + 0xFE * neg          -- `BOOL_TO_VALUE (NEGATED (lit))`
  let oldPhase := a.phaseSaved.get! idx.toNat
  let phase := newPhase ^^^ ((newPhase ^^^ oldPhase) &&& (0 - probing.toUInt8))
  { a with
    values := (a.values.set! lit.toNat VAL_TRUE).set! notLit.toNat VAL_FALSE
    unassigned := a.unassigned - 1
    unflushed := a.unflushed + root
    trail := a.trail.push lit
    phaseSaved := a.phaseSaved.set! idx.toNat phase
    aLevel := a.aLevel.set! idx.toNat level
    aTrail := a.aTrail.set! idx.toNat trailPos
    aReason := a.aReason.set! idx.toNat reason
    aBits := a.aBits.set! idx.toNat (binaryBit.toUInt8 <<< 1) }

/-- Port of `kissat_fast_assign` / `kissat_assign` (inlineassign.h). -/
@[noinline] def assign (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool)
    (lit : Lit) (reason : UInt32) : Solver :=
  let s := if level == 0 then s.markFixedLiteral lit else s
  let a := s.asg
  let s := { s with asg := {} }
  { s with asg := a.assign probing level binary lit reason }

/-- `kissat_assignment_level` on the unpacked state. -/
def asgAssignmentLevel (arena : Arena) (aLevel : U32Vec) (lit : Lit) (ref : Ref) (i n : Nat)
    (res : UInt32) : UInt32 :=
  if h : i < n then
    let other := arena.lit ref i
    let l := if other != lit then aLevel.get! (IDX other).toNat else 0
    asgAssignmentLevel arena aLevel lit ref (i + 1) n (if res < l then l else res)
  else res
termination_by n - i

/-- Port of `kissat_assignment_level` (inlineassign.h): maximum level of the other
  literals of the large clause `ref`. -/
def assignmentLevel (s : Solver) (lit : Lit) (ref : Ref) : UInt32 :=
  asgAssignmentLevel s.arena s.asg.aLevel lit ref 0 (s.arena.size ref).toNat 0

/-- Port of `kissat_assign_unit` (assign.c). -/
@[inline] def assignUnit (s : Solver) (lit : Lit) : Solver :=
  s.assign s.probing 0 false lit UNIT_REASON

/-- Port of `kissat_learned_unit` (assign.c). -/
@[inline] def learnedUnit (s : Solver) (lit : Lit) : Solver := s.assignUnit lit

/-- Port of `kissat_original_unit` (assign.c). -/
@[inline] def originalUnit (s : Solver) (lit : Lit) : Solver := s.assignUnit lit

/-- Port of `kissat_assign_decision` (assign.c). -/
@[inline] def assignDecision (s : Solver) (lit : Lit) : Solver :=
  s.assign s.probing s.level false lit DECISION_REASON

/-- Port of `kissat_assign_binary` (assign.c). -/
def assignBinary (s : Solver) (lit other : Lit) : Solver :=
  let oidx := IDX other
  let level := s.levelIdx oidx
  let (s, other) :=
    if s.options.jumpreasons != 0 && level != 0 && s.isBinaryReason oidx then
      (s, s.reasonIdx oidx) -- INC (jumped_reasons): STATISTIC
    else (s, other)
  s.assign s.probing level true lit other

/-- Port of `kissat_fast_binary_assign` (fastassign.h). -/
@[noinline] def fastBinaryAssign (s : Solver) (probing : Bool) (level : UInt32)
    (lit other : Lit) : Solver :=
  if s.options.jumpreasons != 0 && level != 0 && s.classification.bigbig &&
      s.isBinaryReason (IDX other) then
    -- INC (jumped_reasons): STATISTIC
    s.assign probing level true lit (s.reasonIdx (IDX other))
  else s.assign probing level true lit other

/-- Port of `kissat_assign_reference` / `kissat_fast_assign_reference`. -/
@[noinline] def assignReference (s : Solver) (lit : Lit) (ref : Ref) : Solver :=
  let level := s.assignmentLevel lit ref
  s.assign s.probing level false lit ref

end Solver
end LeanKissat
