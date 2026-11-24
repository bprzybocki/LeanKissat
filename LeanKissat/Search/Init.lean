import LeanKissat.Search.Lucky
import LeanKissat.Core.SortLits

/-
Solver initialization and clause addition (`internal.c`: `kissat_init`,
`kissat_add`, `kissat_value`).
-/
namespace LeanKissat
namespace Solver

/-- Port of `kissat_init` (internal.c) with given options. -/
def init (opts : Options) : Solver :=
  let s : Solver := { options := opts }
  let s := { s with queue := s.queue.init }
  -- `kissat_push_frame (solver, UINT_MAX)`
  let s := s.pushFrame INVALID_LIT
  { s with watching := true, scinc := 1.0, firstReducible := INVALID_REF,
           lastIrredundant := INVALID_REF }

/-- Port of `kissat_new_original_clause` (clause.c): sort literals, then add. -/
def newOriginalClause (s : Solver) : Ref × Solver :=
  let size := s.clause.size
  let lits := sortLiterals s.asg.values (fun idx => s.asg.aLevel.get! idx.toNat) s.clause 0 size
  let s := { s with clause := lits }
  s.newClause true false 0 s.clause

/-- Reset the marks of the clause literals from position `i` (end of `kissat_add`). -/
def clearClauseMarks (s : Solver) (i : Nat) : Solver :=
  if i < s.clause.size then
    let lit := s.clause.get! i
    clearClauseMarks { s with marks := (s.marks.set! lit.toNat 0).set! (NOT lit).toNat 0 } (i + 1)
  else s
termination_by s.clause.size - i

/-- `clearClauseMarks` on the marks alone. -/
def clearClauseMarksBytes (marks : ByteArray) (clause : U32Vec) (i : Nat) : ByteArray :=
  if i < clause.size then
    let lit := clause.get! i
    clearClauseMarksBytes ((marks.set! lit.toNat 0).set! (NOT lit).toNat 0) clause (i + 1)
  else marks
termination_by clause.size - i

/-- Executable version of `clearClauseMarks`; see `clearClauseMarks_eq_clearClauseMarksFast`. -/
def clearClauseMarksFast (s : Solver) (i : Nat) : Solver :=
  let marks := s.marks
  let s := { s with marks := .empty }
  { s with marks := clearClauseMarksBytes marks s.clause i }

private theorem clearClauseMarks_bytes (s : Solver) (i : Nat) :
    s.clearClauseMarks i = { s with marks := clearClauseMarksBytes s.marks s.clause i } := by
  fun_induction s.clearClauseMarks i with
  | case1 s i hi lit ih =>
    rw [ih]
    conv => rhs; unfold clearClauseMarksBytes
    rw [ite_eq_left hi]
  | case2 s i hi =>
    conv => rhs; unfold clearClauseMarksBytes
    rw [ite_eq_right hi]

/-- The compiler runs `clearClauseMarksFast`; proofs reason about `clearClauseMarks`. -/
@[csimp] theorem clearClauseMarks_eq_clearClauseMarksFast :
    @clearClauseMarks = @clearClauseMarksFast := by
  funext s i
  rw [clearClauseMarks_bytes]
  rfl

/-- The assignment after adding a clause whose first literal is unassigned or false. -/
def addAssign (s : Solver) (isize : Nat) (a b : Lit) (res : Ref) : Solver :=
  if isize == 2 then s.assignBinary a b else s.assignReference a res

/-- The assignment logic after adding a clause of size `isize ≥ 2` (internal.c). -/
def addTail (s : Solver) (isize : Nat) (res : Ref) : Solver :=
  let a := s.clause.get! 0
  let b := s.clause.get! 1
  let u := s.value a
  let v := s.value b
  let k := if u != 0 then s.level' a else UINT_MAX
  let l := if v != 0 then s.level' b else UINT_MAX
  if u == 0 && vFalse v then s.addAssign isize a b res
  else if vFalse u && k == l then s.backtrackWithoutUpdatingPhases (k - 1)
  else if vFalse u then s.addAssign isize a b res
  else if vTrue u && vFalse v then s
  else if u == 0 && vTrue v then s.addAssign isize a b res
  else s

/-- The clause-end part of `kissat_add` before resetting the clause (internal.c). -/
def addClauseBody (s : Solver) : Solver :=
  if s.inconsistent then s
  -- a flagged state (`unknown`, out of memory) does not add further clauses
  else if s.overflowed || s.outOfResources || s.notPorted then s
  else if s.clauseSatisfied then s
  else if s.clauseTrivial then s
  else
    let s := s.activateLiterals s.clause.toArray
    let isize := s.clause.size
    if isize == 0 then { s with inconsistent := true }
    else if isize == 1 then
      let unit := s.clause.back!
      let s := s.originalUnit unit
      if s.level == 0 then s.searchPropagate.1 else s
    else
      match s.newOriginalClause with
      | (res, s) => s.addTail isize res

/-- The clause-end part of `kissat_add` (internal.c). -/
def addClauseEnd (s : Solver) : Solver :=
  let s := s.addClauseBody.clearClauseMarks 0
  { s with clause := s.clause.clear, clauseSatisfied := false, clauseTrivial := false, clauseShrink := false }

/-- Port of `kissat_add` (internal.c). `elit = 0` terminates the clause. -/
def add (s : Solver) (elit : Int) : Solver :=
  if elit == 0 then s.addClauseEnd else
  let (ilit, s) := s.importLiteral elit
  let mark := s.mark ilit
  if mark == 0 then
    let value := s.fixedValue ilit
    if vTrue value then { s with clauseSatisfied := true }
    else if vFalse value then { s with clauseShrink := true }
    else
      { s with
        marks := (s.marks.set! ilit.toNat 1).set! (NOT ilit).toNat 0xFF
        clause := s.clause.push ilit }
  else if vFalse mark then { s with clauseTrivial := true }
  else { s with clauseShrink := true }

end Solver
end LeanKissat
