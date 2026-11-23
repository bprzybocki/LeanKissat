import LeanKissat.Search.Reduce
import LeanKissat.Search.Rephase
import LeanKissat.Search.Reorder
import LeanKissat.Frontend.SolverInterface

/-
The `kissat.h` API used by the application (`internal.c`).
-/
namespace LeanKissat
namespace Solver

/-- Port of `kissat_set_conflict_limit` (internal.c). -/
def setConflictLimit (s : Solver) (limit : Nat) : Solver :=
  { s with limited := { s.limited with conflicts := true },
           limits := { s.limits with conflicts := s.stats.conflicts + UInt64.ofNat limit } }

/-- Port of `kissat_set_decision_limit` (internal.c). -/
def setDecisionLimit (s : Solver) (limit : Nat) : Solver :=
  { s with limited := { s.limited with decisions := true },
           limits := { s.limits with decisions := s.stats.decisions + UInt64.ofNat limit } }

/-- Port of `kissat_value` (internal.c). Eliminated variables take their value
  from the `eliminated` stack (filled by `kissat_extend`, ported with elimination). -/
def valueOf (s : Solver) (elit : Int) : Int :=
  let eidx := elit.natAbs
  if eidx ≥ s.importLit.size then 0 else
  let bits := s.importBits.get! eidx
  if bits &&& ImportBits.imported == 0 then 0 else
  let tmp : Value :=
    if bits &&& ImportBits.eliminated != 0 then
      s.eliminated.get! (s.importLit.get! eidx).toNat
    else s.value (s.importLit.get! eidx)
  if tmp == 0 then 0 else
  let tmp := if elit < 0 then tmp.neg else tmp
  if vFalse tmp then -elit else elit

/-- Procedures available so far. -/
def procedures : Procedures :=
  { reduce := Solver.reduce, reorder := Solver.reorder, rephase := Solver.rephase }

end Solver

open Frontend in
instance : SolverInterface Solver where
  init o := Solver.init o
  reserve s n := s.reserve n
  add s lit := s.add lit.toInt
  solve s lim := do
    let s := match lim.conflicts with | some n => s.setConflictLimit n | none => s
    let s := match lim.decisions with | some n => s.setDecisionLimit n | none => s
    let (res, s) := Solver.search Solver.procedures s
    let r : SolveResult := if res == 10 then .sat else if res == 20 then .unsat else .unknown
    if s.notPorted then
      IO.eprintln "c [lkissat] stopped: reached a procedure that is not ported yet"
    pure (r, s)
  value s lit := Int32.ofInt (s.valueOf lit.toInt)
  statistics s := s.stats.toStats

end LeanKissat
