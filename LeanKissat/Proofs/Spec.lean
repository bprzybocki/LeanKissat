import LeanKissat.Search.Api
import Std.Sat.CNF

/-!
# Top-level specification

`solveCNF opts F` is exactly what the `lkissat` binary does after parsing a DIMACS file whose
header declares `F.maxVar` variables: create the solver with the given options, reserve the
variables (`kissat_reserve`), add every clause of `F` literal by literal (`kissat_add`), then
call `kissat_solve`. Variable `v` of `F` is the external DIMACS variable `v + 1`.

The main theorems (`solveCNF_sat`, `solveCNF_unsat`, `Proofs/Main.lean`) state soundness for
the option values of the `--plain` configuration (`PlainConfig`). Results other than 10 and 20
(unknown, limits hit, overflow, resources, not-yet-ported procedures) carry no claim.
-/

namespace LeanKissat
open Std.Sat

/-- External (DIMACS) literal of a CNF literal: variable `v` ↦ `v + 1`. -/
def extLit (l : Literal Nat) : Int := if l.2 then (l.1 + 1 : Int) else -((l.1 + 1 : Nat) : Int)

/-- Add one clause (`kissat_add` for each literal, then `kissat_add (solver, 0)`). -/
def addClause (s : Solver) (c : CNF.Clause Nat) : Solver :=
  (c.literals.foldl (fun s l => s.add (extLit l)) s).add 0

/-- The number of variables of `F` (the largest DIMACS variable). -/
def _root_.Std.Sat.CNF.maxVar (F : CNF Nat) : Nat :=
  F.clauses.foldl (fun m c => c.literals.foldl (fun m l => max m (l.1 + 1)) m) 0

/-- Initialize, reserve the variables (`kissat_reserve` after the `p cnf` header), add all
  clauses of `F`, and solve. -/
def solveCNF (opts : Options) (F : CNF Nat) : UInt32 × Solver :=
  let s := F.clauses.foldl addClause ((Solver.init opts).reserve F.maxVar)
  Solver.search Solver.procedures s

/-- The model reported for variable `v` (`kissat_value (solver, v + 1) > 0`). -/
def modelOf (s : Solver) (v : Nat) : Bool := decide (s.valueOf (v + 1) > 0)

/-- Input restriction of `kissat_add`: variables must be below `EXTERNAL_MAX_VAR`. -/
def CNF.ValidVars (F : CNF Nat) : Prop :=
  ∀ c ∈ F.clauses, ∀ l ∈ c.literals, l.1 + 1 ≤ EXTERNAL_MAX_VAR

end LeanKissat
