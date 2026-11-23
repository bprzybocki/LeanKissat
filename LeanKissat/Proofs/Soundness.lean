import LeanKissat.Proofs.RedMain

/-!
# Soundness of `solveCNF` in the `--plain` configuration

* result 20 (UNSAT) implies that `F` is unsatisfiable;
* result 10 (SAT) implies that the reported model satisfies `F`.

The hypothesis on the reduce procedure of `Main.lean` is discharged by `reduce_ok`.
-/

namespace LeanKissat
open Std.Sat
open Solver

theorem solveCNF_unsat_sound {opts : Options} {F : CNF Nat} (hc : PlainConfig opts) (hv : CNF.ValidVars F) :
    (solveCNF opts F).1 = 20 → F.Unsat :=
  solveCNF_unsat hc hv (reduce_ok (PhiF F))

theorem solveCNF_sat_sound {opts : Options} {F : CNF Nat} (hc : PlainConfig opts) (hv : CNF.ValidVars F) :
    (solveCNF opts F).1 = 10 → F.Sat (modelOf (solveCNF opts F).2) :=
  solveCNF_sat hc hv (reduce_ok (PhiF F))

end LeanKissat
