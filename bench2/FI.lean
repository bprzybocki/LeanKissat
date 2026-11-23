import LeanKissat.Proofs.PropSpec
open LeanKissat Solver
example (probing jump : Bool) (level : UInt32) (notLit : Lit) (ws : WVec) (p q : Nat) (a : Asg) (arena : Arena) (dl : U32Vec) (s : Solver) (ticks : UInt64) (res : Option CRef) :
  (propLoop none false probing jump level notLit ws p q a arena dl s ticks res).p = 0 := by
  fun_induction propLoop none false probing jump level notLit ws p q a arena dl s ticks res
  all_goals trace_state
  all_goals sorry
