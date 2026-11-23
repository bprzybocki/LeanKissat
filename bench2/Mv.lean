import Std.Tactic.Do
open Std.Do

def sumTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    if i == 3 then continue
    acc := acc + 2
  return acc

theorem sumTo_even (n : Nat) : sumTo n % 2 = 0 := by
  generalize h : sumTo n = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨_, acc⟩ => ⌜acc % 2 = 0⌝
  all_goals mleave; omega
