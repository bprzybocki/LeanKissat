import Lean
namespace LeanKissat.BitTac
theorem bv32_eq_iff {x y : BitVec 32} : x = y ↔ (x.getLsbD 0 = y.getLsbD 0 ∧ x.getLsbD 1 = y.getLsbD 1 ∧ x.getLsbD 2 = y.getLsbD 2 ∧ x.getLsbD 3 = y.getLsbD 3 ∧ x.getLsbD 4 = y.getLsbD 4 ∧ x.getLsbD 5 = y.getLsbD 5 ∧ x.getLsbD 6 = y.getLsbD 6 ∧ x.getLsbD 7 = y.getLsbD 7 ∧ x.getLsbD 8 = y.getLsbD 8 ∧ x.getLsbD 9 = y.getLsbD 9 ∧ x.getLsbD 10 = y.getLsbD 10 ∧ x.getLsbD 11 = y.getLsbD 11 ∧ x.getLsbD 12 = y.getLsbD 12 ∧ x.getLsbD 13 = y.getLsbD 13 ∧ x.getLsbD 14 = y.getLsbD 14 ∧ x.getLsbD 15 = y.getLsbD 15 ∧ x.getLsbD 16 = y.getLsbD 16 ∧ x.getLsbD 17 = y.getLsbD 17 ∧ x.getLsbD 18 = y.getLsbD 18 ∧ x.getLsbD 19 = y.getLsbD 19 ∧ x.getLsbD 20 = y.getLsbD 20 ∧ x.getLsbD 21 = y.getLsbD 21 ∧ x.getLsbD 22 = y.getLsbD 22 ∧ x.getLsbD 23 = y.getLsbD 23 ∧ x.getLsbD 24 = y.getLsbD 24 ∧ x.getLsbD 25 = y.getLsbD 25 ∧ x.getLsbD 26 = y.getLsbD 26 ∧ x.getLsbD 27 = y.getLsbD 27 ∧ x.getLsbD 28 = y.getLsbD 28 ∧ x.getLsbD 29 = y.getLsbD 29 ∧ x.getLsbD 30 = y.getLsbD 30 ∧ x.getLsbD 31 = y.getLsbD 31) := by
  constructor
  · intro h; subst h; simp
  · intro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | 8, _ => exact h8
    | 9, _ => exact h9
    | 10, _ => exact h10
    | 11, _ => exact h11
    | 12, _ => exact h12
    | 13, _ => exact h13
    | 14, _ => exact h14
    | 15, _ => exact h15
    | 16, _ => exact h16
    | 17, _ => exact h17
    | 18, _ => exact h18
    | 19, _ => exact h19
    | 20, _ => exact h20
    | 21, _ => exact h21
    | 22, _ => exact h22
    | 23, _ => exact h23
    | 24, _ => exact h24
    | 25, _ => exact h25
    | 26, _ => exact h26
    | 27, _ => exact h27
    | 28, _ => exact h28
    | 29, _ => exact h29
    | 30, _ => exact h30
    | 31, _ => exact h31
    | _ + 32, hi => omega

theorem bv8_eq_iff {x y : BitVec 8} : x = y ↔ (x.getLsbD 0 = y.getLsbD 0 ∧ x.getLsbD 1 = y.getLsbD 1 ∧ x.getLsbD 2 = y.getLsbD 2 ∧ x.getLsbD 3 = y.getLsbD 3 ∧ x.getLsbD 4 = y.getLsbD 4 ∧ x.getLsbD 5 = y.getLsbD 5 ∧ x.getLsbD 6 = y.getLsbD 6 ∧ x.getLsbD 7 = y.getLsbD 7) := by
  constructor
  · intro h; subst h; simp
  · intro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | _ + 8, hi => omega

theorem u32_lt_2pow31 (b : UInt32) : b < 0x80000000 ↔ b.toBitVec.getLsbD 31 = false := by
  rw [UInt32.lt_iff_toNat_lt, BitVec.getLsbD, UInt32.toNat_toBitVec, Nat.testBit_eq_decide_div_mod_eq]
  have := UInt32.toNat_lt b
  simp only [UInt32.reduceToNat, decide_eq_false_iff_not]
  omega


theorem u32_mul_two (a : UInt32) : a * (2 : UInt32) = a <<< (1 : UInt32) := by
  apply UInt32.toNat_inj.mp; simp [UInt32.toNat_mul, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]

end LeanKissat.BitTac

namespace LeanKissat.BitTac
open Lean Meta Elab Tactic

/-- Atoms: Boolean bit terms `x.toBitVec[k]` / `x.getLsbD k` of non-literal bit vectors. -/
def findAtom? (e : Expr) : Option Expr :=
  e.find? fun t =>
    (t.isAppOfArity ``GetElem.getElem 8 || t.isAppOfArity ``BitVec.getLsbD 3) &&
      (t.getAppFn.constName? == some ``BitVec.getLsbD || (t.getArg! 0).isAppOf ``BitVec) &&
      !t.hasLooseBVars

/-- Split on bit atoms of the goal, closing each branch with `simp_all`. -/
def splitAtoms : Nat → TacticM Unit
  | 0 => throwError "bv_k: out of fuel"
  | fuel + 1 => do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    match findAtom? ty with
    | none => evalTactic (← `(tactic| simp_all (config := {decide := true})))
    | some a =>
      let stx ← Term.exprToSyntax a
      evalTactic (← `(tactic| cases h : $stx <;> simp_all (config := {decide := true}) <;> fail))
        <|> do
          evalTactic (← `(tactic| cases _h : $stx <;> try simp_all (config := {decide := true})))
          for g' in (← getGoals) do
            setGoals [g']
            splitAtoms fuel

elab "bv_split" : tactic => do
  evalTactic (← `(tactic| repeat' apply And.intro))
  for g in (← getGoals) do
    setGoals [g]
    splitAtoms 12

end LeanKissat.BitTac

open LeanKissat.BitTac in
/-- Kernel-checked bit-blasting for small `UInt32`/`UInt8` goals (replaces `bv_k`). -/
macro "bv_k" : tactic => `(tactic| (
  try simp only [u32_lt_2pow31, u32_mul_two, ne_eq, bne_iff_ne, bne_eq_false_iff_eq, ← UInt32.toBitVec_inj, ← UInt8.toBitVec_inj,
    UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_xor, UInt32.toBitVec_not,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight, UInt32.toBitVec_ofNat, UInt32.toBitVec_sub,
    UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32,
    UInt8.toBitVec_and, UInt8.toBitVec_or, UInt8.toBitVec_xor, UInt8.toBitVec_not, UInt8.toBitVec_ofNat,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod, BitVec.toNat_ofNat] at *
  try simp only [bv32_eq_iff, bv8_eq_iff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth,
    BitVec.ofNat_sub_ofNat] at *
  try simp (config := {decide := true}) only [Nat.testBit_eq_decide_div_mod_eq, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, decide_true, decide_false] at *
  try simp (config := {decide := true}) at *
  try simp_all (config := {decide := true})
  try bv_split))
