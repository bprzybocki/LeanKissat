import LeanKissat.Proofs.AnaFrame

/-!
# Analysis bits in `assigned[idx]`
-/

namespace LeanKissat
namespace Solver

/-- The analysis bits (`analyzed | poisoned | removable | shrinkable`). -/
def anaMask : UInt8 := ABits.analyzed ||| ABits.poisoned ||| ABits.removable ||| ABits.shrinkable

/-- No analysis bit is set (outside of conflict analysis). -/
def Clean (s : Solver) : Prop := ∀ i, (s.asg.aBits.get! i &&& anaMask) = 0

theorem setABit_bits (s : Solver) (idx : UInt32) (b : UInt8) (on : Bool) (j : Nat) :
    (s.setABit idx b on).asg.aBits.get! j =
      if idx.toNat = j ∧ idx.toNat < s.asg.aBits.size then
        (if on then s.asg.aBits.get! j ||| b else s.asg.aBits.get! j &&& ~~~b)
      else s.asg.aBits.get! j := by
  simp only [setABit, abits]
  rw [ByteArray.get!_set!]
  by_cases e : idx.toNat = j
  · subst e; simp
  · simp [e]

theorem setABit_af (s : Solver) (idx : UInt32) (b : UInt8) (on : Bool) (hb : b &&& ABits.binary = 0) :
    AF (s.setABit idx b on) s := by
  refine ⟨rfl, rfl, rfl, rfl, by simp [setABit], fun i => ?_, rfl, Arena.Same.refl _, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [setABit_bits]
  split
  · split
    · simp only [ABits.binary] at hb ⊢
      generalize s.asg.aBits.get! i = w; revert hb; generalize b = b'; intro hb; bv_k
    · simp only [ABits.binary] at hb ⊢
      generalize s.asg.aBits.get! i = w; revert hb; generalize b = b'; intro hb; bv_k
  · rfl

theorem analyzed_bin : ABits.analyzed &&& ABits.binary = 0 := by decide
theorem poisoned_bin : ABits.poisoned &&& ABits.binary = 0 := by decide
theorem removable_bin : ABits.removable &&& ABits.binary = 0 := by decide
theorem shrinkable_bin : ABits.shrinkable &&& ABits.binary = 0 := by decide

theorem u8_or_and_self (w c : UInt8) (hc : c ≠ 0) : ((w ||| c) &&& c != 0) = true := by
  simp only [bne_iff_ne, ne_eq]; intro h; apply hc; bv_k
theorem u8_andnot_and_self (w c : UInt8) : ((w &&& ~~~c) &&& c != 0) = false := by
  simp only [bne_eq_false_iff_eq]; bv_k
theorem u8_or_and_other (w b c : UInt8) (h : b &&& c = 0) : ((w ||| b) &&& c) = (w &&& c) := by
  bv_k
theorem u8_andnot_and_other (w b c : UInt8) (h : b &&& c = 0) : ((w &&& ~~~b) &&& c) = (w &&& c) := by
  bv_k

/-- The value of an analysis bit after setting a (possibly different) bit. -/
theorem abit_setABit (s : Solver) (idx i : UInt32) (b c : UInt8) (on : Bool)
    (hsz : idx.toNat < s.asg.aBits.size) (hbc : (b = c ∧ c ≠ 0) ∨ (b ≠ c ∧ b &&& c = 0)) :
    (s.setABit idx b on).abit i c =
      if idx = i ∧ b = c then on else s.abit i c := by
  unfold abit abits
  rw [setABit_bits]
  by_cases e : idx = i
  · subst e
    simp only [hsz, and_self, ite_true, true_and]
    rcases hbc with ⟨rfl, hc⟩ | hbc
    · simp only [ite_true]
      cases on
      · simp only [Bool.false_eq_true, ite_false]; exact u8_andnot_and_self _ _
      · simp only [ite_true]; exact u8_or_and_self _ _ hc
    · obtain ⟨hne, hbc⟩ := hbc
      simp only [hne, ite_false]
      cases on
      · simp only [Bool.false_eq_true, ite_false]; rw [u8_andnot_and_other _ _ _ hbc]
      · simp only [ite_true]; rw [u8_or_and_other _ _ _ hbc]
  · have : ¬ (idx.toNat = i.toNat) := fun h => e (UInt32.toNat_inj.mp h)
    simp [this, e]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem AF.trans_left {a b c : Solver} (h2 : AF b c) (h1 : AF a b) : AF a c := h1.trans h2

/-- `AF` for updates that leave all frame fields syntactically equal. -/
macro "af_rfl" : term => `(⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, Arena.Same.refl _, rfl, rfl, rfl, rfl,
  rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- Close `AF (f b) s` from `h : AF b s` when `f` only touches non-frame fields. -/
macro "af_step" : tactic => `(tactic|
  (simp (config := {zetaDelta := true}) only [] at *; first
      | exact AF.trans_left ‹_› af_rfl
      | exact AF.refl _))

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The four analysis bits that are tracked by stacks. -/
def AnaBit (c : UInt8) : Prop :=
  c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable

/-- The stack recording the variables with analysis bit `c`. -/
def anaList (s : Solver) (c : UInt8) : List UInt32 :=
  if c = ABits.analyzed then s.analyzed.view else if c = ABits.poisoned then s.poisoned.view
  else if c = ABits.removable then s.removable.view else s.shrinkable.view

/-- Every set analysis bit is recorded on its stack (needed to clear all bits at the end of
  conflict analysis). -/
def Listed (s : Solver) : Prop := ∀ c, AnaBit c → ∀ i, s.abit i c = true → i ∈ s.anaList c

theorem setABit_true_abit (s : Solver) (idx i : UInt32) (b c : UInt8) (hsz : idx.toNat < s.asg.aBits.size)
    (hb : AnaBit b) (hc : AnaBit c) :
    (s.setABit idx b true).abit i c = if idx = i ∧ b = c then true else s.abit i c := by
  apply abit_setABit s idx i b c true hsz
  rcases hb with rfl | rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem listed_push {s t : Solver} {idx : UInt32} {b : UInt8}
    (hbits : ∀ i c, AnaBit c → t.abit i c = if idx = i ∧ b = c then true else s.abit i c)
    (hl : ∀ c, AnaBit c → ∀ i ∈ s.anaList c, i ∈ t.anaList c) (hnew : idx ∈ t.anaList b)
    (h : Listed s) : Listed t := by
  intro c hc i hi
  rw [hbits i c hc] at hi
  by_cases e : idx = i ∧ b = c
  · obtain ⟨rfl, rfl⟩ := e; exact hnew
  · rw [if_neg e] at hi; exact hl c hc i (h c hc i hi)

theorem anaBit_removable : AnaBit ABits.removable := Or.inr (Or.inr (Or.inl rfl))
theorem anaBit_poisoned : AnaBit ABits.poisoned := Or.inr (Or.inl rfl)
theorem anaBit_shrinkable : AnaBit ABits.shrinkable := Or.inr (Or.inr (Or.inr rfl))
theorem anaBit_analyzed : AnaBit ABits.analyzed := Or.inl rfl

theorem pushRemovable_listed (s : Solver) (idx : UInt32) (hsz : idx.toNat < s.asg.aBits.size)
    (h : Listed s) : Listed (s.pushRemovable idx) := by
  refine listed_push (b := ABits.removable) (fun i c hc => setABit_true_abit s idx i _ c hsz anaBit_removable hc)
    ?_ ?_ h
  · intro c hc i hi
    have e1 : (s.pushRemovable idx).analyzed = s.analyzed := rfl
    have e2 : (s.pushRemovable idx).poisoned = s.poisoned := rfl
    have e3 : (s.pushRemovable idx).shrinkable = s.shrinkable := rfl
    have e4 : (s.pushRemovable idx).removable = s.removable.push idx := rfl
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [anaList, e1, e2, e3, e4, U32Vec.view_push, ABits.analyzed, ABits.poisoned, ABits.removable,
        ABits.shrinkable] at hi ⊢ <;> simp [hi]
  · have e4 : (s.pushRemovable idx).removable = s.removable.push idx := rfl
    simp [anaList, e4, U32Vec.view_push, ABits.analyzed, ABits.poisoned, ABits.removable]

theorem pushPoisoned_listed (s : Solver) (idx : UInt32) (hsz : idx.toNat < s.asg.aBits.size)
    (h : Listed s) : Listed (s.pushPoisoned idx) := by
  refine listed_push (b := ABits.poisoned) (fun i c hc => setABit_true_abit s idx i _ c hsz anaBit_poisoned hc)
    ?_ ?_ h
  · intro c hc i hi
    have e1 : (s.pushPoisoned idx).analyzed = s.analyzed := rfl
    have e2 : (s.pushPoisoned idx).poisoned = s.poisoned.push idx := rfl
    have e3 : (s.pushPoisoned idx).shrinkable = s.shrinkable := rfl
    have e4 : (s.pushPoisoned idx).removable = s.removable := rfl
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [anaList, e1, e2, e3, e4, U32Vec.view_push, ABits.analyzed, ABits.poisoned, ABits.removable,
        ABits.shrinkable] at hi ⊢ <;> simp [hi]
  · have e2 : (s.pushPoisoned idx).poisoned = s.poisoned.push idx := rfl
    simp [anaList, e2, U32Vec.view_push, ABits.analyzed, ABits.poisoned]

theorem pushShrinkable_listed (s : Solver) (idx : UInt32) (hsz : idx.toNat < s.asg.aBits.size)
    (h : Listed s) : Listed (s.pushShrinkable idx) := by
  refine listed_push (b := ABits.shrinkable) (fun i c hc => setABit_true_abit s idx i _ c hsz anaBit_shrinkable hc)
    ?_ ?_ h
  · intro c hc i hi
    have e1 : (s.pushShrinkable idx).analyzed = s.analyzed := rfl
    have e2 : (s.pushShrinkable idx).poisoned = s.poisoned := rfl
    have e3 : (s.pushShrinkable idx).shrinkable = s.shrinkable.push idx := rfl
    have e4 : (s.pushShrinkable idx).removable = s.removable := rfl
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [anaList, e1, e2, e3, e4, U32Vec.view_push, ABits.analyzed, ABits.poisoned, ABits.removable,
        ABits.shrinkable] at hi ⊢ <;> simp [hi]
  · have e3 : (s.pushShrinkable idx).shrinkable = s.shrinkable.push idx := rfl
    simp [anaList, e3, U32Vec.view_push, ABits.analyzed, ABits.poisoned, ABits.removable, ABits.shrinkable]

theorem pushAnalyzed_listed (s : Solver) (idx : UInt32) (hsz : idx.toNat < s.asg.aBits.size)
    (h : Listed s) : Listed (s.pushAnalyzed idx) := by
  refine listed_push (b := ABits.analyzed) (fun i c hc => setABit_true_abit s idx i _ c hsz anaBit_analyzed hc)
    ?_ ?_ h
  · intro c hc i hi
    have e1 : (s.pushAnalyzed idx).analyzed = s.analyzed.push idx := rfl
    have e2 : (s.pushAnalyzed idx).poisoned = s.poisoned := rfl
    have e3 : (s.pushAnalyzed idx).shrinkable = s.shrinkable := rfl
    have e4 : (s.pushAnalyzed idx).removable = s.removable := rfl
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [anaList, e1, e2, e3, e4, U32Vec.view_push, ABits.analyzed, ABits.poisoned, ABits.removable,
        ABits.shrinkable] at hi ⊢ <;> simp [hi]
  · have e1 : (s.pushAnalyzed idx).analyzed = s.analyzed.push idx := rfl
    simp [anaList, e1, U32Vec.view_push, ABits.analyzed]

end Solver
end LeanKissat
