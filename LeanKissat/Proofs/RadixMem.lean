import LeanKissat.Util.Radix

/-!
# Radix sort keeps its elements

Every element of the result of `radixSortCore` on an `Array` satisfies a predicate `P`
that holds for all input elements and for `default`.
-/

namespace LeanKissat
namespace Radix

theorem forIn_list_inv {α σ : Type} (L : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (I : σ → Prop) (h0 : I init) (hf : ∀ a s, I s → I (f a s).value) : I (forIn L init f) := by
  induction L generalizing init with
  | nil => exact h0
  | cons x xs ih =>
    simp only [List.forIn_cons]
    have := hf x init h0
    generalize f x init = r at this
    cases r with
    | done b => exact this
    | yield b => exact ih b this

theorem forIn_range_inv {σ : Type} (r : Std.Legacy.Range) (init : σ) (f : Nat → σ → Id (ForInStep σ))
    (I : σ → Prop) (h0 : I init) (hf : ∀ a s, I s → I (f a s).value) : I (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_list_inv _ _ _ I h0 hf

variable {α : Type} [Inhabited α]

/-- All entries (including out-of-bounds reads) satisfy `P`. -/
def AllP (P : α → Prop) (a : Array α) : Prop := ∀ i : Nat, P a[i]!

theorem AllP.set! {P : α → Prop} {a : Array α} (h : AllP P a) {x : α} (hx : P x) (i : Nat) :
    AllP P (a.set! i x) := by
  unfold AllP
  intro j
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.setIfInBounds i x) j (by simpa using hj), Array.getElem_setIfInBounds]
    split
    · exact hx
    · have := h j; rwa [getElem!_pos a j hj] at this
  · rw [getElem!_neg (a.setIfInBounds i x) j (by simpa using hj)]
    have := h j; rwa [getElem!_neg a j hj] at this

theorem AllP.extract {P : α → Prop} {a : Array α} (h : AllP P a) (lo hi : Nat) : AllP P (a.extract lo hi) := by
  unfold AllP
  intro j
  by_cases hj : j < (a.extract lo hi).size
  · rw [getElem!_pos _ j hj, Array.getElem_extract]
    have := h (lo + j)
    rwa [getElem!_pos a (lo + j) (by simp at hj; omega)] at this
  · rw [getElem!_neg _ j hj]
    have := h a.size; rwa [getElem!_neg a a.size (by omega)] at this

theorem AllP.empty {P : α → Prop} (hd : P default) : AllP P (#[] : Array α) := by
  unfold AllP
  intro j; rw [getElem!_neg _ j (by simp)]; exact hd

theorem AllP.mem {P : α → Prop} {a : Array α} (h : AllP P a) {x : α} (hx : x ∈ a) : P x := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  have := h i; rwa [getElem!_pos a i hi] at this

theorem allP_of_mem {P : α → Prop} {a : Array α} (hd : P default) (h : ∀ x ∈ a, P x) : AllP P a := by
  intro j
  by_cases hj : j < a.size
  · rw [getElem!_pos a j hj]; exact h _ (Array.getElem_mem hj)
  · rw [getElem!_neg a j hj]; exact hd

theorem scatterLoop_allP {P : α → Prop} (rank : α → UInt64) (src : Array α) (soff : Nat) (dst : Array α)
    (doff n : Nat) (i : UInt64) (k : Nat) (count : Array Nat) (hs : AllP P src) (hd : AllP P dst) :
    AllP P (scatterLoop rank src soff dst doff n i k count).1 := by
  induction dst, k, count using scatterLoop.induct rank src soff doff n i with
  | case1 dst k count hk x m p count' ih =>
    rw [scatterLoop, if_pos hk]
    exact ih (hd.set! (hs _) _)
  | case2 dst k count hk =>
    rw [scatterLoop, if_neg hk]; exact hd

theorem copyLoop_allP {P : α → Prop} (src : Array α) (soff : Nat) (dst : Array α) (doff n k : Nat)
    (hs : AllP P src) (hd : AllP P dst) : AllP P (copyLoop src soff dst doff n k) := by
  induction dst, k using copyLoop.induct src soff doff n with
  | case1 dst k hk ih => rw [copyLoop, if_pos hk]; exact ih (hd.set! (hs _) _)
  | case2 dst k hk => rw [copyLoop, if_neg hk]; exact hd

theorem idbind {σ β : Type} (x : Id σ) (f : σ → Id β) : (x >>= f) = f x := rfl
theorem idpure {σ : Type} (x : σ) : (pure x : Id σ) = x := rfl

theorem bind_inv {σ β : Type} (x : Id σ) (f : σ → Id β) (I : σ → Prop) (Q : β → Prop) (hx : I x)
    (hf : ∀ y, I y → Q (f y)) : Q (x >>= f) := hf x hx

theorem radixSortCore_allP {P : α → Prop} (hd : P default) (bits : Nat) (rank : α → UInt64) (a : Array α)
    (lo hi : Nat) (ha : AllP P a) : AllP P (radixSortCore bits rank a lo hi) := by
  unfold radixSortCore
  simp only [Id.run]
  split
  · exact ha
  · refine bind_inv _ _ (fun st => AllP P st.1 ∧ AllP P st.2.1) _ ?_ ?_
    · refine forIn_range_inv (I := fun (st : Array α × Array α × _) => AllP P st.1 ∧ AllP P st.2.1) _ _ _ ?_ ?_
      · exact ⟨ha, AllP.empty hd⟩
      intro pass st hst
      simp only [idbind, idpure]
      repeat' split
      all_goals simp only [ForInStep.value]
      all_goals refine ⟨?_, ?_⟩
      all_goals first
        | exact hst.1 | exact hst.2
        | exact AllP.extract hst.1 _ _
        | (apply scatterLoop_allP <;> first | exact hst.1 | exact hst.2 | exact AllP.extract hst.1 _ _)
    · intro y hy
      simp only [idbind, idpure]
      split
      · exact copyLoop_allP _ _ _ _ _ _ hy.2 hy.1
      · exact hy.1

theorem radixSortArray64_allP {P : α → Prop} (hd : P default) (rank : α → UInt64) (a : Array α)
    (h : ∀ x ∈ a, P x) : AllP P (radixSortArray64 rank a) :=
  radixSortCore_allP hd 64 rank a 0 a.size (allP_of_mem hd h)

end Radix
end LeanKissat
