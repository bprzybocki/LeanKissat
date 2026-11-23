import LeanKissat.Proofs.Backtrack

/-!
# Derived false literals (soundness of learned clauses)

`DerFalse s K y`: the false literal `y` is derivable from the clause `K` by reasons:
it is in `K`, root-level false, or the negation of a literal whose reason clause has all
its other literals derivable. If every literal of an implied clause is derivable from
`K`, then `K` is implied.
-/

namespace LeanKissat
namespace Solver

/-- The antecedent literals of the true literal `t` (its reason clause without `t`), if
  `t` has a reason. -/
def Antecedents (s : Solver) (t : Lit) (A : List Lit) : Prop :=
  s.IsTrue t ∧ 0 < s.lvl t ∧
  ((s.binOf t = true ∧ s.BinWatched t (s.reasonOf t) ∧ A = [s.reasonOf t]) ∨
   (s.binOf t = false ∧ s.reasonOf t ≠ DECISION_REASON ∧ s.LiveRef (s.reasonOf t) ∧
     t ∈ s.clauseL (s.reasonOf t) ∧ ∀ x, x ∈ A ↔ x ∈ s.clauseL (s.reasonOf t) ∧ x ≠ t))

inductive DerFalse (s : Solver) (K : List Lit) : Lit → Prop where
  | inK {y : Lit} : y ∈ K → DerFalse s K y
  | root {y : Lit} : s.IsFalse y → s.lvl y = 0 → DerFalse s K y
  | reason {y : Lit} {A : List Lit} : s.Antecedents (NOT y) A → (∀ x ∈ A, DerFalse s K x) →
      DerFalse s K y

/-- The reason clause of a literal with antecedents is implied (and contains it). -/
theorem Antecedents.implied {Φ : (Nat → Bool) → Prop} {s : Solver} (hdb : DBImplied Φ s)
    {t : Lit} {A : List Lit} (h : s.Antecedents t A) : Implied Φ (t :: A) := by
  obtain ⟨_, _, ⟨_, hb, rfl⟩ | ⟨_, _, hl, ht, hA⟩⟩ := h
  · exact hdb _ ((inDB_iff _ _).mpr (Or.inr ⟨_, _, hb, rfl⟩))
  · exact (hdb _ ((inDB_iff _ _).mpr (Or.inl ⟨_, hl, rfl⟩))).perm (fun x hx => by
      by_cases e : x = t
      · subst e; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ ((hA x).mpr ⟨hx, e⟩))

/-- Semantics: an assignment satisfying `Φ` and falsifying `K` falsifies every derived
  literal. -/
theorem DerFalse.sem {Φ : (Nat → Bool) → Prop} {s : Solver} (hdb : DBImplied Φ s)
    (hroot : RootImplied Φ s) (hvc : ValCons s) (hlv : LvlVar s) {K : List Lit}
    {β : Nat → Bool} (hβ : Φ β) (hK : ∀ z ∈ K, litVal β z = false) :
    ∀ {y : Lit}, DerFalse s K y → litVal β y = false := by
  intro y h
  induction h with
  | inK hy => exact hK _ hy
  | root hf h0 =>
    rename_i y
    have ht : s.IsTrue (NOT y) := by
      have := (hvc (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf
    obtain ⟨z, hz, hv⟩ := hroot (NOT y) ht (by rw [hlv]; exact h0) β hβ
    simp at hz; subst hz
    rw [litVal_NOT] at hv; simpa using hv
  | reason hA _ ih =>
    rename_i y A
    obtain ⟨z, hz, hv⟩ := hA.implied hdb β hβ
    rcases List.mem_cons.mp hz with rfl | hz
    · rw [litVal_NOT] at hv; simpa using hv
    · rw [ih z hz] at hv; simp at hv

/-- If every literal of an implied clause is derivable from `K`, `K` is implied. -/
theorem implied_of_derFalse {Φ : (Nat → Bool) → Prop} {s : Solver} (hdb : DBImplied Φ s)
    (hroot : RootImplied Φ s) (hvc : ValCons s) (hlv : LvlVar s) {K κ : List Lit}
    (hκ : Implied Φ κ) (hd : ∀ y ∈ κ, DerFalse s K y) : Implied Φ K := by
  intro β hβ
  apply Classical.byContradiction
  intro hn
  have hK : ∀ z ∈ K, litVal β z = false := by
    intro z hz
    cases h : litVal β z
    · rfl
    · exact absurd ⟨z, hz, h⟩ hn
  obtain ⟨y, hy, hv⟩ := hκ β hβ
  rw [DerFalse.sem hdb hroot hvc hlv hβ hK (hd y hy)] at hv
  simp at hv

/-- Derivability is transitive: if every literal of `K` is derivable from `K'`, so is
  every literal derivable from `K`. -/
theorem DerFalse.trans {s : Solver} {K K' : List Lit} (hK : ∀ y ∈ K, DerFalse s K' y) :
    ∀ {y : Lit}, DerFalse s K y → DerFalse s K' y := by
  intro y h
  induction h with
  | inK hy => exact hK _ hy
  | root hf h0 => exact .root hf h0
  | reason hA _ ih => exact .reason hA ih

end Solver
end LeanKissat
