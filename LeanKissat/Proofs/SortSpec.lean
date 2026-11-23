import LeanKissat.Proofs.Shrink
namespace LeanKissat
namespace Solver

theorem sortWrite_spec (s : Solver) (n : Nat) (hn : n ≤ s.clause.size) :
    ∀ (starts shadow : U32Vec) (written : Array Nat) (i : Nat),
    (∀ j, j < shadow.size → shadow.get! j = INVALID_LIT ∨ shadow.get! j ∈ s.clause.view) →
    (s.sortWrite starts shadow written i n).2.1.size = shadow.size ∧
    ∀ j, j < shadow.size → (s.sortWrite starts shadow written i n).2.1.get! j = INVALID_LIT ∨
      (s.sortWrite starts shadow written i n).2.1.get! j ∈ s.clause.view := by
  intro starts shadow written i
  fun_induction sortWrite s starts shadow written i n with
  | case1 starts shadow written i hi lit level p ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (fun j hj => by
      rw [U32Vec.get!_set!]
      split
      · right; exact get!_mem_view _ _ (by omega)
      · exact h j (by simpa using hj))
    simp only [U32Vec.size_set!] at h1 h2
    exact ⟨h1, h2⟩
  | case2 => intro h; exact ⟨rfl, h⟩

theorem sortShadow_spec (s : Solver) :
    s.sortShadow.1.size = s.clause.size ∧
    ∀ j, j < s.clause.size → s.sortShadow.1.get! j = INVALID_LIT ∨ s.sortShadow.1.get! j ∈ s.clause.view := by
  unfold sortShadow
  simp only
  have hsz : ((U32Vec.replicate s.clause.size INVALID_LIT).set! 0 (s.clause.get! 0)).size = s.clause.size := by
    simp [U32Vec.size_replicate]
  have := sortWrite_spec s _ (Nat.le_refl _) (sortStarts (s.levels.toArray.qsort (· < ·)) s.frameUsed).1
    ((U32Vec.replicate s.clause.size INVALID_LIT).set! 0 (s.clause.get! 0)) (Array.emptyWithCapacity s.clause.size) 1
    (fun j hj => by
      rw [U32Vec.get!_set!]
      split
      · right; rename_i h; exact get!_mem_view _ _ (by rw [U32Vec.size_replicate] at h; omega)
      · left
        rw [U32Vec.get!_eq_view, U32Vec.view_replicate, List.getD_eq_getElem?_getD,
          List.getElem?_replicate]
        rw [hsz] at hj; simp [hj])
  rw [hsz] at this
  exact this

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem allValid_spec (c : U32Vec) : ∀ i, allValid c i = true → ∀ k, i ≤ k → k < c.size → c.get! k ≠ INVALID_LIT := by
  intro i
  fun_induction allValid c i with
  | case1 i hi ih =>
    intro h k hk1 hk2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    by_cases e : k = i
    · subst e; exact h.1
    · exact ih h.2 k (by omega) hk2
  | case2 i hi => intro _ k hk1 hk2; omega

theorem sortedOK_spec (c shadow : U32Vec) (written : Array Nat) :
    ∀ i, sortedOK c shadow written i = true → ∀ k, i ≤ k → k < c.size →
      written[k - 1]! < shadow.size ∧ shadow.get! written[k - 1]! = c.get! k := by
  intro i
  fun_induction sortedOK c shadow written i with
  | case1 i hi ih =>
    intro h k hk1 hk2
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    by_cases e : k = i
    · subst e; exact ⟨h.1.1, h.1.2⟩
    · exact ih h.2 k (by omega) hk2
  | case2 i hi => intro _ k hk1 hk2; omega

theorem sortDeducedClause_spec (s : Solver) :
    s.sortDeducedClause.overflowed = true ∨
    ∃ sh st, s.sortDeducedClause = { s with clause := sh, frameUsed := st } ∧
      (∀ y ∈ sh.view, y ∈ s.clause.view) ∧ (∀ y ∈ s.clause.view, y ∈ sh.view) := by
  obtain ⟨hsz, hsh⟩ := sortShadow_spec s
  unfold sortDeducedClause
  generalize s.sortShadow = R at hsz hsh ⊢
  obtain ⟨sh, st, w⟩ := R
  simp only at hsz hsh ⊢
  unfold sortFinish
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hc
    have hv := allValid_spec sh 0 h3
    have hs := sortedOK_spec s.clause sh w 1 h2
    right
    refine ⟨sh, st, rfl, fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨q, hq, hqy⟩ := mem_view_pos _ _ hy
      rcases hsh q (by omega) with h' | h'
      · exact absurd h' (hv q (Nat.zero_le _) hq)
      · rw [← hqy]; exact h'
    · obtain ⟨q, hq, hqy⟩ := mem_view_pos _ _ hy
      rw [← hqy]
      by_cases e : q = 0
      · subst e; rw [← h1]; exact get!_mem_view _ _ h0
      · obtain ⟨a, b⟩ := hs q (by omega) hq
        rw [← b]; exact get!_mem_view _ _ a
  · left; rfl

end Solver
end LeanKissat
