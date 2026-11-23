import LeanKissat.Proofs.BacktrackConflict
import LeanKissat.Proofs.Allocate

/-!
# Learning the analyzed clause
-/

namespace LeanKissat
namespace Solver

/-- Updates of fields that no invariant mentions (marks, statistics, …). -/
structure Quiet (t s : Solver) : Prop where
  same : Same t s
  ana : anaSide t = anaSide s

theorem Quiet.refl (s : Solver) : Quiet s s := ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
theorem Quiet.trans {a b c : Solver} (h1 : Quiet a b) (h2 : Quiet b c) : Quiet a c :=
  ⟨⟨h1.same.asg.trans h2.same.asg, h1.same.arena.trans h2.same.arena, h1.same.watches.trans h2.same.watches,
    h1.same.delayed.trans h2.same.delayed, h1.same.vars.trans h2.same.vars, h1.same.level.trans h2.same.level,
    h1.same.frameTrail.trans h2.same.frameTrail, h1.same.propagate.trans h2.same.propagate,
    h1.same.options.trans h2.same.options⟩, h1.ana.trans h2.ana⟩

theorem Quiet.clause {t s : Solver} (h : Quiet t s) : t.clause = s.clause := by
  have := h.ana; simp only [anaSide, Prod.mk.injEq] at this; exact this.1

theorem markClauseLits_spec (n : Nat) :
    ∀ (s : Solver) (i : Nat), (∀ j, j < i → s.marks.get! (s.clause.get! j).toNat ≠ 0) →
    Quiet (s.markClauseLits i n).2 s ∧
    ((s.markClauseLits i n).1 = true → ∀ j2, i ≤ j2 → j2 < n → ∀ j1, j1 < j2 →
      s.clause.get! j1 ≠ s.clause.get! j2) := by
  intro s i
  fun_induction markClauseLits s i n with
  | case1 s i hi lit hm =>
    intro _
    exact ⟨Quiet.refl _, fun h => absurd h (by simp)⟩
  | case2 s i hi lit hm ih =>
    intro hpre
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hm
    obtain ⟨hsz, hm0⟩ := hm
    have hq : Quiet ({ s with marks := s.marks.set! lit.toNat 1 } : Solver) s :=
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    obtain ⟨a1, a2⟩ := ih (fun j hj => by
      show (s.marks.set! lit.toNat 1).get! (s.clause.get! j).toNat ≠ 0
      rw [ByteArray.get!_set!]
      split
      · simp
      · by_cases e : j = i
        · subst e; rename_i h; exact absurd ⟨rfl, by omega⟩ h
        · exact hpre j (by omega))
    refine ⟨a1.trans hq, fun hok j2 hj2 hj2n j1 hj1 => ?_⟩
    by_cases e : j2 = i
    · subst e
      intro heq
      have := hpre j1 hj1
      rw [heq] at this
      exact this hm0
    · exact a2 hok j2 (by omega) hj2n j1 hj1
  | case3 s i hi =>
    intro _
    exact ⟨Quiet.refl _, fun _ j2 hj2 hj2n => absurd hj2n (by omega)⟩

theorem unmarkClauseLits_quiet (n : Nat) : ∀ (s : Solver) (i : Nat), Quiet (s.unmarkClauseLits i n) s := by
  intro s i
  fun_induction unmarkClauseLits s i n with
  | case1 s i hi ih => exact ih.trans ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  | case2 => exact Quiet.refl _

theorem clauseFalseFrom_spec (s : Solver) (n : Nat) :
    ∀ i, s.clauseFalseFrom i n = true → ∀ j, i ≤ j → j < n → s.IsFalse (s.clause.get! j) := by
  intro i
  fun_induction clauseFalseFrom s i n with
  | case1 i hi ih =>
    intro h j hj1 hj2
    simp only [Bool.and_eq_true] at h
    by_cases e : j = i
    · subst e
      have := h.1
      unfold vFalse value at this
      exact beq_iff_eq.mp this
    · exact ih h.2 j (by omega) hj2
  | case2 i hi => intro _ j hj1 hj2; omega

/-- The checked assertion on the learned clause. -/
theorem learnedClauseOK_spec (s : Solver) :
    Quiet s.learnedClauseOK.2 s ∧
    (s.learnedClauseOK.1 = true → 0 < s.clause.size ∧ s.asg.values.get! (s.clause.get! 0).toNat = 0 ∧
      (∀ j, 1 ≤ j → j < s.clause.size → s.IsFalse (s.clause.get! j)) ∧ s.clause.view.Nodup) := by
  unfold learnedClauseOK
  simp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨h0, h1⟩, h2⟩ := hc
    obtain ⟨m1, m2⟩ := markClauseLits_spec s.clause.size s 0 (fun j hj => absurd hj (by omega))
    generalize s.markClauseLits 0 s.clause.size = R at m1 m2 ⊢
    obtain ⟨ok, t⟩ := R
    simp only at m1 m2 ⊢
    have u := unmarkClauseLits_quiet s.clause.size t 0
    refine ⟨u.trans m1, fun hok => ⟨h0, h1, clauseFalseFrom_spec s _ 1 h2, ?_⟩⟩
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    simp only [U32Vec.length_view] at hi hj
    apply m2 hok j (Nat.zero_le _) hj i hij
    rw [U32Vec.get!_eq_view, U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using hi), List.getElem?_eq_getElem (by simpa using hj)]
    simp [heq]
  · exact ⟨Quiet.refl _, fun h => absurd h (by simp)⟩

end Solver
end LeanKissat
