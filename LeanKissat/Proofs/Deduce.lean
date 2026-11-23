import LeanKissat.Proofs.AnaBits

/-!
# First-UIP deduction
-/

namespace LeanKissat
namespace Solver
open Arena

/-- The other analysis bits (not `analyzed`). -/
def otherMask : UInt8 := ABits.poisoned ||| ABits.removable ||| ABits.shrinkable

theorem pushAnalyzed_af (s : Solver) (idx : UInt32) : AF (s.pushAnalyzed idx) s :=
  AF.trans_left (setABit_af s idx _ true analyzed_bin) af_rfl

theorem pushAnalyzed_abit (s : Solver) (idx i : UInt32) (hsz : idx.toNat < s.asg.aBits.size)
    (c : UInt8) (hc : c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable) :
    (s.pushAnalyzed idx).abit i c = if idx = i ∧ c = ABits.analyzed then true else s.abit i c := by
  show (s.setABit idx ABits.analyzed true).abit i c = _
  rw [abit_setABit s idx i _ c true hsz]
  · by_cases e : c = ABits.analyzed
    · subst e; simp
    · simp only [e, and_false, ite_false]
      have : ABits.analyzed ≠ c := fun h => e h.symm
      simp [this]
  · rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩

theorem levelIdx_eq_zero (s : Solver) (lit : Lit) :
    (s.levelIdx (IDX lit) == 0) = true ↔ s.lvl lit = 0 := by
  simp only [levelIdx, Solver.lvl, beq_iff_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact UInt32.toNat_inj.mp (by rw [h]; rfl)

theorem levelIdx_eq_level (s : Solver) (lit : Lit) :
    (s.levelIdx (IDX lit) == s.level) = true ↔ s.lvl lit = s.level.toNat := by
  simp only [levelIdx, Solver.lvl, beq_iff_eq]
  exact ⟨fun h => by rw [h], fun h => UInt32.toNat_inj.mp h⟩

/-- Specification of `analyzeLiteral`. -/
theorem analyzeLiteral_spec (s : Solver) (lit : Lit) (hsz : (IDX lit).toNat < s.asg.aBits.size) :
    AF (s.analyzeLiteral lit).2 s ∧
    ((s.analyzeLiteral lit).1 = true ↔
      (s.lvl lit ≠ 0 ∧ s.isAnalyzed (IDX lit) = false ∧ s.lvl lit = s.level.toNat)) ∧
    (s.analyzeLiteral lit).2.clause = (if s.lvl lit ≠ 0 ∧ s.isAnalyzed (IDX lit) = false ∧
      s.lvl lit ≠ s.level.toNat then s.clause.push lit else s.clause) ∧
    (∀ i, (s.analyzeLiteral lit).2.isAnalyzed i = true ↔
      (s.isAnalyzed i = true ∨ (i = IDX lit ∧ s.lvl lit ≠ 0))) ∧
    (∀ i c, (c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable) →
      (s.analyzeLiteral lit).2.abit i c = s.abit i c) := by
  unfold analyzeLiteral
  simp only
  by_cases h0 : (s.levelIdx (IDX lit) == 0) = true
  · have h0' := (levelIdx_eq_zero s lit).mp h0
    rw [if_pos h0]
    refine ⟨AF.refl _, by simp [h0'], by simp [h0'], fun i => by simp [h0'], fun _ _ _ => rfl⟩
  rw [if_neg h0]
  have h0' : s.lvl lit ≠ 0 := fun h => h0 ((levelIdx_eq_zero s lit).mpr h)
  generalize hs1 : ({ s with antecedentSize := s.antecedentSize + 1 } : Solver) = s1
  have f1 : AF s1 s := by rw [← hs1]; exact af_rfl
  have c1 : s1.clause = s.clause := by rw [← hs1]
  have a1 : ∀ i c, s1.abit i c = s.abit i c := by intro i c; rw [← hs1]; rfl
  have l1 : s1.level = s.level := by rw [← hs1]
  have z1 : s1.asg.aBits.size = s.asg.aBits.size := by rw [← hs1]
  by_cases ha : s1.isAnalyzed (IDX lit) = true
  · rw [if_pos ha]
    have ha' : s.isAnalyzed (IDX lit) = true := by rw [← ha]; unfold isAnalyzed; rw [a1]
    refine ⟨f1, by simp [ha'], by rw [c1]; simp [ha'], fun i => ?_, fun i c _ => a1 i c⟩
    unfold isAnalyzed; rw [a1]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨rfl, _⟩)
      · exact h
      · exact ha'
  rw [if_neg ha]
  have ha' : s.isAnalyzed (IDX lit) = false := by
    have : s1.isAnalyzed (IDX lit) = false := Bool.eq_false_iff.mpr ha
    rw [← this]; unfold isAnalyzed; rw [a1]
  generalize hs2 : s1.pushAnalyzed (IDX lit) = s2
  have f2 : AF s2 s := by rw [← hs2]; exact AF.trans_left f1 (pushAnalyzed_af _ _)
  have c2 : s2.clause = s.clause := by rw [← hs2, ← c1]; rfl
  have l2 : s2.level = s.level := by rw [← hs2, ← l1]; rfl
  have hab : ∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable) →
      s2.abit i c = if IDX lit = i ∧ c = ABits.analyzed then true else s.abit i c := by
    intro i c hc; rw [← hs2, pushAnalyzed_abit s1 (IDX lit) i (by rw [z1]; exact hsz) c hc, a1]
  have hanal : ∀ i, s2.isAnalyzed i = true ↔ (s.isAnalyzed i = true ∨ (i = IDX lit ∧ s.lvl lit ≠ 0)) := by
    intro i
    unfold isAnalyzed; rw [hab i _ (Or.inl rfl)]
    by_cases e : IDX lit = i
    · subst e; simp [h0']
    · simp only [e, false_and, ite_false]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨rfl, _⟩)
        · exact h
        · exact absurd rfl e
  have hother : ∀ i c, (c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable) →
      s2.abit i c = s.abit i c := by
    intro i c hc
    rw [hab i c (Or.inr hc)]
    have : c ≠ ABits.analyzed := by rcases hc with rfl | rfl | rfl <;> decide
    simp [this]
  generalize hs3 : ({ s2 with resolventSize := s2.resolventSize + 1 } : Solver) = s3
  have f3 : AF s3 s := by rw [← hs3]; exact AF.trans_left f2 af_rfl
  have c3 : s3.clause = s.clause := by rw [← hs3, ← c2]
  have l3 : s3.level = s.level := by rw [← hs3, ← l2]
  have an3 : ∀ i, s3.isAnalyzed i = s2.isAnalyzed i := by intro i; rw [← hs3]; rfl
  have ab3 : ∀ i c, s3.abit i c = s2.abit i c := by intro i c; rw [← hs3]; rfl
  by_cases hl : (s.levelIdx (IDX lit) == s2.level) = true
  · rw [if_pos hl]
    have hl' : s.lvl lit = s.level.toNat := (levelIdx_eq_level s lit).mp (by rw [← l2]; exact hl)
    have hL0 : s.level.toNat ≠ 0 := hl' ▸ h0'
    exact ⟨f3, by simp [h0', ha', hl', hL0], by rw [c3]; simp [hl'], fun i => by rw [an3]; exact hanal i,
      fun i c hc => by rw [ab3]; exact hother i c hc⟩
  · rw [if_neg hl]
    have hl' : s.lvl lit ≠ s.level.toNat := fun h => hl (by rw [l2]; exact (levelIdx_eq_level s lit).mpr h)
    split
    · exact ⟨AF.trans_left f2 af_rfl, by simp [hl'], by simp [h0', ha', hl']; rw [c2], hanal, hother⟩
    · exact ⟨AF.trans_left f2 af_rfl, by simp [hl'], by simp [h0', ha', hl']; rw [c2], hanal, hother⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena
open Std.Do
set_option linter.deprecated.syntax false

/-- The fields fixed by pure bookkeeping updates. -/
def frameOf (s : Solver) := (s.asg, s.arena, s.watches, s.delayed, s.vars, s.level, s.frameTrail,
  s.propagate, s.options, s.importLit, s.inconsistent, s.conflictLit0, s.conflictLit1, s.clause,
  s.watching, s.probing, s.importBits)

theorem AF.of_frame {t s : Solver} (h : frameOf t = frameOf s) : AF t s := by
  simp only [frameOf, Prod.mk.injEq] at h
  obtain ⟨ha, har, hw, hd, hv, hl, hf, hp, ho, hi, hc, h0, h1, _, hwa, hpr, hib⟩ := h
  exact ⟨by rw [ha], by rw [ha], by rw [ha], by rw [ha], by rw [ha], fun _ => by rw [ha], by rw [ha],
    by rw [har]; exact Arena.Same.refl _, hw, hd, hv, hl, hf, hp, ho, hi, hc, h0, h1, hwa, hpr, hib⟩

theorem recomputeGlue_frame (s : Solver) (ref : Ref) (limit : UInt32) :
    frameOf (s.recomputeGlue ref limit).2 = frameOf s := by
  generalize h : s.recomputeGlue ref limit = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨_, st⟩ => ⌜frameOf st.1 = frameOf s⌝
  · ⇓⟨_, st⟩ => ⌜frameOf st = frameOf s⌝
  all_goals simp_all [frameOf, setFramePromote]

section RG
variable (s : Solver) (ref : Ref) (limit : UInt32)
theorem recomputeGlue_asg : (s.recomputeGlue ref limit).2.asg = s.asg := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.1
theorem recomputeGlue_arena : (s.recomputeGlue ref limit).2.arena = s.arena := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.1
theorem recomputeGlue_watches : (s.recomputeGlue ref limit).2.watches = s.watches := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.1
theorem recomputeGlue_delayed : (s.recomputeGlue ref limit).2.delayed = s.delayed := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.1
theorem recomputeGlue_vars : (s.recomputeGlue ref limit).2.vars = s.vars := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.1
theorem recomputeGlue_level : (s.recomputeGlue ref limit).2.level = s.level := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.1
theorem recomputeGlue_frameTrail : (s.recomputeGlue ref limit).2.frameTrail = s.frameTrail := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.1
theorem recomputeGlue_propagate : (s.recomputeGlue ref limit).2.propagate = s.propagate := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.1
theorem recomputeGlue_options : (s.recomputeGlue ref limit).2.options = s.options := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_importLit : (s.recomputeGlue ref limit).2.importLit = s.importLit := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_inconsistent : (s.recomputeGlue ref limit).2.inconsistent = s.inconsistent := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_conflictLit0 : (s.recomputeGlue ref limit).2.conflictLit0 = s.conflictLit0 := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_conflictLit1 : (s.recomputeGlue ref limit).2.conflictLit1 = s.conflictLit1 := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_clause : (s.recomputeGlue ref limit).2.clause = s.clause := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_watching : (s.recomputeGlue ref limit).2.watching = s.watching := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_probing : (s.recomputeGlue ref limit).2.probing = s.probing := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem recomputeGlue_importBits : (s.recomputeGlue ref limit).2.importBits = s.importBits := by
  have := recomputeGlue_frame s ref limit; simp only [frameOf, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
end RG

theorem markClauseAsUsed_asg (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).asg = s.asg := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_asg]
theorem markClauseAsUsed_watching (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).watching = s.watching := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_watching]
theorem markClauseAsUsed_probing (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).probing = s.probing := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_probing]
theorem markClauseAsUsed_importBits (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).importBits = s.importBits := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_importBits]
theorem markClauseAsUsed_watches (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).watches = s.watches := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_watches]
theorem markClauseAsUsed_delayed (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).delayed = s.delayed := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_delayed]
theorem markClauseAsUsed_vars (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).vars = s.vars := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_vars]
theorem markClauseAsUsed_level (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).level = s.level := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_level]
theorem markClauseAsUsed_frameTrail (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).frameTrail = s.frameTrail := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_frameTrail]
theorem markClauseAsUsed_propagate (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).propagate = s.propagate := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_propagate]
theorem markClauseAsUsed_options (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).options = s.options := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_options]
theorem markClauseAsUsed_importLit (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).importLit = s.importLit := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_importLit]
theorem markClauseAsUsed_inconsistent (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).inconsistent = s.inconsistent := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_inconsistent]
theorem markClauseAsUsed_conflictLit0 (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).conflictLit0 = s.conflictLit0 := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_conflictLit0]
theorem markClauseAsUsed_conflictLit1 (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).conflictLit1 = s.conflictLit1 := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_conflictLit1]
theorem markClauseAsUsed_clause (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).clause = s.clause := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_clause]

theorem recomputeGlue_analyzed (s : Solver) (ref : Ref) (limit : UInt32) :
    (s.recomputeGlue ref limit).2.analyzed = s.analyzed := by
  generalize h : s.recomputeGlue ref limit = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨_, st⟩ => ⌜st.1.analyzed = s.analyzed⌝
  · ⇓⟨_, st⟩ => ⌜st.analyzed = s.analyzed⌝
  all_goals simp_all [setFramePromote]

theorem markClauseAsUsed_analyzed (s : Solver) (ref : Ref) : (s.markClauseAsUsed ref).analyzed = s.analyzed := by
  unfold markClauseAsUsed recomputeAndPromote promoteClause
  split
  · rfl
  · dsimp only
    split <;> (try split) <;> (try split) <;> simp [recomputeGlue_analyzed]

/-- `markClauseAsUsed` changes the arena only in header bits of `ref`. -/
theorem markClauseAsUsed_cases (s : Solver) (ref : Ref) :
    (s.markClauseAsUsed ref).arena = s.arena ∨
    (s.markClauseAsUsed ref).arena = s.arena.setUsed ref MAX_USED ∨
    ∃ g, (s.markClauseAsUsed ref).arena = (s.arena.setUsed ref MAX_USED).setGlue ref g := by
  unfold markClauseAsUsed
  split
  · exact Or.inl rfl
  · simp only [recomputeAndPromote, promoteClause]
    split
    · split
      · split <;> exact Or.inr (Or.inl (recomputeGlue_arena _ _ _))
      · split <;> exact Or.inr (Or.inr ⟨_, by rw [recomputeGlue_arena]⟩)
    · split <;> exact Or.inr (Or.inl (recomputeGlue_arena _ _ _))

theorem markClauseAsUsed_af (s : Solver) (ref : Ref) (hl : s.arena.Layout)
    (hr : ref ∈ s.arena.chain 0 s.arena.sizeWards) : AF (s.markClauseAsUsed ref) s := by
  have e1 := markClauseAsUsed_asg s ref
  have hsame : Arena.Same s.arena (s.markClauseAsUsed ref).arena := by
    rcases markClauseAsUsed_cases s ref with h | h | ⟨g, h⟩ <;> rw [h]
    · exact Arena.Same.refl _
    · exact setUsed_same hl hr _
    · have h1 := setUsed_same hl hr MAX_USED
      exact h1.trans (setGlue_same (h1.layout hl) (by rw [h1.chain]; exact hr) g)
  exact ⟨by rw [e1], by rw [e1], by rw [e1], by rw [e1], by rw [e1], fun _ => by rw [e1], by rw [e1],
    hsame, markClauseAsUsed_watches s ref, markClauseAsUsed_delayed s ref, markClauseAsUsed_vars s ref,
    markClauseAsUsed_level s ref, markClauseAsUsed_frameTrail s ref, markClauseAsUsed_propagate s ref,
    markClauseAsUsed_options s ref, markClauseAsUsed_importLit s ref, markClauseAsUsed_inconsistent s ref,
    markClauseAsUsed_conflictLit0 s ref, markClauseAsUsed_conflictLit1 s ref, markClauseAsUsed_watching s ref,
    markClauseAsUsed_probing s ref, markClauseAsUsed_importBits s ref⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem countP_succ_of_unique {α : Type} (p q : α → Bool) :
    ∀ (L : List α) (e : α), e ∈ L → L.Nodup → q e = true → p e = false →
    (∀ x ∈ L, x ≠ e → q x = p x) → L.countP q = L.countP p + 1 := by
  intro L
  induction L with
  | nil => intro e he; simp at he
  | cons y ys ih =>
    intro e he hnd hq hp hag
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | he'
    · have : ys.countP q = ys.countP p := List.countP_congr (fun x hx => by
        rw [hag x (List.mem_cons_of_mem _ hx) (fun h => hnd.1 (h ▸ hx))])
      simp [List.countP_cons, hq, hp, this]
    · have h1 := ih e he' hnd.2 hq hp (fun x hx hne => hag x (List.mem_cons_of_mem _ hx) hne)
      have hne : y ≠ e := fun h => hnd.1 (h ▸ he')
      have h2 := hag y (List.mem_cons_self ..) hne
      simp only [List.countP_cons, h1, h2]; omega

theorem countP_eq_of_agree {α : Type} (p q : α → Bool) (L : List α) (h : ∀ x ∈ L, q x = p x) :
    L.countP q = L.countP p := List.countP_congr (fun x hx => by rw [h x hx])

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem analyzeLiteral_list (s : Solver) (lit : Lit) :
    ∀ i, i ∈ s.analyzed.view → i ∈ (s.analyzeLiteral lit).2.analyzed.view := by
  intro i hi
  unfold analyzeLiteral
  simp only
  split
  · exact hi
  split
  · exact hi
  have : i ∈ (s.analyzed.push (IDX lit)).view := by rw [U32Vec.view_push]; exact List.mem_append_left _ hi
  split
  · exact this
  split <;> exact this

theorem analyzeLiteral_list_new (s : Solver) (lit : Lit) :
    s.lvl lit ≠ 0 → IDX lit ∈ (s.analyzeLiteral lit).2.analyzed.view ∨ s.isAnalyzed (IDX lit) = true := by
  intro h0
  unfold analyzeLiteral
  simp only
  have h0' : ¬ (s.levelIdx (IDX lit) == 0) = true := fun h => h0 ((levelIdx_eq_zero s lit).mp h)
  rw [if_neg h0']
  split
  · rename_i h; exact Or.inr h
  have : IDX lit ∈ (s.analyzed.push (IDX lit)).view := by rw [U32Vec.view_push]; simp
  left
  split
  · exact this
  split <;> exact this

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Analyzed literals on the conflict level (`L`), as a predicate on trail literals. -/
def anaP (s0 s : Solver) (L : Nat) (l : Lit) : Bool := s.isAnalyzed (IDX l) && (s0.lvl l == L)

/-- Number of analyzed conflict-level literals before trail position `t`. -/
def pendCount (s0 s : Solver) (L t : Nat) : Nat := (s0.trailL.take t).countP (anaP s0 s L)

/-- The true literal `l` is resolved: its antecedents are analyzed or root-level. -/
def Resolved (s0 s : Solver) (l : Lit) : Prop :=
  ∃ A, s0.Antecedents l A ∧ ∀ x ∈ A, s0.lvl x = 0 ∨ s.isAnalyzed (IDX x) = true

/-- The deduction invariant (relative to the state `s0` at the start of analysis, conflict
  level `L`, trail pointer `t`, `unres` unresolved conflict-level literals). -/
structure DInv (s0 : Solver) (L : Nat) (s : Solver) (t unres : Nat) : Prop where
  af : AF s s0
  csize : 1 ≤ s.clause.size
  tail : ∀ y ∈ s.clause.view.drop 1, s0.IsFalse y ∧ 0 < s0.lvl y ∧ s0.lvl y < L ∧
    s.isAnalyzed (IDX y) = true
  ana : ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isAnalyzed (IDX y) = true →
    (s0.lvl y < L → y ∈ s.clause.view.drop 1) ∧
    (s0.lvl y = L → (∃ p < t, s0.trailL[p]? = some (NOT y)) ∨ Resolved s0 s (NOT y))
  anaAssigned : ∀ i, s.isAnalyzed i = true → ∃ y, IDX y = i ∧ s0.IsFalse y ∧ 0 < s0.lvl y
  count : unres = pendCount s0 s L t
  tle : t ≤ s0.trailL.length
  others : ∀ i c, (c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable) → s.abit i c = false
  list : ∀ i, s.isAnalyzed i = true → i ∈ s.analyzed.view

/-- The base facts about `s0`. -/
structure DBase (Φ : (Nat → Bool) → Prop) (s0 : Solver) (L : Nat) : Prop where
  inv : SInv Φ s0
  level : s0.level.toNat = L
  pos : 0 < L

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ (L : List α), (L.map f).Nodup → L.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun hx => h.1 (List.mem_map_of_mem hx), nodup_of_map f xs h.2⟩

theorem inj_of_nodup_map {α β : Type} (f : α → β) : ∀ (L : List α), (L.map f).Nodup →
    ∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b
  | [], _ => by intro a ha; simp at ha
  | x :: xs, h => by
    rw [List.map_cons, List.nodup_cons] at h
    intro a ha b hb e
    rcases List.mem_cons.mp ha with ea | ha' <;> rcases List.mem_cons.mp hb with eb | hb'
    · rw [ea, eb]
    · subst ea; exact absurd (e ▸ List.mem_map_of_mem hb') h.1
    · subst eb; exact absurd (e.symm ▸ List.mem_map_of_mem ha') h.1
    · exact inj_of_nodup_map f xs h.2 a ha' b hb' e

theorem DBase.trail_nodup {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) :
    s0.trailL.Nodup := nodup_of_map _ _ hb.inv.rsizes.2.2.2.2

theorem DBase.true_on_trail {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {y : Lit} (hf : s0.IsFalse y) (hl : 0 < s0.lvl y) : NOT y ∈ s0.trailL := by
  have ht : s0.IsTrue (NOT y) := by
    have := (hb.inv.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf
  rcases hb.inv.core.trueOnTrail _ ht with h | h
  · exact h
  · rw [hb.inv.core.lvlVar] at h; omega

theorem DBase.idx_unique {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {a b : Lit} (ha : a ∈ s0.trailL) (hb' : b ∈ s0.trailL) (e : IDX a = IDX b) : a = b := by
  have hnd := hb.inv.rsizes.2.2.2.2
  exact inj_of_nodup_map _ _ hnd a ha b hb' e

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem DBase.valid_false {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {y : Lit} (hf : s0.IsFalse y) : s0.ValidLit y := by
  have ht : s0.IsTrue (NOT y) := by
    have := (hb.inv.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf
  have := hb.inv.rsizes.valid ht
  unfold ValidLit at *; rwa [IDX_NOT] at this

theorem DBase.false_same_var {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {x y : Lit} (hx : s0.IsFalse x) (hy : s0.IsFalse y) (e : IDX y = IDX x) : y = x := by
  rcases (IDX_eq_iff y x).mp e with h | h
  · exact h
  · exfalso
    have ht : s0.IsTrue (NOT y) := by
      have := (hb.inv.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hy
    rw [h, NOT_NOT] at ht
    exact (hb.inv.core.valCons x).2 ⟨ht, hx⟩

theorem DInv.analyze {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} {t unres : Nat} (h : DInv s0 L s t unres) {x : Lit} (hx : s0.IsFalse x)
    (hxl : s0.lvl x ≤ L) (hpos : s0.lvl x = L → ∃ p < t, s0.trailL[p]? = some (NOT x)) :
    DInv s0 L (s.analyzeLiteral x).2 t (unres + if (s.analyzeLiteral x).1 then 1 else 0) ∧
    (s0.lvl x = 0 ∨ (s.analyzeLiteral x).2.isAnalyzed (IDX x) = true) ∧
    (∀ i, s.isAnalyzed i = true → (s.analyzeLiteral x).2.isAnalyzed i = true) ∧
    (∀ i, (s.analyzeLiteral x).2.isAnalyzed i = true → s.isAnalyzed i = true ∨ i = IDX x) := by
  have hv := hb.valid_false hx
  have hsz : (IDX x).toNat < s.asg.aBits.size := by
    rw [h.af.bitsSize]; have := hb.inv.rsizes.2.1; unfold ValidLit at hv; omega
  obtain ⟨sp1, sp2, sp3, sp4, sp5⟩ := analyzeLiteral_spec s x hsz
  have L1 := analyzeLiteral_list s x
  have L2 := analyzeLiteral_list_new s x
  generalize hr : s.analyzeLiteral x = r at sp1 sp2 sp3 sp4 sp5 L1 L2 ⊢
  obtain ⟨b, s'⟩ := r
  simp only at sp1 sp2 sp3 sp4 sp5 L1 L2 ⊢
  have el : s.lvl x = s0.lvl x := by rw [h.af.lvl]
  have elv : s.level = s0.level := h.af.level
  rw [el, elv, hb.level] at sp2 sp3
  rw [el] at L2
  simp only [el] at sp4
  have mono : ∀ i, s.isAnalyzed i = true → s'.isAnalyzed i = true := fun i hi => (sp4 i).mpr (Or.inl hi)
  have htailsub : ∀ y ∈ s.clause.view.drop 1, y ∈ s'.clause.view.drop 1 := by
    intro y hy
    rw [sp3]; split
    · rw [U32Vec.view_push, List.drop_append_of_le_length (by have := h.csize; simp; omega)]
      exact List.mem_append_left _ hy
    · exact hy
  refine ⟨⟨sp1.trans h.af, ?csize, ?tail, ?ana, ?aa, ?count, h.tle, ?others, ?list⟩, ?_, mono,
    fun i hi => ((sp4 i).mp hi).imp_right (fun h => h.1)⟩
  case csize => rw [sp3]; split <;> simp [h.csize] <;> have := h.csize <;> omega
  case tail =>
    intro y hy
    rw [sp3] at hy
    split at hy
    · rename_i hc
      rw [U32Vec.view_push, List.drop_append_of_le_length (by have := h.csize; simp; omega)] at hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨a1, a2, a3, a4⟩ := h.tail y hy; exact ⟨a1, a2, a3, mono _ a4⟩
      · simp at hy; subst hy
        exact ⟨hx, by omega, by omega, (sp4 _).mpr (Or.inr ⟨rfl, hc.1⟩)⟩
    · obtain ⟨a1, a2, a3, a4⟩ := h.tail y hy; exact ⟨a1, a2, a3, mono _ a4⟩
  case ana =>
    intro y hyf hyl hya
    rcases (sp4 _).mp hya with hold | ⟨hid, _⟩
    · obtain ⟨a1, a2⟩ := h.ana y hyf hyl hold
      refine ⟨fun hlt => htailsub _ (a1 hlt), fun heq => ?_⟩
      rcases a2 heq with hp | ⟨A, hA, hA'⟩
      · exact Or.inl hp
      · exact Or.inr ⟨A, hA, fun z hz => (hA' z hz).imp_right (mono _)⟩
    · have hyx := hb.false_same_var hx hyf hid
      subst hyx
      by_cases hold : s.isAnalyzed (IDX y) = true
      · obtain ⟨a1, a2⟩ := h.ana y hyf hyl hold
        refine ⟨fun hlt => htailsub _ (a1 hlt), fun heq => ?_⟩
        rcases a2 heq with hp | ⟨A, hA, hA'⟩
        · exact Or.inl hp
        · exact Or.inr ⟨A, hA, fun z hz => (hA' z hz).imp_right (mono _)⟩
      · have hold' : s.isAnalyzed (IDX y) = false := by simpa using hold
        refine ⟨fun hlt => ?_, fun heq => Or.inl (hpos heq)⟩
        rw [sp3, if_pos ⟨by omega, hold', by omega⟩, U32Vec.view_push,
          List.drop_append_of_le_length (by have := h.csize; simp; omega)]
        simp
  case aa =>
    intro i hi
    rcases (sp4 i).mp hi with hold | ⟨rfl, hl0⟩
    · exact h.anaAssigned i hold
    · exact ⟨x, rfl, hx, by omega⟩
  case count =>
    rw [h.count]
    unfold pendCount
    have hnd : (s0.trailL.take t).Nodup := hb.trail_nodup.sublist (List.take_sublist _ _)
    -- marks change only at `IDX x`, and only for a new literal of positive level
    have hmark : ∀ i, s'.isAnalyzed i = (s.isAnalyzed i || (i == IDX x && !(s0.lvl x == 0))) := by
      intro i
      cases h2 : s'.isAnalyzed i <;> cases h1 : s.isAnalyzed i <;> simp
      · intro e; subst e; apply Classical.byContradiction; intro hl
        exact absurd ((sp4 _).mpr (Or.inr ⟨rfl, hl⟩)) (by rw [h2]; simp)
      · exact absurd ((sp4 _).mpr (Or.inl h1)) (by rw [h2]; simp)
      · rcases (sp4 _).mp h2 with h3 | ⟨h3, h4⟩
        · rw [h1] at h3; exact absurd h3 (by simp)
        · exact ⟨h3, h4⟩
    have hsame : ∀ z ∈ s0.trailL.take t, z ≠ NOT x → anaP s0 s' L z = anaP s0 s L z := by
      intro z hz hne
      unfold anaP
      rw [hmark]
      by_cases e : IDX z = IDX x
      · by_cases h0 : s0.lvl x = 0
        · have : (s0.lvl x == 0) = true := by simp [h0]
          rw [this]; simp
        · exfalso
          have hnx := hb.true_on_trail hx (by omega)
          exact hne (hb.idx_unique (List.mem_of_mem_take hz) hnx (by rw [IDX_NOT]; exact e))
      · rw [show (IDX z == IDX x) = false from beq_false_of_ne e]; simp
    by_cases hnew : s0.lvl x ≠ 0 ∧ s.isAnalyzed (IDX x) = false
    · by_cases hL : s0.lvl x = L
      · have hbt : b = true := sp2.mpr ⟨hnew.1, hnew.2, hL⟩
        rw [hbt]; simp only [ite_true]
        obtain ⟨p, hp, hpx⟩ := hpos hL
        have hmem : NOT x ∈ s0.trailL.take t := by
          rw [List.mem_iff_getElem?]; exact ⟨p, by rw [List.getElem?_take]; simp [hp, hpx]⟩
        symm
        apply countP_succ_of_unique _ _ _ (NOT x) hmem hnd
        · unfold anaP; rw [hmark, IDX_NOT]
          have h1 : (s0.lvl x == 0) = false := by simp [hnew.1]
          have h2 : (s0.lvl (NOT x) == L) = true := by rw [hb.inv.core.lvlVar]; simp [hL]
          rw [h1, h2]; simp
        · unfold anaP; rw [IDX_NOT, hnew.2]; simp
        · intro z hz hne; exact hsame z hz hne
      · have hbf : b = false := by
          cases hbv : b
          · rfl
          · exact absurd (sp2.mp hbv).2.2 hL
        rw [hbf]; simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        symm
        apply countP_eq_of_agree
        intro z hz
        by_cases e : z = NOT x
        · subst e; unfold anaP
          have h2 : (s0.lvl (NOT x) == L) = false := by rw [hb.inv.core.lvlVar]; simp [hL]
          rw [h2]; simp
        · exact hsame z hz e
    · have hbf : b = false := by
        cases hbv : b
        · rfl
        · exact absurd ⟨(sp2.mp hbv).1, (sp2.mp hbv).2.1⟩ hnew
      rw [hbf]; simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      symm
      apply countP_eq_of_agree
      intro z hz
      unfold anaP
      rw [hmark]
      by_cases e : IDX z = IDX x
      · by_cases h0 : s0.lvl x = 0
        · have : (s0.lvl x == 0) = true := by simp [h0]
          rw [this]; simp
        · have ha : s.isAnalyzed (IDX x) = true := by
            cases h1 : s.isAnalyzed (IDX x)
            · exact absurd ⟨h0, h1⟩ hnew
            · rfl
          rw [e, ha]; simp only [Bool.true_or]
      · rw [show (IDX z == IDX x) = false from beq_false_of_ne e]; simp
  case others => intro i c hc; rw [sp5 i c hc]; exact h.others i c hc
  case list =>
    intro i hi
    rcases (sp4 i).mp hi with hold | ⟨rfl, hl0⟩
    · exact L1 i (h.list i hold)
    · rcases L2 hl0 with h1 | h1
      · exact h1
      · exact L1 _ (h.list _ h1)
  · rcases Nat.eq_zero_or_pos (s0.lvl x) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ((sp4 _).mpr (Or.inr ⟨rfl, by omega⟩))

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem sublist_pair_pos {α : Type} {a b : α} : ∀ {L : List α}, [a, b].Sublist L →
    ∃ i j : Nat, i < j ∧ L[i]? = some a ∧ L[j]? = some b := by
  intro L h
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    rcases h with _ | ⟨_, h'⟩ | ⟨_, h'⟩
    · obtain ⟨i, j, hij, hi, hj⟩ := ih (by assumption)
      exact ⟨i + 1, j + 1, by omega, by simpa using hi, by simpa using hj⟩
    · -- `a = x` and `[b] <+ xs`
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.singleton_sublist.mp h')
      exact ⟨0, j + 1, by omega, by simp, by simpa using hj⟩

theorem nodup_pos_unique {α : Type} {L : List α} (hnd : L.Nodup) {i j : Nat} {x : α}
    (hi : L[i]? = some x) (hj : L[j]? = some x) : i = j := by
  obtain ⟨hi1, hi2⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj1, hj2⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj hnd).mp (hi2.trans hj2.symm)

/-- Antecedents of a conflict-level literal at trail position `p` are earlier. -/
theorem DBase.ante_before {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {l x : Lit} {p : Nat} (hl : s0.trailL[p]? = some l) (hA : s0.Ante l x) (hx : 0 < s0.lvl x) :
    ∃ q < p, s0.trailL[q]? = some (NOT x) := by
  obtain ⟨i, j, hij, hi, hj⟩ := sublist_pair_pos (hA.2.2 hx)
  have := nodup_pos_unique hb.trail_nodup hj hl
  exact ⟨i, by omega, hi⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem AF.lit_eq {t s : Solver} (h : AF t s) {ref : Ref} (hr : ref ∈ s.arena.chain 0 s.arena.sizeWards)
    {k : Nat} (hk : k < (s.arena.size ref).toNat) : t.arena.lit ref k = s.arena.lit ref k :=
  lit_eq_of_litsL_eq (h.arena.lits ref hr) (by rw [h.arena.size ref hr]; exact hk)

/-- Precondition for analyzing an antecedent literal. -/
def PreA (s0 : Solver) (L t : Nat) (x : Lit) : Prop :=
  s0.IsFalse x ∧ s0.lvl x ≤ L ∧ (s0.lvl x = L → ∃ p < t, s0.trailL[p]? = some (NOT x))

theorem analyzeReasonLits_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {t : Nat} (ref : Ref) (hr : ref ∈ s0.arena.chain 0 s0.arena.sizeWards) (uip : Lit) (n : Nat)
    (hn : n ≤ (s0.arena.size ref).toNat)
    (hpre : ∀ k, k < n → s0.arena.lit ref k ≠ uip → PreA s0 L t (s0.arena.lit ref k)) :
    ∀ (s : Solver) (i u : Nat), DInv s0 L s t u →
    let r := s.analyzeReasonLits ref uip i n u
    DInv s0 L r.2 t r.1 ∧
    (∀ k, i ≤ k → k < n → s0.arena.lit ref k ≠ uip →
      s0.lvl (s0.arena.lit ref k) = 0 ∨ r.2.isAnalyzed (IDX (s0.arena.lit ref k)) = true) ∧
    (∀ j, s.isAnalyzed j = true → r.2.isAnalyzed j = true) ∧
    (∀ j, r.2.isAnalyzed j = true → s.isAnalyzed j = true ∨
      ∃ k, i ≤ k ∧ k < n ∧ s0.arena.lit ref k ≠ uip ∧ j = IDX (s0.arena.lit ref k)) ∧
    u ≤ r.1 := by
  intro s i u
  fun_induction analyzeReasonLits s ref uip i n u with
  | case1 s i u hi lit hlu ih =>
    intro h
    have hlit : lit = s0.arena.lit ref i := h.af.lit_eq hr (by omega)
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
    refine ⟨h1, fun k hk1 hk2 hk3 => ?_, h3, fun j hj => ?_, h5⟩
    · by_cases e : k = i
      · subst e; exact absurd (hlit ▸ (beq_iff_eq.mp hlu)) hk3
      · exact h2 k (by omega) hk2 hk3
    · rcases h4 j hj with h | ⟨k, hk1, hk2, hk3, hk4⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hk2, hk3, hk4⟩
  | case2 s i u hi lit hlu bb s2 heq ih =>
    intro h
    have hlit : lit = s0.arena.lit ref i := h.af.lit_eq hr (by omega)
    have hne : s0.arena.lit ref i ≠ uip := by
      rw [← hlit]; intro e; exact hlu (beq_iff_eq.mpr e)
    obtain ⟨p1, p2, p3⟩ := hpre i hi hne
    rw [← hlit] at p1 p2 p3
    obtain ⟨a1, a2, a3, a4⟩ := DInv.analyze hb h p1 p2 p3
    rw [heq] at a1 a2 a3 a4
    simp only at a1 a2 a3 a4
    simp only [dite_eq_ite] at ih
    have e : (u + if bb = true then 1 else 0) = (if bb = true then u + 1 else u) := by
      split <;> rfl
    rw [e] at a1
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih a1
    refine ⟨h1, fun k hk1 hk2 hk3 => ?_, fun j hj => h3 j (a3 j hj), fun j hj => ?_,
      Nat.le_trans (by split <;> omega) h5⟩
    · by_cases e : k = i
      · subst e
        rw [← hlit]
        rcases a2 with a2 | a2
        · exact Or.inl a2
        · exact Or.inr (h3 _ a2)
      · exact h2 k (by omega) hk2 hk3
    · rcases h4 j hj with h | ⟨k, hk1, hk2, hk3, hk4⟩
      · rcases a4 j h with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨i, Nat.le_refl _, hi, hne, by rw [h', hlit]⟩
      · exact Or.inr ⟨k, by omega, hk2, hk3, hk4⟩
  | case3 s i u hi =>
    intro h
    exact ⟨h, fun k hk1 hk2 => absurd hk2 (by omega), fun j hj => hj, fun j hj => Or.inl hj, Nat.le_refl _⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem findUip_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (s : Solver) (hs : AF s s0) : ∀ t, t ≤ s0.trailL.length → 1 ≤ pendCount s0 s L t →
    let r := s.findUip t
    r.2 < t ∧ s0.trailL[r.2]? = some r.1 ∧ anaP s0 s L r.1 = true ∧
    pendCount s0 s L t = pendCount s0 s L r.2 + 1 ∧
    (∀ q, r.2 < q → q < t → ∀ l, s0.trailL[q]? = some l → anaP s0 s L l = false) := by
  intro t
  fun_induction findUip s t with
  | case1 =>
    intro _ hc; simp [pendCount] at hc
  | case2 t ht uip idx hcond =>
    intro hle hc
    have hlt : t - 1 < s0.trailL.length := by omega
    have hu : s0.trailL[t - 1]? = some uip := by
      have : uip = s.asg.trail.get! (t - 1) := rfl
      rw [this, ← hs.trailL]
      have := trailL_getElem? s (t - 1) (by rw [← length_trailL, hs.trailL]; exact hlt)
      exact this
    have hana : anaP s0 s L uip = true := by
      unfold anaP
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨c1, c2⟩ := hcond
      refine Bool.and_eq_true_iff.mpr ⟨c1, ?_⟩
      have := (levelIdx_eq_level s uip).mp c2
      rw [hs.lvl, hs.level, hb.level] at this
      simpa using this
    refine ⟨by omega, hu, hana, ?_, fun q h1 h2 => absurd h2 (by omega)⟩
    unfold pendCount
    have ht' : t = (t - 1) + 1 := by omega
    conv => lhs; rw [ht', List.take_add_one]
    rw [List.getElem?_eq_getElem hlt] at hu ⊢
    simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    rw [show s0.trailL[t - 1] = uip from Option.some.inj hu, hana]
    simp
  | case3 t ht uip idx hcond ih =>
    intro hle hc
    have hlt : t - 1 < s0.trailL.length := by omega
    have hu : s0.trailL[t - 1]? = some uip := by
      have : uip = s.asg.trail.get! (t - 1) := rfl
      rw [this, ← hs.trailL]
      exact trailL_getElem? s (t - 1) (by rw [← length_trailL, hs.trailL]; exact hlt)
    have hana : anaP s0 s L uip = false := by
      unfold anaP
      cases h1 : s.isAnalyzed (IDX uip)
      · simp
      · have h2 : ¬ (s.levelIdx (IDX uip) == s.level) = true := by
          intro h2; apply hcond; show (s.isAnalyzed (IDX uip) && s.levelIdx (IDX uip) == s.level) = true
          rw [h1, h2]; rfl
        have h3 : ¬ s.lvl uip = s.level.toNat := fun h => h2 ((levelIdx_eq_level s uip).mpr h)
        rw [hs.lvl, hs.level, hb.level] at h3
        have : (s0.lvl uip == L) = false := by simp [h3]
        rw [this]; rfl
    have hcount : pendCount s0 s L t = pendCount s0 s L (t - 1) := by
      unfold pendCount
      have ht' : t = (t - 1) + 1 := by omega
      conv => lhs; rw [ht', List.take_add_one]
      rw [List.getElem?_eq_getElem hlt] at hu ⊢
      simp only [Option.toList_some, List.countP_append, List.countP_singleton]
      rw [show s0.trailL[t - 1] = uip from Option.some.inj hu, hana]
      simp
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (by omega) (by rw [← hcount]; exact hc)
    refine ⟨by omega, h2, h3, by rw [hcount]; exact h4, fun q hq1 hq2 l hl => ?_⟩
    by_cases e : q = t - 1
    · subst e; rw [hu] at hl; cases hl; exact hana
    · exact h5 q hq1 (by omega) l hl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem DBase.ante_of_antecedents {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {l : Lit} {A : List Lit} (hA : s0.Antecedents l A) {x : Lit} (hx : x ∈ A) : s0.Ante l x := by
  obtain ⟨ht, hl, hc⟩ := hA
  rcases hb.inv.reasons l ht hl with e | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩
  · rcases hc with ⟨b1, _, rfl⟩ | ⟨_, hne, _⟩
    · exfalso
      rename_i hbw
      obtain ⟨_, _, hv, _⟩ := hb.inv.ws.bin _ _ hbw
      have := hb.inv.ws.varsBound
      unfold ValidLit at hv; rw [e] at hv
      simp [IDX, DECISION_REASON] at hv
      omega
    · exact absurd e hne
  · rcases hc with ⟨_, _, rfl⟩ | ⟨b1', _⟩
    · simp at hx; subst hx; exact b3
    · rw [b1] at b1'; exact absurd b1' (by simp)
  · rcases hc with ⟨b1', _⟩ | ⟨_, _, _, _, hA'⟩
    · rw [b1] at b1'; exact absurd b1' (by simp)
    · obtain ⟨h1, h2⟩ := (hA' x).mp hx; exact b4 x h1 h2

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem view_set_drop_one (v : U32Vec) (x : UInt32) : (v.set! 0 x).view.drop 1 = v.view.drop 1 := by
  rw [U32Vec.view_set!]
  cases v.view with
  | nil => rfl
  | cons a as => rfl

/-- At the first UIP every analyzed literal is derivable from the learned clause. -/
theorem derive_final {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} {t : Nat} (h : DInv s0 L s t 1) {uip : Lit} {p : Nat} (hpt : p < t)
    (hp : s0.trailL[p]? = some uip) (hcount : pendCount s0 s L p = 0)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → anaP s0 s L l = false) :
    ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isAnalyzed (IDX y) = true →
      DerFalse s0 (s.clause.set! 0 (NOT uip)).view y := by
  have hnd := hb.trail_nodup
  have hC0 : NOT uip ∈ (s.clause.set! 0 (NOT uip)).view := by
    rw [U32Vec.view_set!]
    have : 0 < s.clause.size := by have := h.csize; omega
    exact List.mem_of_getElem (h := by simp; exact this) (List.getElem_set_self _)
  have htail : ∀ y ∈ s.clause.view.drop 1, y ∈ (s.clause.set! 0 (NOT uip)).view := by
    intro y hy
    rw [← view_set_drop_one s.clause (NOT uip)] at hy
    exact List.mem_of_mem_drop hy
  suffices H : ∀ n, ∀ y, s0.trailL[n]? = some (NOT y) → s0.IsFalse y → 0 < s0.lvl y →
      s.isAnalyzed (IDX y) = true → DerFalse s0 (s.clause.set! 0 (NOT uip)).view y by
    intro y hf hl ha
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (hb.true_on_trail hf hl)
    exact H n y hn hf hl ha
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro y hn hf hl ha
  obtain ⟨a1, a2⟩ := h.ana y hf hl ha
  have hle : s0.lvl y ≤ L := by
    have := hb.inv.levelOK.trueLe (NOT y) (by
      have := (hb.inv.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf)
    rw [hb.inv.core.lvlVar, hb.level] at this; exact this
  rcases Nat.lt_or_ge (s0.lvl y) L with hlt | hge
  · exact .inK (htail y (a1 hlt))
  have heq : s0.lvl y = L := by omega
  by_cases hu : NOT y = uip
  · have : y = NOT uip := by rw [← hu, NOT_NOT]
    subst this; exact .inK hC0
  rcases a2 heq with ⟨q, hq, hqy⟩ | ⟨A, hA, hA'⟩
  · exfalso
    have hqn := nodup_pos_unique hnd hqy hn
    subst hqn
    have hana : anaP s0 s L (NOT y) = true := by
      unfold anaP; rw [IDX_NOT, ha, hb.inv.core.lvlVar, heq]; simp
    rcases Nat.lt_trichotomy q p with hlt | heq' | hgt
    · rw [pendCount, List.countP_eq_zero] at hcount
      have hmem : NOT y ∈ s0.trailL.take p := by
        rw [List.mem_iff_getElem?]; exact ⟨q, by rw [List.getElem?_take]; simp [hlt, hqy]⟩
      exact absurd hana (by simpa using hcount _ hmem)
    · subst heq'; rw [hp] at hqy; exact hu (Option.some.inj hqy).symm
    · rw [hgap q hgt hq _ hqy] at hana; exact absurd hana (by simp)
  · apply DerFalse.reason hA
    intro x hx
    have hante := hb.ante_of_antecedents hA hx
    rcases hA' x hx with h0 | hax
    · exact .root hante.1 h0
    · have hxl : 0 < s0.lvl x := by
        obtain ⟨y', hy', hf', hl'⟩ := h.anaAssigned _ hax
        have := hb.false_same_var hante.1 hf' hy'
        subst this; exact hl'
      obtain ⟨q, hq, hqx⟩ := hb.ante_before hn hante hxl
      exact ih q hq x hqx hante.1 hxl hax

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The result of a successful first-UIP deduction. -/
structure DFinal (s0 : Solver) (L : Nat) (s : Solver) : Prop where
  af : AF s s0
  uip : ∃ uip, s.clause.view[0]? = some (NOT uip) ∧ s0.IsTrue uip ∧ s0.lvl uip = L ∧
    s.isAnalyzed (IDX uip) = true
  tail : ∀ y ∈ s.clause.view.drop 1, s0.IsFalse y ∧ 0 < s0.lvl y ∧ s0.lvl y < L ∧
    s.isAnalyzed (IDX y) = true
  der : ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isAnalyzed (IDX y) = true →
    DerFalse s0 s.clause.view y
  others : ∀ i c, (c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable) → s.abit i c = false
  list : ∀ i, s.isAnalyzed i = true → i ∈ s.analyzed.view

/-- DInv is insensitive to updates of the counters `antecedentSize` / `resolventSize`. -/
theorem DInv.counters {s0 : Solver} {L : Nat} {s : Solver} {t u : Nat} (h : DInv s0 L s t u) (a r : UInt32) :
    DInv s0 L { s with antecedentSize := a, resolventSize := r } t u :=
  ⟨AF.trans_left h.af af_rfl, h.csize, h.tail, h.ana, h.anaAssigned, h.count, h.tle, h.others, h.list⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem countP_take_split {α : Type} (f : α → Bool) (T : List α) (p : Nat) (x : α)
    (hp : T[p]? = some x) (hx : f x = true) :
    ∀ k, (∀ q, p < q → q < p + 1 + k → ∀ l, T[q]? = some l → f l = false) →
      p + 1 + k ≤ T.length → (T.take (p + 1 + k)).countP f = (T.take p).countP f + 1 := by
  intro k
  induction k with
  | zero =>
    intro _ hle
    have hpl : p < T.length := by omega
    rw [Nat.add_zero, List.take_add_one, List.getElem?_eq_getElem hpl] at *
    simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    rw [show T[p] = x from Option.some.inj hp, hx]; simp
  | succ k ih =>
    intro hgap hle
    rw [show p + 1 + (k + 1) = (p + 1 + k) + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    rw [ih (fun q h1 h2 l hl => hgap q h1 (by omega) l hl) (by omega)]
    rw [hgap (p + 1 + k) (by omega) (by omega) _ (List.getElem?_eq_getElem (by omega))]
    simp

theorem pendCount_split {s0 s : Solver} {L p t : Nat} {uip : Lit} (hpt : p < t) (htl : t ≤ s0.trailL.length)
    (hp : s0.trailL[p]? = some uip) (hx : anaP s0 s L uip = true)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → anaP s0 s L l = false) :
    pendCount s0 s L t = pendCount s0 s L p + 1 := by
  unfold pendCount
  have := countP_take_split (anaP s0 s L) s0.trailL p uip hp hx (t - p - 1)
    (fun q h1 h2 l hl => hgap q h1 (by omega) l hl) (by omega)
  rwa [show p + 1 + (t - p - 1) = t by omega] at this

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem DInv.switch {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} {t u : Nat} (h : DInv s0 L s t u) {uip : Lit} {p : Nat} (hpt : p < t)
    (hp : s0.trailL[p]? = some uip) (hres : Resolved s0 s uip) (hL : s0.lvl uip = L)
    (hana : s.isAnalyzed (IDX uip) = true)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → anaP s0 s L l = false) :
    DInv s0 L s p (u - 1) := by
  have hnd := hb.trail_nodup
  have hx : anaP s0 s L uip = true := by unfold anaP; rw [hana, hL]; simp
  refine ⟨h.af, h.csize, h.tail, fun y hf hl ha => ?_, h.anaAssigned, ?_, by
    have := h.tle; omega, h.others, h.list⟩
  · obtain ⟨a1, a2⟩ := h.ana y hf hl ha
    refine ⟨a1, fun heq => ?_⟩
    rcases a2 heq with ⟨q, hq, hqy⟩ | hr
    · rcases Nat.lt_trichotomy q p with hlt | heq' | hgt
      · exact Or.inl ⟨q, hlt, hqy⟩
      · subst heq'; rw [hp] at hqy
        have : NOT y = uip := (Option.some.inj hqy).symm
        rw [this]; exact Or.inr hres
      · exfalso
        have := hgap q hgt hq _ hqy
        unfold anaP at this; rw [IDX_NOT, ha, hb.inv.core.lvlVar, heq] at this; simp at this
    · exact Or.inr hr
  · rw [h.count, pendCount_split hpt h.tle hp hx hgap]; omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem DInv.ante {s0 : Solver} {L : Nat} {s : Solver} {t u : Nat} (h : DInv s0 L s t u) (a : UInt32) :
    DInv s0 L { s with antecedentSize := a } t u :=
  ⟨AF.trans_left h.af af_rfl, h.csize, h.tail, h.ana, h.anaAssigned, h.count, h.tle, h.others, h.list⟩

theorem DInv.resol {s0 : Solver} {L : Nat} {s : Solver} {t u : Nat} (h : DInv s0 L s t u) (r : UInt32) :
    DInv s0 L { s with resolventSize := r } t u :=
  ⟨AF.trans_left h.af af_rfl, h.csize, h.tail, h.ana, h.anaAssigned, h.count, h.tle, h.others, h.list⟩

theorem DInv.markUsed {s0 : Solver} {L : Nat} {s : Solver} {t u : Nat} (h : DInv s0 L s t u) (ref : Ref)
    (hl : s.arena.Layout) (hr : ref ∈ s.arena.chain 0 s.arena.sizeWards) :
    DInv s0 L (s.markClauseAsUsed ref) t u := by
  have ea := markClauseAsUsed_asg s ref
  have ec := markClauseAsUsed_clause s ref
  have el := markClauseAsUsed_analyzed s ref
  have hAn : ∀ i, (s.markClauseAsUsed ref).isAnalyzed i = s.isAnalyzed i := by
    intro i; simp [isAnalyzed, abit, abits, ea]
  have hAb : ∀ i c, (s.markClauseAsUsed ref).abit i c = s.abit i c := by
    intro i c; simp [abit, abits, ea]
  have hP : anaP s0 (s.markClauseAsUsed ref) L = anaP s0 s L := by funext l; simp [anaP, hAn]
  refine ⟨AF.trans_left h.af (markClauseAsUsed_af s ref hl hr), by rw [ec]; exact h.csize,
    fun y hy => ?_, fun y hf hl' ha => ?_, fun i hi => h.anaAssigned i (by rw [← hAn]; exact hi),
    by rw [h.count]; unfold pendCount; rw [hP], h.tle, fun i c hc => by rw [hAb]; exact h.others i c hc,
    fun i hi => by rw [el]; exact h.list i (by rw [← hAn]; exact hi)⟩
  · rw [ec] at hy; obtain ⟨a1, a2, a3, a4⟩ := h.tail y hy; exact ⟨a1, a2, a3, by rw [hAn]; exact a4⟩
  · rw [hAn] at ha
    obtain ⟨a1, a2⟩ := h.ana y hf hl' ha
    refine ⟨fun hlt => by rw [ec]; exact a1 hlt, fun heq => ?_⟩
    rcases a2 heq with hp | ⟨A, hA, hA'⟩
    · exact Or.inl hp
    · exact Or.inr ⟨A, hA, fun x hx => by rw [hAn]; exact hA' x hx⟩

theorem resolveReason_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} {t unres : Nat} (h : DInv s0 L s t unres) {uip : Lit} {p : Nat}
    (hp : s0.trailL[p]? = some uip) (hpt : p < t) (hL : s0.lvl uip = L)
    (hdec : ¬ (s.reasonIdx (IDX uip) == DECISION_REASON) = true) :
    DInv s0 L (s.resolveReason uip unres).2 t (s.resolveReason uip unres).1 ∧
    unres ≤ (s.resolveReason uip unres).1 ∧
    Resolved s0 (s.resolveReason uip unres).2 uip ∧
    (∀ i, s.isAnalyzed i = true → (s.resolveReason uip unres).2.isAnalyzed i = true) ∧
    (∀ i, (s.resolveReason uip unres).2.isAnalyzed i = true → s.isAnalyzed i = true ∨
      ∃ x, s0.Ante uip x ∧ i = IDX x) := by
  have huT : s0.IsTrue uip := hb.inv.core.trailTrue _ (List.mem_of_getElem? hp)
  have hLpos := hb.pos
  have hra := hb.inv.reasons uip huT (by omega)
  have eB : s.isBinaryReason (IDX uip) = s0.binOf uip := by
    show s.binOf uip = s0.binOf uip; rw [h.af.binOf]
  have eR : s.reasonIdx (IDX uip) = s0.reasonOf uip := by
    show s.reasonOf uip = s0.reasonOf uip; rw [h.af.reasonOf]
  unfold resolveReason
  simp only
  rw [eR] at hdec
  have hndec : s0.reasonOf uip ≠ DECISION_REASON := fun e => hdec (by rw [e]; rfl)
  have hpre : ∀ x, s0.Ante uip x → PreA s0 L t x := by
    intro x hx
    refine ⟨hx.1, by rw [← hL]; exact hx.2.1, fun hxL => ?_⟩
    obtain ⟨q, hq, hqx⟩ := hb.ante_before hp hx (by omega)
    exact ⟨q, by omega, hqx⟩
  split
  · -- binary reason
    rename_i hbin
    rw [eB] at hbin
    rw [eR]
    rcases hra with e | ⟨b1, b2, b3⟩ | ⟨b1, _⟩
    · exact absurd e hndec
    · obtain ⟨p1, p2, p3⟩ := hpre _ b3
      obtain ⟨a1, a2, a3, a4⟩ := DInv.analyze hb h p1 p2 p3
      generalize s.analyzeLiteral (s0.reasonOf uip) = R at a1 a2 a3 a4 ⊢
      obtain ⟨b, s'⟩ := R
      simp only at a1 a2 a3 a4 ⊢
      have e : (unres + if b = true then 1 else 0) = (if b = true then unres + 1 else unres) := by
        split <;> rfl
      rw [e] at a1
      refine ⟨a1, by split <;> omega, ⟨[s0.reasonOf uip], ⟨huT, by omega, Or.inl ⟨b1, b2, rfl⟩⟩, ?_⟩,
        a3, fun i hi => (a4 i hi).imp_right (fun e => ⟨_, b3, e⟩)⟩
      intro x hx; simp at hx; subst hx; exact a2
    · rw [b1] at hbin; exact absurd hbin (by simp)
  · -- large reason
    rename_i hbin
    rw [eB] at hbin
    rw [eR]
    rcases hra with e | ⟨b1, _⟩ | ⟨b1, b2, b3, b4⟩
    · exact absurd e hndec
    · rw [b1] at hbin; exact absurd hbin (by simp)
    generalize hrf : s0.reasonOf uip = ref at b2 b3 b4 hndec
    have hr : ref ∈ s0.arena.chain 0 s0.arena.sizeWards := b2.1
    have hsz : (s.arena.size ref).toNat = (s0.arena.size ref).toNat := by rw [h.af.arena.size ref hr]
    rw [hsz]
    have spec := analyzeReasonLits_spec hb ref hr uip (s0.arena.size ref).toNat (Nat.le_refl _)
      (fun k hk hne => hpre _ (b4 _ (lit_mem_litsL _ _ _ hk) hne)) s 0 unres h
    generalize s.analyzeReasonLits ref uip 0 (s0.arena.size ref).toNat unres = R at spec ⊢
    obtain ⟨u, s'⟩ := R
    simp only at spec ⊢
    obtain ⟨c1, c2, c3, c4, c5⟩ := spec
    have hl' : s'.arena.Layout := c1.af.arena.layout hb.inv.layout
    have hr' : ref ∈ s'.arena.chain 0 s'.arena.sizeWards := by rw [c1.af.arena.chain]; exact hr
    have hAn : ∀ i, (s'.markClauseAsUsed ref).isAnalyzed i = s'.isAnalyzed i := by
      intro i; simp [isAnalyzed, abit, abits, markClauseAsUsed_asg]
    refine ⟨c1.markUsed ref hl' hr', c5, ⟨(s0.clauseL ref).filter (fun x => x != uip),
      ⟨huT, by omega, Or.inr ⟨b1, by rw [hrf]; exact hndec, by rw [hrf]; exact b2, by rw [hrf]; exact b3,
        fun x => by rw [hrf]; simp [List.mem_filter]⟩⟩, ?_⟩,
      fun i hi => by rw [hAn]; exact c3 i hi, fun i hi => ?_⟩
    · intro x hx
      rw [hAn]
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      have hx2' : x ≠ uip := by simpa using hx2
      obtain ⟨k, hk, rfl⟩ := mem_litsL_iff.mp hx1
      exact c2 k (Nat.zero_le _) hk hx2'
    · rw [hAn] at hi
      rcases c4 i hi with h' | ⟨k, _, hk, hne, rfl⟩
      · exact Or.inl h'
      · exact Or.inr ⟨_, b4 _ (lit_mem_litsL _ _ _ hk) hne, rfl⟩

/-- One round of `deduceLoop`. -/
def deduceRound (s : Solver) (conflict : CRef) (otfs : Bool) (conflictSize : Nat)
    (unresolved resolved : Nat) (t : Nat) (fuel : Nat) : Option CRef × Solver :=
    let (uip, t) := s.findUip t
    if unresolved == 1 then
      (none, { s with clause := s.clause.set! 0 (NOT uip) })
    else if s.reasonIdx (IDX uip) == DECISION_REASON then
      (none, { s with overflowed := true })
    else
      let s := { s with antecedentSize := 1 }
      let resolved := resolved + 1
      let idx := IDX uip
      let (unresolved, s) := s.resolveReason uip unresolved
      let unresolved := unresolved - 1
      let s := { s with resolventSize := s.resolventSize - 1 }
      if otfs && s.antecedentSize > 2 && s.resolventSize < s.antecedentSize then
        let reasonRef := s.reasonIdx idx
        let (res, s) := s.onTheFlyStrengthen reasonRef uip
        let s :=
          if resolved == 1 && s.resolventSize.toNat < conflictSize then
            match conflict with
            | .large d => s.onTheFlySubsume res d
            | .binConflict => s
          else s
        (some res, s)
      else deduceLoop s conflict otfs conflictSize unresolved resolved t fuel

theorem deduceLoop_succ (s : Solver) (conflict : CRef) (otfs : Bool) (cs u r t f : Nat) :
    s.deduceLoop conflict otfs cs u r t (f + 1) = s.deduceRound conflict otfs cs u r t f := rfl

/-- The outcome of the deduction loop. -/
def DOut (s0 : Solver) (L : Nat) (s : Solver) (r : Option CRef × Solver) : Prop :=
  r.1 = none ∧ (r.2.overflowed = true ∨ (DFinal s0 L r.2 ∧ ∀ i, s.isAnalyzed i = true → r.2.isAnalyzed i = true))

theorem deduceLoop_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (conflict : CRef) (csize : Nat) :
    ∀ fuel (s : Solver) (t unres resolved : Nat), DInv s0 L s t unres → 1 ≤ unres →
    DOut s0 L s (s.deduceLoop conflict false csize unres resolved t fuel) := by
  intro fuel
  induction fuel with
  | zero => intro s t unres resolved _ _; exact ⟨rfl, Or.inl rfl⟩
  | succ fuel ih =>
    intro s t unres resolved h hu
    rw [deduceLoop_succ]
    unfold deduceRound
    have hfu := findUip_spec hb s h.af t h.tle (by rw [← h.count]; exact hu)
    generalize s.findUip t = r at hfu ⊢
    obtain ⟨uip, p⟩ := r
    obtain ⟨hpt, hp, hana, hcnt, hgap⟩ := hfu
    simp only at hpt hp hana hcnt hgap ⊢
    have huip : s.isAnalyzed (IDX uip) = true ∧ s0.lvl uip = L := by
      unfold anaP at hana; simp at hana; exact hana
    have huT : s0.IsTrue uip := hb.inv.core.trailTrue _ (List.mem_of_getElem? hp)
    split
    · -- the first UIP
      rename_i h1
      have h1' : unres = 1 := by simpa using h1
      subst h1'
      refine ⟨rfl, Or.inr ⟨⟨AF.trans_left h.af af_rfl, ⟨uip, ?_, huT, huip.2, huip.1⟩, ?_, ?_,
        h.others, h.list⟩, fun i hi => hi⟩⟩
      · rw [U32Vec.view_set!]
        have : 0 < s.clause.view.length := by have := h.csize; simp; omega
        rw [List.getElem?_set_self this]
      · intro y hy; rw [view_set_drop_one] at hy; exact h.tail y hy
      · exact derive_final hb h hpt hp (by rw [h.count] at hcnt; omega) hgap
    split
    · exact ⟨rfl, Or.inl rfl⟩
    rename_i h1 hdec
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    generalize hR : ({ s with antecedentSize := 1 } : Solver).resolveReason uip unres = R
    have h1i : DInv s0 L { s with antecedentSize := 1 } t unres := h.ante 1
    have spec := resolveReason_spec hb h1i hp hpt huip.2 hdec
    rw [hR] at spec
    obtain ⟨u2, s2⟩ := R
    simp only at spec ⊢
    obtain ⟨r1, r2, r3, r4, r5⟩ := spec
    have hu1 : unres ≠ 1 := by intro e; apply h1; simp [e]
    -- no analyzed conflict-level literal strictly between `p` and `t`
    have hgap2 : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → anaP s0 s2 L l = false := by
      intro q hq1 hq2 l hl
      have hg := hgap q hq1 hq2 l hl
      unfold anaP at hg ⊢
      cases hlv : (s0.lvl l == L)
      · simp
      · rw [hlv] at hg
        have hna : s.isAnalyzed (IDX l) = false := by simpa using hg
        cases h2 : s2.isAnalyzed (IDX l)
        · rfl
        · exfalso
          rcases r5 _ h2 with h3 | ⟨x, hx, hxe⟩
          · have : s.isAnalyzed (IDX l) = true := h3
            rw [hna] at this; exact absurd this (by simp)
          · obtain ⟨y, hy, hf, hl0⟩ := r1.anaAssigned _ h2
            have hyx := hb.false_same_var hx.1 hf (by rw [hy, hxe])
            subst hyx
            obtain ⟨q', hq', hq'x⟩ := hb.ante_before hp hx hl0
            have hlx : l = NOT y := by
              apply hb.idx_unique (List.mem_of_getElem? hl) (List.mem_of_getElem? hq'x)
              rw [IDX_NOT, hy, hxe]
            subst hlx
            have := nodup_pos_unique hb.trail_nodup hl hq'x
            omega
    have hana2 : s2.isAnalyzed (IDX uip) = true := r4 _ huip.1
    have hD : DInv s0 L s2 p (u2 - 1) := r1.switch hb hpt hp r3 huip.2 hana2 hgap2
    have hD' := hD.resol (s2.resolventSize - 1)
    obtain ⟨o1, o2⟩ := ih _ p (u2 - 1) (resolved + 1) hD' (by omega)
    refine ⟨o1, ?_⟩
    rcases o2 with o2 | ⟨o2, o3⟩
    · exact Or.inl o2
    · exact Or.inr ⟨o2, fun i hi => o3 i (r4 i hi)⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem AF.crefLit {t s : Solver} (h : AF t s) (c : CRef)
    (hc : ∀ r, c = .large r → r ∈ s.arena.chain 0 s.arena.sizeWards) {k : Nat}
    (hk : k < s.crefSize c) : t.crefLit c k = s.crefLit c k := by
  cases c with
  | binConflict => unfold Solver.crefLit; rw [h.c0, h.c1]
  | large r => exact h.lit_eq (hc r rfl) hk

theorem AF.crefSize {t s : Solver} (h : AF t s) (c : CRef)
    (hc : ∀ r, c = .large r → r ∈ s.arena.chain 0 s.arena.sizeWards) : t.crefSize c = s.crefSize c := by
  cases c with
  | binConflict => rfl
  | large r => show (t.arena.size r).toNat = (s.arena.size r).toNat; rw [h.arena.size r (hc r rfl)]

theorem analyzeConflictLits_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (c : CRef) (hc : ∀ r, c = .large r → r ∈ s0.arena.chain 0 s0.arena.sizeWards) (n : Nat)
    (hn : n ≤ s0.crefSize c) (hpre : ∀ k, k < n → PreA s0 L s0.trailL.length (s0.crefLit c k)) :
    ∀ (s : Solver) (i u cs : Nat), DInv s0 L s s0.trailL.length u →
    let r := s.analyzeConflictLits c i n u cs
    DInv s0 L r.2.2 s0.trailL.length r.1 ∧
    (∀ k, i ≤ k → k < n → s0.lvl (s0.crefLit c k) = 0 ∨ r.2.2.isAnalyzed (IDX (s0.crefLit c k)) = true) ∧
    (∀ j, s.isAnalyzed j = true → r.2.2.isAnalyzed j = true) := by
  intro s i u cs
  fun_induction analyzeConflictLits s c i n u cs with
  | case1 s i u cs hi lit cs' bb s2 heq ih =>
    intro h
    have hlit : lit = s0.crefLit c i := h.af.crefLit c hc (by omega)
    obtain ⟨p1, p2, p3⟩ := hpre i hi
    rw [← hlit] at p1 p2 p3
    obtain ⟨a1, a2, a3, _⟩ := DInv.analyze hb h p1 p2 p3
    rw [heq] at a1 a2 a3
    simp only at a1 a2 a3
    simp only [dite_eq_ite] at ih
    have e : (u + if bb = true then 1 else 0) = (if bb = true then u + 1 else u) := by split <;> rfl
    rw [e] at a1
    obtain ⟨h1, h2, h3⟩ := ih a1
    refine ⟨h1, fun k hk1 hk2 => ?_, fun j hj => h3 j (a3 j hj)⟩
    by_cases e' : k = i
    · subst e'; rw [← hlit]
      rcases a2 with a2 | a2
      · exact Or.inl a2
      · exact Or.inr (h3 _ a2)
    · exact h2 k (by omega) hk2
  | case2 s i u cs hi =>
    intro h
    exact ⟨h, fun k hk1 hk2 => absurd hk2 (by omega), fun j hj => hj⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Preconditions of conflict analysis on the conflict level `L`. -/
structure APre (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) (L : Nat) : Prop where
  base : DBase Φ s L
  conflict : ConflictOK s s c
  clean : ∀ i b, (b = ABits.analyzed ∨ b = ABits.poisoned ∨ b = ABits.removable ∨ b = ABits.shrinkable) →
    s.abit i b = false
  clauseEmpty : s.clause.size = 0
  hasL : ∃ k, k < s.crefSize c ∧ s.lvl (s.crefLit c k) = L
  otfs : s.options.otfs = 0

theorem ConflictOK.lit_false {s : Solver} {c : CRef} (h : ConflictOK s s c) {k : Nat}
    (hk : k < s.crefSize c) : s.IsFalse (s.crefLit c k) := by
  cases c with
  | binConflict =>
    obtain ⟨_, h0, h1⟩ := h
    show s.IsFalse (if k == 0 then s.conflictLit0 else s.conflictLit1)
    split
    · exact h0
    · exact h1
  | large r =>
    obtain ⟨_, h2⟩ := h
    exact h2 _ (lit_mem_litsL _ _ _ hk)

theorem ConflictOK.chain {s : Solver} {c : CRef} (h : ConflictOK s s c) :
    ∀ r, c = .large r → r ∈ s.arena.chain 0 s.arena.sizeWards := by
  intro r hr; subst hr; exact h.1.1

theorem APre.pre {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} {L : Nat} (h : APre Φ s c L) :
    ∀ k, k < s.crefSize c → PreA s L s.trailL.length (s.crefLit c k) := by
  intro k hk
  have hf := h.conflict.lit_false hk
  have hb := h.base
  refine ⟨hf, ?_, fun hL => ?_⟩
  · have ht : s.IsTrue (NOT (s.crefLit c k)) := by
      have := (hb.inv.core.valCons (NOT (s.crefLit c k))).1; rw [NOT_NOT] at this; exact this.mpr hf
    have := hb.inv.levelOK.trueLe _ ht
    rw [hb.inv.core.lvlVar, hb.level] at this; exact this
  · have := hb.true_on_trail hf (by rw [hL]; exact hb.pos)
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp this
    exact ⟨p, (List.getElem?_eq_some_iff.mp hp).1, hp⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

def dfuS1 (s : Solver) (c : CRef) : Solver :=
  if s.crefSize c > 2 then
    match c with
    | .large ref => s.markClauseAsUsed ref
    | .binConflict => s
  else s

def dfuTail (s2 : Solver) (c : CRef) : Option CRef × Solver :=
  let (unresolved, conflictSize, s) := s2.analyzeConflictLits c 0 (s2.crefSize c) 0 0
  s.deduceLoop c (s.options.otfs != 0) conflictSize unresolved 0 s.asg.trail.size (s.asg.trail.size + 1)

/-- The marking step before the conflict loop. -/
theorem deduce_s1 {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} {L : Nat} (h : APre Φ s c L) :
    AF (dfuS1 s c) s ∧ (dfuS1 s c).clause = s.clause ∧ (∀ i b, (dfuS1 s c).abit i b = s.abit i b) ∧
    (dfuS1 s c).analyzed = s.analyzed := by
  have key : ∀ ref, c = .large ref → AF (s.markClauseAsUsed ref) s ∧ (s.markClauseAsUsed ref).clause = s.clause ∧
      (∀ i b, (s.markClauseAsUsed ref).abit i b = s.abit i b) ∧
      (s.markClauseAsUsed ref).analyzed = s.analyzed := by
    intro ref hr
    refine ⟨markClauseAsUsed_af s ref h.base.inv.layout (h.conflict.chain ref hr),
      markClauseAsUsed_clause s ref, fun i b => by simp [abit, abits, markClauseAsUsed_asg],
      markClauseAsUsed_analyzed s ref⟩
  unfold dfuS1
  split
  · cases c with
    | binConflict => exact ⟨AF.refl _, rfl, fun _ _ => rfl, rfl⟩
    | large ref => exact key ref rfl
  · exact ⟨AF.refl _, rfl, fun _ _ => rfl, rfl⟩

theorem deduceFirstUip_eq (s : Solver) (c : CRef) :
    s.deduceFirstUipClause c = dfuTail ({ dfuS1 s c with clause := (dfuS1 s c).clause.push INVALID_LIT, antecedentSize := 0, resolventSize := 0 }) c := rfl

theorem deduceFirstUip_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} {L : Nat}
    (h : APre Φ s c L) :
    (s.deduceFirstUipClause c).1 = none ∧ ((s.deduceFirstUipClause c).2.overflowed = true ∨
      (DFinal s L (s.deduceFirstUipClause c).2 ∧
        ∀ k, k < s.crefSize c → DerFalse s (s.deduceFirstUipClause c).2.clause.view (s.crefLit c k))) := by
  have hb := h.base
  obtain ⟨f1, c1, a1, l1⟩ := deduce_s1 h
  rw [deduceFirstUip_eq]
  generalize dfuS1 s c = s1 at f1 c1 a1 l1 ⊢
  -- the state with the placeholder for the UIP
  generalize hs2 : ({ s1 with clause := s1.clause.push INVALID_LIT, antecedentSize := 0, resolventSize := 0 } : Solver) = s2
  have f2 : AF s2 s := by rw [← hs2]; exact AF.trans_left f1 af_rfl
  have c2 : s2.clause = s1.clause.push INVALID_LIT := by rw [← hs2]
  have a2 : ∀ i b, s2.abit i b = s.abit i b := by intro i b; rw [← hs2, ← a1 i b]; rfl
  have hD2 : DInv s L s2 s.trailL.length 0 := by
    have hcl : s2.clause.view = [INVALID_LIT] := by
      rw [c2, U32Vec.view_push, c1]
      have : s.clause.view = [] := List.eq_nil_of_length_eq_zero (by simp [h.clauseEmpty])
      rw [this]; rfl
    have hna : ∀ i, s2.isAnalyzed i = false := by
      intro i; show s2.abit i ABits.analyzed = false; rw [a2]; exact h.clean i _ (Or.inl rfl)
    refine ⟨f2, by rw [c2]; simp, ?_, ?_, ?_, ?_, Nat.le_refl _, ?_, ?_⟩
    · intro y hy; rw [hcl] at hy; simp at hy
    · intro y _ _ ha; rw [hna] at ha; exact absurd ha (by simp)
    · intro i ha; rw [hna] at ha; exact absurd ha (by simp)
    · unfold pendCount; symm; rw [List.countP_eq_zero]; intro x _; unfold anaP; rw [hna]; simp
    · intro i b hb'; rw [a2]; exact h.clean i b (Or.inr hb')
    · intro i ha; rw [hna] at ha; exact absurd ha (by simp)
  have hn2 : s2.crefSize c = s.crefSize c := f2.crefSize c h.conflict.chain
  have spec := analyzeConflictLits_spec hb c h.conflict.chain (s.crefSize c) (Nat.le_refl _) h.pre s2 0 0 0 hD2
  unfold dfuTail
  rw [hn2]
  generalize s2.analyzeConflictLits c 0 (s.crefSize c) 0 0 = R at spec ⊢
  obtain ⟨unres, cs, s3⟩ := R
  simp only at spec ⊢
  obtain ⟨d1, d2, d3⟩ := spec
  have hot : (s3.options.otfs != 0) = false := by rw [d1.af.options, h.otfs]; rfl
  have htr : s3.asg.trail.size = s.trailL.length := by rw [← length_trailL, d1.af.trailL]
  rw [hot, htr]
  obtain ⟨k, hk, hkL⟩ := h.hasL
  have hu : 1 ≤ unres := by
    rw [d1.count]
    unfold pendCount
    rw [List.take_of_length_le (Nat.le_refl _)]
    have hf := h.conflict.lit_false hk
    have hkp := h.pre k hk
    have hmem := hb.true_on_trail hf (by rw [hkL]; exact hb.pos)
    rcases d2 k (Nat.zero_le _) hk with h0 | ha
    · rw [hkL] at h0; have := hb.pos; omega
    · apply List.countP_pos_iff.mpr
      refine ⟨_, hmem, ?_⟩
      unfold anaP; rw [IDX_NOT, ha, hb.inv.core.lvlVar, hkL]; simp
  obtain ⟨o1, o2⟩ := deduceLoop_spec hb c cs _ s3 s.trailL.length unres 0 d1 hu
  refine ⟨o1, ?_⟩
  rcases o2 with o2 | ⟨o2, o3⟩
  · exact Or.inl o2
  · refine Or.inr ⟨o2, fun k hk => ?_⟩
    rcases d2 k (Nat.zero_le _) hk with h0 | ha
    · exact .root (h.conflict.lit_false hk) h0
    · have hf := h.conflict.lit_false hk
      have hl : 0 < s.lvl (s.crefLit c k) := by
        obtain ⟨y, hy, hfy, hly⟩ := d1.anaAssigned _ ha
        have := hb.false_same_var hf hfy hy; rw [← this]; exact hly
      exact o2.der _ hf hl (o3 _ ha)


end Solver
end LeanKissat
