import LeanKissat.Proofs.SearchStep

/-!
# Lucky phases (`lucky.c`)
-/

namespace LeanKissat
namespace Solver

theorem internalAssume_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s)
    (hp : s.propagate = s.trailL.length) {lit : Lit} (hx : s.ValidLit lit)
    (hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit) :
    SearchInv Φ (s.internalAssume lit) ∧ IrrMono s (s.internalAssume lit) ∧
    (s.internalAssume lit).vars = s.vars ∧ (s.internalAssume lit).level = s.level + 1 := by
  have e : s.internalAssume lit = (({ s with level := s.level + 1 } : Solver).pushFrame lit).assign
      (({ s with level := s.level + 1 } : Solver).pushFrame lit).probing
      ({ s with level := s.level + 1 } : Solver).level false lit DECISION_REASON := rfl
  rw [e]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pushAssign_spec (W := { s with level := s.level + 1 }) h.inv h.invS
    hp rfl rfl rfl rfl rfl rfl rfl rfl rfl hx hun (({ s with level := s.level + 1 } : Solver).pushFrame lit).probing
  generalize (({ s with level := s.level + 1 } : Solver).pushFrame lit).assign
      (({ s with level := s.level + 1 } : Solver).pushFrame lit).probing
      ({ s with level := s.level + 1 } : Solver).level false lit DECISION_REASON = t at p1 p2 p3 p4 p5 p6 p7 p8
  refine ⟨⟨p1, p2, clean_of_bits p4 h.clean, by rw [p6]; exact h.clauseEmpty,
    fun e => h.incons (by rw [← Flg.inconsistent p7]; exact e), by rw [Flg.watching p7]; exact h.watching,
    by rw [Flg.options p7]; exact h.opts, h.imp.flg p7⟩, p3, p8, p5⟩

/-- `SearchInv` does not depend on the `probing` flag. -/
theorem SearchInv.setProbing {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) (b : Bool) :
    SearchInv Φ { s with probing := b } :=
  have hS : Same { s with probing := b } s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ⟨hS.sinv h.inv, fun c hc => by unfold InvS; exact h.invS c hc, h.clean, h.clauseEmpty, h.incons, h.watching,
    h.opts, h.imp⟩

/-- The outcome of one lucky step. -/
def LStepOut (Φ : (Nat → Bool) → Prop) (s : Solver) (r : Option UInt32 × Solver) : Prop :=
  (r.1 = none → SearchInv Φ r.2 ∧ IrrMono s r.2) ∧
  (r.1 = some 20 → ¬ ∃ β, Φ β) ∧ (∀ x, r.1 = some x → x = 0 ∨ x = 20) ∧
  (r.1 = some 0 → Flagged r.2 ∨ (SearchInv Φ r.2 ∧ IrrMono s r.2))

theorem LStepOut.none {Φ : (Nat → Bool) → Prop} {s t : Solver} (h : SearchInv Φ t)
    (m : IrrMono s t) : LStepOut Φ s (none, t) :=
  ⟨fun _ => ⟨h, m⟩, fun e => by simp at e, fun _ e => by simp at e, fun e => by simp at e⟩

theorem LStepOut.zeroF {Φ : (Nat → Bool) → Prop} {s t : Solver} (h : Flagged t) : LStepOut Φ s (some 0, t) :=
  ⟨fun e => by simp at e, fun e => by simp at e, fun x e => by simp at e; exact Or.inl e.symm,
    fun _ => Or.inl h⟩

theorem LStepOut.zeroI {Φ : (Nat → Bool) → Prop} {s t : Solver} (h : SearchInv Φ t) (m : IrrMono s t) :
    LStepOut Φ s (some 0, t) :=
  ⟨fun e => by simp at e, fun e => by simp at e, fun x e => by simp at e; exact Or.inl e.symm,
    fun _ => Or.inr ⟨h, m⟩⟩

theorem LStepOut.twenty {Φ : (Nat → Bool) → Prop} {s t : Solver} (h : ¬ ∃ β, Φ β) : LStepOut Φ s (some 20, t) :=
  ⟨fun e => by simp at e, fun _ => h, fun x e => by simp at e; exact Or.inr e.symm, fun e => by simp at e⟩

theorem notPorted_flagged (s : Solver) : Flagged { s with notPorted := true } := Or.inr (Or.inr rfl)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Backtracking below the level of a conflict. -/
theorem backtrackConflict_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (hA : AStepPre Φ s c)
    (hinc : s.inconsistent = true → ¬ ∃ β, Φ β) (hopt : PlainOpts s.options) (himp : ImportOK s)
    {nl : UInt32} (hlt : nl < s.level) :
    SearchInv Φ (s.backtrackWithoutUpdatingPhases nl) ∧ IrrMono s (s.backtrackWithoutUpdatingPhases nl) ∧
    (s.backtrackWithoutUpdatingPhases nl).level = nl ∧ (s.backtrackWithoutUpdatingPhases nl).vars = s.vars := by
  have hcp := hA.cpre
  obtain ⟨b1, b2, _, b4, b5⟩ := backtrack_spec hcp.inv hlt (P := s.propagate - 1) hcp.invP
    (hcp.framesLe _ (List.getElem_mem _))
  have ba := backtrack_anaSide s nl
  generalize s.backtrackWithoutUpdatingPhases nl = t at b1 b2 b4 b5 ba ⊢
  have hcl : t.clause = s.clause := by have := ba; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  have hflg : Flg t = Flg s := flg_of_anaSide ba
  refine ⟨⟨b1, b4, fun i b hb => ?_, by rw [hcl]; exact hA.clauseEmpty,
    fun e => hinc (by rw [← Flg.inconsistent hflg]; exact e), by rw [Flg.watching hflg]; exact hcp.watching,
    by rw [Flg.options hflg]; exact hopt, himp.flg hflg⟩, b5.irrMono, b2, b5.vars⟩
  unfold abit abits; rw [b5.aBits]; exact hA.clean i b hb

theorem luckyAssume_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) {lit : Lit} :
    ∀ t, s.luckyAssume lit = some t →
      SearchInv Φ t ∧ IrrMono s t ∧ t.vars = s.vars ∧ t.level = s.level + 1 := by
  intro t ht
  unfold luckyAssume at ht
  split at ht
  · rename_i hc
    cases ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have hx : s.ValidLit lit := UInt32.lt_iff_toNat_lt.mp h1
    have hun := unassigned_of_value h.inv.core h2 true
    simp only [ite_true] at hun
    exact internalAssume_spec h (by rw [h3, length_trailL]) hx hun
  · cases ht

theorem probingPropagate_level {Φ : (Nat → Bool) → Prop} {u : Solver} (h : SearchInv Φ u) :
    (u.probingPropagate none true).1.level = u.level :=
  ((probingPropagate_sf u).2.1.same.level).trans (searchPropagate_spec h.inv h.invS).level

theorem level_succ_pos {Φ : (Nat → Bool) → Prop} {t : Solver} (h : SInv Φ t) : (0 : UInt32) < t.level + 1 := by
  have := h.level_small
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add]; simp; omega

theorem luckyFlip_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (hA : AStepPre Φ s c)
    (hinc : s.inconsistent = true → ¬ ∃ β, Φ β) (hopt : PlainOpts s.options) (himp : ImportOK s)
    (hl : 1 < s.level) (first : Lit) :
    LStepOut Φ s (s.luckyFlip first) := by
  unfold luckyFlip
  dsimp only
  have hl' : 1 < s.level.toNat := by have := UInt32.lt_iff_toNat_lt.mp hl; simpa using this
  have hlt : s.level - 1 < s.level := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]
    simp; omega
  obtain ⟨t1, t2, _, _⟩ := backtrackConflict_spec hA hinc hopt himp hlt
  generalize s.backtrackWithoutUpdatingPhases (s.level - 1) = t at t1 t2
  have ha := luckyAssume_spec t1 (lit := NOT first)
  generalize t.luckyAssume (NOT first) = A at ha
  cases A with
  | none => exact LStepOut.zeroF (notPorted_flagged _)
  | some u =>
    obtain ⟨u1, u2, _, u4⟩ := ha u rfl
    dsimp only
    obtain ⟨m, hn, hc⟩ := probingProp_spec u1
    have hlev := probingPropagate_level u1
    generalize u.probingPropagate none true = R at m hn hc hlev
    obtain ⟨v, d⟩ := R
    cases d with
    | none =>
      obtain ⟨v1, -⟩ := hn rfl
      exact LStepOut.none v1 ((t2.trans u2).trans m)
    | some d =>
      obtain ⟨a, ai, ao, aim⟩ := hc d rfl
      have hv0 : (0 : UInt32) < v.level := by rw [hlev, u4]; exact level_succ_pos t1.inv
      obtain ⟨w1, w2, _, _⟩ := backtrackConflict_spec a ai ao aim hv0
      exact LStepOut.zeroI w1 (((t2.trans u2).trans m).trans w2)

theorem luckyFailedRoot_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) :
    LStepOut Φ s s.luckyFailedRoot := by
  unfold luckyFailedRoot
  obtain ⟨m, hn, hc⟩ := probingProp_spec h
  generalize s.probingPropagate none true = R at m hn hc
  obtain ⟨v, d⟩ := R
  cases d with
  | none =>
    obtain ⟨v1, -⟩ := hn rfl
    exact LStepOut.none v1 m
  | some d =>
    obtain ⟨a, ai, ao, aim⟩ := hc d rfl
    obtain ⟨a1, _, _⟩ := searchAnalyze_spec a ai ao aim
    dsimp only
    generalize v.analyze d = A at a1
    obtain ⟨r, w⟩ := A
    dsimp only at a1 ⊢
    by_cases hr : r = 20
    · rw [if_pos (by simp [hr])]; exact LStepOut.twenty (a1 hr)
    · rw [if_neg (by simpa using hr)]; exact LStepOut.zeroF (notPorted_flagged _)

theorem luckyFailed_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (hA : AStepPre Φ s c)
    (hinc : s.inconsistent = true → ¬ ∃ β, Φ β) (hopt : PlainOpts s.options) (himp : ImportOK s) :
    LStepOut Φ s (s.luckyFailed c) := by
  unfold luckyFailed
  obtain ⟨a1, a2, a3⟩ := searchAnalyze_spec hA hinc hopt himp
  generalize s.analyze c = A at a1 a2 a3
  obtain ⟨r, w⟩ := A
  dsimp only at a1 a2 a3 ⊢
  by_cases hr : r = 20
  · rw [if_pos (by simp [hr])]; exact LStepOut.twenty (a1 hr)
  rw [if_neg (by simpa using hr)]
  have h0 : r = 0 := by rcases a2 with e | e; exact e; exact absurd e hr
  by_cases hf : (w.overflowed || w.outOfResources || w.notPorted) = true
  · rw [if_pos hf]
    refine LStepOut.zeroF ?_
    simp only [Bool.or_eq_true] at hf
    rcases hf with (e | e) | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  rw [if_neg hf]
  rcases a3 h0 with hfl | ⟨w1, w2⟩
  · exfalso; apply hf; rcases hfl with e | e | e <;> simp [e]
  · have := luckyFailedRoot_spec w1
    exact ⟨fun e => by obtain ⟨x, z⟩ := this.1 e; exact ⟨x, w2.trans z⟩, this.2.1, this.2.2.1,
      fun e => by
        rcases this.2.2.2 e with h' | ⟨x, y⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, w2.trans y⟩⟩

theorem luckyConflict_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (hA : AStepPre Φ s c)
    (hinc : s.inconsistent = true → ¬ ∃ β, Φ β) (hopt : PlainOpts s.options) (himp : ImportOK s) (first : Lit) :
    LStepOut Φ s (s.luckyConflict first c) := by
  unfold luckyConflict
  split
  · exact luckyFlip_spec hA hinc hopt himp ‹_› first
  · exact luckyFailed_spec hA hinc hopt himp

theorem LStepOut.trans_left {Φ : (Nat → Bool) → Prop} {s t : Solver} {r : Option UInt32 × Solver}
    (m : IrrMono s t) (h : LStepOut Φ t r) : LStepOut Φ s r :=
  ⟨fun e => by obtain ⟨x, z⟩ := h.1 e; exact ⟨x, m.trans z⟩, h.2.1, h.2.2.1, fun e => by
    rcases h.2.2.2 e with h' | ⟨x, y⟩
    · exact Or.inl h'
    · exact Or.inr ⟨x, m.trans y⟩⟩

theorem luckyStep_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) (eidx : Nat) (fp : Bool) :
    LStepOut Φ s (s.luckyStep eidx fp) := by
  unfold luckyStep
  dsimp only
  split
  · exact LStepOut.none h (IrrMono.refl _)
  split
  · exact LStepOut.none h (IrrMono.refl _)
  split
  · exact LStepOut.none h (IrrMono.refl _)
  split
  · exact LStepOut.none h (IrrMono.refl _)
  have ha := luckyAssume_spec h (lit := if fp then s.importLit.get! eidx else NOT (s.importLit.get! eidx))
  generalize s.luckyAssume (if fp then s.importLit.get! eidx else NOT (s.importLit.get! eidx)) = A at ha
  cases A with
  | none => exact LStepOut.zeroF (notPorted_flagged _)
  | some u =>
    obtain ⟨u1, u2, _, _⟩ := ha u rfl
    dsimp only
    obtain ⟨m, hn, hc⟩ := probingProp_spec u1
    generalize u.probingPropagate none true = R at m hn hc
    obtain ⟨v, d⟩ := R
    cases d with
    | none =>
      obtain ⟨v1, -⟩ := hn rfl
      exact LStepOut.none v1 (u2.trans m)
    | some d =>
      obtain ⟨a, ai, ao, aim⟩ := hc d rfl
      exact (luckyConflict_spec a ai ao aim _).trans_left (u2.trans m)

/-- The outcome of a lucky phase. -/
def LSatOut (Φ : (Nat → Bool) → Prop) (s : Solver) (r : UInt32 × Solver) : Prop :=
  (r.1 = 10 → SearchInv Φ r.2 ∧ IrrMono s r.2) ∧ (r.1 = 20 → ¬ ∃ β, Φ β) ∧
  (r.1 = 0 → Flagged r.2 ∨ (SearchInv Φ r.2 ∧ IrrMono s r.2)) ∧ (r.1 = 0 ∨ r.1 = 10 ∨ r.1 = 20)

theorem LSatOut.trans_left {Φ : (Nat → Bool) → Prop} {s t : Solver} {r : UInt32 × Solver}
    (m : IrrMono s t) (h : LSatOut Φ t r) : LSatOut Φ s r :=
  ⟨fun e => by obtain ⟨x, z⟩ := h.1 e; exact ⟨x, m.trans z⟩, h.2.1, fun e => by
    rcases h.2.2.1 e with h' | ⟨x, y⟩
    · exact Or.inl h'
    · exact Or.inr ⟨x, m.trans y⟩, h.2.2.2⟩

theorem luckySatLoop_spec {Φ : (Nat → Bool) → Prop} (fw fp : Bool) (n : Nat) :
    ∀ (s : Solver) (k : Nat), (Flagged s ∨ SearchInv Φ s) → LSatOut Φ s (luckySatLoop fw fp n s k) := by
  intro s k
  fun_induction luckySatLoop fw fp n s k with
  | case1 s k hf =>
    intro _
    refine ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inl ?_, Or.inl rfl⟩
    simp only [Bool.or_eq_true] at hf
    rcases hf with (e | e) | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  | case2 s k hf hk eidx r s' hst =>
    intro h
    have h' : SearchInv Φ s := by
      rcases h with e | e
      · exfalso; apply hf; rcases e with e | e | e <;> simp [e]
      · exact e
    have := luckyStep_spec h' eidx fp
    rw [hst] at this
    obtain ⟨o1, o2, o3, o4⟩ := this
    refine ⟨fun e => ?_, fun e => o2 (by simp at e; simp [e]), fun e => o4 (by simp at e; simp [e]), ?_⟩
    · rcases o3 r rfl with e' | e' <;> rw [e'] at e <;> simp at e
    · rcases o3 r rfl with e' | e'
      · exact Or.inl e'
      · exact Or.inr (Or.inr e')
  | case3 s k hf hk eidx s' hst ih =>
    intro h
    have h' : SearchInv Φ s := by
      rcases h with e | e
      · exfalso; apply hf; rcases e with e | e | e <;> simp [e]
      · exact e
    have := luckyStep_spec h' eidx fp
    rw [hst] at this
    obtain ⟨h1, m⟩ := this.1 rfl
    exact (ih (Or.inr h1)).trans_left m
  | case4 s k hf hk =>
    intro h
    have h' : SearchInv Φ s := by
      rcases h with e | e
      · exfalso; apply hf; rcases e with e | e | e <;> simp [e]
      · exact e
    exact ⟨fun _ => ⟨h', IrrMono.refl _⟩, fun e => by simp at e, fun e => by simp at e, Or.inr (Or.inl rfl)⟩

theorem luckyAssignLoop_spec {Φ : (Nat → Bool) → Prop} (pos : Bool) (n : Nat) :
    ∀ (s : Solver) (i : Nat), SearchInv Φ s →
      (luckyAssignLoop pos n s i).notPorted = true ∨
      (SearchInv Φ (luckyAssignLoop pos n s i) ∧ IrrMono s (luckyAssignLoop pos n s i)) := by
  intro s i
  fun_induction luckyAssignLoop pos n s i with
  | case1 s i hi idx hact ih => exact ih
  | case2 s i hi idx hact hval ih => exact ih
  | case3 s i hi idx hact hval hA => intro _; left; rfl
  | case4 s i hi idx hact hval u hA v c hP =>
    intro _; left; rfl
  | case5 s i hi idx hact hval u hA v hP ih =>
    intro h
    obtain ⟨u1, u2, _, _⟩ := luckyAssume_spec h u hA
    obtain ⟨m, hn, _⟩ := probingProp_spec u1
    rw [hP] at m hn
    obtain ⟨v1, -⟩ := hn rfl
    rcases ih v1 with e | ⟨w1, w2⟩
    · exact Or.inl e
    · exact Or.inr ⟨w1, (u2.trans m).trans w2⟩
  | case6 s i hi => intro h; exact Or.inr ⟨h, IrrMono.refl _⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem luckyAssignPhase_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) :
    (s.luckyAssignPhase.2.notPorted = true ∨ (SearchInv Φ s.luckyAssignPhase.2 ∧ IrrMono s s.luckyAssignPhase.2)) ∧
    (s.luckyAssignPhase.1 = 0 ∨ s.luckyAssignPhase.1 = 10) := by
  unfold luckyAssignPhase
  have key : ∀ (b : Bool) (u : Solver), SearchInv Φ u →
      ((u.luckyAssignAll b).notPorted = true ∨ (SearchInv Φ (u.luckyAssignAll b) ∧ IrrMono u (u.luckyAssignAll b))) :=
    fun b u hu => luckyAssignLoop_spec b u.vars.toNat u 0 hu
  have h1 : ((if s.noAllNegativeClauses then ((if (s.luckyAssignAll true).notPorted then 0 else 10 : UInt32),
      s.luckyAssignAll true) else (0, s)).2.notPorted = true ∨
      (SearchInv Φ (if s.noAllNegativeClauses then ((if (s.luckyAssignAll true).notPorted then 0 else 10 : UInt32),
        s.luckyAssignAll true) else (0, s)).2 ∧
       IrrMono s (if s.noAllNegativeClauses then ((if (s.luckyAssignAll true).notPorted then 0 else 10 : UInt32),
        s.luckyAssignAll true) else (0, s)).2)) ∧
      ((if s.noAllNegativeClauses then ((if (s.luckyAssignAll true).notPorted then 0 else 10 : UInt32),
        s.luckyAssignAll true) else (0, s)).1 = 0 ∨
       (if s.noAllNegativeClauses then ((if (s.luckyAssignAll true).notPorted then 0 else 10 : UInt32),
        s.luckyAssignAll true) else (0, s)).1 = 10) := by
    split
    · exact ⟨key true s h, by dsimp only; split <;> simp⟩
    · exact ⟨Or.inr ⟨h, IrrMono.refl _⟩, Or.inl rfl⟩
  generalize (if s.noAllNegativeClauses then ((if (s.luckyAssignAll true).notPorted then 0 else 10 : UInt32),
      s.luckyAssignAll true) else (0, s)) = R at h1
  obtain ⟨res, u⟩ := R
  obtain ⟨h2, h3⟩ := h1
  dsimp only at h2 h3 ⊢
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    rcases h2 with e | ⟨u1, u2⟩
    · rw [hc.1.2] at e; simp at e
    · refine ⟨?_, by split <;> simp⟩
      rcases key false u u1 with e | ⟨v1, v2⟩
      · exact Or.inl e
      · exact Or.inr ⟨v1, u2.trans v2⟩
  · exact ⟨h2, h3⟩

theorem luckySatisfiable_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : Flagged s ∨ SearchInv Φ s)
    (fw fp : Bool) : LSatOut Φ s (s.luckySatisfiable fw fp) := luckySatLoop_spec fw fp _ s 0 h

theorem LSatOut.chain {Φ : (Nat → Bool) → Prop} {s : Solver} {r1 : UInt32} {t : Solver}
    (h : LSatOut Φ s (r1, t)) (f : Solver → UInt32 × Solver) (hf : ∀ t, SearchInv Φ t → LSatOut Φ t (f t))
    (hff : ∀ t, Flagged t → f t = (0, t)) :
    LSatOut Φ s (match (r1, t) with | (0, t) => f t | r => r) := by
  by_cases e : r1 = 0
  · subst e
    show LSatOut Φ s (f t)
    rcases h.2.2.1 rfl with hfl | ⟨h1, m⟩
    · rw [hff t hfl]
      exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inl hfl, Or.inl rfl⟩
    · exact (hf t h1).trans_left m
  · have : (match (r1, t) with | (0, t) => f t | r => r) = (r1, t) := by
      split
      · rename_i heq; simp at heq; exact absurd heq.1 e
      · rfl
    rw [this]; exact h

theorem luckySatisfiable_flagged (t : Solver) (h : Flagged t) (fw fp : Bool) : t.luckySatisfiable fw fp = (0, t) := by
  unfold luckySatisfiable; rw [luckySatLoop, if_pos (by rcases h with e | e | e <;> simp [e])]

theorem lsat_step {Φ : (Nat → Bool) → Prop} (fw fp : Bool) (f : Solver → UInt32 × Solver)
    (hf : ∀ t, SearchInv Φ t → LSatOut Φ t (f t)) (hff : ∀ t, Flagged t → f t = (0, t)) :
    (∀ u, SearchInv Φ u → LSatOut Φ u (match u.luckySatisfiable fw fp with | (0, s) => f s | r => r)) ∧
    (∀ u, Flagged u → (match u.luckySatisfiable fw fp with | (0, s) => f s | r => r) = (0, u)) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h1 := luckySatisfiable_spec (Φ := Φ) (Or.inr hu) fw fp
    generalize u.luckySatisfiable fw fp = R at h1
    obtain ⟨r1, t⟩ := R
    exact h1.chain f hf hff
  · rw [luckySatisfiable_flagged u hu]; exact hff u hu

theorem luckySatPhases_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) :
    LSatOut Φ s s.luckySatPhases := by
  have l3 := lsat_step (Φ := Φ) false false (fun y => y.luckySatisfiable false true)
    (fun y hy => luckySatisfiable_spec (Or.inr hy) false true) (fun y hy => luckySatisfiable_flagged y hy _ _)
  have l2 := lsat_step (Φ := Φ) true true _ l3.1 l3.2
  have l1 := lsat_step (Φ := Φ) true false _ l2.1 l2.2
  exact l1.1 s h

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The outcome of `kissat_lucky`. -/
def LuckyOut (Φ : (Nat → Bool) → Prop) (s : Solver) (r : UInt32 × Solver) : Prop :=
  (r.1 = 10 → SATState Φ s r.2) ∧ (r.1 = 20 → ¬ ∃ β, Φ β) ∧
  (r.1 = 0 → Flagged r.2 ∨ (SearchInv Φ r.2 ∧ IrrMono s r.2))

theorem Flagged.setProbing {t : Solver} (h : Flagged t) (b : Bool) : Flagged { t with probing := b } := h

theorem lucky_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) : LuckyOut Φ s s.lucky := by
  unfold lucky
  by_cases hi : s.inconsistent = true
  · rw [if_pos hi]; exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inr ⟨h, IrrMono.refl _⟩⟩
  rw [if_neg hi]
  by_cases hf : (s.overflowed || s.outOfResources || s.notPorted) = true
  · rw [if_pos hf]; exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inr ⟨h, IrrMono.refl _⟩⟩
  rw [if_neg hf]
  by_cases hl : (s.options.lucky == 0) = true
  · rw [if_pos hl]; exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inr ⟨h, IrrMono.refl _⟩⟩
  rw [if_neg hl]
  have h0 := h.setProbing true
  have m0 : IrrMono s { s with probing := true } := IrrMono.of_eq rfl rfl rfl
  obtain ⟨a1, a2⟩ := luckyAssignPhase_spec h0
  dsimp only
  generalize ({ s with probing := true } : Solver).luckyAssignPhase = R at a1 a2
  obtain ⟨res, u⟩ := R
  dsimp only at a1 a2 ⊢
  by_cases hnp : u.notPorted = true
  · rw [if_pos hnp]
    exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inl (Or.inr (Or.inr hnp))⟩
  rw [if_neg hnp]
  have hu : SearchInv Φ u ∧ IrrMono s u := by
    rcases a1 with e | ⟨u1, u2⟩
    · exact absurd e hnp
    · exact ⟨u1, m0.trans u2⟩
  have hL : LSatOut Φ u (if res == 0 then u.luckySatPhases else (res, u)) := by
    split
    · exact luckySatPhases_spec hu.1
    · rename_i hz
      have : res = 10 := by rcases a2 with e | e; simp [e] at hz; exact e
      subst this
      exact ⟨fun _ => ⟨hu.1, IrrMono.refl _⟩, fun e => by simp at e, fun e => by simp at e, Or.inr (Or.inl rfl)⟩
  generalize (if res == 0 then u.luckySatPhases else (res, u)) = R at hL
  obtain ⟨r, v⟩ := R
  obtain ⟨l1, l2, l3, l4⟩ := hL
  dsimp only at l1 l2 l3 l4 ⊢
  by_cases hc : (r == 10 && !v.luckyComplete) = true
  · rw [if_pos hc]
    exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inl (Or.inr (Or.inr rfl))⟩
  rw [if_neg hc]
  refine ⟨fun e => ?_, fun e => l2 e, fun e => ?_⟩
  · obtain ⟨v1, v2⟩ := l1 e
    have hcomp : v.luckyComplete = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      cases hv : v.luckyComplete
      · exact absurd ⟨e, hv⟩ hc
      · rfl
    unfold luckyComplete at hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hcomp
    have hv := v1.setProbing false
    exact ⟨hv.inv, hv.invS, by show v.propagate = v.trailL.length; rw [hcomp.2, length_trailL],
      hcomp.1, (hu.2.trans v2).trans (IrrMono.of_eq rfl rfl rfl), hv.imp⟩
  · rcases l3 e with hf | ⟨v1, v2⟩
    · exact Or.inl hf
    · exact Or.inr ⟨v1.setProbing false, (hu.2.trans v2).trans (IrrMono.of_eq rfl rfl rfl)⟩

end Solver
end LeanKissat
