import LeanKissat.Proofs.Decide

/-!
# Restarts, propagation and analysis at the search level
-/

namespace LeanKissat
namespace Solver

theorem updateFocusedRestartLimit_sf (s : Solver) : SFr s.updateFocusedRestartLimit s := by
  unfold updateFocusedRestartLimit; dsimp only; sf_fields

theorem updateTargetAndBestPhases_sf (s : Solver) : SFr s.updateTargetAndBestPhases s := by
  have h : ∀ f : Solver → Prop, (∀ t : Solver, SFr t s → f t) → f s.updateTargetAndBestPhases := by
    intro f hf
    unfold updateTargetAndBestPhases saveTargetPhases saveBestPhases
    split
    · exact hf s (SFr.refl _)
    · dsimp only
      split <;> split <;> exact hf _ (by sf_rfl)
  exact h (fun t => SFr t s) (fun t ht => ht)

theorem reuseTrail_zero (s : Solver) (h : s.options.restartreusetrail = 0) : s.reuseTrail = (0, s) := by
  unfold reuseTrail; simp [h]

theorem restart_eq (s : Solver) (h : s.options.restartreusetrail = 0) :
    s.restart = (let t := (INC! s restarts).backtrackInConsistentState 0
      if !t.stable then t.updateFocusedRestartLimit else t) := by
  unfold restart
  dsimp only
  rw [reuseTrail_zero _ (by exact h)]

/-- Backtracking to the root level (restarts, `reduce`). -/
theorem backtrack0_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s)
    (hl : s.level ≠ 0) :
    SearchInv Φ (s.backtrackWithoutUpdatingPhases 0) ∧ IrrMono s (s.backtrackWithoutUpdatingPhases 0) ∧
    (s.backtrackWithoutUpdatingPhases 0).level = 0 := by
  have hlt : (0 : UInt32) < s.level := by
    rw [UInt32.lt_iff_toNat_lt]
    have : s.level.toNat ≠ 0 := fun e => hl (UInt32.toNat_inj.mp (by simpa using e))
    simp; omega
  have hfl : 0 < s.framesL.length := by rw [h.inv.levelOK.len]; exact UInt32.lt_iff_toNat_lt.mp hlt
  obtain ⟨b1, b2, _, b4, b5⟩ := backtrack_spec h.inv hlt (P := s.framesL[0]'hfl)
    (fun c hc => invSAt_mono (h.invS c hc) (h.inv.levelOK.framesLe _ (List.getElem_mem _))) (Nat.le_refl _)
  have ba := backtrack_anaSide s 0
  generalize s.backtrackWithoutUpdatingPhases 0 = t at b1 b2 b4 b5 ba ⊢
  have hcl : t.clause = s.clause := by have := ba; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  have hflg : Flg t = Flg s := flg_of_anaSide ba
  refine ⟨⟨b1, b4, fun i b hb => ?_, by rw [hcl]; exact h.clauseEmpty,
    fun e => h.incons (by rw [← Flg.inconsistent hflg]; exact e), by rw [Flg.watching hflg]; exact h.watching,
    by rw [Flg.options hflg]; exact h.opts, h.imp.flg hflg⟩, b5.irrMono, b2⟩
  unfold abit abits; rw [b5.aBits]; exact h.clean i b hb

theorem restart_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) (hl : s.level ≠ 0) :
    SearchInv Φ s.restart ∧ IrrMono s s.restart := by
  rw [restart_eq _ h.opts.reuse]
  have h1 : SFr (INC! s restarts) s := by sf_rfl
  generalize (INC! s restarts) = s1 at h1
  have h2 := (updateTargetAndBestPhases_sf s1).trans h1
  unfold backtrackInConsistentState
  generalize s1.updateTargetAndBestPhases = s2 at h2
  have hs2 := h2.searchInv h
  have hl2 : s2.level ≠ 0 := by rw [h2.same.level]; exact hl
  obtain ⟨b1, b2, _⟩ := backtrack0_spec hs2 hl2
  generalize s2.backtrackWithoutUpdatingPhases 0 = t at b1 b2
  dsimp only
  split
  · exact ⟨(updateFocusedRestartLimit_sf t).searchInv b1,
      (h2.irrMono.trans b2).trans (updateFocusedRestartLimit_sf t).irrMono⟩
  · exact ⟨b1, h2.irrMono.trans b2⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The solver stopped with `unknown` (flags checked by the search loop). -/
def Flagged (t : Solver) : Prop := t.overflowed = true ∨ t.outOfResources = true ∨ t.notPorted = true

theorem searchProp_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) :
    IrrMono s s.searchPropagate.1 ∧
    (s.searchPropagate.2 = none → SearchInv Φ s.searchPropagate.1 ∧
      s.searchPropagate.1.propagate = s.searchPropagate.1.trailL.length) ∧
    (∀ c, s.searchPropagate.2 = some c → AStepPre Φ s.searchPropagate.1 c ∧
      (s.searchPropagate.1.inconsistent = true → ¬ ∃ β, Φ β) ∧ PlainOpts s.searchPropagate.1.options ∧
      ImportOK s.searchPropagate.1) := by
  have sp := searchPropagate_spec h.inv h.invS
  have hib := searchPropagate_importBits h.inv h.invS
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := searchPropagate_side h.inv h.invS
  generalize s.searchPropagate = R at sp q1 q2 q3 q4 q5 q6 hib ⊢
  obtain ⟨t, res⟩ := R
  dsimp only at sp q1 q2 q3 q4 q5 q6 hib ⊢
  have hopt : PlainOpts t.options := by rw [sp.options]; exact h.opts
  have himp : ImportOK t := h.imp.congr sp.importLit hib sp.vars
  refine ⟨sp.db.irrMono, fun hn => ?_, fun c hc => ?_⟩
  · obtain ⟨n1, n2⟩ := sp.none hn
    refine ⟨⟨sp.inv, n2, clean_of_bits q4 h.clean, by rw [q1]; exact h.clauseEmpty,
      fun e => h.incons (by rw [← q5 hn]; exact e), by rw [q2]; exact h.watching, hopt, himp⟩, n1⟩
  · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := sp.some c hc
    have hfr : t.framesL = s.framesL := by unfold framesL; rw [sp.frameTrail]
    refine ⟨⟨⟨sp.inv, g1, g4, fun f hf => ?_, sp.inv.levelLt, by rw [q2]; exact h.watching⟩,
      clean_of_bits q4 h.clean, by rw [q1]; exact h.clauseEmpty, hopt.otfs, hopt.eager, hopt.bumpreasons⟩,
      fun e => ?_, hopt, himp⟩
    · rw [hfr] at hf; have := h.inv.levelOK.framesLe f hf; omega
    · rcases q6 e with e' | e'
      · exact h.incons e'
      · exact root_conflict_unsat sp.inv g1 e'

theorem searchAnalyze_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (hA : AStepPre Φ s c)
    (hinc : s.inconsistent = true → ¬ ∃ β, Φ β) (hopt : PlainOpts s.options) (himp : ImportOK s) :
    ((s.analyze c).1 = 20 → ¬ ∃ β, Φ β) ∧ ((s.analyze c).1 = 0 ∨ (s.analyze c).1 = 20) ∧
    ((s.analyze c).1 = 0 → Flagged (s.analyze c).2 ∨
      (SearchInv Φ (s.analyze c).2 ∧ IrrMono s (s.analyze c).2)) := by
  obtain ⟨a1, a2, a3⟩ := analyze_spec hA hinc
  refine ⟨a1, a2, fun h0 => ?_⟩
  rcases a3 h0 with h' | h' | co
  · exact Or.inl (Or.inl h')
  · exact Or.inl (Or.inr (Or.inl h'))
  · right
    refine ⟨⟨co.inv, co.invS, co.clean, co.clauseEmpty, fun e => hinc (by rw [← Flg.inconsistent co.incons]; exact e),
      by rw [Flg.watching co.incons]; exact hA.cpre.watching, by rw [Flg.options co.incons]; exact hopt,
      himp.flg co.incons⟩, co.mono⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- A satisfying end state of the search. -/
structure SATState (Φ : (Nat → Bool) → Prop) (s0 t : Solver) : Prop where
  inv : SInv Φ t
  invS : ∀ c, t.InDB c → t.InvS c
  prop : t.propagate = t.trailL.length
  unassigned : t.asg.unassigned = 0
  mono : IrrMono s0 t
  imp : ImportOK t

theorem SATState.trans_left {Φ : (Nat → Bool) → Prop} {a b t : Solver} (h1 : IrrMono a b) (h2 : SATState Φ b t) :
    SATState Φ a t := ⟨h2.inv, h2.invS, h2.prop, h2.unassigned, h1.trans h2.mono, h2.imp⟩

/-- The specification required from the `reduce` procedure. -/
def ReduceOK (Φ : (Nat → Bool) → Prop) (red : Solver → UInt32 × Solver) : Prop :=
  ∀ s, SearchInv Φ s → s.propagate = s.trailL.length → s.reducing = true →
    ((red s).1 = 20 → ¬ ∃ β, Φ β) ∧ ((red s).1 = 0 ∨ (red s).1 = 20) ∧
    ((red s).1 = 0 → Flagged (red s).2 ∨ (SearchInv Φ (red s).2 ∧ IrrMono s (red s).2))

/-- The outcome of one search step. -/
def StepOut (Φ : (Nat → Bool) → Prop) (s : Solver) (r : Option UInt32 × Solver) : Prop :=
  (r.1 = some 20 → ¬ ∃ β, Φ β) ∧ (r.1 = some 10 → SATState Φ s r.2) ∧
  (r.1 = none → Flagged r.2 ∨ (SearchInv Φ r.2 ∧ IrrMono s r.2))

theorem switchingSearchMode_false (s : Solver) (h : s.options.stable = 2) : s.switchingSearchMode = false := by
  unfold switchingSearchMode; simp [h]

theorem reordering_false (s : Solver) (h : s.options.reorder = 0) : s.reordering = false := by
  unfold reordering; simp [h]

theorem rephasing_false (s : Solver) (h : s.options.rephase = 0) : s.rephasing = false := by
  unfold rephasing; simp [h]

theorem restarting_spec (s : Solver) : SFr s.restarting.2 s ∧ (s.restarting.1 = true → s.level ≠ 0) := by
  unfold restarting
  split
  · exact ⟨SFr.refl _, fun h => by simp at h⟩
  · split
    · exact ⟨SFr.refl _, fun h => by simp at h⟩
    · rename_i h0
      split
      · exact ⟨SFr.refl _, fun h => by simp at h⟩
      · split
        · exact ⟨by sf_rfl, fun _ => by simpa using h0⟩
        · exact ⟨SFr.refl _, fun _ => by simpa using h0⟩

/-- The steps after a conflict-free propagation. -/
theorem searchStepNone_spec {Φ : (Nat → Bool) → Prop} {P : Procedures} (hred : ReduceOK Φ P.reduce)
    (hprobe : ∀ s, (P.probe s).1 = 0 ∧ Flagged (P.probe s).2)
    (helim : ∀ s, (P.eliminate s).1 = 0 ∧ Flagged (P.eliminate s).2)
    {t : Solver} (h : SearchInv Φ t) (hp : t.propagate = t.trailL.length) :
    StepOut Φ t
      (if t.iterating then (none, { t with iterating := false })
      else if t.asg.unassigned == 0 then (some 10, t)
      else if t.terminationFlagged then (some 0, t)
      else if t.reducing then
        let (res, s) := P.reduce t
        if res != 0 then (some res, s) else (none, s)
      else if t.switchingSearchMode then (none, t.switchSearchMode)
      else
        let (r, s) := t.restarting
        if r then (none, s.restart)
        else if s.reordering then (none, P.reorder s)
        else if s.rephasing then (none, P.rephase s)
        else if s.probingP then
          let (res, s) := P.probe s
          if res != 0 then (some res, s) else (none, s)
        else if s.eliminating then
          let (res, s) := P.eliminate s
          if res != 0 then (some res, s) else (none, s)
        else if s.conflictLimitHit then (some 0, s)
        else if s.decisionLimitHit then (some 0, s)
        else (none, s.decide)) := by
  unfold StepOut
  by_cases hi : t.iterating = true
  · rw [ite_eq_left hi]
    have : SFr { t with iterating := false } t := by sf_rfl
    exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inr ⟨this.searchInv h, this.irrMono⟩⟩
  rw [ite_eq_right hi]
  by_cases hu : (t.asg.unassigned == 0) = true
  · rw [ite_eq_left hu]
    exact ⟨fun e => by simp at e, fun _ => ⟨h.inv, h.invS, hp, by simpa using hu, IrrMono.refl _, h.imp⟩,
      fun e => by simp at e⟩
  rw [ite_eq_right hu]
  by_cases htf : t.terminationFlagged = true
  · rw [ite_eq_left htf]
    exact ⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e⟩
  rw [ite_eq_right htf]
  by_cases hrd : t.reducing = true
  · rw [ite_eq_left hrd]
    obtain ⟨r1, r2, r3⟩ := hred t h hp hrd
    generalize P.reduce t = R at r1 r2 r3 ⊢
    obtain ⟨res, u⟩ := R
    dsimp only at r1 r2 r3 ⊢
    by_cases hz : res = 0
    · rw [ite_eq_right (by simp [hz])]
      exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => r3 hz⟩
    · rw [ite_eq_left (by simpa using hz)]
      refine ⟨fun e => r1 (by simpa using e), fun e => ?_, fun e => by simp at e⟩
      have : res = 10 := by simpa using e
      rcases r2 with r | r <;> rw [r] at this <;> simp at this
  rw [ite_eq_right hrd]
  rw [ite_eq_right (by rw [switchingSearchMode_false t h.opts.stable]; simp)]
  obtain ⟨q1, q2⟩ := restarting_spec t
  generalize t.restarting = R at q1 q2 ⊢
  obtain ⟨r, u⟩ := R
  dsimp only at q1 q2 ⊢
  have hu := q1.searchInv h
  have hpu : u.propagate = u.trailL.length := by
    rw [q1.same.propagate, hp]; simp [trailL, q1.same.asg]
  by_cases hr : r = true
  · rw [ite_eq_left hr]
    have hl : u.level ≠ 0 := by rw [q1.same.level]; exact q2 hr
    obtain ⟨g1, g2⟩ := restart_spec hu hl
    exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inr ⟨g1, q1.irrMono.trans g2⟩⟩
  rw [ite_eq_right hr, ite_eq_right (by rw [reordering_false u hu.opts.reorder]; simp),
    ite_eq_right (by rw [rephasing_false u hu.opts.rephase]; simp)]
  by_cases hpb : u.probingP = true
  · rw [ite_eq_left hpb]
    obtain ⟨p1, p2⟩ := hprobe u
    rw [ite_eq_right (by simp [p1])]
    exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inl p2⟩
  rw [ite_eq_right hpb]
  by_cases hel : u.eliminating = true
  · rw [ite_eq_left hel]
    obtain ⟨p1, p2⟩ := helim u
    rw [ite_eq_right (by simp [p1])]
    exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inl p2⟩
  rw [ite_eq_right hel]
  by_cases hcl : u.conflictLimitHit = true
  · rw [ite_eq_left hcl]; exact ⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e⟩
  rw [ite_eq_right hcl]
  by_cases hdl : u.decisionLimitHit = true
  · rw [ite_eq_left hdl]; exact ⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e⟩
  rw [ite_eq_right hdl]
  · refine ⟨fun e => by simp at e, fun e => by simp at e, fun _ => ?_⟩
    rcases decide_spec hu hpu with d | ⟨d1, d2⟩
    · exact Or.inl (Or.inr (Or.inr d))
    · exact Or.inr ⟨d1, q1.irrMono.trans d2⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem StepOut.trans_left {Φ : (Nat → Bool) → Prop} {s t : Solver} {r : Option UInt32 × Solver}
    (m : IrrMono s t) (h : StepOut Φ t r) : StepOut Φ s r :=
  ⟨h.1, fun e => (h.2.1 e).trans_left m, fun e => by
    rcases h.2.2 e with h' | ⟨h1, h2⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h1, m.trans h2⟩⟩

theorem searchStep_spec {Φ : (Nat → Bool) → Prop} {P : Procedures} (hred : ReduceOK Φ P.reduce)
    (hprobe : ∀ s, (P.probe s).1 = 0 ∧ Flagged (P.probe s).2)
    (helim : ∀ s, (P.eliminate s).1 = 0 ∧ Flagged (P.eliminate s).2)
    {s : Solver} (h : SearchInv Φ s) : StepOut Φ s (searchStep P s) := by
  unfold searchStep
  obtain ⟨m, hn, hc⟩ := searchProp_spec h
  generalize s.searchPropagate = R at m hn hc ⊢
  obtain ⟨t, res⟩ := R
  dsimp only at m hn hc ⊢
  cases res with
  | some c =>
    obtain ⟨a, hinc, hopt, himp⟩ := hc c rfl
    obtain ⟨a1, a2, a3⟩ := searchAnalyze_spec a hinc hopt himp
    show StepOut Φ s (if ((t.analyze c).fst != 0) = true then (some (t.analyze c).fst, (t.analyze c).snd)
      else (none, (t.analyze c).snd))
    unfold StepOut
    by_cases hz : (t.analyze c).1 = 0
    · rw [ite_eq_right (by simp [hz])]
      refine ⟨fun e => by simp at e, fun e => by simp at e, fun _ => ?_⟩
      rcases a3 hz with h' | ⟨h1, h2⟩
      · exact Or.inl h'
      · exact Or.inr ⟨h1, m.trans h2⟩
    · rw [ite_eq_left (by simpa using hz)]
      refine ⟨fun e => a1 (by simpa using e), fun e => ?_, fun e => by simp at e⟩
      have : (t.analyze c).1 = 10 := by simpa using e
      rcases a2 with r | r <;> rw [r] at this <;> simp at this
  | none =>
    obtain ⟨hs, hp⟩ := hn rfl
    exact (searchStepNone_spec hred hprobe helim hs hp).trans_left m

theorem searchLoop_flagged (P : Procedures) {s : Solver} (h : Flagged s) (b st : Nat) :
    searchLoop P s b st = (0, s) := by
  rw [searchLoop]
  rw [ite_eq_left (by rcases h with h | h | h <;> simp [h])]

/-- The search loop: 20 refutes `Φ`, 10 ends in a satisfying state. -/
theorem searchLoop_spec {Φ : (Nat → Bool) → Prop} {P : Procedures} (hred : ReduceOK Φ P.reduce)
    (hprobe : ∀ s, (P.probe s).1 = 0 ∧ Flagged (P.probe s).2)
    (helim : ∀ s, (P.eliminate s).1 = 0 ∧ Flagged (P.eliminate s).2) :
    ∀ (s : Solver) (bound steps : Nat), SearchInv Φ s →
      ((searchLoop P s bound steps).1 = 20 → ¬ ∃ β, Φ β) ∧
      ((searchLoop P s bound steps).1 = 10 → SATState Φ s (searchLoop P s bound steps).2) := by
  intro s bound steps
  fun_induction searchLoop P s bound steps with
  | case1 s bound steps hf => intro _; exact ⟨fun e => by simp at e, fun e => by simp at e⟩
  | case2 s bound steps hf hc => intro _; exact ⟨fun e => by simp at e, fun e => by simp at e⟩
  | case3 s bound steps hf hc res s' hst =>
    intro h
    have := searchStep_spec hred hprobe helim h
    rw [hst] at this
    exact ⟨fun e => this.1 (by simp at e; simp [e]), fun e => this.2.1 (by simp at e; simp [e])⟩
  | case4 s bound steps hf hc s' hst h1 ih =>
    intro h
    have := searchStep_spec hred hprobe helim h
    rw [hst] at this
    rcases this.2.2 rfl with hfl | ⟨h', m⟩
    · rw [searchLoop_flagged P hfl]; exact ⟨fun e => by simp at e, fun e => by simp at e⟩
    · obtain ⟨i1, i2⟩ := ih h'
      exact ⟨i1, fun e => (i2 e).trans_left m⟩
  | case5 => intro _; exact ⟨fun e => by simp at e, fun e => by simp at e⟩
  | case6 s bound steps hf hc s' hst h1 h2 h3 ih =>
    intro h
    have := searchStep_spec hred hprobe helim h
    rw [hst] at this
    rcases this.2.2 rfl with hfl | ⟨h', m⟩
    · rw [searchLoop_flagged P hfl]; exact ⟨fun e => by simp at e, fun e => by simp at e⟩
    · obtain ⟨i1, i2⟩ := ih h'
      exact ⟨i1, fun e => (i2 e).trans_left m⟩
  | case7 => intro _; exact ⟨fun e => by simp at e, fun e => by simp at e⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem propagateTrailLoop_none (b : Nat) : ∀ (s : Solver) (i : Nat),
    propagateTrailLoop b none s i = searchPropagateLoop b s i := by
  intro s i
  fun_induction searchPropagateLoop b s i with
  | case1 s i hi lit s' res hpl hres =>
    rw [propagateTrailLoop, dite_eq_left hi]; simp only [lit, hpl, hres]; rfl
  | case2 s i hi lit s' res hpl hres ih =>
    rw [propagateTrailLoop, dite_eq_left hi]; simp only [lit, hpl]; rw [ite_eq_right hres]; exact ih
  | case3 s i hi => rw [propagateTrailLoop, dite_eq_right hi]

theorem SFr.symm {s t : Solver} (h : SFr t s) : SFr s t :=
  ⟨⟨h.same.asg.symm, h.same.arena.symm, h.same.watches.symm, h.same.delayed.symm, h.same.vars.symm,
    h.same.level.symm, h.same.frameTrail.symm, h.same.propagate.symm, h.same.options.symm⟩,
    h.clause.symm, h.flg.symm, h.bits.symm⟩

theorem flushTrail_sfr {x y : Solver} (h : SFr x y) : SFr x.flushTrail y.flushTrail := by
  have ha := h.same.asg
  refine ⟨⟨by simp [flushTrail, ha], h.same.arena, h.same.watches, h.same.delayed, h.same.vars, h.same.level,
    h.same.frameTrail, rfl, h.same.options⟩, h.clause, ?_, by simp [flushTrail, ha]⟩
  have := h.flg; simp only [Flg, flushTrail] at this ⊢; exact this

theorem uct_sfr {x y : Solver} (h : SFr x y) (c : Option CRef) (f cc cc' : Bool) :
    SFr (x.updateConflictsAndTrail c f cc) (y.updateConflictsAndTrail c f cc') := by
  have hl := h.same.level
  have ha := h.same.asg
  unfold updateConflictsAndTrail
  cases c with
  | none =>
    dsimp only
    by_cases hc : (f && x.level == 0 && x.asg.unflushed != 0) = true
    · rw [ite_eq_left hc, ite_eq_left (by rw [← hl, ← ha]; exact hc)]
      exact flushTrail_sfr h
    · rw [ite_eq_right hc, ite_eq_right (by rw [← hl, ← ha]; exact hc)]; exact h
  | some c =>
    dsimp only
    have h1 : SFr (if cc then INC! x conflicts else x) (if cc' then INC! y conflicts else y) := by
      have hx : SFr (if cc then INC! x conflicts else x) x := by split <;> sf_rfl
      have hy : SFr (if cc' then INC! y conflicts else y) y := by split <;> sf_rfl
      exact hx.trans (h.trans hy.symm)
    generalize (if cc then INC! x conflicts else x) = x' at h1
    generalize (if cc' then INC! y conflicts else y) = y' at h1
    have hl' := h1.same.level
    by_cases hz : (x'.level == 0) = true
    · rw [ite_eq_left hz, ite_eq_left (by rw [← hl']; exact hz)]
      refine ⟨⟨h1.same.asg, h1.same.arena, h1.same.watches, h1.same.delayed, h1.same.vars, h1.same.level,
        h1.same.frameTrail, h1.same.propagate, h1.same.options⟩, h1.clause, ?_, h1.bits⟩
      have := h1.flg; simp only [Flg, Prod.mk.injEq] at this ⊢; exact ⟨this.1, trivial, this.2.2⟩
    · rw [ite_eq_right hz, ite_eq_right (by rw [← hl']; exact hz)]; exact h1

theorem uct_c01 (x : Solver) (c : Option CRef) (f cc : Bool) :
    (x.updateConflictsAndTrail c f cc).conflictLit0 = x.conflictLit0 ∧
    (x.updateConflictsAndTrail c f cc).conflictLit1 = x.conflictLit1 := by
  unfold updateConflictsAndTrail; cases c <;> dsimp only <;> repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- Probing propagation (no ignored clause, flushing) agrees with search propagation up to
  statistics. -/
theorem probingPropagate_sf (s : Solver) :
    (s.probingPropagate none true).2 = s.searchPropagate.2 ∧
    SFr (s.probingPropagate none true).1 s.searchPropagate.1 ∧
    (s.probingPropagate none true).1.conflictLit0 = s.searchPropagate.1.conflictLit0 ∧
    (s.probingPropagate none true).1.conflictLit1 = s.searchPropagate.1.conflictLit1 := by
  unfold probingPropagate searchPropagate
  dsimp only
  rw [propagateTrailLoop_none]
  generalize searchPropagateLoop s.vars.toNat { s with ticks := 0 } s.propagate = R
  obtain ⟨t, c, i⟩ := R
  dsimp only
  have hr : ∀ (b : Bool) (u : Solver), SFr u (if b then { u with randec := u.randec - 1 } else u) := by
    intro b u; split <;> sf_rfl
  have hr0 : ∀ (b : Bool) (u : Solver), (if b then { u with randec := u.randec - 1 } else u).conflictLit0 =
      u.conflictLit0 ∧ (if b then { u with randec := u.randec - 1 } else u).conflictLit1 = u.conflictLit1 := by
    intro b u; split <;> exact ⟨rfl, rfl⟩
  refine ⟨rfl, (uct_sfr ?_ c true false true).trans (hr _ _), ?_, ?_⟩
  · sf_rfl
  · rw [(hr0 _ _).1, (uct_c01 _ _ _ _).1, (uct_c01 _ _ _ _).1]; rfl
  · rw [(hr0 _ _).2, (uct_c01 _ _ _ _).2, (uct_c01 _ _ _ _).2]; rfl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem SFr.astepPre {Φ : (Nat → Bool) → Prop} {s t : Solver} {c : CRef} (h : AStepPre Φ s c) (hq : SFr t s)
    (hc01 : t.conflictLit0 = s.conflictLit0 ∧ t.conflictLit1 = s.conflictLit1) : AStepPre Φ t c := by
  have hS := hq.same
  have hopt : t.options = s.options := hS.options
  have hw : t.watching = s.watching := Flg.watching hq.flg
  have hcp := h.cpre
  have hconf : ConflictOK t t c := by
    cases c with
    | binConflict =>
      obtain ⟨hb, h0, h1⟩ := hcp.conflict
      refine ⟨?_, ?_, ?_⟩
      · rw [hc01.1, hc01.2]; unfold BinWatched entries watchesOf at *; rw [hS.watches]; exact hb
      · rw [hc01.1]; unfold IsFalse at *; rw [hS.asg]; exact h0
      · rw [hc01.2]; unfold IsFalse at *; rw [hS.asg]; exact h1
    | large r =>
      obtain ⟨hl, hf⟩ := hcp.conflict
      refine ⟨by unfold LiveRef refsL at *; rw [hS.arena]; exact hl, fun x hx => ?_⟩
      rw [clauseL_eq_litsL, hS.arena] at hx
      have := hf x hx; unfold IsFalse at *; rw [hS.asg]; exact this
  refine ⟨⟨hS.sinv hcp.inv, hconf, fun d hd => ?_, ?_, by rw [hS.level]; exact hcp.levelLt, by rw [hw]; exact hcp.watching⟩,
    fun i b hb => by unfold abit abits; rw [hq.bits]; exact h.clean i b hb, by rw [hq.clause]; exact h.clauseEmpty,
    by rw [hopt]; exact h.otfs, by rw [hopt]; exact h.eager, by rw [hopt]; exact h.bumpreasons⟩
  · rw [invSAt_congr hS.asg hS.frameTrail, hS.propagate]; exact hcp.invP d ((hS.inDB d).mp hd)
  · rw [show t.framesL = s.framesL by unfold framesL; rw [hS.frameTrail], hS.propagate]; exact hcp.framesLe

theorem probingProp_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s) :
    IrrMono s (s.probingPropagate none true).1 ∧
    ((s.probingPropagate none true).2 = none → SearchInv Φ (s.probingPropagate none true).1 ∧
      (s.probingPropagate none true).1.propagate = (s.probingPropagate none true).1.trailL.length) ∧
    (∀ c, (s.probingPropagate none true).2 = some c → AStepPre Φ (s.probingPropagate none true).1 c ∧
      ((s.probingPropagate none true).1.inconsistent = true → ¬ ∃ β, Φ β) ∧
      PlainOpts (s.probingPropagate none true).1.options ∧ ImportOK (s.probingPropagate none true).1) := by
  obtain ⟨e1, e2, e3, e4⟩ := probingPropagate_sf s
  obtain ⟨m, hn, hc⟩ := searchProp_spec h
  rw [e1]
  refine ⟨m.trans e2.irrMono, fun hr => ?_, fun c hr => ?_⟩
  · obtain ⟨a, b⟩ := hn hr
    exact ⟨e2.searchInv a, by rw [e2.same.propagate, b]; simp [trailL, e2.same.asg]⟩
  · obtain ⟨a, b, d, i⟩ := hc c hr
    exact ⟨e2.astepPre a ⟨e3, e4⟩, fun e => b (by rw [← Flg.inconsistent e2.flg]; exact e),
      by rw [e2.same.options]; exact d, i.flg e2.flg⟩

end Solver
end LeanKissat
