import LeanKissat.Proofs.Lucky

/-!
# `kissat_search`: lucky phases, search initialization, the search loop
-/

namespace LeanKissat
namespace Solver

theorem conflictsPlus_sf (s : Solver) (d : UInt64) : SFr (s.conflictsPlus d).2 s := by sf_fields

theorem initConflictLimit_sf (s : Solver) (n : Nat) (b : Bool) : SFr (s.initConflictLimit n b).2 s := by
  unfold initConflictLimit; exact conflictsPlus_sf _ _

theorem initModeLimit_sf (s : Solver) : SFr s.initModeLimit s := by
  unfold initModeLimit; split
  · dsimp only; sf_fields
  · exact SFr.refl _

theorem initLimitWith_sf (s : Solver) (e : Bool) (n : Nat) (b : Bool) (set : UInt64 → Solver → Solver)
    (hset : ∀ l u, SFr (set l u) u) : SFr (s.initLimitWith e n b set) s := by
  unfold initLimitWith; split
  · exact (hset _ _).trans (initConflictLimit_sf _ _ _)
  · exact SFr.refl _

theorem ite_sf (c : Bool) (f : Solver → Solver) (hf : ∀ u, SFr (f u) u) (u : Solver) :
    SFr (if c then f u else u) u := by
  split
  · exact hf u
  · exact SFr.refl _

theorem initLimits_sf (s : Solver) : SFr s.initLimits s := by
  unfold initLimits
  dsimp only
  refine (initLimitWith_sf _ _ _ _ _ (fun _ _ => by sf_rfl)).trans ?_
  refine (initLimitWith_sf _ _ _ _ _ (fun _ _ => by sf_rfl)).trans ?_
  refine (initModeLimit_sf _).trans ?_
  refine (ite_sf _ _ updateFocusedRestartLimit_sf _).trans ?_
  refine (initLimitWith_sf _ _ _ _ _ (fun _ _ => by sf_rfl)).trans ?_
  refine (initLimitWith_sf _ _ _ _ _ (fun _ _ => by sf_rfl)).trans ?_
  refine (initLimitWith_sf _ _ _ _ _ (fun _ _ => by sf_rfl)).trans ?_
  refine (initLimitWith_sf _ _ _ _ _ (fun _ _ => by sf_rfl)).trans ?_
  unfold initEnabled; sf_rfl

theorem classify_sf (s : Solver) : SFr s.classify s := by
  unfold classify; dsimp only; split <;> sf_rfl

theorem updateScoresLoop_sf (n : Nat) : ∀ (s : Solver) (i : Nat), SFr (updateScoresLoop n s i) s := by
  intro s i
  fun_induction updateScoresLoop n s i with
  | case1 s i hi idx s' ih =>
    exact ih.trans (by simp only [s']; split <;> sf_rfl)
  | case2 s i hi => exact SFr.refl _

theorem initTier_sf (s : Solver) (st : Nat) : SFr (s.initTier st) s := by
  unfold initTier; split
  · dsimp only; split <;> sf_rfl
  · exact SFr.refl _

theorem setSeed_sf (u : Solver) : SFr u.setSeed u := by unfold setSeed; sf_rfl
theorem initAverages_sf (u : Solver) : SFr u.initAverages u := by unfold initAverages; sf_rfl
theorem searchesInc_sf (u : Solver) : SFr u.searchesInc u := by unfold searchesInc; sf_rfl
theorem initReluctant_sf (u : Solver) : SFr u.initReluctant u := by unfold initReluctant; sf_rfl
theorem stableInit_sf (u : Solver) : SFr u.stableInit u := by
  unfold stableInit; split
  · exact (updateScoresLoop_sf _ _ _).trans (initReluctant_sf u)
  · exact SFr.refl _
theorem initTiers_sf (u : Solver) : SFr u.initTiers u := (initTier_sf _ _).trans (initTier_sf _ _)

theorem startSearch_sf (s : Solver) : SFr s.startSearch s := by
  unfold startSearch
  exact (setSeed_sf _).trans ((initLimits_sf _).trans ((initTiers_sf _).trans ((stableInit_sf _).trans
    ((classify_sf _).trans ((initAverages_sf _).trans (searchesInc_sf _))))))

theorem stopSearch_sf (s : Solver) : SFr s.stopSearch s := by unfold stopSearch; sf_rfl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The stop flags only become set. -/
def FlagM (t s : Solver) : Prop :=
  (s.overflowed = true → t.overflowed = true) ∧ t.outOfResources = s.outOfResources ∧ t.notPorted = s.notPorted

theorem FlagM.refl (s : Solver) : FlagM s s := ⟨id, rfl, rfl⟩
theorem FlagM.trans {a b c : Solver} (h1 : FlagM a b) (h2 : FlagM b c) : FlagM a c :=
  ⟨fun h => h1.1 (h2.1 h), h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
theorem FlagM.flagged {s t : Solver} (h : FlagM t s) (hf : Flagged s) : Flagged t := by
  rcases hf with e | e | e
  · exact Or.inl (h.1 e)
  · exact Or.inr (Or.inl (by rw [h.2.1]; exact e))
  · exact Or.inr (Or.inr (by rw [h.2.2]; exact e))

macro "fm_rfl" : tactic => `(tactic| exact ⟨id, rfl, rfl⟩)

theorem conflictsPlus_fm (s : Solver) (d : UInt64) : FlagM (s.conflictsPlus d).2 s := by
  unfold conflictsPlus; dsimp only; split
  · exact ⟨fun _ => rfl, rfl, rfl⟩
  · fm_rfl

theorem initLimitWith_fm (s : Solver) (e : Bool) (n : Nat) (b : Bool) (set : UInt64 → Solver → Solver)
    (hset : ∀ l u, FlagM (set l u) u) : FlagM (s.initLimitWith e n b set) s := by
  unfold initLimitWith; split
  · exact (hset _ _).trans (conflictsPlus_fm _ _)
  · exact FlagM.refl _

theorem updateFocusedRestartLimit_fm (s : Solver) : FlagM s.updateFocusedRestartLimit s := by
  unfold updateFocusedRestartLimit; dsimp only
  exact (show FlagM { (s.conflictsPlus _).2 with limits := _ } (s.conflictsPlus _).2 by fm_rfl).trans
    (conflictsPlus_fm _ _)

theorem initModeLimit_fm (s : Solver) : FlagM s.initModeLimit s := by
  unfold initModeLimit; split
  · dsimp only
    exact (show FlagM _ (s.conflictsPlus _).2 by fm_rfl).trans (conflictsPlus_fm _ _)
  · exact FlagM.refl _

theorem ite_fm (c : Bool) (f : Solver → Solver) (hf : ∀ u, FlagM (f u) u) (u : Solver) :
    FlagM (if c then f u else u) u := by
  split
  · exact hf u
  · exact FlagM.refl _

theorem initLimits_fm (s : Solver) : FlagM s.initLimits s := by
  unfold initLimits
  dsimp only
  refine (initLimitWith_fm _ _ _ _ _ (fun _ _ => by fm_rfl)).trans ?_
  refine (initLimitWith_fm _ _ _ _ _ (fun _ _ => by fm_rfl)).trans ?_
  refine (initModeLimit_fm _).trans ?_
  refine (ite_fm _ _ updateFocusedRestartLimit_fm _).trans ?_
  refine (initLimitWith_fm _ _ _ _ _ (fun _ _ => by fm_rfl)).trans ?_
  refine (initLimitWith_fm _ _ _ _ _ (fun _ _ => by fm_rfl)).trans ?_
  refine (initLimitWith_fm _ _ _ _ _ (fun _ _ => by fm_rfl)).trans ?_
  refine (initLimitWith_fm _ _ _ _ _ (fun _ _ => by fm_rfl)).trans ?_
  unfold initEnabled; fm_rfl

theorem updateScoresLoop_fm (n : Nat) : ∀ (s : Solver) (i : Nat), FlagM (updateScoresLoop n s i) s := by
  intro s i
  fun_induction updateScoresLoop n s i with
  | case1 s i hi idx s' ih => exact ih.trans (by simp only [s']; split <;> fm_rfl)
  | case2 s i hi => exact FlagM.refl _

theorem startSearch_fm (s : Solver) : FlagM s.startSearch s := by
  unfold startSearch
  have h1 : ∀ u : Solver, FlagM u.setSeed u := fun u => by unfold setSeed; fm_rfl
  have h2' : ∀ (u : Solver) (st : Nat), FlagM (u.initTier st) u := fun u st => by
    unfold initTier; split
    · dsimp only; split <;> fm_rfl
    · fm_rfl
  have h2 : ∀ u : Solver, FlagM u.initTiers u := fun u => (h2' _ _).trans (h2' _ _)
  have h3 : ∀ u : Solver, FlagM u.stableInit u := fun u => by
    unfold stableInit; split
    · exact (updateScoresLoop_fm _ _ _).trans (by unfold initReluctant; fm_rfl)
    · exact FlagM.refl _
  have h4 : ∀ u : Solver, FlagM u.classify u := fun u => by unfold classify; dsimp only; split <;> fm_rfl
  have h5 : ∀ u : Solver, FlagM u.initAverages u := fun u => by unfold initAverages; fm_rfl
  have h6 : ∀ u : Solver, FlagM u.searchesInc u := fun u => by unfold searchesInc; fm_rfl
  exact (h1 _).trans ((initLimits_fm _).trans ((h2 _).trans ((h3 _).trans ((h4 _).trans ((h5 _).trans (h6 _))))))

theorem classify_fm (u : Solver) : FlagM u.classify u := by unfold classify; dsimp only; split <;> fm_rfl

theorem lucky_flagged (u : Solver) (h : Flagged u) : u.lucky = (0, u) := by
  unfold lucky
  split
  · rfl
  · rw [ite_eq_left (by rcases h with e | e | e <;> simp [e])]

theorem SATState.sfr {Φ : (Nat → Bool) → Prop} {s0 t u : Solver} (h : SATState Φ s0 t) (hu : SFr u t) :
    SATState Φ s0 u :=
  ⟨hu.same.sinv h.inv, fun c hc => by unfold InvS; rw [hu.same.invSAt, hu.same.propagate]; exact h.invS c ((hu.same.inDB c).mp hc),
   by rw [hu.same.propagate, h.prop]; simp [trailL, hu.same.asg], by rw [hu.same.asg]; exact h.unassigned,
   h.mono.trans hu.irrMono, h.imp.flg hu.flg⟩

/-- The tail of `kissat_search` after the lucky and preprocessing phases. -/
theorem searchTail_spec {Φ : (Nat → Bool) → Prop} {P : Procedures} (hred : ReduceOK Φ P.reduce)
    (hprobe : ∀ s, (P.probe s).1 = 0 ∧ Flagged (P.probe s).2)
    (helim : ∀ s, (P.eliminate s).1 = 0 ∧ Flagged (P.eliminate s).2)
    {s0 t : Solver} (h : Flagged t ∨ (SearchInv Φ t ∧ IrrMono s0 t)) :
    let r := (let s := t.classify
      if s.searching then
        let s := s.startSearch
        match searchLoop P s (stepBound s) 0 with
        | (r, s') => (r, s'.stopSearch)
      else (0, s))
    (r.1 = 20 → ¬ ∃ β, Φ β) ∧ (r.1 = 10 → SATState Φ s0 r.2) := by
  intro r
  simp only [r]
  split
  · have hsf := (startSearch_sf t.classify).trans (classify_sf t)
    have hfm := (startSearch_fm t.classify).trans (classify_fm t)
    generalize t.classify.startSearch = u at hsf hfm
    rcases h with hf | ⟨h1, m⟩
    · rw [searchLoop_flagged P (hfm.flagged hf)]
      exact ⟨fun e => by simp at e, fun e => by simp at e⟩
    · have hu := hsf.searchInv h1
      obtain ⟨l1, l2⟩ := searchLoop_spec hred hprobe helim u (stepBound u) 0 hu
      generalize searchLoop P u (stepBound u) 0 = R at l1 l2
      obtain ⟨r1, v⟩ := R
      exact ⟨fun e => l1 e, fun e => ((l2 e).trans_left (m.trans hsf.irrMono)).sfr (stopSearch_sf v)⟩
  · exact ⟨fun e => by simp at e, fun e => by simp at e⟩

theorem kissatSearch_spec {Φ : (Nat → Bool) → Prop} {P : Procedures} (hred : ReduceOK Φ P.reduce)
    (hprobe : ∀ s, (P.probe s).1 = 0 ∧ Flagged (P.probe s).2)
    (helim : ∀ s, (P.eliminate s).1 = 0 ∧ Flagged (P.eliminate s).2)
    (hpre : ∀ s, (P.preprocess s).1 = 0 ∧ Flagged (P.preprocess s).2)
    {s : Solver} (h : SearchInv Φ s) :
    ((search P s).1 = 20 → ¬ ∃ β, Φ β) ∧ ((search P s).1 = 10 → SATState Φ s (search P s).2) := by
  unfold search
  by_cases hi : s.inconsistent = true
  · rw [ite_eq_left hi]; exact ⟨fun _ => h.incons hi, fun e => by simp at e⟩
  rw [ite_eq_right hi]
  have L1 : LuckyOut Φ s (if s.options.luckyearly != 0 then s.lucky else (0, s)) := by
    split
    · exact lucky_spec h
    · exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inr ⟨h, IrrMono.refl _⟩⟩
  generalize (if s.options.luckyearly != 0 then s.lucky else (0, s)) = R at L1
  obtain ⟨r1, s1⟩ := R
  obtain ⟨a1, a2, a3⟩ := L1
  dsimp only at a1 a2 a3 ⊢
  by_cases h1 : r1 ≠ 0
  · rw [ite_eq_left (by simpa using h1)]; exact ⟨a2, a1⟩
  have h1 : r1 = 0 := Decidable.not_not.mp h1
  rw [ite_eq_right (by simp [h1])]
  have G1 := a3 h1
  have L2 : (if s1.options.preprocess != 0 && s1.options.probe != 0 && s1.options.preprocessprobe != 0 then
      P.preprocess s1 else (0, s1)).1 = 0 ∧
      (Flagged (if s1.options.preprocess != 0 && s1.options.probe != 0 && s1.options.preprocessprobe != 0 then
        P.preprocess s1 else (0, s1)).2 ∨
      (SearchInv Φ (if s1.options.preprocess != 0 && s1.options.probe != 0 && s1.options.preprocessprobe != 0 then
        P.preprocess s1 else (0, s1)).2 ∧ IrrMono s (if s1.options.preprocess != 0 && s1.options.probe != 0 &&
        s1.options.preprocessprobe != 0 then P.preprocess s1 else (0, s1)).2)) := by
    split
    · exact ⟨(hpre s1).1, Or.inl (hpre s1).2⟩
    · exact ⟨rfl, G1⟩
  generalize (if s1.options.preprocess != 0 && s1.options.probe != 0 && s1.options.preprocessprobe != 0 then
      P.preprocess s1 else (0, s1)) = R at L2
  obtain ⟨r2, s2⟩ := R
  obtain ⟨b1, G2⟩ := L2
  dsimp only at b1 G2 ⊢
  rw [ite_eq_right (by simp [b1])]
  have L3 : LuckyOut Φ s (if s2.options.luckylate != 0 then s2.lucky else (0, s2)) := by
    rcases G2 with hf | ⟨g1, g2⟩
    · have : (if s2.options.luckylate != 0 then s2.lucky else (0, s2)) = (0, s2) := by
        split
        · exact lucky_flagged s2 hf
        · rfl
      rw [this]; exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inl hf⟩
    · split
      · obtain ⟨c1, c2, c3⟩ := lucky_spec g1
        refine ⟨fun e => (c1 e).trans_left g2, c2, fun e => ?_⟩
        rcases c3 e with hf | ⟨x, y⟩
        · exact Or.inl hf
        · exact Or.inr ⟨x, g2.trans y⟩
      · exact ⟨fun e => by simp at e, fun e => by simp at e, fun _ => Or.inr ⟨g1, g2⟩⟩
  generalize (if s2.options.luckylate != 0 then s2.lucky else (0, s2)) = R at L3
  obtain ⟨r3, s3⟩ := R
  obtain ⟨c1, c2, c3⟩ := L3
  dsimp only at c1 c2 c3 ⊢
  by_cases h3 : r3 ≠ 0
  · rw [ite_eq_left (by simpa using h3)]; exact ⟨c2, c1⟩
  have h3 : r3 = 0 := Decidable.not_not.mp h3
  rw [ite_eq_right (by simp [h3])]
  exact searchTail_spec hred hprobe helim (c3 h3)

end Solver
end LeanKissat
