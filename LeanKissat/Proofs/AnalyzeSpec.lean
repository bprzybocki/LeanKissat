import LeanKissat.Proofs.Analysis
import LeanKissat.Proofs.FailedLit

/-!
# Conflict analysis (`analyze`)
-/

namespace LeanKissat
namespace Solver
open Arena

/-- `clearBitsUp` for any analysis bit: frame and cleared bits. -/
theorem clearBitsUp_gen (v : U32Vec) (b : UInt8) (hb : AnaBit b) (n : Nat) :
    ∀ (s : Solver) (k : Nat),
    AF (s.clearBitsUp v b k n) s ∧ anaSide (s.clearBitsUp v b k n) = anaSide s ∧
    (∀ i, (s.clearBitsUp v b k n).abit i b = true → s.abit i b = true ∧ ∀ j, k ≤ j → j < n → v.get! j ≠ i) ∧
    (∀ i c, c ≠ b → AnaBit c → (s.clearBitsUp v b k n).abit i c = s.abit i c) := by
  have hbin : b &&& ABits.binary = 0 := by rcases hb with rfl | rfl | rfl | rfl <;> decide
  intro s k
  fun_induction clearBitsUp s v b k n with
  | case1 s k hk ih =>
    have f := setABit_af s (v.get! k) b false hbin
    obtain ⟨a1, a2, a3, a4⟩ := ih
    by_cases hsz : (v.get! k).toNat < s.asg.aBits.size
    · have hab : ∀ i c, AnaBit c → (s.setABit (v.get! k) b false).abit i c =
          if v.get! k = i ∧ b = c then false else s.abit i c :=
        fun i c hc => setABit_abit' s _ i b c false hsz hb hc
      refine ⟨a1.trans f, by rw [a2]; rfl, fun i hi => ?_, fun i c hc hc' => ?_⟩
      · obtain ⟨h1, h2⟩ := a3 i hi
        rw [hab i _ hb] at h1
        by_cases e : v.get! k = i
        · simp [e] at h1
        · simp [e] at h1
          refine ⟨h1, fun j hj1 hj2 => ?_⟩
          by_cases ej : j = k
          · subst ej; exact e
          · exact h2 j (by omega) hj2
      · rw [a4 i c hc hc', hab i c hc']
        simp [Ne.symm hc]
    · have hsame : ∀ i c, (s.setABit (v.get! k) b false).abit i c = s.abit i c := by
        intro i c
        unfold abit abits
        rw [setABit_bits]
        congr 1
        rw [ite_eq_right (fun h => hsz h.2)]
      refine ⟨a1.trans f, by rw [a2]; rfl, fun i hi => ?_, fun i c hc hc' => by rw [a4 i c hc hc', hsame]⟩
      obtain ⟨h1, h2⟩ := a3 i hi
      rw [hsame] at h1
      refine ⟨h1, fun j hj1 hj2 => ?_⟩
      by_cases ej : j = k
      · subst ej
        intro e
        apply hsz
        have : s.abit i b = true := h1
        unfold abit abits at this
        rw [e]
        apply Classical.byContradiction
        intro hn
        rw [ByteArray.get!_oob _ _ hn] at this
        simp at this
      · exact h2 j (by omega) hj2
  | case2 s k hk =>
    exact ⟨AF.refl _, rfl, fun i hi => ⟨hi, fun j hj1 hj2 => absurd hj2 (by omega)⟩, fun _ _ _ _ => rfl⟩

/-- Resetting an analysis bit through a stack recording all its variables clears it. -/
theorem clearByList (s : Solver) (v : U32Vec) (b : UInt8) (hb : AnaBit b)
    (hv : ∀ i, s.abit i b = true → i ∈ v.view) :
    AF (s.clearBitsUp v b 0 v.size) s ∧ anaSide (s.clearBitsUp v b 0 v.size) = anaSide s ∧
    (∀ i, (s.clearBitsUp v b 0 v.size).abit i b = false) ∧
    (∀ i c, c ≠ b → AnaBit c → (s.clearBitsUp v b 0 v.size).abit i c = s.abit i c) := by
  obtain ⟨a1, a2, a3, a4⟩ := clearBitsUp_gen v b hb v.size s 0
  refine ⟨a1, a2, fun i => ?_, a4⟩
  cases e : (s.clearBitsUp v b 0 v.size).abit i b
  · rfl
  · exfalso
    obtain ⟨h1, h2⟩ := a3 i e
    obtain ⟨j, hj, hji⟩ := U32Vec.mem_view_pos _ _ (hv i h1)
    exact h2 j (Nat.zero_le _) hj hji

theorem resetOnlyAnalyzed_spec (s : Solver) (hl : Listed s) :
    AF s.resetOnlyAnalyzedLiterals s ∧ (∀ i, s.resetOnlyAnalyzedLiterals.isAnalyzed i = false) ∧
    (∀ i c, c ≠ ABits.analyzed → AnaBit c → s.resetOnlyAnalyzedLiterals.abit i c = s.abit i c) ∧
    s.resetOnlyAnalyzedLiterals.clause = s.clause := by
  obtain ⟨a1, a2, a3, a4⟩ := clearByList s s.analyzed ABits.analyzed anaBit_analyzed
    (fun i hi => by have := hl _ anaBit_analyzed i hi; simpa [anaList] using this)
  have hcl : (s.clearBitsUp s.analyzed ABits.analyzed 0 s.analyzed.size).clause = s.clause := by
    have := a2; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  exact ⟨AF.trans_left a1 af_rfl, a3, a4, hcl⟩

theorem resetRemovable_spec (s : Solver) (hl : Listed s) :
    AF s.resetRemovable s ∧ (∀ i, s.resetRemovable.isRem i = false) ∧
    (∀ i c, c ≠ ABits.removable → AnaBit c → s.resetRemovable.abit i c = s.abit i c) ∧
    s.resetRemovable.clause = s.clause ∧ s.resetRemovable.analyzed = s.analyzed ∧
    s.resetRemovable.poisoned = s.poisoned ∧ s.resetRemovable.shrinkable = s.shrinkable ∧
    s.resetRemovable.levels = s.levels := by
  obtain ⟨a1, a2, a3, a4⟩ := clearByList s s.removable ABits.removable anaBit_removable
    (fun i hi => by
      have := hl _ anaBit_removable i hi
      simpa [anaList, show ABits.removable ≠ ABits.analyzed by decide, show ABits.removable ≠ ABits.poisoned by decide]
        using this)
  have := a2; simp only [anaSide, Prod.mk.injEq] at this
  exact ⟨AF.trans_left a1 af_rfl, a3, a4, this.1, this.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.2.1⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem bumpAnalyzed_cases (s : Solver) :
    (∃ q, s.bumpAnalyzed = { s with queue := q }) ∨ (∃ h f, s.bumpAnalyzed = { s with scores := h, scinc := f }) := by
  unfold bumpAnalyzed
  split
  · left; exact ⟨_, rfl⟩
  · right; exact ⟨_, _, rfl⟩

theorem bumpAnalyzed_frame (s : Solver) :
    AF s.bumpAnalyzed s ∧ anaSide s.bumpAnalyzed = anaSide s ∧ (∀ i b, s.bumpAnalyzed.abit i b = s.abit i b) ∧
    Same s.bumpAnalyzed s := by
  rcases bumpAnalyzed_cases s with ⟨q, e⟩ | ⟨h, f, e⟩
  · rw [e]; exact ⟨af_rfl, rfl, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · rw [e]; exact ⟨af_rfl, rfl, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem finishAnalysis_spec (s : Solver) (hl : Listed s) :
    AF s.finishAnalysis s ∧ (∀ i, s.finishAnalysis.isAnalyzed i = false) ∧
    (∀ i c, c ≠ ABits.analyzed → AnaBit c → s.finishAnalysis.abit i c = s.abit i c) ∧
    s.finishAnalysis.clause = s.clause ∧ (anaSide s.finishAnalysis).2.2 = (anaSide s).2.2 ∧
    s.finishAnalysis.propagate = s.propagate := by
  unfold finishAnalysis
  split
  · have hq : AF (if (!s.probing && s.options.bump != 0) = true then s.bumpAnalyzed else s) s ∧
        anaSide (if (!s.probing && s.options.bump != 0) = true then s.bumpAnalyzed else s) = anaSide s ∧
        (∀ i b, (if (!s.probing && s.options.bump != 0) = true then s.bumpAnalyzed else s).abit i b = s.abit i b) := by
      split
      · obtain ⟨a, b, c, _⟩ := bumpAnalyzed_frame s; exact ⟨a, b, c⟩
      · exact ⟨AF.refl _, rfl, fun _ _ => rfl⟩
    obtain ⟨q1, q2, q3⟩ := hq
    generalize (if (!s.probing && s.options.bump != 0) = true then s.bumpAnalyzed else s) = s1 at q1 q2 q3
    have hl1 : Listed s1 := Listed.of_le hl (fun i b _ h => by rw [← q3]; exact h) (by unfold anaRest; rw [q2])
    obtain ⟨r1, r2, r3, r4⟩ := resetOnlyAnalyzed_spec s1 hl1
    have hcl1 : s1.clause = s.clause := by have := q2; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
    refine ⟨r1.trans q1, r2, fun i c hc hc' => by rw [r3 i c hc hc', q3], by rw [r4, hcl1], ?_, by
      rw [r1.propagate, q1.propagate]⟩
    have e : (anaSide s1.resetOnlyAnalyzedLiterals).2.2 = (anaSide s1).2.2 := by
      have := (clearBitsUp_gen s1.analyzed ABits.analyzed anaBit_analyzed s1.analyzed.size s1 0).2.1
      show (anaSide (s1.clearBitsUp s1.analyzed ABits.analyzed 0 s1.analyzed.size)).2.2 = _
      rw [this]
    rw [e, q2]
  · rename_i h0
    have hsz : s.analyzed.size = 0 := by simpa using h0
    refine ⟨AF.refl _, fun i => ?_, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    cases e : s.isAnalyzed i
    · rfl
    · exfalso
      have := hl _ anaBit_analyzed i e
      simp [anaList] at this
      have hv : s.analyzed.view = [] := List.eq_nil_of_length_eq_zero (by simp [hsz])
      rw [hv] at this; simp at this

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem analyzeReasonSideLiterals_off (s : Solver) (h : s.options.bumpreasons = 0) :
    s.analyzeReasonSideLiterals = s := by
  unfold analyzeReasonSideLiterals
  rw [ite_eq_left (by simp [h])]

/-- The analysis result (unless flagged): invariants, clean bookkeeping except `analyzed` marks. -/
structure AOut (Φ : (Nat → Bool) → Prop) (s0 t : Solver) : Prop where
  inv : SInv Φ t
  invS : ∀ c, t.InDB c → t.InvS c
  listed : Listed t
  others : ∀ i b, (b = ABits.poisoned ∨ b = ABits.removable ∨ b = ABits.shrinkable) → t.abit i b = false
  clauseEmpty : t.clause.size = 0
  incons : Flg t = Flg s0
  mono : IrrMono s0 t

/-- Resetting after learning. -/
theorem resetAnalysis_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) (hinv : ∀ c, s.InDB c → s.InvS c)
    (hl : Listed s) (hother : ∀ i b, (b = ABits.poisoned ∨ b = ABits.shrinkable) → s.abit i b = false) :
    AOut Φ s s.resetAnalysisButNotAnalyzedLiterals ∧
    (∀ i, s.resetAnalysisButNotAnalyzedLiterals.isAnalyzed i = s.isAnalyzed i) ∧
    s.resetAnalysisButNotAnalyzedLiterals.analyzed = s.analyzed ∧
    AF s.resetAnalysisButNotAnalyzedLiterals s := by
  obtain ⟨r1, r2, r3, _, r5, r6, r7, _⟩ := resetRemovable_spec s hl
  unfold resetAnalysisButNotAnalyzedLiterals
  generalize s.resetRemovable = s1 at r1 r2 r3 r5 r6 r7
  have e : AF ({ s1.resetLevels with clause := s1.resetLevels.clause.clear } : Solver) s1 := by
    unfold resetLevels; exact af_rfl
  have hab : ∀ i b, ({ s1.resetLevels with clause := s1.resetLevels.clause.clear } : Solver).abit i b = s1.abit i b := by
    intro i b; unfold resetLevels; rfl
  have hana2 : ({ s1.resetLevels with clause := s1.resetLevels.clause.clear } : Solver).analyzed = s1.analyzed := by
    unfold resetLevels; rfl
  have hcl2 : ({ s1.resetLevels with clause := s1.resetLevels.clause.clear } : Solver).clause.size = 0 := by
    unfold resetLevels; simp [U32Vec.clear, U32Vec.size_shrink]
  generalize ({ s1.resetLevels with clause := s1.resetLevels.clause.clear } : Solver) = s2 at e hab hana2 hcl2
  have hAF : AF s2 s := e.trans r1
  have hbit : ∀ i b, AnaBit b → b ≠ ABits.removable → s2.abit i b = s.abit i b := by
    intro i b hb hne; rw [hab, r3 i b hne hb]
  have hrem : ∀ i, s2.abit i ABits.removable = false := by intro i; rw [hab]; exact r2 i
  refine ⟨⟨hAF.sinv hs, fun c hc => ?_, ?_, fun i b hb' => ?_, hcl2, hAF.flg, hAF.irrMono⟩, fun i => hbit i _ anaBit_analyzed (by decide),
    by rw [hana2, r5], hAF⟩
  · unfold InvS; rw [hAF.invSAt, hAF.propagate]; exact hinv c ((hAF.inDB c).mp hc)
  · intro b hb i hi
    rcases hb with rfl | rfl | rfl | rfl
    · rw [hbit i _ anaBit_analyzed (by decide)] at hi
      have := hl _ anaBit_analyzed i hi
      simpa [anaList, hana2, r5] using this
    · rw [hbit i _ anaBit_poisoned (by decide), hother i _ (Or.inl rfl)] at hi; exact absurd hi (by simp)
    · rw [hrem] at hi; exact absurd hi (by simp)
    · rw [hbit i _ anaBit_shrinkable (by decide), hother i _ (Or.inr rfl)] at hi; exact absurd hi (by simp)
  · rcases hb' with rfl | rfl | rfl
    · rw [hbit i _ anaBit_poisoned (by decide)]; exact hother i _ (Or.inl rfl)
    · exact hrem i
    · rw [hbit i _ anaBit_shrinkable (by decide)]; exact hother i _ (Or.inr rfl)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem resetAnalysis_flags (s : Solver) :
    s.resetAnalysisButNotAnalyzedLiterals.overflowed = s.overflowed ∧
    s.resetAnalysisButNotAnalyzedLiterals.outOfResources = s.outOfResources := by
  have := (clearBitsUp_gen s.removable ABits.removable anaBit_removable s.removable.size s 0).2.1
  simp only [anaSide, Prod.mk.injEq] at this
  unfold resetAnalysisButNotAnalyzedLiterals resetRemovable resetLevels
  exact ⟨this.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem learnDeduced_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} {L : Nat} (hA : APre Φ s0 c L)
    (hP : ∀ d, s0.InDB d → s0.InvSAt (s0.framesL[L - 1]!) d) (hw : s0.watching = true)
    (hes : s0.options.eagersubsume = 0) (hbr : s0.options.bumpreasons = 0) :
    (s0.deduceFirstUipClause c).2.learnDeduced.overflowed = true ∨
    (s0.deduceFirstUipClause c).2.learnDeduced.outOfResources = true ∨
    AOut Φ s0 (s0.deduceFirstUipClause c).2.learnDeduced := by
  have hb := hA.base
  obtain ⟨_, hd⟩ := deduceFirstUip_spec hA
  generalize (s0.deduceFirstUipClause c).2 = s1 at hd ⊢
  unfold learnDeduced
  split
  · left; assumption
  rename_i hov1
  rcases hd with h' | ⟨hDF, hder⟩
  · exact absurd h' hov1
  have MV := minimizeDeduced_spec hb hDF
  dsimp only
  generalize s1.minimizeDeduced = s2 at MV ⊢
  split
  · left; assumption
  rename_i hov2
  rcases MV with h' | M
  · exact absurd h' hov2
  rw [analyzeReasonSideLiterals_off s2 (by rw [M.af.options]; exact hbr)]
  have hlev : s2.level.toNat = L := by rw [M.af.level, hb.level]
  have hs2 : SInv Φ s2 := M.af.sinv hb.inv
  have hfr2 : s2.framesL = s0.framesL := by unfold framesL; rw [M.af.frameTrail]
  have hfl := framesL_last hs2 hlev hb.pos
  have hLP : LPre Φ s2 (s2.framesL[L - 1]'(by rw [hs2.levelOK.len, hlev]; have := hb.pos; omega)) := by
    refine ⟨hs2, by rw [M.af.watching]; exact hw, ?_, fun d hd' => ?_, hfl.2, ?_, fun y hy => ?_⟩
    · intro e; rw [e] at hlev; have := hb.pos; simp at hlev; omega
    · rw [← hfl.1, hfr2, M.af.invSAt]; exact hP d ((M.af.inDB d).mp hd')
    · apply implied_of_derFalse hb.inv.db hb.inv.roots hb.inv.core.valCons hb.inv.core.lvlVar (hA.conflict.implied hb.inv)
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact DerFalse.trans M.der (hder k hk)
    · have := (M.lits y hy).1
      have hv := hb.valid_false this
      unfold ValidLit at *; rw [M.af.vars]; exact hv
  have hLR := learnClause_spec hLP (by rw [M.af.options]; exact hes)
  generalize s2.learnClause = s3 at hLR ⊢
  have hfl3 := resetAnalysis_flags s3
  rcases hLR with h' | h' | lo
  · left; rw [hfl3.1]; exact h'
  · right; left; rw [hfl3.2]; exact h'
  · right; right
    have hl3 : Listed s3 := M.listed.of_le lo.bits lo.rest
    have hoth : ∀ i b, (b = ABits.poisoned ∨ b = ABits.shrinkable) → s3.abit i b = false := by
      intro i b hb'
      cases e : s3.abit i b
      · rfl
      · exfalso
        have := lo.bits i b (by rcases hb' with rfl | rfl <;> simp [AnaBit]) e
        rcases hb' with rfl | rfl
        · rw [M.noPoison] at this; exact absurd this (by simp)
        · have h2 := M.noSh i; unfold isSh at h2; rw [h2] at this; exact absurd this (by simp)
    have r := (resetAnalysis_spec lo.inv lo.invS hl3 hoth).1
    have hinc3 : Flg s3 = Flg s0 := (flg_of_anaRest lo.rest).trans M.af.flg
    exact ⟨r.inv, r.invS, r.listed, r.others, r.clauseEmpty, r.incons.trans hinc3,
      (M.af.irrMono.trans lo.mono).trans r.mono⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- Preconditions of an analysis step at a conflict. -/
structure AStepPre (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) : Prop where
  cpre : CPre Φ s c
  clean : ∀ i b, AnaBit b → s.abit i b = false
  clauseEmpty : s.clause.size = 0
  otfs : s.options.otfs = 0
  eager : s.options.eagersubsume = 0
  bumpreasons : s.options.bumpreasons = 0

/-- The search invariants after a successful analysis. -/
structure CleanOut (Φ : (Nat → Bool) → Prop) (s0 t : Solver) : Prop where
  inv : SInv Φ t
  invS : ∀ c, t.InDB c → t.InvS c
  clean : ∀ i b, AnaBit b → t.abit i b = false
  clauseEmpty : t.clause.size = 0
  incons : Flg t = Flg s0
  mono : IrrMono s0 t

theorem finish_flags (s : Solver) :
    s.finishAnalysis.overflowed = s.overflowed ∧ s.finishAnalysis.outOfResources = s.outOfResources := by
  have key : ∀ t : Solver, (anaSide t).2.2 = (anaSide s).2.2 →
      t.overflowed = s.overflowed ∧ t.outOfResources = s.outOfResources := by
    intro t ht; simp only [anaSide, Prod.mk.injEq] at ht
    exact ⟨ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.2.2.1⟩
  apply key
  unfold finishAnalysis
  split
  · have hq : anaSide (if (!s.probing && s.options.bump != 0) = true then s.bumpAnalyzed else s) = anaSide s := by
      split
      · exact (bumpAnalyzed_frame s).2.1
      · rfl
    generalize (if (!s.probing && s.options.bump != 0) = true then s.bumpAnalyzed else s) = s1 at hq
    have := (clearBitsUp_gen s1.analyzed ABits.analyzed anaBit_analyzed s1.analyzed.size s1 0).2.1
    show (anaSide (s1.clearBitsUp s1.analyzed ABits.analyzed 0 s1.analyzed.size)).2.2 = _
    rw [this, hq]
  · rfl

theorem listed_of_clean {s : Solver} (h : ∀ i b, AnaBit b → s.abit i b = false) : Listed s := by
  intro b hb i hi; rw [h i b hb] at hi; exact absurd hi (by simp)

/-- The finishing step turns an analysis result into a clean state. -/
theorem finish_clean {Φ : (Nat → Bool) → Prop} {s0 t : Solver} (h : AOut Φ s0 t) : CleanOut Φ s0 t.finishAnalysis := by
  obtain ⟨f1, f2, f3, f4, _, f6⟩ := finishAnalysis_spec t h.listed
  refine ⟨f1.sinv h.inv, fun c hc => ?_, fun i b hb => ?_, by rw [f4]; exact h.clauseEmpty,
    f1.flg.trans h.incons, h.mono.trans f1.irrMono⟩
  · unfold InvS; rw [f1.invSAt, f6]; exact h.invS c ((f1.inDB c).mp hc)
  · by_cases e : b = ABits.analyzed
    · subst e; exact f2 i
    · rw [f3 i b e hb]
      rcases hb with rfl | rfl | rfl | rfl
      · exact absurd rfl e
      · exact h.others i _ (Or.inl rfl)
      · exact h.others i _ (Or.inr (Or.inl rfl))
      · exact h.others i _ (Or.inr (Or.inr rfl))

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The outcome of an analysis step. -/
def AStepOut (Φ : (Nat → Bool) → Prop) (s : Solver) (r : (Int ⊕ CRef) × Solver) : Prop :=
  (r.1 = .inl (-1) → ¬ ∃ β, Φ β) ∧ (r.1 = .inl 1 ∨ r.1 = .inl (-1)) ∧
  (r.1 ≠ .inl (-1) → r.2.overflowed = true ∨ r.2.outOfResources = true ∨ CleanOut Φ s r.2)

theorem analyzeStep_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (h : AStepPre Φ s c) :
    AStepOut Φ s (s.analyzeStep c) := by
  have hco := oneLiteralOnConflictLevel_spec h.cpre
  unfold analyzeStep
  generalize s.oneLiteralOnConflictLevel c = R at hco ⊢
  obtain ⟨forced, cl, s1⟩ := R
  dsimp only at hco ⊢
  split
  · -- forced (or flagged)
    rename_i hf
    refine ⟨fun e => by simp at e, Or.inl rfl, fun _ => ?_⟩
    rcases hco with ⟨h1, _⟩ | ⟨_, hov⟩ | ⟨_, lo, hcl⟩ | ⟨h1, _⟩
    · have : forced = false := h1; rw [this] at hf; exact absurd hf (by simp)
    · left; rw [(finish_flags s1).1]; exact hov
    · right; right
      have hcl1 : ∀ i b, AnaBit b → s1.abit i b = false := by
        intro i b hb; cases e : s1.abit i b
        · rfl
        · have := lo.bits i b hb e; rw [h.clean i b hb] at this; exact absurd this (by simp)
      have hinc : Flg s1 = Flg s := flg_of_anaRest lo.rest
      exact finish_clean ⟨lo.inv, lo.invS, listed_of_clean hcl1, fun i b hb => hcl1 i b
        (by rcases hb with rfl | rfl | rfl <;> simp [AnaBit]), by rw [hcl]; exact h.clauseEmpty, hinc, lo.mono⟩
    · have : forced = false := h1; rw [this] at hf; exact absurd hf (by simp)
  rename_i hf
  have hff : forced = false := by simpa using hf
  -- the analysis precondition on the conflict level
  have hAP : 0 < cl.toNat → APost Φ s c s1 cl := by
    intro hpos
    rcases hco with ⟨_, h0, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, hap⟩
    · have : cl = 0 := h0; rw [this] at hpos; simp at hpos
    · have : forced = true := h1; rw [hff] at this; exact absurd this (by simp)
    · have : forced = true := h1; rw [hff] at this; exact absurd this (by simp)
    · exact hap
  split
  · -- conflict on the root level
    rename_i h0
    have h0' : cl = 0 := by simpa using h0
    refine ⟨fun _ => ?_, Or.inr rfl, fun e => absurd rfl e⟩
    rcases hco with ⟨_, _, _, hu⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, hpos, _⟩
    · exact hu
    · have : forced = true := h1; rw [hff] at this; exact absurd this (by simp)
    · have : forced = true := h1; rw [hff] at this; exact absurd this (by simp)
    · have e1 : cl.toNat = 0 := by rw [h0']; rfl
      have e2 : (forced, cl, s1).2.1.toNat = cl.toNat := rfl
      omega
  rename_i h0
  have hpos : 0 < cl.toNat := by
    have : cl ≠ 0 := by simpa using h0
    have : cl.toNat ≠ 0 := fun e => this (UInt32.toNat_inj.mp (by simpa using e))
    omega
  have hap := hAP hpos
  have hcl1 : s1.clause = s.clause := by have := hap.ana; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  have hopt1 : s1.options = s.options := by
    have := hap.ana; simp only [anaSide, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.1
  have hw1 : s1.watching = s.watching := by
    have := hap.ana; simp only [anaSide, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.1
  have hclean1 : ∀ i b, AnaBit b → s1.abit i b = false := fun i b hb => by rw [hap.bits]; exact h.clean i b hb
  split
  · -- conflict on level one
    rename_i h1
    have h1' : cl = 1 := by simpa using h1
    have hFP : FPre Φ s1 c := by
      refine ⟨hap.inv, by rw [hap.level, h1']; rfl, hap.conflict, fun d hd => ?_, hclean1,
        by rw [hcl1]; exact h.clauseEmpty, listed_of_clean hclean1⟩
      have := hap.invP d hd; rw [h1'] at this; exact this
    refine ⟨fun e => by simp at e, Or.inl rfl, fun _ => ?_⟩
    rcases analyzeFailedLiteral_spec hFP with h' | fo
    · left; rw [(finish_flags _).1]; exact h'
    · right; right
      have hinc : Flg s1 = Flg s := flg_of_anaSide hap.ana
      exact finish_clean ⟨fo.inv, fo.invS, fo.listed, fo.others, fo.clauseEmpty, fo.incons.trans hinc,
        hap.mono.trans fo.mono⟩
  · -- first-UIP learning
    have hA : APre Φ s1 c cl.toNat := ⟨⟨hap.inv, by rw [hap.level], hpos⟩, hap.conflict, hclean1,
      by rw [hcl1]; exact h.clauseEmpty, hap.hasL, by rw [hopt1]; exact h.otfs⟩
    have hd := (deduceFirstUip_spec hA).1
    have hL := learnDeduced_spec hA hap.invP (by rw [hw1]; exact h.cpre.watching) (by rw [hopt1]; exact h.eager)
      (by rw [hopt1]; exact h.bumpreasons)
    generalize s1.deduceFirstUipClause c = D at hd hL ⊢
    obtain ⟨o, s2⟩ := D
    dsimp only at hd hL ⊢
    subst hd
    dsimp only
    refine ⟨fun e => by simp at e, Or.inl rfl, fun _ => ?_⟩
    rcases hL with h' | h' | ao
    · left; rw [(finish_flags _).1]; exact h'
    · right; left; rw [(finish_flags _).2]; exact h'
    · right; right
      have hinc : Flg s1 = Flg s := flg_of_anaSide hap.ana
      have c := finish_clean ao
      exact ⟨c.inv, c.invS, c.clean, c.clauseEmpty, c.incons.trans hinc, hap.mono.trans c.mono⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem modifyAverages_quiet (s : Solver) (f : Averages → Averages) : Quiet (s.modifyAverages f) s :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem Quiet.astepPre {Φ : (Nat → Bool) → Prop} {s t : Solver} {c : CRef} (h : AStepPre Φ s c) (hq : Quiet t s)
    (hc01 : t.conflictLit0 = s.conflictLit0 ∧ t.conflictLit1 = s.conflictLit1) : AStepPre Φ t c := by
  have hS := hq.same
  have hopt : t.options = s.options := hS.options
  have hw : t.watching = s.watching := by
    have := hq.ana; simp only [anaSide, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.1
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
    fun i b hb => by rw [hq.abit]; exact h.clean i b hb, by rw [hq.clause]; exact h.clauseEmpty,
    by rw [hopt]; exact h.otfs, by rw [hopt]; exact h.eager, by rw [hopt]; exact h.bumpreasons⟩
  · rw [invSAt_congr hS.asg hS.frameTrail, hS.propagate]; exact hcp.invP d ((hS.inDB d).mp hd)
  · rw [show t.framesL = s.framesL by unfold framesL; rw [hS.frameTrail], hS.propagate]; exact hcp.framesLe

/-- Conflict analysis (`kissat_analyze`) in the `--plain` configuration. -/
theorem analyze_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (h : AStepPre Φ s c)
    (hinc : s.inconsistent = true → ¬ ∃ β, Φ β) :
    ((s.analyze c).1 = 20 → ¬ ∃ β, Φ β) ∧ ((s.analyze c).1 = 0 ∨ (s.analyze c).1 = 20) ∧
    ((s.analyze c).1 = 0 → (s.analyze c).2.overflowed = true ∨ (s.analyze c).2.outOfResources = true ∨
      CleanOut Φ s (s.analyze c).2) := by
  unfold analyze
  split
  · exact ⟨fun _ => hinc ‹_›, Or.inr rfl, fun e => by simp at e⟩
  rename_i hinc0
  have hq : Quiet (if !s.probing then s.updateAnalysisAverages else s) s := by
    split
    · exact (modifyAverages_quiet _ _).trans ((modifyAverages_quiet _ _).trans (modifyAverages_quiet _ _))
    · exact Quiet.refl _
  have hc01 : (if !s.probing then s.updateAnalysisAverages else s).conflictLit0 = s.conflictLit0 ∧
      (if !s.probing then s.updateAnalysisAverages else s).conflictLit1 = s.conflictLit1 := by
    have := hq.ana; simp only [anaSide, Prod.mk.injEq] at this
    exact ⟨this.2.2.2.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  dsimp only
  generalize (if !s.probing then s.updateAnalysisAverages else s) = s1 at hq hc01 ⊢
  have h1 := hq.astepPre h hc01
  have hinc1 : Flg s1 = Flg s := flg_of_anaSide hq.ana
  -- the analysis loop runs exactly one step
  have hloop : ∀ fuel, s1.analyzeLoop c (fuel + 1) = match s1.analyzeStep c with
      | (.inl r, t) => (r, t) | (.inr c', t) => t.analyzeLoop c' fuel := fun fuel => rfl
  generalize hf : s1.arena.words.size = n
  rw [hloop n]
  obtain ⟨o1, o2, o3⟩ := analyzeStep_spec h1
  generalize s1.analyzeStep c = R at o1 o2 o3 ⊢
  obtain ⟨r, t⟩ := R
  dsimp only at o1 o2 o3 ⊢
  rcases o2 with e | e
  · subst e
    dsimp only
    refine ⟨fun e => by simp at e, Or.inl rfl, fun _ => ?_⟩
    rcases o3 (by simp) with h' | h' | co
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ⟨co.inv, co.invS, co.clean, co.clauseEmpty, co.incons.trans hinc1,
        (IrrMono.of_eq hq.same.asg hq.same.arena hq.same.watches).trans co.mono⟩)
  · subst e
    dsimp only
    exact ⟨fun _ => o1 rfl, Or.inr rfl, fun e => by simp at e⟩

end Solver
end LeanKissat
