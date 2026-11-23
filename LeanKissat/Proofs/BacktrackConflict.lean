import LeanKissat.Proofs.AssignSInv

/-!
# `backtrackAfterConflict`
-/

namespace LeanKissat
namespace Solver

/-- The analysis-side fields untouched by backtracking. -/
def anaSide (s : Solver) := (s.clause, s.analyzed, s.removable, s.poisoned, s.shrinkable, s.minimize,
  s.levels, s.options, s.inconsistent, s.overflowed, s.watching, s.probing, s.outOfResources,
  s.conflictLit0, s.conflictLit1, s.importLit, s.importBits, s.vars, s.notPorted)

theorem backtrackLoop_anaSide (a : Asg) (newLevel : UInt32) (stop : Nat) :
    ∀ (s : Solver) (p q : Nat), anaSide (backtrackLoop a s newLevel p q stop).2.1 = anaSide s := by
  intro s p q
  fun_induction backtrackLoop a s newLevel p q stop with
  | case1 a s p q h lit idx level hl a' ih => exact ih
  | case2 a s p q h lit idx level hl notLit a' s' ih =>
    rw [ih]
    simp only [s']
    split
    · split <;> rfl
    · rfl
  | case3 => rfl

theorem backtrack_anaSide (s : Solver) (newLevel : UInt32) :
    anaSide (s.backtrackWithoutUpdatingPhases newLevel) = anaSide s := by
  by_cases h : s.level = newLevel
  · unfold backtrackWithoutUpdatingPhases; rw [if_pos (by simp [h])]
  · rw [backtrack_eq s newLevel h]
    unfold btFinish
    generalize hr : backtrackLoop s.asg ({ s.shrinkFrames (newLevel.toNat + 1) with asg := {} }) newLevel
      (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat
      (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat s.asg.trail.size = r
    have := backtrackLoop_anaSide s.asg newLevel s.asg.trail.size
      ({ s.shrinkFrames (newLevel.toNat + 1) with asg := {} }) (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat
      (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat
    rw [hr] at this
    obtain ⟨a, t, q⟩ := r
    exact this

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem updateTargetAndBestPhases_same (s : Solver) : Same s.updateTargetAndBestPhases s := by
  have h : ∀ f : Solver → Prop, (∀ t : Solver, Same t s → f t) → f s.updateTargetAndBestPhases := by
    intro f hf
    unfold updateTargetAndBestPhases saveTargetPhases saveBestPhases
    split
    · exact hf s ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · dsimp only
      split <;> split <;> exact hf _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact h (fun t => Same t s) (fun t ht => ht)

theorem updateTargetAndBestPhases_anaSide (s : Solver) : anaSide s.updateTargetAndBestPhases = anaSide s := by
  unfold updateTargetAndBestPhases saveTargetPhases saveBestPhases
  split
  · rfl
  · dsimp only
    split <;> split <;> rfl

theorem SInv.framesL_lt {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {k : UInt32} (hk : k < s.level) :
    k.toNat < s.framesL.length := by
  rw [hs.levelOK.len]; exact UInt32.lt_iff_toNat_lt.mp hk

/-- Backtracking after a conflict to `newLevel < level`. -/
theorem backtrackAfterConflict_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s)
    (hl0 : s.level ≠ 0) {newLevel : UInt32} (hnl : newLevel < s.level) {P : Nat}
    (hP : ∀ c, s.InDB c → s.InvSAt P c) (hPle : ∀ f ∈ s.framesL, f ≤ P) :
    SInv Φ (s.backtrackAfterConflict newLevel) ∧ (s.backtrackAfterConflict newLevel).level = newLevel ∧
    (∀ c, (s.backtrackAfterConflict newLevel).InDB c → (s.backtrackAfterConflict newLevel).InvS c) ∧
    anaSide (s.backtrackAfterConflict newLevel) = anaSide s ∧
    (∀ c, (s.backtrackAfterConflict newLevel).InDB c ↔ s.InDB c) ∧
    (s.backtrackAfterConflict newLevel).arena = s.arena ∧
    (s.backtrackAfterConflict newLevel).watches = s.watches ∧
    (s.backtrackAfterConflict newLevel).vars = s.vars ∧
    (s.backtrackAfterConflict newLevel).asg.aBits = s.asg.aBits ∧
    (s.backtrackAfterConflict newLevel).asg.aLevel = s.asg.aLevel ∧
    (∀ l, s.IsTrue l → s.lvl l ≤ newLevel.toNat → (s.backtrackAfterConflict newLevel).IsTrue l) ∧
    (∀ l, (s.backtrackAfterConflict newLevel).IsTrue l → s.IsTrue l) := by
  unfold backtrackAfterConflict
  have hne : (s.level != 0) = true := by simpa using hl0
  have hpos : 0 < s.level.toNat := by
    have : s.level.toNat ≠ 0 := fun e => hl0 (UInt32.toNat_inj.mp (by simpa using e))
    omega
  rw [if_pos hne]
  have hlt1 : s.level - 1 < s.level := by
    have : 0 < s.level.toNat := by
      have : s.level.toNat ≠ 0 := fun e => hl0 (UInt32.toNat_inj.mp (by simpa using e))
      omega
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp; omega
  obtain ⟨b1, b2, _, b4, b5⟩ := backtrack_spec hs hlt1 hP
    (hPle _ (List.getElem_mem (hs.framesL_lt hlt1)))
  have a1 := backtrack_anaSide s (s.level - 1)
  generalize s.backtrackWithoutUpdatingPhases (s.level - 1) = s1 at b1 b2 b4 b5 a1
  dsimp only
  have hU := updateTargetAndBestPhases_same s1
  have aU := updateTargetAndBestPhases_anaSide s1
  generalize s1.updateTargetAndBestPhases = s2 at hU aU ⊢
  have hs2 : SInv Φ s2 := hU.sinv b1
  have hinv2 : ∀ c, s2.InDB c → s2.InvS c := by
    intro c hc
    unfold InvS; rw [invSAt_congr hU.asg hU.frameTrail, hU.propagate]
    exact b4 c ((hU.inDB c).mp hc)
  have hdb2 : ∀ c, s2.InDB c ↔ s.InDB c := by
    intro c; rw [hU.inDB c, inDB_congr b5.watches b5.arena c]
  by_cases heq : s2.level = newLevel
  · have : s2.backtrackWithoutUpdatingPhases newLevel = s2 := by
      unfold backtrackWithoutUpdatingPhases; rw [if_pos (by simp [heq])]
    rw [this]
    have eT2 : ∀ l, s2.IsTrue l ↔ s1.IsTrue l := by intro l; unfold IsTrue; rw [hU.asg]
    have hlt1' : (s.level - 1).toNat = s.level.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
    refine ⟨hs2, heq, hinv2, by rw [aU, a1], hdb2, by rw [hU.arena, b5.arena], by rw [hU.watches, b5.watches],
      by rw [hU.vars, b5.vars], by rw [hU.asg, b5.aBits], by rw [hU.asg, b5.aLevel], fun l hl hlv => ?_,
      fun l hl => b5.trueTo l ((eT2 l).mp hl)⟩
    apply (eT2 l).mpr
    apply b5.keep l hl
    have := UInt32.lt_iff_toNat_lt.mp hnl
    rw [hlt1']; rw [← hU.level, heq] at *; omega
  · have hlt2 : newLevel < s2.level := by
      rw [hU.level, b2]
      rw [hU.level, b2] at heq
      have h1 := UInt32.lt_iff_toNat_lt.mp hnl
      have h2 : newLevel.toNat ≠ (s.level - 1).toNat := fun e => heq (UInt32.toNat_inj.mp e).symm
      rw [UInt32.lt_iff_toNat_lt]
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)] at h2 ⊢
      simp at h2 ⊢; omega
    obtain ⟨c1, c2, _, c4, c5⟩ := backtrack_spec hs2 hlt2 hinv2
      (hs2.levelOK.framesLe _ (List.getElem_mem (hs2.framesL_lt hlt2)))
    have a2 := backtrack_anaSide s2 newLevel
    have eT2 : ∀ l, s2.IsTrue l ↔ s1.IsTrue l := by intro l; unfold IsTrue; rw [hU.asg]
    have eL2 : ∀ l, s2.lvl l = s1.lvl l := by intro l; unfold lvl; rw [hU.asg]
    have eL1 : ∀ l, s1.lvl l = s.lvl l := by intro l; unfold lvl; rw [b5.aLevel]
    have hlt1' : (s.level - 1).toNat = s.level.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
    refine ⟨c1, c2, c4, by rw [a2, aU, a1], fun c => (inDB_congr c5.watches c5.arena c).trans (hdb2 c),
      by rw [c5.arena, hU.arena, b5.arena], by rw [c5.watches, hU.watches, b5.watches],
      by rw [c5.vars, hU.vars, b5.vars], by rw [c5.aBits, hU.asg, b5.aBits], by rw [c5.aLevel, hU.asg, b5.aLevel],
      fun l hl hlv => ?_, fun l hl => b5.trueTo l ((eT2 l).mp (c5.trueTo l hl))⟩
    have hnl' := UInt32.lt_iff_toNat_lt.mp hnl
    apply c5.keep l
    · apply (eT2 l).mpr
      apply b5.keep l hl
      rw [hlt1']; omega
    · rw [eL2, eL1]; exact hlv

end Solver
end LeanKissat
