import LeanKissat.Proofs.Backtrack

/-!
# Assignments outside propagation

`Solver.assign` of an unassigned literal at a level at most the current one, with a valid
reason, preserves `SInv` and the watch invariant at every pointer inside the old trail.
-/

namespace LeanKissat
namespace Solver

/-- The reason condition for a new assignment of `x` at level `k` with reason `rr`. -/
def NewReason (W : Solver) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) : Prop :=
  rr = DECISION_REASON ∨
  (bb = true ∧ W.BinWatched x rr ∧ W.IsFalse rr ∧ W.lvl rr ≤ k.toNat) ∨
  (bb = false ∧ W.LiveRef rr ∧ x ∈ W.clauseL rr ∧
    ∀ y ∈ W.clauseL rr, y ≠ x → W.IsFalse y ∧ W.lvl y ≤ k.toNat)

theorem just_withAssign {Φ : (Nat → Bool) → Prop} {W : Solver} (hc : W.Core) (h1 : W.ReasonOK)
    (h2 : RootImplied Φ W) (h3 : W.ReasonSizes)
    {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit} {rr : UInt32}
    (hx : W.ValidLit x) (hun : ¬ W.IsTrue x ∧ ¬ W.IsFalse x)
    (hnew : k ≠ 0 → NewReason W k bb x rr) (hroot : k = 0 → Implied Φ [x]) :
    (W.withAssign probing k bb x rr).ReasonOK ∧ RootImplied Φ (W.withAssign probing k bb x rr) ∧
    (W.withAssign probing k bb x rr).ReasonSizes := by
  have hs := hc.sizes
  have hold : ∀ l, (W.withAssign probing k bb x rr).IsTrue l → l ≠ x → W.IsTrue l ∧ IDX l ≠ IDX x := by
    intro l hl hne
    rcases (assign_isTrue hs hx l).mp hl with e | ⟨hne', hl'⟩
    · exact absurd e hne
    · refine ⟨hl', fun e => ?_⟩
      rcases (IDX_eq_iff l x).mp e with e | e
      · exact hne e
      · exact hne' e
  have hlvx : (W.withAssign probing k bb x rr).lvl x = k.toNat := by
    rw [assign_lvl hs hx]; simp
  have hlvl : ∀ l, IDX l ≠ IDX x → (W.withAssign probing k bb x rr).lvl l = W.lvl l := by
    intro l hl; rw [assign_lvl hs hx]; simp [hl]
  have eW : (W.withAssign probing k bb x rr).BinWatched = W.BinWatched := rfl
  have eLive : (W.withAssign probing k bb x rr).LiveRef = W.LiveRef := rfl
  have eCl : (W.withAssign probing k bb x rr).clauseL = W.clauseL := rfl
  refine ⟨?_, ?_, assign_reasonSizes h3 hc hx hun⟩
  · intro l hl hlv
    unfold ReasonAt
    rw [eW, eLive, eCl]
    by_cases e : l = x
    · subst e
      have hk : k ≠ 0 := by intro e; rw [hlvx, e] at hlv; simp at hlv
      rw [assign_reasonOf_self h3 hx hk, assign_binOf_self h3 hx hk]
      rcases hnew hk with e | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl ⟨b1, b2, ante_assign_new hc hx hun b3 b4⟩)
      · refine Or.inr (Or.inr ⟨b1, b2, b3, fun y hy hne => ?_⟩)
        obtain ⟨g1, g2⟩ := b4 y hy hne
        exact ante_assign_new hc hx hun g1 g2
    · obtain ⟨hl', hidx⟩ := hold l hl e
      rw [assign_reasonOf_ne l hidx, assign_binOf_ne l hidx]
      rw [hlvl l hidx] at hlv
      rcases h1 l hl' hlv with e | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl ⟨b1, b2, ante_assign_old hc hx hun (hlvl l hidx) b3⟩)
      · exact Or.inr (Or.inr ⟨b1, b2, b3, fun y hy hne =>
          ante_assign_old hc hx hun (hlvl l hidx) (b4 y hy hne)⟩)
  · intro l hl hlv
    by_cases e : l = x
    · subst e
      rw [hlvx] at hlv
      exact hroot (UInt32.toNat_inj.mp (by simpa using hlv))
    · obtain ⟨hl', hidx⟩ := hold l hl e
      rw [hlvl l hidx] at hlv
      exact h2 l hl' hlv

theorem levelOK_withAssign {W : Solver} (hc : W.Core) (hl : W.LevelOK)
    {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit} {rr : UInt32}
    (hx : W.ValidLit x) (hun : ¬ W.IsTrue x ∧ ¬ W.IsFalse x) (hk : k.toNat ≤ W.level.toNat) :
    (W.withAssign probing k bb x rr).LevelOK := by
  have hs := hc.sizes
  have hlvl : ∀ l, (W.withAssign probing k bb x rr).lvl l = if IDX l = IDX x then k.toNat else W.lvl l := by
    intro l; rw [assign_lvl hs hx]
  have eFr : (W.withAssign probing k bb x rr).framesL = W.framesL := rfl
  have eP : (W.withAssign probing k bb x rr).pushLevel = W.pushLevel := rfl
  have eLev : (W.withAssign probing k bb x rr).level = W.level := rfl
  have eProp : (W.withAssign probing k bb x rr).propagate = W.propagate := rfl
  have htr := assign_trailL (s := W) (probing := probing) (level := k) (binary := bb) (lit := x) (reason := rr)
  refine ⟨?_, ?_, by rw [eFr]; exact hl.sorted, by rw [eFr, eLev]; exact hl.len,
    by rw [eFr, eProp]; exact hl.framesLe, by rw [htr, eProp]; have := hl.propLe; simp; omega,
    by rw [eFr]; exact hl.strict, fun f hf => by
      rw [eFr] at hf; rw [htr]; have := hl.framesLt f hf; simp; omega, hl.frames0⟩
  · intro l ht
    rw [hlvl, eLev]
    split
    · exact hk
    · rename_i hne
      rcases (assign_isTrue hs hx l).mp ht with e | ⟨_, ht'⟩
      · subst e; exact absurd rfl hne
      · exact hl.trueLe l ht'
  · intro p l hp
    rw [htr] at hp
    rw [eP, hlvl]
    by_cases hpl : p < W.trailL.length
    · rw [List.getElem?_append_left hpl] at hp
      split
      · rename_i e
        have hm := List.mem_of_getElem? hp
        have ht := hc.trailTrue l hm
        rcases (IDX_eq_iff l x).mp e with e' | e'
        · subst e'; exact absurd ht hun.1
        · exfalso; subst e'
          exact hun.2 ((hc.valCons (NOT x)).1.mp ht |> fun h => by rw [NOT_NOT] at h; exact h)
      · exact hl.pushLe p l hp
    · have hp' : p = W.trailL.length := by
        have := (List.getElem?_eq_some_iff.mp hp).1; simp at this; omega
      subst hp'
      rw [List.getElem?_append_right (Nat.le_refl _)] at hp
      simp at hp; subst hp
      simp only [ite_true]
      rw [hl.pushLevel_cur hl.propLe]; exact hk

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem withAssign_sinv {Φ : (Nat → Bool) → Prop} {W : Solver} (hs : SInv Φ W)
    {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit} {rr : UInt32}
    (hx : W.ValidLit x) (hun : ¬ W.IsTrue x ∧ ¬ W.IsFalse x) (hk : k.toNat ≤ W.level.toNat)
    (hnew : k ≠ 0 → NewReason W k bb x rr) (hroot : k = 0 → Implied Φ [x]) :
    SInv Φ (W.withAssign probing k bb x rr) ∧
    (∀ P c, P ≤ W.trailL.length → W.InvSAt P c → (W.withAssign probing k bb x rr).InvSAt P c) := by
  obtain ⟨c1, _, c3⟩ := assign_core (probing := probing) (level := k) (binary := bb) (reason := rr)
    hs.core hx hun
  obtain ⟨j1, j2, j3⟩ := just_withAssign hs.core hs.reasons hs.roots hs.rsizes (probing := probing) hx hun hnew hroot
  have hW : (W.withAssign probing k bb x rr).WatchStruct :=
    WatchStruct.congr (t := W.withAssign probing k bb x rr) (s := W) rfl rfl rfl rfl hs.ws
  refine ⟨⟨c1, levelOK_withAssign hs.core hs.levelOK hx hun hk, hW, hs.layout, j1, j2, j3, ?_, hs.jump⟩, c3⟩
  intro c hc; exact hs.db c ((inDB_congr rfl rfl c).mp hc)

theorem deactivateVariable_asg (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).asg = s.asg := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_arena (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).arena = s.arena := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_watches (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).watches = s.watches := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_delayed (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).delayed = s.delayed := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_vars (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).vars = s.vars := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_level (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).level = s.level := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_frameTrail (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).frameTrail = s.frameTrail := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_propagate (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).propagate = s.propagate := by
  unfold deactivateVariable; dsimp only; split <;> rfl
theorem deactivateVariable_options (s : Solver) (idx : UInt32) : (s.deactivateVariable idx).options = s.options := by
  unfold deactivateVariable; dsimp only; split <;> rfl

theorem deactivateVariable_same (s : Solver) (idx : UInt32) : Same (s.deactivateVariable idx) s :=
  ⟨deactivateVariable_asg s idx, deactivateVariable_arena s idx, deactivateVariable_watches s idx,
   deactivateVariable_delayed s idx, deactivateVariable_vars s idx, deactivateVariable_level s idx,
   deactivateVariable_frameTrail s idx, deactivateVariable_propagate s idx, deactivateVariable_options s idx⟩

theorem markFixedLiteral_same (s : Solver) (lit : Lit) : Same (s.markFixedLiteral lit) s := by
  have h := deactivateVariable_same (s.setVarFlag (IDX lit) VarFlags.fixed true) (IDX lit)
  exact ⟨h.asg, h.arena, h.watches, h.delayed, h.vars, h.level, h.frameTrail, h.propagate, h.options⟩

theorem assign_eq (s : Solver) (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) :
    s.assign probing k bb x rr =
      (if k == 0 then s.markFixedLiteral x else s).withAssign probing k bb x rr := by
  unfold assign withAssign; rfl

/-- `Solver.assign` preserves `SInv`. -/
theorem assign_sinv {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s)
    {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit} {rr : UInt32}
    (hx : s.ValidLit x) (hun : ¬ s.IsTrue x ∧ ¬ s.IsFalse x) (hk : k.toNat ≤ s.level.toNat)
    (hnew : k ≠ 0 → NewReason s k bb x rr) (hroot : k = 0 → Implied Φ [x]) :
    SInv Φ (s.assign probing k bb x rr) ∧
    (∀ P c, P ≤ s.trailL.length → s.InvSAt P c → (s.assign probing k bb x rr).InvSAt P c) ∧
    Same' (s.assign probing k bb x rr) (s.withAssign probing k bb x rr) ∧
    (s.assign probing k bb x rr).propagate = s.propagate := by
  rw [assign_eq]
  have hS : Same (if k == 0 then s.markFixedLiteral x else s) s := by
    split
    · exact markFixedLiteral_same s x
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  generalize hW : (if k == 0 then s.markFixedLiteral x else s) = W at hS ⊢
  have hsW : SInv Φ W := hS.sinv hs
  have eAsg := hS.asg
  have eV : ∀ l, W.ValidLit l ↔ s.ValidLit l := by intro l; simp [ValidLit, hS.vars]
  have eT : ∀ l, W.IsTrue l ↔ s.IsTrue l := by intro l; simp [IsTrue, eAsg]
  have eF : ∀ l, W.IsFalse l ↔ s.IsFalse l := by intro l; simp [IsFalse, eAsg]
  have eL : ∀ l, W.lvl l = s.lvl l := by intro l; simp [lvl, eAsg]
  have eTr : W.trailL = s.trailL := by simp [trailL, eAsg]
  have hnew' : k ≠ 0 → NewReason W k bb x rr := by
    intro hk0
    have eLive : ∀ r, W.LiveRef r ↔ s.LiveRef r := by intro r; simp [LiveRef, refsL, hS.arena]
    have eCl : ∀ r, W.clauseL r = s.clauseL r := by intro r; simp [clauseL, hS.arena]
    have eB : ∀ a b, W.BinWatched a b ↔ s.BinWatched a b := by
      intro a b; simp [BinWatched, entries, watchesOf, hS.watches]
    rcases hnew hk0 with e | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨b1, (eB _ _).mpr b2, (eF _).mpr b3, by rw [eL]; exact b4⟩)
    · refine Or.inr (Or.inr ⟨b1, (eLive _).mpr b2, by rw [eCl]; exact b3, fun y hy hne => ?_⟩)
      rw [eCl] at hy
      obtain ⟨g1, g2⟩ := b4 y hy hne
      exact ⟨(eF _).mpr g1, by rw [eL]; exact g2⟩
  obtain ⟨r1, r2⟩ := withAssign_sinv hsW ((eV x).mpr hx) ⟨fun h => hun.1 ((eT x).mp h), fun h => hun.2 ((eF x).mp h)⟩
    (by rw [hS.level]; exact hk) hnew' hroot (probing := probing)
  refine ⟨r1, fun P c hP hinv => r2 P c (by rw [eTr]; exact hP) ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hS.propagate⟩
  · -- transfer of the watch invariant along `Same`
    have eE : W.entries = s.entries := by funext l; simp [entries, watchesOf, hS.watches]
    have ePF : ∀ w k', W.PropFalseAt P w k' ↔ s.PropFalseAt P w k' := by
      intro w k'
      simp [PropFalseAt, IsFalse, trailL, pushLevel, framesL, lvl, eAsg, hS.frameTrail]
    intro w0 w1 rest hc' k0 k1 hp0 hp1
    obtain ⟨t, ht, htt, htl⟩ := hinv w0 w1 rest hc' k0 k1 ((ePF _ _).mp hp0) ((ePF _ _).mp hp1)
    exact ⟨t, ht, (eT t).mpr htt, by rw [eL]; exact htl⟩
  · show W.asg.assign probing k bb x rr = s.asg.assign probing k bb x rr; rw [eAsg]
  · exact hS.arena
  · exact hS.watches
  · exact hS.delayed
  · exact hS.vars
  · exact hS.level
  · exact hS.frameTrail
  · exact hS.options

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem assign_irrMono {s : Solver} (hc : s.Core) {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit}
    {rr : UInt32} (hx : s.ValidLit x) (hun : ¬ s.IsTrue x ∧ ¬ s.IsFalse x) :
    IrrMono s (s.assign probing k bb x rr) := by
  rw [assign_eq]
  have hS : Same (if k == 0 then s.markFixedLiteral x else s) s := by
    split
    · exact markFixedLiteral_same s x
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  generalize (if k == 0 then s.markFixedLiteral x else s) = W at hS
  have eA : (W.withAssign probing k bb x rr).asg = (s.withAssign probing k bb x rr).asg := by
    simp [withAssign, hS.asg]
  apply IrrMono.of_large
  · intro r h1 h2
    refine ⟨by simpa [LiveRef, refsL, withAssign, hS.arena] using h1,
      by simpa [withAssign, hS.arena] using h2, fun y hy => by simpa [clauseL, withAssign, hS.arena] using hy⟩
  · intro a b hab; simpa [BinWatched, entries, watchesOf, withAssign, hS.watches] using hab
  · intro l ⟨h1, h2⟩
    obtain ⟨g1, g2⟩ := withAssign_keep (probing := probing) (k := k) (binary := bb) (reason := rr) hc hx hun h1
    refine ⟨?_, ?_⟩
    · unfold IsTrue at *; rw [eA]; exact g1
    · unfold lvl at *; rw [eA]; exact g2.trans h2

end Solver
end LeanKissat
