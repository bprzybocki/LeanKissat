import LeanKissat.Proofs.PropWatch
import LeanKissat.Proofs.Justify

/-!
# Reasons and root implications across a propagation round
-/

namespace LeanKissat
namespace Solver
open Arena

theorem le_asgAssignmentLevel (arena : Arena) (aLevel : U32Vec) (lit : Lit) (ref : Ref)
    (i n : Nat) (res : UInt32) :
    res ≤ asgAssignmentLevel arena aLevel lit ref i n res ∧
    ∀ k, i ≤ k → k < n → arena.lit ref k ≠ lit →
      aLevel.get! (IDX (arena.lit ref k)).toNat ≤ asgAssignmentLevel arena aLevel lit ref i n res := by
  fun_induction asgAssignmentLevel arena aLevel lit ref i n res with
  | case1 i res hi other l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hres : res ≤ (if res < l then l else res) := by
      split
      · rename_i h; exact UInt32.le_of_lt h
      · exact UInt32.le_refl _
    have hl : l ≤ (if res < l then l else res) := by
      split
      · exact UInt32.le_refl _
      · rename_i h; exact UInt32.not_lt.mp h
    refine ⟨UInt32.le_trans hres ih1, ?_⟩
    intro k hk1 hk2 hne
    by_cases e : k = i
    · subst e
      have : l = aLevel.get! (IDX other).toNat := by simp [l, other, hne]
      rw [← this]; exact UInt32.le_trans hl ih1
    · exact ih2 k (by omega) hk2 hne
  | case2 i res hi =>
    exact ⟨UInt32.le_refl _, fun k hk1 hk2 => absurd hk2 (by omega)⟩

/-- The fixed justification context of a round. -/
structure JCtx (Φ : (Nat → Bool) → Prop) (s0 : Solver) : Prop where
  reasons : s0.ReasonOK
  roots : RootImplied Φ s0
  db : DBImplied Φ s0
  sizes : s0.ReasonSizes

def JustInv (Φ : (Nat → Bool) → Prop) (s0 : Solver) (st : PS) : Prop :=
  (V s0 st).ReasonOK ∧ RootImplied Φ (V s0 st) ∧ (V s0 st).ReasonSizes

theorem JustInv.init {Φ : (Nat → Bool) → Prop} {s0 : Solver} (h : JCtx Φ s0) (cold : Solver) :
    JustInv Φ s0 (PS.init s0 cold) := ⟨h.reasons, h.roots, h.sizes⟩

/-- Database clauses of the virtual solver are implied. -/
theorem RunInv.dbImplied {Φ : (Nat → Bool) → Prop} {s0 : Solver} {i : Nat} {n : Lit} {st : PS}
    {d : List WEntry} (h : RunInv s0 i n st d) (hj : JCtx Φ s0) : DBImplied Φ (V s0 st) := by
  intro c hc
  rcases (inDB_iff _ c).mp hc with ⟨r, hl, rfl⟩ | ⟨x, y, hxy, rfl⟩
  · have hl0 := (h.arena.liveRef r).mp hl
    exact (hj.db _ ((inDB_iff _ _).mpr (Or.inl ⟨r, hl0, rfl⟩))).perm
      (fun x hx => (h.arena.perm r hl0.1).mem_iff.mpr hx)
  · exact hj.db _ ((inDB_iff _ _).mpr (Or.inr ⟨x, y, hxy, rfl⟩))

/-- Only the arena changed (by clause permutations). -/
theorem JustInv.arena {Φ : (Nat → Bool) → Prop} {s0 : Solver} {i : Nat} {n : Lit}
    {st st' : PS} {d d' : List WEntry} (h : JustInv Φ s0 st) (hr : RunInv s0 i n st d)
    (hr' : RunInv s0 i n st' d') (ha : st'.a = st.a) : JustInv Φ s0 st' := by
  have hlive : ∀ r, (V s0 st').LiveRef r ↔ (V s0 st).LiveRef r := fun r =>
    (hr'.arena.liveRef r).trans (hr.arena.liveRef r).symm
  have hmem : ∀ r, (V s0 st).LiveRef r → ∀ x, x ∈ (V s0 st').clauseL r ↔ x ∈ (V s0 st).clauseL r := by
    intro r hl x
    have hl0 := (hr.arena.liveRef r).mp hl
    exact ((hr'.arena.perm r hl0.1).mem_iff).trans ((hr.arena.perm r hl0.1).mem_iff).symm
  have eT : (V s0 st').IsTrue = (V s0 st).IsTrue := by funext l; simp [IsTrue, V, ha]
  have eF : (V s0 st').IsFalse = (V s0 st).IsFalse := by funext l; simp [IsFalse, V, ha]
  have eL : (V s0 st').lvl = (V s0 st).lvl := by funext l; simp [lvl, V, ha]
  have eB : (V s0 st').binOf = (V s0 st).binOf := by
    funext l; simp [binOf, isBinaryReason, abit, abits, V, ha]
  have eR : (V s0 st').reasonOf = (V s0 st).reasonOf := by funext l; simp [reasonOf, reasonIdx, V, ha]
  have eW : (V s0 st').BinWatched = (V s0 st).BinWatched := rfl
  have eS : (V s0 st').ReasonSizes = (V s0 st).ReasonSizes := by simp [ReasonSizes, trailL, V, ha]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, by rw [eS]; exact h3⟩
  · intro l hl hlv
    rw [eT] at hl; rw [eL] at hlv
    exact reasonAt_congr (by simp [V, ha]) (fun r h => (hlive r).mpr h)
      (fun r h x => hmem r h x) (fun a b h => h) (h1 l hl hlv)
  · intro l hl hlv
    rw [eT] at hl; rw [eL] at hlv
    exact h2 l hl hlv

/-- Truth and level of false literals survive an assignment. -/
theorem withAssign_keepF {s : Solver} {probing : Bool} {k : UInt32} {binary : Bool} {x : Lit}
    {reason : UInt32} (hc : s.Core) (hx : s.ValidLit x) (hun : ¬ s.IsTrue x ∧ ¬ s.IsFalse x)
    {y : Lit} (hy : s.IsFalse y) :
    (s.withAssign probing k binary x reason).IsFalse y ∧
    (s.withAssign probing k binary x reason).lvl y = s.lvl y := by
  obtain ⟨hc', _, _⟩ := assign_core (probing := probing) (level := k) (binary := binary)
    (reason := reason) hc hx hun
  have hn : s.IsTrue (NOT y) := by
    have := (hc.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hy
  obtain ⟨h1, h2⟩ := withAssign_keep hc hx hun hn
  constructor
  · have := (hc'.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mp h1
  · rw [← hc'.lvlVar y, h2, hc.lvlVar]

theorem ante_assign_old {W : Solver} {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit}
    {rr : UInt32} (hc : W.Core) (hx : W.ValidLit x) (hun : ¬ W.IsTrue x ∧ ¬ W.IsFalse x)
    {l y : Lit} (hll : (W.withAssign probing k bb x rr).lvl l = W.lvl l) (h : W.Ante l y) :
    (W.withAssign probing k bb x rr).Ante l y := by
  obtain ⟨f1, f2⟩ := withAssign_keepF (probing := probing) (k := k) (binary := bb)
    (reason := rr) hc hx hun h.1
  refine ⟨f1, by rw [f2, hll]; exact h.2.1, fun hp => ?_⟩
  rw [f2] at hp
  have := h.2.2 hp
  unfold Before at *; rw [assign_trailL]
  exact this.trans (List.sublist_append_left _ _)

theorem ante_assign_new {W : Solver} {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit}
    {rr : UInt32} (hc : W.Core) (hx : W.ValidLit x) (hun : ¬ W.IsTrue x ∧ ¬ W.IsFalse x)
    {y : Lit} (hy : W.IsFalse y) (hly : W.lvl y ≤ k.toNat) :
    (W.withAssign probing k bb x rr).Ante x y := by
  obtain ⟨f1, f2⟩ := withAssign_keepF (probing := probing) (k := k) (binary := bb)
    (reason := rr) hc hx hun hy
  have hlvx : (W.withAssign probing k bb x rr).lvl x = k.toNat := by
    rw [assign_lvl hc.sizes hx]; simp
  refine ⟨f1, by rw [f2, hlvx]; exact hly, fun hp => ?_⟩
  rw [f2] at hp
  have hnt : W.IsTrue (NOT y) := by
    have := (hc.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hy
  have hmem : NOT y ∈ W.trailL := by
    rcases hc.trueOnTrail _ hnt with h | h
    · exact h
    · rw [hc.lvlVar] at h; omega
  unfold Before; rw [assign_trailL]
  exact List.Sublist.append (List.singleton_sublist.mpr hmem) (List.Sublist.refl _)

theorem JustInv.assign {Φ : (Nat → Bool) → Prop} {s0 : Solver} {i : Nat} {n : Lit} {st : PS}
    {d : List WEntry} (h : JustInv Φ s0 st) (hr : RunInv s0 i n st d)
    {probing : Bool} {k : UInt32} {bb : Bool} {x : Lit} {rr : UInt32}
    (hx : (V s0 st).ValidLit x) (hun : ¬ (V s0 st).IsTrue x ∧ ¬ (V s0 st).IsFalse x)
    (hnew : k ≠ 0 → (rr = DECISION_REASON ∨
      (bb = true ∧ (V s0 st).BinWatched x rr ∧ (V s0 st).IsFalse rr ∧ (V s0 st).lvl rr ≤ k.toNat) ∨
      (bb = false ∧ (V s0 st).LiveRef rr ∧ x ∈ (V s0 st).clauseL rr ∧
        ∀ y ∈ (V s0 st).clauseL rr, y ≠ x → (V s0 st).IsFalse y ∧ (V s0 st).lvl y ≤ k.toNat)))
    (hroot : k = 0 → Implied Φ [x]) :
    JustInv Φ s0 { st with a := st.a.assign probing k bb x rr } := by
  unfold JustInv
  rw [V_withAssign]
  generalize hW : V s0 st = W at hx hun hnew
  have hc : W.Core := hW ▸ hr.core
  obtain ⟨h1, h2, h3⟩ := h
  rw [hW] at h1 h2 h3
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

theorem JustInv.same {Φ : (Nat → Bool) → Prop} {s0 : Solver} {st st' : PS}
    (h : JustInv Φ s0 st) (ha : st'.a = st.a) (har : st'.arena = st.arena) : JustInv Φ s0 st' := by
  have : V s0 st' = V s0 st := by simp [V, ha, har]
  unfold JustInv; rw [this]; exact h

theorem mem_litsL_iff {a : Arena} {r : Ref} {y : Lit} :
    y ∈ a.litsL r ↔ ∃ k, k < (a.size r).toNat ∧ a.lit r k = y := by
  unfold litsL; simp

theorem just_step {Φ : (Nat → Bool) → Prop} {s0 : Solver} {i : Nat} {lit : Lit} {st : PS}
    {done rest : List WEntry} {e : WEntry} (H : StepHyp s0 i lit st done rest e)
    (hj : JustInv Φ s0 st) (hjc : JCtx Φ s0) (probing : Bool) {lv : UInt32}
    (hlv : lv.toNat = s0.lvl lit) :
    JustInv Φ s0 (PS.step probing false lv (NOT lit) st e) := by
  cases e with
  | bin b =>
    have hbw : s0.BinWatched (NOT lit) b := H.mem
    obtain ⟨hbw', _, hvb, _⟩ := H.ctx.ws.bin _ _ hbw
    unfold PS.step
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    split
    · exact hj.same rfl rfl
    split
    · exact hj.same rfl rfl
    rename_i h1 h2
    have hun : ¬ (V s0 st).IsTrue b ∧ ¬ (V s0 st).IsFalse b :=
      ⟨fun h => h1 ((isTrue_iff_vTrue _ _).mp h), fun h => h2 ((isFalse_iff_vFalse _ _).mp h)⟩
    refine JustInv.same (st := { st with a := st.a.assign probing lv true b (NOT lit) }) ?_ rfl rfl
    refine hj.assign H.run hvb hun ?_ ?_
    · intro _
      refine Or.inr (Or.inl ⟨rfl, hbw', H.notLitFalse, ?_⟩)
      rw [H.run.core.lvlVar, (H.run.persist lit H.ctx.litTrue).2, hlv]; exact Nat.le_refl _
    · intro hz
      have h0 : s0.lvl lit = 0 := by rw [← hlv, hz]; rfl
      have hlitI := hjc.roots lit H.ctx.litTrue h0
      have hcI := hjc.db _ ((inDB_iff _ _).mpr (Or.inr ⟨_, _, hbw, rfl⟩))
      refine hcI.unit (fun y hy hne => ?_)
      simp at hy
      rcases hy with rfl | rfl
      · rw [NOT_NOT]; exact hlitI
      · exact absurd rfl hne
  | large b r =>
    have hR := step_large H probing false lv
    unfold PS.step at hR ⊢
    simp only at hR ⊢
    by_cases hbt : vTrue (st.a.values.get! b.toNat) = true
    · rw [ite_eq_left hbt]; exact hj.same rfl rfl
    rw [ite_eq_right hbt] at hR ⊢
    have hr0 := (H.ctx.ws.refOK _ _ _ H.mem).1
    have hgeq : st.arena.garbage r = s0.arena.garbage r := by
      unfold garbage flag; rw [H.run.arena.word0 r hr0]
    by_cases hg : st.arena.garbage r = true
    · rw [ite_eq_left hg]; exact hj
    rw [ite_eq_right hg] at hR ⊢
    have F := H.largeFacts (by rw [← hgeq]; simpa using hg)
    by_cases hot : vTrue (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat) = true
    · rw [ite_eq_left hot]; exact hj.same rfl rfl
    rw [ite_eq_right hot] at hR ⊢
    have SS := search_spec st.arena st.a.values r _ _ F.searched2 F.searchedLt
    simp only at SS
    generalize (if findReplacement st.arena st.a.values r (st.arena.searched r).toNat
        (st.arena.size r).toNat < (st.arena.size r).toNat then
        findReplacement st.arena st.a.values r (st.arena.searched r).toNat (st.arena.size r).toNat
      else if findReplacement st.arena st.a.values r 2 (st.arena.searched r).toNat <
        (st.arena.searched r).toNat then findReplacement st.arena st.a.values r 2 (st.arena.searched r).toNat
      else (st.arena.size r).toNat) = R at SS hR ⊢
    by_cases hRs : R < (st.arena.size r).toNat
    · rw [ite_eq_left hRs] at hR ⊢; exact hj.arena H.run hR rfl
    rw [ite_eq_right hRs] at hR ⊢
    have hall := SS.2 hRs
    by_cases h1 : (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat != 0) = true
    · rw [ite_eq_left h1]; exact hj.same rfl rfl
    rw [ite_eq_right h1]
    have hfe := F.false_except H hall
    have hle := (le_asgAssignmentLevel st.arena st.a.aLevel
      (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit) r 0 (st.arena.size r).toNat 0).2
    generalize hother : st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit = other at h1 hfe hle ⊢
    have hw := F.watch
    rw [hother] at hw
    have hmem : other ∈ st.arena.litsL r := by
      rcases hw with ⟨_, h⟩ | ⟨_, h⟩
      · rw [← h]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
      · rw [← h]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
    have hv0 : st.a.values.get! other.toNat = 0 := by simpa using h1
    have hun : ¬ (V s0 st).IsTrue other ∧ ¬ (V s0 st).IsFalse other := by
      constructor
      · intro h; have : st.a.values.get! other.toNat = VAL_TRUE := h; rw [hv0] at this; simp [VAL_TRUE] at this
      · intro h; have : st.a.values.get! other.toNat = VAL_FALSE := h; rw [hv0] at this; simp [VAL_FALSE] at this
    have hvalid := F.valid other hmem
    generalize asgAssignmentLevel st.arena st.a.aLevel other r 0 (st.arena.size r).toNat 0 = al at hle ⊢
    have hlive : (V s0 st).LiveRef r := (H.run.arena.liveRef r).mpr F.live0
    have hothers : ∀ y ∈ (V s0 st).clauseL r, y ≠ other →
        (V s0 st).IsFalse y ∧ (V s0 st).lvl y ≤ al.toNat := by
      intro y hy hne
      obtain ⟨k, hk, rfl⟩ := mem_litsL_iff.mp hy
      exact ⟨hfe k hk hne, UInt32.le_iff_toNat_le.mp (hle k (Nat.zero_le _) hk hne)⟩
    refine JustInv.same (st := { st with a := st.a.assign probing al false other r }) ?_ rfl rfl
    refine hj.assign H.run hvalid hun ?_ ?_
    · intro _
      exact Or.inr (Or.inr ⟨rfl, hlive, hmem, hothers⟩)
    · intro hz
      have hcI := H.run.dbImplied hjc _ ((inDB_iff _ _).mpr (Or.inl ⟨r, hlive, rfl⟩))
      refine hcI.unit (fun y hy hne => ?_)
      obtain ⟨hf, hl⟩ := hothers y hy hne
      rw [hz] at hl
      have ht : (V s0 st).IsTrue (NOT y) := by
        have := (H.run.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf
      exact hj.2.1 (NOT y) ht (by rw [H.run.core.lvlVar]; simpa using hl)

theorem run_all {Φ : (Nat → Bool) → Prop} {s0 : Solver} {i : Nat} {lit : Lit}
    (hctx : Ctx s0 i lit) (hjc : JCtx Φ s0) (probing : Bool)
    {lv : UInt32} (hlv : lv.toNat = s0.lvl lit) :
    ∀ (es : List WEntry) (st : PS) (done : List WEntry), RunInv s0 i (NOT lit) st done →
    WSInv s0 (NOT lit) st es → JustInv Φ s0 st → s0.entries (NOT lit) = done ++ es →
    RunInv s0 i (NOT lit) (PS.run probing false lv (NOT lit) st es) (done ++ es) ∧
    WSInv s0 (NOT lit) (PS.run probing false lv (NOT lit) st es) [] ∧
    JustInv Φ s0 (PS.run probing false lv (NOT lit) st es) := by
  have hlv' : lv.toNat ≤ s0.level.toNat := by
    rw [hlv]; exact hctx.levelOK.trueLe lit hctx.litTrue
  intro es
  induction es with
  | nil => intro st done h hw hj _; simpa [PS.run] using ⟨h, hw, hj⟩
  | cons e es ih =>
    intro st done h hw hj hsplit
    by_cases hres : st.res.isSome
    · rw [PS.run_of_res st hres]
      exact ⟨h.extend_conflict hres _ _ rfl rfl rfl rfl, hw.flush, hj.same rfl rfl⟩
    · have hres' : st.res = none := by simpa using hres
      rw [PS.run_cons_none st hres']
      have H : StepHyp s0 i lit st done es e := ⟨hctx, h, hres', hsplit⟩
      have hstep : RunInv s0 i (NOT lit) (PS.step probing false lv (NOT lit) st e)
          (done ++ [e]) := by
        cases e with
        | bin b => exact step_bin H probing false hlv'
        | large b r => exact step_large H probing false lv
      have := ih _ _ hstep (ws_step H hw probing false lv) (just_step H hj hjc probing hlv)
        (by rw [hsplit]; simp)
      simpa using this

end Solver
end LeanKissat
