import LeanKissat.Proofs.AnalyzeSpec

/-!
# Search-level invariant, decisions

`SearchInv Φ s`: the invariants that hold between two steps of the search loop.
`pushAssign_spec`: pushing a decision frame and assigning the decision literal
(`kissat_decide`, `kissat_internal_assume`) preserves them.
-/

namespace LeanKissat
namespace Solver

/-- Options of the `--plain` configuration the proofs rely on. -/
structure PlainOpts (o : Options) : Prop where
  otfs : o.otfs = 0
  eager : o.eagersubsume = 0
  bumpreasons : o.bumpreasons = 0
  reorder : o.reorder = 0
  rephase : o.rephase = 0
  reuse : o.restartreusetrail = 0
  stable : o.stable = 2
  compact : o.compact = 0

/-- The import map is the identity (`kissat_reserve`, `tumble = 0`): external variable `v + 1`
  is internal variable `v`, imported and not eliminated. -/
def ImportOK (s : Solver) : Prop :=
  ∀ v, v < s.vars.toNat → v + 1 < s.importLit.size ∧
    s.importLit.get! (v + 1) = LIT (UInt32.ofNat v) ∧ (s.importBits.get! (v + 1) &&& ImportBits.imported) ≠ 0 ∧
    (s.importBits.get! (v + 1) &&& ImportBits.eliminated) = 0

theorem ImportOK.congr {s t : Solver} (h1 : t.importLit = s.importLit) (h2 : t.importBits = s.importBits)
    (h3 : t.vars = s.vars) (h : ImportOK s) : ImportOK t := by
  unfold ImportOK at *; rw [h1, h2, h3]; exact h

theorem ImportOK.flg {s t : Solver} (hf : Flg t = Flg s) (h : ImportOK s) : ImportOK t :=
  h.congr (Flg.importLit hf) (Flg.importBits hf) (Flg.vars hf)

/-- The invariants between two search steps. -/
structure SearchInv (Φ : (Nat → Bool) → Prop) (s : Solver) : Prop where
  inv : SInv Φ s
  invS : ∀ c, s.InDB c → s.InvS c
  clean : ∀ i b, AnaBit b → s.abit i b = false
  clauseEmpty : s.clause.size = 0
  incons : s.inconsistent = true → ¬ ∃ β, Φ β
  watching : s.watching = true
  opts : PlainOpts s.options
  imp : ImportOK s

/-- A search frame: the invariant-relevant fields are unchanged. -/
structure SFr (t s : Solver) : Prop where
  same : Same t s
  clause : t.clause = s.clause
  flg : Flg t = Flg s
  bits : t.asg.aBits = s.asg.aBits

theorem SFr.refl (s : Solver) : SFr s s := ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem SFr.trans {a b c : Solver} (h1 : SFr a b) (h2 : SFr b c) : SFr a c :=
  ⟨⟨h1.same.asg.trans h2.same.asg, h1.same.arena.trans h2.same.arena, h1.same.watches.trans h2.same.watches,
    h1.same.delayed.trans h2.same.delayed, h1.same.vars.trans h2.same.vars, h1.same.level.trans h2.same.level,
    h1.same.frameTrail.trans h2.same.frameTrail, h1.same.propagate.trans h2.same.propagate,
    h1.same.options.trans h2.same.options⟩, h1.clause.trans h2.clause, h1.flg.trans h2.flg,
    h1.bits.trans h2.bits⟩

theorem SFr.searchInv {Φ : (Nat → Bool) → Prop} {s t : Solver} (h : SFr t s) (hs : SearchInv Φ s) :
    SearchInv Φ t := by
  refine ⟨h.same.sinv hs.inv, fun c hc => ?_, fun i b hb => ?_, by rw [h.clause]; exact hs.clauseEmpty,
    fun e => hs.incons (by rw [← (Flg.inconsistent h.flg)]; exact e), by rw [(Flg.watching h.flg)]; exact hs.watching,
    by rw [(Flg.options h.flg)]; exact hs.opts, hs.imp.flg h.flg⟩
  · unfold InvS; rw [h.same.invSAt, h.same.propagate]; exact hs.invS c ((h.same.inDB c).mp hc)
  · unfold abit abits; rw [h.bits]; exact hs.clean i b hb

theorem SFr.irrMono {s t : Solver} (h : SFr t s) : IrrMono s t :=
  IrrMono.of_eq h.same.asg h.same.arena h.same.watches

theorem clean_of_bits {s t : Solver} (h : BitsShrink t.asg s.asg)
    (hc : ∀ i b, AnaBit b → s.abit i b = false) : ∀ i b, AnaBit b → t.abit i b = false := by
  intro i b hb
  have hc' := hc i b hb
  unfold abit abits at *
  rcases h i.toNat with e | e | e
  · rw [e]; exact hc'
  · rw [e]; simp
  · rw [e]; rcases hb with rfl | rfl | rfl | rfl <;> decide

/-- The decision level is bounded by the trail length. -/
theorem SInv.level_le {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) :
    s.level.toNat ≤ s.trailL.length := by
  have := nodup_length_le s.trailL.length s.framesL (hs.levelOK.strict.imp (fun h => Nat.ne_of_lt h))
    hs.levelOK.framesLt
  rw [hs.levelOK.len] at this; exact this

theorem SInv.level_small {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) :
    s.level.toNat < 2 ^ 30 := by
  have := hs.level_le; have := hs.trail_le; have := hs.ws.varsBound; omega

theorem SInv.levelLt {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) : s.level < INVALID_LEVEL := by
  have := hs.level_small
  rw [UInt32.lt_iff_toNat_lt]; unfold INVALID_LEVEL; simp; omega

/-- A conflict on the root level refutes `Φ`. -/
theorem root_conflict_unsat {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (hs : SInv Φ s)
    (hc : ConflictOK s s c) (h0 : s.level = 0) : ¬ ∃ β, Φ β := by
  apply unsat_of_root_false hs (hc.implied hs)
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨ConflictOK.lit_false hc hk, ?_⟩
  have := isFalse_lvl_le hs (ConflictOK.lit_false hc hk)
  rw [h0] at this; simp at this; omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem core_congr {t v : Solver} (ha : t.asg = v.asg) (hv : t.vars = v.vars) (hc : v.Core) : t.Core := by
  have e1 : ∀ l, t.IsTrue l ↔ v.IsTrue l := by intro l; simp [IsTrue, ha]
  have e2 : ∀ l, t.IsFalse l ↔ v.IsFalse l := by intro l; simp [IsFalse, ha]
  have e3 : ∀ l, t.lvl l = v.lvl l := by intro l; simp [lvl, ha]
  have e4 : t.trailL = v.trailL := by simp [trailL, ha]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l; rw [e1, e2, e2]; exact hc.valCons l
  · intro l hl; rw [e1] at hl; rw [e4, e3]; exact hc.trueOnTrail l hl
  · intro l hl; rw [e4] at hl; rw [e1]; exact hc.trailTrue l hl
  · intro l; rw [e3, e3]; exact hc.lvlVar l
  · unfold Sizes; rw [ha, hv]; exact hc.sizes
  · intro j; rw [ha]; exact hc.domain j

theorem framesL_pushFrame (s : Solver) (lit : Lit) (h : 1 ≤ s.frameTrail.size)
    (hT : s.asg.trail.size < 2 ^ 32) :
    (s.pushFrame lit).framesL = s.framesL ++ [s.asg.trail.size] := by
  unfold framesL pushFrame
  dsimp only
  rw [U32Vec.view_push, List.drop_append_of_le_length (by simp; omega)]
  simp only [List.map_append, List.map_cons, List.map_nil]
  congr 2
  simp; omega

/-- Pushing a decision frame and assigning the (unassigned) decision literal. -/
theorem pushAssign_spec {Φ : (Nat → Bool) → Prop} {s W : Solver} (hs : SInv Φ s)
    (hinv : ∀ c, s.InDB c → s.InvS c) (hp : s.propagate = s.trailL.length)
    (ha : W.asg = s.asg) (har : W.arena = s.arena) (hw : W.watches = s.watches)
    (hd : W.delayed = s.delayed) (hv : W.vars = s.vars) (ho : W.options = s.options)
    (hpr : W.propagate = s.propagate) (hft : W.frameTrail = s.frameTrail) (hl : W.level = s.level + 1)
    {lit : Lit} (hx : s.ValidLit lit) (hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit) (probing : Bool) :
    SInv Φ ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON) ∧
    (∀ c, ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON).InDB c →
      ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON).InvS c) ∧
    IrrMono s ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON) ∧
    BitsShrink ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON).asg s.asg ∧
    ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON).level = s.level + 1 ∧
    ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON).clause = W.clause ∧
    Flg ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON) = Flg W ∧
    ((W.pushFrame lit).assign probing W.level false lit DECISION_REASON).vars = s.vars := by
  have hsmall := hs.level_small
  have hL := hs.levelOK
  have hk0 : W.level ≠ 0 := by
    rw [hl]; intro e
    have := congrArg UInt32.toNat e
    rw [UInt32.toNat_add] at this; simp at this; omega
  have hkN : W.level.toNat = s.level.toNat + 1 := by
    rw [hl, UInt32.toNat_add]; simp; omega
  have heq : (W.pushFrame lit).assign probing W.level false lit DECISION_REASON =
      (W.pushFrame lit).withAssign probing W.level false lit DECISION_REASON := by
    rw [assign_eq]; rw [if_neg (by simpa using hk0)]
  rw [heq]
  generalize hV : s.withAssign probing W.level false lit DECISION_REASON = V
  have hTA : ((W.pushFrame lit).withAssign probing W.level false lit DECISION_REASON).asg = V.asg := by
    rw [← hV]; simp [withAssign, pushFrame, ha]
  obtain ⟨c1, c2, c3⟩ := assign_core (probing := probing) (level := W.level) (binary := false)
    (reason := DECISION_REASON) hs.core hx hun
  rw [hV] at c1 c2 c3
  obtain ⟨j1, j2, j3⟩ := just_withAssign hs.core hs.reasons hs.roots hs.rsizes (probing := probing)
    (k := W.level) (bb := false) (rr := DECISION_REASON) hx hun (fun _ => Or.inl rfl) (fun h0 => absurd h0 hk0)
  rw [hV] at j1 j2 j3
  generalize hT : (W.pushFrame lit).withAssign probing W.level false lit DECISION_REASON = t at hTA ⊢
  have hVs : V.arena = s.arena ∧ V.watches = s.watches ∧ V.delayed = s.delayed ∧ V.vars = s.vars ∧
      V.options = s.options ∧ V.propagate = s.propagate ∧ V.frameTrail = s.frameTrail ∧ V.level = s.level := by
    rw [← hV]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hts : t.arena = s.arena ∧ t.watches = s.watches ∧ t.delayed = s.delayed ∧ t.vars = s.vars ∧
      t.options = s.options ∧ t.propagate = s.propagate ∧ t.level = s.level + 1 ∧ t.clause = W.clause ∧
      Flg t = Flg W ∧ t.frameTrail = (W.pushFrame lit).frameTrail := by
    rw [← hT]; exact ⟨har, hw, hd, hv, ho, hpr, hl, rfl, rfl, rfl⟩
  obtain ⟨tA, tW, tD, tVr, tO, tP, tLv, tC, tF, tFT⟩ := hts
  have hT32 : s.asg.trail.size < 2 ^ 32 := by
    have := hs.trail_le; have := hs.ws.varsBound; rw [length_trailL] at *; omega
  have hframes : t.framesL = s.framesL ++ [s.trailL.length] := by
    unfold framesL; rw [tFT]
    have := framesL_pushFrame W lit (by rw [hft]; exact hL.frames0) (by rw [ha]; exact hT32)
    unfold framesL at this; rw [this, hft, ha, length_trailL]
  have eT : ∀ l, t.IsTrue l ↔ V.IsTrue l := by intro l; simp [IsTrue, hTA]
  have eF : ∀ l, t.IsFalse l ↔ V.IsFalse l := by intro l; simp [IsFalse, hTA]
  have eL : ∀ l, t.lvl l = V.lvl l := by intro l; simp [lvl, hTA]
  have eTr : t.trailL = s.trailL ++ [lit] := by
    rw [show t.trailL = V.trailL by simp [trailL, hTA], ← hV, assign_trailL]
  have hsz := hs.core.sizes
  have hVT : ∀ l, V.IsTrue l ↔ (l = lit ∨ (l ≠ NOT lit ∧ s.IsTrue l)) := by
    intro l; rw [← hV]; exact assign_isTrue hsz hx l
  have hVL : ∀ l, V.lvl l = if IDX l = IDX lit then W.level.toNat else s.lvl l := by
    intro l; rw [← hV]; exact assign_lvl hsz hx l
  -- pushLevel on old positions
  have hpushOld : ∀ p, p < s.trailL.length → t.pushLevel p = s.pushLevel p := by
    intro p hp; unfold pushLevel; rw [hframes, List.countP_append]
    simp; omega
  have hpushNew : t.pushLevel s.trailL.length = s.level.toNat + 1 := by
    unfold pushLevel; rw [hframes, List.countP_append, ← hL.len, List.countP_eq_length.mpr]
    · simp
    · intro f hf; have := hL.framesLt f hf; simp; omega
  have hlevel : t.LevelOK := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l htl
      rw [eT, hVT] at htl; rw [eL, hVL, tLv]
      have : (s.level + 1).toNat = s.level.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
      rw [this]; split
      · omega
      · rcases htl with rfl | ⟨_, htl⟩
        · exact absurd rfl ‹_›
        · have := hL.trueLe l htl; omega
    · intro p l hpl
      rw [eTr] at hpl
      by_cases hp : p < s.trailL.length
      · rw [List.getElem?_append_left hp] at hpl
        have hlt : s.IsTrue l := hs.core.trailTrue l (List.mem_of_getElem? hpl)
        rw [hpushOld p hp, eL, hVL]
        have hne : IDX l ≠ IDX lit := by
          intro e
          rcases (IDX_eq_iff l lit).mp e with rfl | rfl
          · exact hun.1 hlt
          · have := (hs.core.valCons (NOT lit)).1.mp hlt; rw [NOT_NOT] at this; exact hun.2 this
        rw [if_neg hne]; exact hL.pushLe p l hpl
      · rw [List.getElem?_append_right (by omega)] at hpl
        have hp' : p = s.trailL.length := by
          have := (List.getElem?_eq_some_iff.mp hpl).1; simp at this; omega
        subst hp'
        simp at hpl; subst hpl
        rw [hpushNew, eL, hVL, if_pos rfl, hkN]; exact Nat.le_refl _
    · rw [hframes]; refine List.pairwise_append.mpr ⟨hL.sorted, by simp, ?_⟩
      intro a ha' b hb; simp at hb; subst hb; exact Nat.le_of_lt (hL.framesLt a ha')
    · rw [hframes, tLv]; simp [hL.len]; omega
    · intro f hf; rw [hframes] at hf; rw [tP, hp]
      rcases List.mem_append.mp hf with hf | hf
      · exact Nat.le_of_lt (hL.framesLt f hf)
      · simp at hf; omega
    · rw [tP, eTr, hp]; simp
    · rw [hframes]; refine List.pairwise_append.mpr ⟨hL.strict, by simp, ?_⟩
      intro a ha' b hb; simp at hb; subst hb; exact hL.framesLt a ha'
    · intro f hf; rw [hframes] at hf; rw [eTr]
      rcases List.mem_append.mp hf with hf | hf
      · have := hL.framesLt f hf; simp; omega
      · simp at hf; simp; omega
    · rw [tFT]; unfold pushFrame; simp [U32Vec.size_push]
  have eLive : ∀ r, t.LiveRef r ↔ V.LiveRef r := by intro r; simp [LiveRef, refsL, tA, hVs.1]
  have eCl : ∀ r, t.clauseL r = V.clauseL r := by intro r; simp [clauseL, tA, hVs.1]
  have eB : ∀ a b, t.BinWatched a b ↔ V.BinWatched a b := by
    intro a b; simp [BinWatched, entries, watchesOf, tW, hVs.2.1]
  have hdb : ∀ c, t.InDB c ↔ s.InDB c := inDB_congr tW tA
  have hsinv : SInv Φ t := by
    refine ⟨core_congr hTA (by rw [tVr, hVs.2.2.2.1]) c1, hlevel,
      WatchStruct.congr tW tA tD tVr hs.ws, by rw [tA]; exact hs.layout,
      reasonOK_transfer hTA eLive eCl eB j1, rootImplied_transfer hTA j2, ?_,
      fun c hc => hs.db c ((hdb c).mp hc), by rw [tO]; exact hs.jump⟩
    have := j3; unfold ReasonSizes at *
    rw [hTA, tVr, ← hVs.2.2.2.1, show t.trailL = V.trailL by simp [trailL, hTA]]; exact this
  refine ⟨hsinv, fun c hc => ?_, ?_, ?_, tLv, tC, tF, tVr⟩
  · -- the watch invariant at the (unchanged) propagation pointer
    have hV' := c3 s.propagate c hL.propLe (hinv c ((hdb c).mp hc))
    unfold InvS; rw [tP]
    intro w0 w1 rest hcw k0 k1 hp0 hp1
    have conv : ∀ w k, t.PropFalseAt s.propagate w k → V.PropFalseAt s.propagate w k := by
      intro w k ⟨hf, hr⟩
      refine ⟨(eF w).mp hf, ?_⟩
      rcases hr with ⟨q, hq, hqP, rfl⟩ | ⟨hn, h0, rfl⟩
      · left
        have hqs : q < s.trailL.length := by omega
        refine ⟨q, ?_, hqP, ?_⟩
        · rw [show V.trailL = t.trailL by simp [trailL, hTA]]; exact hq
        · rw [hpushOld q hqs]; rw [← hV]; rfl
      · right
        exact ⟨by rw [show V.trailL = t.trailL by simp [trailL, hTA]]; exact hn, by rw [← eL]; exact h0, rfl⟩
    obtain ⟨x, hxc, hxt, hxl⟩ := hV' w0 w1 rest hcw k0 k1 (conv _ _ hp0) (conv _ _ hp1)
    exact ⟨x, hxc, (eT x).mpr hxt, by rw [eL]; exact hxl⟩
  · apply IrrMono.of_large
    · intro r h1 h2
      refine ⟨by simpa [LiveRef, refsL, tA] using h1, by rw [tA]; exact h2,
        fun y hy => by simpa [clauseL, tA] using hy⟩
    · intro a b hab; simpa [BinWatched, entries, watchesOf, tW] using hab
    · intro l ⟨h1, h2⟩
      obtain ⟨g1, g2⟩ := withAssign_keep (probing := probing) (k := W.level) (binary := false)
        (reason := DECISION_REASON) hs.core hx hun h1
      rw [hV] at g1 g2
      exact ⟨(eT l).mpr g1, by rw [eL, g2, h2]⟩
  · intro j; rw [hTA, ← hV]; exact assign_bitsShrink _ _ _ _ _ _ j

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

macro "sf_rfl" : tactic => `(tactic| exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem sfr_of_fields {t s : Solver} (h1 : t.asg = s.asg) (h2 : t.arena = s.arena) (h3 : t.watches = s.watches)
    (h4 : t.delayed = s.delayed) (h5 : t.vars = s.vars) (h6 : t.level = s.level)
    (h7 : t.frameTrail = s.frameTrail) (h8 : t.propagate = s.propagate) (h9 : t.options = s.options)
    (h10 : t.clause = s.clause) (h11 : t.inconsistent = s.inconsistent) (h12 : t.watching = s.watching)
    (h13 : t.probing = s.probing) (h14 : t.importLit = s.importLit) (h15 : t.importBits = s.importBits) :
    SFr t s :=
  ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10, by simp only [Flg, h5, h9, h11, h12, h13, h14, h15], by rw [h1]⟩

@[simp] theorem conflictsPlus_asg (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.asg = s.asg := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_arena (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.arena = s.arena := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_watches (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.watches = s.watches := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_delayed (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.delayed = s.delayed := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_vars (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.vars = s.vars := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_level (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.level = s.level := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_frameTrail (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.frameTrail = s.frameTrail := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_propagate (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.propagate = s.propagate := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_options (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.options = s.options := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_clause (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.clause = s.clause := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_inconsistent (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.inconsistent = s.inconsistent := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_watching (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.watching = s.watching := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_probing (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.probing = s.probing := by
  unfold conflictsPlus; dsimp only; split <;> rfl

@[simp] theorem conflictsPlus_importLit (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.importLit = s.importLit := by
  unfold conflictsPlus; dsimp only; split <;> rfl
@[simp] theorem conflictsPlus_importBits (s : Solver) (d : UInt64) : (s.conflictsPlus d).2.importBits = s.importBits := by
  unfold conflictsPlus; dsimp only; split <;> rfl

macro "sf_fields" : tactic => `(tactic| (apply sfr_of_fields <;> ((try dsimp only); try simp only [conflictsPlus_asg,
  conflictsPlus_arena, conflictsPlus_watches, conflictsPlus_delayed, conflictsPlus_vars, conflictsPlus_level,
  conflictsPlus_frameTrail, conflictsPlus_propagate, conflictsPlus_options, conflictsPlus_clause,
  conflictsPlus_inconsistent, conflictsPlus_watching, conflictsPlus_probing, conflictsPlus_importLit,
  conflictsPlus_importBits])))

theorem startRandomSequence_sf (s : Solver) : SFr s.startRandomSequence s := by
  unfold startRandomSequence
  repeat' split
  all_goals first
    | sf_rfl
    | skip
  dsimp only
  split
  · sf_rfl
  · sf_fields

theorem randomPickLoop_sf : ∀ (fuel : Nat) (s : Solver), SFr (s.randomPickLoop fuel).2 s := by
  intro fuel
  induction fuel with
  | zero => intro s; exact SFr.refl _
  | succ n ih =>
    intro s
    unfold randomPickLoop
    have hd : SFr s.randomDraw.2 s := by unfold randomDraw; split; sf_rfl
    generalize s.randomDraw = D at hd ⊢
    obtain ⟨r, s'⟩ := D
    dsimp only at hd ⊢
    split
    · exact (ih _).trans hd
    · split
      · exact (ih _).trans hd
      · exact hd

theorem largestScoreLoop_sf : ∀ (fuel : Nat) (s : Solver), SFr (s.largestScoreLoop fuel).2 s := by
  intro fuel
  induction fuel with
  | zero => intro s; exact SFr.refl _
  | succ n ih =>
    intro s
    unfold largestScoreLoop
    dsimp only
    split
    · exact (ih _).trans (by sf_rfl)
    · exact SFr.refl _

theorem randomStart_sf (s : Solver) : ∀ x, s.randomStart = some x → SFr x s := by
  intro x hx
  unfold randomStart at hx
  repeat' split at hx
  all_goals cases hx
  all_goals first | exact startRandomSequence_sf s | exact SFr.refl _

theorem nextRandomDecision_sf (s : Solver) : SFr s.nextRandomDecision.2 s := by
  unfold nextRandomDecision
  have hr := randomStart_sf s
  generalize s.randomStart = r at hr
  repeat' split
  all_goals first
    | exact SFr.refl _
    | exact (randomPickLoop_sf _ _).trans (hr _ rfl)

theorem nextDecisionVariable_sf (s : Solver) : SFr s.nextDecisionVariable.2 s := by
  unfold nextDecisionVariable
  have h1 := nextRandomDecision_sf s
  generalize s.nextRandomDecision = R at h1 ⊢
  obtain ⟨res, s1⟩ := R
  dsimp only at h1 ⊢
  split
  · split
    · exact (largestScoreLoop_sf _ _).trans h1
    · exact (show SFr _ s1 by sf_rfl).trans h1
  · exact h1

theorem IDX_LIT_toNat (idx : UInt32) (h : idx.toNat < 2 ^ 31) : (IDX (LIT idx)).toNat = idx.toNat := by
  rw [IDX_toNat]; unfold LIT
  rw [UInt32.toNat_shiftLeft]; simp; omega

/-- An unassigned literal of an unassigned variable. -/
theorem unassigned_of_value {s : Solver} (hc : s.Core) {x : Lit} (hv : s.value x = 0) (b : Bool) :
    ¬ s.IsTrue (if b then x else NOT x) ∧ ¬ s.IsFalse (if b then x else NOT x) := by
  have hT : ¬ s.IsTrue x := by unfold IsTrue; unfold value at hv; rw [hv]; decide
  have hF : ¬ s.IsFalse x := by unfold IsFalse; unfold value at hv; rw [hv]; decide
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    constructor
    · intro h; have := (hc.valCons (NOT x)).1.mp h; rw [NOT_NOT] at this; exact hF this
    · intro h; exact hT ((hc.valCons x).1.mpr h)
  · simp only [ite_true]; exact ⟨hT, hF⟩

theorem decideOn_spec {Φ : (Nat → Bool) → Prop} {s W : Solver} (h : SearchInv Φ s)
    (hp : s.propagate = s.trailL.length) (hS : SFr W { s with level := s.level + 1 }) (idx : UInt32) :
    (W.decideOn idx).notPorted = true ∨ (SearchInv Φ (W.decideOn idx) ∧ IrrMono s (W.decideOn idx)) := by
  unfold decideOn
  split
  · left; rfl
  rename_i hchk
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hchk
  obtain ⟨hidx, hval⟩ := hchk
  right
  show SearchInv Φ ((W.pushFrame (if W.decidePhase idx then LIT idx else NOT (LIT idx))).assign W.probing W.level
      false (if W.decidePhase idx then LIT idx else NOT (LIT idx)) DECISION_REASON) ∧
    IrrMono s ((W.pushFrame (if W.decidePhase idx then LIT idx else NOT (LIT idx))).assign W.probing W.level
      false (if W.decidePhase idx then LIT idx else NOT (LIT idx)) DECISION_REASON)
  have ha : W.asg = s.asg := hS.same.asg
  have hv : W.vars = s.vars := hS.same.vars
  have hidx' : idx.toNat < s.vars.toNat := by
    rw [← hv]; exact UInt32.lt_iff_toNat_lt.mp (by simpa using hidx)
  have hsmall := h.inv.ws.varsBound
  have hvalid : ∀ b : Bool, s.ValidLit (if b then LIT idx else NOT (LIT idx)) := by
    intro b; unfold ValidLit; cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [IDX_NOT, IDX_LIT_toNat _ (by omega)]; exact hidx'
    · simp only [ite_true]; rw [IDX_LIT_toNat _ (by omega)]; exact hidx'
  have hval' : s.value (LIT idx) = 0 := by unfold value at *; rw [← ha]; simpa using hval
  have hun := unassigned_of_value h.inv.core hval' (W.decidePhase idx)
  obtain ⟨p1, p2, p3, p4, _, p6, p7, -⟩ := pushAssign_spec (W := W) h.inv h.invS hp ha hS.same.arena
    hS.same.watches hS.same.delayed hv hS.same.options hS.same.propagate hS.same.frameTrail hS.same.level
    (hvalid (W.decidePhase idx)) hun W.probing
  have hflg : Flg W = Flg s := hS.flg
  refine ⟨⟨p1, p2, clean_of_bits p4 h.clean, by rw [p6, hS.clause]; exact h.clauseEmpty,
    fun e => h.incons (by rw [← Flg.inconsistent (p7.trans hflg)]; exact e),
    by rw [Flg.watching (p7.trans hflg)]; exact h.watching, by rw [Flg.options (p7.trans hflg)]; exact h.opts,
    h.imp.flg (p7.trans hflg)⟩, p3⟩

theorem decide_eq (s : Solver) :
    s.decide = s.decideStart.nextDecisionVariable.2.decideOn s.decideStart.nextDecisionVariable.1 := rfl

theorem decide_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SearchInv Φ s)
    (hp : s.propagate = s.trailL.length) :
    s.decide.notPorted = true ∨ (SearchInv Φ s.decide ∧ IrrMono s s.decide) := by
  rw [decide_eq]
  apply decideOn_spec h hp
  refine (nextDecisionVariable_sf _).trans ?_
  unfold decideStart; split <;> sf_rfl

end Solver
end LeanKissat
