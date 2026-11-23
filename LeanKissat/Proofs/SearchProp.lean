import LeanKissat.Proofs.PropLit

/-!
# `searchPropagate`

The search invariant `SInv` and its preservation by the propagation loop.
-/

namespace LeanKissat
namespace Solver
open Arena

theorem countP_eq_le_one (n : Nat) : ∀ (L : List Nat), L.Nodup → L.countP (fun x => x == n) ≤ 1 := by
  intro L
  induction L with
  | nil => simp
  | cons x xs ih =>
    intro h
    rw [List.nodup_cons] at h
    by_cases e : x = n
    · subst e
      have : xs.countP (fun y => y == x) = 0 := by
        rw [List.countP_eq_zero]; intro y hy; simp; intro e; subst e; exact h.1 hy
      simp [this]
    · have := ih h.2; simp [e]; omega

theorem nodup_length_le : ∀ (n : Nat) (L : List Nat), L.Nodup → (∀ x ∈ L, x < n) → L.length ≤ n := by
  intro n
  induction n with
  | zero => intro L _ hl; cases L with
    | nil => simp
    | cons x _ => have := hl x (by simp); omega
  | succ n ih =>
    intro L hnd hl
    have h1 := ih (L.filter (fun x => x != n)) (hnd.filter _) (by
      intro x hx
      simp at hx
      have := hl x hx.1; omega)
    have h2 := List.length_eq_countP_add_countP (fun x => x != n) (l := L)
    have h3 := countP_eq_le_one n L hnd
    have h4 : L.countP (fun x => ¬ (x != n)) = L.countP (fun x => x == n) := by
      apply List.countP_congr; intro x _; simp
    rw [List.countP_eq_length_filter] at h2
    omega

/-- The base search invariant (the watch invariant is stated separately, relative to a
  propagation pointer). -/
structure SInv (Φ : (Nat → Bool) → Prop) (s : Solver) : Prop where
  core : s.Core
  levelOK : s.LevelOK
  ws : s.WatchStruct
  layout : s.arena.Layout
  reasons : s.ReasonOK
  roots : RootImplied Φ s
  rsizes : s.ReasonSizes
  db : DBImplied Φ s
  jump : s.options.jumpreasons = 0

theorem SInv.trail_le {Φ : (Nat → Bool) → Prop} {s : Solver} (h : SInv Φ s) :
    s.trailL.length ≤ s.vars.toNat := by
  have hnd := h.rsizes.2.2.2.2
  have := nodup_length_le s.vars.toNat ((s.trailL.map IDX).map UInt32.toNat)
    (List.Pairwise.map UInt32.toNat (fun a b hab e => hab (UInt32.toNat_inj.mp e)) hnd)
    (by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      exact h.rsizes.valid (h.core.trailTrue l hl))
  simpa using this

/-- Fields the invariants depend on. -/
structure Same (t s : Solver) : Prop where
  asg : t.asg = s.asg
  arena : t.arena = s.arena
  watches : t.watches = s.watches
  delayed : t.delayed = s.delayed
  vars : t.vars = s.vars
  level : t.level = s.level
  frameTrail : t.frameTrail = s.frameTrail
  propagate : t.propagate = s.propagate
  options : t.options = s.options

section Congr
variable {t s : Solver}

theorem Same.inDB (h : Same t s) (c : List Lit) : t.InDB c ↔ s.InDB c := by
  unfold InDB LiveRef refsL clauseL BinWatched entries watchesOf
  rw [h.arena, h.watches]

theorem Same.invSAt (h : Same t s) (P : Nat) (c : List Lit) : t.InvSAt P c ↔ s.InvSAt P c :=
  SameView.invSAt ⟨h.asg, h.arena, h.frameTrail, h.propagate, h.vars⟩ P c

theorem WatchStruct.congr (hw : t.watches = s.watches) (ha : t.arena = s.arena)
    (hd : t.delayed = s.delayed) (hv : t.vars = s.vars) (hW : s.WatchStruct) : t.WatchStruct := by
  have eE : t.entries = s.entries := by funext l; simp [entries, watchesOf, hw]
  have eLive : ∀ r, t.LiveRef r ↔ s.LiveRef r := by intro r; simp [LiveRef, refsL, ha]
  have eB : ∀ a b, t.BinWatched a b ↔ s.BinWatched a b := by intro a b; simp [BinWatched, eE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l; simp only [watchesOf, hw]; exact hW.words l
  · simp only [eE, refsL, lit0, lit1, clauseL, ha]; exact hW.refOK
  · intro r hr
    rw [eLive] at hr
    simp only [eE, lit0, lit1, clauseL, ValidLit, ha, hv]; exact hW.live r hr
  · intro a b hab
    rw [eB] at hab
    simp only [BinWatched, eE, ValidLit, hv]; exact hW.bin a b hab
  · rw [hd]; exact hW.delayed
  · rw [hw, hv]; exact hW.watchesSize
  · rw [hv]; exact hW.varsBound

theorem inDB_congr (hw : t.watches = s.watches) (ha : t.arena = s.arena) (c : List Lit) :
    t.InDB c ↔ s.InDB c := by
  unfold InDB LiveRef refsL clauseL BinWatched entries watchesOf
  rw [ha, hw]

/-- `Same` without the propagation pointer. -/
structure Same' (t s : Solver) : Prop where
  asg : t.asg = s.asg
  arena : t.arena = s.arena
  watches : t.watches = s.watches
  delayed : t.delayed = s.delayed
  vars : t.vars = s.vars
  level : t.level = s.level
  frameTrail : t.frameTrail = s.frameTrail
  options : t.options = s.options

theorem Same.same' (h : Same t s) : Same' t s :=
  ⟨h.asg, h.arena, h.watches, h.delayed, h.vars, h.level, h.frameTrail, h.options⟩

/-- All parts of `SInv` except `LevelOK` transfer along `Same'`. -/
theorem Same'.sinv {Φ : (Nat → Bool) → Prop} (h : Same' t s) (hs : SInv Φ s) (hl : t.LevelOK) :
    SInv Φ t := by
  have hcore : t.Core := by
    have e1 : ∀ l, t.IsTrue l ↔ s.IsTrue l := by intro l; simp [IsTrue, h.asg]
    have e2 : ∀ l, t.IsFalse l ↔ s.IsFalse l := by intro l; simp [IsFalse, h.asg]
    have e3 : ∀ l, t.lvl l = s.lvl l := by intro l; simp [lvl, h.asg]
    have e4 : t.trailL = s.trailL := by simp [trailL, h.asg]
    have hc := hs.core
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; rw [e1, e2, e2]; exact hc.valCons l
    · intro l hl; rw [e1] at hl; rw [e4, e3]; exact hc.trueOnTrail l hl
    · intro l hl; rw [e4] at hl; rw [e1]; exact hc.trailTrue l hl
    · intro l; rw [e3, e3]; exact hc.lvlVar l
    · unfold Sizes; rw [h.asg, h.vars]; exact hc.sizes
    · intro j; rw [h.asg]; exact hc.domain j
  have eTr : t.trailL = s.trailL := by simp [trailL, h.asg]
  have eE : t.entries = s.entries := by funext l; simp [entries, watchesOf, h.watches]
  have eLive : ∀ r, t.LiveRef r ↔ s.LiveRef r := by intro r; simp [LiveRef, refsL, h.arena]
  have eCl : ∀ r, t.clauseL r = s.clauseL r := by intro r; simp [clauseL, h.arena]
  have eB : ∀ a b, t.BinWatched a b ↔ s.BinWatched a b := by intro a b; simp [BinWatched, eE]
  have hdb : ∀ c, t.InDB c ↔ s.InDB c := by
    intro c; unfold InDB LiveRef refsL clauseL BinWatched entries watchesOf
    rw [h.arena, h.watches]
  have hW := hs.ws
  refine ⟨hcore, hl, ?_, by rw [h.arena]; exact hs.layout,
    reasonOK_transfer h.asg eLive eCl eB hs.reasons, rootImplied_transfer h.asg hs.roots, ?_, ?_,
    by rw [h.options]; exact hs.jump⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; simp only [watchesOf, h.watches]; exact hW.words l
    · simp only [eE, refsL, lit0, lit1, clauseL, h.arena]; exact hW.refOK
    · intro r hr
      rw [eLive] at hr
      simp only [eE, lit0, lit1, clauseL, ValidLit, h.arena, h.vars]; exact hW.live r hr
    · intro a b hab
      rw [eB] at hab
      simp only [BinWatched, eE, ValidLit, h.vars]; exact hW.bin a b hab
    · rw [h.delayed]; exact hW.delayed
    · rw [h.watches, h.vars]; exact hW.watchesSize
    · rw [h.vars]; exact hW.varsBound
  · have := hs.rsizes; unfold ReasonSizes at *; rw [h.asg, h.vars, eTr]; exact this
  · intro c hc; exact hs.db c ((hdb c).mp hc)

theorem Same.levelOK (h : Same t s) (hl : s.LevelOK) : t.LevelOK := by
  have eT : t.IsTrue = s.IsTrue := by funext l; simp [IsTrue, h.asg]
  have eL : t.lvl = s.lvl := by funext l; simp [lvl, h.asg]
  have eTr : t.trailL = s.trailL := by simp [trailL, h.asg]
  have eFr : t.framesL = s.framesL := by simp [framesL, h.frameTrail]
  have eP : t.pushLevel = s.pushLevel := by funext p; simp [pushLevel, eFr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eT, eL, h.level]; exact hl.trueLe
  · rw [eTr, eL, eP]; exact hl.pushLe
  · rw [eFr]; exact hl.sorted
  · rw [eFr, h.level]; exact hl.len
  · rw [eFr, h.propagate]; exact hl.framesLe
  · rw [eTr, h.propagate]; exact hl.propLe
  · rw [eFr]; exact hl.strict
  · rw [eFr, eTr]; exact hl.framesLt
  · rw [h.frameTrail]; exact hl.frames0

theorem Same.sinv {Φ : (Nat → Bool) → Prop} (h : Same t s) (hs : SInv Φ s) : SInv Φ t :=
  h.same'.sinv hs (h.levelOK hs.levelOK)

end Congr

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The clause database and the true literals of `s0` are preserved in `s`. -/
structure DBRel (s0 s : Solver) : Prop where
  live : ∀ r, s.LiveRef r ↔ s0.LiveRef r
  perm : ∀ r, s0.LiveRef r → (s.clauseL r).Perm (s0.clauseL r)
  word0 : ∀ r, s0.LiveRef r → s.arena.word0 r = s0.arena.word0 r
  bins : ∀ a b, s.BinWatched a b ↔ s0.BinWatched a b
  persist : ∀ l, s0.IsTrue l → s.IsTrue l ∧ s.lvl l = s0.lvl l

theorem DBRel.refl (s : Solver) : DBRel s s :=
  ⟨fun _ => Iff.rfl, fun _ _ => List.Perm.refl _, fun _ _ => rfl, fun _ _ => Iff.rfl,
   fun _ h => ⟨h, rfl⟩⟩

theorem DBRel.trans {a b c : Solver} (h1 : DBRel a b) (h2 : DBRel b c) : DBRel a c := by
  refine ⟨fun r => (h2.live r).trans (h1.live r), fun r hr => ?_, fun r hr => ?_,
    fun x y => (h2.bins x y).trans (h1.bins x y), fun l hl => ?_⟩
  · exact (h2.perm r ((h1.live r).mpr hr)).trans (h1.perm r hr)
  · rw [h2.word0 r ((h1.live r).mpr hr), h1.word0 r hr]
  · obtain ⟨h3, h4⟩ := h1.persist l hl
    obtain ⟨h5, h6⟩ := h2.persist l h3
    exact ⟨h5, h6.trans h4⟩

theorem DBRel.dbImplied {Φ : (Nat → Bool) → Prop} {s0 s : Solver} (h : DBRel s0 s)
    (hdb : DBImplied Φ s0) : DBImplied Φ s := by
  intro c hc
  rcases (inDB_iff _ c).mp hc with ⟨r, hl, rfl⟩ | ⟨x, y, hxy, rfl⟩
  · have hl0 := (h.live r).mp hl
    exact (hdb _ ((inDB_iff _ _).mpr (Or.inl ⟨r, hl0, rfl⟩))).perm
      (fun x hx => (h.perm r hl0).mem_iff.mpr hx)
  · exact hdb _ ((inDB_iff _ _).mpr (Or.inr ⟨x, y, (h.bins x y).mp hxy, rfl⟩))

theorem PropOut.dbrel {Φ : (Nat → Bool) → Prop} {s0 : Solver} {i : Nat} {s1 : Solver}
    {res : Option CRef} (h : PropOut Φ s0 i s1 res) : DBRel s0 s1 :=
  ⟨h.live, h.perm, h.word0, h.bins, h.persist⟩

theorem trailL_getElem? (s : Solver) (i : Nat) (h : i < s.asg.trail.size) :
    s.trailL[i]? = some (s.asg.trail.get! i) := by
  unfold trailL
  rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using h)]
  rfl

theorem length_trailL (s : Solver) : s.trailL.length = s.asg.trail.size := by
  simp [trailL]

theorem propLit_step {Φ : (Nat → Bool) → Prop} {s : Solver} {i : Nat} (hs : SInv Φ s)
    (hi : i < s.asg.trail.size) (hp : s.propagate ≤ i) (hinv : ∀ c, s.InDB c → s.InvSAt i c) :
    PropOut Φ s i (s.propagateLiteral none false (s.asg.trail.get! i)).1
      (s.propagateLiteral none false (s.asg.trail.get! i)).2 ∧
    SInv Φ (s.propagateLiteral none false (s.asg.trail.get! i)).1 := by
  have hat := trailL_getElem? s i hi
  have hctx : Ctx s i (s.asg.trail.get! i) :=
    ⟨hs.core, hs.levelOK, hs.ws, hs.layout, hat, hp, hinv,
     hs.rsizes.valid (hs.core.trailTrue _ (List.mem_of_getElem? hat))⟩
  have po := propagateLiteral_spec (Φ := Φ) hctx ⟨hs.reasons, hs.roots, hs.db, hs.rsizes⟩ hs.jump
  refine ⟨po, po.core, po.levelOK, po.ws, po.layout, po.reasons, po.roots, po.rsizes,
    po.dbrel.dbImplied hs.db, by rw [po.frame.options]; exact hs.jump⟩

theorem searchPropagateLoop_spec {Φ : (Nat → Bool) → Prop} (bound : Nat) (s : Solver) (i : Nat) :
    SInv Φ s → bound = s.vars.toNat → s.propagate ≤ i → i ≤ s.trailL.length →
    (∀ c, s.InDB c → s.InvSAt i c) →
    let r := searchPropagateLoop bound s i
    SInv Φ r.1 ∧ Frame r.1 s ∧ BitsShrink r.1.asg s.asg ∧
    ((∀ n, 2 * n ≤ s.asg.values.size → ActOK s.flags s.asg.values n → ActOK r.1.flags r.1.asg.values n) ∧
      r.1.asg.values.size = s.asg.values.size) ∧
    DBRel s r.1 ∧ (∃ ext, r.1.trailL = s.trailL ++ ext) ∧ i ≤ r.2.2 ∧
    (r.2.1 = none → r.2.2 = r.1.trailL.length ∧ ∀ c, r.1.InDB c → r.1.InvSAt r.2.2 c) ∧
    (∀ c, r.2.1 = some c → ConflictOK r.1 r.1 c ∧ i < r.2.2 ∧ r.2.2 ≤ r.1.trailL.length ∧
      ∀ d, r.1.InDB d → r.1.InvSAt (r.2.2 - 1) d) := by
  fun_induction searchPropagateLoop bound s i with
  | case1 s i hi lit s' res hpl hres =>
    intro hs hb hp hil hinv
    obtain ⟨po, _⟩ := propLit_step hs hi.1 hp hinv
    simp only [lit, hpl] at po
    obtain ⟨ext, hext⟩ := po.trail
    refine ⟨?_, po.frame, po.bits, ⟨po.act, po.vsize⟩, po.dbrel, po.trail, by simp, fun h => by simp only at h; simp [h] at hres,
      fun c hc => ?_⟩
    · have := propLit_step hs hi.1 hp hinv
      simp only [lit, hpl] at this
      exact this.2
    · simp only at hc ⊢
      refine ⟨po.conflict c hc, by omega, ?_, by simpa using po.invC⟩
      rw [hext]; simp; have := length_trailL s; omega
  | case2 s i hi lit s' res hpl hres ih =>
    intro hs hb hp hil hinv
    obtain ⟨po, hs'⟩ := propLit_step hs hi.1 hp hinv
    simp only [lit, hpl] at po hs'
    have hres' : res = none := by simpa using hres
    obtain ⟨ext, hext⟩ := po.trail
    obtain ⟨h1, h2, hb2, ⟨ha2, hv2⟩, h3, ⟨ext2, h4⟩, h45, h5, h6⟩ := ih hs' (by rw [po.frame.vars]; exact hb)
      (by rw [po.frame.propagate]; omega)
      (by rw [hext]; simp; have := length_trailL s; omega)
      (po.invN hres')
    exact ⟨h1, h2.trans po.frame, po.bits.trans hb2,
      ⟨fun n hn ha => ha2 n (by rw [po.vsize]; exact hn) (po.act n hn ha), hv2.trans po.vsize⟩,
      po.dbrel.trans h3, ⟨ext ++ ext2, by rw [h4, hext]; simp⟩,
      by omega, h5, fun c hc => by obtain ⟨a, b, c', d⟩ := h6 c hc; exact ⟨a, by omega, c', d⟩⟩
  | case3 s i hi =>
    intro hs hb hp hil hinv
    refine ⟨hs, Frame.refl _, BitsShrink.refl _, ⟨fun _ _ h => h, rfl⟩, DBRel.refl _, ⟨[], by simp⟩, Nat.le_refl _, fun _ => ⟨?_, hinv⟩,
      fun c hc => by simp at hc⟩
    have := hs.trail_le
    have := length_trailL s
    simp only
    omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem conflictOK_congr {t s : Solver} (h : Same' t s) (h0 : t.conflictLit0 = s.conflictLit0)
    (h1 : t.conflictLit1 = s.conflictLit1) (c : CRef) (hc : ConflictOK s s c) : ConflictOK t t c := by
  have eF : t.IsFalse = s.IsFalse := by funext l; simp [IsFalse, h.asg]
  have eE : t.entries = s.entries := by funext l; simp [entries, watchesOf, h.watches]
  have eLive : ∀ r, t.LiveRef r ↔ s.LiveRef r := by intro r; simp [LiveRef, refsL, h.arena]
  have eCl : ∀ r, t.clauseL r = s.clauseL r := by intro r; simp [clauseL, h.arena]
  cases c with
  | binConflict =>
    obtain ⟨a1, a2, a3⟩ := hc
    refine ⟨?_, ?_, ?_⟩ <;> simp only [h0, h1, eF]
    · simp only [BinWatched, eE]; exact a1
    · exact a2
    · exact a3
  | large r =>
    obtain ⟨a1, a2⟩ := hc
    exact ⟨(eLive r).mpr a1, fun x hx => by rw [eF]; rw [eCl] at hx; exact a2 x hx⟩

/-- Flushing the trail at the root level. -/
theorem flush_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) (h0 : s.level = 0)
    (hinv : ∀ c, s.InDB c → s.InvSAt s.trailL.length c) :
    SInv Φ s.flushTrail ∧ DBRel s s.flushTrail ∧ s.flushTrail.propagate = 0 ∧
    s.flushTrail.trailL = [] ∧ ∀ c, s.flushTrail.InDB c → s.flushTrail.InvSAt 0 c := by
  have hL := hs.levelOK
  have hframes : s.framesL = [] := by
    have := hL.len; rw [h0] at this; exact List.eq_nil_of_length_eq_zero this
  have hlv0 : ∀ l, s.IsTrue l → s.lvl l = 0 := by
    intro l hl; have := hL.trueLe l hl; rw [h0] at this; simpa using this
  have eT : s.flushTrail.IsTrue = s.IsTrue := rfl
  have eF : s.flushTrail.IsFalse = s.IsFalse := rfl
  have eL : s.flushTrail.lvl = s.lvl := rfl
  have eTr : s.flushTrail.trailL = [] := by
    simp [flushTrail, trailL, U32Vec.clear, U32Vec.view_shrink]
  have hc := hs.core
  have hdb : ∀ c, s.flushTrail.InDB c ↔ s.InDB c := inDB_congr (t := s.flushTrail) (s := s) rfl rfl
  refine ⟨⟨?_, ?_, WatchStruct.congr (t := s.flushTrail) (s := s) rfl rfl rfl rfl hs.ws, hs.layout, ?_, ?_, ?_, ?_, hs.jump⟩, ?_, rfl, eTr, ?_⟩
  · refine ⟨hc.valCons, fun l hl => Or.inr (hlv0 l hl), fun l hl => by rw [eTr] at hl; simp at hl,
      hc.lvlVar, hc.sizes, hc.domain⟩
  · refine ⟨hL.trueLe, fun p l hp => by rw [eTr] at hp; simp at hp, hL.sorted, hL.len,
      fun f hf => by
        have : f ∈ s.framesL := hf
        rw [hframes] at this; simp at this, Nat.zero_le _,
      by show s.framesL.Pairwise _; rw [hframes]; simp,
      fun f hf => by
        have : f ∈ s.framesL := hf
        rw [hframes] at this; simp at this, hL.frames0⟩
  · intro l hl hlv; rw [eL, hlv0 l hl] at hlv; simp at hlv
  · exact hs.roots
  · have := hs.rsizes
    refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, by rw [eTr]; simp⟩
  · intro c hc'; exact hs.db c ((hdb c).mp hc')
  · exact ⟨fun r => Iff.rfl, fun r _ => List.Perm.refl _, fun r _ => rfl, fun a b => Iff.rfl,
      fun l hl => ⟨hl, rfl⟩⟩
  · intro c hc' w0 w1 rs heq k0 k1 hf0 hf1
    have hP : ∀ w k, s.flushTrail.PropFalseAt 0 w k → s.PropFalseAt s.trailL.length w 0 ∧ k = 0 := by
      intro w k hf
      obtain ⟨hfw, ⟨p, _, hp, _⟩ | ⟨_, hlw, hk⟩⟩ := hf
      · omega
      · refine ⟨⟨hfw, ?_⟩, hk⟩
        by_cases hm : NOT w ∈ s.trailL
        · obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hm
          refine Or.inl ⟨p, hp, (List.getElem?_eq_some_iff.mp hp).1, ?_⟩
          unfold pushLevel; rw [hframes]; rfl
        · exact Or.inr ⟨hm, hlw, rfl⟩
    obtain ⟨g0, e0⟩ := hP w0 k0 hf0
    obtain ⟨g1, e1⟩ := hP w1 k1 hf1
    obtain ⟨t, ht, htt, hlt⟩ := hinv c ((hdb c).mp hc') w0 w1 rs heq 0 0 g0 g1
    subst e0 e1
    exact ⟨t, ht, htt, hlt⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem SInv.setProp {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {i : Nat}
    (h1 : s.propagate ≤ i) (h2 : i ≤ s.trailL.length) : SInv Φ { s with propagate := i } := by
  have hL := hs.levelOK
  refine Same'.sinv (t := { s with propagate := i }) (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hs ⟨hL.trueLe, hL.pushLe, hL.sorted,
    hL.len, fun f hf => Nat.le_trans (hL.framesLe f hf) h1, h2, hL.strict, hL.framesLt, hL.frames0⟩

/-- The tail of `searchPropagate` after the loop. -/
def searchPropFinish (saved : Nat) (r : Solver × Option CRef × Nat) : Solver × Option CRef :=
  match r with
  | (s, conflict, i) =>
    let s := { s with propagate := i }
    let s := s.updateSearchPropagationStatistics saved
    let s := s.updateConflictsAndTrail conflict true true
    let s := if conflict.isSome && s.randec != 0 then { s with randec := s.randec - 1 } else s
    (s, conflict)

theorem searchPropagate_eq (s : Solver) :
    s.searchPropagate = searchPropFinish s.propagate
      (searchPropagateLoop s.vars.toNat { s with ticks := 0 } s.propagate) := rfl

/-- Conclusions about `searchPropagate`. -/
structure SPOut (Φ : (Nat → Bool) → Prop) (s0 s : Solver) (res : Option CRef) : Prop where
  inv : SInv Φ s
  db : DBRel s0 s
  vars : s.vars = s0.vars
  level : s.level = s0.level
  frameTrail : s.frameTrail = s0.frameTrail
  importLit : s.importLit = s0.importLit
  options : s.options = s0.options
  none : res = none → s.propagate = s.trailL.length ∧ ∀ c, s.InDB c → s.InvS c
  some : ∀ c, res = some c → ConflictOK s s c ∧ 1 ≤ s.propagate ∧ s.propagate ≤ s.trailL.length ∧
    (∀ d, s.InDB d → s.InvSAt (s.propagate - 1) d) ∧ (s.level = 0 → s.inconsistent = true) ∧
    s0.propagate < s.propagate

theorem invSAt_congr {t s : Solver} (ha : t.asg = s.asg) (hf : t.frameTrail = s.frameTrail)
    (P : Nat) (c : List Lit) : t.InvSAt P c ↔ s.InvSAt P c := by
  have : t.PropFalseAt = s.PropFalseAt := by
    funext P w k; simp [PropFalseAt, IsFalse, trailL, lvl, pushLevel, framesL, ha, hf]
  simp only [InvSAt, this, IsTrue, lvl, ha]

/-- The statistics/conflict tail of `searchPropagate`. -/
def spTail (saved : Nat) (conflict : Option CRef) (s : Solver) : Solver × Option CRef :=
  let s := s.updateSearchPropagationStatistics saved
  let s := s.updateConflictsAndTrail conflict true true
  let s := if conflict.isSome && s.randec != 0 then { s with randec := s.randec - 1 } else s
  (s, conflict)

theorem searchPropFinish_eq (saved : Nat) (s2 : Solver) (c : Option CRef) (i : Nat) :
    searchPropFinish saved (s2, c, i) = spTail saved c { s2 with propagate := i } := rfl

theorem dbrel_same {t s : Solver} (h : Same' t s) : DBRel s t := by
  have eE : t.entries = s.entries := by funext l; simp [entries, watchesOf, h.watches]
  refine ⟨fun r => by simp [LiveRef, refsL, h.arena], fun r _ => by simp [clauseL, h.arena],
    fun r _ => by rw [h.arena], fun a b => by simp [BinWatched, eE], fun l hl => ?_⟩
  have e1 : t.IsTrue l = s.IsTrue l := by simp [IsTrue, h.asg]
  have e2 : t.lvl l = s.lvl l := by simp [lvl, h.asg]
  rw [e1, e2]; exact ⟨hl, rfl⟩

/-- Same fields and same `importLit`, conflict literals. -/
structure SameX (t s : Solver) : Prop where
  same : Same t s
  importLit : t.importLit = s.importLit
  c0 : t.conflictLit0 = s.conflictLit0
  c1 : t.conflictLit1 = s.conflictLit1

theorem spTail_none {Φ : (Nat → Bool) → Prop} (saved : Nat) (s : Solver) (hs : SInv Φ s)
    (hp : s.propagate = s.trailL.length) (hinv : ∀ c, s.InDB c → s.InvS c) :
    let t := (spTail saved none s).1
    SInv Φ t ∧ DBRel s t ∧ t.vars = s.vars ∧ t.level = s.level ∧ t.frameTrail = s.frameTrail ∧
    t.importLit = s.importLit ∧ t.options = s.options ∧ t.propagate = t.trailL.length ∧
    ∀ c, t.InDB c → t.InvS c := by
  intro t
  generalize hs4 : s.updateSearchPropagationStatistics saved = s4
  have h4 : SameX s4 s := by rw [← hs4]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  have ht : t = s4.updateConflictsAndTrail none true true := by
    simp only [t, spTail, hs4, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ite_false]
  have hs4i := h4.same.sinv hs
  have hinv4 : ∀ c, s4.InDB c → s4.InvSAt s4.trailL.length c := by
    intro c hc
    rw [invSAt_congr h4.same.asg h4.same.frameTrail]
    have e : s4.trailL.length = s.propagate := by
      rw [show s4.trailL = s.trailL by simp [trailL, h4.same.asg]]; exact hp.symm
    rw [e]; exact hinv c ((h4.same.inDB c).mp hc)
  rw [ht]
  unfold updateConflictsAndTrail
  simp only
  split
  · rename_i hfl
    have hl0 : s4.level = 0 := by simp at hfl; exact hfl.1
    obtain ⟨f1, f2, f3, f4, f5⟩ := flush_spec hs4i hl0 hinv4
    refine ⟨f1, (dbrel_same h4.same.same').trans f2, ?_, ?_, ?_, ?_, ?_, by rw [f3, f4]; rfl,
      fun c hc => by unfold InvS; rw [f3]; exact f5 c hc⟩
    · exact h4.same.vars
    · exact h4.same.level
    · exact h4.same.frameTrail
    · exact h4.importLit
    · exact h4.same.options
  · refine ⟨hs4i, dbrel_same h4.same.same', h4.same.vars, h4.same.level, h4.same.frameTrail,
      h4.importLit, h4.same.options, ?_, ?_⟩
    · rw [h4.same.propagate, hp]; simp [trailL, h4.same.asg]
    · intro c hc; unfold InvS
      rw [invSAt_congr h4.same.asg h4.same.frameTrail, h4.same.propagate]
      exact hinv c ((h4.same.inDB c).mp hc)

theorem SameX.trans {a b c : Solver} (h1 : SameX a b) (h2 : SameX b c) : SameX a c :=
  ⟨⟨h1.same.asg.trans h2.same.asg, h1.same.arena.trans h2.same.arena,
    h1.same.watches.trans h2.same.watches, h1.same.delayed.trans h2.same.delayed,
    h1.same.vars.trans h2.same.vars, h1.same.level.trans h2.same.level,
    h1.same.frameTrail.trans h2.same.frameTrail, h1.same.propagate.trans h2.same.propagate,
    h1.same.options.trans h2.same.options⟩, h1.importLit.trans h2.importLit, h1.c0.trans h2.c0,
    h1.c1.trans h2.c1⟩

theorem uct_some (u : Solver) (c : CRef) :
    SameX (u.updateConflictsAndTrail (some c) true true) u ∧
    ((u.updateConflictsAndTrail (some c) true true).level = 0 →
      (u.updateConflictsAndTrail (some c) true true).inconsistent = true) := by
  unfold updateConflictsAndTrail
  simp only [ite_true]
  split
  · rename_i h
    refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, fun _ => rfl⟩
  · rename_i h
    refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, fun h' => ?_⟩
    exfalso; apply h; simpa using h'

theorem randec_same (u : Solver) (b : Bool) :
    SameX (if b then { u with randec := u.randec - 1 } else u) u ∧
    (if b then { u with randec := u.randec - 1 } else u).inconsistent = u.inconsistent := by
  split
  · exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl⟩
  · exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl⟩

theorem spTail_some {Φ : (Nat → Bool) → Prop} (saved : Nat) (s : Solver) (c : CRef) (hs : SInv Φ s)
    (hc : ConflictOK s s c) (h1 : 1 ≤ s.propagate) (h2 : s.propagate ≤ s.trailL.length)
    (hinv : ∀ d, s.InDB d → s.InvSAt (s.propagate - 1) d) :
    let t := (spTail saved (some c) s).1
    SInv Φ t ∧ DBRel s t ∧ t.vars = s.vars ∧ t.level = s.level ∧ t.frameTrail = s.frameTrail ∧
    t.importLit = s.importLit ∧ t.options = s.options ∧ ConflictOK t t c ∧ 1 ≤ t.propagate ∧
    t.propagate ≤ t.trailL.length ∧ (∀ d, t.InDB d → t.InvSAt (t.propagate - 1) d) ∧
    (t.level = 0 → t.inconsistent = true) ∧ t.propagate = s.propagate := by
  intro t
  generalize hs4 : s.updateSearchPropagationStatistics saved = s4
  have h4 : SameX s4 s := by rw [← hs4]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  generalize hs5 : s4.updateConflictsAndTrail (some c) true true = s5
  obtain ⟨h5, hinc5⟩ := uct_some s4 c
  rw [hs5] at h5 hinc5
  have ht : t = if (some c).isSome && s5.randec != 0 then { s5 with randec := s5.randec - 1 } else s5 := by
    simp only [t, spTail, hs4, hs5]
  obtain ⟨h6, hinc6⟩ := randec_same s5 ((some c).isSome && s5.randec != 0)
  rw [← ht] at h6 hinc6
  have hx : SameX t s := h6.trans (h5.trans h4)
  have hinc : t.level = 0 → t.inconsistent = true := by
    intro h0; rw [hinc6]; apply hinc5; rw [← h6.same.level]; exact h0
  have hS := hx.same
  refine ⟨hS.sinv hs, dbrel_same hS.same', hS.vars, hS.level, hS.frameTrail, hx.importLit, hS.options,
    conflictOK_congr hS.same' hx.c0 hx.c1 c hc, by rw [hS.propagate]; exact h1, ?_, ?_, hinc, hS.propagate⟩
  · rw [hS.propagate, show t.trailL = s.trailL by simp [trailL, hS.asg]]; exact h2
  · intro d hd
    rw [invSAt_congr hS.asg hS.frameTrail, hS.propagate]
    exact hinv d ((hS.inDB d).mp hd)

theorem searchPropagate_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s)
    (hinv : ∀ c, s.InDB c → s.InvS c) :
    SPOut Φ s s.searchPropagate.1 s.searchPropagate.2 := by
  rw [searchPropagate_eq]
  have hs1 : SInv Φ { s with ticks := 0 } :=
    Same.sinv (t := { s with ticks := 0 }) (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hs
  have L := searchPropagateLoop_spec (Φ := Φ) s.vars.toNat { s with ticks := 0 } s.propagate hs1 rfl
    (Nat.le_refl _) hs.levelOK.propLe hinv
  have hdbT : DBRel s ({ s with ticks := 0 } : Solver) :=
    ⟨fun _ => Iff.rfl, fun _ _ => List.Perm.refl _, fun _ _ => rfl, fun _ _ => Iff.rfl,
     fun _ h => ⟨h, rfl⟩⟩
  have hfrT : Frame ({ s with ticks := 0 } : Solver) s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hlenT : ({ s with ticks := 0 } : Solver).trailL = s.trailL := rfl
  generalize searchPropagateLoop s.vars.toNat { s with ticks := 0 } s.propagate = r at L ⊢
  obtain ⟨s2, conflict, i⟩ := r
  obtain ⟨h1, hfr, -, -, hdb, ⟨ext, hext⟩, hge, hnone, hsome⟩ := L
  simp only at h1 hfr hdb hext hge hnone hsome
  rw [hlenT] at hext
  have hfr2 := hfr.trans hfrT
  have hdb2 := hdbT.trans hdb
  rw [searchPropFinish_eq]
  have hlen : s.trailL.length ≤ s2.trailL.length := by rw [hext]; simp
  have hp0 := hs.levelOK.propLe
  generalize hs3 : ({ s2 with propagate := i } : Solver) = s3
  have e3 : Same' s3 s2 := by rw [← hs3]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have e3i : s3.importLit = s2.importLit := by rw [← hs3]
  have e3p : s3.propagate = i := by rw [← hs3]
  have hdb3 : DBRel s s3 := hdb2.trans (dbrel_same e3)
  have htr3 : s3.trailL = s2.trailL := by simp [trailL, e3.asg]
  cases conflict with
  | none =>
    obtain ⟨hi, hinvi⟩ := hnone rfl
    have hs3i : SInv Φ s3 := by
      rw [← hs3]; exact h1.setProp (by rw [hfr2.propagate]; omega) (by omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := spTail_none s.propagate s3 hs3i
      (by rw [e3p, htr3]; exact hi)
      (fun c hc => by
        unfold InvS; rw [invSAt_congr e3.asg e3.frameTrail, e3p]
        exact hinvi c ((inDB_congr e3.watches e3.arena c).mp hc))
    refine ⟨g1, hdb3.trans g2, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨g8, g9⟩, fun c hc => by
      simp [spTail] at hc⟩
    · rw [g3, e3.vars, hfr2.vars]
    · rw [g4, e3.level, hfr2.level]
    · rw [g5, e3.frameTrail, hfr2.frameTrail]
    · rw [g6, e3i, hfr2.importLit]
    · rw [g7, e3.options, hfr2.options]
  | some c =>
    obtain ⟨hc, hi1, hi2, hinvi⟩ := hsome c rfl
    have hs3i : SInv Φ s3 := by
      rw [← hs3]; exact h1.setProp (by rw [hfr2.propagate]; omega) hi2
    have hc3 : ConflictOK s3 s3 c := conflictOK_congr e3 (by rw [← hs3]) (by rw [← hs3]) c hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := spTail_some s.propagate s3 c hs3i hc3
      (by rw [e3p]; omega) (by rw [e3p, htr3]; exact hi2)
      (fun d hd => by
        rw [invSAt_congr e3.asg e3.frameTrail, e3p]
        exact hinvi d ((inDB_congr e3.watches e3.arena d).mp hd))
    refine ⟨g1, hdb3.trans g2, ?_, ?_, ?_, ?_, ?_, fun h => by simp [spTail] at h,
      fun c' hc' => ?_⟩
    · rw [g3, e3.vars, hfr2.vars]
    · rw [g4, e3.level, hfr2.level]
    · rw [g5, e3.frameTrail, hfr2.frameTrail]
    · rw [g6, e3i, hfr2.importLit]
    · rw [g7, e3.options, hfr2.options]
    · simp [spTail] at hc'; subst hc'; exact ⟨g8, g9, g10, g11, g12, by rw [g13, e3p]; exact hi1⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-! ### Monotonicity of the irredundant database (SAT direction) -/

/-- Every irredundant clause of `s` is satisfied at the root of `t` or subsumed by an
  irredundant clause of `t`; root-true literals stay root-true. -/
structure IrrMono (s t : Solver) : Prop where
  irr : ∀ d, s.InIrrDB d → (∃ x ∈ d, t.RootTrue x) ∨ ∃ d', t.InIrrDB d' ∧ ∀ x ∈ d', x ∈ d
  roots : ∀ l, s.RootTrue l → t.RootTrue l

theorem IrrMono.refl (s : Solver) : IrrMono s s :=
  ⟨fun d hd => Or.inr ⟨d, hd, fun _ h => h⟩, fun _ h => h⟩

theorem IrrMono.trans {a b c : Solver} (h1 : IrrMono a b) (h2 : IrrMono b c) : IrrMono a c := by
  refine ⟨fun d hd => ?_, fun l hl => h2.roots l (h1.roots l hl)⟩
  rcases h1.irr d hd with ⟨x, hx, hr⟩ | ⟨d', hd', hsub⟩
  · exact Or.inl ⟨x, hx, h2.roots x hr⟩
  · rcases h2.irr d' hd' with ⟨x, hx, hr⟩ | ⟨d'', hd'', hsub'⟩
    · exact Or.inl ⟨x, hsub x hx, hr⟩
    · exact Or.inr ⟨d'', hd'', fun x hx => hsub x (hsub' x hx)⟩

theorem redundant_of_word0 {a b : Arena} {r : Ref} (h : a.word0 r = b.word0 r) :
    a.redundant r = b.redundant r := by
  unfold Arena.redundant Arena.flag; rw [h]

/-- A general criterion: live irredundant clauses stay live irredundant with a subset
  of literals, binary watches persist, root-true literals persist. -/
theorem IrrMono.of_large {s t : Solver}
    (hl : ∀ r, s.LiveRef r → s.arena.redundant r = false →
      t.LiveRef r ∧ t.arena.redundant r = false ∧ ∀ x ∈ t.clauseL r, x ∈ s.clauseL r)
    (hb : ∀ a b, s.BinWatched a b → t.BinWatched a b)
    (hr : ∀ l, s.RootTrue l → t.RootTrue l) : IrrMono s t := by
  refine ⟨fun d hd => Or.inr ?_, hr⟩
  rcases hd with ⟨r, h1, h2, rfl⟩ | ⟨a, b, h1, rfl⟩
  · obtain ⟨g1, g2, g3⟩ := hl r h1 h2
    exact ⟨_, Or.inl ⟨r, g1, g2, rfl⟩, g3⟩
  · exact ⟨_, Or.inr ⟨a, b, hb a b h1, rfl⟩, fun _ h => h⟩

theorem IrrMono.of_eq {s t : Solver} (ha : t.asg = s.asg) (har : t.arena = s.arena)
    (hw : t.watches = s.watches) : IrrMono s t := by
  apply IrrMono.of_large
  · intro r h1 h2
    refine ⟨?_, by rw [har]; exact h2, fun x hx => by simpa [clauseL, har] using hx⟩
    simpa [LiveRef, refsL, har] using h1
  · intro a b h; simpa [BinWatched, entries, watchesOf, hw] using h
  · intro l h; simpa [RootTrue, IsTrue, lvl, ha] using h

theorem IrrMono.of_keep {s t : Solver} (har : t.arena = s.arena) (hw : t.watches = s.watches)
    (hal : t.asg.aLevel = s.asg.aLevel) (hk : ∀ l, s.IsTrue l → s.lvl l = 0 → t.IsTrue l) : IrrMono s t := by
  apply IrrMono.of_large
  · intro r h1 h2
    refine ⟨by simpa [LiveRef, refsL, har] using h1, by rw [har]; exact h2,
      fun x hx => by simpa [clauseL, har] using hx⟩
  · intro a b hab; simpa [BinWatched, entries, watchesOf, hw] using hab
  · intro l ⟨h1, h2⟩; exact ⟨hk l h1 h2, by simpa [lvl, hal] using h2⟩

theorem DBRel.irrMono {s t : Solver} (h : DBRel s t) : IrrMono s t := by
  apply IrrMono.of_large
  · intro r h1 h2
    refine ⟨(h.live r).mpr h1, ?_, fun x hx => (h.perm r h1).mem_iff.mp hx⟩
    rw [redundant_of_word0 (h.word0 r h1)]; exact h2
  · intro a b hab; exact (h.bins a b).mpr hab
  · intro l ⟨h1, h2⟩; obtain ⟨g1, g2⟩ := h.persist l h1; exact ⟨g1, g2.trans h2⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem spTail_side (saved : Nat) (c : Option CRef) (u : Solver) :
    (spTail saved c u).1.clause = u.clause ∧ (spTail saved c u).1.watching = u.watching ∧
    (spTail saved c u).1.probing = u.probing ∧ (spTail saved c u).1.asg.aBits = u.asg.aBits ∧
    (c = none → (spTail saved c u).1.inconsistent = u.inconsistent) ∧
    ((spTail saved c u).1.inconsistent = true → u.inconsistent = true ∨ u.level = 0) := by
  have key : ∀ t : Solver, t.clause = u.clause ∧ t.watching = u.watching ∧ t.probing = u.probing ∧
      t.asg.aBits = u.asg.aBits ∧ (c = none → t.inconsistent = u.inconsistent) →
      (t.inconsistent = true → u.inconsistent = true ∨ u.level = 0) →
      t.clause = u.clause ∧ t.watching = u.watching ∧ t.probing = u.probing ∧
      t.asg.aBits = u.asg.aBits ∧ (c = none → t.inconsistent = u.inconsistent) ∧
      (t.inconsistent = true → u.inconsistent = true ∨ u.level = 0) := fun _ h h' => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h'⟩
  have e : ∀ v : Solver, v.level = u.level → v.inconsistent = u.inconsistent →
      (if v.level == 0 then { v with inconsistent := true } else v).inconsistent = true →
      u.inconsistent = true ∨ u.level = 0 := by
    intro v h1 h2 h
    by_cases hl : u.level = 0
    · exact Or.inr hl
    · rw [ite_eq_right (by simp [h1, hl])] at h; left; rw [← h2]; exact h
  apply key
  · unfold spTail updateConflictsAndTrail
    cases c with
    | none =>
      dsimp only
      repeat' split
      all_goals exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
    | some c =>
      dsimp only
      repeat' split
      all_goals exact ⟨rfl, rfl, rfl, rfl, fun h => by simp at h⟩
  · unfold spTail updateConflictsAndTrail
    cases c with
    | none =>
      dsimp only
      intro h; left
      have : ∀ b : Bool, (if b then (u.updateSearchPropagationStatistics saved).flushTrail
          else u.updateSearchPropagationStatistics saved).inconsistent = u.inconsistent := by
        intro b; split <;> rfl
      rw [← this _]; exact h
    | some c =>
      intro h
      by_cases hl : u.level = 0
      · exact Or.inr hl
      · left
        have hl' : (u.level == 0) = false := by simpa using hl
        simp only [Option.isSome_some, Bool.true_and, updateSearchPropagationStatistics, hl', ite_true,
          ite_false, Bool.false_eq_true] at h
        revert h; split <;> exact fun h => h

/-- Fields of `searchPropagate` that the search invariant needs beyond `SPOut`. -/
theorem searchPropagate_side {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s)
    (hinv : ∀ c, s.InDB c → s.InvS c) :
    s.searchPropagate.1.clause = s.clause ∧ s.searchPropagate.1.watching = s.watching ∧
    s.searchPropagate.1.probing = s.probing ∧ BitsShrink s.searchPropagate.1.asg s.asg ∧
    (s.searchPropagate.2 = none → s.searchPropagate.1.inconsistent = s.inconsistent) ∧
    (s.searchPropagate.1.inconsistent = true → s.inconsistent = true ∨ s.searchPropagate.1.level = 0) := by
  rw [searchPropagate_eq]
  have L := searchPropagateLoop_spec (Φ := Φ) s.vars.toNat { s with ticks := 0 } s.propagate
    (Same.sinv (t := { s with ticks := 0 }) (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hs) rfl
    (Nat.le_refl _) hs.levelOK.propLe hinv
  generalize searchPropagateLoop s.vars.toNat { s with ticks := 0 } s.propagate = r at L ⊢
  obtain ⟨s2, conflict, i⟩ := r
  obtain ⟨-, hfr, hb, -, -⟩ := L
  rw [searchPropFinish_eq]
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := spTail_side s.propagate conflict { s2 with propagate := i }
  refine ⟨by rw [t1]; exact hfr.clause, by rw [t2]; exact hfr.watching, by rw [t3]; exact hfr.probing,
    fun j => by rw [t4]; exact hb j, fun h => by rw [t5 h]; exact hfr.inconsistent, fun h => ?_⟩
  have hlev : (spTail s.propagate conflict { s2 with propagate := i }).1.level = s2.level := by
    unfold spTail updateConflictsAndTrail; cases conflict <;> dsimp only <;> repeat' split
    all_goals rfl
  rcases t6 h with h' | h'
  · left; rw [← hfr.inconsistent]; exact h'
  · right; show (spTail s.propagate conflict { s2 with propagate := i }).1.level = 0
    rw [hlev]; exact h'

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem spTail_importBits (saved : Nat) (c : Option CRef) (u : Solver) :
    (spTail saved c u).1.importBits = u.importBits := by
  unfold spTail updateConflictsAndTrail; cases c <;> dsimp only <;> repeat' split
  all_goals rfl

theorem searchPropagate_importBits {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s)
    (hinv : ∀ c, s.InDB c → s.InvS c) : s.searchPropagate.1.importBits = s.importBits := by
  rw [searchPropagate_eq]
  have L := searchPropagateLoop_spec (Φ := Φ) s.vars.toNat { s with ticks := 0 } s.propagate
    (Same.sinv (t := { s with ticks := 0 }) (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hs) rfl
    (Nat.le_refl _) hs.levelOK.propLe hinv
  generalize searchPropagateLoop s.vars.toNat { s with ticks := 0 } s.propagate = r at L ⊢
  obtain ⟨s2, conflict, i⟩ := r
  obtain ⟨-, hfr, -⟩ := L
  rw [searchPropFinish_eq, spTail_importBits]
  exact hfr.importBits

theorem spTail_flags_values (saved : Nat) (c : Option CRef) (u : Solver) :
    (spTail saved c u).1.flags = u.flags ∧ (spTail saved c u).1.asg.values = u.asg.values := by
  unfold spTail updateConflictsAndTrail; cases c <;> dsimp only <;> repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem searchPropagate_act {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s)
    (hinv : ∀ c, s.InDB c → s.InvS c) (n : Nat) (hn : 2 * n ≤ s.asg.values.size)
    (ha : ActOK s.flags s.asg.values n) :
    ActOK s.searchPropagate.1.flags s.searchPropagate.1.asg.values n ∧
    s.searchPropagate.1.asg.values.size = s.asg.values.size := by
  rw [searchPropagate_eq]
  have L := searchPropagateLoop_spec (Φ := Φ) s.vars.toNat { s with ticks := 0 } s.propagate
    (Same.sinv (t := { s with ticks := 0 }) (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hs) rfl
    (Nat.le_refl _) hs.levelOK.propLe hinv
  generalize searchPropagateLoop s.vars.toNat { s with ticks := 0 } s.propagate = r at L ⊢
  obtain ⟨s2, conflict, i⟩ := r
  obtain ⟨-, -, -, ⟨h1, h2⟩, -⟩ := L
  rw [searchPropFinish_eq]
  obtain ⟨f1, f2⟩ := spTail_flags_values s.propagate conflict { s2 with propagate := i }
  rw [f1, f2]
  exact ⟨h1 n hn ha, h2⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem spTail_nf (saved : Nat) (c : Option CRef) (u : Solver) :
    (spTail saved c u).1.overflowed = u.overflowed ∧ (spTail saved c u).1.outOfResources = u.outOfResources ∧
    (spTail saved c u).1.notPorted = u.notPorted ∧ (spTail saved c u).1.marks = u.marks ∧
    (spTail saved c u).1.flags = u.flags := by
  unfold spTail updateConflictsAndTrail; cases c <;> dsimp only <;> repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem searchPropagate_nf {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s)
    (hinv : ∀ c, s.InDB c → s.InvS c) :
    s.searchPropagate.1.overflowed = s.overflowed ∧ s.searchPropagate.1.outOfResources = s.outOfResources ∧
    s.searchPropagate.1.notPorted = s.notPorted ∧ s.searchPropagate.1.marks = s.marks := by
  rw [searchPropagate_eq]
  have L := searchPropagateLoop_spec (Φ := Φ) s.vars.toNat { s with ticks := 0 } s.propagate
    (Same.sinv (t := { s with ticks := 0 }) (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hs) rfl
    (Nat.le_refl _) hs.levelOK.propLe hinv
  generalize searchPropagateLoop s.vars.toNat { s with ticks := 0 } s.propagate = r at L ⊢
  obtain ⟨s2, conflict, i⟩ := r
  obtain ⟨-, hfr, -⟩ := L
  rw [searchPropFinish_eq]
  obtain ⟨f1, f2, f3, f4, -⟩ := spTail_nf s.propagate conflict { s2 with propagate := i }
  rw [f1, f2, f3, f4]
  exact ⟨hfr.overflowed, hfr.outOfResources, hfr.notPorted, hfr.marks⟩

end Solver
end LeanKissat
