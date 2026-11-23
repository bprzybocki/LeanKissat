import LeanKissat.Proofs.PropJust

/-!
# `propagateLiteral` on the concrete solver
-/

namespace LeanKissat
namespace Solver
open Arena

/-- Fields untouched by propagation (other than the assignment, arena, watches). -/
structure Frame (s t : Solver) : Prop where
  vars : s.vars = t.vars
  level : s.level = t.level
  frameTrail : s.frameTrail = t.frameTrail
  propagate : s.propagate = t.propagate
  importLit : s.importLit = t.importLit
  options : s.options = t.options
  inconsistent : s.inconsistent = t.inconsistent
  clause : s.clause = t.clause
  watching : s.watching = t.watching
  probing : s.probing = t.probing
  importBits : s.importBits = t.importBits
  overflowed : s.overflowed = t.overflowed
  outOfResources : s.outOfResources = t.outOfResources
  notPorted : s.notPorted = t.notPorted
  marks : s.marks = t.marks

theorem Frame.refl (s : Solver) : Frame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {s t u : Solver} (h1 : Frame s t) (h2 : Frame t u) : Frame s u :=
  ⟨h1.vars.trans h2.vars, h1.level.trans h2.level, h1.frameTrail.trans h2.frameTrail,
   h1.propagate.trans h2.propagate, h1.importLit.trans h2.importLit, h1.options.trans h2.options,
   h1.inconsistent.trans h2.inconsistent, h1.clause.trans h2.clause, h1.watching.trans h2.watching,
   h1.probing.trans h2.probing, h1.importBits.trans h2.importBits, h1.overflowed.trans h2.overflowed,
   h1.outOfResources.trans h2.outOfResources, h1.notPorted.trans h2.notPorted, h1.marks.trans h2.marks⟩

theorem Frame.symm {s t : Solver} (h : Frame s t) : Frame t s :=
  ⟨h.vars.symm, h.level.symm, h.frameTrail.symm, h.propagate.symm, h.importLit.symm,
   h.options.symm, h.inconsistent.symm, h.clause.symm, h.watching.symm, h.probing.symm, h.importBits.symm,
   h.overflowed.symm, h.outOfResources.symm, h.notPorted.symm, h.marks.symm⟩

/-- Analysis bytes only lose bits (an assignment resets them to `0` or `binary`). -/
def BitsShrink (a' a : Asg) : Prop :=
  ∀ j, a'.aBits.get! j = a.aBits.get! j ∨ a'.aBits.get! j = 0 ∨ a'.aBits.get! j = ABits.binary

theorem BitsShrink.refl (a : Asg) : BitsShrink a a := fun _ => Or.inl rfl

theorem BitsShrink.trans {a b c : Asg} (h1 : BitsShrink b a) (h2 : BitsShrink c b) : BitsShrink c a := by
  intro j
  rcases h2 j with e | e | e
  · rw [e]; exact h1 j
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

theorem assign_bitsShrink (a : Asg) (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) :
    BitsShrink (a.assign probing k bb x rr) a := by
  intro j
  simp only [Asg.assign]
  rw [ByteArray.get!_set!]
  split
  · right
    have hv : ((bb.toUInt32 &&& (((k == 0).toUInt32 &&& ((rr == UNIT_REASON).toUInt32 ^^^ 1)) ^^^ 1)).toUInt8 <<< 1) = 0 ∨
        ((bb.toUInt32 &&& (((k == 0).toUInt32 &&& ((rr == UNIT_REASON).toUInt32 ^^^ 1)) ^^^ 1)).toUInt8 <<< 1) = 2 := by
      cases bb <;> cases (k == 0) <;> cases (rr == UNIT_REASON) <;> decide
    exact hv
  · left; rfl

theorem frame_markFixed (s : Solver) (l : Lit) : Frame (s.markFixedLiteral l) s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp [markFixedLiteral, deactivateVariable, setVarFlag]; try (split <;> rfl))

theorem PS.step_frame (probing jump : Bool) (lv : UInt32) (notLit : Lit) (st : PS) (e : WEntry) :
    Frame (PS.step probing jump lv notLit st e).s st.s := by
  cases e with
  | bin b =>
    unfold PS.step; simp only
    split
    · exact Frame.refl _
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only; split
      · exact frame_markFixed _ _
      · exact Frame.refl _
  | large b r =>
    unfold PS.step; simp only
    repeat' split
    all_goals first | exact Frame.refl _ | exact frame_markFixed _ _

theorem PS.run_frame (probing jump : Bool) (lv : UInt32) (notLit : Lit) :
    ∀ (es : List WEntry) (st : PS), Frame (PS.run probing jump lv notLit st es).s st.s := by
  intro es
  induction es with
  | nil => intro st; exact Frame.refl _
  | cons e es ih =>
    intro st
    unfold PS.run
    split
    · exact Frame.refl _
    · exact (ih _).trans (PS.step_frame _ _ _ _ _ _)

theorem PS.step_bits (probing jump : Bool) (lv : UInt32) (notLit : Lit) (st : PS) (e : WEntry) :
    BitsShrink (PS.step probing jump lv notLit st e).a st.a := by
  cases e with
  | bin b =>
    unfold PS.step; simp only
    split
    · exact BitsShrink.refl _
    split
    · exact BitsShrink.refl _
    · exact assign_bitsShrink _ _ _ _ _ _
  | large b r =>
    unfold PS.step; simp only
    repeat' split
    all_goals first | exact BitsShrink.refl _ | exact assign_bitsShrink _ _ _ _ _ _

theorem PS.run_bits (probing jump : Bool) (lv : UInt32) (notLit : Lit) :
    ∀ (es : List WEntry) (st : PS), BitsShrink (PS.run probing jump lv notLit st es).a st.a := by
  intro es
  induction es with
  | nil => intro st; exact BitsShrink.refl _
  | cons e es ih =>
    intro st
    unfold PS.run
    split
    · exact BitsShrink.refl _
    · exact (PS.step_bits _ _ _ _ _ _).trans (ih _)

/-- Every variable below `n` is active or assigned. -/
def ActOK (flags : U32Vec) (values : ByteArray) (n : Nat) : Prop :=
  ∀ v, v < n → (flags.get! v &&& VarFlags.active != 0) = true ∨ values.get! (2 * v) ≠ 0

theorem assign_values_mono (a : Asg) (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) (j : Nat)
    (h : a.values.get! j ≠ 0) : (a.assign probing k bb x rr).values.get! j ≠ 0 := by
  simp only [Asg.assign]
  rw [ByteArray.get!_set!, ByteArray.get!_set!]
  split
  · decide
  · split
    · decide
    · exact h

theorem assign_values_var (a : Asg) (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32)
    (hsz : x.toNat < a.values.size) (hsz' : (NOT x).toNat < a.values.size) :
    (a.assign probing k bb x rr).values.get! (2 * (IDX x).toNat) ≠ 0 := by
  rw [Asg.assign_values_get! _ _ _ _ _ _ _ hsz' hsz]
  have key : IDX x * 2 = x ∨ IDX x * 2 = NOT x := by unfold IDX NOT; bv_k
  have hm : (IDX x * 2).toNat = 2 * (IDX x).toNat := by
    rw [UInt32.toNat_mul]; have := IDX_toNat x; have := x.toNat_lt; simp; omega
  rw [← hm]
  rcases key with e | e
  · rw [e, ite_eq_right (lit_toNat_ne_not x), ite_eq_left rfl]; decide
  · rw [e, ite_eq_left rfl]; decide

theorem markFixedLiteral_flags_ne (s : Solver) (lit : Lit) (v : Nat) (hv : v ≠ (IDX lit).toNat) :
    (s.markFixedLiteral lit).flags.get! v = s.flags.get! v := by
  unfold markFixedLiteral deactivateVariable
  simp only [setVarFlag]
  split <;> simp only [U32Vec.get!_set!_ne _ _ _ _ (Ne.symm hv)]

theorem actOK_assign (s : Solver) (a : Asg) (n : Nat) (hsz : 2 * n ≤ a.values.size) (h : ActOK s.flags a.values n)
    (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) (mf : Bool) :
    ActOK (if mf then s.markFixedLiteral x else s).flags (a.assign probing k bb x rr).values n := by
  intro v hv
  by_cases e : v = (IDX x).toNat
  · right; subst e
    have hx : x.toNat < 2 * n := by have := IDX_toNat x; omega
    have hnx : (NOT x).toNat < 2 * n := by
      have := IDX_toNat (NOT x); rw [IDX_NOT] at this; omega
    exact assign_values_var a probing k bb x rr (by omega) (by omega)
  · have hf : (if mf then s.markFixedLiteral x else s).flags.get! v = s.flags.get! v := by
      split
      · exact markFixedLiteral_flags_ne s x v e
      · rfl
    rw [hf]
    rcases h v hv with h' | h'
    · exact Or.inl h'
    · exact Or.inr (assign_values_mono a probing k bb x rr _ h')

theorem assign_values_size (a : Asg) (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) :
    (a.assign probing k bb x rr).values.size = a.values.size := by
  simp [Asg.assign]

theorem PS.step_shape (probing jump : Bool) (lv : UInt32) (notLit : Lit) (st : PS) (e : WEntry) :
    ((PS.step probing jump lv notLit st e).s.flags = st.s.flags ∧ (PS.step probing jump lv notLit st e).a = st.a) ∨
    (∃ (x : Lit) (k : UInt32) (bb : Bool) (rr : UInt32), (PS.step probing jump lv notLit st e).s = st.s ∧
      (PS.step probing jump lv notLit st e).a = st.a.assign probing k bb x rr) ∨
    (∃ (x : Lit) (k : UInt32) (bb : Bool) (rr : UInt32),
      (PS.step probing jump lv notLit st e).s = st.s.markFixedLiteral x ∧
      (PS.step probing jump lv notLit st e).a = st.a.assign probing k bb x rr) := by
  cases e with
  | bin b =>
    unfold PS.step; simp only
    split
    · exact Or.inl ⟨rfl, rfl⟩
    split
    · exact Or.inl ⟨rfl, rfl⟩
    · dsimp only
      split
      · exact Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl⟩)
  | large b r =>
    unfold PS.step; simp only
    repeat' split
    all_goals first
      | exact Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl⟩)
      | exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl⟩)
      | exact Or.inl ⟨rfl, rfl⟩

theorem PS.step_active (probing jump : Bool) (lv : UInt32) (notLit : Lit) (st : PS) (e : WEntry) (n : Nat)
    (hsz : 2 * n ≤ st.a.values.size) (h : ActOK st.s.flags st.a.values n) :
    ActOK (PS.step probing jump lv notLit st e).s.flags (PS.step probing jump lv notLit st e).a.values n ∧
    (PS.step probing jump lv notLit st e).a.values.size = st.a.values.size := by
  rcases PS.step_shape probing jump lv notLit st e with ⟨e1, e2⟩ | ⟨x, k, bb, rr, e1, e2⟩ | ⟨x, k, bb, rr, e1, e2⟩
  · rw [e1, e2]; exact ⟨h, rfl⟩
  · rw [e1, e2]; exact ⟨actOK_assign st.s st.a n hsz h _ _ _ _ _ false, assign_values_size _ _ _ _ _ _⟩
  · rw [e1, e2]; exact ⟨actOK_assign st.s st.a n hsz h _ _ _ _ _ true, assign_values_size _ _ _ _ _ _⟩

theorem PS.run_active (probing jump : Bool) (lv : UInt32) (notLit : Lit) (n : Nat) :
    ∀ (es : List WEntry) (st : PS), 2 * n ≤ st.a.values.size → ActOK st.s.flags st.a.values n →
      ActOK (PS.run probing jump lv notLit st es).s.flags (PS.run probing jump lv notLit st es).a.values n := by
  intro es
  induction es with
  | nil => intro st _ h; exact h
  | cons e es ih =>
    intro st hsz h
    unfold PS.run
    split
    · exact h
    · obtain ⟨h1, h2⟩ := PS.step_active probing jump lv notLit st e n hsz h
      exact ih _ (by rw [h2]; exact hsz) h1

/-- Delayed entries targeting watch list index `j`. -/
def delayedAt (dl : List (Lit × Lit × Ref)) (j : Nat) : List WEntry :=
  dl.filterMap (fun x => if x.1.toNat = j then some (.large x.2.1 x.2.2) else none)

theorem delayedAt_eq (dl : List (Lit × Lit × Ref)) (l : Lit) : delayedAt dl l.toNat = delayedFor dl l := by
  unfold delayedAt delayedFor
  congr 1; funext x
  by_cases h : x.1 = l
  · simp [h]
  · have : x.1.toNat ≠ l.toNat := fun e => h (UInt32.toNat_inj.mp e)
    simp [h, this]

theorem blockingWatch_idem (x : Lit) : blockingWatch (watchLit (blockingWatch x)) = blockingWatch x := by
  simp only [blockingWatch, watchLit]; bv_k

theorem wld_spec (d : U32Vec) (wss : Array WVec) (k : Nat) :
    ∀ dl, d.view.drop k = flatDelayed dl → (∀ x ∈ dl, x.1.toNat < wss.size) →
    (watchLargeDelayedLoop d wss k).size = wss.size ∧
    ∀ j, j < wss.size → (watchLargeDelayedLoop d wss k)[j]!.data.toList =
      wss[j]!.data.toList ++ encodeWatches (delayedAt dl j) := by
  fun_induction watchLargeDelayedLoop d wss k with
  | case1 wss k hk lit w ref wss' ih =>
    intro dl hdrop hval
    have hlen : k + 2 < d.view.length := by simpa using hk
    rw [List.drop_eq_getElem_cons (by omega : k < d.view.length),
      List.drop_eq_getElem_cons (by omega : k + 1 < d.view.length),
      List.drop_eq_getElem_cons (by omega : k + 2 < d.view.length)] at hdrop
    cases dl with
    | nil => exact absurd hdrop (by simp [flatDelayed]; omega)
    | cons x dl' =>
      simp only [flatDelayed, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq] at hdrop
      obtain ⟨e0, e1, e2, erest⟩ := hdrop
      have hlit : lit = x.1 := by
        simp only [lit, U32Vec.get!_eq_view]; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < d.view.length), Option.getD_some]; exact e0
      have hw : w = blockingWatch x.2.1 := by
        simp only [w, U32Vec.get!_eq_view]; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k + 1 < d.view.length), Option.getD_some]; exact e1
      have href : ref = x.2.2 := by
        simp only [ref, U32Vec.get!_eq_view]; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k + 2 < d.view.length), Option.getD_some]; exact e2
      have hsz : wss'.size = wss.size := by simp [wss']
      obtain ⟨ih1, ih2⟩ := ih dl' (by simpa [flatDelayed] using erest) (fun y hy => by
        rw [hsz]; exact hval y (List.mem_cons_of_mem _ hy))
      refine ⟨ih1.trans hsz, fun j hj => ?_⟩
      rw [ih2 j (by rw [hsz]; exact hj)]
      have hx := hval x (List.mem_cons_self ..)
      have hmod : wss'[j]! = if lit.toNat = j then
          (wss[j]!.push (blockingWatch (watchLit w))).push (largeWatch ref) else wss[j]! := by
        simp only [wss']
        simp [Array.getElem_modify, hj]
      rw [hmod]
      unfold delayedAt
      by_cases e : x.1.toNat = j
      · rw [ite_eq_left (by rw [hlit]; exact e)]
        simp only [List.filterMap_cons, e, ite_true]
        simp only [WVec.push, Array.toList_push, encodeWatches, List.flatMap_cons, WEntry.words,
          List.append_assoc, hw, href, blockingWatch_idem]
        rfl
      · rw [ite_eq_right (by rw [hlit]; exact e)]
        simp only [List.filterMap_cons, e, ite_false]
  | case2 wss k hk =>
    intro dl hdrop _
    cases dl with
    | nil => exact ⟨rfl, fun j _ => by simp [delayedAt, encodeWatches]⟩
    | cons x dl' =>
      exfalso
      have := congrArg List.length hdrop
      simp [flatDelayed] at this
      simp at hk
      omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The tail of `propagateLiteral` after the watch loop. -/
def propFinish (wss : Array WVec) (notLit : Lit) (R : PropResult) : Solver × Option CRef :=
  match R with
  | ⟨ws, p, q, a, arena, delayed, s, ticks, res⟩ =>
    let (ws, q) := copyRest ws p q
    let ws := ws.shrink q
    let wss := wss.set! notLit.toNat ws
    let wss := watchLargeDelayedLoop delayed wss 0
    ({ s with watches := wss, ticks := s.ticks + ticks, asg := a, arena := arena,
              delayed := delayed.clear }, res)

theorem propagateLiteral_eq (s : Solver) (lit : Lit) :
    s.propagateLiteral none false lit =
      propFinish ((s.watches.set! (NOT lit).toNat WVec.empty)) (NOT lit)
        (propLoop none false s.probing (s.options.jumpreasons != 0 && s.classification.bigbig)
          (s.asg.aLevel.get! (IDX lit).toNat) (NOT lit) (s.watches[(NOT lit).toNat]!) 0 0 s.asg
          s.arena s.delayed { s with asg := {}, arena := {}, delayed := .empty, watches := #[] }
          (1 + cacheLines (UInt64.ofNat (s.watches[(NOT lit).toNat]!).size)) none) := rfl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem getElem!_set!_arr (W : Array WVec) (i j : Nat) (x : WVec) (hj : j < W.size) :
    (W.set! i x)[j]! = if i = j then x else W[j]! := by
  simp [Array.set!, Array.getElem_setIfInBounds, hj]

/-- The watch lists after `propagateLiteral`. -/
theorem final_watches (W : Array WVec) (notLit : Lit) (X : WVec) (d : U32Vec)
    (out : List WEntry) (dlist : List (Lit × Lit × Ref))
    (hn : notLit.toNat < W.size) (hX : X.data.toList = encodeWatches out)
    (hdl : d.view = flatDelayed dlist) (hdne : ∀ x ∈ dlist, x.1 ≠ notLit)
    (hdv : ∀ x ∈ dlist, x.1.toNat < W.size)
    (hwords : ∀ l : Lit, WordsOK (W[l.toNat]!).data.toList)
    (hwf : ∀ l, ∀ e ∈ (if l = notLit then out else
      parseWatches (W[l.toNat]!).data.toList ++ delayedFor dlist l), e.WF) :
    let W' := watchLargeDelayedLoop d ((W.set! notLit.toNat WVec.empty).set! notLit.toNat X) 0
    W'.size = W.size ∧
    ∀ l, parseWatches (W'[l.toNat]!).data.toList =
        (if l = notLit then out else parseWatches (W[l.toNat]!).data.toList ++ delayedFor dlist l) ∧
      WordsOK (W'[l.toNat]!).data.toList := by
  intro W'
  have hsz2 : ((W.set! notLit.toNat WVec.empty).set! notLit.toNat X).size = W.size := by simp
  obtain ⟨h1, h2⟩ := wld_spec d ((W.set! notLit.toNat WVec.empty).set! notLit.toNat X) 0 dlist
    (by simpa using hdl) (fun x hx => by rw [hsz2]; exact hdv x hx)
  rw [hsz2] at h1 h2
  refine ⟨h1, fun l => ?_⟩
  have key : (W'[l.toNat]!).data.toList = encodeWatches
      (if l = notLit then out else parseWatches (W[l.toNat]!).data.toList ++ delayedFor dlist l) := by
    by_cases hl : l.toNat < W.size
    · rw [h2 l.toNat hl, delayedAt_eq]
      rw [getElem!_set!_arr _ _ _ _ (by simp; exact hl), getElem!_set!_arr _ _ _ _ hl]
      by_cases e : l = notLit
      · subst e
        have : delayedFor dlist l = [] := by
          unfold delayedFor
          rw [List.filterMap_eq_nil_iff]
          intro x hx; simp [hdne x hx]
        simp [hX, this, encodeWatches]
      · have e' : notLit.toNat ≠ l.toNat := fun h => e (UInt32.toNat_inj.mp h).symm
        simp only [e', ite_false, e, encode_append, encode_parse _ (hwords l)]
    · have e : l ≠ notLit := by intro h; subst h; exact hl hn
      have hd : delayedFor dlist l = [] := by
        unfold delayedFor
        rw [List.filterMap_eq_nil_iff]
        intro x hx
        have : x.1 ≠ l := by intro h; have := hdv x hx; rw [h] at this; exact hl this
        simp [this]
      have hl' : ¬ l.toNat < W'.size := by rw [h1]; exact hl
      simp only [e, ite_false, hd, List.append_nil]
      rw [getElem!_neg W' l.toNat hl', getElem!_neg W l.toNat hl]
      exact (encode_parse _ (by
        have := hwords l; rwa [getElem!_neg W l.toNat hl] at this)).symm
  rw [key]
  exact parse_encode _ (hwf l)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem propFinish_props (W : Array WVec) (n : Lit) (ws : WVec) (p q : Nat) (a : Asg)
    (arena : Arena) (delayed : U32Vec) (s' : Solver) (ticks : UInt64) (res : Option CRef) :
    let out := propFinish W n ⟨ws, p, q, a, arena, delayed, s', ticks, res⟩
    out.2 = res ∧ out.1.asg = a ∧ out.1.arena = arena ∧
    out.1.watches = watchLargeDelayedLoop delayed
      (W.set! n.toNat ((copyRest ws p q).1.shrink (copyRest ws p q).2)) 0 ∧
    out.1.delayed = delayed.clear ∧ Frame out.1 s' ∧
    out.1.conflictLit0 = s'.conflictLit0 ∧ out.1.conflictLit1 = s'.conflictLit1 ∧ out.1.flags = s'.flags := by
  intro out
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

section Transfer
variable {t v : Solver}

theorem inDB_transfer (hl : ∀ r, t.LiveRef r ↔ v.LiveRef r) (hc : ∀ r, t.clauseL r = v.clauseL r)
    (hb : ∀ a b, t.BinWatched a b ↔ v.BinWatched a b) (c : List Lit) : t.InDB c ↔ v.InDB c := by
  unfold InDB
  constructor
  · rintro (⟨r, h1, rfl⟩ | ⟨a, b, h1, rfl⟩)
    · exact Or.inl ⟨r, (hl r).mp h1, hc r⟩
    · exact Or.inr ⟨a, b, (hb a b).mp h1, rfl⟩
  · rintro (⟨r, h1, rfl⟩ | ⟨a, b, h1, rfl⟩)
    · exact Or.inl ⟨r, (hl r).mpr h1, (hc r).symm⟩
    · exact Or.inr ⟨a, b, (hb a b).mpr h1, rfl⟩

theorem reasonOK_transfer (ha : t.asg = v.asg) (hl : ∀ r, t.LiveRef r ↔ v.LiveRef r)
    (hc : ∀ r, t.clauseL r = v.clauseL r) (hb : ∀ a b, t.BinWatched a b ↔ v.BinWatched a b)
    (h : v.ReasonOK) : t.ReasonOK := by
  have eT : t.IsTrue = v.IsTrue := by funext l; simp [IsTrue, ha]
  have eL : t.lvl = v.lvl := by funext l; simp [lvl, ha]
  intro l hlt hlv
  rw [eT] at hlt; rw [eL] at hlv
  exact reasonAt_congr ha (fun r h => (hl r).mpr h) (fun r _ x => by rw [hc]) (fun a b h => (hb a b).mpr h)
    (h l hlt hlv)

theorem rootImplied_transfer {Φ : (Nat → Bool) → Prop} (ha : t.asg = v.asg) (h : RootImplied Φ v) :
    RootImplied Φ t := by
  intro l hl hlv
  have e1 : t.IsTrue l = v.IsTrue l := by simp [IsTrue, ha]
  have e2 : t.lvl l = v.lvl l := by simp [lvl, ha]
  rw [e1] at hl; rw [e2] at hlv
  exact h l hl hlv

end Transfer

/-- Conclusions about one call of `propagateLiteral`. -/
structure PropOut (Φ : (Nat → Bool) → Prop) (s0 : Solver) (i : Nat) (s1 : Solver)
    (res : Option CRef) : Prop where
  frame : Frame s1 s0
  core : s1.Core
  levelOK : s1.LevelOK
  ws : s1.WatchStruct
  layout : s1.arena.Layout
  trail : ∃ ext, s1.trailL = s0.trailL ++ ext
  persist : ∀ l, s0.IsTrue l → s1.IsTrue l ∧ s1.lvl l = s0.lvl l
  live : ∀ r, s1.LiveRef r ↔ s0.LiveRef r
  perm : ∀ r, s0.LiveRef r → (s1.clauseL r).Perm (s0.clauseL r)
  word0 : ∀ r, s0.LiveRef r → s1.arena.word0 r = s0.arena.word0 r
  bins : ∀ a b, s1.BinWatched a b ↔ s0.BinWatched a b
  reasons : s1.ReasonOK
  roots : RootImplied Φ s1
  rsizes : s1.ReasonSizes
  invC : ∀ c, s1.InDB c → s1.InvSAt i c
  invN : res = none → ∀ c, s1.InDB c → s1.InvSAt (i + 1) c
  conflict : ∀ c, res = some c → ConflictOK s1 s1 c
  bits : BitsShrink s1.asg s0.asg
  act : ∀ n, 2 * n ≤ s0.asg.values.size → ActOK s0.flags s0.asg.values n → ActOK s1.flags s1.asg.values n
  vsize : s1.asg.values.size = s0.asg.values.size

theorem sameView_of {t v : Solver} (ha : t.asg = v.asg) (har : t.arena = v.arena)
    (hf : t.frameTrail = v.frameTrail) (hp : t.propagate = v.propagate) (hv : t.vars = v.vars) :
    SameView t v := ⟨ha, har, hf, hp, hv⟩

theorem propagateLiteral_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {i : Nat} {lit : Lit}
    (hctx : Ctx s i lit) (hjc : JCtx Φ s) (hjump : s.options.jumpreasons = 0) :
    PropOut Φ s i (s.propagateLiteral none false lit).1 (s.propagateLiteral none false lit).2 := by
  rw [propagateLiteral_eq]
  have hjf : (s.options.jumpreasons != 0 && s.classification.bigbig) = false := by simp [hjump]
  rw [hjf]
  generalize hcold : ({ s with asg := {}, arena := {}, delayed := .empty, watches := #[] } : Solver) = cold
  have hprob : cold.probing = s.probing := by rw [← hcold]
  generalize hlv : s.asg.aLevel.get! (IDX lit).toNat = lv
  have hlv' : lv.toNat = s.lvl lit := by rw [← hlv]; rfl
  -- the spec run
  have hrel : LoopRel (s.watches[(NOT lit).toNat]!).data.toList (s.watches[(NOT lit).toNat]!) 0 0 [] :=
    ⟨rfl, Nat.le_refl _, Nat.zero_le _, rfl, by simp only [List.drop_zero]; exact hctx.ws.words (NOT lit), by simp [encodeWatches]⟩
  have hdl0 : s.delayed.view = flatDelayed [] := by
    apply List.eq_nil_of_length_eq_zero; simp [hctx.ws.delayed]
  have hcorr := propLoop_spec s.probing false lv (NOT lit) _ _ 0 0 s.asg s.arena s.delayed cold
    (1 + cacheLines (UInt64.ofNat (s.watches[(NOT lit).toNat]!).size)) none [] [] hrel hdl0
  simp only [List.drop_zero] at hcorr
  have hentries : parseWatches (s.watches[(NOT lit).toNat]!).data.toList = s.entries (NOT lit) := rfl
  rw [hentries] at hcorr
  have hinit : (⟨[], s.asg, s.arena, [], cold, none⟩ : PS) = PS.init s cold := rfl
  rw [hinit] at hcorr
  obtain ⟨hR, hW, hJ⟩ := run_all hctx hjc s.probing hlv' (s.entries (NOT lit)) (PS.init s cold) []
    (RunInv.init hctx cold) (WSInv.init s hctx.ws (NOT lit) cold) (JustInv.init hjc cold) rfl
  simp only [List.nil_append] at hR
  have hfr := PS.run_frame s.probing false lv (NOT lit) (s.entries (NOT lit)) (PS.init s cold)
  have hbits := PS.run_bits s.probing false lv (NOT lit) (s.entries (NOT lit)) (PS.init s cold)
  have hact := PS.run_active s.probing false lv (NOT lit)
  have hvs : ∀ (es : List WEntry) (st : PS), (PS.run s.probing false lv (NOT lit) st es).a.values.size = st.a.values.size := by
    intro es; induction es with
    | nil => intro st; rfl
    | cons e es ih => intro st; unfold PS.run; split
                      · rfl
                      · rw [ih]; exact (PS.step_active _ _ _ _ st e 0 (by omega) (fun v hv => absurd hv (by omega))).2
  have hvs1 := hvs (s.entries (NOT lit)) (PS.init s cold)
  have hact1 := fun n => hact n (s.entries (NOT lit)) (PS.init s cold)
  generalize PS.run s.probing false lv (NOT lit) (PS.init s cold) (s.entries (NOT lit)) = st
    at hcorr hR hW hJ hfr hbits hvs1 hact1
  have hfr' : Frame st.s s := by
    refine hfr.trans ?_
    rw [← hcold]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  generalize propLoop none false s.probing false lv (NOT lit) (s.watches[(NOT lit).toNat]!) 0 0
    s.asg s.arena s.delayed cold (1 + cacheLines (UInt64.ofNat (s.watches[(NOT lit).toNat]!).size))
    none = R at hcorr
  obtain ⟨ws, p, q, a, arena, delayed, s', ticks, res⟩ := R
  obtain ⟨ha, harena, hs', hres, hdel, htake⟩ := hcorr
  simp only at ha harena hs' hres hdel htake
  subst ha harena hs' hres
  have hfin := propFinish_props (s.watches.set! (NOT lit).toNat WVec.empty) (NOT lit) ws p q st.a
    st.arena delayed st.s ticks st.res
  generalize propFinish (s.watches.set! (NOT lit).toNat WVec.empty) (NOT lit)
    ⟨ws, p, q, st.a, st.arena, delayed, st.s, ticks, st.res⟩ = out at hfin ⊢
  obtain ⟨s1, res⟩ := out
  obtain ⟨e2, ea, ear, ew, ed, efr, ec0, ec1, efl⟩ := hfin
  simp only at e2 ea ear ew ed efr ec0 ec1 efl ⊢
  subst e2
  have hfrs : Frame s1 s := efr.trans hfr'
  -- the virtual solver
  have hsv : SameView s1 (V s st) := sameView_of ea ear hfrs.frameTrail hfrs.propagate hfrs.vars
  have eT : s1.IsTrue = (V s st).IsTrue := by funext l; simp [IsTrue, ea, V]
  have eF : s1.IsFalse = (V s st).IsFalse := by funext l; simp [IsFalse, ea, V]
  have eL : s1.lvl = (V s st).lvl := by funext l; simp [lvl, ea, V]
  have eTr : s1.trailL = (V s st).trailL := by simp [trailL, ea, V]
  have eLive : ∀ r, s1.LiveRef r ↔ (V s st).LiveRef r := by
    intro r; simp [LiveRef, refsL, ear, V]
  have eCl : ∀ r, s1.clauseL r = (V s st).clauseL r := by intro r; simp [clauseL, ear, V]
  -- watch lists
  have hX : ((copyRest ws p q).1.shrink (copyRest ws p q).2).data.toList = encodeWatches st.out := by
    rw [← htake]; simp [WVec.shrink]
  have hn : (NOT lit).toNat < s.watches.size := by
    have := hctx.ws.watchesSize
    have := validLit_lt (validLit_not hctx.valid)
    omega
  have hwlEq : ∀ l, WL s (NOT lit) st [] l = (if l = NOT lit then st.out else
      parseWatches (s.watches[l.toNat]!).data.toList ++ delayedFor st.delayed l) := by
    intro l; unfold WL; by_cases e : l = NOT lit
    · simp [e]
    · simp only [e, ite_false]; rfl
  have fw := final_watches s.watches (NOT lit) ((copyRest ws p q).1.shrink (copyRest ws p q).2)
    delayed st.out st.delayed hn hX hdel hW.delayedNe
    (fun x hx => by
      have := hW.delayedValid x hx
      have := hctx.ws.watchesSize
      rw [IDX_toNat] at *; omega)
    (fun l => hctx.ws.words l)
    (fun l => by rw [← hwlEq]; exact hW.wf l)
  simp only at fw
  have hent : ∀ l, s1.entries l = WL s (NOT lit) st [] l := by
    intro l
    show parseWatches (s1.watches[l.toNat]!).data.toList = _
    rw [ew, (fw.2 l).1, hwlEq]
  have hbins : ∀ a b, s1.BinWatched a b ↔ s.BinWatched a b := by
    intro a b
    show WEntry.bin b ∈ s1.entries a ↔ _
    rw [hent]; exact hW.bins a b
  have hbinsV : ∀ a b, s1.BinWatched a b ↔ (V s st).BinWatched a b := hbins
  have hDB : ∀ c, s1.InDB c ↔ (V s st).InDB c := inDB_transfer eLive eCl hbinsV
  have hA := hR.arena
  obtain ⟨ext, hext⟩ := hR.trail
  have hc1 : s1.Core := hsv.core hR.core
  have hext1 : s1.trailL = s.trailL ++ ext := by rw [eTr]; exact hext
  have hpersist : ∀ l, s.IsTrue l → s1.IsTrue l ∧ s1.lvl l = s.lvl l := by
    intro l hl; rw [eT, eL]; exact hR.persist l hl
  have hlvlT : ∀ l, s1.IsTrue l → s1.lvl l ≤ s.level.toNat := by
    intro l hl; rw [eT] at hl; rw [eL]; exact hR.lvl_true hctx.levelOK hl
  have hpush : ∀ p', s1.pushLevel p' = s.pushLevel p' := by
    intro p'; unfold pushLevel framesL; rw [hfrs.frameTrail]
  refine ⟨hfrs, hc1, ?lv, ?ws, by rw [ear]; exact hA.layout, ⟨ext, hext1⟩, hpersist,
    fun r => (eLive r).trans (hA.liveRef r), ?perm, ?w0, hbins, ?rs, ?roots, ?rsz, ?invC, ?invN, ?conf,
    by rw [ea]; exact hbits, fun n hn ha => by
      rw [ea, efl]; rw [← hcold] at hact1
      have := hact1 n hn ha; exact this, by rw [ea]; exact hvs1⟩
  case lv =>
    have hL := hctx.levelOK
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; rw [hfrs.level]; exact hlvlT l hl
    · intro p' l hp
      rw [hpush]
      rw [hext1] at hp
      by_cases hpl : p' < s.trailL.length
      · rw [List.getElem?_append_left hpl] at hp
        have hl0 : s.IsTrue l := hctx.core.trailTrue l (List.mem_of_getElem? hp)
        rw [(hpersist l hl0).2]; exact hL.pushLe p' l hp
      · have hmem : l ∈ s1.trailL := by rw [hext1]; exact List.mem_of_getElem? hp
        have hl1 := hc1.trailTrue l hmem
        rw [hL.pushLevel_cur (by have := hL.propLe; omega)]
        exact hlvlT l hl1
    · unfold framesL; rw [hfrs.frameTrail]; exact hL.sorted
    · unfold framesL; rw [hfrs.frameTrail, hfrs.level]; exact hL.len
    · unfold framesL; rw [hfrs.frameTrail, hfrs.propagate]; exact hL.framesLe
    · rw [hfrs.propagate, hext1]; have := hL.propLe; simp; omega
    · unfold framesL; rw [hfrs.frameTrail]; exact hL.strict
    · intro f hf; unfold framesL at hf; rw [hfrs.frameTrail] at hf
      rw [hext1]; have := hL.framesLt f hf; simp; omega
    · rw [hfrs.frameTrail]; exact hL.frames0
  case ws =>
    have hwsa := hW.wsa
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; show WordsOK (s1.watches[l.toNat]!).data.toList; rw [ew]; exact (fw.2 l).2
    · intro l b r hm
      rw [hent] at hm
      obtain ⟨h1, h2⟩ := hwsa.refOK l b r hm
      unfold refsL lit0 lit1 clauseL; rw [ear]
      exact ⟨h1, h2⟩
    · intro r hl
      have hl' : r ∈ st.arena.chain 0 st.arena.sizeWards ∧ st.arena.garbage r = false := by
        unfold LiveRef refsL at hl; rw [ear] at hl; exact hl
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hwsa.live r hl'.1 hl'.2
      unfold lit0 lit1 clauseL ValidLit
      rw [ear, hent, hent, hfrs.vars]
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · intro a b hab
      have hab' : WEntry.bin b ∈ WL s (NOT lit) st [] a := by rw [← hent]; exact hab
      obtain ⟨h1, h2, h3, h4⟩ := hwsa.bin a b hab'
      unfold ValidLit; rw [hfrs.vars]
      exact ⟨by show WEntry.bin a ∈ s1.entries b; rw [hent]; exact h1, h2, h3, h4⟩
    · rw [ed]; simp [U32Vec.clear, U32Vec.size_shrink]
    · rw [ew, fw.1, hfrs.vars]; exact hctx.ws.watchesSize
    · rw [hfrs.vars]; exact hctx.ws.varsBound
  case perm =>
    intro r hl
    rw [eCl]; exact hA.perm r hl.1
  case w0 =>
    intro r hl
    rw [ear]; exact hA.word0 r hl.1
  case rs => exact reasonOK_transfer ea eLive eCl hbinsV hJ.1
  case roots => exact rootImplied_transfer ea hJ.2.1
  case rsz =>
    have := hJ.2.2; unfold ReasonSizes at *; rw [ea, hfrs.vars, eTr]; exact this
  case invC =>
    intro c hc
    rw [hsv.invSAt]
    exact hR.inv c ((hDB c).mp hc)
  case invN =>
    intro hres c hc
    rw [hsv.invSAt]
    exact hR.invNext hctx hres c ((hDB c).mp hc)
  case conf =>
    intro c hc
    have := hR.conflict c hc
    cases c with
    | binConflict =>
      obtain ⟨h1, h2, h3⟩ := this
      refine ⟨?_, ?_, ?_⟩ <;> simp only [ec0, ec1]
      · exact (hbins _ _).mpr h1
      · rw [eF]; exact h2
      · rw [eF]; exact h3
    | large r =>
      obtain ⟨h1, h2⟩ := this
      refine ⟨(eLive r).mpr h1, fun x hx => ?_⟩
      rw [eF]; rw [eCl] at hx; exact h2 x hx

end Solver
end LeanKissat
