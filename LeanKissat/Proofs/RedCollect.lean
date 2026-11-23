import LeanKissat.Proofs.RedRewatch

/-!
# `reduce`: the non-compacting garbage collection (`kissat_sparse_collect`)
-/

namespace LeanKissat
namespace Solver
open Arena

/-! ### Flushing -/

theorem flush_entries (u : Solver) (start : Ref) (hv : u.vars.toNat < 2 ^ 30)
    (hw : ∀ l, WordsOK (u.watchesOf l).data.toList) :
    let w := u.flushAllWatchedClauses start
    stripW w = stripW u ∧ w.watches.size = u.watches.size ∧ (∀ l, WordsOK (w.watchesOf l).data.toList) ∧
    ∀ l, w.entries l = if (IDX l).toNat < u.vars.toNat then
      (u.entries l).filter (flushKeep u (u.fixedValue l) start) else u.entries l := by
  intro w
  obtain ⟨h1, h2, h3⟩ := flushAll_spec u start hv hw
  have hwf : ∀ l, ∀ e ∈ (u.entries l).filter (flushKeep u (u.fixedValue l) start), e.WF :=
    fun l e he => parse_wf _ e (List.mem_filter.mp he).1
  refine ⟨h1, h2, fun l => ?_, fun l => ?_⟩
  · rw [h3 l]; split
    · exact (parse_encode _ (hwf l)).2
    · exact hw l
  · unfold entries; rw [h3 l]; split
    · exact (parse_encode _ (hwf l)).1
    · rfl

/-- The reduce precondition of the garbage collection. -/
structure ColPre (Φ : (Nat → Bool) → Prop) (u : Solver) (start : Ref) (P Q : List Ref) : Prop where
  sinv : SInv Φ u
  invS : ∀ c, u.InDB c → u.InvS c
  prop : u.propagate = u.trailL.length
  lp : LayoutTo u.arena 0 start.toNat P
  refs : u.refsL = P ++ Q
  lq : LayoutTo u.arena start u.arena.sizeWards Q
  rb : ∀ l, u.IsTrue l → 0 < u.lvl l → u.binOf l = false → u.reasonOf l ≠ DECISION_REASON →
    start ≤ u.reasonOf l → u.arena.reason (u.reasonOf l) = true
  empty : ∀ l, ¬ (IDX l).toNat < u.vars.toNat → u.entries l = []

theorem fixedValue_not_true {s : Solver} {l : Lit} (h : s.IsTrue l ∧ 0 < s.lvl l ∨ s.IsFalse l) :
    vTrue (s.fixedValue l) = false := by
  unfold fixedValue
  rcases h with ⟨_, hl⟩ | hf
  · have : s.level' l ≠ 0 := by intro e; unfold lvl at hl; unfold level' at e; rw [e] at hl; simp at hl
    dsimp only; split
    · rfl
    · rw [if_pos (by simpa using this)]; rfl
  · unfold IsFalse at hf
    dsimp only; simp only [value, hf]
    split
    · rfl
    · split <;> rfl

/-- The fields of the flushed state. -/
theorem stripW_fields {s t : Solver} (h : stripW t = stripW s) : t.arena = s.arena ∧ t.asg = s.asg ∧
    t.vars = s.vars ∧ t.delayed = s.delayed ∧ t.options = s.options := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Solver.arena h; exact this
  · have := congrArg Solver.asg h; exact this
  · have := congrArg Solver.vars h; exact this
  · have := congrArg Solver.delayed h; exact this
  · have := congrArg Solver.options h; exact this

theorem swPre_of {Φ : (Nat → Bool) → Prop} {u : Solver} {start : Ref} {P Q : List Ref} (h : ColPre Φ u start P Q) :
    SwPre (u.flushAllWatchedClauses start) start Q := by
  have hW := h.sinv.ws
  obtain ⟨f1, f2, f3, f4⟩ := flush_entries u start hW.varsBound hW.words
  generalize u.flushAllWatchedClauses start = w at f1 f2 f3 f4 ⊢
  obtain ⟨e1, e2, e3, _, _⟩ := stripW_fields f1
  have hlive : ∀ r, w.LiveRef r ↔ u.LiveRef r := by intro r; simp [LiveRef, refsL, e1]
  have hcl : ∀ r, w.clauseL r = u.clauseL r := by intro r; simp [clauseL, e1]
  have hT : ∀ l, w.IsTrue l ↔ u.IsTrue l := by intro l; simp [IsTrue, e2]
  have hL : ∀ l, w.lvl l = u.lvl l := by intro l; simp [lvl, e2]
  have hRo : ∀ l, w.reasonOf l = u.reasonOf l := by intro l; simp [reasonOf, reasonIdx, e2]
  have hBo : ∀ l, w.binOf l = u.binOf l := by intro l; simp [binOf, isBinaryReason, abit, abits, e2]
  have hRS := h.sinv.rsizes
  refine ⟨by rw [e1]; exact h.sinv.layout, by rw [e1]; exact h.lq, fun r hr hg => ?_, fun l ht hl => ?_,
    fun l ht hl hb hd hs => ?_, core_congr e2 e3 h.sinv.core, f3, by rw [f2, e3]; exact hW.watchesSize,
    by rw [e3]; exact hW.varsBound, by rw [e3, e2]; exact ⟨hRS.1, hRS.2.1⟩,
    ⟨P, by rw [e1]; exact h.lp, by unfold refsL; rw [e1]; exact h.refs⟩⟩
  · rw [e1] at hg
    have hl : u.LiveRef r := ⟨by rw [h.refs]; simp [hr], hg⟩
    obtain ⟨_, hnd, _, _, _, _, hv⟩ := hW.live r hl
    rw [hcl]
    exact ⟨fun x hx => by unfold ValidLit; rw [e3]; exact hv x hx, hnd⟩
  · rw [hT] at ht; rw [hL] at hl
    have hR := h.sinv.reasons l ht hl
    unfold ReasonAt at hR ⊢
    rw [hRo, hBo]
    rcases hR with h1 | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h1
    · refine Or.inr (Or.inl ⟨h1, ?_, (ante_congr e2).mpr h3⟩)
      unfold BinWatched at *
      rw [f4]
      have hvl : (IDX l).toNat < u.vars.toNat := h.sinv.rsizes.valid ht
      rw [if_pos hvl]
      apply List.mem_filter.mpr ⟨h2, ?_⟩
      simp only [flushKeep, Bool.not_eq_true', Bool.or_eq_false_iff]
      exact ⟨fixedValue_not_true (Or.inl ⟨ht, hl⟩), fixedValue_not_true (Or.inr h3.1)⟩
    · exact Or.inr (Or.inr ⟨h1, (hlive _).mpr h2, by rw [hcl]; exact h3,
        fun x hx hne => (ante_congr e2).mpr (h4 x (by rw [← hcl]; exact hx) hne)⟩)
  · rw [hT] at ht; rw [hL] at hl; rw [hBo] at hb; rw [hRo] at hd hs ⊢; rw [e1]
    exact h.rb l ht hl hb hd hs

/-! ### The state after the collection -/

/-- The garbage collected state `f` described in terms of the state `u` before it. -/
structure CollOut (u : Solver) (start : Ref) (P Q N : List Ref) (f : Solver) : Prop where
  lay : f.arena.Layout
  refs : f.refsL = P ++ N
  lnew : LayoutTo f.arena start f.arena.sizeWards N
  pv : ∀ x ∈ P, f.arena.word0 x = u.arena.word0 x ∧ f.arena.size x = u.arena.size x ∧
    f.arena.searched x = u.arena.searched x ∧ f.arena.litsL x = u.arena.litsL x
  nv : ∀ n ∈ N, ∃ o ∈ Q, u.arena.garbage o = false ∧ (f.arena.litsL n).Perm (filt u o) ∧
    f.arena.redundant n = u.arena.redundant o ∧ f.arena.garbage n = false ∧ f.arena.searched n = 2 ∧
    3 ≤ (f.arena.size n).toNat ∧
    ((∃ x ∈ filt u o, vNeg (u.asg.values.get! x.toNat) = false) →
      vNeg (u.asg.values.get! (f.arena.lit n 0).toNat) = false)
  old : ∀ o ∈ Q, u.arena.garbage o = false → SatW u o ∨
    (∃ a b, filt u o = [a, b] ∧ f.BinWatched a b ∧ f.BinWatched b a) ∨
    (∃ n ∈ N, (f.arena.litsL n).Perm (filt u o) ∧ f.arena.redundant n = u.arena.redundant o)
  ent : ∀ l, ∃ (B : List Lit) (E : List WEntry), f.entries l = (if (IDX l).toNat < u.vars.toNat then
      (u.entries l).filter (flushKeep u (u.fixedValue l) start) else u.entries l) ++ B.map WEntry.bin ++ E ∧
    (∀ e ∈ E, ∃ n ∈ N, (e = .large (f.arena.lit n 1) n ∧ l = f.arena.lit n 0) ∨
      (e = .large (f.arena.lit n 0) n ∧ l = f.arena.lit n 1)) ∧
    (∀ r, countRef r E = if r ∈ N then (if l = f.arena.lit r 0 then 1 else 0) + (if l = f.arena.lit r 1 then 1 else 0)
      else 0)
  binNew : ∀ a b, f.BinWatched a b →
    (WEntry.bin b ∈ u.entries a ∧ (IDX a).toNat < u.vars.toNat ∧ flushKeep u (u.fixedValue a) start (.bin b) = true) ∨
    (f.BinWatched b a ∧ ∃ o ∈ Q, u.arena.garbage o = false ∧ (filt u o = [a, b] ∨ filt u o = [b, a]))
  words : ∀ l, WordsOK (f.watchesOf l).data.toList
  wsz : f.watches.size = u.watches.size
  asg : f.asg = { u.asg with aReason := f.asg.aReason, aBits := f.asg.aBits }
  rsz : f.asg.aReason.size = u.asg.aReason.size ∧ f.asg.aBits.size = u.asg.aBits.size
  bits : ∀ i b, AnaBit b → f.abit i b = u.abit i b
  reasons : ∀ l, u.IsTrue l → 0 < u.lvl l → f.ReasonAt l
  vars : f.vars = u.vars
  delayed : f.delayed = u.delayed
  level : f.level = u.level
  frameTrail : f.frameTrail = u.frameTrail
  propagate : f.propagate = u.propagate
  clause : f.clause = u.clause
  flg : Flg f = Flg u

theorem _root_.LeanKissat.Arena.LayoutTo.congr_hdr {a b : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref}, LayoutTo a r e refs →
    (∀ x ∈ refs, a.word0 x = b.word0 x ∧ a.size x = b.size x) → LayoutTo b r e refs := by
  intro r e refs
  induction refs generalizing r with
  | nil => intro h _; exact h
  | cons r' rs ih =>
    intro h hq
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h
    obtain ⟨e0, e2⟩ := hq r' (List.mem_cons_self ..)
    have hn := nextClause_eq e0 e2 hsh
    have hshb : b.shrunken r' = false := by unfold shrunken; rw [← flag_eq_of_word0 e0]; exact hsh
    refine ⟨rfl, hlt, hshb, by rw [← hn, hnext, e2], ?_⟩
    rw [← hn]
    exact ih hrest (fun x hx => hq x (List.mem_cons_of_mem _ hx))

theorem flg_stripRW (t : Solver) : Flg (stripRW t) = Flg t := rfl
theorem flg_stripT (t : Solver) : Flg (stripT t) = Flg t := rfl
theorem flg_stripW (t : Solver) : Flg (stripW t) = Flg t := rfl

/-- Frame fields along a strip equality. -/
structure SFields (f u : Solver) : Prop where
  vars : f.vars = u.vars
  delayed : f.delayed = u.delayed
  level : f.level = u.level
  frameTrail : f.frameTrail = u.frameTrail
  propagate : f.propagate = u.propagate
  clause : f.clause = u.clause
  flg : Flg f = Flg u

theorem SFields.trans {a b c : Solver} (h1 : SFields a b) (h2 : SFields b c) : SFields a c :=
  ⟨h1.vars.trans h2.vars, h1.delayed.trans h2.delayed, h1.level.trans h2.level, h1.frameTrail.trans h2.frameTrail,
    h1.propagate.trans h2.propagate, h1.clause.trans h2.clause, h1.flg.trans h2.flg⟩

theorem sfields_RW {f t : Solver} (h : stripRW f = stripRW t) : SFields f t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Solver.vars h; exact this
  · have := congrArg Solver.delayed h; exact this
  · have := congrArg Solver.level h; exact this
  · have := congrArg Solver.frameTrail h; exact this
  · have := congrArg Solver.propagate h; exact this
  · have := congrArg Solver.clause h; exact this
  · rw [← flg_stripRW f, ← flg_stripRW t, h]

theorem sfields_T {f t : Solver} (h : stripT f = stripT t) : SFields f t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Solver.vars h; exact this
  · have := congrArg Solver.delayed h; exact this
  · have := congrArg Solver.level h; exact this
  · have := congrArg Solver.frameTrail h; exact this
  · have := congrArg Solver.propagate h; exact this
  · have := congrArg Solver.clause h; exact this
  · rw [← flg_stripT f, ← flg_stripT t, h]

theorem sfields_W {f t : Solver} (h : stripW f = stripW t) : SFields f t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Solver.vars h; exact this
  · have := congrArg Solver.delayed h; exact this
  · have := congrArg Solver.level h; exact this
  · have := congrArg Solver.frameTrail h; exact this
  · have := congrArg Solver.propagate h; exact this
  · have := congrArg Solver.clause h; exact this
  · rw [← flg_stripW f, ← flg_stripW t, h]

theorem filt_congr {w u : Solver} (ha : w.arena = u.arena) (hs : w.asg = u.asg) (o : Ref) : filt w o = filt u o := by
  unfold filt clauseL rootF value level'; rw [ha, hs]

theorem satW_congr {w u : Solver} (ha : w.arena = u.arena) (hs : w.asg = u.asg) (o : Ref) : SatW w o ↔ SatW u o := by
  unfold SatW rootT clauseL value level'; rw [ha, hs]

theorem countRef_filter_keep (u : Solver) (fv : Value) (start r : Ref) : ∀ (L : List WEntry),
    countRef r (L.filter (flushKeep u fv start)) = if r < start then countRef r L else 0 := by
  intro L
  induction L with
  | nil => simp [countRef]
  | cons e L ih =>
    cases e with
    | bin o =>
      by_cases hk : flushKeep u fv start (.bin o) = true
      · rw [List.filter_cons_of_pos hk]; simp only [countRef]; exact ih
      · rw [List.filter_cons_of_neg hk]; simp only [countRef]; exact ih
    | large b r' =>
      by_cases hk : flushKeep u fv start (.large b r') = true
      · rw [List.filter_cons_of_pos hk]; simp only [countRef]; rw [ih]
        simp only [flushKeep, decide_eq_true_eq] at hk
        by_cases e : r' = r
        · subst e; simp [hk]
        · simp [e]
      · rw [List.filter_cons_of_neg hk]; simp only [countRef]; rw [ih]
        simp only [flushKeep, decide_eq_true_eq] at hk
        by_cases e : r' = r
        · subst e; simp [hk]
        · simp [e]

theorem countRef_map_bin (r : Ref) : ∀ (B : List Lit), countRef r (B.map WEntry.bin) = 0 := by
  intro B; induction B with
  | nil => rfl
  | cons x B ih => simp only [List.map_cons, countRef]; exact ih

theorem lit_eq_of_litsL {a b : Arena} {r : Ref} (hs : a.size r = b.size r) (hl : a.litsL r = b.litsL r) {k : Nat}
    (hk : k < (a.size r).toNat) : a.lit r k = b.lit r k := by
  have h1 : k < (a.litsL r).length := by rw [length_litsL]; exact hk
  have h2 : k < (b.litsL r).length := by rw [length_litsL, ← hs]; exact hk
  have := getElem_litsL a r k h1
  have := getElem_litsL b r k h2
  rw [← getElem_litsL a r k h1, ← getElem_litsL b r k h2]
  simp [hl]

theorem asg_view {t u : Solver} (h : t.asg = { u.asg with aReason := t.asg.aReason, aBits := t.asg.aBits }) :
    t.asg.values = u.asg.values ∧ t.asg.aLevel = u.asg.aLevel ∧ t.asg.trail = u.asg.trail ∧
    t.asg.unassigned = u.asg.unassigned := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h]

theorem ante_view {t u : Solver} (h : t.asg = { u.asg with aReason := t.asg.aReason, aBits := t.asg.aBits })
    {l x : Lit} : t.Ante l x ↔ u.Ante l x := by
  obtain ⟨h1, h2, h3, _⟩ := asg_view h
  simp [Ante, Before, IsFalse, lvl, trailL, h1, h2, h3]

theorem collOut_of {Φ : (Nat → Bool) → Prop} {u : Solver} {start : Ref} {P Q N : List Ref} {t f : Solver}
    (h : ColPre Φ u start P Q) (hO : SwOut (u.flushAllWatchedClauses start) start Q t N)
    (hR : RWI t start f N []) : CollOut u start P Q N f := by
  have hW := h.sinv.ws
  obtain ⟨f1, f2, f3, f4⟩ := flush_entries u start hW.varsBound hW.words
  have hp := swPre_of h
  generalize u.flushAllWatchedClauses start = w at f1 f2 f3 f4 hO hp
  obtain ⟨e1, e2, e3, _, _⟩ := stripW_fields f1
  have hFt : f.asg = t.asg := by have := congrArg Solver.asg hR.frame; exact this
  have hSF : SFields f u := (sfields_RW hR.frame).trans ((sfields_T hO.frame).trans (sfields_W f1))
  obtain ⟨P', hP'w, hRw, hRt, hPt⟩ := hO.chain
  have hPP : P' = P := by
    have h1 : w.refsL = P ++ Q := by unfold refsL; rw [e1]; exact h.refs
    rw [h1] at hRw; exact (List.append_cancel_right hRw).symm
  subst hPP
  -- the arena
  have hfsz : f.arena.words.size = t.arena.words.size := hR.wsize
  have hfsw : f.arena.sizeWards = t.arena.sizeWards := by unfold sizeWards; rw [hfsz]
  have hPf : LayoutTo f.arena 0 start.toNat P' := hPt.congr (hR.pre.symm.mono (Nat.le_refl _) (Nat.le_refl _))
  have hNf : LayoutTo f.arena start f.arena.sizeWards N := by
    rw [hfsw]
    exact hO.lnew.congr_hdr (fun x hx => ⟨(hR.done x (by simp [hx])).1.symm, (hR.done x (by simp [hx])).2.1.symm⟩)
  have hall : LayoutTo f.arena 0 f.arena.sizeWards (P' ++ N) := hPf.append hNf
  have hch : f.arena.chain 0 f.arena.sizeWards = P' ++ N := hall.chain_eq _ (by
    have := hall.length_le; simp at this ⊢; omega)
  have hlay : f.arena.Layout := ⟨by rw [hch]; exact layoutFrom_iff.mpr hall,
    by rw [hfsz, hfsw]; exact hO.lay.mult4, by rw [hfsw]; exact hO.lay.bound⟩
  -- views of the old prefix
  have hpv : ∀ x ∈ P', f.arena.word0 x = u.arena.word0 x ∧ f.arena.size x = u.arena.size x ∧
      f.arena.searched x = u.arena.searched x ∧ f.arena.litsL x = u.arena.litsL x := by
    intro x hx
    obtain ⟨_, bt, _⟩ := hPt.mem_bounds x hx
    obtain ⟨_, bw, _⟩ := hP'w.mem_bounds x hx
    obtain ⟨a0, a1, a2, a3⟩ := clause_eq_of_eqOn (a := t.arena) (b := f.arena) (x := x)
      (hR.pre.symm.mono (Nat.zero_le _) (by omega))
    obtain ⟨b0, b1, b2, b3⟩ := clause_eq_of_eqOn (a := w.arena) (b := t.arena) (x := x)
      (hO.pre.symm.mono (Nat.zero_le _) (by omega))
    rw [e1] at b0 b1 b2 b3
    exact ⟨(b0.trans a0).symm, (b2.trans a2).symm, (b1.trans a1).symm, (b3.trans a3).symm⟩
  have hTf : ∀ l, ∃ E, f.entries l = t.entries l ++ E ∧ ∀ e ∈ E, ∃ b r, e = .large b r := by
    intro l
    obtain ⟨E, hE, hmem, _⟩ := hR.ent l
    exact ⟨E, hE, fun e he => by obtain ⟨n, _, h1 | h1⟩ := hmem e he <;> exact ⟨_, _, h1.1⟩⟩
  have hBf : ∀ a b, t.BinWatched a b → f.BinWatched a b := by
    intro a b hab; obtain ⟨E, hE, _⟩ := hTf a; unfold BinWatched; rw [hE]; exact List.mem_append_left _ hab
  have hBt : ∀ a b, w.BinWatched a b → t.BinWatched a b := by
    intro a b hab; obtain ⟨B, hB⟩ := hO.ent a; unfold BinWatched; rw [hB]
    exact List.mem_append_left _ hab
  have hfilt := filt_congr e1 e2
  have htv : t.asg.values = u.asg.values := by rw [(asg_view hO.asg).1, e2]
  have hfasg : f.asg = { u.asg with aReason := f.asg.aReason, aBits := f.asg.aBits } := by
    rw [hFt]; have := hO.asg; rw [e2] at this; exact this
  have hfu : f.asg.values = u.asg.values := (asg_view hfasg).1
  refine ⟨hlay, hch, hNf, hpv, ?_, ?_, ?_, ?_, hR.words, by rw [hR.wsz, hO.wsz, f2], hfasg,
    by rw [hFt, hO.rsz.1, hO.rsz.2, e2]; exact ⟨rfl, rfl⟩, fun i b hb => ?_, ?_, hSF.vars, hSF.delayed,
    hSF.level, hSF.frameTrail, hSF.propagate, hSF.clause, hSF.flg⟩
  · -- new clauses
    intro n hn
    obtain ⟨o, ho, g, hlit, hred, hgar, hsea, hsz⟩ := hO.newCl n hn
    obtain ⟨d0, d1, d2, d3, d4⟩ := hR.done n (by simp [hn])
    refine ⟨o, ho, by rw [← e1]; exact g, by rw [← hfilt, ← hlit]; exact d3, ?_, ?_, d2, by rw [d1]; exact hsz, ?_⟩
    · unfold redundant; rw [flag_eq_of_word0 d0]; rw [← e1]; exact hred
    · unfold garbage; rw [flag_eq_of_word0 d0]; exact hgar
    · intro hx
      rw [← htv]; apply d4
      rw [hlit, hfilt, htv]; exact hx
  · -- old clauses
    intro o ho g
    rcases hO.oldCl o ho (by rw [e1]; exact g) with h1 | ⟨a, b, h1, h2, h3⟩ | ⟨n, hn, h1, h2⟩
    · exact Or.inl ((satW_congr e1 e2 o).mp h1)
    · exact Or.inr (Or.inl ⟨a, b, by rw [← hfilt]; exact h1, hBf _ _ h2, hBf _ _ h3⟩)
    · obtain ⟨d0, _, _, d3, _⟩ := hR.done n (by simp [hn])
      refine Or.inr (Or.inr ⟨n, hn, by rw [← hfilt, ← h1]; exact d3, ?_⟩)
      unfold redundant; rw [flag_eq_of_word0 d0, ← e1]; exact h2
  · -- watch lists
    intro l
    obtain ⟨E, hE, hmem, hcnt⟩ := hR.ent l
    obtain ⟨B, hB⟩ := hO.ent l
    refine ⟨B, E, ?_, fun e he => ?_, fun r => ?_⟩
    · rw [hE, hB, f4 l]
    · obtain ⟨n, hn, h1⟩ := hmem e he; exact ⟨n, by simpa using hn, h1⟩
    · exact hcnt r
  · -- binary watches
    intro a b hab
    obtain ⟨E, hE, hlarge⟩ := hTf a
    have hab' : t.BinWatched a b := by
      unfold BinWatched at hab; rw [hE] at hab
      rcases List.mem_append.mp hab with h1 | h1
      · exact h1
      · obtain ⟨_, _, e⟩ := hlarge _ h1; cases e
    rcases hO.binNew a b hab' with h1 | ⟨h2, o, ho, g, h3⟩
    · left
      unfold BinWatched at h1; rw [f4 a] at h1
      split at h1
      · rename_i hv; exact ⟨(List.mem_filter.mp h1).1, hv, (List.mem_filter.mp h1).2⟩
      · rename_i hv; rw [h.empty a hv] at h1; simp at h1
    · exact Or.inr ⟨hBf _ _ h2, o, ho, by rw [← e1]; exact g, by rw [← hfilt]; exact h3⟩
  · -- analysis bits
    have : f.abit i b = t.abit i b := by unfold abit abits; rw [hFt]
    rw [this, hO.bits i b hb]; unfold abit abits; rw [e2]
  · -- reasons
    intro l ht hl
    have hTw : w.IsTrue l := by unfold IsTrue; rw [e2]; exact ht
    have hLw : 0 < w.lvl l := by unfold lvl; rw [e2]; exact hl
    have hRw := hp.reasons l hTw hLw
    have hRS := hO.reasons l hTw hLw
    have eR : f.reasonOf l = t.reasonOf l := by unfold reasonOf reasonIdx; rw [hFt]
    have eB : f.binOf l = t.binOf l := by unfold binOf isBinaryReason abit abits; rw [hFt]
    have hAft : ∀ x, f.Ante l x ↔ w.Ante l x := by
      intro x
      have h1 : f.asg = { w.asg with aReason := f.asg.aReason, aBits := f.asg.aBits } := by
        rw [hFt]; exact hO.asg
      exact ante_view h1
    have hLiveN : ∀ n ∈ N, f.LiveRef n := by
      intro n hn
      obtain ⟨o, ho, g, hlit, hred, hgar, hsea, hsz⟩ := hO.newCl n hn
      obtain ⟨d0, _⟩ := hR.done n (by simp [hn])
      refine ⟨by unfold refsL; rw [hch]; simp [hn], ?_⟩
      unfold garbage; rw [flag_eq_of_word0 d0]; exact hgar
    unfold RS at hRS
    split at hRS
    · rename_i hc
      rcases hRw with hd | ⟨hb1, _⟩ | ⟨_, hlive, hlin, hante⟩
      · exact absurd hd hc.2.1
      · rw [hc.1] at hb1; simp at hb1
      rcases hRS with ⟨h1, _⟩ | ⟨h1, n, hn, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
      · simp at h1
      · -- moved large reason
        obtain ⟨_, _, _, d3, _⟩ := hR.done n (by simp [hn])
        have hperm : (f.arena.litsL n).Perm (filt w (w.reasonOf l)) := by rw [← h3]; exact d3
        unfold ReasonAt
        rw [eR, eB, h2]
        refine Or.inr (Or.inr ⟨h1, hLiveN n hn, ?_, fun x hx hne => ?_⟩)
        · show l ∈ f.arena.litsL n
          apply hperm.symm.subset
          unfold filt
          apply List.mem_filter.mpr ⟨hlin, ?_⟩
          have : w.rootF l = false := by
            unfold rootF; have := (hp.core.valCons l).2
            have hf : ¬ w.IsFalse l := fun hf => this ⟨hTw, hf⟩
            rw [isFalse_iff_vFalse] at hf
            simp only [value]; simp [hf]
          simp [this]
        · have hx' : x ∈ filt w (w.reasonOf l) := hperm.subset hx
          exact (hAft x).mpr (hante x (filt_sub hx') hne)
      · -- binary reason
        unfold ReasonAt
        rw [eR, eB]
        exact Or.inr (Or.inl ⟨h1, hBf _ _ h2, (hAft _).mpr (hante _ h3 h4)⟩)
    · rename_i hc
      obtain ⟨h1, h2⟩ := hRS
      unfold ReasonAt
      rw [eR, eB, h1, h2]
      rcases hRw with hd | ⟨hb1, hb2, hb3⟩ | ⟨hb1, hlive, hlin, hante⟩
      · exact Or.inl hd
      · exact Or.inr (Or.inl ⟨hb1, hBf _ _ (hBt _ _ hb2), (hAft _).mpr hb3⟩)
      · -- an old large reason before `start`
        have hwr : w.refsL = P' ++ Q := by unfold refsL; rw [e1]; exact h.refs
        have hmem := hlive.1; rw [hwr] at hmem
        have hbd : (w.reasonOf l).toNat < 2 ^ 31 := by
          have := (hp.lay.mem_bounds (show w.reasonOf l ∈ w.arena.chain 0 w.arena.sizeWards from hlive.1))
          have := hp.lay.bound; have := wardsOfClause_pos (w.arena.size (w.reasonOf l)).toNat; omega
        have hdec : w.reasonOf l ≠ DECISION_REASON := by
          intro e; rw [e] at hbd; simp [DECISION_REASON] at hbd
        have hlt : ¬ start ≤ w.reasonOf l := fun hs => hc ⟨hb1, hdec, hs⟩
        have hP : w.reasonOf l ∈ P' := by
          rcases List.mem_append.mp hmem with h1 | h1
          · exact h1
          · exfalso; apply hlt
            have := (h.lq.mem_bounds _ h1).1
            rw [UInt32.le_iff_toNat_le]; exact this
        obtain ⟨v0, _, _, v3⟩ := hpv _ hP
        have hcl : f.clauseL (w.reasonOf l) = w.clauseL (w.reasonOf l) := by
          show f.arena.litsL _ = w.arena.litsL _; rw [v3, e1]
        refine Or.inr (Or.inr ⟨hb1, ⟨by unfold refsL; rw [hch]; simp [hP], ?_⟩, by rw [hcl]; exact hlin,
          fun x hx hne => (hAft x).mpr (hante x (by rw [← hcl]; exact hx) hne)⟩)
        have := hlive.2
        unfold garbage at this ⊢; rw [flag_eq_of_word0 v0, ← e1]; exact this

/-! ### The invariants after the collection -/

section Final
variable {Φ : (Nat → Bool) → Prop} {u : Solver} {start : Ref} {P Q N : List Ref} {f : Solver}

theorem CollOut.P_lt (h : ColPre Φ u start P Q) {x : Ref} (hx : x ∈ P) : x.toNat < start.toNat := by
  have := (h.lp.mem_bounds x hx).2.1
  have := wardsOfClause_pos (u.arena.size x).toNat
  omega

theorem CollOut.N_ge (hC : CollOut u start P Q N f) {x : Ref} (hx : x ∈ N) : start.toNat ≤ x.toNat :=
  (hC.lnew.mem_bounds x hx).1

theorem CollOut.liveP (hC : CollOut u start P Q N f) (h : ColPre Φ u start P Q) {r : Ref} (hr : r ∈ P) :
    (f.LiveRef r ↔ u.LiveRef r) ∧ f.clauseL r = u.clauseL r ∧
    (2 ≤ (u.arena.size r).toNat → f.lit0 r = u.lit0 r ∧ f.lit1 r = u.lit1 r) ∧
    f.arena.size r = u.arena.size r ∧ f.arena.searched r = u.arena.searched r ∧
    f.arena.redundant r = u.arena.redundant r := by
  obtain ⟨v0, v1, v2, v3⟩ := hC.pv r hr
  have hg : f.arena.garbage r = u.arena.garbage r := by unfold garbage; rw [flag_eq_of_word0 v0]
  have hmf : r ∈ f.refsL := by rw [hC.refs]; simp [hr]
  have hmu : r ∈ u.refsL := by rw [h.refs]; simp [hr]
  refine ⟨⟨fun hl => ⟨hmu, by rw [← hg]; exact hl.2⟩, fun hl => ⟨hmf, by rw [hg]; exact hl.2⟩⟩, v3,
    fun h2 => ⟨lit_eq_of_litsL v1 v3 (by rw [v1]; omega), lit_eq_of_litsL v1 v3 (by rw [v1]; omega)⟩, v1, v2,
    by unfold redundant; rw [flag_eq_of_word0 v0]⟩

theorem filt_nodup {u : Solver} {o : Ref} (h : (u.clauseL o).Nodup) : (filt u o).Nodup := h.filter _

theorem CollOut.liveN (hC : CollOut u start P Q N f) (h : ColPre Φ u start P Q) {n : Ref} (hn : n ∈ N) :
    ∃ o ∈ Q, u.LiveRef o ∧ f.LiveRef n ∧ (f.clauseL n).Perm (filt u o) ∧ (f.clauseL n).Nodup ∧
      (∀ x ∈ f.clauseL n, f.ValidLit x) ∧ 3 ≤ (f.arena.size n).toNat ∧ f.arena.searched n = 2 ∧
      f.arena.redundant n = u.arena.redundant o ∧
      ((∃ x ∈ filt u o, vNeg (u.asg.values.get! x.toNat) = false) →
        vNeg (u.asg.values.get! (f.lit0 n).toNat) = false) := by
  obtain ⟨o, ho, g, hp, hred, hgar, hsea, hsz, hfront⟩ := hC.nv n hn
  have hlo : u.LiveRef o := ⟨by rw [h.refs]; simp [ho], g⟩
  obtain ⟨_, hnd, _, _, _, _, hv⟩ := h.sinv.ws.live o hlo
  have hnd' : (f.clauseL n).Nodup := (hp.nodup_iff).mpr (filt_nodup hnd)
  refine ⟨o, ho, hlo, ⟨by rw [hC.refs]; simp [hn], hgar⟩, hp, hnd', fun x hx => ?_, hsz, hsea, hred, hfront⟩
  have := hv x (filt_sub (hp.subset hx))
  unfold ValidLit at *; rw [hC.vars]; exact this

theorem lit01_ne {s : Solver} {r : Ref} (hnd : (s.clauseL r).Nodup) (h2 : 2 ≤ (s.arena.size r).toNat) :
    s.lit0 r ≠ s.lit1 r := by
  intro e
  have hnd' : (s.arena.litsL r).Nodup := hnd
  have h0 : 0 < (s.arena.litsL r).length := by rw [length_litsL]; omega
  have h1 : 1 < (s.arena.litsL r).length := by rw [length_litsL]; omega
  have := hnd'.eq_of_getElem_eq h0 h1 (by rw [getElem_litsL, getElem_litsL]; exact e)
  simp at this

theorem lit_mem_clauseL {s : Solver} {r : Ref} {k : Nat} (hk : k < (s.arena.size r).toNat) :
    s.arena.lit r k ∈ s.clauseL r := lit_mem_litsL s.arena r k hk

theorem CollOut.watchStruct (hC : CollOut u start P Q N f) (h : ColPre Φ u start P Q) : f.WatchStruct := by
  have hW := h.sinv.ws
  have hvl : ∀ x, f.ValidLit x ↔ u.ValidLit x := by intro x; unfold ValidLit; rw [hC.vars]
  -- the large entries of the final watch lists
  have hlarge : ∀ l b r, WEntry.large b r ∈ f.entries l →
      (r ∈ P ∧ WEntry.large b r ∈ u.entries l) ∨
      (r ∈ N ∧ ((b = f.lit1 r ∧ l = f.lit0 r) ∨ (b = f.lit0 r ∧ l = f.lit1 r))) := by
    intro l b r hm
    obtain ⟨B, E, hE, hmem, _⟩ := hC.ent l
    rw [hE] at hm
    simp only [List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · split at hm
      · obtain ⟨hm1, hm2⟩ := List.mem_filter.mp hm
        simp only [flushKeep, decide_eq_true_eq] at hm2
        left
        have hr := (hW.refOK l b r hm1).1
        rw [h.refs] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨hr, hm1⟩
        · exfalso; have := (h.lq.mem_bounds r hr).1; rw [UInt32.lt_iff_toNat_lt] at hm2; omega
      · rename_i hv; rw [h.empty l hv] at hm; simp at hm
    · simp at hm
    · obtain ⟨n, hn, h1 | h1⟩ := hmem _ hm
      · right; cases h1.1; exact ⟨hn, Or.inl ⟨rfl, h1.2⟩⟩
      · right; cases h1.1; exact ⟨hn, Or.inr ⟨rfl, h1.2⟩⟩
  -- counts
  have hcount : ∀ l r, f.ValidLit l → countRef r (f.entries l) =
      (if r ∈ P then countRef r (u.entries l) else 0) +
      (if r ∈ N then (if l = f.lit0 r then 1 else 0) + (if l = f.lit1 r then 1 else 0) else 0) := by
    intro l r hl
    obtain ⟨B, E, hE, _, hcnt⟩ := hC.ent l
    rw [hE, countRef_append, countRef_append, countRef_map_bin, hcnt r]
    rw [if_pos (show (IDX l).toNat < u.vars.toNat from (hvl l).mp hl), countRef_filter_keep]
    congr 1
    · by_cases hP : r ∈ P
      · rw [if_pos hP, if_pos (by rw [UInt32.lt_iff_toNat_lt]; exact CollOut.P_lt h hP), Nat.add_zero]
      · rw [if_neg hP, Nat.add_zero]
        split
        · rename_i hlt
          -- `r < start` entries of `u` point into the prefix
          apply countRef_zero
          intro b hb
          have hr := (hW.refOK l b r hb).1
          rw [h.refs] at hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hP hr
          · have := (h.lq.mem_bounds r hr).1; rw [UInt32.lt_iff_toNat_lt] at hlt; omega
        · rfl
  refine ⟨hC.words, fun l b r hm => ?_, fun r hr => ?_, fun a b hab => ?_, by rw [hC.delayed]; exact hW.delayed,
    by rw [hC.wsz, hC.vars]; exact hW.watchesSize, by rw [hC.vars]; exact hW.varsBound⟩
  · -- refOK
    rcases hlarge l b r hm with ⟨hP, hm'⟩ | ⟨hN, hb⟩
    · obtain ⟨hlv, hcl, h01, _, _, _⟩ := hC.liveP h hP
      obtain ⟨_, hng⟩ := hW.refOK l b r hm'
      refine ⟨by rw [hC.refs]; simp [hP], fun hg => ?_⟩
      have hlu : u.LiveRef r := hlv.mp ⟨by rw [hC.refs]; simp [hP], hg⟩
      obtain ⟨h3, _⟩ := hW.live r hlu
      obtain ⟨e0, e1⟩ := h01 (by omega)
      obtain ⟨k1, k2⟩ := hng hlu.2
      exact ⟨by rw [e0, e1]; exact k1, by rw [hcl]; exact k2⟩
    · obtain ⟨o, _, _, hlf, _, _, _, h3, _⟩ := hC.liveN h hN
      refine ⟨hlf.1, fun _ => ?_⟩
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Or.inl rfl, lit_mem_clauseL (by omega)⟩
      · exact ⟨Or.inr rfl, lit_mem_clauseL (by omega)⟩
  · -- live clauses
    have hmem := hr.1
    rw [hC.refs] at hmem
    rcases List.mem_append.mp hmem with hP | hN
    · obtain ⟨hlv, hcl, h01, hsz, hse, _⟩ := hC.liveP h hP
      have hlu := hlv.mp hr
      obtain ⟨h3, hnd, hs1, hs2, c0, c1, hv⟩ := hW.live r hlu
      obtain ⟨e0, e1⟩ := h01 (by omega)
      have hnN : r ∉ N := fun hn => by have := CollOut.P_lt h hP; have := hC.N_ge hn; omega
      have hv0 : f.ValidLit (f.lit0 r) := by rw [e0, hvl]; exact hv _ (lit_mem_clauseL (by omega))
      have hv1 : f.ValidLit (f.lit1 r) := by rw [e1, hvl]; exact hv _ (lit_mem_clauseL (by omega))
      refine ⟨by rw [hsz]; exact h3, by rw [hcl]; exact hnd, by rw [hse]; exact hs1, by rw [hse, hsz]; exact hs2,
        ?_, ?_, fun x hx => by rw [hvl]; rw [hcl] at hx; exact hv x hx⟩
      · rw [hcount _ _ hv0, if_pos hP, if_neg hnN, e0]; exact c0
      · rw [hcount _ _ hv1, if_pos hP, if_neg hnN, e1]; exact c1
    · obtain ⟨o, _, _, _, _, hnd, hv, h3, hse, _, _⟩ := hC.liveN h hN
      have hnP : r ∉ P := fun hp => by have := CollOut.P_lt h hp; have := hC.N_ge hN; omega
      have hne := lit01_ne hnd (by omega)
      have hv0 : f.ValidLit (f.lit0 r) := hv _ (lit_mem_clauseL (by omega))
      have hv1 : f.ValidLit (f.lit1 r) := hv _ (lit_mem_clauseL (by omega))
      refine ⟨h3, hnd, by rw [hse]; decide, by rw [hse]; simp; omega, ?_, ?_, hv⟩
      · rw [hcount _ _ hv0, if_neg hnP, if_pos hN, if_pos rfl, if_neg hne]
      · rw [hcount _ _ hv1, if_neg hnP, if_pos hN, if_pos rfl, if_neg (Ne.symm hne)]
  · -- binary clauses
    rcases hC.binNew a b hab with ⟨h1, h2, h3⟩ | ⟨h1, o, ho, g, h2⟩
    · obtain ⟨k1, k2, k3, k4⟩ := hW.bin a b h1
      refine ⟨?_, (hvl a).mpr k2, (hvl b).mpr k3, k4⟩
      obtain ⟨B, E, hE, _, _⟩ := hC.ent b
      unfold BinWatched; rw [hE, if_pos (show (IDX b).toNat < u.vars.toNat from k3)]
      apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_filter.mpr ⟨k1, ?_⟩
      simp only [flushKeep, Bool.not_eq_true', Bool.or_eq_false_iff] at h3 ⊢
      exact ⟨h3.2, h3.1⟩
    · have hlo : u.LiveRef o := ⟨by rw [h.refs]; simp [ho], g⟩
      obtain ⟨_, hnd, _, _, _, _, hv⟩ := h.sinv.ws.live o hlo
      have hfn := filt_nodup hnd
      have hva : ∀ x ∈ filt u o, f.ValidLit x := fun x hx => (hvl x).mpr (hv x (filt_sub hx))
      rcases h2 with e | e <;> rw [e] at hfn hva
      · exact ⟨h1, hva a (by simp), hva b (by simp), by simpa using hfn⟩
      · exact ⟨h1, hva a (by simp), hva b (by simp), by simpa [eq_comm] using hfn⟩

/-- With full propagation, every database clause has a literal that is not false. -/
theorem nonFalse_of_invS {u : Solver} {Φ : (Nat → Bool) → Prop} (hs : SInv Φ u) (hprop : u.propagate = u.trailL.length)
    {c : List Lit} (hinv : u.InvS c) (hlen : 2 ≤ c.length) : ∃ x ∈ c, ¬ u.IsFalse x := by
  match c, hlen, hinv with
  | w0 :: w1 :: rest, _, hinv =>
    apply Classical.byContradiction; intro hno
    have hf : ∀ l ∈ w0 :: w1 :: rest, u.IsFalse l := fun l hl =>
      Classical.byContradiction fun h => hno ⟨l, hl, h⟩
    have hc := hs.core
    obtain ⟨k0, h0⟩ := propFalse_of_complete hc.valCons hc.trueOnTrail hc.lvlVar hprop (hf w0 (by simp))
    obtain ⟨k1, h1⟩ := propFalse_of_complete hc.valCons hc.trueOnTrail hc.lvlVar hprop (hf w1 (by simp))
    obtain ⟨t, ht, htt, _⟩ := hinv w0 w1 rest rfl k0 k1 h0 h1
    exact (hc.valCons t).2 ⟨htt, hf t ht⟩

theorem rootF_iff {u : Solver} (x : Lit) : u.rootF x = true ↔ u.IsFalse x ∧ u.lvl x = 0 := by
  unfold rootF lvl level'
  rw [isFalse_iff_vFalse]
  simp only [Bool.and_eq_true, beq_iff_eq, value]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, UInt32.toNat_inj.mp (by simpa using h2)⟩

/-- Dropping root-level false literals keeps implied clauses implied. -/
theorem implied_filt {u : Solver} {Φ : (Nat → Bool) → Prop} (hs : SInv Φ u) {o : Ref}
    (h : Implied Φ (u.clauseL o)) : Implied Φ (filt u o) := by
  intro β hβ
  obtain ⟨x, hx, hv⟩ := h β hβ
  by_cases hr : u.rootF x = true
  · exfalso
    obtain ⟨hf, hl⟩ := (rootF_iff x).mp hr
    have hnt : u.IsTrue (NOT x) := by
      have := (hs.core.valCons (NOT x)).1; rw [NOT_NOT] at this; exact this.mpr hf
    have := hs.roots (NOT x) hnt (by rw [hs.core.lvlVar]; exact hl) β hβ
    obtain ⟨y, hy, hyv⟩ := this
    simp at hy; subst hy
    rw [litVal_NOT, hv] at hyv; simp at hyv
  · exact ⟨x, List.mem_filter.mpr ⟨hx, by simpa using hr⟩, hv⟩

theorem vNeg_false_of_not_false {u : Solver} (hs : u.Core) {x : Lit} (h : ¬ u.IsFalse x) :
    vNeg (u.asg.values.get! x.toNat) = false := by
  unfold IsFalse at h
  rcases hs.domain x.toNat with e | e | e
  · rw [e]; decide
  · rw [e]; decide
  · exact absurd e h

theorem not_false_of_vNeg {u : Solver} {x : Lit} (h : vNeg (u.asg.values.get! x.toNat) = false) :
    ¬ u.IsFalse x := by
  unfold IsFalse; intro e; rw [e] at h; exact absurd h (by decide)

theorem CollOut.views (hC : CollOut u start P Q N f) :
    f.IsTrue = u.IsTrue ∧ f.IsFalse = u.IsFalse ∧ f.lvl = u.lvl ∧ f.trailL = u.trailL ∧ f.framesL = u.framesL ∧
    f.pushLevel = u.pushLevel := by
  obtain ⟨h1, h2, h3, _⟩ := asg_view hC.asg
  have eFr : f.framesL = u.framesL := by simp [framesL, hC.frameTrail]
  refine ⟨by funext l; simp [IsTrue, h1], by funext l; simp [IsFalse, h1], by funext l; simp [lvl, h2],
    by simp [trailL, h3], eFr, by funext p; simp [pushLevel, eFr]⟩

theorem CollOut.invSAt (hC : CollOut u start P Q N f) (Pp : Nat) (c : List Lit) : f.InvSAt Pp c ↔ u.InvSAt Pp c := by
  obtain ⟨eT, eF, eL, eTr, _, eP⟩ := hC.views
  have : f.PropFalseAt = u.PropFalseAt := by
    funext Pp w k; simp only [PropFalseAt, eF, eTr, eP, eL]
  simp only [InvSAt, this, eT, eL]

theorem CollOut.inDB (hC : CollOut u start P Q N f) (h : ColPre Φ u start P Q) {c : List Lit} (hc : f.InDB c) :
    (∃ r ∈ P, u.LiveRef r ∧ c = u.clauseL r) ∨
    (∃ n ∈ N, ∃ o ∈ Q, u.LiveRef o ∧ c.Perm (filt u o) ∧ c = f.clauseL n ∧ 3 ≤ (f.arena.size n).toNat ∧
      f.arena.redundant n = u.arena.redundant o ∧ f.LiveRef n ∧
      ((∃ x ∈ filt u o, vNeg (u.asg.values.get! x.toNat) = false) →
        vNeg (u.asg.values.get! (f.lit0 n).toNat) = false)) ∨
    (∃ a b, c = [a, b] ∧ u.BinWatched a b) ∨
    (∃ a b, ∃ o ∈ Q, c = [a, b] ∧ u.LiveRef o ∧ (filt u o = [a, b] ∨ filt u o = [b, a])) := by
  rcases hc with ⟨r, hr, rfl⟩ | ⟨a, b, hab, rfl⟩
  · have hmem := hr.1; rw [hC.refs] at hmem
    rcases List.mem_append.mp hmem with hP | hN
    · obtain ⟨hlv, hcl, _⟩ := hC.liveP h hP
      exact Or.inl ⟨r, hP, hlv.mp hr, hcl⟩
    · obtain ⟨o, ho, hlo, hlf, hp, _, _, h3, _, hred, hfr⟩ := hC.liveN h hN
      exact Or.inr (Or.inl ⟨r, hN, o, ho, hlo, hp, rfl, h3, hred, hlf, hfr⟩)
  · rcases hC.binNew a b hab with ⟨h1, _, _⟩ | ⟨_, o, ho, g, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, rfl, h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, o, ho, rfl, ⟨by rw [h.refs]; simp [ho], g⟩, h2⟩))

theorem rootT_iff {u : Solver} (x : Lit) : u.rootT x = true ↔ u.IsTrue x ∧ u.lvl x = 0 := by
  unfold rootT lvl level'
  rw [isTrue_iff_vTrue]
  simp only [Bool.and_eq_true, beq_iff_eq, value]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, UInt32.toNat_inj.mp (by simpa using h2)⟩

theorem rootTrue_of_fixed {u : Solver} {x : Lit} (h : vTrue (u.fixedValue x) = true) : u.RootTrue x := by
  unfold fixedValue at h
  dsimp only at h
  split at h
  · simp [vTrue] at h
  · split at h
    · simp [vTrue] at h
    · rename_i h1 h2
      refine ⟨(isTrue_iff_vTrue u x).mpr h, ?_⟩
      unfold lvl; unfold level' at h2; simp at h2; rw [h2]; rfl

theorem clauseL_head {s : Solver} {r : Ref} (h : 1 ≤ (s.arena.size r).toNat) :
    ∃ rest, s.clauseL r = s.lit0 r :: rest := by
  unfold clauseL lit0
  obtain ⟨k, hk⟩ : ∃ k, (s.arena.size r).toNat = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  rw [hk, List.range_succ_eq_map]
  exact ⟨_, List.map_cons⟩

theorem CollOut.final (hC : CollOut u start P Q N f) (h : ColPre Φ u start P Q) :
    SInv Φ f ∧ (∀ c, f.InDB c → f.InvS c) ∧ IrrMono u f := by
  have hs := h.sinv
  obtain ⟨eT, eF, eL, eTr, eFr, eP⟩ := hC.views
  obtain ⟨v1, v2, v3, v4⟩ := asg_view hC.asg
  have hprop : f.propagate = u.propagate := hC.propagate
  have hRT : ∀ l, f.RootTrue l ↔ u.RootTrue l := by intro l; simp [RootTrue, eT, eL]
  -- the database is implied
  have hdb : DBImplied Φ f := by
    intro c hc
    rcases hC.inDB h hc with ⟨r, _, hl, rfl⟩ | ⟨n, _, o, _, hlo, hp, _, _⟩ | ⟨a, b, rfl, hab⟩ |
        ⟨a, b, o, _, rfl, hlo, hf⟩
    · exact hs.db _ (Or.inl ⟨r, hl, rfl⟩)
    · exact (implied_filt hs (hs.db _ (Or.inl ⟨o, hlo, rfl⟩))).perm (fun x hx => hp.symm.subset hx)
    · exact hs.db _ (Or.inr ⟨a, b, hab, rfl⟩)
    · have := implied_filt hs (hs.db _ (Or.inl ⟨o, hlo, rfl⟩))
      rcases hf with e | e <;> rw [e] at this
      · exact this
      · exact this.perm (fun x hx => by simp at hx ⊢; rcases hx with rfl | rfl <;> simp)
  -- the watch invariant
  have hinv : ∀ c, f.InDB c → f.InvS c := by
    intro c hc
    unfold InvS; rw [hC.invSAt, hprop]
    rcases hC.inDB h hc with ⟨r, _, hl, rfl⟩ | ⟨n, _, o, _, hlo, hp, rfl, h3, _, _, hfront⟩ | ⟨a, b, rfl, hab⟩ |
        ⟨a, b, o, _, rfl, hlo, hf⟩
    · exact h.invS _ (Or.inl ⟨r, hl, rfl⟩)
    · -- the first literal is not false
      have hlen : 2 ≤ (u.clauseL o).length := by
        have := (h.sinv.ws.live o hlo).1; unfold clauseL; simp; omega
      obtain ⟨x, hx, hxf⟩ := nonFalse_of_invS hs h.prop (h.invS _ (Or.inl ⟨o, hlo, rfl⟩)) hlen
      have hxF : x ∈ filt u o := List.mem_filter.mpr ⟨hx, by
        have : ¬ (u.IsFalse x ∧ u.lvl x = 0) := fun e => hxf e.1
        rw [← rootF_iff] at this; simpa using this⟩
      have h0 := not_false_of_vNeg (hfront ⟨x, hxF, vNeg_false_of_not_false hs.core hxf⟩)
      intro w0 w1 rest e k0 k1 hw0 _
      obtain ⟨rest', hr'⟩ := clauseL_head (s := f) (r := n) (by omega)
      rw [hr'] at e
      have : w0 = f.lit0 n := (List.cons.inj e).1.symm
      rw [this] at hw0
      exact absurd hw0.1 h0
    · exact h.invS _ (Or.inr ⟨a, b, hab, rfl⟩)
    · -- a new binary clause: its two literals are not both false
      intro w0 w1 rest e k0 k1 hw0 hw1
      exfalso
      have hlen : 2 ≤ (u.clauseL o).length := by
        have := (h.sinv.ws.live o hlo).1; unfold clauseL; simp; omega
      obtain ⟨x, hx, hxf⟩ := nonFalse_of_invS hs h.prop (h.invS _ (Or.inl ⟨o, hlo, rfl⟩)) hlen
      have hxF : x ∈ filt u o := List.mem_filter.mpr ⟨hx, by
        have : ¬ (u.IsFalse x ∧ u.lvl x = 0) := fun e => hxf e.1
        rw [← rootF_iff] at this; simpa using this⟩
      have ea : a = w0 := (List.cons.inj e).1
      have eb : b = w1 := (List.cons.inj (List.cons.inj e).2).1
      have hfa : u.IsFalse a := ea ▸ hw0.1
      have hfb : u.IsFalse b := eb ▸ hw1.1
      rcases hf with hf | hf <;> rw [hf] at hxF <;> simp at hxF <;> rcases hxF with hx' | hx' <;>
        rw [hx'] at hxf <;> first | exact hxf hfa | exact hxf hfb
  -- the irredundant clauses
  have hmono : IrrMono u f := by
    refine ⟨fun d hd => ?_, fun l hl => (hRT l).mpr hl⟩
    rcases hd with ⟨r, hl, hred, rfl⟩ | ⟨a, b, hab, rfl⟩
    · have hmem := hl.1; rw [h.refs] at hmem
      rcases List.mem_append.mp hmem with hP | hQ
      · obtain ⟨hlv, hcl, _, _, _, hr⟩ := hC.liveP h hP
        exact Or.inr ⟨u.clauseL r, Or.inl ⟨r, hlv.mpr hl, by rw [hr]; exact hred, hcl.symm⟩, fun _ h => h⟩
      · rcases hC.old r hQ hl.2 with ⟨x, hx, hxt⟩ | ⟨a, b, hf, hab, _⟩ | ⟨n, hn, hp, hrn⟩
        · exact Or.inl ⟨x, hx, (hRT x).mpr ((rootT_iff x).mp hxt)⟩
        · exact Or.inr ⟨[a, b], Or.inr ⟨a, b, hab, rfl⟩, fun x hx => filt_sub (by rw [hf]; exact hx)⟩
        · obtain ⟨_, _, _, hlf, _⟩ := hC.liveN h hn
          exact Or.inr ⟨f.clauseL n, Or.inl ⟨n, hlf, by rw [hrn]; exact hred, rfl⟩,
            fun x hx => filt_sub (hp.subset hx)⟩
    · by_cases hk : flushKeep u (u.fixedValue a) start (.bin b) = true
      · refine Or.inr ⟨[a, b], Or.inr ⟨a, b, ?_, rfl⟩, fun _ h => h⟩
        obtain ⟨_, ha, _, _⟩ := hs.ws.bin a b hab
        obtain ⟨B, E, hE, _, _⟩ := hC.ent a
        unfold BinWatched; rw [hE, if_pos (show (IDX a).toNat < u.vars.toNat from ha)]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_filter.mpr ⟨hab, hk⟩))
      · left
        have hk2 : (vTrue (u.fixedValue a) || vTrue (u.fixedValue b)) = true := by
          unfold flushKeep at hk; cases e : (vTrue (u.fixedValue a) || vTrue (u.fixedValue b)) <;> simp_all
        simp only [Bool.or_eq_true] at hk2
        rcases hk2 with hk | hk
        · exact ⟨a, by simp, (hRT a).mpr (rootTrue_of_fixed hk)⟩
        · exact ⟨b, by simp, (hRT b).mpr (rootTrue_of_fixed hk)⟩
  -- the base invariant
  have hcore : f.Core := by
    have hc := hs.core
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; rw [eT, eF]; exact hc.valCons l
    · intro l hl; rw [eT] at hl; rw [eTr, eL]; exact hc.trueOnTrail l hl
    · intro l hl; rw [eTr] at hl; rw [eT]; exact hc.trailTrue l hl
    · intro l; rw [eL]; exact hc.lvlVar l
    · unfold Sizes; rw [v1, v2, hC.vars]; exact hc.sizes
    · intro j; rw [v1]; exact hc.domain j
  have hlev : f.LevelOK := by
    have hl := hs.levelOK
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eT, eL, hC.level]; exact hl.trueLe
    · rw [eTr, eL, eP]; exact hl.pushLe
    · rw [eFr]; exact hl.sorted
    · rw [eFr, hC.level]; exact hl.len
    · rw [eFr, hprop]; exact hl.framesLe
    · rw [eTr, hprop]; exact hl.propLe
    · rw [eFr]; exact hl.strict
    · rw [eFr, eTr]; exact hl.framesLt
    · rw [hC.frameTrail]; exact hl.frames0
  have hrs : f.ReasonSizes := by
    obtain ⟨r1, r2, r3, r4, r5⟩ := hs.rsizes
    refine ⟨by rw [hC.rsz.1, hC.vars]; exact r1, by rw [hC.rsz.2, hC.vars]; exact r2, fun j hj => ?_, ?_, ?_⟩
    · rw [v1]; exact r3 j (by rw [← hC.vars]; exact hj)
    · rw [v4, v1, hC.vars]; exact r4
    · rw [eTr]; exact r5
  refine ⟨⟨hcore, hlev, hC.watchStruct h, hC.lay, fun l ht hl => ?_, fun l ht hl => ?_, hrs, hdb, ?_⟩,
    hinv, hmono⟩
  · rw [eT] at ht; rw [eL] at hl; exact hC.reasons l ht hl
  · rw [eT] at ht; rw [eL] at hl; exact hs.roots l ht hl
  · rw [Flg.options hC.flg]; exact hs.jump

end Final

theorem watchBlocking_np (t : Solver) (a b : Lit) (r : Ref) : (t.watchBlocking a b r).notPorted = t.notPorted := rfl

theorem rewatchClause_np (s : Solver) (ref : Ref) : (s.rewatchClause ref).notPorted = s.notPorted := by
  rw [rewatchClause_eq, watchBlocking_np, watchBlocking_np]
  dsimp only [rwS]

theorem rewatchClauses_np (t : Solver) (start : Ref) : (t.rewatchClauses start).notPorted = t.notPorted := by
  unfold rewatchClauses
  generalize t.arena.chain start t.arena.sizeWards = L
  induction L generalizing t with
  | nil => rfl
  | cons x L ih => simp only [List.foldl_cons]; rw [ih, rewatchClause_np]

/-- The non-compacting garbage collection. -/
theorem sparseCollect_spec {Φ : (Nat → Bool) → Prop} {u : Solver} {start : Ref} {P Q : List Ref}
    (h : ColPre Φ u start P Q) :
    (u.sparseCollect false start).notPorted = true ∨ ∃ N, CollOut u start P Q N (u.sparseCollect false start) := by
  have hp := swPre_of h
  have hsw := sweep_spec hp
  have hW := h.sinv.ws
  obtain ⟨f1, f2, f3, f4⟩ := flush_entries u start hW.varsBound hW.words
  unfold sparseCollect
  simp only [Bool.false_eq_true, ite_false]
  generalize (u.flushAllWatchedClauses start).sparseSweepGarbageClauses start = R at hsw ⊢
  obtain ⟨res, t⟩ := R
  dsimp only at hsw ⊢
  by_cases hres : (res != INVALID_REF) = true
  · rw [if_pos hres]; exact Or.inl rfl
  rw [if_neg hres]
  rcases hsw with hf | ⟨N, hO⟩
  · left; rw [rewatchClauses_np]; exact hf
  right
  refine ⟨N, collOut_of h hO (rewatch_spec hO.lnew ?_ ?_ hO.lay hO.words)⟩
  · intro n hn x hx
    obtain ⟨o, ho, g, hlit, _⟩ := hO.newCl n hn
    rw [hlit] at hx
    have hv := (hp.live o ho g).1 x (filt_sub hx)
    obtain ⟨b1, b2⟩ := validLit_bounds hp.watchesSize hp.varsBound hv
    exact ⟨by rw [hO.wsz]; exact b1, b2⟩
  · intro n hn
    obtain ⟨_, _, _, _, _, _, _, h3⟩ := hO.newCl n hn
    omega

end Solver
end LeanKissat
