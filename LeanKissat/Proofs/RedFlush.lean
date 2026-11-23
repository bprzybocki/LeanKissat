import LeanKissat.Proofs.Main
import LeanKissat.Proofs.RadixMem

/-!
# `reduce`: flushing the watch lists (`flush_all_watched_clauses`, `compact = false`)
-/

namespace LeanKissat
namespace Solver
open Arena

/-- The solver without its variable flags and statistics. -/
def strip (s : Solver) : Solver := { s with flags := default, stats := default }

/-- The solver without flags, statistics and watch lists. -/
def stripW (s : Solver) : Solver := { s with flags := default, stats := default, watches := #[] }

theorem stripW_of_strip {s t : Solver} (h : strip t = strip s) : stripW t = stripW s := by
  have := congrArg (fun x : Solver => { x with watches := #[] }) h
  exact this

theorem strip_markRemovedLiteral (s : Solver) (l : Lit) : strip (s.markRemovedLiteral l) = strip s := by
  unfold markRemovedLiteral
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem strip_deleteBinary (s : Solver) (a b : Lit) : strip (s.deleteBinary a b) = strip s := by
  unfold deleteBinary decClause
  dsimp only
  have h1 := strip_markRemovedLiteral s a
  have h2 := strip_markRemovedLiteral (s.markRemovedLiteral a) b
  generalize (s.markRemovedLiteral a).markRemovedLiteral b = u at h2
  generalize s.markRemovedLiteral a = u' at h1 h2
  simp only [ite_true]
  exact (show strip { u with stats := _ } = strip u from rfl).trans (h2.trans h1)

theorem fixedValue_congr {s t : Solver} (h : t.asg = s.asg) (l : Lit) : t.fixedValue l = s.fixedValue l := by
  simp [fixedValue, value, level', h]

/-- Entries kept by `flushLoop`. -/
def flushKeep (s : Solver) (litFixed : Value) (start : Ref) : WEntry → Bool
  | .bin o => !(vTrue litFixed || vTrue (s.fixedValue o))
  | .large _ r => Decidable.decide (r < start)

theorem watchRef_largeWatch (r : Ref) (hr : r.toNat < 2 ^ 31) : watchRef (largeWatch r) = r := by
  have := lt31 hr
  simp only [watchRef, largeWatch]; bv_k

theorem watchLit_blocking (b : Lit) (hb : b.toNat < 2 ^ 31) : watchLit (blockingWatch b) = b := by
  have := lt31 hb
  simp only [watchLit, blockingWatch]; bv_k

theorem watchLit_binary (b : Lit) (hb : b.toNat < 2 ^ 31) : watchLit (binaryWatch b) = b := by
  have := lt31 hb
  simp only [watchLit, binaryWatch, WATCH_BINARY_BIT]; bv_k

theorem wvec_push_toList (w : WVec) (x : UInt32) : (w.push x).data.toList = w.data.toList ++ [x] := by
  simp [WVec.push]

theorem flushLoop_spec (lit : Lit) (litFixed : Value) (start : Ref) (ws : WVec) (s0 : Solver) :
    ∀ (s : Solver) (out : WVec) (p : Nat) (R : List WEntry), strip s = strip s0 →
    ws.data.toList.drop p = encodeWatches R → (∀ e ∈ R, e.WF) →
    strip (flushLoop lit litFixed start ws s out p).1 = strip s0 ∧
    (flushLoop lit litFixed start ws s out p).2.data.toList =
      out.data.toList ++ encodeWatches (R.filter (flushKeep s0 litFixed start)) := by
  intro s out p
  induction s, out, p using flushLoop.induct lit litFixed start ws with
  | case1 s out p hp head hb other hfix ih =>
    intro R hs hd hwf
    have hb' : watchIsBinary ws[p] = true := hb
    have hfix' : (vTrue litFixed || vTrue (s.fixedValue (watchLit ws[p]))) = true := hfix
    rw [flushLoop, dite_eq_left hp]; dsimp only; rw [ite_eq_left hb', ite_eq_left hfix']
    have hL : p < ws.data.toList.length := by simpa [WVec.size] using hp
    have hw : ws[p] = ws.data.toList[p] := wvec_getElem_eq ws p hp
    cases R with
    | nil => exfalso; have : ws.data.toList.drop p = [] := by simpa [encodeWatches] using hd
             rw [List.drop_eq_nil_iff] at this; omega
    | cons e R =>
    cases e with
    | large b r =>
      exfalso
      have hd' : ws.data.toList.drop p = blockingWatch b :: (largeWatch r :: encodeWatches R) := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, _⟩ := drop_cons_getElem _ _ _ _ hd'
      have := blocking_not_binary b (hwf _ (List.mem_cons_self ..)).1
      rw [← h1, ← hw] at this; exact absurd (hb'.symm.trans this) (by simp)
    | bin o =>
      have hd' : ws.data.toList.drop p = binaryWatch o :: encodeWatches R := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, h2⟩ := drop_cons_getElem _ _ _ _ hd'
      have ho : other = o := by
        show watchLit ws[p] = o
        rw [hw, h1]; exact watchLit_binary o (hwf _ (List.mem_cons_self ..))
      have hs' : strip (if lit < watchLit ws[p] then s.deleteBinary lit (watchLit ws[p]) else s) = strip s0 := by
        split
        · rw [strip_deleteBinary]; exact hs
        · exact hs
      obtain ⟨k1, k2⟩ := ih R (by exact hs') h2 (fun e he => hwf e (List.mem_cons_of_mem _ he))
      simp only [dite_eq_ite] at k1 k2
      refine ⟨k1, ?_⟩
      rw [k2]
      have hasg : s.asg = s0.asg := by have := congrArg Solver.asg hs; exact this
      have hk : flushKeep s0 litFixed start (.bin o) = false := by
        simp only [flushKeep, ← ho, ← fixedValue_congr hasg other]; simp [hfix]
      simp [hk]
  | case2 s out p hp head hb other hfix ih =>
    intro R hs hd hwf
    have hb' : watchIsBinary ws[p] = true := hb
    have hfix' : ¬ (vTrue litFixed || vTrue (s.fixedValue (watchLit ws[p]))) = true := hfix
    rw [flushLoop, dite_eq_left hp]; dsimp only; rw [ite_eq_left hb', ite_eq_right hfix']
    have hL : p < ws.data.toList.length := by simpa [WVec.size] using hp
    have hw : ws[p] = ws.data.toList[p] := wvec_getElem_eq ws p hp
    cases R with
    | nil => exfalso; have : ws.data.toList.drop p = [] := by simpa [encodeWatches] using hd
             rw [List.drop_eq_nil_iff] at this; omega
    | cons e R =>
    cases e with
    | large b r =>
      exfalso
      have hd' : ws.data.toList.drop p = blockingWatch b :: (largeWatch r :: encodeWatches R) := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, _⟩ := drop_cons_getElem _ _ _ _ hd'
      have := blocking_not_binary b (hwf _ (List.mem_cons_self ..)).1
      rw [← h1, ← hw] at this; exact absurd (hb'.symm.trans this) (by simp)
    | bin o =>
      have hd' : ws.data.toList.drop p = binaryWatch o :: encodeWatches R := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, h2⟩ := drop_cons_getElem _ _ _ _ hd'
      have ho : other = o := by
        show watchLit ws[p] = o
        rw [hw, h1]; exact watchLit_binary o (hwf _ (List.mem_cons_self ..))
      obtain ⟨k1, k2⟩ := ih R hs h2 (fun e he => hwf e (List.mem_cons_of_mem _ he))
      refine ⟨k1, ?_⟩
      rw [k2, wvec_push_toList]
      have hasg : s.asg = s0.asg := by have := congrArg Solver.asg hs; exact this
      have hk : flushKeep s0 litFixed start (.bin o) = true := by
        simp only [flushKeep, ← ho, ← fixedValue_congr hasg other]; simpa using hfix
      simp [hk, encodeWatches, WEntry.words, ho]
  | case3 s out p hp head hb tail hlt ih =>
    intro R hs hd hwf
    have hb' : ¬ watchIsBinary ws[p] = true := hb
    have hlt' : watchRef (ws.get! (p + 1)) < start := hlt
    rw [flushLoop, dite_eq_left hp]; dsimp only; rw [ite_eq_right hb', ite_eq_left hlt']
    have hL : p < ws.data.toList.length := by simpa [WVec.size] using hp
    have hw : ws[p] = ws.data.toList[p] := wvec_getElem_eq ws p hp
    cases R with
    | nil => exfalso; have : ws.data.toList.drop p = [] := by simpa [encodeWatches] using hd
             rw [List.drop_eq_nil_iff] at this; omega
    | cons e R =>
    cases e with
    | bin o =>
      exfalso
      have hd' : ws.data.toList.drop p = binaryWatch o :: encodeWatches R := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, _⟩ := drop_cons_getElem _ _ _ _ hd'
      have := binary_is_binary o (hwf _ (List.mem_cons_self ..))
      rw [← h1, ← hw] at this; exact hb' this
    | large b r =>
      have hd' : ws.data.toList.drop p = blockingWatch b :: (largeWatch r :: encodeWatches R) := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, h2⟩ := drop_cons_getElem _ _ _ _ hd'
      obtain ⟨_, h3, h4⟩ := drop_cons_getElem _ _ _ _ h2
      have hwf1 := hwf _ (List.mem_cons_self ..)
      have ht : tail = largeWatch r := by
        show ws.get! (p + 1) = _
        rw [wvec_get!_eq ws (p + 1) (by omega), h3]
      have hr : watchRef tail = r := by rw [ht]; exact watchRef_largeWatch r hwf1.2
      obtain ⟨k1, k2⟩ := ih R hs (by rw [show p + 2 = p + 1 + 1 by omega]; exact h4)
        (fun e he => hwf e (List.mem_cons_of_mem _ he))
      refine ⟨k1, ?_⟩
      rw [k2, wvec_push_toList, wvec_push_toList]
      have hk : flushKeep s0 litFixed start (.large b r) = true := by
        simp only [flushKeep, ← hr]; simpa using hlt
      have hh : head = blockingWatch b := by show ws[p] = _; rw [hw, h1]
      simp [hk, encodeWatches, WEntry.words, hh, ht]
  | case4 s out p hp head hb tail hlt ih =>
    intro R hs hd hwf
    have hb' : ¬ watchIsBinary ws[p] = true := hb
    have hlt' : ¬ watchRef (ws.get! (p + 1)) < start := hlt
    rw [flushLoop, dite_eq_left hp]; dsimp only; rw [ite_eq_right hb', ite_eq_right hlt']
    have hL : p < ws.data.toList.length := by simpa [WVec.size] using hp
    have hw : ws[p] = ws.data.toList[p] := wvec_getElem_eq ws p hp
    cases R with
    | nil => exfalso; have : ws.data.toList.drop p = [] := by simpa [encodeWatches] using hd
             rw [List.drop_eq_nil_iff] at this; omega
    | cons e R =>
    cases e with
    | bin o =>
      exfalso
      have hd' : ws.data.toList.drop p = binaryWatch o :: encodeWatches R := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, _⟩ := drop_cons_getElem _ _ _ _ hd'
      have := binary_is_binary o (hwf _ (List.mem_cons_self ..))
      rw [← h1, ← hw] at this; exact hb' this
    | large b r =>
      have hd' : ws.data.toList.drop p = blockingWatch b :: (largeWatch r :: encodeWatches R) := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, h2⟩ := drop_cons_getElem _ _ _ _ hd'
      obtain ⟨_, h3, h4⟩ := drop_cons_getElem _ _ _ _ h2
      have hwf1 := hwf _ (List.mem_cons_self ..)
      have ht : tail = largeWatch r := by
        show ws.get! (p + 1) = _
        rw [wvec_get!_eq ws (p + 1) (by omega), h3]
      have hr : watchRef tail = r := by rw [ht]; exact watchRef_largeWatch r hwf1.2
      obtain ⟨k1, k2⟩ := ih R hs (by rw [show p + 2 = p + 1 + 1 by omega]; exact h4)
        (fun e he => hwf e (List.mem_cons_of_mem _ he))
      refine ⟨k1, ?_⟩
      rw [k2]
      have hk : flushKeep s0 litFixed start (.large b r) = false := by
        simp only [flushKeep, ← hr]; simpa using hlt
      simp [hk]
  | case5 s out p hp =>
    intro R hs hd hwf
    rw [flushLoop, dite_eq_right hp]
    refine ⟨hs, ?_⟩
    cases R with
    | nil => simp [encodeWatches]
    | cons e R =>
      exfalso
      have hL : ws.data.toList.length ≤ p := by simpa [WVec.size] using hp
      rw [List.drop_eq_nil_of_le hL] at hd
      cases e <;> simp [encodeWatches, WEntry.words] at hd

theorem watchesOf_modify (s : Solver) (lit l : Lit) (f : WVec → WVec) :
    (s.modifyWatches lit f).watchesOf l =
      if l = lit ∧ lit.toNat < s.watches.size then f (s.watchesOf lit) else s.watchesOf l := by
  show (s.watches.modify lit.toNat f)[l.toNat]! = _
  by_cases hl : l.toNat < s.watches.size
  · rw [getElem!_pos (s.watches.modify lit.toNat f) l.toNat (by simpa using hl), Array.getElem_modify]
    by_cases e : l = lit
    · subst e; simp [hl, watchesOf]
    · have : lit.toNat ≠ l.toNat := fun h => e (UInt32.toNat_inj.mp h).symm
      simp [this, e, watchesOf, getElem!_pos s.watches l.toNat hl]
  · have e : ¬ (l = lit ∧ lit.toNat < s.watches.size) := by
      rintro ⟨rfl, h⟩; exact hl h
    rw [ite_eq_right e, getElem!_neg _ l.toNat (by simpa using hl)]
    simp only [watchesOf]; rw [getElem!_neg s.watches l.toNat hl]

theorem modifyWatches_size (s : Solver) (lit : Lit) (f : WVec → WVec) :
    (s.modifyWatches lit f).watches.size = s.watches.size := by
  simp [modifyWatches]

theorem watchesOf_oob {s : Solver} {l : Lit} (h : ¬ l.toNat < s.watches.size) : s.watchesOf l = default := by
  simp only [watchesOf]; rw [getElem!_neg s.watches l.toNat h]

/-- The kept words of the watch list of `lit`. -/
def flushedWords (s : Solver) (lit : Lit) (start : Ref) : List UInt32 :=
  encodeWatches ((s.entries lit).filter (flushKeep s (s.fixedValue lit) start))

theorem flushLit_spec (s : Solver) (lit : Lit) (start : Ref) (hw : WordsOK (s.watchesOf lit).data.toList) :
    stripW (s.flushWatchedClausesByLiteral lit start) = stripW s ∧
    (s.flushWatchedClausesByLiteral lit start).watches.size = s.watches.size ∧
    ∀ l, ((s.flushWatchedClausesByLiteral lit start).watchesOf l).data.toList =
      if l = lit then flushedWords s lit start else (s.watchesOf l).data.toList := by
  unfold flushWatchedClausesByLiteral
  have k := flushLoop_spec lit (s.fixedValue lit) start (s.watchesOf lit) s s WVec.empty 0 (s.entries lit) rfl
    (by simp only [List.drop_zero, entries]; rw [encode_parse _ hw]) (parse_wf _)
  generalize flushLoop lit (s.fixedValue lit) start (s.watchesOf lit) s WVec.empty 0 = r at k
  obtain ⟨k1, k2⟩ := k
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · show stripW { r.1 with watches := _ } = _
    exact (show stripW { r.1 with watches := r.1.watches.modify lit.toNat (fun _ => r.2) } = stripW r.1 from rfl).trans
      (stripW_of_strip k1)
  · rw [modifyWatches_size]; have := congrArg Solver.watches k1; exact congrArg Array.size this
  · intro l
    have hws : r.1.watches = s.watches := by have := congrArg Solver.watches k1; exact this
    rw [watchesOf_modify]
    have hwo : ∀ x, r.1.watchesOf x = s.watchesOf x := by intro x; simp [watchesOf, hws]
    by_cases e : l = lit
    · subst e
      by_cases hlt : l.toNat < r.1.watches.size
      · rw [ite_eq_left ⟨rfl, hlt⟩, ite_eq_left rfl, k2]; simp [WVec.empty, flushedWords]
      · rw [ite_eq_right (fun h => hlt h.2), ite_eq_left rfl, hwo]
        rw [hws] at hlt
        unfold flushedWords entries
        rw [watchesOf_oob hlt]; rfl
    · rw [ite_eq_right (fun h => e h.1), ite_eq_right e, hwo]

theorem flushedWords_congr {s t : Solver} (ha : t.asg = s.asg) (lit : Lit)
    (hw : (t.watchesOf lit).data.toList = (s.watchesOf lit).data.toList) (start : Ref) :
    flushedWords t lit start = flushedWords s lit start := by
  unfold flushedWords entries
  rw [hw]
  have : t.fixedValue lit = s.fixedValue lit := fixedValue_congr ha lit
  rw [this]
  congr 2
  funext e; cases e <;> simp [flushKeep, fixedValue_congr ha]

theorem flushAllLoop_spec (s0 : Solver) (start : Ref) (n : Nat) (hn : n < 2 ^ 30)
    (hw0 : ∀ l, WordsOK (s0.watchesOf l).data.toList) :
    ∀ s i, stripW s = stripW s0 → s.watches.size = s0.watches.size →
    (∀ l, (s.watchesOf l).data.toList =
      if (IDX l).toNat < i then flushedWords s0 l start else (s0.watchesOf l).data.toList) →
    stripW (flushAllLoop start n s i) = stripW s0 ∧ (flushAllLoop start n s i).watches.size = s0.watches.size ∧
    ∀ l, ((flushAllLoop start n s i).watchesOf l).data.toList =
      if (IDX l).toNat < max i n then flushedWords s0 l start else (s0.watchesOf l).data.toList := by
  intro s i
  induction s, i using flushAllLoop.induct start n with
  | case1 s i hi lit ih =>
    intro hs hsz hws
    rw [flushAllLoop, ite_eq_left hi]
    dsimp only
    have hasg : s.asg = s0.asg := by have := congrArg Solver.asg hs; exact this
    have hidx : (IDX lit).toNat = i := by
      show (IDX (LIT (UInt32.ofNat i))).toNat = i
      rw [IDX_LIT_toNat _ (by simp; omega)]; simp; omega
    have hne : NOT lit ≠ lit := NOT_ne lit
    have w1 : WordsOK (s.watchesOf lit).data.toList := by
      rw [hws lit, ite_eq_right (by omega)]; exact hw0 lit
    obtain ⟨a1, a2, a3⟩ := flushLit_spec s lit start w1
    generalize s.flushWatchedClausesByLiteral lit start = s1 at a1 a2 a3 ih
    have w2 : WordsOK (s1.watchesOf (NOT lit)).data.toList := by
      rw [a3, ite_eq_right hne, hws, ite_eq_right (by rw [IDX_NOT]; omega)]; exact hw0 _
    obtain ⟨b1, b2, b3⟩ := flushLit_spec s1 (NOT lit) start w2
    generalize s1.flushWatchedClausesByLiteral (NOT lit) start = s2 at b1 b2 b3 ih
    have hasg1 : s1.asg = s0.asg := by have := congrArg Solver.asg (a1.trans hs); exact this
    rw [show max i n = max (i + 1) n by omega]
    refine ih (b1.trans (a1.trans hs)) (by rw [b2, a2, hsz]) ?_
    intro l
    rw [b3]
    by_cases e2 : l = NOT lit
    · subst e2
      rw [ite_eq_left rfl, ite_eq_left (by rw [IDX_NOT]; omega)]
      apply flushedWords_congr hasg1
      have := a3 (NOT lit); rw [ite_eq_right hne] at this
      rw [this, hws, ite_eq_right (by rw [IDX_NOT]; omega)]
    · rw [ite_eq_right e2, a3]
      by_cases e1 : l = lit
      · subst e1
        rw [ite_eq_left rfl, ite_eq_left (by omega)]
        apply flushedWords_congr hasg
        have := hws lit; rw [ite_eq_right (by omega)] at this
        exact this
      · rw [ite_eq_right e1, hws]
        have hl : (IDX l).toNat ≠ i := by
          intro h
          rcases (IDX_eq_iff l lit).mp (UInt32.toNat_inj.mp (h.trans hidx.symm)) with h' | h'
          · exact e1 h'
          · exact e2 h'
        by_cases hli : (IDX l).toNat < i
        · rw [ite_eq_left hli, ite_eq_left (by omega)]
        · rw [ite_eq_right hli, ite_eq_right (by omega)]
  | case2 s i hi =>
    intro hs hsz hws
    rw [flushAllLoop, ite_eq_right hi]
    refine ⟨hs, hsz, fun l => ?_⟩
    rw [hws l, show max i n = i by omega]

theorem flushAll_spec (s : Solver) (start : Ref) (hv : s.vars.toNat < 2 ^ 30)
    (hw : ∀ l, WordsOK (s.watchesOf l).data.toList) :
    stripW (s.flushAllWatchedClauses start) = stripW s ∧
    (s.flushAllWatchedClauses start).watches.size = s.watches.size ∧
    ∀ l, ((s.flushAllWatchedClauses start).watchesOf l).data.toList =
      if (IDX l).toNat < s.vars.toNat then flushedWords s l start else (s.watchesOf l).data.toList := by
  have := flushAllLoop_spec s start s.vars.toNat hv hw s 0 rfl rfl (fun l => by simp)
  unfold flushAllWatchedClauses
  obtain ⟨h1, h2, h3⟩ := this
  refine ⟨h1, h2, fun l => ?_⟩
  rw [h3 l]; simp

end Solver
end LeanKissat
