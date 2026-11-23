import LeanKissat.Proofs.LearnSpec

/-!
# Adding watches for a new clause
-/

namespace LeanKissat
namespace Solver
open Arena

theorem parse_push_entry (L : List UInt32) (hL : WordsOK L) (e : WEntry) (he : e.WF) :
    parseWatches (L ++ e.words) = parseWatches L ++ [e] ∧ WordsOK (L ++ e.words) := by
  have h1 : L ++ e.words = encodeWatches (parseWatches L ++ [e]) := by
    rw [encode_append, encode_parse _ hL]; simp [encodeWatches]
  rw [h1]
  exact parse_encode _ (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact parse_wf L x hx
    · simp at hx; subst hx; exact he)

/-- Adding the entry `e` to the watch list of `lit`. -/
def AddsEntry (t s : Solver) (lit : Lit) (e : WEntry) : Prop :=
  ∀ l, (t.watchesOf l).data.toList = if l = lit then (s.watchesOf l).data.toList ++ e.words
    else (s.watchesOf l).data.toList

theorem watchOther_adds (s : Solver) (lit other : Lit) (hlt : lit.toNat < s.watches.size) :
    AddsEntry (s.watchOther lit other) s lit (.bin other) := by
  intro l
  show ((s.watches.modify lit.toNat (·.push (binaryWatch other)))[l.toNat]!).data.toList = _
  by_cases hl : l.toNat < s.watches.size
  · simp only [watchesOf]
    rw [getElem!_pos (s.watches.modify lit.toNat (·.push (binaryWatch other))) l.toNat (by simpa using hl),
      getElem!_pos s.watches l.toNat hl, Array.getElem_modify]
    by_cases e : l = lit
    · subst e; simp [WVec.push, WEntry.words]
    · have : lit.toNat ≠ l.toNat := fun h => e (UInt32.toNat_inj.mp h).symm
      simp [this, e]
  · have e : l ≠ lit := by intro h; subst h; exact hl hlt
    simp only [watchesOf, e, ite_false]
    rw [getElem!_neg _ l.toNat (by simpa using hl), getElem!_neg s.watches l.toNat hl]

theorem watchBlocking_adds (s : Solver) (lit b : Lit) (r : Ref) (hlt : lit.toNat < s.watches.size) :
    AddsEntry (s.watchBlocking lit b r) s lit (.large b r) := by
  intro l
  show ((s.watches.modify lit.toNat (fun w => (w.push (blockingWatch b)).push (largeWatch r)))[l.toNat]!).data.toList = _
  by_cases hl : l.toNat < s.watches.size
  · simp only [watchesOf]
    rw [getElem!_pos (s.watches.modify lit.toNat (fun w => (w.push (blockingWatch b)).push (largeWatch r))) l.toNat
      (by simpa using hl), getElem!_pos s.watches l.toNat hl, Array.getElem_modify]
    by_cases e : l = lit
    · subst e; simp [WVec.push, WEntry.words]
    · have : lit.toNat ≠ l.toNat := fun h => e (UInt32.toNat_inj.mp h).symm
      simp [this, e]
  · have e : l ≠ lit := by intro h; subst h; exact hl hlt
    simp only [watchesOf, e, ite_false]
    rw [getElem!_neg _ l.toNat (by simpa using hl), getElem!_neg s.watches l.toNat hl]

theorem AddsEntry.entries {t s : Solver} {lit : Lit} {e : WEntry} (h : AddsEntry t s lit e)
    (hW : ∀ l, WordsOK (s.watchesOf l).data.toList) (he : e.WF) :
    ∀ l, t.entries l = (if l = lit then s.entries l ++ [e] else s.entries l) ∧
      WordsOK (t.watchesOf l).data.toList := by
  intro l
  unfold Solver.entries
  rw [h l]
  split
  · exact parse_push_entry _ (hW l) e he
  · exact ⟨rfl, hW l⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem validLit_toNat {s : Solver} (hW : s.WatchStruct) {l : Lit} (h : s.ValidLit l) :
    l.toNat < 2 * s.vars.toNat ∧ l.toNat < 2 ^ 31 ∧ l.toNat < s.watches.size := by
  unfold ValidLit at h; rw [IDX_toNat] at h
  have := hW.varsBound; have := hW.watchesSize
  omega

theorem countRef_append_bin (r : Ref) (L : List WEntry) (b : Lit) :
    countRef r (L ++ [WEntry.bin b]) = countRef r L := by
  simp [countRef_append, countRef]

/-- Watching a new binary clause `a ∨ b`. -/
theorem watchBinary_ws {s : Solver} (hW : s.WatchStruct) {a b : Lit} (ha : s.ValidLit a) (hb : s.ValidLit b)
    (hab : a ≠ b) :
    (s.watchBinary a b).WatchStruct ∧
    (∀ x y, (s.watchBinary a b).BinWatched x y ↔ s.BinWatched x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)) ∧
    (∀ l (b' : Lit) (r : Ref), WEntry.large b' r ∈ (s.watchBinary a b).entries l ↔ WEntry.large b' r ∈ s.entries l) ∧
    (∀ l r, countRef r ((s.watchBinary a b).entries l) = countRef r (s.entries l)) := by
  obtain ⟨_, ha31, haw⟩ := validLit_toNat hW ha
  obtain ⟨_, hb31, hbw⟩ := validLit_toNat hW hb
  have h1 := watchOther_adds s a b haw
  have hsz1 : (s.watchOther a b).watches.size = s.watches.size := by simp [watchOther, modifyWatches]
  have h2 := watchOther_adds (s.watchOther a b) b a (by rw [hsz1]; exact hbw)
  have e1 := h1.entries hW.words (show WEntry.WF (.bin b) from hb31)
  have e2 := h2.entries (fun l => (e1 l).2) (show WEntry.WF (.bin a) from ha31)
  have hent : ∀ l, (s.watchBinary a b).entries l =
      (s.entries l ++ (if l = a then [WEntry.bin b] else [])) ++ (if l = b then [WEntry.bin a] else []) := by
    intro l
    show (s.watchOther a b |>.watchOther b a).entries l = _
    rw [(e2 l).1, (e1 l).1]
    by_cases ea : l = a <;> by_cases eb : l = b <;> simp [ea, eb, hab, Ne.symm hab]
  have hbin : ∀ x y, (s.watchBinary a b).BinWatched x y ↔ s.BinWatched x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
    intro x y
    unfold BinWatched
    rw [hent]
    by_cases ea : x = a <;> by_cases eb : x = b
    · subst ea; exact absurd eb hab
    · subst ea
      simp only [ite_true, eb, ite_false, List.append_nil, List.mem_append, List.mem_singleton, WEntry.bin.injEq,
        true_and, false_and, or_false]
    · subst eb
      simp only [ite_true, ea, ite_false, List.append_nil, List.mem_append, List.mem_singleton, WEntry.bin.injEq,
        true_and, false_and, false_or]
    · simp [ea, eb]
  have hlarge : ∀ l (b' : Lit) (r : Ref), WEntry.large b' r ∈ (s.watchBinary a b).entries l ↔
      WEntry.large b' r ∈ s.entries l := by
    intro l b' r; rw [hent]; by_cases ea : l = a <;> by_cases eb : l = b <;> simp [ea, eb]
  have hcount : ∀ l r, countRef r ((s.watchBinary a b).entries l) = countRef r (s.entries l) := by
    intro l r; rw [hent]
    by_cases ea : l = a <;> by_cases eb : l = b <;> simp [ea, eb, hab, Ne.symm hab, countRef_append, countRef]
  have eArena : (s.watchBinary a b).arena = s.arena := rfl
  refine ⟨⟨fun l => ?_, ?_, ?_, ?_, hW.delayed, ?_, hW.varsBound⟩, hbin, hlarge, hcount⟩
  · exact (e2 l).2
  · intro l b' r hm
    exact hW.refOK l b' r ((hlarge l b' r).mp hm)
  · intro r hr
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hW.live r hr
    exact ⟨g1, g2, g3, g4, by rw [show (s.watchBinary a b).lit0 r = s.lit0 r from rfl, hcount]; exact g5,
      by rw [show (s.watchBinary a b).lit1 r = s.lit1 r from rfl, hcount]; exact g6, g7⟩
  · intro x y hxy
    rcases (hbin x y).mp hxy with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨k1, k2, k3, k4⟩ := hW.bin x y h
      exact ⟨(hbin y x).mpr (Or.inl k1), k2, k3, k4⟩
    · exact ⟨(hbin _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ha, hb, hab⟩
    · exact ⟨(hbin _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), hb, ha, Ne.symm hab⟩
  · show 2 * s.vars.toNat ≤ (s.watchBinary a b).watches.size
    have : (s.watchBinary a b).watches.size = s.watches.size := by simp [watchBinary, watchOther, modifyWatches]
    rw [this]; exact hW.watchesSize

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem _root_.LeanKissat.Arena.Alloc.litsL_new {a b : Arena} {r : Ref} {red : Bool} {glue : UInt32} {lits : U32Vec}
    (h : Alloc a b r red glue lits) (hn : lits.size < 2 ^ 32) : b.litsL r = lits.view := by
  unfold litsL
  rw [h.size, UInt32.toNat_ofNat_of_lt' hn]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  simp at h1
  rw [h.lit i h1, U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem _root_.LeanKissat.Arena.Alloc.litsL_old {a b : Arena} {r : Ref} {red : Bool} {glue : UInt32} {lits : U32Vec}
    (h : Alloc a b r red glue lits) (hl : a.Layout) {x : Ref} (hx : x ∈ a.chain 0 a.sizeWards) :
    b.litsL x = a.litsL x := by
  obtain ⟨_, e2, _, e4⟩ := h.oldReads hl hx
  unfold litsL; rw [e2]
  apply List.map_congr_left; intro i hi; exact e4 i (by simpa using hi)

theorem _root_.LeanKissat.Arena.Alloc.ref_not_old {a b : Arena} {r : Ref} {red : Bool} {glue : UInt32} {lits : U32Vec}
    (h : Alloc a b r red glue lits) (hl : a.Layout) {x : Ref} (hx : x ∈ a.chain 0 a.sizeWards) : x ≠ r := by
  intro e; subst e
  have h1 := hl.mem_bounds hx
  have h2 := wardsOfClause_pos (a.size x).toNat
  have h3 := h.ref
  omega

/-- The watch structure after allocating a new large clause and watching its first two literals. -/
theorem allocWatch_ws {s : Solver} (hW : s.WatchStruct) (hl : s.arena.Layout) {b : Arena} {r : Ref} {red : Bool}
    {glue : UInt32} {lits : U32Vec} (hA : Alloc s.arena b r red glue lits) (hch : b.chain 0 b.sizeWards = s.arena.chain 0 s.arena.sizeWards ++ [r])
    (hn : 3 ≤ lits.size) (hn32 : lits.size < 2 ^ 32) (hnd : lits.view.Nodup)
    (hv : ∀ x ∈ lits.view, s.ValidLit x)
    {s1 : Solver} (hs1 : s1 = ({ s with arena := b } : Solver)) {k0 k1 : Lit} (hk0 : lits.get! 0 = k0)
    (hk1 : lits.get! 1 = k1) {t : Solver} (ht : t = (s1.watchBlocking k0 k1 r).watchBlocking k1 k0 r) :
    t.WatchStruct ∧ (∀ x y, t.BinWatched x y ↔ s.BinWatched x y) ∧
    (∀ x, t.LiveRef x ↔ s.LiveRef x ∨ x = r) ∧ (∀ x, s.LiveRef x → t.clauseL x = s.clauseL x) ∧
    t.clauseL r = lits.view := by
  have hmem0 : lits.get! 0 ∈ lits.view := U32Vec.get!_mem_view _ _ (by omega)
  have hmem1 : lits.get! 1 ∈ lits.view := U32Vec.get!_mem_view _ _ (by omega)
  have hne01 : lits.get! 0 ≠ lits.get! 1 := by
    intro e
    rw [List.Nodup, List.pairwise_iff_getElem] at hnd
    have := hnd 0 1 (by simp; omega) (by simp; omega) (by omega)
    apply this
    rw [U32Vec.get!_eq_view, U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by simp; omega)] at e
    simpa using e
  rw [hk0] at hmem0 hne01
  rw [hk1] at hmem1 hne01
  obtain ⟨_, k0_31, k0w⟩ := validLit_toNat hW (hv _ hmem0)
  obtain ⟨_, k1_31, k1w⟩ := validLit_toNat hW (hv _ hmem1)
  have hr31 : r.toNat < 2 ^ 31 := by
    have := hA.bound; have := hA.sizeWards; have := wardsOfClause_pos lits.size; rw [hA.ref]; omega
  have ew1 : s1.watches = s.watches := by rw [hs1]
  have eE1 : s1.entries = s.entries := by funext l; simp [entries, watchesOf, ew1]
  have h1 := watchBlocking_adds s1 k0 k1 r (by rw [ew1]; exact k0w)
  have hsz1 : (s1.watchBlocking k0 k1 r).watches.size = s.watches.size := by
    simp [watchBlocking, modifyWatches, ew1]
  have h2 := watchBlocking_adds (s1.watchBlocking k0 k1 r) k1 k0 r (by rw [hsz1]; exact k1w)
  have hw1 : ∀ l, WordsOK (s1.watchesOf l).data.toList := by
    intro l; simp only [watchesOf, ew1]; exact hW.words l
  have e1 := h1.entries hw1 (show WEntry.WF (.large k1 r) from ⟨k1_31, hr31⟩)
  have e2 := h2.entries (fun l => (e1 l).2) (show WEntry.WF (.large k0 r) from ⟨k0_31, hr31⟩)
  have hent : ∀ l, t.entries l = (s.entries l ++ (if l = k0 then [WEntry.large k1 r] else [])) ++
      (if l = k1 then [WEntry.large k0 r] else []) := by
    intro l
    rw [ht, (e2 l).1, (e1 l).1, eE1]
    by_cases ea : l = k0 <;> by_cases eb : l = k1 <;> simp [ea, eb, hne01, Ne.symm hne01]
  have eArena : t.arena = b := by rw [ht, hs1]; rfl
  have eVars : t.vars = s.vars := by rw [ht, hs1]; rfl
  have eDel : t.delayed = s.delayed := by rw [ht, hs1]; rfl
  have hold : ∀ {x : Ref}, x ∈ s.arena.chain 0 s.arena.sizeWards → _ := fun {x} hx => hA.oldReads hl (x := x) hx
  have hchain_old : ∀ x, x ∈ s.arena.chain 0 s.arena.sizeWards → x ∈ b.chain 0 b.sizeWards := by
    intro x hx; rw [hch]; exact List.mem_append_left _ hx
  have hgar_old : ∀ x, x ∈ s.arena.chain 0 s.arena.sizeWards → b.garbage x = s.arena.garbage x := by
    intro x hx; unfold garbage flag; rw [(hold hx).1]
  have hlit_old : ∀ x, x ∈ s.arena.chain 0 s.arena.sizeWards → ∀ i, i < 2 → i < (s.arena.size x).toNat →
      b.lit x i = s.arena.lit x i := fun x hx i _ hi => (hold hx).2.2.2 i hi
  have hrefs_old : ∀ l b' x, WEntry.large b' x ∈ s.entries l → x ≠ r := by
    intro l b' x hm
    exact hA.ref_not_old hl (hW.refOK l b' x hm).1
  have hcnt_old : ∀ l, countRef r (s.entries l) = 0 := by
    intro l
    suffices h : ∀ L : List WEntry, (∀ b' x, WEntry.large b' x ∈ L → x ≠ r) → countRef r L = 0 from
      h _ (fun b' x hm => hrefs_old l b' x hm)
    intro L
    induction L with
    | nil => intro _; rfl
    | cons e L ih =>
      intro hL
      cases e with
      | bin b' => exact ih (fun b'' x hm => hL b'' x (List.mem_cons_of_mem _ hm))
      | large b' x =>
        simp only [countRef]
        rw [if_neg (hL b' x (List.mem_cons_self ..)), ih (fun b'' x hm => hL b'' x (List.mem_cons_of_mem _ hm))]
  have hnewlits := hA.litsL_new hn32
  have hsize_new : (b.size r).toNat = lits.size := by rw [hA.size, UInt32.toNat_ofNat_of_lt' hn32]
  have hgar_new := hA.newFlags.2
  have hlit0 : b.lit r 0 = k0 := by rw [hA.lit 0 (by omega), hk0]
  have hlit1 : b.lit r 1 = k1 := by rw [hA.lit 1 (by omega), hk1]
  have hLive : ∀ x, t.LiveRef x ↔ s.LiveRef x ∨ x = r := by
    intro x
    unfold LiveRef refsL; rw [eArena, hch]
    constructor
    · rintro ⟨hx, hg⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨hx, by rw [← hgar_old x hx]; exact hg⟩
      · simp at hx; exact Or.inr hx
    · rintro (⟨hx, hg⟩ | rfl)
      · exact ⟨List.mem_append_left _ hx, by rw [hgar_old x hx]; exact hg⟩
      · exact ⟨List.mem_append_right _ (List.mem_singleton_self _), hgar_new⟩
  have hclOld : ∀ x, s.LiveRef x → t.clauseL x = s.clauseL x := by
    intro x hx
    rw [clauseL_eq_litsL, clauseL_eq_litsL, eArena]
    exact hA.litsL_old hl hx.1
  have hclNew : t.clauseL r = lits.view := by rw [clauseL_eq_litsL, eArena]; exact hnewlits
  have hcount : ∀ l x, x ≠ r → countRef x (t.entries l) = countRef x (s.entries l) := by
    intro l x hx
    rw [hent]
    by_cases ea : l = k0 <;> by_cases eb : l = k1 <;>
      simp [ea, eb, hne01, Ne.symm hne01, countRef_append, countRef, Ne.symm hx]
  have hBin : ∀ x y, t.BinWatched x y ↔ s.BinWatched x y := by
    intro x y; unfold BinWatched; rw [hent]
    by_cases ea : x = k0 <;> by_cases eb : x = k1 <;> simp [ea, eb, hne01, Ne.symm hne01]
  refine ⟨⟨fun l => ?_, ?_, ?_, ?_, by rw [eDel]; exact hW.delayed, ?_, by rw [eVars]; exact hW.varsBound⟩,
    hBin, hLive, hclOld, hclNew⟩
  · rw [ht]; exact (e2 l).2
  · intro l b' x hm
    rw [hent] at hm
    unfold refsL; rw [eArena]
    simp only [List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · obtain ⟨g1, g2⟩ := hW.refOK l b' x hm
      refine ⟨hchain_old x g1, fun hg => ?_⟩
      rw [hgar_old x g1] at hg
      obtain ⟨g3 | g3, g4⟩ := g2 hg
      · have hlv := (hW.live x ⟨g1, hg⟩).1
        exact ⟨Or.inl (by unfold lit0; rw [eArena, hlit_old x g1 0 (by omega) (by omega)]; exact g3),
          by rw [clauseL_eq_litsL, eArena, hA.litsL_old hl g1]; exact g4⟩
      · have hlv := (hW.live x ⟨g1, hg⟩).1
        exact ⟨Or.inr (by unfold lit1; rw [eArena, hlit_old x g1 1 (by omega) (by omega)]; exact g3),
          by rw [clauseL_eq_litsL, eArena, hA.litsL_old hl g1]; exact g4⟩
    · split at hm
      · rename_i ea; simp at hm; obtain ⟨hb', hx⟩ := hm
        rw [hb', hx]
        refine ⟨by rw [hch]; simp, fun _ => ⟨Or.inl (by unfold lit0; rw [eArena, hlit0]; exact ea), ?_⟩⟩
        rw [clauseL_eq_litsL, eArena, hnewlits]; exact hmem1
      · simp at hm
    · split at hm
      · rename_i eb; simp at hm; obtain ⟨hb', hx⟩ := hm
        rw [hb', hx]
        refine ⟨by rw [hch]; simp, fun _ => ⟨Or.inr (by unfold lit1; rw [eArena, hlit1]; exact eb), ?_⟩⟩
        rw [clauseL_eq_litsL, eArena, hnewlits]; exact hmem0
      · simp at hm
  · intro x hx
    rcases (hLive x).mp hx with hx' | rfl
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hW.live x hx'
      have hxr : x ≠ r := hA.ref_not_old hl hx'.1
      obtain ⟨o0, o2, o3, _⟩ := hold hx'.1
      refine ⟨by unfold Solver.clauseL at *; rw [eArena, o2]; exact g1, by rw [hclOld x hx']; exact g2,
        by rw [eArena, o3]; exact g3, by rw [eArena, o3, o2]; exact g4, ?_, ?_,
        fun y hy => by rw [hclOld x hx'] at hy; unfold ValidLit; rw [eVars]; exact g7 y hy⟩
      · rw [show t.lit0 x = s.lit0 x by unfold lit0; rw [eArena, hlit_old x hx'.1 0 (by omega) (by omega)],
          hcount _ _ hxr]; exact g5
      · rw [show t.lit1 x = s.lit1 x by unfold lit1; rw [eArena, hlit_old x hx'.1 1 (by omega) (by omega)],
          hcount _ _ hxr]; exact g6
    · refine ⟨by rw [eArena, hsize_new]; exact hn, by rw [hclNew]; exact hnd,
        by rw [eArena, hA.searched]; decide, by rw [eArena, hA.searched, hsize_new]; simp; omega, ?_, ?_,
        fun y hy => by rw [hclNew] at hy; unfold ValidLit; rw [eVars]; exact hv y hy⟩
      · rw [show t.lit0 x = k0 by unfold lit0; rw [eArena, hlit0], hent]
        simp [hne01, countRef_append, countRef, hcnt_old]
      · rw [show t.lit1 x = k1 by unfold lit1; rw [eArena, hlit1], hent]
        simp [Ne.symm hne01, countRef_append, countRef, hcnt_old]
  · intro x y hxy
    rw [hBin] at hxy
    obtain ⟨g1, g2, g3, g4⟩ := hW.bin x y hxy
    exact ⟨(hBin y x).mpr g1, by unfold ValidLit; rw [eVars]; exact g2, by unfold ValidLit; rw [eVars]; exact g3, g4⟩
  · show 2 * t.vars.toNat ≤ t.watches.size
    have : t.watches.size = s.watches.size := by
      rw [ht]; simp [watchBlocking, modifyWatches, ew1]
    rw [this, eVars]; exact hW.watchesSize

end Solver
end LeanKissat
