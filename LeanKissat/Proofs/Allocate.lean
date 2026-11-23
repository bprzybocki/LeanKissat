import LeanKissat.Proofs.ArenaSame

/-!
# Clause allocation at the end of the arena

`Arena.allocate` appends a clause: every old clause keeps its words, the clause chain is
extended by the new reference, and the layout invariant is preserved.
-/

namespace LeanKissat

theorem U32Vec.view_appendFrom (src : U32Vec) (n : Nat) (hn : n ≤ src.size) :
    ∀ (a : U32Vec) (i : Nat), i ≤ n →
      (a.appendFrom src i n).view = a.view ++ (src.view.drop i).take (n - i) := by
  intro a i
  fun_induction U32Vec.appendFrom a src i n with
  | case1 a i hi ih =>
    intro _
    rw [ih (by omega), U32Vec.view_push, List.append_assoc]
    congr 1
    have hi' : i < src.view.length := by simp; omega
    rw [List.drop_eq_getElem_cons hi', show n - i = (n - (i + 1)) + 1 by omega, List.take_succ_cons]
    rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rfl
  | case2 a i hi =>
    intro h; rw [show n - i = 0 by omega]; simp

namespace Arena

/-- Words written by `allocate`. -/
def allocWords (red : Bool) (glue : UInt32) (lits : U32Vec) : List UInt32 :=
  [(if red then min MAX_GLUE glue else 0) ||| (if red then ClauseHeader.redundantBit else 0), 2,
    UInt32.ofNat lits.size] ++ lits.view ++ List.replicate (4 * wardsOfClause lits.size - (3 + lits.size)) 0

theorem allocate_some {a : Arena} {red : Bool} {glue : UInt32} {lits : U32Vec} {r : Ref} {b : Arena}
    (h : a.allocate red glue lits = (some r, b)) :
    b.words.view = a.words.view ++ allocWords red glue lits ∧ r = UInt32.ofNat a.sizeWards ∧
    a.words.size / 4 + wardsOfClause lits.size ≤ MAX_ARENA := by
  unfold allocate at h
  simp only at h
  split at h
  · simp at h
  · rename_i hle
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, rfl, by omega⟩
    simp only [U32Vec.view_pushN, U32Vec.view_appendFrom lits lits.size (Nat.le_refl _) _ 0 (Nat.zero_le _),
      U32Vec.view_push, List.drop_zero, Nat.sub_zero, allocWords, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [List.take_of_length_le (by simp)]

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

theorem length_allocWords (red : Bool) (glue : UInt32) (lits : U32Vec) :
    (allocWords red glue lits).length = 4 * wardsOfClause lits.size := by
  have := wardsOfClause_fits lits.size
  simp [allocWords]; omega

/-- The facts about an allocation used by the invariants. -/
structure Alloc (a b : Arena) (r : Ref) (red : Bool) (glue : UInt32) (lits : U32Vec) : Prop where
  old : ∀ j, j < a.words.size → b.words.get! j = a.words.get! j
  sizeWards : b.sizeWards = a.sizeWards + wardsOfClause lits.size
  wsize : b.words.size = a.words.size + 4 * wardsOfClause lits.size
  ref : r.toNat = a.sizeWards
  bound : b.sizeWards ≤ 2 ^ 31
  word0 : b.word0 r = (if red then min MAX_GLUE glue else 0) ||| (if red then ClauseHeader.redundantBit else 0)
  searched : b.searched r = 2
  size : b.size r = UInt32.ofNat lits.size
  lit : ∀ i, i < lits.size → b.lit r i = lits.get! i

theorem allocate_alloc {a : Arena} (hl : a.Layout) {red : Bool} {glue : UInt32} {lits : U32Vec} {r : Ref}
    {b : Arena} (h : a.allocate red glue lits = (some r, b)) : Alloc a b r red glue lits := by
  obtain ⟨hv, hr, hle⟩ := allocate_some h
  have hm := hl.mult4
  have hlenA : a.words.view.length = 4 * a.sizeWards := by rw [U32Vec.length_view]; exact hm
  have hws : b.words.size = a.words.size + 4 * wardsOfClause lits.size := by
    rw [← U32Vec.length_view, hv, List.length_append, length_allocWords, U32Vec.length_view]
  have hsw : b.sizeWards = a.sizeWards + wardsOfClause lits.size := by
    unfold sizeWards; rw [hws, hm]; omega
  have hN : a.sizeWards < 2 ^ 32 := by unfold MAX_ARENA at hle; simp at hle; unfold sizeWards; omega
  have hrN : r.toNat = a.sizeWards := by rw [hr, UInt32.toNat_ofNat_of_lt' hN]
  have hold : ∀ j, j < a.words.size → b.words.get! j = a.words.get! j := by
    intro j hj
    rw [U32Vec.get!_eq_view, U32Vec.get!_eq_view, hv, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa using hj)]
  have hnew : ∀ k, k < 4 * wardsOfClause lits.size →
      b.words.get! (4 * a.sizeWards + k) = (allocWords red glue lits).getD k 0 := by
    intro k _
    rw [U32Vec.get!_eq_view, hv, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    congr 2; omega
  have hfit := wardsOfClause_fits lits.size
  have hbase : base r = 4 * a.sizeWards := by unfold base; rw [hrN]
  refine ⟨hold, hsw, hws, hrN, by rw [hsw]; unfold MAX_ARENA at hle; simp at hle; unfold sizeWards; omega,
    ?_, ?_, ?_, fun i hi => ?_⟩
  · unfold word0; rw [hbase, show 4 * a.sizeWards = 4 * a.sizeWards + 0 by rfl, hnew 0 (by omega)]
    simp [allocWords]
  · unfold searched; rw [hbase, hnew 1 (by omega)]; simp [allocWords]
  · unfold size; rw [hbase, hnew 2 (by omega)]; simp [allocWords]
  · unfold lit litPos; rw [hbase, show 4 * a.sizeWards + 3 + i = 4 * a.sizeWards + (3 + i) by omega,
      hnew (3 + i) (by omega)]
    simp only [allocWords, List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ,
      show 3 + i = i + 1 + 1 + 1 by omega]
    rw [List.getElem?_append_left (by simpa using hi), U32Vec.get!_eq_view, List.getD_eq_getElem?_getD,
      List.nil_append]

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

theorem LayoutFrom.length_le {a : Arena} :
    ∀ {r : Ref} {refs : List Ref}, LayoutFrom a r refs → r.toNat + refs.length ≤ a.sizeWards := by
  intro r refs
  induction refs generalizing r with
  | nil => intro h; simp [LayoutFrom] at h; simp; omega
  | cons r' rs ih =>
    intro h
    obtain ⟨_, hlt, _, hnext, hrest⟩ := h
    have := ih hrest
    have := wardsOfClause_pos (a.size r).toNat
    simp; omega

theorem LayoutFrom.chain_eq {a : Arena} :
    ∀ {r : Ref} {refs : List Ref}, LayoutFrom a r refs → ∀ fuel, refs.length ≤ fuel → a.chain r fuel = refs := by
  intro r refs
  induction refs generalizing r with
  | nil =>
    intro h fuel _
    simp [LayoutFrom] at h
    cases fuel with
    | zero => rfl
    | succ f => unfold chain; rw [ite_eq_right (by omega)]
  | cons r' rs ih =>
    intro h fuel hf
    obtain ⟨rfl, hlt, _, _, hrest⟩ := h
    cases fuel with
    | zero => simp at hf
    | succ f =>
      unfold chain; rw [ite_eq_left hlt, ih hrest f (by simp at hf; omega)]

theorem alloc_flags (red : Bool) (glue : UInt32) :
    (((if red then min MAX_GLUE glue else 0) ||| (if red then ClauseHeader.redundantBit else 0)) &&&
      ClauseHeader.shrunkenBit) = 0 ∧
    (((if red then min MAX_GLUE glue else 0) ||| (if red then ClauseHeader.redundantBit else 0)) &&&
      ClauseHeader.garbageBit) = 0 := by
  cases red <;> simp only [ite_true, Bool.false_eq_true, ite_false]
  · decide
  · have hm : (min MAX_GLUE glue).toNat < 2 ^ 19 := by
      rw [UInt32.min_def]; split
      · decide
      · rename_i h; simp only [MAX_GLUE, UInt32.le_iff_toNat_le] at h; simp only [UInt32.reduceShiftLeft,
          UInt32.reduceSub, UInt32.reduceToNat] at h; omega
    generalize min MAX_GLUE glue = m at hm ⊢
    have b19 : m.toBitVec.getLsbD 19 = false := Nat.testBit_lt_two_pow (by simpa using hm)
    have b23 : m.toBitVec.getLsbD 23 = false := Nat.testBit_lt_two_pow (by simp; omega)
    unfold ClauseHeader.shrunkenBit ClauseHeader.garbageBit ClauseHeader.redundantBit
    constructor <;> bv_k

theorem Alloc.oldReads {a b : Arena} {r : Ref} {red : Bool} {glue : UInt32} {lits : U32Vec}
    (h : Alloc a b r red glue lits) (hl : a.Layout) {x : Ref} (hx : x ∈ a.chain 0 a.sizeWards) :
    b.word0 x = a.word0 x ∧ b.size x = a.size x ∧ b.searched x = a.searched x ∧
    (∀ i, i < (a.size x).toNat → b.lit x i = a.lit x i) := by
  have hb := hl.mem_bounds hx
  have hf := wardsOfClause_fits (a.size x).toNat
  have hm := hl.mult4
  have hw := wardsOfClause_pos (a.size x).toNat
  refine ⟨h.old _ (by unfold base; omega), h.old _ (by unfold base; omega), h.old _ (by unfold base; omega),
    fun i hi => h.old _ (by unfold litPos base; omega)⟩

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

theorem Alloc.newFlags {a b : Arena} {r : Ref} {red : Bool} {glue : UInt32} {lits : U32Vec}
    (h : Alloc a b r red glue lits) : b.shrunken r = false ∧ b.garbage r = false := by
  have := alloc_flags red glue
  unfold shrunken garbage flag; rw [h.word0, this.1, this.2]; simp

theorem Alloc.layoutFrom {a b : Arena} {r : Ref} {red : Bool} {glue : UInt32} {lits : U32Vec}
    (h : Alloc a b r red glue lits) (hl : a.Layout) (hn : lits.size < 2 ^ 32) :
    ∀ (refs : List Ref) (x : Ref), (∀ y ∈ refs, y ∈ a.chain 0 a.sizeWards) → LayoutFrom a x refs →
      LayoutFrom b x (refs ++ [r]) := by
  have hw := wardsOfClause_pos lits.size
  have hbnd := h.bound
  intro refs
  induction refs with
  | nil =>
    intro x _ hx
    simp only [LayoutFrom] at hx
    have hxr : x = r := UInt32.toNat_inj.mp (by rw [hx, h.ref])
    subst hxr
    have hsz : (b.size x).toNat = lits.size := by rw [h.size, UInt32.toNat_ofNat_of_lt' hn]
    have hsw := h.sizeWards
    have hwlt : wardsOfClause lits.size < 2 ^ 32 := by omega
    have hnext : (b.nextClause x).toNat = x.toNat + wardsOfClause (b.size x).toNat := by
      unfold nextClause
      rw [actualWards_of_not_shrunken b x h.newFlags.1, UInt32.toNat_add, hsz, UInt32.toNat_ofNat_of_lt' hwlt]
      have : x.toNat + wardsOfClause lits.size < 2 ^ 32 := by rw [h.ref]; omega
      exact Nat.mod_eq_of_lt this
    refine ⟨rfl, by rw [h.sizeWards, h.ref]; omega, h.newFlags.1, hnext, ?_⟩
    simp only [LayoutFrom]; rw [hnext, hsz, h.ref, h.sizeWards]
  | cons x' rs ih =>
    intro x hsub hx
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := hx
    have hmem : x' ∈ a.chain 0 a.sizeWards := hsub x' (List.mem_cons_self ..)
    obtain ⟨e0, e2, _, _⟩ := h.oldReads hl hmem
    have hshb : b.shrunken x' = false := by unfold shrunken flag at *; rw [e0]; exact hsh
    have hn' : b.nextClause x' = a.nextClause x' := by
      unfold nextClause
      rw [actualWards_of_not_shrunken a x' hsh, actualWards_of_not_shrunken b x' hshb, e2]
    refine ⟨rfl, by rw [h.sizeWards]; omega, hshb, by rw [hn', hnext, e2], ?_⟩
    rw [hn']
    exact ih _ (fun y hy => hsub y (List.mem_cons_of_mem _ hy)) hrest

theorem allocate_layout {a : Arena} (hl : a.Layout) {red : Bool} {glue : UInt32} {lits : U32Vec} {r : Ref}
    {b : Arena} (h : a.allocate red glue lits = (some r, b)) (hn : lits.size < 2 ^ 32) :
    Alloc a b r red glue lits ∧ b.Layout ∧ b.chain 0 b.sizeWards = a.chain 0 a.sizeWards ++ [r] := by
  have hA := allocate_alloc hl h
  have hlf := hA.layoutFrom hl hn _ 0 (fun y hy => hy) hl.chain
  have hch : b.chain 0 b.sizeWards = a.chain 0 a.sizeWards ++ [r] := by
    apply hlf.chain_eq
    have := hlf.length_le
    simp at this ⊢; omega
  refine ⟨hA, ⟨by rw [hch]; exact hlf, ?_, hA.bound⟩, hch⟩
  rw [hA.wsize, hA.sizeWards, hl.mult4]; omega

end Arena
end LeanKissat
