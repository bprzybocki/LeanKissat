import LeanKissat.Proofs.ArenaLayout

/-!
# Writes into a single clause of a well-laid-out arena

`setLit` and `setSearched` on a chain clause preserve the layout, the chain, the
header words (`word0`, `size`) of every clause, and the literals of every other
clause. The literal list of the written clause changes by `List.set`.
-/

namespace LeanKissat
namespace Arena

/-- Literal list of a clause. -/
def litsL (a : Arena) (r : Ref) : List Lit := (List.range (a.size r).toNat).map (a.lit r)

/-- The facts preserved by a write into clause `x0`. -/
structure WriteOK (a b : Arena) (x0 : Ref) : Prop where
  layout : b.Layout
  sizeWards : b.sizeWards = a.sizeWards
  chain : b.chain 0 b.sizeWards = a.chain 0 a.sizeWards
  word0 : ∀ x ∈ a.chain 0 a.sizeWards, b.word0 x = a.word0 x
  size : ∀ x ∈ a.chain 0 a.sizeWards, b.size x = a.size x
  others : ∀ x ∈ a.chain 0 a.sizeWards, x ≠ x0 → b.litsL x = a.litsL x ∧ b.searched x = a.searched x

theorem WriteOK.refl (a : Arena) (x0 : Ref) (h : a.Layout) : WriteOK a a x0 :=
  ⟨h, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem WriteOK.trans {a b c : Arena} {x0 : Ref} (h1 : WriteOK a b x0) (h2 : WriteOK b c x0) :
    WriteOK a c x0 := by
  refine ⟨h2.layout, h2.sizeWards.trans h1.sizeWards, h2.chain.trans h1.chain, ?_, ?_, ?_⟩
  · intro x hx; rw [h2.word0 x (h1.chain ▸ hx), h1.word0 x hx]
  · intro x hx; rw [h2.size x (h1.chain ▸ hx), h1.size x hx]
  · intro x hx hne
    obtain ⟨e1, e2⟩ := h1.others x hx hne
    obtain ⟨e3, e4⟩ := h2.others x (h1.chain ▸ hx) hne
    exact ⟨e3.trans e1, e4.trans e2⟩

theorem setLit_writeOK {a : Arena} (h : a.Layout) {x0 : Ref} (hx0 : x0 ∈ a.chain 0 a.sizeWards)
    {k : Nat} (hk : k < (a.size x0).toNat) (v : Lit) :
    WriteOK a (a.setLit x0 k v) x0 ∧
    (a.setLit x0 k v).litsL x0 = (a.litsL x0).set k v ∧
    (a.setLit x0 k v).searched x0 = a.searched x0 := by
  have hj : ∀ x ∈ a.chain 0 a.sizeWards, litPos x0 k ≠ base x ∧ litPos x0 k ≠ base x + 2 := by
    intro x hx
    have := lit_pos_ne_header h hx0 hx hk
    exact ⟨this.1, this.2.2⟩
  obtain ⟨hsw, hch, hlay, hagree⟩ := layout_write h (litPos x0 k) v hj
  have hsize : ∀ x ∈ a.chain 0 a.sizeWards, (a.setLit x0 k v).size x = a.size x :=
    fun x hx => (hagree x hx).2
  have hlit : ∀ x i, (a.setLit x0 k v).lit x i =
      if litPos x0 k = litPos x i ∧ litPos x i < a.words.size then v else a.lit x i := by
    intro x i; simp [setLit, lit, U32Vec.get!_set!]
  refine ⟨⟨hlay, hsw, hch, fun x hx => (hagree x hx).1, hsize, ?_⟩, ?_, ?_⟩
  · intro x hx hne
    constructor
    · unfold litsL
      rw [hsize x hx]
      apply List.map_congr_left
      intro i hi
      rw [hlit]
      have hi' : i < (a.size x).toNat := by simpa using hi
      rw [ite_eq_right (by intro e; exact lit_pos_ne_lit h hx0 hx (fun e' => hne e'.symm) hk hi' e.1)]
    · have := lit_pos_ne_header h hx0 hx hk
      simp only [setLit, searched, U32Vec.get!_set!]
      rw [ite_eq_right (by intro e; exact this.2.1 e.1)]
  · unfold litsL
    rw [hsize x0 hx0]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_set]
    rw [hlit]
    have hb : litPos x0 i < a.words.size := by
      have := h.mem_bounds hx0
      have := wardsOfClause_fits (a.size x0).toNat
      have hm := h.mult4
      simp at h1
      unfold litPos base; omega
    by_cases e : k = i
    · subst e; simp [hb]
    · have : litPos x0 k ≠ litPos x0 i := by unfold litPos; omega
      simp [this, e]
  · have := lit_pos_ne_header h hx0 hx0 hk
    simp only [setLit, searched, U32Vec.get!_set!]
    rw [ite_eq_right (by intro e; exact this.2.1 e.1)]

theorem setSearched_writeOK {a : Arena} (h : a.Layout) {x0 : Ref}
    (hx0 : x0 ∈ a.chain 0 a.sizeWards) (v : UInt32) :
    WriteOK a (a.setSearched x0 v) x0 ∧
    (a.setSearched x0 v).litsL x0 = a.litsL x0 ∧
    (a.setSearched x0 v).searched x0 = v := by
  have hsz := h.mem_bounds hx0
  have hfit := wardsOfClause_fits (a.size x0).toNat
  have hm := h.mult4
  have hpos : ∀ x ∈ a.chain 0 a.sizeWards, x ≠ x0 →
      (base x0 + 1 < 4 * x.toNat ∨ 4 * x.toNat + 4 * wardsOfClause (a.size x).toNat ≤ base x0) := by
    intro x hx hne
    rcases h.disjoint hx0 hx (Ne.symm hne) with h1 | h1
    · left; unfold base; omega
    · right; unfold base; omega
  have hj : ∀ x ∈ a.chain 0 a.sizeWards, base x0 + 1 ≠ base x ∧ base x0 + 1 ≠ base x + 2 := by
    intro x hx
    by_cases e : x = x0
    · subst e; omega
    · have := hpos x hx e
      have := wardsOfClause_pos (a.size x).toNat
      unfold base at *; omega
  obtain ⟨hsw, hch, hlay, hagree⟩ := layout_write h (base x0 + 1) v hj
  have hsize : ∀ x ∈ a.chain 0 a.sizeWards, (a.setSearched x0 v).size x = a.size x :=
    fun x hx => (hagree x hx).2
  have hlitne : ∀ x ∈ a.chain 0 a.sizeWards, ∀ i, i < (a.size x).toNat →
      (a.setSearched x0 v).lit x i = a.lit x i := by
    intro x hx i hi
    simp only [setSearched, lit, U32Vec.get!_set!]
    rw [ite_eq_right]
    intro ⟨e, _⟩
    by_cases ex : x = x0
    · subst ex; unfold litPos at e; omega
    · have := hpos x hx ex; have := wardsOfClause_fits (a.size x).toNat
      unfold litPos base at *; omega
  refine ⟨⟨hlay, hsw, hch, fun x hx => (hagree x hx).1, hsize, ?_⟩, ?_, ?_⟩
  · intro x hx hne
    constructor
    · unfold litsL; rw [hsize x hx]
      apply List.map_congr_left; intro i hi; exact hlitne x hx i (by simpa using hi)
    · simp only [setSearched, searched, U32Vec.get!_set!]
      rw [ite_eq_right]
      intro ⟨e, _⟩
      have := hpos x hx hne
      have := wardsOfClause_pos (a.size x).toNat
      unfold base at *; omega
  · unfold litsL; rw [hsize x0 hx0]
    apply List.map_congr_left; intro i hi; exact hlitne x0 hx0 i (by simpa using hi)
  · simp only [setSearched, searched, U32Vec.get!_set!, true_and]
    rw [ite_eq_left (by unfold base; omega)]

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

theorem length_litsL (a : Arena) (r : Ref) : (a.litsL r).length = (a.size r).toNat := by
  simp [litsL]

theorem getElem_litsL (a : Arena) (r : Ref) (i : Nat) (h : i < (a.litsL r).length) :
    (a.litsL r)[i] = a.lit r i := by simp [litsL]

/-- The four writes of a watch replacement in `propLoop`. -/
def replaceArena (a : Arena) (x0 : Ref) (r : Nat) (other notLit : Lit) : Arena :=
  (((a.setSearched x0 (UInt32.ofNat r)).setLit x0 0 other).setLit x0 1 (a.lit x0 r)).setLit x0 r notLit

theorem perm_replace {L : List Lit} {r : Nat} (hr2 : 2 ≤ r) (hrs : r < L.length) (other notLit : Lit)
    (hw : (L[0]'(by omega) = notLit ∧ L[1]'(by omega) = other) ∨
      (L[1]'(by omega) = notLit ∧ L[0]'(by omega) = other)) :
    (((L.set 0 other).set 1 L[r]).set r notLit).Perm L := by
  rcases hw with ⟨e0, e1⟩ | ⟨e1, e0⟩
  · have m : ((L.set 0 other).set 1 notLit).Perm L := by
      have := List.set_set_perm (as := L) (i := 0) (j := 1) (by omega) (by omega)
      rwa [e1, e0] at this
    have hM := List.set_set_perm (as := (L.set 0 other).set 1 notLit) (i := 1) (j := r)
      (by simp; omega) (by simp; omega)
    have hMr : ((L.set 0 other).set 1 notLit)[r]'(by simp; omega) = L[r] := by
      simp only [List.getElem_set]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hM1 : ((L.set 0 other).set 1 notLit)[1]'(by simp; omega) = notLit := by simp
    rw [hMr, hM1, List.set_set] at hM
    exact hM.trans m
  · have e : (L.set 0 other) = L := by
      rw [← e0]; exact List.set_getElem_self _
    rw [e, ← e1]
    exact List.set_set_perm (by omega) (by omega)

theorem replace_writeOK {a : Arena} (h : a.Layout) {x0 : Ref} (hx0 : x0 ∈ a.chain 0 a.sizeWards)
    {r : Nat} (hr2 : 2 ≤ r) (hrs : r < (a.size x0).toNat) (other notLit : Lit)
    (hw : (a.lit x0 0 = notLit ∧ a.lit x0 1 = other) ∨ (a.lit x0 1 = notLit ∧ a.lit x0 0 = other)) :
    WriteOK a (a.replaceArena x0 r other notLit) x0 ∧
    ((a.replaceArena x0 r other notLit).litsL x0).Perm (a.litsL x0) ∧
    (a.replaceArena x0 r other notLit).litsL x0 =
      (((a.litsL x0).set 0 other).set 1 (a.lit x0 r)).set r notLit ∧
    (a.replaceArena x0 r other notLit).searched x0 = UInt32.ofNat r := by
  obtain ⟨w1, l1, s1⟩ := setSearched_writeOK h hx0 (UInt32.ofNat r)
  have hx1 : x0 ∈ (a.setSearched x0 (UInt32.ofNat r)).chain 0
      (a.setSearched x0 (UInt32.ofNat r)).sizeWards := by rw [w1.chain]; exact hx0
  have hsz1 := w1.size x0 hx0
  obtain ⟨w2, l2, s2⟩ := setLit_writeOK w1.layout hx1 (k := 0) (by rw [hsz1]; omega) other
  have hx2 : x0 ∈ ((a.setSearched x0 (UInt32.ofNat r)).setLit x0 0 other).chain 0
      ((a.setSearched x0 (UInt32.ofNat r)).setLit x0 0 other).sizeWards := by
    rw [w2.chain]; exact hx1
  have hsz2 := w2.size x0 hx1
  obtain ⟨w3, l3, s3⟩ := setLit_writeOK w2.layout hx2 (k := 1) (by rw [hsz2, hsz1]; omega)
    (a.lit x0 r)
  have hx3 : x0 ∈ (((a.setSearched x0 (UInt32.ofNat r)).setLit x0 0 other).setLit x0 1
      (a.lit x0 r)).chain 0 (((a.setSearched x0 (UInt32.ofNat r)).setLit x0 0 other).setLit x0 1
      (a.lit x0 r)).sizeWards := by rw [w3.chain]; exact hx2
  have hsz3 := w3.size x0 hx2
  obtain ⟨w4, l4, s4⟩ := setLit_writeOK w3.layout hx3 (k := r)
    (by rw [hsz3, hsz2, hsz1]; exact hrs) notLit
  have hL' : (a.replaceArena x0 r other notLit).litsL x0 =
      (((a.litsL x0).set 0 other).set 1 (a.lit x0 r)).set r notLit := by
    unfold replaceArena; rw [l4, l3, l2, l1]
  have hlen : (a.litsL x0).length = (a.size x0).toNat := length_litsL _ _
  have gr : (a.litsL x0)[r]'(by omega) = a.lit x0 r := getElem_litsL _ _ _ _
  have g0 : (a.litsL x0)[0]'(by omega) = a.lit x0 0 := getElem_litsL _ _ _ _
  have g1 : (a.litsL x0)[1]'(by omega) = a.lit x0 1 := getElem_litsL _ _ _ _
  refine ⟨w1.trans (w2.trans (w3.trans w4)), ?_, hL', ?_⟩
  · rw [hL', ← gr]
    exact perm_replace hr2 (by omega) other notLit (by rw [g0, g1]; exact hw)
  · unfold replaceArena; rw [s4, s3, s2, s1]

end Arena
end LeanKissat
