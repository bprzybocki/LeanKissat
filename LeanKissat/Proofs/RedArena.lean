import LeanKissat.Proofs.RedFlush

/-!
# Arena segments

`LayoutTo a r e refs`: the clauses `refs` follow each other from ward `r` up to ward `e`.
Segments only depend on the words in `[4 r, 4 e)`.
-/

namespace LeanKissat
namespace Arena

/-- Exact layout of a chain segment from `r` to `e`. -/
def LayoutTo (a : Arena) : Ref → Nat → List Ref → Prop
  | r, e, [] => r.toNat = e
  | r, e, r' :: rs => r' = r ∧ r.toNat < e ∧ a.shrunken r = false ∧
      (a.nextClause r).toNat = r.toNat + wardsOfClause (a.size r).toNat ∧
      LayoutTo a (a.nextClause r) e rs

/-- The words of `a` and `b` agree on `[lo, hi)`. -/
def EqOn (a b : Arena) (lo hi : Nat) : Prop := ∀ j, lo ≤ j → j < hi → a.words.get! j = b.words.get! j

theorem EqOn.symm {a b : Arena} {lo hi : Nat} (h : EqOn a b lo hi) : EqOn b a lo hi :=
  fun j h1 h2 => (h j h1 h2).symm

theorem EqOn.trans {a b c : Arena} {lo hi : Nat} (h1 : EqOn a b lo hi) (h2 : EqOn b c lo hi) : EqOn a c lo hi :=
  fun j k1 k2 => (h1 j k1 k2).trans (h2 j k1 k2)

theorem EqOn.mono {a b : Arena} {lo hi lo' hi' : Nat} (h : EqOn a b lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    EqOn a b lo' hi' := fun j k1 k2 => h j (by omega) (by omega)

theorem LayoutTo.le {a : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref}, LayoutTo a r e refs → r.toNat ≤ e := by
  intro r e refs h
  cases refs with
  | nil => simp [LayoutTo] at h; omega
  | cons r' rs => obtain ⟨_, hlt, _⟩ := h; omega

theorem LayoutTo.mem_bounds {a : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref}, LayoutTo a r e refs →
    ∀ x ∈ refs, r.toNat ≤ x.toNat ∧ x.toNat + wardsOfClause (a.size x).toNat ≤ e ∧ a.shrunken x = false := by
  intro r e refs
  induction refs generalizing r with
  | nil => intro _ x hx; simp at hx
  | cons r' rs ih =>
    intro h x hx
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨Nat.le_refl _, ?_, hsh⟩
      have := LayoutTo.le hrest; omega
    · have ⟨h1, h2, h3⟩ := ih hrest x hx
      exact ⟨by omega, h2, h3⟩

/-- Header words of a clause are read from `[4 x, 4 x + 3)`. -/
theorem header_eq_of_eqOn {a b : Arena} {x : Ref} (h : EqOn a b (4 * x.toNat) (4 * x.toNat + 3)) :
    a.word0 x = b.word0 x ∧ a.searched x = b.searched x ∧ a.size x = b.size x := by
  unfold word0 searched size base
  exact ⟨h _ (by omega) (by omega), h _ (by omega) (by omega), h _ (by omega) (by omega)⟩

theorem flag_eq_of_word0 {a b : Arena} {x : Ref} (h : a.word0 x = b.word0 x) (bit : UInt32) :
    a.flag x bit = b.flag x bit := by unfold flag; rw [h]

theorem nextClause_eq {a b : Arena} {x : Ref} (h0 : a.word0 x = b.word0 x) (h2 : a.size x = b.size x)
    (hsh : a.shrunken x = false) : a.nextClause x = b.nextClause x := by
  have hshb : b.shrunken x = false := by unfold shrunken flag at *; rw [← h0]; exact hsh
  unfold nextClause
  rw [actualWards_of_not_shrunken a x hsh, actualWards_of_not_shrunken b x hshb, h2]

theorem LayoutTo.congr {a b : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref}, LayoutTo a r e refs →
    EqOn a b (4 * r.toNat) (4 * e) → LayoutTo b r e refs := by
  intro r e refs
  induction refs generalizing r with
  | nil => intro h _; exact h
  | cons r' rs ih =>
    intro h hq
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h
    have hw := wardsOfClause_pos (a.size r').toNat
    have hle := LayoutTo.le hrest
    obtain ⟨e0, _, e2⟩ := header_eq_of_eqOn (hq.mono (Nat.le_refl _) (by omega))
    have hn := nextClause_eq e0 e2 hsh
    have hshb : b.shrunken r' = false := by unfold shrunken; rw [← flag_eq_of_word0 e0]; exact hsh
    refine ⟨rfl, hlt, hshb, by rw [← hn, hnext, e2], ?_⟩
    rw [← hn]
    exact ih hrest (hq.mono (by omega) (Nat.le_refl _))

theorem LayoutTo.append {a : Arena} : ∀ {r : Ref} {m : Ref} {e : Nat} {P Q : List Ref}, LayoutTo a r m.toNat P →
    LayoutTo a m e Q → LayoutTo a r e (P ++ Q) := by
  intro r m e P
  induction P generalizing r with
  | nil => intro Q h1 h2; simp only [LayoutTo] at h1; have := UInt32.toNat_inj.mp h1; subst this; exact h2
  | cons x xs ih =>
    intro Q h1 h2
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h1
    have := LayoutTo.le h2
    exact ⟨rfl, by omega, hsh, hnext, ih hrest h2⟩

theorem layoutFrom_iff {a : Arena} : ∀ {r : Ref} {refs : List Ref},
    LayoutFrom a r refs ↔ LayoutTo a r a.sizeWards refs := by
  intro r refs
  induction refs generalizing r with
  | nil => simp [LayoutFrom, LayoutTo]
  | cons x xs ih =>
    simp only [LayoutFrom, LayoutTo]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, ih.mp h5⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, ih.mpr h5⟩

theorem LayoutTo.nodup {a : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref}, LayoutTo a r e refs → refs.Nodup := by
  intro r e refs
  induction refs generalizing r with
  | nil => intro _; exact List.nodup_nil
  | cons x xs ih =>
    intro h
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, ih hrest⟩
    have := (hrest.mem_bounds x hx).1
    have := wardsOfClause_pos (a.size x).toNat
    omega

/-- Two different clauses of a segment occupy disjoint ward ranges. -/
theorem LayoutTo.disjoint {a : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref}, LayoutTo a r e refs →
    ∀ x ∈ refs, ∀ y ∈ refs, x ≠ y →
      x.toNat + wardsOfClause (a.size x).toNat ≤ y.toNat ∨ y.toNat + wardsOfClause (a.size y).toNat ≤ x.toNat := by
  intro r e refs
  induction refs generalizing r with
  | nil => intro _ x hx; simp at hx
  | cons r' rs ih =>
    intro h x hx y hy hxy
    obtain ⟨rfl, hlt, _, hnext, hrest⟩ := h
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · exact absurd (ex.trans ey.symm) hxy
    · subst ex; left; have := (hrest.mem_bounds y hy').1; omega
    · subst ey; right; have := (hrest.mem_bounds x hx').1; omega
    · exact ih hrest x hx' y hy' hxy

/-- Clause view (header words and literals) of the clause at `x`, read from its wards. -/
theorem clause_eq_of_eqOn {a b : Arena} {x : Ref}
    (h : EqOn a b (4 * x.toNat) (4 * x.toNat + 4 * wardsOfClause (a.size x).toNat)) :
    a.word0 x = b.word0 x ∧ a.searched x = b.searched x ∧ a.size x = b.size x ∧
    a.litsL x = b.litsL x := by
  have hf := wardsOfClause_fits (a.size x).toNat
  obtain ⟨e0, e1, e2⟩ := header_eq_of_eqOn (h.mono (Nat.le_refl _) (by omega))
  refine ⟨e0, e1, e2, ?_⟩
  unfold litsL
  rw [← e2]
  apply List.map_congr_left
  intro i hi
  simp at hi
  unfold lit litPos base
  exact h _ (by omega) (by omega)

/-- A segment decomposes the chain from its start. -/
theorem LayoutTo.chain_eq {a : Arena} {r : Ref} {refs : List Ref} (h : LayoutTo a r a.sizeWards refs)
    (fuel : Nat) (hf : refs.length ≤ fuel) : a.chain r fuel = refs :=
  LayoutFrom.chain_eq (layoutFrom_iff.mpr h) fuel hf

theorem LayoutTo.length_le {a : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref}, LayoutTo a r e refs →
    r.toNat + refs.length ≤ e := by
  intro r e refs
  induction refs generalizing r with
  | nil => intro h; simp [LayoutTo] at h; simp; omega
  | cons r' rs ih =>
    intro h
    obtain ⟨_, hlt, _, hnext, hrest⟩ := h
    have := ih hrest
    have := wardsOfClause_pos (a.size r).toNat
    simp; omega

end Arena
end LeanKissat
