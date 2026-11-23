import LeanKissat.Proofs.Struct

/-!
# Arena layout

`LayoutFrom a r refs`: starting at ward `r`, the clauses `refs` follow each other
without gaps up to the end of the arena, none of them is shrunken (in the `--plain`
configuration on-the-fly strengthening, the only producer of shrunken clauses, is
disabled), and each occupies `wardsOfClause size` wards.

Consequences: the word ranges of distinct clauses are disjoint, so writes into one
clause's literals or header do not change any other clause, nor the chain itself.
-/

namespace LeanKissat
namespace Arena

/-- Exact layout of the clause chain from `r`. -/
def LayoutFrom (a : Arena) : Ref → List Ref → Prop
  | r, [] => r.toNat = a.sizeWards
  | r, r' :: rs => r' = r ∧ r.toNat < a.sizeWards ∧ a.shrunken r = false ∧
      (a.nextClause r).toNat = r.toNat + wardsOfClause (a.size r).toNat ∧
      LayoutFrom a (a.nextClause r) rs

/-- The arena layout invariant. -/
structure Layout (a : Arena) : Prop where
  chain : LayoutFrom a 0 (a.chain 0 a.sizeWards)
  mult4 : a.words.size = 4 * a.sizeWards
  bound : a.sizeWards ≤ 2 ^ 31

theorem wardsOfClause_pos (n : Nat) : 1 ≤ wardsOfClause n := by
  unfold wardsOfClause; omega

theorem wardsOfClause_fits (n : Nat) : 3 + n ≤ 4 * wardsOfClause n := by
  unfold wardsOfClause; omega

theorem LayoutFrom.le_end {a : Arena} :
    ∀ {r : Ref} {refs : List Ref}, LayoutFrom a r refs → r.toNat ≤ a.sizeWards := by
  intro r refs h
  cases refs with
  | nil => simp [LayoutFrom] at h; omega
  | cons r' rs => obtain ⟨_, hlt, _⟩ := h; omega

/-- Every clause of an exact chain fits in its wards and lies inside the arena. -/
theorem LayoutFrom.mem_bounds {a : Arena} :
    ∀ {r : Ref} {refs : List Ref}, LayoutFrom a r refs → ∀ x ∈ refs,
      r.toNat ≤ x.toNat ∧ x.toNat + wardsOfClause (a.size x).toNat ≤ a.sizeWards := by
  intro r refs
  induction refs generalizing r with
  | nil => intro _ x hx; simp at hx
  | cons r' rs ih =>
    intro h x hx
    obtain ⟨rfl, hlt, _, hnext, hrest⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨Nat.le_refl _, ?_⟩
      have := LayoutFrom.le_end hrest
      omega
    · have ⟨h1, h2⟩ := ih hrest x hx
      exact ⟨by omega, h2⟩

/-- Distinct clauses of an exact chain occupy disjoint ward ranges. -/
theorem LayoutFrom.disjoint {a : Arena} :
    ∀ {r : Ref} {refs : List Ref}, LayoutFrom a r refs → ∀ x ∈ refs, ∀ y ∈ refs, x ≠ y →
      x.toNat + wardsOfClause (a.size x).toNat ≤ y.toNat ∨
      y.toNat + wardsOfClause (a.size y).toNat ≤ x.toNat := by
  intro r refs
  induction refs generalizing r with
  | nil => intro _ x hx; simp at hx
  | cons r' rs ih =>
    intro h x hx y hy hxy
    obtain ⟨rfl, hlt, _, hnext, hrest⟩ := h
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · exact absurd (ex.trans ey.symm) hxy
    · subst ex; left; have := (LayoutFrom.mem_bounds hrest y hy').1; omega
    · subst ey; right; have := (LayoutFrom.mem_bounds hrest x hx').1; omega
    · exact ih hrest x hx' y hy' hxy

theorem Layout.mem_bounds {a : Arena} (h : a.Layout) {x : Ref} (hx : x ∈ a.chain 0 a.sizeWards) :
    x.toNat + wardsOfClause (a.size x).toNat ≤ a.sizeWards :=
  (h.chain.mem_bounds x hx).2

theorem Layout.disjoint {a : Arena} (h : a.Layout) {x y : Ref}
    (hx : x ∈ a.chain 0 a.sizeWards) (hy : y ∈ a.chain 0 a.sizeWards) (hxy : x ≠ y) :
    x.toNat + wardsOfClause (a.size x).toNat ≤ y.toNat ∨
    y.toNat + wardsOfClause (a.size y).toNat ≤ x.toNat :=
  h.chain.disjoint x hx y hy hxy

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

theorem actualWards_of_not_shrunken (a : Arena) (r : Ref) (h : a.shrunken r = false) :
    a.actualWards r = wardsOfClause (a.size r).toNat := by
  unfold actualWards wardsOfClause litPos base
  simp only [h, Bool.false_eq_true, ite_false]
  omega

/-- Two arenas agreeing on the size, and on header words 0 and 2 of the clauses of a
  chain, have the same chain. -/
theorem chain_congr {a b : Arena} (hs : a.sizeWards = b.sizeWards) :
    ∀ (fuel : Nat) (r : Ref),
    (∀ x ∈ a.chain r fuel, a.word0 x = b.word0 x ∧ a.size x = b.size x ∧ a.shrunken x = false) →
    a.chain r fuel = b.chain r fuel := by
  intro fuel
  induction fuel with
  | zero => intro r _; rfl
  | succ n ih =>
    intro r h
    unfold chain
    by_cases hr : r.toNat < a.sizeWards
    · have hr' : r.toNat < b.sizeWards := by omega
      simp only [hr, hr', ite_true]
      have hmem : r ∈ a.chain r (n + 1) := by unfold chain; simp [hr]
      obtain ⟨h0, h2, hsh⟩ := h r hmem
      have hshb : b.shrunken r = false := by
        unfold shrunken flag at *; rw [← h0]; exact hsh
      have hnext : a.nextClause r = b.nextClause r := by
        unfold nextClause
        rw [actualWards_of_not_shrunken a r hsh, actualWards_of_not_shrunken b r hshb, h2]
      rw [hnext, ih (b.nextClause r)]
      intro x hx
      apply h x
      unfold chain; simp only [hr, ite_true]; rw [hnext]; exact List.mem_cons_of_mem _ hx
    · have hr' : ¬ r.toNat < b.sizeWards := by omega
      simp [hr, hr']

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

theorem layoutFrom_congr {a b : Arena} (hs : a.sizeWards = b.sizeWards) :
    ∀ (refs : List Ref) (r : Ref),
    (∀ x ∈ refs, a.word0 x = b.word0 x ∧ a.size x = b.size x) →
    LayoutFrom a r refs → LayoutFrom b r refs := by
  intro refs
  induction refs with
  | nil => intro r _ h; simp [LayoutFrom] at *; omega
  | cons r' rs ih =>
    intro r hagree h
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h
    obtain ⟨h0, h2⟩ := hagree r' (List.mem_cons_self ..)
    have hshb : b.shrunken r' = false := by unfold shrunken flag at *; rw [← h0]; exact hsh
    have hn : a.nextClause r' = b.nextClause r' := by
      unfold nextClause
      rw [actualWards_of_not_shrunken a r' hsh, actualWards_of_not_shrunken b r' hshb, h2]
    refine ⟨rfl, by omega, hshb, by rw [← hn, hnext, h2], ?_⟩
    rw [← hn]
    exact ih _ (fun x hx => hagree x (List.mem_cons_of_mem _ hx)) hrest

theorem LayoutFrom.not_shrunken {a : Arena} :
    ∀ {r : Ref} {refs : List Ref}, LayoutFrom a r refs → ∀ x ∈ refs, a.shrunken x = false := by
  intro r refs
  induction refs generalizing r with
  | nil => intro _ x hx; simp at hx
  | cons r' rs ih =>
    intro hl x hx
    obtain ⟨rfl, _, hsh, _, hrest⟩ := hl
    rcases List.mem_cons.mp hx with ex | hx'
    · subst ex; exact hsh
    · exact ih hrest x hx'

/-- Facts about a single-word write into the arena that avoids all header words
  (`word0`, `size`) of chain clauses. -/
theorem layout_write {a : Arena} (h : a.Layout) (j : Nat) (v : UInt32)
    (hj : ∀ x ∈ a.chain 0 a.sizeWards, j ≠ base x ∧ j ≠ base x + 2) :
    let b : Arena := { words := a.words.set! j v }
    b.sizeWards = a.sizeWards ∧ b.chain 0 b.sizeWards = a.chain 0 a.sizeWards ∧ b.Layout ∧
    (∀ x ∈ a.chain 0 a.sizeWards, b.word0 x = a.word0 x ∧ b.size x = a.size x) := by
  intro b
  have hsw : b.sizeWards = a.sizeWards := by simp [b, sizeWards]
  have hagree : ∀ x ∈ a.chain 0 a.sizeWards, b.word0 x = a.word0 x ∧ b.size x = a.size x := by
    intro x hx
    have := hj x hx
    simp only [b, word0, size, U32Vec.get!_set!]
    constructor
    · rw [if_neg (by intro e; exact this.1 e.1)]
    · rw [if_neg (by intro e; exact this.2 e.1)]
  have hlayA := h.chain
  have hshA : ∀ x ∈ a.chain 0 a.sizeWards, a.shrunken x = false :=
    fun x hx => LayoutFrom.not_shrunken hlayA x hx
  have hch : b.chain 0 b.sizeWards = a.chain 0 a.sizeWards := by
    rw [hsw]
    exact (chain_congr (by rw [hsw]) _ 0 (fun x hx => ⟨(hagree x hx).1.symm, (hagree x hx).2.symm,
      hshA x hx⟩)).symm
  refine ⟨hsw, hch, ⟨?_, ?_, ?_⟩, hagree⟩
  · rw [hch]
    exact layoutFrom_congr hsw.symm _ 0 (fun x hx => ⟨(hagree x hx).1.symm, (hagree x hx).2.symm⟩) h.chain
  · simp only [b, sizeWards, U32Vec.size_set!]; have := h.mult4; simp [sizeWards] at this ⊢; omega
  · rw [hsw]; exact h.bound

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

/-- Header and literal positions of a chain clause. -/
theorem lit_pos_ne_header {a : Arena} (h : a.Layout) {x0 x : Ref}
    (hx0 : x0 ∈ a.chain 0 a.sizeWards) (hx : x ∈ a.chain 0 a.sizeWards) {k : Nat}
    (hk : k < (a.size x0).toNat) :
    litPos x0 k ≠ base x ∧ litPos x0 k ≠ base x + 1 ∧ litPos x0 k ≠ base x + 2 := by
  unfold litPos base
  have hf0 := wardsOfClause_fits (a.size x0).toNat
  by_cases e : x0 = x
  · subst e; omega
  · rcases h.disjoint hx0 hx e with h1 | h1
    · have := wardsOfClause_fits (a.size x).toNat; omega
    · have := wardsOfClause_fits (a.size x).toNat; omega

/-- Literal positions of distinct chain clauses differ. -/
theorem lit_pos_ne_lit {a : Arena} (h : a.Layout) {x0 x : Ref}
    (hx0 : x0 ∈ a.chain 0 a.sizeWards) (hx : x ∈ a.chain 0 a.sizeWards) (hne : x0 ≠ x)
    {k i : Nat} (hk : k < (a.size x0).toNat) (hi : i < (a.size x).toNat) :
    litPos x0 k ≠ litPos x i := by
  unfold litPos base
  have hf0 := wardsOfClause_fits (a.size x0).toNat
  have hf := wardsOfClause_fits (a.size x).toNat
  rcases h.disjoint hx0 hx hne with h1 | h1 <;> omega

end Arena
end LeanKissat
