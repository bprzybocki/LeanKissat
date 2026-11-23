import LeanKissat.Proofs.ArenaWrites

/-!
# Arenas with the same clauses (header bits other than garbage/redundant/shrunken may differ)
-/

namespace LeanKissat
namespace Arena

/-- The header bits the invariants depend on. -/
def keyMask : UInt32 := ClauseHeader.garbageBit ||| ClauseHeader.redundantBit ||| ClauseHeader.shrunkenBit

structure Same (a b : Arena) : Prop where
  wsize : b.words.size = a.words.size
  chain : b.chain 0 b.sizeWards = a.chain 0 a.sizeWards
  size : ∀ x ∈ a.chain 0 a.sizeWards, b.size x = a.size x
  lits : ∀ x ∈ a.chain 0 a.sizeWards, b.litsL x = a.litsL x
  searched : ∀ x ∈ a.chain 0 a.sizeWards, b.searched x = a.searched x
  key : ∀ x ∈ a.chain 0 a.sizeWards, (b.word0 x &&& keyMask) = (a.word0 x &&& keyMask)

theorem key_bit (w w' : UInt32) (e : (w &&& keyMask) = (w' &&& keyMask)) {bit : UInt32}
    (hb : bit = ClauseHeader.garbageBit ∨ bit = ClauseHeader.redundantBit ∨
      bit = ClauseHeader.shrunkenBit) : (w &&& bit != 0) = (w' &&& bit != 0) := by
  have key : (w &&& bit = 0) ↔ (w' &&& bit = 0) := by
    simp only [keyMask, ClauseHeader.garbageBit, ClauseHeader.redundantBit,
      ClauseHeader.shrunkenBit] at e hb
    rcases hb with rfl | rfl | rfl <;> constructor <;> intro h <;> bv_k
  cases h1 : (w &&& bit != 0) <;> cases h2 : (w' &&& bit != 0) <;> simp_all

theorem flag_of_key {a b : Arena} {x : Ref} (h : (b.word0 x &&& keyMask) = (a.word0 x &&& keyMask))
    {bit : UInt32} (hb : bit = ClauseHeader.garbageBit ∨ bit = ClauseHeader.redundantBit ∨
      bit = ClauseHeader.shrunkenBit) : b.flag x bit = a.flag x bit := by
  unfold flag; exact key_bit _ _ h hb

theorem chain_congr' {a b : Arena} (hs : a.sizeWards = b.sizeWards) :
    ∀ (fuel : Nat) (r : Ref),
    (∀ x ∈ a.chain r fuel, a.size x = b.size x ∧ a.shrunken x = false ∧ b.shrunken x = false) →
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
      obtain ⟨h2, hsh, hshb⟩ := h r hmem
      have hnext : a.nextClause r = b.nextClause r := by
        unfold nextClause
        rw [actualWards_of_not_shrunken a r hsh, actualWards_of_not_shrunken b r hshb, h2]
      rw [hnext, ih (b.nextClause r)]
      intro x hx
      apply h x
      unfold chain; simp only [hr, ite_true]; rw [hnext]; exact List.mem_cons_of_mem _ hx
    · have hr' : ¬ r.toNat < b.sizeWards := by omega
      simp [hr, hr']

theorem layoutFrom_congr' {a b : Arena} (hs : a.sizeWards = b.sizeWards) :
    ∀ (refs : List Ref) (r : Ref),
    (∀ x ∈ refs, a.size x = b.size x ∧ b.shrunken x = false) →
    LayoutFrom a r refs → LayoutFrom b r refs := by
  intro refs
  induction refs with
  | nil => intro r _ h; simp [LayoutFrom] at *; omega
  | cons r' rs ih =>
    intro r hagree h
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h
    obtain ⟨h2, hshb⟩ := hagree r' (List.mem_cons_self ..)
    have hn : a.nextClause r' = b.nextClause r' := by
      unfold nextClause
      rw [actualWards_of_not_shrunken a r' hsh, actualWards_of_not_shrunken b r' hshb, h2]
    refine ⟨rfl, by omega, hshb, by rw [← hn, hnext, h2], ?_⟩
    rw [← hn]
    exact ih _ (fun x hx => hagree x (List.mem_cons_of_mem _ hx)) hrest

theorem Same.flags {a b : Arena} (h : Same a b) {x : Ref} (hx : x ∈ a.chain 0 a.sizeWards) :
    b.garbage x = a.garbage x ∧ b.redundant x = a.redundant x ∧ b.shrunken x = a.shrunken x :=
  ⟨flag_of_key (h.key x hx) (Or.inl rfl), flag_of_key (h.key x hx) (Or.inr (Or.inl rfl)),
   flag_of_key (h.key x hx) (Or.inr (Or.inr rfl))⟩

theorem Same.layout {a b : Arena} (h : Same a b) (hl : a.Layout) : b.Layout := by
  have hsw : b.sizeWards = a.sizeWards := by simp [sizeWards, h.wsize]
  refine ⟨?_, by rw [h.wsize, hsw]; exact hl.mult4, by rw [hsw]; exact hl.bound⟩
  rw [h.chain]
  apply layoutFrom_congr' hsw.symm _ 0 _ hl.chain
  intro x hx
  refine ⟨(h.size x hx).symm, ?_⟩
  rw [(h.flags hx).2.2]; exact LayoutFrom.not_shrunken hl.chain x hx

theorem Same.refl (a : Arena) : Same a a :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Same.trans {a b c : Arena} (h1 : Same a b) (h2 : Same b c) : Same a c := by
  refine ⟨h2.wsize.trans h1.wsize, h2.chain.trans h1.chain, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [h2.size x (h1.chain ▸ hx), h1.size x hx]
  · intro x hx; rw [h2.lits x (h1.chain ▸ hx), h1.lits x hx]
  · intro x hx; rw [h2.searched x (h1.chain ▸ hx), h1.searched x hx]
  · intro x hx; rw [h2.key x (h1.chain ▸ hx), h1.key x hx]

/-- Header positions of distinct chain clauses, and against their size/searched/literal words. -/
theorem header_ne {a : Arena} (h : a.Layout) {r x : Ref} (hr : r ∈ a.chain 0 a.sizeWards)
    (hx : x ∈ a.chain 0 a.sizeWards) :
    base r ≠ base x + 1 ∧ base r ≠ base x + 2 ∧ (∀ k, k < (a.size x).toNat → base r ≠ litPos x k) ∧
    (r ≠ x → base r ≠ base x) := by
  have hfx := wardsOfClause_fits (a.size x).toNat
  have hfr := wardsOfClause_fits (a.size r).toNat
  unfold litPos base
  by_cases e : r = x
  · subst e; refine ⟨by omega, by omega, fun k _ => by omega, fun h => absurd rfl h⟩
  · rcases h.disjoint hr hx e with h1 | h1 <;>
      exact ⟨by omega, by omega, fun k hk => by omega, fun _ => by omega⟩

/-- Rewriting a header word while keeping the key bits. -/
theorem setWord0_same {a : Arena} (h : a.Layout) {r : Ref} (hr : r ∈ a.chain 0 a.sizeWards)
    {w : UInt32} (hw : (w &&& keyMask) = (a.word0 r &&& keyMask)) : Same a (a.setWord0 r w) := by
  have hsz : (a.setWord0 r w).words.size = a.words.size := by simp [setWord0]
  have hsw : (a.setWord0 r w).sizeWards = a.sizeWards := by simp [sizeWards, hsz]
  have hget : ∀ j, (a.setWord0 r w).words.get! j = if base r = j ∧ base r < a.words.size then w
      else a.words.get! j := by
    intro j; simp only [setWord0, U32Vec.get!_set!]
    by_cases e : base r = j
    · subst e; rfl
    · simp [e]
  have hsize : ∀ x ∈ a.chain 0 a.sizeWards, (a.setWord0 r w).size x = a.size x := by
    intro x hx; unfold size; rw [hget, if_neg (fun e => (header_ne h hr hx).2.1 e.1)]
  have hshr : ∀ x ∈ a.chain 0 a.sizeWards, (a.setWord0 r w).shrunken x = a.shrunken x := by
    intro x hx
    by_cases e : r = x
    · subst e; exact flag_of_key (by
        unfold word0; rw [hget]; by_cases hb : base r < a.words.size
        · rw [if_pos ⟨rfl, hb⟩]; exact hw
        · rw [if_neg (fun e => hb e.2)]) (Or.inr (Or.inr rfl))
    · unfold shrunken flag word0; rw [hget, if_neg (fun e' => (header_ne h hr hx).2.2.2 e e'.1)]
  have hch : (a.setWord0 r w).chain 0 (a.setWord0 r w).sizeWards = a.chain 0 a.sizeWards := by
    rw [hsw]; symm
    apply chain_congr' hsw.symm _ 0
    intro x hx
    have hns := LayoutFrom.not_shrunken h.chain x hx
    exact ⟨(hsize x hx).symm, hns, by rw [hshr x hx]; exact hns⟩
  refine ⟨hsz, hch, hsize, ?_, ?_, ?_⟩
  · intro x hx
    unfold litsL; rw [hsize x hx]
    apply List.map_congr_left; intro k hk
    simp at hk
    unfold lit; rw [hget, if_neg (fun e => (header_ne h hr hx).2.2.1 k hk e.1)]
  · intro x hx; unfold searched; rw [hget, if_neg (fun e => (header_ne h hr hx).1 e.1)]
  · intro x hx
    by_cases e : r = x
    · subst e; unfold word0; rw [hget]; by_cases hb : base r < a.words.size
      · rw [if_pos ⟨rfl, hb⟩]; exact hw
      · rw [if_neg (fun e => hb e.2)]
    · unfold word0; rw [hget, if_neg (fun e' => (header_ne h hr hx).2.2.2 e e'.1)]

theorem setGlue_same {a : Arena} (h : a.Layout) {r : Ref} (hr : r ∈ a.chain 0 a.sizeWards) (g : UInt32) :
    Same a (a.setGlue r g) :=
  setWord0_same h hr (by simp only [keyMask, MAX_GLUE, ClauseHeader.garbageBit,
    ClauseHeader.redundantBit, ClauseHeader.shrunkenBit]; bv_k)

theorem setUsed_same {a : Arena} (h : a.Layout) {r : Ref} (hr : r ∈ a.chain 0 a.sizeWards) (u : UInt32) :
    Same a (a.setUsed r u) :=
  setWord0_same h hr (by simp only [keyMask, MAX_USED, ClauseHeader.usedShift, ClauseHeader.garbageBit,
    ClauseHeader.redundantBit, ClauseHeader.shrunkenBit]; bv_k)

theorem setReason_same {a : Arena} (h : a.Layout) {r : Ref} (hr : r ∈ a.chain 0 a.sizeWards) (b : Bool) :
    Same a (a.setReason r b) := by
  apply setWord0_same h hr
  simp only [keyMask, ClauseHeader.reasonBit, ClauseHeader.garbageBit,
    ClauseHeader.redundantBit, ClauseHeader.shrunkenBit]
  cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> bv_k

end Arena
end LeanKissat
