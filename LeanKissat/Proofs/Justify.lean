import LeanKissat.Proofs.Struct

/-!
# Semantic implication, root units and reasons

`Φ` is a set of assignments of the internal variables (later: the assignments that
satisfy the input formula). `Implied Φ c`: every assignment in `Φ` satisfies `c`.
-/

namespace LeanKissat
namespace Solver

/-- Truth of an internal literal under an assignment of the internal variables. -/
def litVal (β : Nat → Bool) (l : Lit) : Bool := β (IDX l).toNat ^^ (l &&& 1 != 0)

theorem sign_NOT (l : Lit) : ((NOT l) &&& 1 != 0) = !(l &&& 1 != 0) := by
  simp only [NOT]
  by_cases h : l &&& 1 = 0
  · have : (l ^^^ 1) &&& 1 = 1 := by bv_k
    simp [h, this]
  · have : (l ^^^ 1) &&& 1 = 0 := by bv_k
    simp [h, this]

theorem litVal_NOT (β : Nat → Bool) (l : Lit) : litVal β (NOT l) = !litVal β l := by
  unfold litVal; rw [IDX_NOT, sign_NOT]; cases β (IDX l).toNat <;> cases (l &&& 1 != 0) <;> rfl

def Implied (Φ : (Nat → Bool) → Prop) (c : List Lit) : Prop :=
  ∀ β, Φ β → ∃ x ∈ c, litVal β x = true

/-- Every database clause is implied. -/
def DBImplied (Φ : (Nat → Bool) → Prop) (s : Solver) : Prop := ∀ c, s.InDB c → Implied Φ c

/-- Every root-level true literal is implied. -/
def RootImplied (Φ : (Nat → Bool) → Prop) (s : Solver) : Prop :=
  ∀ l, s.IsTrue l → s.lvl l = 0 → Implied Φ [l]

theorem Implied.perm {Φ : (Nat → Bool) → Prop} {c d : List Lit} (h : Implied Φ c)
    (hp : ∀ x, x ∈ c → x ∈ d) : Implied Φ d := by
  intro β hβ
  obtain ⟨x, hx, hv⟩ := h β hβ
  exact ⟨x, hp x hx, hv⟩

/-- Unit resolution: if all literals of an implied clause other than `x` are implied
  false, `x` is implied. -/
theorem Implied.unit {Φ : (Nat → Bool) → Prop} {c : List Lit} (h : Implied Φ c) {x : Lit}
    (hother : ∀ y ∈ c, y ≠ x → Implied Φ [NOT y]) : Implied Φ [x] := by
  intro β hβ
  obtain ⟨z, hz, hv⟩ := h β hβ
  by_cases e : z = x
  · subst e; exact ⟨z, by simp, hv⟩
  · obtain ⟨w, hw, hwv⟩ := hother z hz e β hβ
    simp at hw; subst hw
    rw [litVal_NOT, hv] at hwv
    simp at hwv

/-- Reason of an assigned literal (`assigned[idx].reason`, `.binary`). -/
def reasonOf (s : Solver) (l : Lit) : UInt32 := s.reasonIdx (IDX l)
def binOf (s : Solver) (l : Lit) : Bool := s.isBinaryReason (IDX l)

/-- `a` is on the trail before `b`. -/
def Before (s : Solver) (a b : Lit) : Prop := [a, b].Sublist s.trailL

/-- `x` is a valid antecedent literal for the true literal `l`: false, assigned at a
  level at most `l`'s and (above the root) before `l` on the trail. -/
def Ante (s : Solver) (l x : Lit) : Prop :=
  s.IsFalse x ∧ s.lvl x ≤ s.lvl l ∧ (0 < s.lvl x → s.Before (NOT x) l)

/-- The reason of the true literal `l` justifies it. -/
def ReasonAt (s : Solver) (l : Lit) : Prop :=
  s.reasonOf l = DECISION_REASON ∨
  (s.binOf l = true ∧ s.BinWatched l (s.reasonOf l) ∧ s.Ante l (s.reasonOf l)) ∨
  (s.binOf l = false ∧ s.LiveRef (s.reasonOf l) ∧ l ∈ s.clauseL (s.reasonOf l) ∧
    ∀ x ∈ s.clauseL (s.reasonOf l), x ≠ l → s.Ante l x)

theorem ante_congr {s t : Solver} (ha : t.asg = s.asg) {l x : Lit} : t.Ante l x ↔ s.Ante l x := by
  simp [Ante, Before, IsFalse, lvl, trailL, ha]

/-- Transfer of `ReasonAt` along equal assignments and equivalent databases. -/
theorem reasonAt_congr {s t : Solver} (ha : t.asg = s.asg)
    (hl : ∀ r, s.LiveRef r → t.LiveRef r)
    (hc : ∀ r, s.LiveRef r → ∀ x, x ∈ t.clauseL r ↔ x ∈ s.clauseL r)
    (hb : ∀ a b, s.BinWatched a b → t.BinWatched a b) {l : Lit} (h : s.ReasonAt l) :
    t.ReasonAt l := by
  have eR : t.reasonOf = s.reasonOf := by funext l; simp [reasonOf, reasonIdx, ha]
  have eB : t.binOf = s.binOf := by funext l; simp [binOf, isBinaryReason, abit, abits, ha]
  unfold ReasonAt
  rw [eR, eB]
  rcases h with e | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl ⟨b1, hb _ _ b2, (ante_congr ha).mpr b3⟩)
  · exact Or.inr (Or.inr ⟨b1, hl _ b2, (hc _ b2 l).mpr b3,
      fun x hx hne => (ante_congr ha).mpr (b4 x ((hc _ b2 x).mp hx) hne)⟩)

/-- Every true literal above the root level is justified by its reason. -/
def ReasonOK (s : Solver) : Prop := ∀ l, s.IsTrue l → 0 < s.lvl l → s.ReasonAt l

/-- The per-variable reason arrays cover all variables, and literals of variables
  beyond `vars` are unassigned. -/
def ReasonSizes (s : Solver) : Prop :=
  s.vars.toNat ≤ s.asg.aReason.size ∧ s.vars.toNat ≤ s.asg.aBits.size ∧
  (∀ j, 2 * s.vars.toNat ≤ j → s.asg.values.get! j = 0) ∧
  -- `unassigned` counts the unassigned variables
  s.asg.unassigned.toNat +
    (List.range s.vars.toNat).countP (fun v => s.asg.values.get! (2 * v) != 0) = s.vars.toNat ∧
  -- the trail assigns each variable at most once
  (s.trailL.map IDX).Nodup

/-- True literals are valid. -/
theorem ReasonSizes.valid {s : Solver} (h : s.ReasonSizes) {l : Lit} (hl : s.IsTrue l) :
    s.ValidLit l := by
  unfold ValidLit; rw [IDX_toNat]
  apply Classical.byContradiction; intro hc
  have := h.2.2.1 l.toNat (by omega)
  unfold IsTrue at hl; rw [this] at hl; simp [VAL_TRUE] at hl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

section
variable {s : Solver} {probing : Bool} {level : UInt32} {binary : Bool} {lit : Lit}
  {reason : UInt32}

theorem countP_range_update (p q : Nat → Bool) (v : Nat) (hq : q v = true) (hp : p v = false)
    (he : ∀ w, w ≠ v → q w = p w) :
    ∀ n, v < n → (List.range n).countP q = (List.range n).countP p + 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    rw [List.range_succ, List.countP_append, List.countP_append]
    by_cases e : v = n
    · subst e
      have h0 : (List.range v).countP q = (List.range v).countP p := by
        apply List.countP_congr
        intro w hw; rw [he w (by simp at hw; omega)]
      simp [h0, hq, hp]
    · have := ih (by omega)
      rw [this]; simp [List.countP_cons, he n (Ne.symm e)]; omega

theorem two_mul_idx (x : Lit) : 2 * (IDX x).toNat = x.toNat ∨ 2 * (IDX x).toNat = (NOT x).toNat := by
  have h1 : (IDX x).toNat = x.toNat / 2 := IDX_toNat x
  have h2 : (IDX (NOT x)).toNat = (NOT x).toNat / 2 := IDX_toNat (NOT x)
  rw [IDX_NOT] at h2
  have hne : (NOT x).toNat ≠ x.toNat := fun e => NOT_ne x (UInt32.toNat_inj.mp e)
  omega

theorem assign_reasonSizes (h : s.ReasonSizes) (hc : s.Core) (hl : s.ValidLit lit)
    (hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit) :
    (s.withAssign probing level binary lit reason).ReasonSizes := by
  have hs := hc.sizes
  have hv : (s.withAssign probing level binary lit reason).vars = s.vars := rfl
  have h1 := validLit_lt hl
  have h2 := validLit_lt (validLit_not hl)
  have hval : ∀ j, (s.withAssign probing level binary lit reason).asg.values.get! j =
      if j = (NOT lit).toNat then VAL_FALSE else if j = lit.toNat then VAL_TRUE
      else s.asg.values.get! j := assign_value hs hl
  have hx0 : s.asg.values.get! lit.toNat = 0 := by
    rcases hc.domain lit.toNat with e | e | e
    · exact e
    · exact absurd e hun.1
    · exact absurd e hun.2
  have hnx0 : s.asg.values.get! (NOT lit).toNat = 0 := by
    have hnt : ¬ s.IsTrue (NOT lit) := by
      intro h; have := (hc.valCons (NOT lit)).1.mp h; rw [NOT_NOT] at this; exact hun.2 this
    have hnf : ¬ s.IsFalse (NOT lit) := by
      intro h; have := (hc.valCons lit).1.mpr h; exact hun.1 this
    rcases hc.domain (NOT lit).toNat with e | e | e
    · exact e
    · exact absurd e hnt
    · exact absurd e hnf
  obtain ⟨r1, r2, r3, r4, r5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [withAssign, Asg.assign, U32Vec.size_set!]; exact r1
  · simp only [withAssign, Asg.assign, ByteArray.size_set!']; exact r2
  · intro j hj
    rw [hv] at hj
    rw [hval, if_neg (by omega), if_neg (by omega)]
    exact r3 j hj
  · rw [hv]
    have hvar : (IDX lit).toNat < s.vars.toNat := hl
    have hcnt := countP_range_update (fun v => s.asg.values.get! (2 * v) != 0)
      (fun v => (s.withAssign probing level binary lit reason).asg.values.get! (2 * v) != 0)
      (IDX lit).toNat
      (by
        rcases two_mul_idx lit with e | e <;> rw [e, hval]
        · rw [if_neg (lit_toNat_ne_not lit), if_pos rfl]; decide
        · rw [if_pos rfl]; decide)
      (by
        rcases two_mul_idx lit with e | e <;> rw [e]
        · rw [hx0]; rfl
        · rw [hnx0]; rfl)
      (by
        intro w hw
        have e1 : 2 * w ≠ (NOT lit).toNat := by
          intro e; apply hw; have := IDX_toNat (NOT lit); rw [IDX_NOT] at this; omega
        have e2 : 2 * w ≠ lit.toNat := by
          intro e; apply hw; have := IDX_toNat lit; omega
        rw [hval, if_neg e1, if_neg e2])
      s.vars.toNat hvar
    -- the unassigned counter
    have hlt : (List.range s.vars.toNat).countP (fun v => s.asg.values.get! (2 * v) != 0) <
        s.vars.toNat := by
      have := List.countP_le_length (p := fun v => (s.withAssign probing level binary lit reason).asg.values.get! (2 * v) != 0) (l := List.range s.vars.toNat)
      simp at this; omega
    have hu : 1 ≤ s.asg.unassigned.toNat := by omega
    show (s.asg.unassigned - 1).toNat + _ = _
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hu)]
    have : (1 : UInt32).toNat = 1 := rfl
    rw [this, hcnt]; omega
  · rw [assign_trailL, List.map_append, List.nodup_append]
    refine ⟨r5, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    obtain ⟨l, hl', rfl⟩ := List.mem_map.mp ha
    intro e
    rcases (IDX_eq_iff l lit).mp e with rfl | rfl
    · exact hun.1 (hc.trailTrue _ hl')
    · have := hc.trailTrue _ hl'
      exact hun.2 (by have := (hc.valCons (NOT lit)).1.mp this; rwa [NOT_NOT] at this)

theorem assign_reasonOf_ne (l : Lit) (hne : IDX l ≠ IDX lit) :
    (s.withAssign probing level binary lit reason).reasonOf l = s.reasonOf l := by
  simp only [reasonOf, reasonIdx, withAssign, Asg.assign, U32Vec.get!_set!]
  rw [if_neg]; intro ⟨e, _⟩; exact hne (UInt32.toNat_inj.mp e).symm

theorem assign_binOf_ne (l : Lit) (hne : IDX l ≠ IDX lit) :
    (s.withAssign probing level binary lit reason).binOf l = s.binOf l := by
  simp only [binOf, isBinaryReason, abit, abits, withAssign, Asg.assign]
  rw [ByteArray.get!_set!_ne]; intro e; exact hne (UInt32.toNat_inj.mp e).symm

theorem assign_reasonOf_self (h : s.ReasonSizes) (hl : s.ValidLit lit) (hk : level ≠ 0) :
    (s.withAssign probing level binary lit reason).reasonOf lit = reason := by
  simp only [reasonOf, reasonIdx, withAssign, Asg.assign]
  have : (IDX lit).toNat < s.asg.aReason.size := by unfold ValidLit at hl; have := h.1; omega
  rw [U32Vec.get!_set!_self _ _ _ this]
  have : (level == 0) = false := by simpa using hk
  simp only [this]
  bv_k

theorem assign_binOf_self (h : s.ReasonSizes) (hl : s.ValidLit lit) (hk : level ≠ 0) :
    (s.withAssign probing level binary lit reason).binOf lit = binary := by
  simp only [binOf, isBinaryReason, abit, abits, withAssign, Asg.assign]
  have : (IDX lit).toNat < s.asg.aBits.size := by unfold ValidLit at hl; have := h.2.1; omega
  rw [ByteArray.get!_set!_self _ _ _ this]
  have : (level == 0) = false := by simpa using hk
  simp only [this, ABits.binary]
  generalize (reason == UNIT_REASON) = c
  cases binary <;> cases c <;> decide

end

end Solver
end LeanKissat
