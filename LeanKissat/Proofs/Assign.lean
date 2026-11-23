import LeanKissat.Proofs.SatFinal

/-!
# Effect of an assignment (`Asg.assign`, `Solver.assign`)
-/

namespace LeanKissat
open Solver

theorem lit_toNat_ne_not (l : Lit) : l.toNat ≠ (NOT l).toNat := by
  intro h
  have : l = NOT l := UInt32.toNat_inj.mp h
  exact NOT_ne l this.symm

theorem toNat_eq_iff (a b : Lit) : a.toNat = b.toNat ↔ a = b := UInt32.toNat_inj

namespace Asg

variable (a : Asg) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit) (reason : UInt32)

theorem assign_values_get! (j : Nat) (hb : (NOT lit).toNat < a.values.size)
    (hb' : lit.toNat < a.values.size) :
    (a.assign probing level binary lit reason).values.get! j =
      if j = (NOT lit).toNat then VAL_FALSE else if j = lit.toNat then VAL_TRUE
      else a.values.get! j := by
  simp only [Asg.assign]
  rw [ByteArray.get!_set!, ByteArray.get!_set!]
  simp only [ByteArray.size_set!']
  by_cases h1 : j = (NOT lit).toNat
  · subst h1; simp [hb]
  · by_cases h2 : j = lit.toNat
    · subst h2; simp [hb', Ne.symm h1]; intro h; exact absurd h h1
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

theorem assign_trail_view :
    (a.assign probing level binary lit reason).trail.view = a.trail.view ++ [lit] := by
  simp only [Asg.assign, U32Vec.view_push]

theorem assign_aLevel_get! (k : Nat) :
    (a.assign probing level binary lit reason).aLevel.get! k =
      if (IDX lit).toNat = k ∧ k < a.aLevel.size then level else a.aLevel.get! k := by
  simp only [Asg.assign, U32Vec.get!_set!]

end Asg
end LeanKissat

namespace LeanKissat
open Solver

theorem IDX_eq_iff (a b : Lit) : IDX a = IDX b ↔ a = b ∨ a = NOT b := by
  simp only [IDX, NOT]
  constructor
  · intro h
    by_cases e : a = b
    · exact Or.inl e
    · right; bv_k
  · rintro (rfl | rfl) <;> bv_k

theorem NOT_inj {a b : Lit} (h : NOT a = NOT b) : a = b := by
  have := congrArg NOT h; simpa [NOT_NOT] using this

namespace Solver

theorem markFixedLiteral_asg (s : Solver) (lit : Lit) : (s.markFixedLiteral lit).asg = s.asg := by
  simp [markFixedLiteral, deactivateVariable, setVarFlag]
  split <;> rfl

theorem markFixedLiteral_arena (s : Solver) (lit : Lit) : (s.markFixedLiteral lit).arena = s.arena := by
  simp [markFixedLiteral, deactivateVariable, setVarFlag]
  split <;> rfl

theorem markFixedLiteral_watches (s : Solver) (lit : Lit) :
    (s.markFixedLiteral lit).watches = s.watches := by
  simp [markFixedLiteral, deactivateVariable, setVarFlag]
  split <;> rfl

theorem markFixedLiteral_propagate (s : Solver) (lit : Lit) :
    (s.markFixedLiteral lit).propagate = s.propagate := by
  simp [markFixedLiteral, deactivateVariable, setVarFlag]
  split <;> rfl

theorem markFixedLiteral_frameTrail (s : Solver) (lit : Lit) :
    (s.markFixedLiteral lit).frameTrail = s.frameTrail := by
  simp [markFixedLiteral, deactivateVariable, setVarFlag]
  split <;> rfl

theorem markFixedLiteral_vars (s : Solver) (lit : Lit) : (s.markFixedLiteral lit).vars = s.vars := by
  simp [markFixedLiteral, deactivateVariable, setVarFlag]
  split <;> rfl

theorem assign_vars (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit)
    (reason : UInt32) : (s.assign probing level binary lit reason).vars = s.vars := by
  unfold Solver.assign
  split <;> simp [markFixedLiteral_vars]

theorem assign_asg (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit)
    (reason : UInt32) :
    (s.assign probing level binary lit reason).asg = s.asg.assign probing level binary lit reason := by
  unfold Solver.assign
  split <;> simp [markFixedLiteral_asg]

theorem assign_arena (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit)
    (reason : UInt32) : (s.assign probing level binary lit reason).arena = s.arena := by
  unfold Solver.assign
  split <;> simp [markFixedLiteral_arena]

theorem assign_watches (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit)
    (reason : UInt32) : (s.assign probing level binary lit reason).watches = s.watches := by
  unfold Solver.assign
  split <;> simp [markFixedLiteral_watches]

theorem assign_propagate (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit)
    (reason : UInt32) : (s.assign probing level binary lit reason).propagate = s.propagate := by
  unfold Solver.assign
  split <;> simp [markFixedLiteral_propagate]

theorem assign_frameTrail (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit)
    (reason : UInt32) : (s.assign probing level binary lit reason).frameTrail = s.frameTrail := by
  unfold Solver.assign
  split <;> simp [markFixedLiteral_frameTrail]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Literal in range of the per-literal arrays (its variable is `< vars`). -/
def ValidLit (s : Solver) (l : Lit) : Prop := (IDX l).toNat < s.vars.toNat

theorem IDX_toNat (l : Lit) : (IDX l).toNat = l.toNat / 2 := by
  simp [IDX, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem validLit_lt {s : Solver} {l : Lit} (h : s.ValidLit l) : l.toNat < 2 * s.vars.toNat := by
  unfold ValidLit at h; rw [IDX_toNat] at h; omega

/-- Size facts used by the read/write lemmas. -/
def Sizes (s : Solver) : Prop :=
  2 * s.vars.toNat ≤ s.asg.values.size ∧ s.vars.toNat ≤ s.asg.aLevel.size

/-- Trail literals are true. -/
def TrailTrue (s : Solver) : Prop := ∀ l ∈ s.trailL, s.IsTrue l

/-- The core assignment invariant. -/
structure Core (s : Solver) : Prop where
  valCons : ValCons s
  trueOnTrail : TrueOnTrail s
  trailTrue : TrailTrue s
  lvlVar : LvlVar s
  sizes : Sizes s
  /-- values are C `signed char`s in `{-1, 0, 1}` -/
  domain : ∀ j, s.asg.values.get! j = 0 ∨ s.asg.values.get! j = VAL_TRUE ∨
    s.asg.values.get! j = VAL_FALSE

theorem validLit_not {s : Solver} {l : Lit} (h : s.ValidLit l) : s.ValidLit (NOT l) := by
  unfold ValidLit at *; rw [IDX_NOT]; exact h

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The assignment-record update of `Solver.assign` (without the root-level
  bookkeeping of `kissat_mark_fixed_literal`, which touches other fields). -/
def withAssign (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool) (lit : Lit)
    (reason : UInt32) : Solver :=
  { s with asg := s.asg.assign probing level binary lit reason }

section AssignInv
variable {s : Solver} {probing : Bool} {level : UInt32} {binary : Bool} {lit : Lit}
  {reason : UInt32}

local notation "s'" => withAssign s probing level binary lit reason

/-- Values after an assignment. -/
theorem assign_value (hs : s.Sizes) (hl : s.ValidLit lit) (j : Nat) :
    (s').asg.values.get! j =
      if j = (NOT lit).toNat then VAL_FALSE else if j = lit.toNat then VAL_TRUE
      else s.asg.values.get! j := by
  show (s.asg.assign probing level binary lit reason).values.get! j = _
  have h1 := validLit_lt hl
  have h2 := validLit_lt (validLit_not hl)
  exact Asg.assign_values_get! _ _ _ _ _ _ j (by have := hs.1; omega) (by have := hs.1; omega)

theorem assign_isTrue (hs : s.Sizes) (hl : s.ValidLit lit) (l : Lit) :
    (s').IsTrue l ↔ (l = lit ∨ (l ≠ NOT lit ∧ s.IsTrue l)) := by
  unfold IsTrue
  rw [assign_value hs hl]
  by_cases h1 : l = NOT lit
  · subst h1; simp [toNat_eq_iff, VAL_FALSE, VAL_TRUE, NOT_ne]
  · by_cases h2 : l = lit
    · subst h2; simp [toNat_eq_iff, h1]
    · simp [toNat_eq_iff, h1, h2]

theorem assign_isFalse (hs : s.Sizes) (hl : s.ValidLit lit) (l : Lit) :
    (s').IsFalse l ↔ (l = NOT lit ∨ (l ≠ lit ∧ s.IsFalse l)) := by
  unfold IsFalse
  rw [assign_value hs hl]
  by_cases h1 : l = NOT lit
  · subst h1; simp [toNat_eq_iff]
  · by_cases h2 : l = lit
    · subst h2; simp [toNat_eq_iff, h1, VAL_FALSE, VAL_TRUE]
    · simp [toNat_eq_iff, h1, h2]

theorem assign_lvl (hs : s.Sizes) (hl : s.ValidLit lit) (l : Lit) :
    (s').lvl l = if IDX l = IDX lit then level.toNat else s.lvl l := by
  unfold lvl
  show ((s.asg.assign probing level binary lit reason).aLevel.get! _).toNat = _
  rw [Asg.assign_aLevel_get!]
  have hv : (IDX lit).toNat < s.asg.aLevel.size := by
    have := hs.2; unfold ValidLit at hl; omega
  by_cases h : IDX l = IDX lit
  · rw [h]; simp [hv]
  · have : ¬ ((IDX lit).toNat = (IDX l).toNat) := fun e => h (UInt32.toNat_inj.mp e).symm
    simp [h, this]

theorem assign_trailL : (s').trailL = s.trailL ++ [lit] := by
  unfold trailL; exact Asg.assign_trail_view _ _ _ _ _ _

theorem assign_pushLevel (p : Nat) : (s').pushLevel p = s.pushLevel p := rfl

theorem assign_clauseL (r : Ref) : (s').clauseL r = s.clauseL r := rfl

/-- An assignment of an unassigned valid literal preserves the core invariant and
  the watch invariant (for every propagation pointer up to the old trail end). -/
theorem assign_core (hc : s.Core) (hl : s.ValidLit lit)
    (hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit) :
    (s').Core ∧ (s').IsTrue lit ∧
    (∀ P c, P ≤ s.trailL.length → s.InvSAt P c → (s').InvSAt P c) := by
  have hs := hc.sizes
  have hnl : ¬ s.IsTrue (NOT lit) := by
    intro h; have := (hc.valCons (NOT lit)).1.mp h; rw [NOT_NOT] at this; exact hun.2 this
  have hlitTrail : lit ∉ s.trailL := fun h => hun.1 (hc.trailTrue lit h)
  refine ⟨⟨?vc, ?tot, ?tt, ?lv, ?sz, ?dom⟩, (assign_isTrue hs hl lit).mpr (Or.inl rfl), ?inv⟩
  case dom =>
    intro j
    have := hc.domain j
    rw [assign_value hs hl j]
    split
    · exact Or.inr (Or.inr rfl)
    · split
      · exact Or.inr (Or.inl rfl)
      · exact this
  case vc =>
    intro l
    rw [assign_isTrue hs hl, assign_isFalse hs hl, assign_isFalse hs hl]
    have hv := hc.valCons l
    constructor
    · constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact Or.inl rfl
        · right; refine ⟨fun e => h1 (by rw [← e, NOT_NOT]), hv.1.mp h2⟩
      · rintro (e | ⟨h1, h2⟩)
        · exact Or.inl (NOT_inj e)
        · right; refine ⟨fun e => h1 (by rw [e, NOT_NOT]), hv.1.mpr h2⟩
    · rintro ⟨h1 | ⟨h1, h2⟩, h3 | ⟨h3, h4⟩⟩
      · subst h1; exact NOT_ne _ h3.symm
      · exact h3 h1
      · exact h1 h3
      · exact hv.2 ⟨h2, h4⟩
  case tot =>
    intro l h
    rw [assign_isTrue hs hl] at h
    rw [assign_trailL, assign_lvl hs hl]
    rcases h with rfl | ⟨h1, h2⟩
    · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
    · rcases hc.trueOnTrail l h2 with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · by_cases e : IDX l = IDX lit
        · rcases (IDX_eq_iff l lit).mp e with rfl | rfl
          · exact absurd h2 hun.1
          · exact absurd h2 hnl
        · right; simp [e, h]
  case tt =>
    intro l h
    rw [assign_trailL] at h
    rw [assign_isTrue hs hl]
    rcases List.mem_append.mp h with h | h
    · have := hc.trailTrue l h
      by_cases e : l = lit
      · exact Or.inl e
      · right; exact ⟨fun e' => hnl (e' ▸ this), this⟩
    · exact Or.inl (List.mem_singleton.mp h)
  case lv =>
    intro l
    rw [assign_lvl hs hl, assign_lvl hs hl, IDX_NOT, hc.lvlVar]
  case sz =>
    unfold Sizes
    show 2 * s.vars.toNat ≤ (s.asg.assign probing level binary lit reason).values.size ∧
      s.vars.toNat ≤ (s.asg.assign probing level binary lit reason).aLevel.size
    simp only [Asg.assign, ByteArray.size_set!', U32Vec.size_set!]
    exact hs
  case inv =>
    intro P c hP h w0 w1 rest hcw k0 k1 h0 h1
    have back : ∀ w k, (s').PropFalseAt P w k → s.PropFalseAt P w k := by
      intro w k ⟨hf, hd⟩
      rw [assign_isFalse hs hl] at hf
      rcases hf with rfl | ⟨hw, hf⟩
      · -- `NOT lit` became false now; its negation `lit` is at the end of the trail
        exfalso
        rcases hd with ⟨p, hp, hpP, _⟩ | ⟨hm, _, _⟩
        · rw [assign_trailL, NOT_NOT] at hp
          have hpl : p < s.trailL.length := by omega
          rw [List.getElem?_append_left hpl] at hp
          exact hlitTrail (List.mem_of_getElem? hp)
        · rw [assign_trailL, NOT_NOT] at hm
          exact hm (List.mem_append_right _ (List.mem_singleton_self _))
      · refine ⟨hf, ?_⟩
        rcases hd with ⟨p, hp, hpP, hk⟩ | ⟨hm, hl0, hk⟩
        · left
          refine ⟨p, ?_, hpP, by rw [hk, assign_pushLevel]⟩
          rw [assign_trailL] at hp
          rwa [List.getElem?_append_left (by omega)] at hp
        · right
          refine ⟨fun hm' => hm (by rw [assign_trailL]; exact List.mem_append_left _ hm'), ?_, hk⟩
          rw [assign_lvl hs hl] at hl0
          by_cases e : IDX w = IDX lit
          · rcases (IDX_eq_iff w lit).mp e with rfl | rfl
            · exact absurd rfl hw
            · exact absurd ((hc.valCons lit).1.mpr hf) hun.1
          · simpa [e] using hl0
    obtain ⟨t, ht, htt, hlt⟩ := h w0 w1 rest hcw k0 k1 (back _ _ h0) (back _ _ h1)
    refine ⟨t, ht, (assign_isTrue hs hl t).mpr (Or.inr ⟨fun e => hnl (e ▸ htt), htt⟩), ?_⟩
    rw [assign_lvl hs hl]
    by_cases e : IDX t = IDX lit
    · rcases (IDX_eq_iff t lit).mp e with rfl | rfl
      · exact absurd htt hun.1
      · exact absurd htt hnl
    · simpa [e] using hlt

end AssignInv
end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem assign_eq_withAssign (s : Solver) (probing : Bool) (level : UInt32) (binary : Bool)
    (lit : Lit) (reason : UInt32) :
    s.assign probing level binary lit reason =
      (if level == 0 then s.markFixedLiteral lit else s).withAssign probing level binary lit reason := by
  unfold Solver.assign withAssign
  split <;> rfl

/-- Two states with the same assignment record, arena, frames, propagation pointer
  and number of variables have the same semantic view. -/
structure SameView (s t : Solver) : Prop where
  asg : s.asg = t.asg
  arena : s.arena = t.arena
  frameTrail : s.frameTrail = t.frameTrail
  propagate : s.propagate = t.propagate
  vars : s.vars = t.vars

theorem sameView_markFixed (s : Solver) (lit : Lit) : SameView (s.markFixedLiteral lit) s :=
  ⟨markFixedLiteral_asg s lit, markFixedLiteral_arena s lit, markFixedLiteral_frameTrail s lit,
   markFixedLiteral_propagate s lit, markFixedLiteral_vars s lit⟩

theorem SameView.core {s t : Solver} (h : SameView s t) (hc : t.Core) : s.Core := by
  obtain ⟨ha, _, _, _, hv⟩ := h
  have e1 : ∀ l, s.IsTrue l ↔ t.IsTrue l := by intro l; simp [IsTrue, ha]
  have e2 : ∀ l, s.IsFalse l ↔ t.IsFalse l := by intro l; simp [IsFalse, ha]
  have e3 : ∀ l, s.lvl l = t.lvl l := by intro l; simp [lvl, ha]
  have e4 : s.trailL = t.trailL := by simp [trailL, ha]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l; rw [e1, e2, e2]; exact hc.valCons l
  · intro l h; rw [e1] at h; rw [e4, e3]; exact hc.trueOnTrail l h
  · intro l h; rw [e4] at h; rw [e1]; exact hc.trailTrue l h
  · intro l; rw [e3, e3]; exact hc.lvlVar l
  · unfold Sizes; rw [ha, hv]; exact hc.sizes
  · intro j; rw [ha]; exact hc.domain j

theorem SameView.invSAt {s t : Solver} (h : SameView s t) (P : Nat) (c : List Lit) :
    s.InvSAt P c ↔ t.InvSAt P c := by
  obtain ⟨ha, _, hf, _, _⟩ := h
  have : s.PropFalseAt = t.PropFalseAt := by
    funext P w k; simp [PropFalseAt, IsFalse, trailL, lvl, pushLevel, framesL, ha, hf]
  simp only [InvSAt, this, IsTrue, lvl, ha]

end Solver
end LeanKissat
