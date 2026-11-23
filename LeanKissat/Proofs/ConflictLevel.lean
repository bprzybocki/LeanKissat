import LeanKissat.Proofs.Unwatch
import LeanKissat.Proofs.Deduce

/-!
# `oneLiteralOnConflictLevel`
-/

namespace LeanKissat
namespace Solver
open Arena

theorem invSAt_mono {s : Solver} {P P' : Nat} {c : List Lit} (h : s.InvSAt P c) (hle : P' ≤ P) : s.InvSAt P' c := by
  intro w0 w1 rest he k0 k1 h0 h1
  have up : ∀ w k, s.PropFalseAt P' w k → s.PropFalseAt P w k := by
    rintro w k ⟨hf, ⟨p, hp, hpP, hk⟩ | h2⟩
    · exact ⟨hf, Or.inl ⟨p, hp, by omega, hk⟩⟩
    · exact ⟨hf, Or.inr h2⟩
  exact h w0 w1 rest he k0 k1 (up _ _ h0) (up _ _ h1)

/-- A literal of positive level `L` is not propagated false before the start of level `L`. -/
theorem not_propFalse_of_lvl {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {w : Lit} {L : Nat}
    (hL : 0 < L) (hw : s.lvl w = L) (hLe : L ≤ s.level.toNat) {P : Nat}
    (hP : P ≤ s.framesL[L - 1]'(by rw [hs.levelOK.len]; omega)) (k : Nat) : ¬ s.PropFalseAt P w k := by
  rintro ⟨hf, ⟨p, hp, hpP, _⟩ | ⟨_, h0, _⟩⟩
  · have hpl := hs.levelOK.pushLe p _ hp
    rw [hs.core.lvlVar, hw] at hpl
    -- the push level of a position before the start of level `L` is below `L`
    have hsorted := hs.levelOK.sorted
    have hlen := hs.levelOK.len
    have : s.pushLevel p ≤ L - 1 := by
      unfold pushLevel
      have key := countP_le_of_sorted s.framesL (L - 1) p hsorted (by rw [hlen]; omega) (by omega)
      rw [key]
      have := List.countP_le_length (p := fun f : Nat => Decidable.decide (f ≤ p)) (l := s.framesL.take (L - 1))
      simp at this; omega
    omega
  · omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- An implied clause all of whose literals are false at the root makes `Φ` unsatisfiable. -/
theorem unsat_of_root_false {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {c : List Lit}
    (hc : Implied Φ c) (hf : ∀ x ∈ c, s.IsFalse x ∧ s.lvl x = 0) : ¬ ∃ β, Φ β := by
  rintro ⟨β, hβ⟩
  obtain ⟨x, hx, hv⟩ := hc β hβ
  obtain ⟨h1, h2⟩ := hf x hx
  have ht : s.IsTrue (NOT x) := by
    have := (hs.core.valCons (NOT x)).1; rw [NOT_NOT] at this; exact this.mpr h1
  obtain ⟨z, hz, hzv⟩ := hs.roots _ ht (by rw [hs.core.lvlVar]; exact h2) β hβ
  simp at hz; subst hz
  rw [litVal_NOT, hv] at hzv; simp at hzv

/-- The literals of a conflict form an implied clause. -/
theorem ConflictOK.implied {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {c : CRef}
    (h : ConflictOK s s c) : Implied Φ ((List.range (s.crefSize c)).map (s.crefLit c)) := by
  cases c with
  | binConflict =>
    obtain ⟨hb, _, _⟩ := h
    have := hs.db _ ((inDB_iff _ _).mpr (Or.inr ⟨_, _, hb, rfl⟩))
    have e : (List.range (s.crefSize .binConflict)).map (s.crefLit .binConflict) = [s.conflictLit0, s.conflictLit1] := by
      simp [crefSize, crefLit, List.range_succ]
    rw [e]; exact this
  | large r =>
    obtain ⟨hl, _⟩ := h
    have := hs.db _ ((inDB_iff _ _).mpr (Or.inl ⟨r, hl, rfl⟩))
    exact this

/-- Preconditions at a conflict. -/
structure CPre (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) : Prop where
  inv : SInv Φ s
  conflict : ConflictOK s s c
  invP : ∀ d, s.InDB d → s.InvSAt (s.propagate - 1) d
  framesLe : ∀ f ∈ s.framesL, f ≤ s.propagate - 1
  levelLt : s.level < INVALID_LEVEL
  watching : s.watching = true

/-- The state handed to conflict analysis. -/
structure APost (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) (t : Solver) (L : UInt32) : Prop where
  inv : SInv Φ t
  level : t.level = L
  conflict : ConflictOK t t c
  invP : ∀ d, t.InDB d → t.InvSAt (t.framesL[L.toNat - 1]!) d
  hasL : ∃ k, k < t.crefSize c ∧ t.lvl (t.crefLit c k) = L.toNat
  bits : ∀ i b, t.abit i b = s.abit i b
  ana : anaSide t = anaSide s
  mono : IrrMono s t

/-- Result of `oneLiteralOnConflictLevel`. -/
def COut (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) (r : Bool × UInt32 × Solver) : Prop :=
  (r.1 = false ∧ r.2.1 = 0 ∧ r.2.2.inconsistent = true ∧ ¬ ∃ β, Φ β) ∨ (r.1 = true ∧ r.2.2.overflowed = true) ∨
  (r.1 = true ∧ LOut Φ s r.2.2 ∧ r.2.2.clause = s.clause) ∨
  (r.1 = false ∧ 0 < r.2.1.toNat ∧ APost Φ s c r.2.2 r.2.1)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem crefSize_pos {s : Solver} {c : CRef} (hW : s.WatchStruct) (h : ConflictOK s s c) : 2 ≤ s.crefSize c := by
  cases c with
  | binConflict => simp [crefSize]
  | large r => have := (hW.live r h.1).1; simp only [crefSize]; omega

theorem crefLit_mem_large {s : Solver} {r : Ref} {k : Nat} (hk : k < s.crefSize (.large r)) :
    s.crefLit (.large r) k ∈ s.clauseL r := lit_mem_litsL _ _ _ hk

theorem ConflictOK.lit_false' {s : Solver} {c : CRef} (h : ConflictOK s s c) {k : Nat} (hk : k < s.crefSize c) :
    s.IsFalse (s.crefLit c k) := ConflictOK.lit_false h hk

/-- The state after the optional backtracking to the conflict level. -/
structure CMid (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) (cl : UInt32) (t : Solver) : Prop where
  inv : SInv Φ t
  level : t.level = cl
  conflict : ConflictOK t t c
  invP : ∀ d, t.InDB d → t.InvSAt (t.framesL[cl.toNat - 1]!) d
  size : t.crefSize c = s.crefSize c
  lits : ∀ k, t.crefLit c k = s.crefLit c k
  bits : ∀ i b, t.abit i b = s.abit i b
  ana : anaSide t = anaSide s
  lvl : ∀ l, t.lvl l = s.lvl l
  mono : IrrMono s t

theorem framesL_last {Φ : (Nat → Bool) → Prop} {t : Solver} (ht : SInv Φ t) {L : Nat} (hL : t.level.toNat = L)
    (hpos : 0 < L) : (t.framesL[L - 1]! = t.framesL[L - 1]'(by rw [ht.levelOK.len, hL]; omega)) ∧
      ∀ f ∈ t.framesL, f ≤ t.framesL[L - 1]'(by rw [ht.levelOK.len, hL]; omega) := by
  have hlen : t.framesL.length = L := by rw [ht.levelOK.len, hL]
  refine ⟨getElem!_pos t.framesL (L - 1) (by omega), fun f hf => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
  have hs := ht.levelOK.sorted
  rw [List.pairwise_iff_getElem] at hs
  by_cases e : j = L - 1
  · subst e; exact Nat.le_refl _
  · exact hs j (L - 1) hj (by omega) (by omega)

theorem conflict_mid {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (h : CPre Φ s c) {cl : UInt32}
    (hcl0 : cl ≠ 0) (hle : cl ≤ s.level)
    (hmaxN : ∀ k, k < s.crefSize c → s.lvl (s.crefLit c k) ≤ cl.toNat) :
    CMid Φ s c cl (if cl < s.level then s.backtrackAfterConflict cl else s) := by
  have hs := h.inv
  have hclpos : 0 < cl.toNat := by
    have : cl.toNat ≠ 0 := fun e => hcl0 (UInt32.toNat_inj.mp (by simpa using e)); omega
  split
  · rename_i hlt
    have hl0 : s.level ≠ 0 := by intro e; rw [e] at hlt; exact absurd hlt (by simp)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ :=
      backtrackAfterConflict_spec hs hl0 hlt h.invP h.framesLe
    generalize s.backtrackAfterConflict cl = t at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 ⊢
    have eA := b6; have eW := b7
    have hsize : t.crefSize c = s.crefSize c := by cases c <;> simp [crefSize, eA]
    have hc01 : t.conflictLit0 = s.conflictLit0 ∧ t.conflictLit1 = s.conflictLit1 := by
      have := b4; simp only [anaSide, Prod.mk.injEq] at this
      exact ⟨this.2.2.2.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    have hlits : ∀ k, t.crefLit c k = s.crefLit c k := by
      intro k; cases c <;> simp [crefLit, eA, hc01.1, hc01.2]
    have hlvl : ∀ l, t.lvl l = s.lvl l := by intro l; unfold lvl; rw [b10]
    have hfalse : ∀ k, k < s.crefSize c → t.IsFalse (s.crefLit c k) := by
      intro k hk
      have hf := ConflictOK.lit_false h.conflict hk
      have ht : s.IsTrue (NOT (s.crefLit c k)) := by
        have := (hs.core.valCons (NOT (s.crefLit c k))).1; rw [NOT_NOT] at this; exact this.mpr hf
      have := b11 _ ht (by rw [hs.core.lvlVar]; exact hmaxN k hk)
      have := (b1.core.valCons (NOT (s.crefLit c k))).1.mp this
      rwa [NOT_NOT] at this
    have hP := framesL_last b1 (by rw [b2]) hclpos
    refine ⟨b1, b2, ?_, fun d hd => ?_, hsize, hlits, fun i b => by unfold Solver.abit Solver.abits; rw [b9], b4, hlvl,
      IrrMono.of_keep b6 b7 b10 (fun l h1 h2 => b11 l h1 (by rw [h2]; exact Nat.zero_le _))⟩
    · cases c with
      | binConflict =>
        obtain ⟨hb, _, _⟩ := h.conflict
        refine ⟨?_, by rw [hc01.1]; exact hfalse 0 (by simp [crefSize]), by rw [hc01.2]; exact hfalse 1 (by simp [crefSize])⟩
        rw [hc01.1, hc01.2]
        have := (b5 [s.conflictLit0, s.conflictLit1]).mpr ((inDB_iff _ _).mpr (Or.inr ⟨_, _, hb, rfl⟩))
        rcases (inDB_iff _ _).mp this with ⟨r, _, hr⟩ | ⟨x, y, hxy, hxy'⟩
        · -- a large clause can't have two literals
          exfalso
          have hlr := (b1.ws.live r ‹_›).1
          have : (t.arena.litsL r).length = 2 := by rw [← hr]; rfl
          rw [length_litsL] at this; omega
        · simp at hxy'; obtain ⟨rfl, rfl⟩ := hxy'; exact hxy
      | large r =>
        obtain ⟨hl, _⟩ := h.conflict
        have hl' : t.LiveRef r := by
          unfold LiveRef refsL at *; rw [eA]; exact hl
        refine ⟨hl', fun x hx => ?_⟩
        rw [clauseL_eq_litsL, eA] at hx
        obtain ⟨k, hk, rfl⟩ := mem_litsL_iff.mp hx
        exact hfalse k hk
    · rw [hP.1]; exact invSAt_mono (b3 d hd) (b1.levelOK.framesLe _ (List.getElem_mem _))
  · rename_i hnlt
    have heq : cl = s.level := by
      rw [UInt32.le_iff_toNat_le] at hle; rw [UInt32.lt_iff_toNat_lt] at hnlt
      exact UInt32.toNat_inj.mp (by omega)
    have hP := framesL_last hs (by rw [heq]) hclpos
    refine ⟨hs, heq.symm, h.conflict, fun d hd => ?_, rfl, fun _ => rfl, fun _ _ => rfl, rfl, fun _ => rfl,
      IrrMono.refl _⟩
    rw [hP.1]
    exact invSAt_mono (h.invP d hd) (h.framesLe _ (List.getElem_mem _))

/-- The state after re-ordering the watches of the conflict. -/
structure CMid2 (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) (cl : UInt32) (fl : Lit) (t : Solver) : Prop where
  inv : SInv Φ t
  level : t.level = cl
  conflict : ConflictOK t t c
  invP : ∀ d, t.InDB d → t.InvSAt (t.framesL[cl.toNat - 1]!) d
  size : t.crefSize c = s.crefSize c
  forced : ∃ k, k < s.crefSize c ∧ t.crefLit c k = fl
  flLvl : t.lvl fl = cl.toNat
  bits : ∀ i b, t.abit i b = s.abit i b
  ana : anaSide t = anaSide s
  lvl : ∀ l, t.lvl l = s.lvl l
  mono : IrrMono s t

theorem MoveRel.conflictOK {s t : Solver} {r : Ref} (h : MoveRel s t r) (hc : ConflictOK s s (.large r)) :
    ConflictOK t t (.large r) := by
  obtain ⟨hl, hf⟩ := hc
  refine ⟨(h.live r).mpr hl, fun x hx => ?_⟩
  have := hf x (h.perm.mem_iff.mp hx)
  unfold IsFalse at *; rw [h.asg]; exact this

theorem conflict_move {Φ : (Nat → Bool) → Prop} {s t : Solver} {c : CRef} {cl : UInt32} (M : CMid Φ s c cl t)
    (hcl0 : cl ≠ 0) {fl : Lit} {k0 : Nat} (hk0 : k0 < s.crefSize c) (hfl : fl = s.crefLit c k0)
    (hflL : s.lvl fl = cl.toNat) :
    (s.crefSize c > 2 && (if s.crefSize c > 2 then (t.moveHighest c (s.crefSize c) cl 0).moveHighest c (s.crefSize c) cl 1
      else t).level' ((if s.crefSize c > 2 then (t.moveHighest c (s.crefSize c) cl 0).moveHighest c (s.crefSize c) cl 1
      else t).crefLit c 0) != cl) = true ∨
    CMid2 Φ s c cl fl (if s.crefSize c > 2 then (t.moveHighest c (s.crefSize c) cl 0).moveHighest c (s.crefSize c) cl 1
      else t) := by
  have hclpos : 0 < cl.toNat := by
    have : cl.toNat ≠ 0 := fun e => hcl0 (UInt32.toNat_inj.mp (by simpa using e)); omega
  cases c with
  | binConflict =>
    right
    have hn : ¬ s.crefSize .binConflict > 2 := by simp [crefSize]
    simp only [hn, ite_false]
    exact ⟨M.inv, M.level, M.conflict, M.invP, M.size, ⟨k0, hk0, by rw [M.lits, hfl]⟩, by rw [M.lvl]; exact hflL,
      M.bits, M.ana, M.lvl, M.mono⟩
  | large r =>
    have hlive : t.LiveRef r := M.conflict.1
    have hsz3 : 3 ≤ (t.arena.size r).toNat := (M.inv.ws.live r hlive).1
    have hsize : s.crefSize (.large r) = (t.arena.size r).toNat := by rw [← M.size]; rfl
    have hgt : s.crefSize (.large r) > 2 := by omega
    simp only [hgt, ite_true, decide_true, Bool.true_and]
    rw [hsize]
    have m1 := moveHighest_rel M.inv.ws M.inv.layout hlive cl (i := 0) (by omega)
    have hlive1 : (t.moveHighest (.large r) (t.arena.size r).toNat cl 0).LiveRef r := (m1.live r).mpr hlive
    have hsz1 : ((t.moveHighest (.large r) (t.arena.size r).toNat cl 0).arena.size r).toNat = (t.arena.size r).toNat := by
      rw [m1.write.size r hlive.1]
    have m2 := moveHighest_rel m1.ws m1.layout hlive1 cl (i := 1) (by omega)
    rw [hsz1] at m2
    have mr := m1.trans m2
    generalize ((t.moveHighest (.large r) (t.arena.size r).toNat cl 0).moveHighest (.large r)
      (t.arena.size r).toNat cl 1) = t2 at mr ⊢
    by_cases hchk : t2.level' (t2.crefLit (.large r) 0) = cl
    · right
      have eT : ∀ l, t2.IsTrue l ↔ t.IsTrue l := by intro l; unfold IsTrue; rw [mr.asg]
      have eL : ∀ l, t2.lvl l = t.lvl l := by intro l; unfold lvl; rw [mr.asg]
      have eFr : t2.framesL = t.framesL := by unfold framesL; rw [mr.frameTrail]
      have hinv2 : SInv Φ t2 := by
        apply sinv_extend (s := t) M.inv mr.asg mr.vars mr.level mr.frameTrail mr.propagate (by
          have := mr.ana; simp only [anaSide, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.1) mr.ws mr.layout
          (fun x hx => (mr.live x).mpr hx) ?_ (fun a b h' => (mr.bin a b).mpr h') ?_
        · intro x hx y
          by_cases hxr : x = r
          · subst hxr; exact mr.perm.mem_iff
          · rw [mr.clauseL x hx.1 hxr]
        · intro d hd
          rcases (inDB_iff _ _).mp hd with ⟨x, hx, rfl⟩ | ⟨a, b, hab, rfl⟩
          · have hx' := (mr.live x).mp hx
            by_cases hxr : x = r
            · subst hxr
              right
              exact (M.inv.db _ ((inDB_iff _ _).mpr (Or.inl ⟨x, hx', rfl⟩))).perm (fun y hy => mr.perm.mem_iff.mpr hy)
            · left
              exact (inDB_iff _ _).mpr (Or.inl ⟨x, hx', by rw [← clauseL_eq_litsL, ← clauseL_eq_litsL, mr.clauseL x hx'.1 hxr]⟩)
          · exact Or.inl ((inDB_iff _ _).mpr (Or.inr ⟨a, b, (mr.bin a b).mp hab, rfl⟩))
      have hlevel2 : t2.level = cl := by rw [mr.level, M.level]
      have hflt : t.crefLit (.large r) k0 = fl := by rw [M.lits, hfl]
      have hflmem : fl ∈ t2.clauseL r := by
        have : fl ∈ t.clauseL r := by rw [← hflt]; exact crefLit_mem_large (by rw [M.size]; exact hk0)
        exact mr.perm.mem_iff.mpr this
      refine ⟨hinv2, hlevel2, mr.conflictOK M.conflict, fun d hd => ?_, ?_, ?_, by rw [eL, M.lvl]; exact hflL,
        fun i b => by unfold Solver.abit Solver.abits; rw [mr.asg]; exact M.bits i b, by rw [mr.ana, M.ana],
        fun l => by rw [eL, M.lvl], M.mono.trans mr.irrMono⟩
      · rw [eFr]
        rcases (inDB_iff _ _).mp hd with ⟨x, hx, hdx⟩ | ⟨a, b, hab, hdab⟩
        · have hx' := (mr.live x).mp hx
          by_cases hxr : x = r
          · subst hxr
            -- the new first watch is on the conflict level
            have hw0 : t2.lvl (t2.arena.lit x 0) = cl.toNat := by
              have := congrArg UInt32.toNat hchk; unfold level' at this; unfold lvl; exact this
            have hsz2 : 3 ≤ (t2.arena.size x).toNat := (hinv2.ws.live x hx).1
            have hcl2 : t2.arena.litsL x = t2.arena.lit x 0 :: t2.arena.lit x 1 :: (t2.arena.litsL x).drop 2 := by
              apply List.ext_getElem (by simp [length_litsL]; omega)
              intro j h1 h2
              rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | hj
              · simp [getElem_litsL]
              · simp [getElem_litsL]
              · simp only [List.getElem_cons, List.getElem_drop]
                rw [dif_neg (by omega), dif_neg (by omega)]
                congr 1; omega
            intro w0 w1 rest he k0' k1' hp0 _
            rw [hdx, hcl2] at he
            simp at he; obtain ⟨rfl, _, _⟩ := he
            rw [← eFr] at hp0
            have hfr := framesL_last hinv2 (by rw [hlevel2]) (L := cl.toNat) (by omega)
            rw [hfr.1] at hp0
            exact absurd hp0 (not_propFalse_of_lvl hinv2 (by omega) hw0 (by rw [hlevel2]; exact Nat.le_refl _) (Nat.le_refl _) k0')
          · have hd' : t.InDB d := (inDB_iff _ _).mpr (Or.inl ⟨x, hx', by rw [hdx, ← clauseL_eq_litsL, ← clauseL_eq_litsL,
              mr.clauseL x hx'.1 hxr]⟩)
            exact (invSAt_congr mr.asg mr.frameTrail _ d).mpr (M.invP d hd')
        · have hd' : t.InDB d := (inDB_iff _ _).mpr (Or.inr ⟨a, b, (mr.bin a b).mp hab, hdab⟩)
          exact (invSAt_congr mr.asg mr.frameTrail _ d).mpr (M.invP d hd')
      · show t2.crefSize (.large r) = s.crefSize (.large r)
        rw [← M.size]; show (t2.arena.size r).toNat = (t.arena.size r).toNat; rw [mr.write.size r hlive.1]
      · obtain ⟨k, hk, hkx⟩ := mem_litsL_iff.mp hflmem
        refine ⟨k, ?_, hkx⟩
        rw [hsize, ← mr.write.size r hlive.1]; exact hk
    · left; simpa using hchk

theorem forcedOKFrom_spec (s : Solver) (c : CRef) (size : Nat) (lit : Lit) :
    ∀ i, s.forcedOKFrom c size lit i = true → ∀ k, i ≤ k → k < size → s.crefLit c k = lit ∨ s.IsFalse (s.crefLit c k) := by
  intro i
  fun_induction forcedOKFrom s c size lit i with
  | case1 i hi other ih =>
    intro h k hk1 hk2
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    by_cases e : k = i
    · subst e
      rcases h.1 with h' | h'
      · exact Or.inl h'
      · right; unfold vFalse value at h'; exact beq_iff_eq.mp h'
    · exact ih h.2 k (by omega) hk2
  | case2 i hi => intro _ k hk1 hk2; omega

theorem forcedOK_spec {s : Solver} {c : CRef} {size : Nat} {lit : Lit} (h : s.forcedOK c size lit = true) :
    s.asg.values.get! lit.toNat = 0 ∧ ∀ k, k < size → s.crefLit c k = lit ∨ s.IsFalse (s.crefLit c k) := by
  unfold forcedOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun k hk => forcedOKFrom_spec s c size lit 0 h.2 k (Nat.zero_le _) hk⟩

/-- Assigning `lit` with the binary reason `lit ∨ other`. -/
theorem assignBinary_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {lit other : Lit}
    (hb : s.BinWatched lit other) (hof : s.IsFalse other) (hx : s.ValidLit lit)
    (hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit) :
    SInv Φ (s.assignBinary lit other) ∧
    (∀ P d, P ≤ s.trailL.length → s.InvSAt P d → (s.assignBinary lit other).InvSAt P d) ∧
    (s.assignBinary lit other).propagate = s.propagate ∧
    (∀ d, (s.assignBinary lit other).InDB d ↔ s.InDB d) ∧
    (∀ i b, AnaBit b → (s.assignBinary lit other).abit i b = true → s.abit i b = true) ∧
    anaSide (s.assignBinary lit other) = anaSide s := by
  have hjump : s.options.jumpreasons = 0 := hs.jump
  have hab' : s.assignBinary lit other = s.assign s.probing (s.levelIdx (IDX other)) true lit other := by
    unfold assignBinary; simp [hjump]
  rw [hab']
  have hlvb : (s.levelIdx (IDX other)).toNat = s.lvl other := by unfold levelIdx lvl; rfl
  have hk : (s.levelIdx (IDX other)).toNat ≤ s.level.toNat := by rw [hlvb]; exact isFalse_lvl_le hs hof
  obtain ⟨a1, a2, a3, a4⟩ := assign_sinv hs (probing := s.probing) (bb := true) (rr := other) hx hun hk
    (fun _ => Or.inr (Or.inl ⟨rfl, hb, hof, by rw [hlvb]; exact Nat.le_refl _⟩))
    (fun h0 => by
      apply Implied.unit (hs.db _ ((inDB_iff _ _).mpr (Or.inr ⟨_, _, hb, rfl⟩)))
      intro y hy hne
      simp at hy
      rcases hy with rfl | rfl
      · exact absurd rfl hne
      · have h0' : s.lvl y = 0 := by rw [← hlvb, h0]; rfl
        have ht : s.IsTrue (NOT y) := by
          have := (hs.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hof
        exact hs.roots _ ht (by rw [hs.core.lvlVar]; exact h0'))
  refine ⟨a1, a2, a4, fun d => inDB_congr (by rw [a3.watches]; rfl) (by rw [a3.arena]; rfl) d,
    fun i b hc hbit => assign_abit_le _ _ _ _ _ _ i b hc hbit, assign_anaSide _ _ _ _ _ _⟩

theorem assignBinary_irrMono {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {lit other : Lit}
    (hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit) (hx : s.ValidLit lit) : IrrMono s (s.assignBinary lit other) := by
  have hjump : s.options.jumpreasons = 0 := hs.jump
  have hab' : s.assignBinary lit other = s.assign s.probing (s.levelIdx (IDX other)) true lit other := by
    unfold assignBinary; simp [hjump]
  rw [hab']; exact assign_irrMono hs.core hx hun

theorem oneLiteralOnConflictLevel_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (h : CPre Φ s c) :
    COut Φ s c (s.oneLiteralOnConflictLevel c) := by
  have hs := h.inv
  have hsz := crefSize_pos hs.ws h.conflict
  have hall : ∀ k, k < s.crefSize c → s.level' (s.crefLit c k) ≤ s.level := by
    intro k hk
    have := isFalse_lvl_le hs (ConflictOK.lit_false h.conflict hk)
    rw [UInt32.le_iff_toNat_le]; unfold level'; unfold lvl at this; exact this
  obtain ⟨⟨k0, hk0, hfl, hcl⟩, hmax⟩ := conflictLevelLoop_spec s c (s.crefSize c) h.levelLt hall 0 INVALID_LEVEL
    INVALID_LEVEL 0 INVALID_LIT (Nat.zero_le _) (Or.inl ⟨rfl, rfl⟩) (by omega)
  unfold oneLiteralOnConflictLevel
  dsimp only
  generalize s.conflictLevelLoop c (s.crefSize c) 0 INVALID_LEVEL INVALID_LEVEL 0 INVALID_LIT = R at hfl hcl hmax ⊢
  obtain ⟨jl, cl, on, fl⟩ := R
  dsimp only at hfl hcl hmax ⊢
  -- `cl` as a natural number
  have hclN : cl.toNat = s.lvl fl := by rw [← hcl]; rfl
  have hmaxN : ∀ k, k < s.crefSize c → s.lvl (s.crefLit c k) ≤ cl.toNat := by
    intro k hk; have := UInt32.le_iff_toNat_le.mp (hmax k hk); unfold level' at this; exact this
  split
  · -- root-level conflict
    rename_i h0
    have h0' : cl = 0 := by simpa using h0
    refine Or.inl ⟨rfl, h0', rfl, ?_⟩
    apply unsat_of_root_false hs (h.conflict.implied hs)
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨ConflictOK.lit_false h.conflict hk, ?_⟩
    have := hmaxN k hk; rw [h0'] at this; simp at this; omega
  rename_i h0
  have hcl0 : cl ≠ 0 := by simpa using h0
  have hclpos : 0 < cl.toNat := by
    have : cl.toNat ≠ 0 := fun e => hcl0 (UInt32.toNat_inj.mp (by simpa using e)); omega
  have hle : cl ≤ s.level := by rw [← hcl, hfl]; exact hall k0 hk0
  have M := conflict_mid h hcl0 hle hmaxN
  generalize (if cl < s.level then s.backtrackAfterConflict cl else s) = t at M ⊢
  have MV := conflict_move M hcl0 hk0 hfl (by rw [← hclN])
  generalize (if s.crefSize c > 2 then (t.moveHighest c (s.crefSize c) cl 0).moveHighest c (s.crefSize c) cl 1
      else t) = t2 at MV ⊢
  split
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  rename_i hchk
  rcases MV with hc | M2
  · exact absurd hc hchk
  split
  · -- analysis continues on the conflict level
    refine Or.inr (Or.inr (Or.inr ⟨rfl, hclpos, ⟨M2.inv, M2.level, M2.conflict, M2.invP, ?_, M2.bits, M2.ana,
      M2.mono⟩⟩))
    obtain ⟨k, hk, hkx⟩ := M2.forced
    exact ⟨k, by rw [M2.size]; exact hk, by rw [hkx]; exact M2.flLvl⟩
  -- the forced literal
  obtain ⟨d1, _⟩ := determineNewLevel_spec t2 jl
  generalize t2.determineNewLevel jl = D at d1 ⊢
  obtain ⟨nl, s3⟩ := D
  dsimp only
  split
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  rename_i hge
  have hS3 := d1.same
  have hs3 : SInv Φ s3 := hS3.sinv M2.inv
  have hlev3 : s3.level = cl := by rw [hS3.level, M2.level]
  have hlt : nl < s3.level := by
    have : ¬ s3.level ≤ nl := hge
    rw [UInt32.le_iff_toNat_le] at this; rw [UInt32.lt_iff_toNat_lt]; omega
  have hl03 : s3.level ≠ 0 := by rw [hlev3]; exact hcl0
  have eFr3 : s3.framesL = t2.framesL := by unfold framesL; rw [hS3.frameTrail]
  have hfr := framesL_last hs3 (by rw [hlev3]) hclpos
  have hP3 : ∀ d, s3.InDB d → s3.InvSAt (s3.framesL[cl.toNat - 1]'(by rw [hs3.levelOK.len, hlev3]; omega)) d := by
    intro d hd
    rw [← hfr.1, eFr3, invSAt_congr hS3.asg hS3.frameTrail]
    exact M2.invP d ((hS3.inDB d).mp hd)
  obtain ⟨b1, _, b3, b4, b5, b6, b7, b8, b9, b10, b11, _⟩ := backtrackAfterConflict_spec hs3 hl03 hlt hP3 hfr.2
  have hm4 : IrrMono s (s3.backtrackAfterConflict nl) :=
    (M2.mono.trans (IrrMono.of_eq hS3.asg hS3.arena hS3.watches)).trans
      (IrrMono.of_keep b6 b7 b10 (fun l h1 h2 => b11 l h1 (by rw [h2]; exact Nat.zero_le _)))
  generalize s3.backtrackAfterConflict nl = s4 at b1 b3 b4 b5 b6 b7 b8 b9 b10 hm4 ⊢
  split
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  rename_i hfok
  have hfok' : s4.forcedOK c (s.crefSize c) fl = true := by simpa using hfok
  obtain ⟨f1, f2⟩ := forcedOK_spec hfok'
  have hana4 : anaSide s4 = anaSide s := by rw [b4, d1.ana, M2.ana]
  have hc01 : s4.conflictLit0 = s.conflictLit0 ∧ s4.conflictLit1 = s.conflictLit1 := by
    have := hana4; simp only [anaSide, Prod.mk.injEq] at this
    exact ⟨this.2.2.2.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hc01' : t2.conflictLit0 = s.conflictLit0 ∧ t2.conflictLit1 = s.conflictLit1 := by
    have := M2.ana; simp only [anaSide, Prod.mk.injEq] at this
    exact ⟨this.2.2.2.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hlits4 : ∀ k, s4.crefLit c k = t2.crefLit c k := by
    intro k; cases c with
    | binConflict => simp [crefLit, hc01.1, hc01.2, hc01'.1, hc01'.2]
    | large r => show s4.arena.lit r k = t2.arena.lit r k; rw [b6, hS3.arena]
  have hun : ¬ s4.IsTrue fl ∧ ¬ s4.IsFalse fl := by unfold IsTrue IsFalse; rw [f1]; simp [VAL_TRUE, VAL_FALSE]
  have hsize4 : s4.crefSize c = s.crefSize c := by
    rw [← M2.size]; cases c with
    | binConflict => rfl
    | large r => show (s4.arena.size r).toNat = (t2.arena.size r).toNat; rw [b6, hS3.arena]
  have hdb4 : ∀ d, s4.InDB d ↔ t2.InDB d := fun d => (b5 d).trans (hS3.inDB d)
  have hbits4 : ∀ i b, s4.abit i b = s.abit i b := by
    intro i b; unfold Solver.abit Solver.abits; rw [b9, hS3.asg]; exact M2.bits i b
  -- the result relation for the final assignment
  have fin : ∀ (u : Solver), SInv Φ u → (∀ P d, P ≤ s4.trailL.length → s4.InvSAt P d → u.InvSAt P d) →
      u.propagate = s4.propagate → (∀ d, u.InDB d ↔ s4.InDB d) →
      (∀ i b, AnaBit b → u.abit i b = true → s4.abit i b = true) → anaSide u = anaSide s4 →
      IrrMono s4 u → LOut Φ s u ∧ u.clause = s.clause := by
    intro u hu hinvP hprop hdb hbit hana hmu
    refine ⟨⟨hu, fun d hd => ?_, fun i b hb hub => by rw [← hbits4]; exact hbit i b hb hub, ?_, hm4.trans hmu⟩, ?_⟩
    · unfold InvS; rw [hprop]; exact hinvP _ d b1.levelOK.propLe (b3 d ((hdb d).mp hd))
    · unfold anaRest; rw [hana, hana4]
    · have := hana.trans hana4; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  cases c with
  | binConflict =>
    obtain ⟨hb, _, _⟩ := M2.conflict
    obtain ⟨k, hk, hkx⟩ := M2.forced
    have hk2 : k < 2 := by simpa [crefSize] using hk
    have hbin4 : s4.BinWatched t2.conflictLit0 t2.conflictLit1 := by
      have := (hdb4 [t2.conflictLit0, t2.conflictLit1]).mpr ((inDB_iff _ _).mpr (Or.inr ⟨_, _, hb, rfl⟩))
      rcases (inDB_iff _ _).mp this with ⟨r, hr, hr'⟩ | ⟨x, y, hxy, hxy'⟩
      · exfalso
        have := (b1.ws.live r hr).1
        have : (s4.arena.litsL r).length = 2 := by rw [← hr']; rfl
        rw [length_litsL] at this; omega
      · simp at hxy'; obtain ⟨rfl, rfl⟩ := hxy'; exact hxy
    obtain ⟨_, hv0, hv1, hne⟩ := b1.ws.bin _ _ hbin4
    have hsym := (b1.ws.bin _ _ hbin4).1
    have e0 : s4.conflictLit0 = t2.conflictLit0 := by rw [hc01.1, hc01'.1]
    have e1 : s4.conflictLit1 = t2.conflictLit1 := by rw [hc01.2, hc01'.2]
    -- the forced literal is one of the two, `other` is the other one
    have hcases : (fl = t2.conflictLit0 ∧ s4.conflictLit0 ^^^ s4.conflictLit1 ^^^ fl = t2.conflictLit1) ∨
        (fl = t2.conflictLit1 ∧ s4.conflictLit0 ^^^ s4.conflictLit1 ^^^ fl = t2.conflictLit0) := by
      rw [e0, e1]
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · left; simp [crefLit] at hkx; subst hkx
        refine ⟨rfl, ?_⟩
        rw [UInt32.xor_comm (t2.conflictLit0) (t2.conflictLit1), UInt32.xor_assoc, UInt32.xor_self, UInt32.xor_zero]
      · right; simp [crefLit] at hkx; subst hkx
        refine ⟨rfl, ?_⟩
        rw [UInt32.xor_assoc, UInt32.xor_self, UInt32.xor_zero]
    have hfalse_other : ∀ y, (y = t2.conflictLit0 ∨ y = t2.conflictLit1) → y ≠ fl → s4.IsFalse y := by
      intro y hy hne
      rcases hy with rfl | rfl
      · rcases f2 0 (by simp [crefSize]) with h' | h'
        · simp [crefLit, e0] at h'; exact absurd h' hne
        · simpa [crefLit, e0] using h'
      · rcases f2 1 (by simp [crefSize]) with h' | h'
        · simp [crefLit, e1] at h'; exact absurd h' hne
        · simpa [crefLit, e1] using h'
    right; right; left
    refine ⟨rfl, ?_⟩
    rcases hcases with ⟨hf0, ho⟩ | ⟨hf1, ho⟩
    · dsimp only; rw [ho]
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := assignBinary_spec b1 (by rw [hf0]; exact hbin4)
        (hfalse_other _ (Or.inr rfl) (by rw [hf0]; exact Ne.symm hne)) (by rw [hf0]; exact hv0) hun
      exact fin _ a1 a2 a3 a4 a5 a6 (assignBinary_irrMono b1 hun (by rw [hf0]; exact hv0))
    · dsimp only; rw [ho]
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := assignBinary_spec b1 (by rw [hf1]; exact hsym)
        (hfalse_other _ (Or.inl rfl) (by rw [hf1]; exact hne)) (by rw [hf1]; exact hv1) hun
      exact fin _ a1 a2 a3 a4 a5 a6 (assignBinary_irrMono b1 hun (by rw [hf1]; exact hv1))
  | large r =>
    right; right; left
    refine ⟨rfl, ?_⟩
    dsimp only
    obtain ⟨hl2, _⟩ := M2.conflict
    have hl4 : s4.LiveRef r := by unfold LiveRef refsL at *; rw [b6, hS3.arena]; exact hl2
    obtain ⟨k, hk, hkx⟩ := M2.forced
    have hmem : fl ∈ s4.clauseL r := by
      rw [← hkx, ← hlits4]; exact crefLit_mem_large (by rw [hsize4]; exact hk)
    have hvfl : s4.ValidLit fl := (b1.ws.live r hl4).2.2.2.2.2.2 fl hmem
    obtain ⟨a1, a2, a3, a4, _⟩ := assignReference_spec b1 hl4 hmem hvfl hun (fun y hy hne => by
      obtain ⟨j, hj, rfl⟩ := mem_litsL_iff.mp hy
      rcases f2 j (by rw [← hsize4]; exact hj) with h' | h'
      · exact absurd h' hne
      · exact h')
    exact fin _ a1 a2 a4 (fun d => inDB_congr (by rw [a3.watches]; rfl) (by rw [a3.arena]; rfl) d)
      (fun i b hc hbit => assign_abit_le _ _ _ _ _ _ i b hc hbit) (assign_anaSide _ _ _ _ _ _)
      (assign_irrMono b1.core hvfl hun)

end Solver
end LeanKissat
