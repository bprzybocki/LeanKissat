import LeanKissat.Proofs.LearnAdd
import LeanKissat.Proofs.AnaBits

/-!
# `learnReference`, `learnBinary`, `learnUnit`
-/

namespace LeanKissat
namespace Solver
open Arena

theorem selectJump_spec (s : Solver) (bl : UInt32) (n : Nat) :
    ∀ (i : Nat) (jl : Lit) (lv : UInt32) (q : Nat), 1 ≤ i → jl = s.clause.get! q → 1 ≤ q → q < n →
      (s.selectJump bl i n jl lv q).1 = s.clause.get! (s.selectJump bl i n jl lv q).2.2 ∧
      1 ≤ (s.selectJump bl i n jl lv q).2.2 ∧ (s.selectJump bl i n jl lv q).2.2 < n := by
  intro i jl lv q
  fun_induction selectJump s bl i n jl lv q with
  | case1 i jl lv q hi lit level hge ih => intro _; exact ih (by omega)
  | case2 i jl lv q hi lit level hge heq =>
    intro hi1 _ hq _; exact ⟨rfl, hi1, hi⟩
  | case3 i jl lv q hi lit level hge heq ih =>
    intro hi1 _ hq _; exact ih (by omega) rfl hi1 hi
  | case4 i jl lv q hi => intro _ h1 h2 h3; exact ⟨h1, h2, h3⟩

theorem determineNewLevel_spec (s : Solver) (j : UInt32) :
    Quiet (s.determineNewLevel j).2 s ∧
    ((s.determineNewLevel j).1 = j ∨ (s.determineNewLevel j).1 = s.level - 1) := by
  unfold determineNewLevel
  simp only
  split
  · exact ⟨Quiet.refl _, Or.inl rfl⟩
  · split
    · exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, Or.inr rfl⟩
    · exact ⟨Quiet.refl _, Or.inl rfl⟩

theorem swap_perm (c : U32Vec) (q : Nat) (hq1 : 1 ≤ q) (hq : q < c.size) :
    ((c.set! q (c.get! 1)).set! 1 (c.get! q)).view.Perm c.view := by
  rw [U32Vec.view_set!, U32Vec.view_set!]
  have h1 : c.get! 1 = c.view[1]'(by simp; omega) := by
    rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h2 : c.get! q = c.view[q]'(by simp; omega) := by
    rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl
  rw [h1, h2]
  exact List.set_set_perm (by simp; omega) (by simp; omega)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- Analysis bits are only cleared by an assignment. -/
theorem assign_abit_le (s : Solver) (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32)
    (i : UInt32) (c : UInt8) (hc : AnaBit c) :
    (s.assign probing k bb x rr).abit i c = true → s.abit i c = true := by
  rw [assign_eq]
  have hS : (if k == 0 then s.markFixedLiteral x else s).asg = s.asg := by
    split
    · exact (markFixedLiteral_same s x).asg
    · rfl
  intro h
  have : ((if k == 0 then s.markFixedLiteral x else s).withAssign probing k bb x rr).abit i c = true := h
  unfold withAssign abit abits at this
  unfold abit abits
  rw [← hS]
  generalize (if k == 0 then s.markFixedLiteral x else s) = W at this ⊢
  simp only [Asg.assign] at this
  rw [ByteArray.get!_set!] at this
  split at this
  · exfalso
    have hc' : ∀ v : UInt8, (v = 0 ∨ v = 2) → (v &&& c) = 0 := by
      intro v hv; rcases hv with rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl <;> decide
    have hv : ((bb.toUInt32 &&& (((k == 0).toUInt32 &&& ((rr == UNIT_REASON).toUInt32 ^^^ 1)) ^^^ 1)).toUInt8 <<< 1) = 0 ∨
        ((bb.toUInt32 &&& (((k == 0).toUInt32 &&& ((rr == UNIT_REASON).toUInt32 ^^^ 1)) ^^^ 1)).toUInt8 <<< 1) = 2 := by
      cases bb <;> cases (k == 0) <;> cases (rr == UNIT_REASON) <;> decide
    rw [hc' _ hv] at this; simp at this
  · exact this

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem isFalse_lvl_le {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {y : Lit} (hy : s.IsFalse y) :
    s.lvl y ≤ s.level.toNat := by
  have ht : s.IsTrue (NOT y) := by
    have := (hs.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hy
  have := hs.levelOK.trueLe _ ht
  rwa [hs.core.lvlVar] at this

/-- Assigning the first literal of a live clause whose other literals are false. -/
theorem assignReference_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {lit : Lit} {ref : Ref}
    (hlive : s.LiveRef ref) (hmem : lit ∈ s.clauseL ref) (hx : s.ValidLit lit)
    (hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit) (hoth : ∀ y ∈ s.clauseL ref, y ≠ lit → s.IsFalse y) :
    SInv Φ (s.assignReference lit ref) ∧
    (∀ P c, P ≤ s.trailL.length → s.InvSAt P c → (s.assignReference lit ref).InvSAt P c) ∧
    Same' (s.assignReference lit ref) (s.withAssign s.probing (s.assignmentLevel lit ref) false lit ref) ∧
    (s.assignReference lit ref).propagate = s.propagate ∧
    (s.assignReference lit ref).IsTrue lit := by
  have hcl : ∀ j, j < (s.arena.size ref).toNat → s.arena.lit ref j ∈ s.clauseL ref :=
    fun j hj => lit_mem_litsL _ _ _ hj
  have hlvEq : ∀ y, s.asg.aLevel.get! (IDX y).toNat = UInt32.ofNat (s.lvl y) := by
    intro y; unfold lvl; simp
  have hk : (s.assignmentLevel lit ref).toNat ≤ s.level.toNat := by
    have : s.assignmentLevel lit ref ≤ s.level := by
      apply asgAssignmentLevel_le _ _ _ _ _ _ _ _ UInt32.zero_le
      intro j _ hj hne
      have hf := hoth _ (hcl j hj) hne
      have := isFalse_lvl_le hs hf
      rw [UInt32.le_iff_toNat_le]; unfold lvl at this; exact this
    exact UInt32.le_iff_toNat_le.mp this
  have hge : ∀ y ∈ s.clauseL ref, y ≠ lit → s.lvl y ≤ (s.assignmentLevel lit ref).toNat := by
    intro y hy hne
    obtain ⟨j, hj, rfl⟩ := mem_litsL_iff.mp hy
    have := (le_asgAssignmentLevel s.arena s.asg.aLevel lit ref 0 (s.arena.size ref).toNat 0).2 j (Nat.zero_le _) hj hne
    unfold lvl; exact UInt32.le_iff_toNat_le.mp this
  have hnew : s.assignmentLevel lit ref ≠ 0 → NewReason s (s.assignmentLevel lit ref) false lit ref :=
    fun _ => Or.inr (Or.inr ⟨rfl, hlive, hmem, fun y hy hne => ⟨hoth y hy hne, hge y hy hne⟩⟩)
  have hroot : s.assignmentLevel lit ref = 0 → Implied Φ [lit] := by
    intro h0
    apply Implied.unit (hs.db _ ((inDB_iff _ _).mpr (Or.inl ⟨ref, hlive, rfl⟩)))
    intro y hy hne
    have hf := hoth y hy hne
    have h0' : s.lvl y = 0 := by have := hge y hy hne; rw [h0] at this; simp at this; omega
    have ht : s.IsTrue (NOT y) := by
      have := (hs.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf
    exact hs.roots _ ht (by rw [hs.core.lvlVar]; exact h0')
  obtain ⟨a1, a2, a3, a4⟩ := assign_sinv hs (probing := s.probing) hx hun hk hnew hroot
  refine ⟨a1, a2, a3, a4, ?_⟩
  have ht := (assign_core (probing := s.probing) (level := s.assignmentLevel lit ref) (binary := false)
    (reason := ref) hs.core hx hun).2.1
  have e : (s.assignReference lit ref).asg = (s.withAssign s.probing (s.assignmentLevel lit ref) false lit ref).asg :=
    a3.asg
  unfold IsTrue at *; rw [e]; exact ht

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem SInv.valid_false {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {y : Lit} (hf : s.IsFalse y) :
    s.ValidLit y := by
  have ht : s.IsTrue (NOT y) := by
    have := (hs.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf
  have := hs.rsizes.valid ht
  unfold ValidLit at *; rwa [IDX_NOT] at this

theorem newLargeClause_invalid {s : Solver} (hl : s.arena.Layout) (glue : UInt32) (lits : U32Vec)
    (h : (s.newLargeClause false true glue lits).1 = INVALID_REF) :
    (s.newLargeClause false true glue lits).2.outOfResources = true := by
  generalize hal : s.arena.allocate true glue lits = R at h
  obtain ⟨o, b⟩ := R
  cases o with
  | none => unfold newLargeClause; simp only [hal]
  | some res =>
    exfalso
    unfold newLargeClause at h; simp only [hal] at h
    obtain ⟨_, hr, hle⟩ := Arena.allocate_some hal
    have hN : s.arena.sizeWards < 2 ^ 31 := by
      have := wardsOfClause_pos lits.size
      have hm : MAX_ARENA = 2 ^ 31 := by decide
      rw [hm] at hle; unfold Arena.sizeWards; omega
    have : res.toNat < 2 ^ 31 := by
      rw [hr, UInt32.toNat_ofNat_of_lt' (by have : UInt32.size = 4294967296 := rfl; omega)]; exact hN
    rw [h] at this; simp [INVALID_REF] at this

def anaRest (s : Solver) := (anaSide s).2

/-- Flags that analysis preserves. -/
def Flg (s : Solver) := (s.options, s.inconsistent, s.watching, s.probing, s.importLit, s.importBits, s.vars)

theorem flg_of_anaSide {s t : Solver} (h : anaSide t = anaSide s) : Flg t = Flg s := by
  simp only [anaSide, Prod.mk.injEq] at h
  simp only [Flg, h]

theorem flg_of_anaRest {s t : Solver} (h : anaRest t = anaRest s) : Flg t = Flg s := by
  simp only [anaRest, anaSide, Prod.mk.injEq] at h
  simp only [Flg, h]

theorem AF.flg {s t : Solver} (h : AF t s) : Flg t = Flg s := by
  simp only [Flg, h.options, h.inconsistent, h.watching, h.probing, h.importLit, h.importBits, h.vars]

theorem Flg.inconsistent {s t : Solver} (h : Flg t = Flg s) : t.inconsistent = s.inconsistent := by
  simp only [Flg, Prod.mk.injEq] at h; exact h.2.1
theorem Flg.options {s t : Solver} (h : Flg t = Flg s) : t.options = s.options := by
  simp only [Flg, Prod.mk.injEq] at h; exact h.1
theorem Flg.watching {s t : Solver} (h : Flg t = Flg s) : t.watching = s.watching := by
  simp only [Flg, Prod.mk.injEq] at h; exact h.2.2.1
theorem Flg.probing {s t : Solver} (h : Flg t = Flg s) : t.probing = s.probing := by
  simp only [Flg, Prod.mk.injEq] at h; exact h.2.2.2.1
theorem Flg.importLit {s t : Solver} (h : Flg t = Flg s) : t.importLit = s.importLit := by
  simp only [Flg, Prod.mk.injEq] at h; exact h.2.2.2.2.1
theorem Flg.importBits {s t : Solver} (h : Flg t = Flg s) : t.importBits = s.importBits := by
  simp only [Flg, Prod.mk.injEq] at h; exact h.2.2.2.2.2.1
theorem Flg.vars {s t : Solver} (h : Flg t = Flg s) : t.vars = s.vars := by
  simp only [Flg, Prod.mk.injEq] at h; exact h.2.2.2.2.2.2

theorem markFixedLiteral_anaSide (s : Solver) (lit : Lit) : anaSide (s.markFixedLiteral lit) = anaSide s := by
  have h : ∀ (t : Solver) (idx : UInt32), anaSide (t.deactivateVariable idx) = anaSide t := by
    intro t idx; unfold deactivateVariable; dsimp only; split <;> rfl
  have := h (s.setVarFlag (IDX lit) VarFlags.fixed true) (IDX lit)
  exact this

theorem assign_anaSide (s : Solver) (probing : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) :
    anaSide (s.assign probing k bb x rr) = anaSide s := by
  rw [assign_eq]
  split
  · exact markFixedLiteral_anaSide s x
  · rfl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The facts established by learning. -/
structure LOut (Φ : (Nat → Bool) → Prop) (s t : Solver) : Prop where
  inv : SInv Φ t
  invS : ∀ c, t.InDB c → t.InvS c
  bits : ∀ i c, AnaBit c → t.abit i c = true → s.abit i c = true
  rest : anaRest t = anaRest s
  mono : IrrMono s t

/-- Preconditions of learning the clause in `s.clause`. -/
structure LPre (Φ : (Nat → Bool) → Prop) (s : Solver) (P : Nat) : Prop where
  inv : SInv Φ s
  watching : s.watching = true
  level : s.level ≠ 0
  invP : ∀ c, s.InDB c → s.InvSAt P c
  framesLe : ∀ f ∈ s.framesL, f ≤ P
  implied : Implied Φ s.clause.view
  valid : ∀ y ∈ s.clause.view, s.ValidLit y

theorem LPre.of_same {Φ : (Nat → Bool) → Prop} {s t : Solver} {P : Nat} (h : LPre Φ s P) (hS : Same t s)
    (hw : t.watching = s.watching) (hc : t.clause.view.Perm s.clause.view) : LPre Φ t P := by
  refine ⟨hS.sinv h.inv, by rw [hw]; exact h.watching, by rw [hS.level]; exact h.level, fun c hc' => ?_,
    by rw [show t.framesL = s.framesL by simp [framesL, hS.frameTrail]]; exact h.framesLe,
    h.implied.perm (fun x hx => hc.mem_iff.mpr hx), fun y hy => ?_⟩
  · rw [invSAt_congr hS.asg hS.frameTrail]; exact h.invP c ((hS.inDB c).mp hc')
  · unfold ValidLit; rw [hS.vars]; exact h.valid y (hc.mem_iff.mp hy)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The facts on a learned clause after the checked assertion. -/
structure ClauseOK (Φ : (Nat → Bool) → Prop) (s : Solver) : Prop where
  inv : SInv Φ s
  invS : ∀ c, s.InDB c → s.InvS c
  watching : s.watching = true
  implied : Implied Φ s.clause.view
  valid : ∀ y ∈ s.clause.view, s.ValidLit y
  pos : 0 < s.clause.size
  first : s.asg.values.get! (s.clause.get! 0).toNat = 0
  others : ∀ j, 1 ≤ j → j < s.clause.size → s.IsFalse (s.clause.get! j)
  nodup : s.clause.view.Nodup

theorem ClauseOK.firstUn {Φ : (Nat → Bool) → Prop} {s : Solver} (h : ClauseOK Φ s) :
    ¬ s.IsTrue (s.clause.get! 0) ∧ ¬ s.IsFalse (s.clause.get! 0) := by
  unfold IsTrue IsFalse; rw [h.first]; simp [VAL_TRUE, VAL_FALSE]

theorem ClauseOK.otherFalse {Φ : (Nat → Bool) → Prop} {s : Solver} (h : ClauseOK Φ s) :
    ∀ y ∈ s.clause.view, y ≠ s.clause.get! 0 → s.IsFalse y := by
  intro y hy hne
  obtain ⟨j, hj, rfl⟩ := U32Vec.mem_view_pos _ _ hy
  have : j ≠ 0 := by intro e; subst e; exact hne rfl
  exact h.others j (by omega) hj

/-- The watch invariant holds for a clause whose first literal is unassigned. -/
theorem invSAt_unassigned_first {s : Solver} {P : Nat} {c : List Lit} {x : Lit} (hx : ¬ s.IsFalse x)
    (hc : c.head? = some x) : s.InvSAt P c := by
  intro w0 w1 rest he k0 k1 h0 _
  rw [he] at hc; simp at hc; subst hc
  exact absurd h0.1 hx

def withUsed (t : Solver) (ref : Ref) : Solver := { t with arena := t.arena.setUsed ref MAX_USED }

/-- The tail of `learnReference` after the checked assertion. -/
def largeTail (s : Solver) (notUip : Lit) (glue : UInt32) : Ref × Solver :=
  let (ref, t) := s.newRedundantClause glue
  if ref == INVALID_REF then (ref, t) else (ref, (withUsed t ref).assignReference notUip ref)

theorem learnLargeTail_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : ClauseOK Φ s) (hn : 3 ≤ s.clause.size)
    (glue : UInt32) :
    (s.largeTail (s.clause.get! 0) glue).2.outOfResources = true ∨ LOut Φ s (s.largeTail (s.clause.get! 0) glue).2 := by
  have hnr : s.newRedundantClause glue = s.newLargeClause false true glue s.clause := by
    unfold newRedundantClause newClause
    rw [if_neg (by simp; omega)]
  unfold largeTail
  rw [hnr]
  by_cases hinv : (s.newLargeClause false true glue s.clause).1 = INVALID_REF
  · left
    have := newLargeClause_invalid h.inv.layout glue s.clause hinv
    generalize s.newLargeClause false true glue s.clause = R at hinv this ⊢
    obtain ⟨ref, t⟩ := R
    simp only at hinv this ⊢
    rw [if_pos (by simp [hinv])]; exact this
  right
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := newLargeClause_spec h.inv h.watching glue s.clause hn
    h.nodup h.valid h.implied hinv
  generalize s.newLargeClause false true glue s.clause = R at hinv n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 ⊢
  obtain ⟨ref, t⟩ := R
  simp only at hinv n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 ⊢
  rw [if_neg (by simpa using hinv)]
  simp only
  -- the clause buffer is unchanged
  have hcl : t.clause = s.clause := by have := n6; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  -- `withUsed`
  have hu : AF (withUsed t ref) t := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact setUsed_same n1.layout n2.1 MAX_USED
  have hu1 : SInv Φ (withUsed t ref) := hu.sinv n1
  have huL : (withUsed t ref).LiveRef ref := (hu.liveRef ref).mpr n2
  have huC : (withUsed t ref).clauseL ref = s.clause.view := by rw [hu.clauseL ref n2.1, n3]
  have hfirst := h.firstUn
  have eT : ∀ l, (withUsed t ref).IsTrue l ↔ s.IsTrue l := by
    intro l; unfold IsTrue; rw [show (withUsed t ref).asg = s.asg by rw [← n5]; rfl]
  have eF : ∀ l, (withUsed t ref).IsFalse l ↔ s.IsFalse l := by
    intro l; unfold IsFalse; rw [show (withUsed t ref).asg = s.asg by rw [← n5]; rfl]
  have hmem0 : s.clause.get! 0 ∈ s.clause.view := U32Vec.get!_mem_view _ _ h.pos
  have hval0 : (withUsed t ref).ValidLit (s.clause.get! 0) := by
    unfold ValidLit; rw [show (withUsed t ref).vars = s.vars by rw [← n10]; rfl]; exact h.valid _ hmem0
  have hun0 : ¬ (withUsed t ref).IsTrue (s.clause.get! 0) ∧ ¬ (withUsed t ref).IsFalse (s.clause.get! 0) :=
    ⟨fun h' => hfirst.1 ((eT _).mp h'), fun h' => hfirst.2 ((eF _).mp h')⟩
  obtain ⟨a1, a2, a3, a4, _⟩ := assignReference_spec hu1 huL (by rw [huC]; exact hmem0) hval0 hun0
    (fun y hy hne => (eF y).mpr (h.otherFalse y (by rw [huC] at hy; exact hy) hne))
  refine ⟨a1, ?_, ?_, ?_, (n12.trans hu.irrMono).trans (assign_irrMono hu1.core hval0 hun0)⟩
  · intro c hc
    have hc' : (withUsed t ref).InDB c := by
      have := a3.watches; have := a3.arena
      exact (inDB_congr (by rw [a3.watches]; rfl) (by rw [a3.arena]; rfl) c).mp hc
    unfold InvS; rw [a4]
    apply a2 _ c hu1.levelOK.propLe
    have hc2 : t.InDB c := (hu.inDB c).mp hc'
    rw [hu.invSAt]
    rcases (n4 c).mp hc2 with hold | rfl
    · -- old clauses: the watch invariant at `s.propagate`
      have := h.invS c hold
      unfold InvS at this
      have e := invSAt_congr (t := t) (s := s) n5 n9 s.propagate c
      show t.InvSAt t.propagate c
      rw [n8]
      exact e.mpr this
    · apply invSAt_unassigned_first (x := s.clause.get! 0)
      · intro hf; exact hfirst.2 ((show t.IsFalse _ ↔ s.IsFalse _ by unfold IsFalse; rw [n5]).mp hf)
      · cases hv : s.clause.view with
        | nil => rw [hv] at hmem0; simp at hmem0
        | cons a rest =>
          have : s.clause.get! 0 = a := by
            rw [U32Vec.get!_eq_view, hv]; rfl
          simp [this]
  · intro i c hc hb
    have := assign_abit_le _ _ _ _ _ _ i c hc hb
    have e : (withUsed t ref).abit i c = s.abit i c := by unfold abit abits; rw [show (withUsed t ref).asg = s.asg by rw [← n5]; rfl]
    rw [e] at this; exact this
  · have := assign_anaSide (withUsed t ref) (withUsed t ref).probing ((withUsed t ref).assignmentLevel (s.clause.get! 0) ref)
      false (s.clause.get! 0) ref
    unfold anaRest
    rw [show (withUsed t ref).assignReference (s.clause.get! 0) ref = (withUsed t ref).assign (withUsed t ref).probing
      ((withUsed t ref).assignmentLevel (s.clause.get! 0) ref) false (s.clause.get! 0) ref from rfl, this]
    show (anaSide t).2 = (anaSide s).2
    rw [n6]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem Quiet.lpre {Φ : (Nat → Bool) → Prop} {s t : Solver} {P : Nat} (h : LPre Φ s P) (hq : Quiet t s) :
    LPre Φ t P := by
  have hw : t.watching = s.watching := by
    have := hq.ana; simp only [anaSide, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.1
  exact h.of_same hq.same hw (by rw [hq.clause])

theorem Quiet.abit {s t : Solver} (hq : Quiet t s) (i : UInt32) (c : UInt8) : t.abit i c = s.abit i c := by
  unfold Solver.abit Solver.abits; rw [hq.same.asg]

theorem anaRest_clause (s : Solver) (c : U32Vec) : anaRest ({ s with clause := c } : Solver) = anaRest s := rfl
theorem abit_clause (s : Solver) (c : U32Vec) (i : UInt32) (b : UInt8) :
    ({ s with clause := c } : Solver).abit i b = s.abit i b := rfl

theorem LOut.trans_quiet {Φ : (Nat → Bool) → Prop} {s t u : Solver} (h : LOut Φ t u) (hq : Quiet t s) :
    LOut Φ s u :=
  ⟨h.inv, h.invS, fun i c hc hb => by rw [← hq.abit]; exact h.bits i c hc hb,
   by rw [h.rest]; unfold anaRest; rw [hq.ana], (IrrMono.of_eq hq.same.asg hq.same.arena
     hq.same.watches).trans h.mono⟩

theorem learnReference_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {P : Nat} (h : LPre Φ s P)
    (hn : 3 ≤ s.clause.size) (glue : UInt32) :
    (s.learnReference (s.clause.get! 0) glue).2.overflowed = true ∨
    (s.learnReference (s.clause.get! 0) glue).2.outOfResources = true ∨
    LOut Φ s (s.learnReference (s.clause.get! 0) glue).2 := by
  unfold learnReference
  dsimp only
  obtain ⟨j1, j2, j3⟩ := selectJump_spec s (s.level - 1) s.clause.size 2 (s.clause.get! 1)
    (s.level' (s.clause.get! 1)) 1 (by omega) rfl (Nat.le_refl _) (by omega)
  generalize s.selectJump (s.level - 1) 2 s.clause.size (s.clause.get! 1) (s.level' (s.clause.get! 1)) 1 = J at j1 j2 j3 ⊢
  obtain ⟨jl, jlev, q⟩ := J
  simp only at j1 j2 j3 ⊢
  -- the swapped clause
  have hperm := swap_perm s.clause q j2 j3
  rw [← j1] at hperm
  have hget0 : ((s.clause.set! q (s.clause.get! 1)).set! 1 jl).get! 0 = s.clause.get! 0 := by
    rw [U32Vec.get!_set!_ne _ _ _ _ (by omega), U32Vec.get!_set!_ne _ _ _ _ (by omega)]
  generalize hs1 : ({ s with clause := (s.clause.set! q (s.clause.get! 1)).set! 1 jl } : Solver) = s1 at ⊢
  have hS1 : Same s1 s := by rw [← hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcl1 : s1.clause = (s.clause.set! q (s.clause.get! 1)).set! 1 jl := by rw [← hs1]
  have hp1 : LPre Φ s1 P := h.of_same hS1 (by rw [← hs1]) (by rw [hcl1]; exact hperm)
  have hsz1 : 3 ≤ s1.clause.size := by rw [hcl1]; simpa using hn
  have hrest1 : anaRest s1 = anaRest s := by rw [← hs1]; exact anaRest_clause _ _
  have hbits1 : ∀ i c, s1.abit i c = s.abit i c := by intro i c; rw [← hs1]; exact abit_clause _ _ _ _
  have hnot : s.clause.get! 0 = s1.clause.get! 0 := by rw [hcl1, hget0]
  rw [hnot]
  obtain ⟨d1, d2⟩ := determineNewLevel_spec s1 jlev
  generalize s1.determineNewLevel jlev = D at d1 d2
  obtain ⟨nl, s2⟩ := D
  simp only at d1 d2 ⊢
  have hp2 : LPre Φ s2 P := d1.lpre hp1
  have hcl2 : s2.clause = s1.clause := d1.clause
  have hlev2 : s2.level = s1.level := d1.same.level
  split
  · left; rfl
  rename_i hge
  have hlt : nl < s2.level := by
    have : ¬ s2.level ≤ nl := hge
    rw [UInt32.le_iff_toNat_le] at this; rw [UInt32.lt_iff_toNat_lt]; omega
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -⟩ := backtrackAfterConflict_spec hp2.inv hp2.level hlt hp2.invP hp2.framesLe
  have ok2 := learnedClauseOK_spec (s2.backtrackAfterConflict nl)
  have hm3 : IrrMono s (s2.backtrackAfterConflict nl) :=
    ((IrrMono.of_eq hS1.asg hS1.arena hS1.watches).trans
      (IrrMono.of_eq d1.same.asg d1.same.arena d1.same.watches)).trans
      (IrrMono.of_keep b6 b7 b10 (fun l h1 h2 => b11 l h1 (by rw [h2]; exact Nat.zero_le _)))
  generalize s2.backtrackAfterConflict nl = s3 at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 ok2 hm3 ⊢
  obtain ⟨q1, q2⟩ := ok2
  generalize s3.learnedClauseOK = Q at q1 q2 ⊢
  obtain ⟨ok, s4⟩ := Q
  simp only at q1 q2 ⊢
  split
  · left; rfl
  rename_i hok
  have hok' : ok = true := by simpa using hok
  obtain ⟨c1, c2, c3, c4⟩ := q2 hok'
  have hcl3 : s3.clause = s2.clause := by have := b4; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  have hw3 : s3.watching = s2.watching := by
    have := b4; simp only [anaSide, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.1
  have hcl4 : s4.clause = s3.clause := q1.clause
  have hS4 := q1.same
  have hCOK : ClauseOK Φ s4 := by
    have eF : ∀ l, s4.IsFalse l ↔ s3.IsFalse l := by intro l; unfold IsFalse; rw [hS4.asg]
    refine ⟨hS4.sinv b1, fun c hc => ?_, ?_, ?_, ?_, ?_, ?_, fun j hj1 hj2 => ?_, ?_⟩
    · unfold InvS; rw [invSAt_congr hS4.asg hS4.frameTrail, hS4.propagate]; exact b3 c ((hS4.inDB c).mp hc)
    · have := q1.ana; simp only [anaSide, Prod.mk.injEq] at this; rw [this.2.2.2.2.2.2.2.2.2.2.1, hw3]
      have := d1.ana; simp only [anaSide, Prod.mk.injEq] at this; rw [this.2.2.2.2.2.2.2.2.2.2.1]
      exact hp1.watching
    · rw [hcl4, hcl3, hcl2]; exact hp1.implied
    · intro y hy; rw [hcl4, hcl3, hcl2] at hy; unfold ValidLit; rw [hS4.vars, b8, d1.same.vars]; exact hp1.valid y hy
    · rw [hcl4]; exact c1
    · rw [hcl4, hS4.asg]; exact c2
    · rw [hcl4] at hj2 ⊢; exact (eF _).mpr (c3 j hj1 hj2)
    · rw [hcl4]; exact c4
  have hn4 : 3 ≤ s4.clause.size := by rw [hcl4, hcl3, hcl2]; exact hsz1
  have hnot4 : s1.clause.get! 0 = s4.clause.get! 0 := by rw [hcl4, hcl3, hcl2]
  rw [hnot4]
  have tail := learnLargeTail_spec hCOK hn4 glue
  have heq : ∀ (x : Ref × Solver), x = s4.largeTail (s4.clause.get! 0) glue →
      (x.2.overflowed = true ∨ x.2.outOfResources = true ∨ LOut Φ s x.2) := by
    intro x hx
    subst hx
    rcases tail with h' | h'
    · exact Or.inr (Or.inl h')
    · refine Or.inr (Or.inr ⟨h'.inv, h'.invS, fun i c hc hb => ?_, ?_,
        (hm3.trans (IrrMono.of_eq hS4.asg hS4.arena hS4.watches)).trans h'.mono⟩)
      · have := h'.bits i c hc hb
        rw [q1.abit] at this
        have e3 : s3.abit i c = s2.abit i c := by unfold Solver.abit Solver.abits; rw [b9]
        rw [e3, d1.abit, hbits1] at this; exact this
      · rw [h'.rest]; unfold anaRest; rw [q1.ana, b4, d1.ana]; exact hrest1
  exact heq _ rfl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The result of a learning step. -/
def LRes (Φ : (Nat → Bool) → Prop) (s t : Solver) : Prop :=
  t.overflowed = true ∨ t.outOfResources = true ∨ LOut Φ s t

theorem learnPrefix_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {P : Nat} (h : LPre Φ s P) (j : UInt32)
    (T : Solver → Solver)
    (hT : ∀ s4, ClauseOK Φ s4 → s4.clause = s.clause → anaSide s4 = anaSide s →
      (∀ i c, s4.abit i c = s.abit i c) → LRes Φ s4 (T s4)) :
    LRes Φ s (s.learnPrefix j T) := by
  unfold learnPrefix
  obtain ⟨d1, _⟩ := determineNewLevel_spec s j
  generalize s.determineNewLevel j = D at d1
  obtain ⟨nl, s2⟩ := D
  dsimp only
  have hp2 : LPre Φ s2 P := d1.lpre h
  split
  · left; rfl
  rename_i hge
  have hlt : nl < s2.level := by
    have : ¬ s2.level ≤ nl := hge
    rw [UInt32.le_iff_toNat_le] at this; rw [UInt32.lt_iff_toNat_lt]; omega
  obtain ⟨b1, _, b3, b4, _, b6, b7, b8, b9, b10, b11, -⟩ := backtrackAfterConflict_spec hp2.inv hp2.level hlt hp2.invP hp2.framesLe
  have ok2 := learnedClauseOK_spec (s2.backtrackAfterConflict nl)
  have hm3 : IrrMono s (s2.backtrackAfterConflict nl) :=
    (IrrMono.of_eq d1.same.asg d1.same.arena d1.same.watches).trans
      (IrrMono.of_keep b6 b7 b10 (fun l h1 h2 => b11 l h1 (by rw [h2]; exact Nat.zero_le _)))
  generalize s2.backtrackAfterConflict nl = s3 at b1 b3 b4 b8 b9 ok2 hm3 ⊢
  obtain ⟨q1, q2⟩ := ok2
  generalize s3.learnedClauseOK = Q at q1 q2 ⊢
  obtain ⟨ok, s4⟩ := Q
  dsimp only at q1 q2 ⊢
  split
  · left; rfl
  rename_i hok
  have hok' : ok = true := by simpa using hok
  obtain ⟨c1, c2, c3, c4⟩ := q2 hok'
  have hana4 : anaSide s4 = anaSide s := by rw [q1.ana, b4, d1.ana]
  have hcl4 : s4.clause = s.clause := by have := hana4; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  have hcl3 : s3.clause = s.clause := by rw [← hcl4, q1.clause]
  have hS4 := q1.same
  have hbits : ∀ i c, s4.abit i c = s.abit i c := by
    intro i c; rw [q1.abit]
    have e3 : s3.abit i c = s2.abit i c := by unfold Solver.abit Solver.abits; rw [b9]
    rw [e3, d1.abit]
  have hCOK : ClauseOK Φ s4 := by
    have eF : ∀ l, s4.IsFalse l ↔ s3.IsFalse l := by intro l; unfold IsFalse; rw [hS4.asg]
    have hw : s4.watching = s.watching := by
      have := hana4; simp only [anaSide, Prod.mk.injEq] at this; exact this.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨hS4.sinv b1, fun c hc => ?_, by rw [hw]; exact h.watching, by rw [hcl4]; exact h.implied, ?_, ?_, ?_,
      fun j hj1 hj2 => ?_, ?_⟩
    · unfold InvS; rw [invSAt_congr hS4.asg hS4.frameTrail, hS4.propagate]; exact b3 c ((hS4.inDB c).mp hc)
    · intro y hy; rw [hcl4] at hy; unfold ValidLit; rw [hS4.vars, b8, d1.same.vars]; exact h.valid y hy
    · rw [q1.clause]; exact c1
    · rw [q1.clause, hS4.asg]; exact c2
    · rw [q1.clause] at hj2 ⊢; exact (eF _).mpr (c3 j hj1 hj2)
    · rw [q1.clause]; exact c4
  rcases hT s4 hCOK hcl4 hana4 hbits with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · refine Or.inr (Or.inr ⟨h'.inv, h'.invS, fun i c hc hb => by rw [← hbits]; exact h'.bits i c hc hb, ?_,
      (hm3.trans (IrrMono.of_eq hS4.asg hS4.arena hS4.watches)).trans h'.mono⟩)
    rw [h'.rest]; unfold anaRest; rw [hana4]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem invSAt_unassigned_second {s : Solver} {P : Nat} {a b : Lit} (hb : ¬ s.IsFalse b) :
    s.InvSAt P [a, b] := by
  intro w0 w1 rest he k0 k1 _ h1
  simp at he; obtain ⟨_, rfl, _⟩ := he
  exact absurd h1.1 hb

theorem view_one (c : U32Vec) (h : c.size = 1) : c.view = [c.get! 0] := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp at h1 h2
  subst h2
  rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [h])]; simp

theorem view_two (c : U32Vec) (h : c.size = 2) : c.view = [c.get! 0, c.get! 1] := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp at h1 h2
  rw [U32Vec.get!_eq_view, U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp [h]), List.getElem?_eq_getElem (by simp [h])]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem learnUnitTail_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : ClauseOK Φ s) (hn : s.clause.size = 1) :
    LRes Φ s (learnUnitTail (s.clause.get! 0) s) := by
  right; right
  have hv := view_one _ hn
  have hmem0 : s.clause.get! 0 ∈ s.clause.view := by rw [hv]; simp
  have hfirst := h.firstUn
  obtain ⟨a1, a2, a3, a4⟩ := assign_sinv h.inv (probing := s.probing) (k := 0) (bb := false) (rr := UNIT_REASON)
    (h.valid _ hmem0) hfirst (by simp) (fun h0 => absurd rfl h0) (fun _ => by rw [← hv]; exact h.implied)
  have hq : Quiet (learnUnitTail (s.clause.get! 0) s) (s.assign s.probing 0 false (s.clause.get! 0) UNIT_REASON) := by
    unfold learnUnitTail learnedUnit assignUnit
    dsimp only
    split
    · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    · exact Quiet.refl _
  generalize learnUnitTail (s.clause.get! 0) s = t at hq ⊢
  have hS := hq.same
  refine ⟨hS.sinv a1, fun c hc => ?_, fun i c hc hb => ?_, ?_,
    (assign_irrMono h.inv.core (h.valid _ hmem0) hfirst).trans (IrrMono.of_eq hS.asg hS.arena hS.watches)⟩
  · have hc' := (hS.inDB c).mp hc
    have hc'' : s.InDB c := by
      have e := inDB_congr (t := s.assign s.probing 0 false (s.clause.get! 0) UNIT_REASON) (s := s)
        (by rw [a3.watches]; rfl) (by rw [a3.arena]; rfl) c
      exact e.mp hc'
    unfold InvS; rw [invSAt_congr hS.asg hS.frameTrail, hS.propagate, a4]
    exact a2 _ c h.inv.levelOK.propLe (h.invS c hc'')
  · rw [hq.abit] at hb; exact assign_abit_le _ _ _ _ _ _ i c hc hb
  · unfold anaRest; rw [hq.ana, assign_anaSide]

theorem learnBinaryTail_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (h : ClauseOK Φ s) (hn : s.clause.size = 2) :
    LRes Φ s (learnBinaryTail (s.clause.get! 0) (s.clause.get! 1) s) := by
  right; right
  have hv := view_two _ hn
  generalize ha : s.clause.get! 0 = a at hv
  generalize hb : s.clause.get! 1 = b at hv
  have hfirst := h.firstUn; rw [ha] at hfirst
  have hbF : s.IsFalse b := by rw [← hb]; exact h.others 1 (Nat.le_refl _) (by omega)
  have hab : a ≠ b := by
    have := h.nodup; rw [hv] at this; simpa using this
  have hva : s.ValidLit a := h.valid a (by rw [hv]; simp)
  have hvb : s.ValidLit b := h.valid b (by rw [hv]; simp)
  have himp : Implied Φ [a, b] := by rw [← hv]; exact h.implied
  have hnr : s.newRedundantClause 1 = (INVALID_REF, s.newBinaryClauseAux false true a b) := by
    unfold newRedundantClause newClause; rw [if_pos (by simp [hn])]; rw [ha, hb]
  unfold learnBinaryTail
  rw [hnr]
  dsimp only
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := newBinaryClause_spec h.inv hva hvb hab himp
  generalize s.newBinaryClauseAux false true a b = t at n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 ⊢
  have eF : ∀ l, t.IsFalse l ↔ s.IsFalse l := by intro l; unfold IsFalse; rw [n4]
  have eT : ∀ l, t.IsTrue l ↔ s.IsTrue l := by intro l; unfold IsTrue; rw [n4]
  have eL : ∀ l, t.lvl l = s.lvl l := by intro l; unfold lvl; rw [n4]
  have hjump : t.options.jumpreasons = 0 := n1.jump
  have hab' : t.assignBinary a b = t.assign t.probing (t.levelIdx (IDX b)) true a b := by
    unfold assignBinary; simp [hjump]
  rw [hab']
  have hlvb : (t.levelIdx (IDX b)).toNat = t.lvl b := by unfold levelIdx lvl; rfl
  have hk : (t.levelIdx (IDX b)).toNat ≤ t.level.toNat := by rw [hlvb]; exact isFalse_lvl_le n1 ((eF b).mpr hbF)
  have hvaT : t.ValidLit a := by unfold ValidLit; rw [n9]; exact hva
  have hunT : ¬ t.IsTrue a ∧ ¬ t.IsFalse a := ⟨fun h' => hfirst.1 ((eT a).mp h'), fun h' => hfirst.2 ((eF a).mp h')⟩
  obtain ⟨a1, a2, a3, a4⟩ := assign_sinv n1 (probing := t.probing) (bb := true) (rr := b)
    hvaT hunT hk
    (fun _ => Or.inr (Or.inl ⟨rfl, n3, (eF b).mpr hbF, by rw [hlvb]; exact Nat.le_refl _⟩))
    (fun h0 => by
      apply Implied.unit himp
      intro y hy hne
      simp at hy
      rcases hy with rfl | rfl
      · exact absurd rfl hne
      · have h0' : s.lvl y = 0 := by
          rw [← eL, ← hlvb, h0]; rfl
        have ht : s.IsTrue (NOT y) := by
          have := (h.inv.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hbF
        exact h.inv.roots _ ht (by rw [h.inv.core.lvlVar]; exact h0'))
  refine ⟨a1, fun c hc => ?_, fun i c hc hbit => ?_, ?_, n11.trans (assign_irrMono n1.core hvaT hunT)⟩
  · have hc' : t.InDB c := (inDB_congr (by rw [a3.watches]; rfl) (by rw [a3.arena]; rfl) c).mp hc
    unfold InvS; rw [a4]
    apply a2 _ c n1.levelOK.propLe
    rcases (n2 c).mp hc' with hold | rfl | rfl
    · have := h.invS c hold; unfold InvS at this
      rw [n7]; exact (invSAt_congr n4 n8 _ c).mpr this
    · exact invSAt_unassigned_first (x := a) (fun h' => hfirst.2 ((eF a).mp h')) rfl
    · exact invSAt_unassigned_second (fun h' => hfirst.2 ((eF a).mp h'))
  · have := assign_abit_le _ _ _ _ _ _ i c hc hbit
    have e : t.abit i c = s.abit i c := by unfold Solver.abit Solver.abits; rw [n4]
    rw [e] at this; exact this
  · unfold anaRest; rw [assign_anaSide, n5]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem updateLearned_quiet (s : Solver) (g n : UInt32) : Quiet (s.updateLearned g n) s := by
  unfold updateLearned modifyAverages
  dsimp only
  split <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem learnReference_zero {Φ : (Nat → Bool) → Prop} {s : Solver} {P : Nat} (h : LPre Φ s P)
    (hn : s.clause.size = 0) (notUip : Lit) (glue : UInt32) :
    (s.learnReference notUip glue).2.overflowed = true := by
  unfold learnReference
  dsimp only
  generalize s.selectJump (s.level - 1) 2 s.clause.size (s.clause.get! 1) (s.level' (s.clause.get! 1)) 1 = J
  obtain ⟨jl, jlev, q⟩ := J
  dsimp only
  have hsz : ((s.clause.set! q (s.clause.get! 1)).set! 1 jl).size = 0 := by simp [hn]
  generalize hs1 : ({ s with clause := (s.clause.set! q (s.clause.get! 1)).set! 1 jl } : Solver) = s1 at ⊢
  have hS1 : Same s1 s := by rw [← hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcl1 : s1.clause.size = 0 := by rw [← hs1]; exact hsz
  have hp1 : LPre Φ s1 P := h.of_same hS1 (by rw [← hs1])
    (by rw [show s1.clause.view = [] from List.eq_nil_of_length_eq_zero (by simp [hcl1]),
      show s.clause.view = [] from List.eq_nil_of_length_eq_zero (by simp [hn])])
  obtain ⟨d1, _⟩ := determineNewLevel_spec s1 jlev
  generalize s1.determineNewLevel jlev = D at d1
  obtain ⟨nl, s2⟩ := D
  dsimp only
  split
  · rfl
  rename_i hge
  have hp2 : LPre Φ s2 P := d1.lpre hp1
  have hlt : nl < s2.level := by
    have : ¬ s2.level ≤ nl := hge
    rw [UInt32.le_iff_toNat_le] at this; rw [UInt32.lt_iff_toNat_lt]; omega
  obtain ⟨_, _, _, b4, -⟩ := backtrackAfterConflict_spec hp2.inv hp2.level hlt hp2.invP hp2.framesLe
  have hcl3 : (s2.backtrackAfterConflict nl).clause.size = 0 := by
    have := b4; simp only [anaSide, Prod.mk.injEq] at this; rw [this.1, d1.clause]; exact hcl1
  generalize s2.backtrackAfterConflict nl = s3 at hcl3 ⊢
  have : s3.learnedClauseOK = (false, s3) := by
    unfold learnedClauseOK; simp [hcl3]
  rw [this]
  rfl

/-- Learning the analyzed clause. -/
theorem learnClause_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {P : Nat} (h : LPre Φ s P)
    (hes : s.options.eagersubsume = 0) : LRes Φ s s.learnClause := by
  unfold learnClause
  dsimp only
  have hq : Quiet (if !s.probing then s.updateLearned (UInt32.ofNat s.levels.size) (UInt32.ofNat s.clause.size) else s) s := by
    split
    · exact updateLearned_quiet _ _ _
    · exact Quiet.refl _
  have hcl : (if !s.probing then s.updateLearned (UInt32.ofNat s.levels.size) (UInt32.ofNat s.clause.size) else s).clause = s.clause :=
    hq.clause
  generalize (if !s.probing then s.updateLearned (UInt32.ofNat s.levels.size) (UInt32.ofNat s.clause.size) else s) = s1 at hq hcl ⊢
  have hp1 : LPre Φ s1 P := hq.lpre h
  have hopt : s1.options = s.options := hq.same.options
  rw [← hcl]
  have key : LRes Φ s1 (if s1.clause.size == 1 then (INVALID_REF, s1.learnUnit (s1.clause.get! 0))
      else if s1.clause.size == 2 then (INVALID_REF, s1.learnBinary (s1.clause.get! 0))
      else s1.learnReference (s1.clause.get! 0) (UInt32.ofNat s.levels.size)).2 := by
    split
    · rename_i h1
      have h1' : s1.clause.size = 1 := by simpa using h1
      exact learnPrefix_spec hp1 0 _ (fun s4 hok hc _ _ => by
        have := learnUnitTail_spec hok (by rw [hc]; exact h1')
        rw [hc] at this; exact this)
    · split
      · rename_i _ h2
        have h2' : s1.clause.size = 2 := by simpa using h2
        exact learnPrefix_spec hp1 _ _ (fun s4 hok hc _ _ => by
          have := learnBinaryTail_spec hok (by rw [hc]; exact h2')
          rw [hc] at this; exact this)
      · rename_i h1 h2
        by_cases h0 : s1.clause.size = 0
        · exact Or.inl (learnReference_zero hp1 h0 _ _)
        · exact learnReference_spec hp1 (by simp at h1 h2; omega) _
  generalize (if s1.clause.size == 1 then (INVALID_REF, s1.learnUnit (s1.clause.get! 0))
      else if s1.clause.size == 2 then (INVALID_REF, s1.learnBinary (s1.clause.get! 0))
      else s1.learnReference (s1.clause.get! 0) (UInt32.ofNat s.levels.size)) = R at key ⊢
  obtain ⟨ref, t⟩ := R
  dsimp only at key ⊢
  rw [if_neg (by simp [hes])]
  rcases key with k | k | k
  · exact Or.inl k
  · exact Or.inr (Or.inl k)
  · exact Or.inr (Or.inr (k.trans_quiet hq))

end Solver
end LeanKissat
