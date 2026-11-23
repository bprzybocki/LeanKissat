import LeanKissat.Proofs.SearchTop

/-!
# From the search invariants to models and refutations of the input CNF

Variable `v` of the CNF is internal variable `v` (`ImportOK`): the CNF literal `(v, b)` is the
internal literal `impLit (v, b)`. `PhiF F` is the set of assignments of the internal variables
satisfying `F`.
-/

namespace LeanKissat
namespace Solver
open Std.Sat

/-- The internal literal of a CNF literal (identity import). -/
def impLit (l : Literal Nat) : Lit := if l.2 then LIT (UInt32.ofNat l.1) else NOT (LIT (UInt32.ofNat l.1))

/-- The models of `F` as assignments of the internal variables. -/
def PhiF (F : CNF Nat) (β : Nat → Bool) : Prop :=
  ∀ c ∈ F.clauses.toList, ∃ l ∈ c.literals, litVal β (impLit l) = true

/-- Coverage of the input clauses by the irredundant database (identity import). -/
def CoveredI (s : Solver) (F : CNF Nat) : Prop :=
  ∀ c ∈ F.clauses.toList,
    (∃ v, (v, true) ∈ c.literals ∧ (v, false) ∈ c.literals) ∨
    (∃ l ∈ c.literals, s.RootTrue (impLit l)) ∨
    (∃ d, s.InIrrDB d ∧ ∀ x ∈ d, (∃ l ∈ c.literals, x = impLit l) ∨ s.RootFalse x)

theorem IDX_impLit (l : Literal Nat) (h : l.1 < 2 ^ 31) : (IDX (impLit l)).toNat = l.1 := by
  unfold impLit
  have : (UInt32.ofNat l.1).toNat = l.1 := by simp; omega
  split
  · rw [IDX_LIT_toNat _ (by rw [this]; exact h), this]
  · rw [IDX_NOT, IDX_LIT_toNat _ (by rw [this]; exact h), this]

theorem sign_LIT (x : UInt32) : (LIT x &&& 1 != 0) = false := by
  unfold LIT; simp only [bne_eq_false_iff_eq]; bv_decide

theorem litVal_impLit (β : Nat → Bool) (l : Literal Nat) (h : l.1 < 2 ^ 31) :
    litVal β (impLit l) = (β l.1 == l.2) := by
  have hi := IDX_impLit l h
  unfold litVal; rw [hi]
  unfold impLit
  cases hb : l.2
  · simp only [Bool.false_eq_true, ite_false]; rw [sign_NOT, sign_LIT]; cases β l.1 <;> rfl
  · simp only [ite_true]; rw [sign_LIT]; cases β l.1 <;> rfl

/-- A refutation of `PhiF F` refutes `F`. -/
theorem unsat_of_phiF {F : CNF Nat} (hF : ∀ c ∈ F.clauses.toList, ∀ l ∈ c.literals, l.1 < 2 ^ 31)
    (h : ¬ ∃ β, PhiF F β) : F.Unsat := by
  intro a
  cases he : CNF.eval a F
  · rfl
  · exfalso; apply h
    refine ⟨a, fun c hc => ?_⟩
    have hs : CNF.Sat a F := he
    rw [CNF.sat_iff_all_mem_sat] at hs
    have hcs := hs c (by simpa [CNF.Internal.mem_iff] using hc)
    rw [CNF.Clause.sat_iff_exists_mem_eq] at hcs
    obtain ⟨l, hl, hal⟩ := hcs
    refine ⟨l, hl, ?_⟩
    rw [litVal_impLit a l (hF c hc l hl), hal]; simp

/-- With `unassigned = 0` every variable is assigned. -/
theorem assigned_of_complete {Φ : (Nat → Bool) → Prop} {t : Solver} (hs : SInv Φ t) (hu : t.asg.unassigned = 0)
    {l : Lit} (hv : t.ValidLit l) : t.IsTrue l ∨ t.IsFalse l := by
  have hc := hs.rsizes.2.2.2.1
  rw [hu] at hc; simp only [UInt32.toNat_zero, Nat.zero_add] at hc
  have hall := List.countP_eq_length.mp (by rw [List.length_range]; exact hc)
  have hv' : (IDX l).toNat < t.vars.toNat := hv
  have h2 := hall (IDX l).toNat (List.mem_range.mpr hv')
  simp only [bne_iff_ne, ne_eq] at h2
  have hcore := hs.core
  have hdom := hcore.domain (2 * (IDX l).toNat)
  -- the positive literal of the variable is assigned
  have hpos : t.IsTrue (LIT (IDX l)) ∨ t.IsFalse (LIT (IDX l)) := by
    have e : (LIT (IDX l)).toNat = 2 * (IDX l).toNat := by
      unfold LIT; rw [UInt32.toNat_shiftLeft]; have := hs.ws.varsBound; simp; omega
    unfold IsTrue IsFalse; rw [e]
    rcases hdom with h0 | h0 | h0
    · exact absurd h0 h2
    · exact Or.inl h0
    · exact Or.inr h0
  rcases (IDX_eq_iff l (LIT (IDX l))).mp (by
    rw [show IDX (LIT (IDX l)) = IDX l from UInt32.toNat_inj.mp (IDX_LIT_toNat _ (by
      have := hs.ws.varsBound; omega))]) with e | e
  · rw [e]; exact hpos
  · rw [e]
    rcases hpos with h' | h'
    · right; exact (hcore.valCons _).1.mp h'
    · left; have := (hcore.valCons (NOT (LIT (IDX l)))).1; rw [NOT_NOT] at this; exact this.mpr h'

theorem dbAssigned_of_complete {Φ : (Nat → Bool) → Prop} {t : Solver} (hs : SInv Φ t)
    (hu : t.asg.unassigned = 0) : DBAssigned t := by
  intro c hc l hl
  apply assigned_of_complete hs hu
  rcases (inDB_iff _ c).mp hc with ⟨r, hr, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact (hs.ws.live r hr).2.2.2.2.2.2 l hl
  · obtain ⟨_, ha, hb, _⟩ := hs.ws.bin a b hab
    simp at hl; rcases hl with rfl | rfl
    · exact ha
    · exact hb

theorem dbLen_of_sinv {Φ : (Nat → Bool) → Prop} {t : Solver} (hs : SInv Φ t) : DBLen t := by
  intro c hc
  rcases (inDB_iff _ c).mp hc with ⟨r, hr, rfl⟩ | ⟨a, b, _, rfl⟩
  · have := (hs.ws.live r hr).1; rw [Arena.length_litsL]; omega
  · simp

/-- The reported model agrees with the internal assignment. -/
theorem modelOf_of_true {Φ : (Nat → Bool) → Prop} {t : Solver} (hs : SInv Φ t) (himp : ImportOK t)
    {l : Literal Nat} (hl : l.1 < 2 ^ 31) (ht : t.IsTrue (impLit l)) : modelOf t l.1 = l.2 := by
  have hv := hs.rsizes.valid ht
  have hidx := IDX_impLit l hl
  have hlt : l.1 < t.vars.toNat := by unfold ValidLit at hv; rw [hidx] at hv; exact hv
  obtain ⟨hsz, e1, e2, e3⟩ := himp l.1 hlt
  have hcore := hs.core
  unfold modelOf valueOf
  have hn : ((l.1 : Int) + 1).natAbs = l.1 + 1 := by omega
  rw [hn]
  have c1 : ¬ (l.1 + 1 ≥ t.importLit.size) := by omega
  have c2 : (t.importBits.get! (l.1 + 1) &&& ImportBits.imported == 0) = false := by simpa using e2
  have c3 : (t.importBits.get! (l.1 + 1) &&& ImportBits.eliminated != 0) = false := by simp [e3]
  have hpos : ¬ ((l.1 : Int) + 1 < 0) := by omega
  simp only [c1, c2, c3, e1, hpos, if_false, Bool.false_eq_true]
  unfold impLit at ht
  cases hb : l.2
  · rw [hb] at ht; simp only [Bool.false_eq_true, ite_false] at ht
    have hf : t.IsFalse (LIT (UInt32.ofNat l.1)) := by
      have := (hcore.valCons (NOT (LIT (UInt32.ofNat l.1)))).1.mp ht; rwa [NOT_NOT] at this
    unfold IsFalse at hf
    simp only [value, hf, VAL_FALSE, vFalse]
    simp; omega
  · rw [hb] at ht; simp only [ite_true] at ht
    unfold IsTrue at ht
    simp only [value, ht, VAL_TRUE, vFalse]
    simp

/-- A satisfying end state yields a model of the input. -/
theorem sat_final {F : CNF Nat} {s0 t : Solver} (h : SATState (PhiF F) s0 t) (h0 : SInv (PhiF F) s0)
    (hcov : CoveredI s0 F) (hF : ∀ c ∈ F.clauses.toList, ∀ l ∈ c.literals, l.1 < 2 ^ 31) :
    F.Sat (modelOf t) := by
  rw [CNF.sat_iff_all_mem_sat]
  intro c hcF
  have hc : c ∈ F.clauses.toList := by simpa [CNF.Internal.mem_iff] using hcF
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  have ht := h.inv
  have hcore := ht.core
  -- a true literal of `t` that comes from `c` or is root-false in `s0`
  have fin : ∀ x, t.IsTrue x → ((∃ l ∈ c.literals, x = impLit l) ∨ s0.RootFalse x) →
      ∃ lit ∈ c, modelOf t lit.1 = lit.2 := by
    intro x hx hor
    rcases hor with ⟨l, hl, rfl⟩ | ⟨hf, hl0⟩
    · exact ⟨l, hl, modelOf_of_true ht h.imp (hF c hc l hl) hx⟩
    · exfalso
      have hnt : s0.IsTrue (NOT x) := by
        have := (h0.core.valCons (NOT x)).1; rw [NOT_NOT] at this; exact this.mpr hf
      have hrt : t.RootTrue (NOT x) := h.mono.roots _ ⟨hnt, by rw [h0.core.lvlVar]; exact hl0⟩
      have hfx : t.IsFalse x := by
        have := (hcore.valCons (NOT x)).1.mp hrt.1; rwa [NOT_NOT] at this
      exact (hcore.valCons x).2 ⟨hx, hfx⟩
  rcases hcov c hc with ⟨v, hp, hn⟩ | ⟨l, hl, hrt⟩ | ⟨d, hd, hsub⟩
  · by_cases hm : modelOf t v = true
    · exact ⟨(v, true), hp, hm⟩
    · exact ⟨(v, false), hn, by simpa using hm⟩
  · exact ⟨l, hl, modelOf_of_true ht h.imp (hF c hc l hl) (h.mono.roots _ hrt).1⟩
  · rcases h.mono.irr d hd with ⟨x, hx, hrx⟩ | ⟨d', hd', hsub'⟩
    · exact fin x hrx.1 (hsub x hx)
    · obtain ⟨x, hx, hxt⟩ := db_satisfied hcore.valCons hcore.trueOnTrail hcore.lvlVar h.prop h.invS
        (dbAssigned_of_complete ht h.unassigned) (dbLen_of_sinv ht) (InDB_of_InIrrDB hd')
      exact fin x hxt (hsub x (hsub' x hx))

end Solver
end LeanKissat
