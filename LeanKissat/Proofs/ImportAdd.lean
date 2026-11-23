import LeanKissat.Proofs.Import

/-!
# Clause addition (`kissat_add`)
-/

namespace LeanKissat
namespace Solver
open Std.Sat

theorem natAbs_extLit (l : Literal Nat) : (extLit l).natAbs = l.1 + 1 := by
  unfold extLit; split <;> omega

theorem importLiteral_imported {s : Solver} (hImp : ImportOK s) (ht : s.options.tumble = 0) (l : Literal Nat)
    (hl : l.1 < s.vars.toNat) : s.importLiteral (extLit l) = (impLit l, s) := by
  obtain ⟨hsz, e1, e2, e3⟩ := hImp l.1 hl
  have hn := natAbs_extLit l
  unfold importLiteral
  rw [ite_eq_right (by simp [ht]), hn, ite_eq_left hsz]
  unfold importLiteralAux
  rw [hn]
  dsimp only
  have hA : s.adjustImports (l.1 + 1) = s := by unfold adjustImports; rw [ite_eq_left hsz]
  rw [hA]
  have c1 : (s.importBitsAt (l.1 + 1) &&& ImportBits.eliminated != 0) = false := by
    unfold importBitsAt; simp [e3]
  have c2 : (s.importBitsAt (l.1 + 1) &&& ImportBits.imported == 0) = false := by
    unfold importBitsAt; simpa using e2
  simp only [c1, c2, Bool.false_eq_true, ite_false, e1]
  unfold impLit extLit
  cases l.2 <;> simp; omega

theorem impLit_inj {l l' : Literal Nat} (h1 : l.1 < 2 ^ 31) (h2 : l'.1 < 2 ^ 31) (h : impLit l = impLit l') :
    l = l' := by
  have e1 := IDX_impLit l h1
  have e2 := IDX_impLit l' h2
  rw [h] at e1
  have hv : l.1 = l'.1 := by omega
  have hs : ∀ m : Literal Nat, m.1 < 2 ^ 31 → (impLit m &&& 1 != 0) = !m.2 := by
    intro m hm; unfold impLit; cases m.2
    · simp only [Bool.false_eq_true, ite_false, Bool.not_false]; rw [sign_NOT, sign_LIT]; rfl
    · simp only [ite_true, Bool.not_true]; exact sign_LIT _
  have hb : l.2 = l'.2 := by
    have := hs l h1; rw [h, hs l' h2] at this; cases hl : l.2 <;> cases hl' : l'.2 <;> simp_all
  obtain ⟨a, b⟩ := l; obtain ⟨a', b'⟩ := l'; simp only at hv hb; rw [hv, hb]

theorem NOT_impLit (l : Literal Nat) : NOT (impLit l) = impLit (l.1, !l.2) := by
  unfold impLit; cases l.2 <;> simp [NOT_NOT]

/-- The import invariant between two clauses (consistent, not flagged). -/
structure ImpBase (F : CNF Nat) (s : Solver) : Prop where
  search : SearchInv (PhiF F) s
  level : s.level = 0
  prop : s.propagate = s.trailL.length
  marks : ∀ j, s.marks.get! j = 0
  marksSize : 2 * s.vars.toNat ≤ s.marks.size
  cs : s.clauseSatisfied = false
  ct : s.clauseTrivial = false
  csh : s.clauseShrink = false
  active : ActOK s.flags s.asg.values s.vars.toNat
  tumble : s.options.tumble = 0
  fvars : ∀ c ∈ F.clauses.toList, ∀ l ∈ c.literals, l.1 < s.vars.toNat
  incons : s.inconsistent = false
  flags : ¬ Flagged s

/-- The state while the literals `P` of a clause are added. -/
structure LitPhase (base s : Solver) (P : List (Literal Nat)) : Prop where
  cfr : s = { base with marks := s.marks, clause := s.clause, clauseSatisfied := s.clauseSatisfied, clauseTrivial := s.clauseTrivial, clauseShrink := s.clauseShrink }
  buf : ∀ x ∈ s.clause.view, ∃ l ∈ P, x = impLit l
  nodup : s.clause.view.Nodup
  unas : ∀ x ∈ s.clause.view, ¬ base.IsTrue x ∧ ¬ base.IsFalse x
  m1 : ∀ x ∈ s.clause.view, s.marks.get! x.toNat = 1 ∧ s.marks.get! (NOT x).toNat = 0xFF
  m2 : ∀ j, s.marks.get! j ≠ 0 → ∃ x ∈ s.clause.view, j = x.toNat ∨ j = (NOT x).toNat
  msize : s.marks.size = base.marks.size
  sat : s.clauseSatisfied = true → ∃ l ∈ P, base.RootTrue (impLit l)
  triv : s.clauseTrivial = true → ∃ v, (v, true) ∈ P ∧ (v, false) ∈ P
  cover : ∀ l ∈ P, impLit l ∈ s.clause.view ∨ base.RootFalse (impLit l) ∨ s.clauseSatisfied = true ∨
    s.clauseTrivial = true

theorem LitPhase.init {F : CNF Nat} {base : Solver} (h : ImpBase F base) : LitPhase base base [] := by
  have hc : base.clause.view = [] := by
    apply List.eq_nil_of_length_eq_zero; simp [h.search.clauseEmpty]
  refine ⟨rfl, by rw [hc]; simp, by rw [hc]; simp, by rw [hc]; simp, by rw [hc]; simp,
    fun j hj => absurd (h.marks j) hj, rfl, fun e => by rw [h.cs] at e; simp at e,
    fun e => by rw [h.ct] at e; simp at e, fun l hl => by simp at hl⟩

theorem LitPhase.eqs {base s : Solver} {P : List (Literal Nat)} (h : LitPhase base s P) :
    s.asg = base.asg ∧ s.vars = base.vars ∧ s.importLit = base.importLit ∧ s.importBits = base.importBits ∧
    s.options = base.options ∧ s.level = base.level := by
  have e := h.cfr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [e])

theorem LitPhase.step {F : CNF Nat} {base s : Solver} {P : List (Literal Nat)} (hb : ImpBase F base)
    (h : LitPhase base s P) (hP : ∀ l' ∈ P, l'.1 < 2 ^ 31) (l : Literal Nat) (hl : l.1 < base.vars.toNat) :
    LitPhase base (s.add (extLit l)) (l :: P) := by
  obtain ⟨ea, ev, eil, eib, eo, el⟩ := h.eqs
  have hsmall := hb.search.inv.ws.varsBound
  have hl31 : l.1 < 2 ^ 31 := by omega
  have hne : (extLit l == 0) = false := by unfold extLit; split <;> simp <;> omega
  have hImp : ImportOK s := hb.search.imp.congr eil eib ev
  unfold add
  rw [ite_eq_right (by simp [hne])]
  rw [importLiteral_imported hImp (by rw [eo]; exact hb.tumble) l (by rw [ev]; exact hl)]
  dsimp only
  generalize hx : impLit l = x
  have hxv : base.ValidLit x := by unfold ValidLit; rw [← hx, IDX_impLit l hl31]; exact hl
  have hxlt := validLit_lt hxv
  have hnxlt := validLit_lt (validLit_not hxv)
  have hcore := hb.search.inv.core
  have hmsz : 2 * base.vars.toNat ≤ s.marks.size := by rw [h.msize]; exact hb.marksSize
  have hxx : x ≠ NOT x := by intro e; have := congrArg (· &&& 1) e; simp [NOT] at this; bv_k
  have toN : ∀ a b : Lit, a.toNat = b.toNat → a = b := fun a b e => UInt32.toNat_inj.mp e
  -- the value of `x` and its level
  have hval : s.value x = base.asg.values.get! x.toNat := by unfold value; rw [ea]
  have hlvl0 : (base.asg.values.get! x.toNat ≠ 0) → base.lvl x = 0 := by
    intro hv
    rcases hcore.domain x.toNat with e | e | e
    · exact absurd e hv
    · have := hb.search.inv.levelOK.trueLe x e; rw [hb.level] at this; simp at this; exact this
    · have ht : base.IsTrue (NOT x) := by
        have := (hcore.valCons (NOT x)).1; rw [NOT_NOT] at this; exact this.mpr e
      have := hb.search.inv.levelOK.trueLe _ ht; rw [hb.level, hcore.lvlVar] at this; simp at this; exact this
  have hfix : s.fixedValue x = base.asg.values.get! x.toNat := by
    unfold fixedValue; dsimp only; rw [hval]
    by_cases hv : base.asg.values.get! x.toNat = 0
    · simp [hv]
    · rw [ite_eq_right (by simpa using hv)]
      have h0 := hlvl0 hv
      have : s.level' x = 0 := by unfold level'; rw [ea]; unfold lvl at h0; exact UInt32.toNat_inj.mp (by simpa using h0)
      simp [this]
  have hcfr := h.cfr
  -- flags-only updates
  have upd : ∀ (cs ct csh : Bool), (s.clauseSatisfied = true → cs = true) → (s.clauseTrivial = true → ct = true) →
      (cs = true → ∃ l' ∈ l :: P, base.RootTrue (impLit l')) → (ct = true → ∃ v, (v, true) ∈ l :: P ∧ (v, false) ∈ l :: P) →
      (impLit l ∈ s.clause.view ∨ base.RootFalse (impLit l) ∨ cs = true ∨ ct = true) →
      LitPhase base { s with clauseSatisfied := cs, clauseTrivial := ct, clauseShrink := csh } (l :: P) := by
    intro cs ct csh hcs hct hsat htriv hcov
    refine ⟨by rw [hcfr], fun y hy => ?_, h.nodup, h.unas, h.m1, h.m2, h.msize, hsat, htriv, fun l' hl' => ?_⟩
    · obtain ⟨l'', hl'', e⟩ := h.buf y hy; exact ⟨l'', List.mem_cons_of_mem _ hl'', e⟩
    · rcases List.mem_cons.mp hl' with rfl | hl'
      · exact hcov
      · rcases h.cover l' hl' with e | e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl (hcs e)))
        · exact Or.inr (Or.inr (Or.inr (hct e)))
  by_cases hm0 : (s.mark x == 0) = true
  · rw [ite_eq_left hm0]
    have hm0' : s.marks.get! x.toNat = 0 := by simpa [mark] using hm0
    have hxL : x ∉ s.clause.view := fun hm => by have := (h.m1 x hm).1; rw [hm0'] at this; simp at this
    have hnxL : NOT x ∉ s.clause.view := fun hm => by
      have := (h.m1 _ hm).2; rw [NOT_NOT, hm0'] at this; simp at this
    try dsimp only
    rw [hfix]
    rcases hcore.domain x.toNat with hv | hv | hv
    · -- unassigned: push the literal
      rw [hv]
      simp only [show vTrue 0 = false by rfl, show vFalse 0 = false by rfl, Bool.false_eq_true, ite_false]
      have hT : ¬ base.IsTrue x := by unfold IsTrue; rw [hv]; decide
      have hF : ¬ base.IsFalse x := by unfold IsFalse; rw [hv]; decide
      have hview : (s.clause.push x).view = s.clause.view ++ [x] := U32Vec.view_push _ _
      have hmk : ∀ j, ((s.marks.set! x.toNat 1).set! (NOT x).toNat 0xFF).get! j =
          if j = (NOT x).toNat then 0xFF else if j = x.toNat then 1 else s.marks.get! j := by
        intro j
        rw [ByteArray.get!_set!, ByteArray.get!_set!]
        by_cases e1 : j = (NOT x).toNat
        · simp [e1, show (NOT x).toNat < s.marks.size by omega]
        · simp only [e1, ite_false]
          by_cases e2 : j = x.toNat
          · subst e2; simp [show x.toNat < s.marks.size by omega]; intro e; exact absurd e.symm e1
          · simp [e2, show ¬ (NOT x).toNat = j by omega, show ¬ x.toNat = j by omega]
      refine ⟨by rw [hcfr], fun y hy => ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun j hj => ?_, by simp [h.msize],
        fun e => ?_, fun e => ?_, fun l' hl' => ?_⟩
      · rw [hview] at hy; rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨l'', hl'', e⟩ := h.buf y hy; exact ⟨l'', List.mem_cons_of_mem _ hl'', e⟩
        · simp at hy; exact ⟨l, List.mem_cons_self .., by rw [hy, hx]⟩
      · rw [hview]; exact List.nodup_append.mpr ⟨h.nodup, by simp, fun a ha b hb e => by
          simp at hb; subst hb; subst e; exact hxL ha⟩
      · rw [hview] at hy; rcases List.mem_append.mp hy with hy | hy
        · exact h.unas y hy
        · simp at hy; rw [hy]; exact ⟨hT, hF⟩
      · rw [hview] at hy; rw [hmk, hmk]
        rcases List.mem_append.mp hy with hy | hy
        · have hyx : y ≠ x := fun e => hxL (e ▸ hy)
          have hynx : y ≠ NOT x := fun e => hnxL (e ▸ hy)
          have hnyx : NOT y ≠ x := fun e => hnxL (by rw [← e, NOT_NOT]; exact hy)
          have hnynx : NOT y ≠ NOT x := fun e => hyx (by rw [← NOT_NOT y, e, NOT_NOT])
          rw [ite_eq_right (fun e => hynx (toN _ _ e)), ite_eq_right (fun e => hyx (toN _ _ e)),
            ite_eq_right (fun e => hnynx (toN _ _ e)), ite_eq_right (fun e => hnyx (toN _ _ e))]
          exact h.m1 y hy
        · simp at hy; subst hy
          rw [ite_eq_right (fun e => hxx (toN _ _ e)), ite_eq_left rfl, ite_eq_left rfl]; exact ⟨rfl, rfl⟩
      · rw [hmk] at hj
        rw [hview]
        by_cases e1 : j = (NOT x).toNat
        · exact ⟨x, by simp, Or.inr e1⟩
        · by_cases e2 : j = x.toNat
          · exact ⟨x, by simp, Or.inl e2⟩
          · rw [ite_eq_right e1, ite_eq_right e2] at hj
            obtain ⟨y, hy, hj'⟩ := h.m2 j hj
            exact ⟨y, List.mem_append_left _ hy, hj'⟩
      · obtain ⟨l', hl', hr⟩ := h.sat e; exact ⟨l', List.mem_cons_of_mem _ hl', hr⟩
      · obtain ⟨v, h1, h2⟩ := h.triv e; exact ⟨v, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
      · rw [hview]
        rcases List.mem_cons.mp hl' with rfl | hl'
        · left; rw [hx]; simp
        · rcases h.cover l' hl' with e | e | e | e
          · exact Or.inl (List.mem_append_left _ e)
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr e))
    · -- root-true: satisfied
      rw [hv]
      simp only [show vTrue VAL_TRUE = true by rfl, ite_true]
      have hr : base.RootTrue x := ⟨hv, hlvl0 (by rw [hv]; decide)⟩
      exact upd true s.clauseTrivial s.clauseShrink (fun _ => rfl) id (fun _ => ⟨l, List.mem_cons_self .., by rw [hx]; exact hr⟩)
        (fun e => by obtain ⟨v, h1, h2⟩ := h.triv e; exact ⟨v, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩)
        (Or.inr (Or.inr (Or.inl rfl)))
    · -- root-false: dropped
      rw [hv]
      simp only [show vTrue VAL_FALSE = false by rfl, show vFalse VAL_FALSE = true by rfl, Bool.false_eq_true, ite_false,
        ite_true]
      have hr : base.RootFalse x := ⟨hv, hlvl0 (by rw [hv]; decide)⟩
      exact upd s.clauseSatisfied s.clauseTrivial true id id
        (fun e => by obtain ⟨l', hl', hr'⟩ := h.sat e; exact ⟨l', List.mem_cons_of_mem _ hl', hr'⟩)
        (fun e => by obtain ⟨v, h1, h2⟩ := h.triv e; exact ⟨v, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩)
        (Or.inr (Or.inl (by rw [hx]; exact hr)))
  · rw [ite_eq_right hm0]
    have hm0' : s.marks.get! x.toNat ≠ 0 := by simpa [mark] using hm0
    obtain ⟨y, hy, hj⟩ := h.m2 _ hm0'
    by_cases hmf : vFalse (s.mark x) = true
    · rw [ite_eq_left hmf]
      have hmf' : s.marks.get! x.toNat = 0xFF := by simpa [mark, vFalse] using hmf
      -- `x = NOT y` for a literal `y` of the clause
      have hxy : x = NOT y := by
        rcases hj with e | e
        · have := (h.m1 y hy).1; rw [← toN _ _ e, hmf'] at this; simp at this
        · exact toN _ _ e
      obtain ⟨l', hl', hy'⟩ := h.buf y hy
      have hl'31 : l'.1 < 2 ^ 31 := hP l' hl'
      have hll : l' = (l.1, !l.2) := by
        apply impLit_inj (l' := (l.1, !l.2)) hl'31 hl31
        rw [← hy', ← NOT_impLit, hx, hxy, NOT_NOT]
      exact upd s.clauseSatisfied true s.clauseShrink id (fun _ => rfl)
        (fun e => by obtain ⟨l'', hl'', hr'⟩ := h.sat e; exact ⟨l'', List.mem_cons_of_mem _ hl'', hr'⟩)
        (fun _ => ⟨l.1, by
          cases hb2 : l.2
          · exact List.mem_cons_of_mem _ (by rw [hll, hb2] at hl'; exact hl')
          · exact List.mem_cons.mpr (Or.inl (by rw [← hb2]))
          , by
          cases hb2 : l.2
          · exact List.mem_cons.mpr (Or.inl (by rw [← hb2]))
          · exact List.mem_cons_of_mem _ (by rw [hll, hb2] at hl'; exact hl')⟩)
        (Or.inr (Or.inr (Or.inr rfl)))
    · rw [ite_eq_right hmf]
      have hxy : x = y := by
        rcases hj with e | e
        · exact toN _ _ e
        · exfalso; apply hmf
          have := (h.m1 y hy).2; rw [← toN _ _ e] at this; simp [mark, vFalse, this]
      exact upd s.clauseSatisfied s.clauseTrivial true id id
        (fun e => by obtain ⟨l'', hl'', hr'⟩ := h.sat e; exact ⟨l'', List.mem_cons_of_mem _ hl'', hr'⟩)
        (fun e => by obtain ⟨v, h1, h2⟩ := h.triv e; exact ⟨v, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩)
        (Or.inl (by rw [hx, hxy]; exact hy))

theorem LitPhase.fold {F : CNF Nat} {base : Solver} (hb : ImpBase F base) :
    ∀ (L : List (Literal Nat)) (s : Solver) (P : List (Literal Nat)), LitPhase base s P →
      (∀ l ∈ P, l.1 < 2 ^ 31) → (∀ l ∈ L, l.1 < base.vars.toNat) →
      LitPhase base (L.foldl (fun s l => s.add (extLit l)) s) (L.reverse ++ P) := by
  intro L
  induction L with
  | nil => intro s P h _ _; simpa using h
  | cons l L ih =>
    intro s P h hP hL
    have hsm := hb.search.inv.ws.varsBound
    have h1 := h.step hb hP l (hL l (List.mem_cons_self ..))
    have := ih (s.add (extLit l)) (l :: P) h1 (fun l' hl' => by
      rcases List.mem_cons.mp hl' with rfl | hl'
      · have := hL _ (List.mem_cons_self ..); omega
      · exact hP l' hl') (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))
    simpa using this

theorem bytes_set_zero (M : ByteArray) (i j : Nat) (h : (M.set! i 0).get! j ≠ 0) : j ≠ i ∧ M.get! j ≠ 0 := by
  rw [ByteArray.get!_set!] at h
  by_cases e : i = j
  · subst e
    by_cases hi : i < M.size
    · simp [hi] at h
    · simp [hi] at h; exact absurd (ByteArray.get!_oob M i hi) h
  · simp [e] at h; exact ⟨Ne.symm e, h⟩

theorem clearClauseMarks_zero : ∀ (s : Solver) (i : Nat),
    (∀ j, s.marks.get! j ≠ 0 → ∃ k, i ≤ k ∧ k < s.clause.size ∧
      (j = (s.clause.get! k).toNat ∨ j = (NOT (s.clause.get! k)).toNat)) →
    ∃ M : ByteArray, s.clearClauseMarks i = { s with marks := M } ∧ M.size = s.marks.size ∧ ∀ j, M.get! j = 0 := by
  intro s i
  fun_induction clearClauseMarks s i with
  | case1 s i hi lit ih =>
    intro h
    obtain ⟨M, e1, e2, e3⟩ := ih (fun j hj => by
      simp only at hj
      obtain ⟨n1, hj1⟩ := bytes_set_zero _ _ _ hj
      obtain ⟨n2, hj2⟩ := bytes_set_zero _ _ _ hj1
      obtain ⟨k, k1, k2, k3⟩ := h j hj2
      by_cases ek : k = i
      · subst ek; rcases k3 with e | e
        · exact absurd e n2
        · exact absurd e n1
      · exact ⟨k, by omega, k2, k3⟩)
    exact ⟨M, by rw [e1], by rw [e2]; simp, e3⟩
  | case2 s i hi =>
    intro h
    refine ⟨s.marks, rfl, rfl, fun j => ?_⟩
    exact Classical.byContradiction fun hj => by obtain ⟨k, k1, k2, _⟩ := h j hj; omega

theorem activateLiterals_noop (s : Solver) (L : List Lit) (h : ∀ x ∈ L, s.isActive (IDX x) = true) :
    L.foldl activateLiteral s = s := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx : s.activateLiteral x = s := by
      unfold activateLiteral; dsimp only; rw [ite_eq_left (h x (List.mem_cons_self ..))]
    simp only [List.foldl_cons, hx]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem moveSmallest_unassigned (values : ByteArray) (level : UInt32 → UInt32) (sat : Bool) (lits : U32Vec)
    (off start size : Nat) (h : values.get! (lits.get! (off + start)).toNat = 0) :
    moveSmallestLiteralToFront values level sat lits off start size = (0, lits) := by
  unfold moveSmallestLiteralToFront
  simp [h]

theorem sortLiterals_unassigned (values : ByteArray) (level : UInt32 → UInt32) (lits : U32Vec) (off size : Nat)
    (h0 : values.get! (lits.get! off).toNat = 0) (h1 : values.get! (lits.get! (off + 1)).toNat = 0) :
    sortLiterals values level lits off size = lits := by
  unfold sortLiterals
  rw [moveSmallest_unassigned _ _ _ _ _ _ _ (by simpa using h0)]
  dsimp only
  split
  · rw [moveSmallest_unassigned _ _ _ _ _ _ _ h1]
  · rfl

/-- Coverage of one input clause. -/
def CovC (s : Solver) (c : CNF.Clause Nat) : Prop :=
  (∃ v, (v, true) ∈ c.literals ∧ (v, false) ∈ c.literals) ∨
  (∃ l ∈ c.literals, s.RootTrue (impLit l)) ∨
  (∃ d, s.InIrrDB d ∧ ∀ x ∈ d, (∃ l ∈ c.literals, x = impLit l) ∨ s.RootFalse x)

theorem CovC.mono {s t : Solver} {c : CNF.Clause Nat} (h : CovC s c) (m : IrrMono s t) (hs : s.Core) (ht : t.Core) :
    CovC t c := by
  have rf : ∀ x, s.RootFalse x → t.RootFalse x := by
    intro x ⟨hf, hl⟩
    have hnt : s.IsTrue (NOT x) := by
      have := (hs.valCons (NOT x)).1; rw [NOT_NOT] at this; exact this.mpr hf
    have hr := m.roots _ ⟨hnt, by rw [hs.lvlVar]; exact hl⟩
    refine ⟨?_, by rw [← ht.lvlVar]; exact hr.2⟩
    have := (ht.valCons (NOT x)).1.mp hr.1; rwa [NOT_NOT] at this
  rcases h with h | ⟨l, hl, hr⟩ | ⟨d, hd, hsub⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨l, hl, m.roots _ hr⟩)
  · rcases m.irr d hd with ⟨x, hx, hrx⟩ | ⟨d', hd', hsub'⟩
    · rcases hsub x hx with ⟨l, hl, rfl⟩ | hrf
      · exact Or.inr (Or.inl ⟨l, hl, hrx⟩)
      · exfalso
        have := rf x hrf
        exact (ht.valCons x).2 ⟨hrx.1, this.1⟩
    · refine Or.inr (Or.inr ⟨d', hd', fun x hx => ?_⟩)
      rcases hsub x (hsub' x hx) with e | e
      · exact Or.inl e
      · exact Or.inr (rf x e)

/-- The good outcome of adding one clause, before resetting the clause buffer. -/
structure BodyGood (F : CNF Nat) (base u : Solver) (c : CNF.Clause Nat) : Prop where
  inv : SInv (PhiF F) u
  invS : ∀ d, u.InDB d → u.InvS d
  prop : u.propagate = u.trailL.length
  level : u.level = 0
  clean : ∀ i b, AnaBit b → u.abit i b = false
  flg : Flg u = Flg base
  active : ActOK u.flags u.asg.values u.vars.toNat
  notFlagged : ¬ Flagged u
  mono : IrrMono base u
  cov : CovC u c

/-- The outcome of `addClauseBody`. -/
def BodyOut (F : CNF Nat) (base s u : Solver) (c : CNF.Clause Nat) : Prop :=
  u.clause = s.clause ∧ u.marks = s.marks ∧
  ((u.inconsistent = true ∧ ¬ ∃ β, PhiF F β) ∨ (Flagged u ∧ u.inconsistent = false) ∨ BodyGood F base u c)

theorem LitPhase.same {base s : Solver} {P : List (Literal Nat)} (h : LitPhase base s P) : Same s base := by
  have e := h.cfr
  exact ⟨by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], by rw [e]⟩

theorem LitPhase.flg {base s : Solver} {P : List (Literal Nat)} (h : LitPhase base s P) : Flg s = Flg base := by
  have e := h.cfr; rw [e]; rfl

theorem LitPhase.flags {base s : Solver} {P : List (Literal Nat)} (h : LitPhase base s P) :
    s.flags = base.flags ∧ s.overflowed = base.overflowed ∧ s.outOfResources = base.outOfResources ∧
    s.notPorted = base.notPorted ∧ s.inconsistent = base.inconsistent := by
  have e := h.cfr; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [e])

/-- The base state seen through the literal phase is still good. -/
theorem LitPhase.good {F : CNF Nat} {base s : Solver} {P : List (Literal Nat)} (hb : ImpBase F base)
    (h : LitPhase base s P) (c : CNF.Clause Nat) (hc : CovC s c) : BodyGood F base s c := by
  have hS := h.same
  obtain ⟨ef, eo, eoor, enp, ei⟩ := h.flags
  refine ⟨hS.sinv hb.search.inv, fun d hd => ?_, ?_, by rw [hS.level]; exact hb.level,
    fun i b hb' => by unfold abit abits; rw [hS.asg]; exact hb.search.clean i b hb', h.flg, ?_, ?_,
    IrrMono.of_eq hS.asg hS.arena hS.watches, hc⟩
  · unfold InvS; rw [hS.invSAt, hS.propagate]; exact hb.search.invS d ((hS.inDB d).mp hd)
  · rw [hS.propagate, hb.prop]; simp [trailL, hS.asg]
  · rw [ef, hS.asg, hS.vars]; exact hb.active
  · intro hf; apply hb.flags; unfold Flagged at *; rw [← eo, ← eoor, ← enp]; exact hf

/-- The clause buffer at the end of a clause that is neither satisfied nor trivial. -/
theorem LitPhase.implied {F : CNF Nat} {base s : Solver} {c : CNF.Clause Nat} (hb : ImpBase F base)
    (h : LitPhase base s c.literals.reverse) (hcF : c ∈ F.clauses.toList)
    (hns : s.clauseSatisfied = false ∧ s.clauseTrivial = false) :
    Implied (PhiF F) s.clause.view := by
  intro β hβ
  obtain ⟨l, hl, hv⟩ := hβ c hcF
  rcases h.cover l (List.mem_reverse.mpr hl) with e | ⟨hf, h0⟩ | e | e
  · exact ⟨_, e, hv⟩
  · exfalso
    have hcore := hb.search.inv.core
    have hnt : base.IsTrue (NOT (impLit l)) := by
      have := (hcore.valCons (NOT (impLit l))).1; rw [NOT_NOT] at this; exact this.mpr hf
    obtain ⟨y, hy, hyv⟩ := hb.search.inv.roots _ hnt (by rw [hcore.lvlVar]; exact h0) β hβ
    simp at hy; subst hy
    rw [litVal_NOT] at hyv; rw [hv] at hyv; simp at hyv
  · rw [hns.1] at e; simp at e
  · rw [hns.2] at e; simp at e

theorem markFixedLiteral_marks (s : Solver) (lit : Lit) : (s.markFixedLiteral lit).marks = s.marks :=
  (frame_markFixed s lit).marks

theorem assign_marks (s : Solver) (p : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) :
    (s.assign p k bb x rr).marks = s.marks := by
  rw [assign_eq]; unfold withAssign; split
  · exact markFixedLiteral_marks s x
  · rfl

theorem assign_nf (s : Solver) (p : Bool) (k : UInt32) (bb : Bool) (x : Lit) (rr : UInt32) :
    (s.assign p k bb x rr).overflowed = s.overflowed ∧ (s.assign p k bb x rr).outOfResources = s.outOfResources ∧
    (s.assign p k bb x rr).notPorted = s.notPorted := by
  have := assign_anaSide s p k bb x rr
  simp only [anaSide, Prod.mk.injEq] at this
  exact ⟨this.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Root-level propagation after adding a unit. -/
theorem body_propagate {F : CNF Nat} {base s u : Solver} {c : CNF.Clause Nat} (hu : SInv (PhiF F) u)
    (hinv : ∀ d, u.InDB d → u.InvS d) (hlev : u.level = 0) (hclean : ∀ i b, AnaBit b → u.abit i b = false)
    (hflg : Flg u = Flg base) (hact : ActOK u.flags u.asg.values u.vars.toNat) (hnf : ¬ Flagged u)
    (hmono : IrrMono base u) (hcov : CovC u c) (hcl : u.clause = s.clause) (hmk : u.marks = s.marks) :
    BodyOut F base s u.searchPropagate.1 c := by
  have sp := searchPropagate_spec hu hinv
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := searchPropagate_side hu hinv
  obtain ⟨n1, n2, n3, n4⟩ := searchPropagate_nf hu hinv
  have hib := searchPropagate_importBits hu hinv
  have hsz : 2 * u.vars.toNat ≤ u.asg.values.size := hu.core.sizes.1
  obtain ⟨a1, a2⟩ := searchPropagate_act hu hinv u.vars.toNat hsz hact
  have hcov' : CovC u.searchPropagate.1 c := hcov.mono sp.db.irrMono hu.core sp.inv.core
  generalize hR : u.searchPropagate = R at sp q1 q2 q3 q4 q5 q6 n1 n2 n3 n4 hib a1 a2 hcov'
  obtain ⟨w, res⟩ := R
  simp only at sp q1 q2 q3 q4 q5 q6 n1 n2 n3 n4 hib a1 a2 hcov' ⊢
  refine ⟨by rw [q1, hcl], by rw [n4, hmk], ?_⟩
  cases res with
  | some cr =>
    left
    obtain ⟨g1, -, -, -, g5, -⟩ := sp.some cr rfl
    have hl0 : w.level = 0 := by rw [sp.level, hlev]
    exact ⟨g5 hl0, root_conflict_unsat sp.inv g1 hl0⟩
  | none =>
    right; right
    obtain ⟨p1, p2⟩ := sp.none rfl
    have hflg' : Flg w = Flg u := by
      simp only [Flg, sp.options, q5 rfl, q2, q3, sp.importLit, hib, sp.vars]
    refine ⟨sp.inv, p2, p1, by rw [sp.level, hlev], clean_of_bits q4 hclean, hflg'.trans hflg,
      by rw [sp.vars]; exact a1, ?_, hmono.trans sp.db.irrMono, hcov'⟩
    intro hf; apply hnf; unfold Flagged at *; rw [n1, n2, n3] at hf; exact hf

theorem body_unit {F : CNF Nat} {base s : Solver} {c : CNF.Clause Nat} (hb : ImpBase F base)
    (hcF : c ∈ F.clauses.toList) (h : LitPhase base s c.literals.reverse)
    (hns : s.clauseSatisfied = false ∧ s.clauseTrivial = false) (h1 : s.clause.size = 1) :
    BodyOut F base s (if (s.originalUnit s.clause.back!).level == 0 then (s.originalUnit s.clause.back!).searchPropagate.1
      else s.originalUnit s.clause.back!) c := by
  have hS := h.same
  have hs : SInv (PhiF F) s := hS.sinv hb.search.inv
  have hview : s.clause.view = [s.clause.back!] := by
    apply List.ext_getElem (by simp [h1])
    intro i h1' h2'; simp at h1' h2'; subst h2'
    simp [U32Vec.back!, h1, U32Vec.get!_eq_view]
  generalize hx : s.clause.back! = x at hview ⊢
  have hxm : x ∈ s.clause.view := by rw [hview]; simp
  obtain ⟨hxT, hxF⟩ := h.unas x hxm
  obtain ⟨l, hl, hxl⟩ := h.buf x hxm
  have hlv : l.1 < base.vars.toNat := hb.fvars c hcF l (List.mem_reverse.mp hl)
  have hsm := hb.search.inv.ws.varsBound
  have hxv : base.ValidLit x := by unfold ValidLit; rw [hxl, IDX_impLit l (by omega)]; exact hlv
  have hxv' : s.ValidLit x := by unfold ValidLit; rw [hS.vars]; exact hxv
  have hun : ¬ s.IsTrue x ∧ ¬ s.IsFalse x := by unfold IsTrue IsFalse; rw [hS.asg]; exact ⟨hxT, hxF⟩
  have himp : Implied (PhiF F) [x] := by rw [← hview]; exact h.implied hb hcF hns
  have hu_eq : s.originalUnit x = s.assign s.probing 0 false x UNIT_REASON := rfl
  rw [hu_eq]
  obtain ⟨a1, a2, a3, a4⟩ := assign_sinv hs (probing := s.probing) (k := 0) (bb := false) (rr := UNIT_REASON)
    hxv' hun (by simp) (fun h0 => absurd rfl h0) (fun _ => himp)
  have hlev : (s.assign s.probing 0 false x UNIT_REASON).level = 0 := by rw [a3.level]; show s.level = 0; rw [hS.level, hb.level]
  rw [ite_eq_left (by simp [hlev])]
  have hsinvS : ∀ d, s.InDB d → s.InvS d := fun d hd => by
    unfold InvS; rw [hS.invSAt, hS.propagate]; exact hb.search.invS d ((hS.inDB d).mp hd)
  have hasg : (s.assign s.probing 0 false x UNIT_REASON).asg = s.asg.assign s.probing 0 false x UNIT_REASON := by
    rw [a3.asg]; rfl
  have hfl : (s.assign s.probing 0 false x UNIT_REASON).flags = (if true then s.markFixedLiteral x else s).flags := by
    rw [assign_eq]; simp only [beq_self_eq_true, ite_true]; rfl
  have hsz : 2 * s.vars.toNat ≤ s.asg.values.size := hs.core.sizes.1
  have hactS : ActOK s.flags s.asg.values s.vars.toNat := by
    obtain ⟨ef, -⟩ := h.flags; rw [ef, hS.asg, hS.vars]; exact hb.active
  obtain ⟨nf1, nf2, nf3⟩ := assign_nf s s.probing 0 false x UNIT_REASON
  obtain ⟨-, eo, eoor, enp, -⟩ := h.flags
  have hTx : (s.assign s.probing 0 false x UNIT_REASON).IsTrue x := by
    unfold IsTrue; rw [hasg]; exact (assign_isTrue (s := s) (probing := s.probing) (level := 0) (binary := false)
      (reason := UNIT_REASON) hs.core.sizes hxv' x).mpr (Or.inl rfl)
  have hLx : (s.assign s.probing 0 false x UNIT_REASON).lvl x = 0 := by
    have := assign_lvl (s := s) (probing := s.probing) (level := 0) (binary := false) (reason := UNIT_REASON)
      hs.core.sizes hxv' x
    rw [ite_eq_left rfl] at this
    show ((s.assign s.probing 0 false x UNIT_REASON).asg.aLevel.get! (IDX x).toNat).toNat = 0
    rw [hasg]; exact this
  apply body_propagate a1
  · intro d hd
    have hd' : s.InDB d := (inDB_congr (by rw [a3.watches]; rfl) (by rw [a3.arena]; rfl) d).mp hd
    unfold InvS; rw [a4]; exact a2 _ d hs.levelOK.propLe (hsinvS d hd')
  · exact hlev
  · intro i b hb'
    have := clean_of_bits (s := s) (t := s.assign s.probing 0 false x UNIT_REASON)
      (by rw [hasg]; exact assign_bitsShrink _ _ _ _ _ _)
      (fun i b hb' => by unfold abit abits; rw [hS.asg]; exact hb.search.clean i b hb')
    exact this i b hb'
  · exact (flg_of_anaSide (assign_anaSide _ _ _ _ _ _)).trans h.flg
  · rw [hfl, hasg, show (s.assign s.probing 0 false x UNIT_REASON).vars = s.vars from a3.vars]
    exact actOK_assign s s.asg s.vars.toNat hsz hactS _ _ _ _ _ true
  · intro hf; apply hb.flags; unfold Flagged at *; rw [nf1, nf2, nf3, eo, eoor, enp] at hf; exact hf
  · exact (IrrMono.of_eq hS.asg hS.arena hS.watches).trans (assign_irrMono hs.core hxv' hun)
  · exact Or.inr (Or.inl ⟨l, List.mem_reverse.mp hl, by rw [← hxl]; exact ⟨hTx, hLx⟩⟩)
  · have := assign_anaSide s s.probing 0 false x UNIT_REASON
    simp only [anaSide, Prod.mk.injEq] at this; exact this.1
  · exact assign_marks _ _ _ _ _ _

theorem markAddedLiteral_act (t : Solver) (lit : Lit) (n : Nat) (h : ActOK t.flags t.asg.values n) :
    ActOK (t.markAddedLiteral lit).flags (t.markAddedLiteral lit).asg.values n := by
  intro v hv
  have hf : (t.markAddedLiteral lit).flags = (markAddedFlags t.flags t.stats lit).1 := rfl
  rw [hf, show (t.markAddedLiteral lit).asg = t.asg from rfl]
  obtain ⟨a1, a2⟩ := markAddedFlags_get t.flags t.stats lit v
  rcases a1 with e | e
  · rw [e]; exact h v hv
  · subst e
    rcases h _ hv with h' | h'
    · exact Or.inl (a2 h')
    · exact Or.inr h'

theorem markAddedLiterals_act (L : List Lit) : ∀ (t : Solver) (n : Nat), ActOK t.flags t.asg.values n →
    ActOK (L.foldl markAddedLiteral t).flags (L.foldl markAddedLiteral t).asg.values n := by
  induction L with
  | nil => intro t n h; exact h
  | cons x xs ih => intro t n h; exact ih _ n (markAddedLiteral_act t x n h)

theorem newOriginalClause_eq (s : Solver) (h0 : s.asg.values.get! (s.clause.get! 0).toNat = 0)
    (h1 : s.asg.values.get! (s.clause.get! 1).toNat = 0) :
    s.newOriginalClause = s.newClause true false 0 s.clause := by
  unfold newOriginalClause
  dsimp only
  rw [sortLiterals_unassigned _ _ _ _ _ h0 (by simpa using h1)]

theorem newBinary_quiet (s : Solver) (o : Bool) (a b : Lit) :
    Quiet (s.newBinaryClauseAux o true a b) (s.watchBinary a b) := by
  unfold newBinaryClauseAux
  simp only [ite_true]
  exact (incClause_quiet _ _ _ _).trans ((markAddedLiteral_quiet _ _).trans (markAddedLiteral_quiet _ _))

theorem markAddedLiteral_marks (t : Solver) (lit : Lit) : (t.markAddedLiteral lit).marks = t.marks := rfl
theorem incClause_marks (t : Solver) (o r b : Bool) : (t.incClause o r b).marks = t.marks := rfl
theorem incClause_flags (t : Solver) (o r b : Bool) : (t.incClause o r b).flags = t.flags := rfl
theorem watchBinary_marks (t : Solver) (a b : Lit) : (t.watchBinary a b).marks = t.marks := rfl

theorem newBinary_marks (s : Solver) (o : Bool) (a b : Lit) : (s.newBinaryClauseAux o true a b).marks = s.marks := by
  unfold newBinaryClauseAux; simp only [ite_true]
  rw [incClause_marks, markAddedLiteral_marks, markAddedLiteral_marks, watchBinary_marks]

theorem newBinary_flags (s : Solver) (o : Bool) (a b : Lit) :
    (s.newBinaryClauseAux o true a b).flags = (((s.watchBinary a b).markAddedLiteral a).markAddedLiteral b).flags := by
  unfold newBinaryClauseAux; simp only [ite_true]; rw [incClause_flags]

theorem Quiet.symm' {t s : Solver} (h : Quiet t s) : Quiet s t :=
  ⟨⟨h.same.asg.symm, h.same.arena.symm, h.same.watches.symm, h.same.delayed.symm, h.same.vars.symm,
    h.same.level.symm, h.same.frameTrail.symm, h.same.propagate.symm, h.same.options.symm⟩, h.ana.symm⟩

theorem assigned_of_var {s : Solver} (hc : s.Core) (x : Lit) (h : s.asg.values.get! (2 * (IDX x).toNat) ≠ 0) :
    s.IsTrue x ∨ s.IsFalse x := by
  have key : IDX x * 2 = x ∨ IDX x * 2 = NOT x := by unfold IDX NOT; bv_k
  have hm : (IDX x * 2).toNat = 2 * (IDX x).toNat := by
    rw [UInt32.toNat_mul]; have := IDX_toNat x; have := x.toNat_lt; simp; omega
  rw [← hm] at h
  rcases key with e | e
  · rw [e] at h
    rcases hc.domain x.toNat with d | d | d
    · exact absurd d h
    · exact Or.inl d
    · exact Or.inr d
  · rw [e] at h
    rcases hc.domain (NOT x).toNat with d | d | d
    · exact absurd d h
    · right; have := (hc.valCons (NOT x)).1; rw [NOT_NOT] at this; exact this.mp d
    · left; exact (hc.valCons x).1.mpr d

/-- The assignment logic after adding a clause with two unassigned watches does nothing. -/
theorem addTail_unassigned (t : Solver) (isize : Nat) (res : Ref) (h0 : t.value (t.clause.get! 0) = 0)
    (h1 : t.value (t.clause.get! 1) = 0) : t.addTail isize res = t := by
  unfold addTail
  simp only [h0, h1]
  rfl

theorem newLargeClause_act (s : Solver) (o red : Bool) (g : UInt32) (lits : U32Vec) (n : Nat) (hw : s.watching = true)
    (h : ActOK s.flags s.asg.values n) :
    ActOK (s.newLargeClause o red g lits).2.flags (s.newLargeClause o red g lits).2.asg.values n := by
  unfold newLargeClause
  dsimp only
  split
  · exact h
  · dsimp only
    rw [hw]; simp only [ite_true]
    split
    · split <;> exact h
    · unfold markAddedLiterals
      rw [← Array.foldl_toList]
      exact markAddedLiterals_act _ _ n h

theorem addClauseBody_spec {F : CNF Nat} {base s : Solver} {c : CNF.Clause Nat} (hb : ImpBase F base)
    (hcF : c ∈ F.clauses.toList) (h : LitPhase base s c.literals.reverse) :
    BodyOut F base s s.addClauseBody c := by
  have hS := h.same
  obtain ⟨ef, eo, eoor, enp, ei⟩ := h.flags
  unfold addClauseBody
  rw [ite_eq_right (by rw [ei, hb.incons]; simp)]
  rw [ite_eq_right (by intro hf; apply hb.flags; unfold Flagged; rw [← eo, ← eoor, ← enp]; simpa [or_assoc] using hf)]
  by_cases hsat : s.clauseSatisfied = true
  · rw [ite_eq_left hsat]
    obtain ⟨l, hl, hr⟩ := h.sat hsat
    refine ⟨rfl, rfl, Or.inr (Or.inr (h.good hb c (Or.inr (Or.inl ⟨l, List.mem_reverse.mp hl, ?_⟩))))⟩
    unfold RootTrue IsTrue lvl at *; rw [hS.asg]; exact hr
  rw [ite_eq_right hsat]
  by_cases htr : s.clauseTrivial = true
  · rw [ite_eq_left htr]
    obtain ⟨v, h1, h2⟩ := h.triv htr
    exact ⟨rfl, rfl, Or.inr (Or.inr (h.good hb c (Or.inl ⟨v, List.mem_reverse.mp h1, List.mem_reverse.mp h2⟩)))⟩
  rw [ite_eq_right htr]
  have hns : s.clauseSatisfied = false ∧ s.clauseTrivial = false := by simp_all
  have hcore := hb.search.inv.core
  have hsm := hb.search.inv.ws.varsBound
  -- buffer literals are active
  have hact : ∀ x ∈ s.clause.toArray.toList, s.isActive (IDX x) = true := by
    intro x hx
    have hxv : x ∈ s.clause.view := by
      have e : s.clause.toArray.toList = s.clause.view := by simp [U32Vec.toArray, U32Vec.view]
      rw [← e]; exact hx
    obtain ⟨hT, hF⟩ := h.unas x hxv
    obtain ⟨l, hl, hxl⟩ := h.buf x hxv
    have hlv : l.1 < base.vars.toNat := hb.fvars c hcF l (List.mem_reverse.mp hl)
    have hidx : (IDX x).toNat < base.vars.toNat := by rw [hxl, IDX_impLit l (by omega)]; exact hlv
    rcases hb.active _ hidx with e | e
    · unfold isActive varFlags; rw [ef]; exact e
    · exfalso; rcases assigned_of_var hcore x e with e' | e'
      · exact hT e'
      · exact hF e'
  unfold activateLiterals
  rw [← Array.foldl_toList, activateLiterals_noop s _ hact]
  dsimp only
  have himp := h.implied hb hcF hns
  by_cases h0 : s.clause.size = 0
  · rw [ite_eq_left (by simp [h0])]
    refine ⟨rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
    rintro ⟨β, hβ⟩
    have hv : s.clause.view = [] := by apply List.eq_nil_of_length_eq_zero; simp [h0]
    obtain ⟨x, hx, _⟩ := himp β hβ
    rw [hv] at hx; simp at hx
  rw [ite_eq_right (by simpa using h0)]
  by_cases h1 : s.clause.size = 1
  · rw [ite_eq_left (by simp [h1])]
    exact body_unit hb hcF h hns h1
  rw [ite_eq_right (by simpa using h1)]
  have h2 : 2 ≤ s.clause.size := by omega
  -- the clause literals: valid, unassigned, distinct
  have hmem : ∀ i, i < s.clause.size → s.clause.get! i ∈ s.clause.view := fun i hi => U32Vec.get!_mem_view _ _ hi
  have hval : ∀ x ∈ s.clause.view, s.ValidLit x := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := h.buf x hx
    have hlv : l.1 < base.vars.toNat := hb.fvars c hcF l (List.mem_reverse.mp hl)
    unfold ValidLit; rw [hS.vars, hxl, IDX_impLit l (by omega)]; exact hlv
  have hun : ∀ x ∈ s.clause.view, s.asg.values.get! x.toNat = 0 := by
    intro x hx
    obtain ⟨hT, hF⟩ := h.unas x hx
    rw [hS.asg]
    rcases hcore.domain x.toNat with d | d | d
    · exact d
    · exact absurd d hT
    · exact absurd d hF
  have hs : SInv (PhiF F) s := hS.sinv hb.search.inv
  have hsinvS : ∀ d, s.InDB d → s.InvS d := fun d hd => by
    unfold InvS; rw [hS.invSAt, hS.propagate]; exact hb.search.invS d ((hS.inDB d).mp hd)
  have hnotF : ∀ x ∈ s.clause.view, ¬ s.IsFalse x := fun x hx => by unfold IsFalse; rw [hun x hx]; decide
  have hactS : ActOK s.flags s.asg.values s.vars.toNat := by rw [ef, hS.asg, hS.vars]; exact hb.active
  have hcovL : ∀ x ∈ s.clause.view, (∃ l ∈ c.literals, x = impLit l) ∨ False := by
    intro x hx; obtain ⟨l, hl, e⟩ := h.buf x hx; exact Or.inl ⟨l, List.mem_reverse.mp hl, e⟩
  rw [newOriginalClause_eq s (hun _ (hmem 0 (by omega))) (hun _ (hmem 1 (by omega)))]
  unfold newClause
  have hw : s.watching = true := by rw [Flg.watching h.flg]; exact hb.search.watching
  have hmono0 : IrrMono base s := IrrMono.of_eq hS.asg hS.arena hS.watches
  have hfl0 : Flg s = Flg base := h.flg
  by_cases hb2 : s.clause.size = 2
  · simp only [hb2, beq_self_eq_true, ite_true]
    have hv2 := view_two s.clause hb2
    generalize ha : s.clause.get! 0 = a at hv2 ⊢
    generalize hbb : s.clause.get! 1 = b at hv2 ⊢
    have hva : s.ValidLit a := hval a (by rw [hv2]; simp)
    have hvb : s.ValidLit b := hval b (by rw [hv2]; simp)
    have hab : a ≠ b := by have := h.nodup; rw [hv2] at this; simpa using this
    have himp2 : Implied (PhiF F) [a, b] := by rw [← hv2]; exact himp
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := newBinaryClause_spec hs hva hvb hab himp2
    have hq : Quiet (s.newBinaryClauseAux true true a b) (s.newBinaryClauseAux false true a b) :=
      (newBinary_quiet s true a b).trans (newBinary_quiet s false a b).symm'
    have hmk := newBinary_marks s true a b
    generalize s.newBinaryClauseAux false true a b = t0 at n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 hq
    have hfl := newBinary_flags s true a b
    generalize hT : s.newBinaryClauseAux true true a b = t at hq hmk hfl ⊢
    have hTS := hq.same
    have hcl : t.clause = s.clause := by
      have := hq.ana.trans n5; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
    have hta : t.asg = s.asg := hTS.asg.trans n4
    have hu0 : t.value (t.clause.get! 0) = 0 := by unfold value; rw [hta, hcl, ha]; exact hun a (by rw [hv2]; simp)
    have hu1 : t.value (t.clause.get! 1) = 0 := by unfold value; rw [hta, hcl, hbb]; exact hun b (by rw [hv2]; simp)
    rw [addTail_unassigned t _ _ hu0 hu1]
    refine ⟨hcl, hmk, Or.inr (Or.inr ⟨hTS.sinv n1, fun d hd => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
    · have hd0 := (hTS.inDB d).mp hd
      unfold InvS; rw [invSAt_congr hta (hTS.frameTrail.trans n8), hTS.propagate, n7]
      rcases (n2 d).mp hd0 with hold | rfl | rfl
      · exact hsinvS d hold
      · exact invSAt_unassigned_first (x := a) (hnotF a (by rw [hv2]; simp)) rfl
      · exact invSAt_unassigned_first (x := b) (hnotF b (by rw [hv2]; simp)) rfl
    · rw [hTS.propagate, n7, hS.propagate, hb.prop]; simp [trailL, hta, hS.asg]
    · rw [hTS.level, n6, hS.level, hb.level]
    · intro i bb hbb'; unfold abit abits; rw [hta, hS.asg]; exact hb.search.clean i bb hbb'
    · exact ((flg_of_anaSide hq.ana).trans (flg_of_anaSide n5)).trans hfl0
    · rw [hfl, hta, show t.vars = s.vars from hTS.vars.trans n9]
      exact markAddedLiteral_act _ _ _ (markAddedLiteral_act _ _ _ hactS)
    · intro hf; apply hb.flags
      have e := hq.ana.trans n5; simp only [anaSide, Prod.mk.injEq] at e
      unfold Flagged at *
      rw [e.2.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, eo, eoor, enp] at hf
      exact hf
    · exact (hmono0.trans n11).trans (IrrMono.of_eq hTS.asg hTS.arena hTS.watches)
    · refine Or.inr (Or.inr ⟨[a, b], Or.inr ⟨a, b, ?_, rfl⟩, fun x hx => ?_⟩)
      · unfold BinWatched entries watchesOf at *; rw [hTS.watches]; exact n3
      · exact Or.inl (by rcases hcovL x (by rw [hv2]; exact hx) with e | e; exact e; exact absurd e id)
  · simp only [show (s.clause.size == 2) = false by simpa using hb2, Bool.false_eq_true, ite_false]
    have h3 : 3 ≤ s.clause.size := by omega
    have hact' := newLargeClause_act s true false 0 s.clause s.vars.toNat hw hactS
    generalize hal : s.arena.allocate false 0 s.clause = A
    obtain ⟨o, ab⟩ := A
    cases o with
    | none =>
      have e : s.newLargeClause true false 0 s.clause = (INVALID_REF, { s with arena := ab, outOfResources := true }) := by
        unfold newLargeClause; simp only [hal]
      rw [e]
      dsimp only
      rw [addTail_unassigned _ _ _ (by unfold value; exact hun _ (hmem 0 (by omega)))
        (by unfold value; exact hun _ (hmem 1 (by omega)))]
      exact ⟨rfl, rfl, Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by rw [ei, hb.incons]⟩)⟩
    | some res =>
      have hres : (s.newLargeClause true false 0 s.clause).1 = res := by
        rw [newLargeClause_eqG s true false 0 s.clause ab res hal hw]
      have hok : (s.newLargeClause true false 0 s.clause).1 ≠ INVALID_REF := by
        rw [hres]
        have hA := Arena.allocate_alloc hs.layout hal
        intro e
        have href := hA.ref
        have hbd := hs.layout.bound
        rw [e] at href; unfold INVALID_REF at href; simp at href; omega
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ :=
        newLargeClause_specG hs hw true false 0 s.clause h3 h.nodup hval himp hok
      rw [hres] at g2 g3 g4
      generalize s.newLargeClause true false 0 s.clause = R at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 hact' hres ⊢
      obtain ⟨r, t⟩ := R
      simp only at hres g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 hact' ⊢
      subst hres
      have hcl : t.clause = s.clause := by have := g7; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
      have hu0 : t.value (t.clause.get! 0) = 0 := by unfold value; rw [g6, hcl]; exact hun _ (hmem 0 (by omega))
      have hu1 : t.value (t.clause.get! 1) = 0 := by unfold value; rw [g6, hcl]; exact hun _ (hmem 1 (by omega))
      rw [addTail_unassigned t _ _ hu0 hu1]
      have hvars : t.vars = s.vars := Flg.vars (flg_of_anaSide g7)
      refine ⟨hcl, g12, Or.inr (Or.inr ⟨g1, fun d hd => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
      · unfold InvS; rw [invSAt_congr g6 g10, g9]
        rcases (g5 d).mp hd with hold | rfl
        · exact hsinvS d hold
        · exact invSAt_unassigned_first (x := s.clause.get! 0) (hnotF _ (hmem 0 (by omega)))
            (by rw [U32Vec.get!_eq_view]; cases hv : s.clause.view with
              | nil => have := congrArg List.length hv; simp at this; omega
              | cons y ys => simp)
      · rw [g9, hS.propagate, hb.prop]; simp [trailL, g6, hS.asg]
      · rw [g8, hS.level, hb.level]
      · intro i bb hbb'; unfold abit abits; rw [g6, hS.asg]; exact hb.search.clean i bb hbb'
      · exact (flg_of_anaSide g7).trans hfl0
      · rw [hvars]; exact hact'
      · intro hf; apply hb.flags
        have e := g7; simp only [anaSide, Prod.mk.injEq] at e
        unfold Flagged at *
        rw [e.2.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, eo, eoor, enp] at hf
        exact hf
      · exact hmono0.trans g13
      · refine Or.inr (Or.inr ⟨s.clause.view, Or.inl ⟨r, g2, g4, g3.symm⟩, fun x hx => ?_⟩)
        rcases hcovL x hx with e | e
        · exact Or.inl e
        · exact absurd e id

/-- The state after adding one clause. -/
def ImpStep (F : CNF Nat) (base t : Solver) (c : CNF.Clause Nat) : Prop :=
  (t.inconsistent = true ∧ ¬ ∃ β, PhiF F β) ∨ (Flagged t ∧ t.inconsistent = false) ∨
  (ImpBase F t ∧ IrrMono base t ∧ CovC t c)

theorem addClauseEnd_spec {F : CNF Nat} {base s : Solver} {c : CNF.Clause Nat} (hb : ImpBase F base)
    (hcF : c ∈ F.clauses.toList) (h : LitPhase base s c.literals.reverse) :
    ImpStep F base s.addClauseEnd c := by
  obtain ⟨o1, o2, o3⟩ := addClauseBody_spec hb hcF h
  unfold addClauseEnd
  generalize s.addClauseBody = u at o1 o2 o3
  obtain ⟨M, e1, e2, e3⟩ := clearClauseMarks_zero u 0 (fun j hj => by
    rw [o2] at hj
    obtain ⟨x, hx, hjx⟩ := h.m2 j hj
    rw [← o1] at hx
    obtain ⟨q, hq, hqx⟩ := U32Vec.mem_view_pos _ _ hx
    exact ⟨q, Nat.zero_le _, hq, by rw [hqx]; exact hjx⟩)
  rw [e1]
  dsimp only
  generalize ht : ({ ({ u with marks := M } : Solver) with clause := u.clause.clear, clauseSatisfied := false, clauseTrivial := false, clauseShrink := false } : Solver) = t
  have hS : Same t u := by rw [← ht]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have tI : t.inconsistent = u.inconsistent := by rw [← ht]
  have tFl : (t.overflowed = u.overflowed ∧ t.outOfResources = u.outOfResources ∧ t.notPorted = u.notPorted) := by
    rw [← ht]; exact ⟨rfl, rfl, rfl⟩
  have tFlg : Flg t = Flg u := by rw [← ht]; rfl
  rcases o3 with hi | ⟨hf, hi⟩ | g
  · exact Or.inl ⟨by rw [tI]; exact hi.1, hi.2⟩
  · refine Or.inr (Or.inl ⟨?_, by rw [tI]; exact hi⟩)
    unfold Flagged at *; rw [tFl.1, tFl.2.1, tFl.2.2]; exact hf
  · right; right
    have hflg : Flg t = Flg base := tFlg.trans g.flg
    have hvars : t.vars = base.vars := Flg.vars hflg
    have hmono : IrrMono u t := IrrMono.of_eq hS.asg hS.arena hS.watches
    refine ⟨⟨⟨hS.sinv g.inv, fun d hd => ?_, fun i b hb' => ?_, ?_, fun e => ?_, ?_, ?_, ?_⟩,
      by rw [hS.level]; exact g.level, by rw [hS.propagate, g.prop]; simp [trailL, hS.asg],
      fun j => by rw [← ht]; exact e3 j, ?_, by rw [← ht], by rw [← ht], by rw [← ht], ?_, ?_, ?_,
      by rw [tI]; exact Flg.inconsistent g.flg ▸ hb.incons, ?_⟩, g.mono.trans hmono,
      g.cov.mono hmono g.inv.core (hS.sinv g.inv).core⟩
    · unfold InvS; rw [hS.invSAt, hS.propagate]; exact g.invS d ((hS.inDB d).mp hd)
    · unfold abit abits; rw [hS.asg]; exact g.clean i b hb'
    · rw [← ht]; simp [U32Vec.clear, U32Vec.size_shrink]
    · rw [tI, Flg.inconsistent g.flg, hb.incons] at e; simp at e
    · rw [Flg.watching hflg]; exact hb.search.watching
    · rw [Flg.options hflg]; exact hb.search.opts
    · exact hb.search.imp.flg hflg
    · have hm : M.size = s.marks.size := by rw [e2, o2]
      rw [show t.marks = M by rw [← ht], hm, h.msize, hvars]; exact hb.marksSize
    · rw [show t.flags = u.flags by rw [← ht], hS.asg, hS.vars]; exact g.active
    · rw [Flg.options hflg]; exact hb.tumble
    · rw [hvars]; exact hb.fvars
    · intro hf; apply g.notFlagged; unfold Flagged at *; rw [tFl.1, tFl.2.1, tFl.2.2] at hf; exact hf

theorem addClause_spec {F : CNF Nat} {base : Solver} {c : CNF.Clause Nat} (hb : ImpBase F base)
    (hcF : c ∈ F.clauses.toList) : ImpStep F base (addClause base c) c := by
  unfold addClause
  have hsm := hb.search.inv.ws.varsBound
  have hP := LitPhase.fold hb c.literals base [] (LitPhase.init hb) (by simp)
    (fun l hl => hb.fvars c hcF l hl)
  simp only [List.append_nil] at hP
  have e : ((c.literals.foldl (fun s l => s.add (extLit l)) base).add 0) =
      (c.literals.foldl (fun s l => s.add (extLit l)) base).addClauseEnd := by
    unfold add; rw [ite_eq_left (by rfl)]
  rw [e]
  exact addClauseEnd_spec hb hcF hP

/-- Fields untouched by importing literals. -/
def KF (t s : Solver) : Prop :=
  t.inconsistent = s.inconsistent ∧ t.overflowed = s.overflowed ∧ t.outOfResources = s.outOfResources ∧
  t.notPorted = s.notPorted

theorem KF.refl (s : Solver) : KF s s := ⟨rfl, rfl, rfl, rfl⟩
theorem KF.trans {a b c : Solver} (h1 : KF a b) (h2 : KF b c) : KF a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

macro "kf_rfl" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl⟩)

theorem increaseSize_kf (s : Solver) (n : UInt32) : KF (s.increaseSize n) s := by
  unfold increaseSize; dsimp only; split
  · kf_rfl
  · kf_rfl

theorem enlargeVariables_kf (s : Solver) (n : UInt32) : KF (s.enlargeVariables n) s := by
  unfold enlargeVariables; split
  · kf_rfl
  · dsimp only; split
    · exact (show KF _ _ by kf_rfl).trans (increaseSize_kf _ _)
    · kf_rfl

theorem adjustExports_kf (s : Solver) (e : Nat) (x : Bool) : KF (s.adjustExports e x) s := by
  unfold adjustExports; dsimp only
  have h1 := enlargeVariables_kf s (s.vars + 1)
  generalize s.enlargeVariables (s.vars + 1) = s1 at h1
  refine (show KF _ s1 by split <;> kf_rfl).trans h1

theorem importLiteralAux_kf (s : Solver) (e : Int) (x : Bool) : KF (s.importLiteralAux e x).2 s := by
  have hA : KF (s.adjustImports e.natAbs) s := by unfold adjustImports; split <;> kf_rfl
  unfold importLiteralAux; dsimp only
  generalize s.adjustImports e.natAbs = s1 at hA
  split
  · exact hA
  · have h2 : KF (if (s1.importBitsAt e.natAbs &&& ImportBits.imported == 0) = true then s1.adjustExports e.natAbs x
        else s1) s := by
      split
      · exact (adjustExports_kf _ _ _).trans hA
      · exact hA
    exact h2

theorem importUpTo_kf (e : Nat) : ∀ (k o : Nat) (s : Solver) (l : Lit), e + 1 - o = k → KF (importUpTo s o e l).2 s := by
  intro k
  induction k with
  | zero =>
    intro o s l hk
    rw [importUpTo, dite_eq_right (by omega)]; exact KF.refl _
  | succ k ih =>
    intro o s l hk
    rw [importUpTo, dite_eq_left (by omega)]
    dsimp only
    exact (ih (o + 1) _ _ (by omega)).trans (importLiteralAux_kf _ _ _)

theorem importLiteral_kf (s : Solver) (e : Int) : KF (s.importLiteral e).2 s := by
  unfold importLiteral
  split
  · exact importLiteralAux_kf _ _ _
  · dsimp only
    split
    · exact importLiteralAux_kf _ _ _
    · have h0 : KF (if s.importLit.size == 0 then (s.adjustImports 0, 1) else (s, s.importLit.size)).1 s := by
        split
        · unfold adjustImports; split <;> kf_rfl
        · exact KF.refl _
      generalize (if s.importLit.size == 0 then (s.adjustImports 0, 1) else (s, s.importLit.size)) = P at h0
      obtain ⟨u, o⟩ := P
      exact (importUpTo_kf _ _ _ _ _ rfl).trans h0

theorem clearClauseMarks_kf (s : Solver) (i : Nat) : KF (s.clearClauseMarks i) s := by
  fun_induction clearClauseMarks s i with
  | case1 s i hi lit ih => exact ih.trans (by kf_rfl)
  | case2 => exact KF.refl _

theorem KF.bad {s t : Solver} (h : KF t s) (hb : s.inconsistent = true ∨ Flagged s) :
    t.inconsistent = true ∨ Flagged t := by
  obtain ⟨e1, e2, e3, e4⟩ := h
  unfold Flagged at *; rw [e1, e2, e3, e4]; exact hb

theorem add_bad (s : Solver) (e : Int) (hb : s.inconsistent = true ∨ Flagged s) : KF (s.add e) s := by
  unfold add
  split
  · unfold addClauseEnd
    have hbody : s.addClauseBody = s := by
      unfold addClauseBody
      rcases hb with h | h
      · rw [ite_eq_left h]
      · by_cases hi : s.inconsistent = true
        · rw [ite_eq_left hi]
        · rw [ite_eq_right hi, ite_eq_left (by unfold Flagged at h; rcases h with h | h | h <;> simp [h])]
    rw [hbody]
    exact (show KF _ (s.clearClauseMarks 0) by kf_rfl).trans (clearClauseMarks_kf _ _)
  · dsimp only
    have h1 := importLiteral_kf s e
    generalize s.importLiteral e = R at h1
    obtain ⟨il, u⟩ := R
    dsimp only at h1 ⊢
    have h2 : ∀ t : Solver, KF t u → KF t s := fun t ht => ht.trans h1
    apply h2
    repeat' split
    all_goals kf_rfl

theorem addClause_bad (s : Solver) (c : CNF.Clause Nat) (hb : s.inconsistent = true ∨ Flagged s) :
    KF (addClause s c) s := by
  unfold addClause
  have : ∀ (L : List (Literal Nat)) (u : Solver), (u.inconsistent = true ∨ Flagged u) → KF u s →
      KF ((L.foldl (fun s l => s.add (extLit l)) u).add 0) s := by
    intro L
    induction L with
    | nil => intro u hu hk; exact (add_bad u 0 hu).trans hk
    | cons l L ih =>
      intro u hu hk
      have h1 := add_bad u (extLit l) hu
      exact ih _ (h1.bad hu) (h1.trans hk)
  exact this _ s hb (KF.refl _)

end Solver
end LeanKissat
