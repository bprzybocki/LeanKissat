import LeanKissat.Proofs.ConflictLevel

/-!
# `analyzeFailedLiteral` (conflicts on decision level one)
-/

namespace LeanKissat
namespace Solver
open Arena

/-- The invariant of the failed-literal resolution walk. -/
structure FInv (Φ : (Nat → Bool) → Prop) (s0 : Solver) (c : CRef) (m : Nat) (s : Solver) (t u : Nat) : Prop where
  af : AF s s0
  ana : ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isAnalyzed (IDX y) = true →
    (∃ p < t, s0.trailL[p]? = some (NOT y)) ∨ Resolved s0 s (NOT y)
  anaAssigned : ∀ i, s.isAnalyzed i = true → ∃ y, IDX y = i ∧ s0.IsFalse y ∧ 0 < s0.lvl y
  count : u = pendCount s0 s 1 t
  tle : t ≤ s0.trailL.length
  conf : ∀ k, k < m → s0.lvl (s0.crefLit c k) = 0 ∨ s.isAnalyzed (IDX (s0.crefLit c k)) = true
  units : ∀ x ∈ s.clause.view, Implied Φ [x] ∧ s0.ValidLit x
  listed : Listed s
  others : ∀ i b, (b = ABits.poisoned ∨ b = ABits.removable ∨ b = ABits.shrinkable) → s.abit i b = false

/-- With one pending literal `lit` at position `p`, every analyzed literal is derivable from `NOT lit`. -/
theorem failed_derive {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    {s : Solver} {t : Nat} (h : FInv Φ s0 c (s0.crefSize c) s t 1) {lit : Lit} {p : Nat} (hpt : p < t)
    (hp : s0.trailL[p]? = some lit) (hcount : pendCount s0 s 1 p = 0)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → anaP s0 s 1 l = false) :
    ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isAnalyzed (IDX y) = true → DerFalse s0 [NOT lit] y := by
  have hnd := hb.trail_nodup
  suffices H : ∀ n, ∀ y, s0.trailL[n]? = some (NOT y) → s0.IsFalse y → 0 < s0.lvl y →
      s.isAnalyzed (IDX y) = true → DerFalse s0 [NOT lit] y by
    intro y hf hl ha
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (hb.true_on_trail hf hl)
    exact H n y hn hf hl ha
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro y hn hf hl ha
  have hle : s0.lvl y ≤ 1 := by
    have := hb.inv.levelOK.trueLe (NOT y) (by
      have := (hb.inv.core.valCons (NOT y)).1; rw [NOT_NOT] at this; exact this.mpr hf)
    rw [hb.inv.core.lvlVar, hb.level] at this; exact this
  have heq : s0.lvl y = 1 := by omega
  by_cases hu : NOT y = lit
  · have : y = NOT lit := by rw [← hu, NOT_NOT]
    subst this; exact .inK (List.mem_singleton_self _)
  rcases h.ana y hf hl ha with ⟨q, hq, hqy⟩ | ⟨A, hA, hA'⟩
  · exfalso
    have hqn := nodup_pos_unique hnd hqy hn
    subst hqn
    have hana : anaP s0 s 1 (NOT y) = true := by
      unfold anaP; rw [IDX_NOT, ha, hb.inv.core.lvlVar, heq]; simp
    rcases Nat.lt_trichotomy q p with hlt | heq' | hgt
    · rw [pendCount, List.countP_eq_zero] at hcount
      have hmem : NOT y ∈ s0.trailL.take p := by
        rw [List.mem_iff_getElem?]; exact ⟨q, by rw [List.getElem?_take]; simp [hlt, hqy]⟩
      exact absurd hana (by simpa using hcount _ hmem)
    · subst heq'; rw [hp] at hqy; exact hu (Option.some.inj hqy).symm
    · rw [hgap q hgt hq _ hqy] at hana; exact absurd hana (by simp)
  · apply DerFalse.reason hA
    intro x hx
    have hante := hb.ante_of_antecedents hA hx
    rcases hA' x hx with h0 | hax
    · exact .root hante.1 h0
    · have hxl : 0 < s0.lvl x := by
        obtain ⟨y', hy', hf', hl'⟩ := h.anaAssigned _ hax
        have := hb.false_same_var hante.1 hf' hy'
        subst this; exact hl'
      obtain ⟨q, hq, hqx⟩ := hb.ante_before hn hante hxl
      exact ih q hq x hqx hante.1 hxl hax

/-- The conflict implies the unit `NOT lit` when `lit` is the only pending literal. -/
theorem failed_unit {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    (hc : ConflictOK s0 s0 c) {s : Solver} {t : Nat} (h : FInv Φ s0 c (s0.crefSize c) s t 1) {lit : Lit} {p : Nat} (hpt : p < t)
    (hp : s0.trailL[p]? = some lit) (hcount : pendCount s0 s 1 p = 0)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → anaP s0 s 1 l = false) :
    Implied Φ [NOT lit] := by
  apply implied_of_derFalse hb.inv.db hb.inv.roots hb.inv.core.valCons hb.inv.core.lvlVar (hc.implied hb.inv)
  intro y hy
  simp only [List.mem_map, List.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  have hf := ConflictOK.lit_false hc hk
  rcases h.conf k hk with h0 | ha
  · exact .root hf h0
  · have hl : 0 < s0.lvl (s0.crefLit c k) := by
      obtain ⟨y', hy', hf', hl'⟩ := h.anaAssigned _ ha
      have := hb.false_same_var hf hf' hy'
      subst this; exact hl'
    exact failed_derive hb h hpt hp hcount hgap _ hf hl ha

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem decisionsOK_spec (s : Solver) (failed : Lit) (n : Nat) :
    ∀ i, s.decisionsOK failed i n = true → ∀ q, i ≤ q → q < n →
      s.reasonIdx (IDX (s.asg.trail.get! q)) ≠ DECISION_REASON ∨ s.asg.trail.get! q = failed := by
  intro i
  fun_induction decisionsOK s failed i n with
  | case1 i hi x ih =>
    intro h q hq1 hq2
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    by_cases e : q = i
    · subst e; exact h.1
    · exact ih h.2 q (by omega) hq2
  | case2 i hi => intro _ q hq1 hq2; omega

/-- A true literal of level `L > 0` sits on the trail at or after the start of level `L`. -/
theorem pos_ge_frame {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {x : Lit} {p : Nat}
    (hp : s.trailL[p]? = some x) {L : Nat} (hL : s.lvl x = L) (hpos : 0 < L) (hLe : L ≤ s.level.toNat) :
    s.framesL[L - 1]'(by rw [hs.levelOK.len]; omega) ≤ p := by
  apply Classical.byContradiction
  intro hlt
  have hpl := hs.levelOK.pushLe p x hp
  rw [hL] at hpl
  have key := countP_le_of_sorted s.framesL (L - 1) p hs.levelOK.sorted (by rw [hs.levelOK.len]; omega) (by omega)
  unfold pushLevel at hpl
  rw [key] at hpl
  have := List.countP_le_length (p := fun f : Nat => Decidable.decide (f ≤ p)) (l := s.framesL.take (L - 1))
  simp at this; omega

theorem antecedents_of_reasonAt {s : Solver} {x : Lit} (ht : s.IsTrue x) (hl : 0 < s.lvl x) (hr : s.ReasonAt x)
    (hnd : s.reasonOf x ≠ DECISION_REASON) :
    ∃ A, s.Antecedents x A ∧ ∀ a ∈ A, s.Ante x a := by
  rcases hr with e | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩
  · exact absurd e hnd
  · exact ⟨[s.reasonOf x], ⟨ht, hl, Or.inl ⟨b1, b2, rfl⟩⟩, fun a ha => by simp at ha; subst ha; exact b3⟩
  · refine ⟨(s.clauseL (s.reasonOf x)).filter (fun a => a != x), ⟨ht, hl, Or.inr ⟨b1, hnd, b2, b3, fun a => ?_⟩⟩,
      fun a ha => ?_⟩
    · simp [List.mem_filter]
    · obtain ⟨h1, h2⟩ := List.mem_filter.mp ha
      exact b4 a h1 (by simpa using h2)

/-- With `failed` the only decision of level one, its negation is implied. -/
theorem failed_notFailed {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    (hc : ConflictOK s0 s0 c) {failed : Lit} (hdec : s0.decisionsOK failed (s0.frameTrailAt 1).toNat s0.asg.trail.size = true) :
    Implied Φ [NOT failed] := by
  have hs := hb.inv
  have hfr : (s0.frameTrailAt 1).toNat = s0.framesL[0]'(by rw [hs.levelOK.len, hb.level]; omega) :=
    frameTrailAt_eq s0 hs.levelOK 0 (by rw [hb.level]; omega)
  have hd := decisionsOK_spec s0 failed s0.asg.trail.size _ hdec
  suffices H : ∀ n, ∀ y, s0.trailL[n]? = some (NOT y) → s0.IsFalse y → 0 < s0.lvl y → DerFalse s0 [NOT failed] y by
    apply implied_of_derFalse hs.db hs.roots hs.core.valCons hs.core.lvlVar (hc.implied hs)
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hf := ConflictOK.lit_false hc hk
    by_cases h0 : s0.lvl (s0.crefLit c k) = 0
    · exact .root hf h0
    · obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (hb.true_on_trail hf (by omega))
      exact H n _ hn hf (by omega)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro y hn hf hl
  have ht : s0.IsTrue (NOT y) := hs.core.trailTrue _ (List.mem_of_getElem? hn)
  have hle : s0.lvl y ≤ 1 := by
    have := hs.levelOK.trueLe (NOT y) ht
    rw [hs.core.lvlVar, hb.level] at this; exact this
  have hl1 : s0.lvl (NOT y) = 1 := by rw [hs.core.lvlVar]; omega
  have hge := pos_ge_frame hs hn hl1 (by omega) (by rw [hb.level]; exact Nat.le_refl _)
  have hnlen : n < s0.asg.trail.size := by
    have := (List.getElem?_eq_some_iff.mp hn).1; unfold trailL at this; simpa using this
  have hget : s0.asg.trail.get! n = NOT y := by
    unfold trailL at hn
    rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, hn]; rfl
  rcases hd n (by rw [hfr]; exact hge) hnlen with hr | hr
  · rw [hget] at hr
    obtain ⟨A, hA, hA'⟩ := antecedents_of_reasonAt ht (by rw [hl1]; omega) (hs.reasons _ ht (by rw [hl1]; omega)) hr
    apply DerFalse.reason hA
    intro x hx
    have hax := hA' x hx
    by_cases hx0 : s0.lvl x = 0
    · exact .root hax.1 hx0
    · obtain ⟨q, hq, hqx⟩ := hb.ante_before hn hax (by omega)
      exact ih q hq x hqx hax.1 (by omega)
  · rw [hget] at hr
    have : y = NOT failed := by rw [← hr, NOT_NOT]
    subst this; exact .inK (List.mem_singleton_self _)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem Resolved.mono {s0 s t : Solver} {l : Lit} (h : Resolved s0 s l)
    (hm : ∀ i, s.isAnalyzed i = true → t.isAnalyzed i = true) : Resolved s0 t l := by
  obtain ⟨A, hA, hA'⟩ := h
  exact ⟨A, hA, fun x hx => (hA' x hx).imp_right (hm _)⟩

theorem FInv.push {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} {m : Nat} (hb : DBase Φ s0 1) {s : Solver} {t u : Nat}
    (h : FInv Φ s0 c m s t u) {x : Lit} (hx : s0.IsFalse x) (hxl : s0.lvl x = 1)
    (hna : s.isAnalyzed (IDX x) = false) (hpos : ∃ q < t, s0.trailL[q]? = some (NOT x)) :
    FInv Φ s0 c m (s.pushAnalyzed (IDX x)) t (u + 1) ∧
    (∀ i, s.isAnalyzed i = true → (s.pushAnalyzed (IDX x)).isAnalyzed i = true) ∧
    (s.pushAnalyzed (IDX x)).isAnalyzed (IDX x) = true ∧ (s.pushAnalyzed (IDX x)).clause = s.clause := by
  have hv := hb.valid_false hx
  have hsz : (IDX x).toNat < s.asg.aBits.size := by
    rw [h.af.bitsSize]; have := hb.inv.rsizes.2.1; unfold ValidLit at hv; omega
  have hab : ∀ i, (s.pushAnalyzed (IDX x)).isAnalyzed i = (if IDX x = i then true else s.isAnalyzed i) := by
    intro i; show (s.pushAnalyzed (IDX x)).abit i ABits.analyzed = _
    rw [pushAnalyzed_abit s _ i hsz _ (Or.inl rfl)]; simp; rfl
  have hmono : ∀ i, s.isAnalyzed i = true → (s.pushAnalyzed (IDX x)).isAnalyzed i = true := by
    intro i hi; rw [hab]; split <;> simp_all
  have hnew : (s.pushAnalyzed (IDX x)).isAnalyzed (IDX x) = true := by rw [hab]; simp
  refine ⟨⟨(pushAnalyzed_af s _).trans h.af, fun y hy hyl hya => ?_, fun i hi => ?_, ?_, h.tle,
    fun k hk => (h.conf k hk).imp_right (hmono _), h.units, pushAnalyzed_listed s _ hsz h.listed,
    fun i b hb' => ?_⟩, hmono, hnew, rfl⟩
  · rw [hab] at hya
    by_cases e : IDX x = IDX y
    · have := hb.false_same_var hx hy e.symm
      subst this; exact Or.inl hpos
    · rw [if_neg e] at hya
      exact (h.ana y hy hyl hya).imp_right (fun hr => hr.mono hmono)
  · rw [hab] at hi
    by_cases e : IDX x = i
    · subst e; exact ⟨x, rfl, hx, by omega⟩
    · rw [if_neg e] at hi; exact h.anaAssigned i hi
  · rw [h.count]
    unfold pendCount
    obtain ⟨q, hq, hqx⟩ := hpos
    have hmem : NOT x ∈ s0.trailL.take t := by
      rw [List.mem_iff_getElem?]; exact ⟨q, by rw [List.getElem?_take]; simp [hq, hqx]⟩
    have hnd : (s0.trailL.take t).Nodup := hb.trail_nodup.sublist (List.take_sublist _ _)
    symm
    apply countP_succ_of_unique _ _ _ (NOT x) hmem hnd
    · unfold anaP; rw [IDX_NOT, hnew, hb.inv.core.lvlVar, hxl]; simp
    · unfold anaP; rw [IDX_NOT, hna]; simp
    · intro z hz hne
      unfold anaP
      rw [hab]
      have : IDX x ≠ IDX z := by
        intro e
        exact hne (hb.idx_unique (List.mem_of_mem_take hz) (List.mem_of_mem_take hmem) (by rw [IDX_NOT, e]))
      rw [if_neg this]
  · rw [pushAnalyzed_abit s _ i hsz _ (by rcases hb' with rfl | rfl | rfl <;> simp)]
    have : b ≠ ABits.analyzed := by rcases hb' with rfl | rfl | rfl <;> decide
    simp [this]; exact h.others i b hb'

/-- Moving the trail pointer to the resolved literal at `p`. -/
theorem FInv.move {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} {m : Nat} (hb : DBase Φ s0 1) {s : Solver} {t u : Nat}
    (h : FInv Φ s0 c m s t u) {lit : Lit} {p : Nat} (hpt : p < t) (hp : s0.trailL[p]? = some lit)
    (hlit : s.isAnalyzed (IDX lit) = true) (hres : Resolved s0 s lit)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → s.isAnalyzed (IDX l) = false) :
    FInv Φ s0 c m s p (u - 1) := by
  have hlt : s0.IsTrue lit := hb.inv.core.trailTrue _ (List.mem_of_getElem? hp)
  have hll : s0.lvl lit = 1 := by
    obtain ⟨y, hy, hf, hl⟩ := h.anaAssigned _ hlit
    have hnty := hb.true_on_trail hf hl
    have : NOT y = lit := hb.idx_unique hnty (List.mem_of_getElem? hp) (by rw [IDX_NOT, hy])
    rw [← this, hb.inv.core.lvlVar]
    have := hb.inv.levelOK.trueLe (NOT y) (by rw [this]; exact hlt)
    rw [hb.inv.core.lvlVar, hb.level] at this; omega
  have hana : anaP s0 s 1 lit = true := by unfold anaP; rw [hlit, hll]; simp
  have hsplit := pendCount_split hpt h.tle hp hana (fun q h1 h2 l hl => by
    unfold anaP; rw [hgap q h1 h2 l hl]; simp)
  refine ⟨h.af, fun y hy hyl hya => ?_, h.anaAssigned, by rw [h.count, hsplit]; omega, by have := h.tle; omega,
    h.conf, h.units, h.listed, h.others⟩
  rcases h.ana y hy hyl hya with ⟨q, hq, hqy⟩ | hr
  · rcases Nat.lt_trichotomy q p with hlt' | heq | hgt
    · exact Or.inl ⟨q, hlt', hqy⟩
    · subst heq; rw [hp] at hqy
      have : NOT y = lit := (Option.some.inj hqy).symm
      rw [this]; exact Or.inr hres
    · have := hgap q hgt hq _ hqy; rw [IDX_NOT, hya] at this; simp at this
  · exact Or.inr hr

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem conflict_distinct {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) {c : CRef}
    (hc : ConflictOK s0 s0 c) : ∀ j k, j < s0.crefSize c → k < s0.crefSize c → j ≠ k →
      IDX (s0.crefLit c j) ≠ IDX (s0.crefLit c k) := by
  intro j k hj hk hjk e
  have hfj := ConflictOK.lit_false hc hj
  have hfk := ConflictOK.lit_false hc hk
  have heq := hb.false_same_var hfk hfj e
  cases c with
  | binConflict =>
    obtain ⟨hbw, _, _⟩ := hc
    have hne := (hb.inv.ws.bin _ _ hbw).2.2.2
    simp [crefSize] at hj hk
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact hjk rfl
    · simp [crefLit] at heq; exact hne heq
    · simp [crefLit] at heq; exact hne heq.symm
    · exact hjk rfl
  | large r =>
    have hnd := (hb.inv.ws.live r hc.1).2.1
    rw [List.Nodup, List.pairwise_iff_getElem] at hnd
    have hlen : (s0.clauseL r).length = (s0.arena.size r).toNat := length_litsL _ _
    simp only [crefSize] at hj hk
    have gj : (s0.clauseL r)[j]'(by omega) = s0.crefLit (.large r) j := getElem_litsL _ _ _ _
    have gk : (s0.clauseL r)[k]'(by omega) = s0.crefLit (.large r) k := getElem_litsL _ _ _ _
    rcases Nat.lt_or_gt_of_ne hjk with h' | h'
    · exact hnd j k (by omega) (by omega) h' (by rw [gj, gk]; exact heq)
    · exact hnd k j (by omega) (by omega) h' (by rw [gj, gk]; exact heq.symm)

/-- Facts kept by every step of the failed-literal analysis. -/
structure FPost (Φ : (Nat → Bool) → Prop) (s0 : Solver) (s : Solver) : Prop where
  af : AF s s0
  units : ∀ x ∈ s.clause.view, Implied Φ [x] ∧ s0.ValidLit x
  listed : Listed s
  others : ∀ i b, (b = ABits.poisoned ∨ b = ABits.removable ∨ b = ABits.shrinkable) → s.abit i b = false

theorem FInv.post {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} {m : Nat} {s : Solver} {t u : Nat}
    (h : FInv Φ s0 c m s t u) : FPost Φ s0 s := ⟨h.af, h.units, h.listed, h.others⟩

theorem failedInit_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    (hc : ConflictOK s0 s0 c) (notFailed : Lit) :
    ∀ (s : Solver) (i u : Nat), FInv Φ s0 c i s s0.trailL.length u → i ≤ s0.crefSize c →
      (∀ k, i ≤ k → k < s0.crefSize c → s.isAnalyzed (IDX (s0.crefLit c k)) = false) →
      (∀ k, s.crefLit c k = s0.crefLit c k) →
      FPost Φ s0 (s.failedInit c notFailed (s0.crefSize c) i u).2.2 ∧
      ((s.failedInit c notFailed (s0.crefSize c) i u).1 = false →
        FInv Φ s0 c (s0.crefSize c) (s.failedInit c notFailed (s0.crefSize c) i u).2.2 s0.trailL.length
          (s.failedInit c notFailed (s0.crefSize c) i u).2.1 ∧
        ∀ k, (s.failedInit c notFailed (s0.crefSize c) i u).2.2.crefLit c k = s0.crefLit c k) := by
  intro s i u
  fun_induction failedInit s c notFailed (s0.crefSize c) i u with
  | case1 s i u hi lit hnf =>
    intro h _ _ _
    exact ⟨h.post, fun hf => absurd hf (by simp)⟩
  | case2 s i u hi lit hnf idx h0 ih =>
    intro h _ hna hcl
    have hc' : FInv Φ s0 c (i + 1) s s0.trailL.length u := by
      refine ⟨h.af, h.ana, h.anaAssigned, h.count, h.tle, fun k hk => ?_, h.units, h.listed, h.others⟩
      by_cases e : k = i
      · subst e; left
        have : (s.levelIdx (IDX (s.crefLit c k)) == 0) = true := h0
        rw [hcl] at this
        rw [← h.af.lvl]; exact (levelIdx_eq_zero s _).mp this
      · exact h.conf k (by omega)
    exact ih hc' (by omega) (fun k hk1 hk2 => hna k (by omega) hk2) hcl
  | case3 s i u hi lit hnf idx h0 ih =>
    intro h _ hna hcl
    have hlit : lit = s0.crefLit c i := hcl i
    have hf := ConflictOK.lit_false hc hi
    have hl1 : s0.lvl (s0.crefLit c i) = 1 := by
      have hne : s.levelIdx (IDX lit) ≠ 0 := by simpa using h0
      have hpos : 0 < s0.lvl (s0.crefLit c i) := by
        rw [← h.af.lvl, ← hlit]
        apply Nat.pos_of_ne_zero; intro e; exact hne (by have := (levelIdx_eq_zero s lit).mpr e; simpa using this)
      have := hb.inv.levelOK.trueLe (NOT (s0.crefLit c i)) (by
        have := (hb.inv.core.valCons (NOT (s0.crefLit c i))).1; rw [NOT_NOT] at this; exact this.mpr hf)
      rw [hb.inv.core.lvlVar, hb.level] at this; omega
    obtain ⟨p1, p2, p3, p4⟩ := h.push hb hf hl1 (hna i (Nat.le_refl _) hi)
      (by
        obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp (hb.true_on_trail hf (by omega))
        exact ⟨q, (List.getElem?_eq_some_iff.mp hq).1, hq⟩)
    have hidx : idx = IDX (s0.crefLit c i) := by show IDX (s.crefLit c i) = _; rw [hcl]
    rw [← hidx] at p1 p2 p3 p4
    have hc' : FInv Φ s0 c (i + 1) (s.pushAnalyzed idx) s0.trailL.length (u + 1) := by
      refine ⟨p1.af, p1.ana, p1.anaAssigned, p1.count, p1.tle, fun k hk => ?_, p1.units, p1.listed, p1.others⟩
      by_cases e : k = i
      · subst e; rw [← hidx]; exact Or.inr p3
      · exact p1.conf k (by omega)
    have hdist := conflict_distinct hb hc
    have hsz : idx.toNat < s.asg.aBits.size := by
      rw [hidx, h.af.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf; unfold ValidLit at this; omega
    refine ih hc' (by omega) (fun k hk1 hk2 => ?_) (fun k => by rw [← hcl k]; rfl)
    show (s.pushAnalyzed idx).abit _ ABits.analyzed = false
    rw [pushAnalyzed_abit s idx _ hsz _ (Or.inl rfl)]
    have hne : idx ≠ IDX (s0.crefLit c k) := by rw [hidx]; exact hdist i k hi hk2 (by omega)
    simp only [hne, false_and, ite_false]
    exact hna k (by omega) hk2
  | case4 s i u hi =>
    intro h hle _ hcl
    have : i = s0.crefSize c := by omega
    subst this
    exact ⟨h.post, fun _ => ⟨h, hcl⟩⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem prevAnalyzed_spec (s : Solver) : ∀ t p, s.prevAnalyzed t = some p →
    p < t ∧ s.isAnalyzed (IDX (s.asg.trail.get! p)) = true ∧
    ∀ q, p < q → q < t → s.isAnalyzed (IDX (s.asg.trail.get! q)) = false := by
  intro t
  induction t with
  | zero => intro p h; simp [prevAnalyzed] at h
  | succ t ih =>
    intro p h
    unfold prevAnalyzed at h
    split at h
    · rename_i ha; simp at h; subst h
      exact ⟨by omega, ha, fun q h1 h2 => by omega⟩
    · rename_i hna
      obtain ⟨a1, a2, a3⟩ := ih p h
      refine ⟨by omega, a2, fun q h1 h2 => ?_⟩
      by_cases e : q = t
      · subst e; simpa using hna
      · exact a3 q h1 (by omega)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem DBase.invalid_not_false' {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) :
    ¬ s0.IsFalse INVALID_LIT := by
  intro h
  have := hb.valid_false h
  have hv := hb.inv.ws.varsBound
  unfold ValidLit at this; rw [IDX_toNat] at this
  simp [INVALID_LIT] at this; omega

theorem FInv.lvl_one {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} {m : Nat} (hb : DBase Φ s0 1)
    {s : Solver} {t u : Nat} (h : FInv Φ s0 c m s t u) {x : Lit} (hx : s0.IsFalse x) (h0 : s0.lvl x ≠ 0) :
    s0.lvl x = 1 := by
  have := hb.inv.levelOK.trueLe (NOT x) (by
    have := (hb.inv.core.valCons (NOT x)).1; rw [NOT_NOT] at this; exact this.mpr hx)
  rw [hb.inv.core.lvlVar, hb.level] at this; omega

/-- The large-reason loop of the failed-literal walk. -/
theorem failedLarge_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} {m : Nat} (hb : DBase Φ s0 1)
    {t : Nat} (lit unit notFailed : Lit) (ref : Ref) (n : Nat)
    (hr : ref ∈ s0.arena.chain 0 s0.arena.sizeWards) (hn : n ≤ (s0.arena.size ref).toNat)
    {p : Nat} (hp : s0.trailL[p]? = some lit) (hpt : p < t)
    (hante : ∀ k, k < n → s0.arena.lit ref k ≠ lit → s0.Ante lit (s0.arena.lit ref k)) :
    ∀ (s : Solver) (j u : Nat), FInv Φ s0 c m s t u →
      (unit = INVALID_LIT ∨ s.isAnalyzed (IDX unit) = true) →
      (∀ k, k < j → s0.arena.lit ref k ≠ lit → s0.lvl (s0.arena.lit ref k) = 0 ∨
        s.isAnalyzed (IDX (s0.arena.lit ref k)) = true) →
      FPost Φ s0 (s.failedLarge lit unit notFailed ref j n u).2.2 ∧
      (∀ i, s.isAnalyzed i = true → (s.failedLarge lit unit notFailed ref j n u).2.2.isAnalyzed i = true) ∧
      (∀ i, (s.failedLarge lit unit notFailed ref j n u).2.2.isAnalyzed i = true → s.isAnalyzed i = true ∨
        ∃ k, k < n ∧ s0.arena.lit ref k ≠ lit ∧ IDX (s0.arena.lit ref k) = i) ∧
      (s.failedLarge lit unit notFailed ref j n u).2.2.clause = s.clause ∧
      ((s.failedLarge lit unit notFailed ref j n u).1 = false →
        FInv Φ s0 c m (s.failedLarge lit unit notFailed ref j n u).2.2 t (s.failedLarge lit unit notFailed ref j n u).2.1 ∧
        ∀ k, k < n → s0.arena.lit ref k ≠ lit → s0.lvl (s0.arena.lit ref k) = 0 ∨
          (s.failedLarge lit unit notFailed ref j n u).2.2.isAnalyzed (IDX (s0.arena.lit ref k)) = true) := by
  intro s j u
  fun_induction failedLarge s lit unit notFailed ref j n u with
  | case1 s j u hj other hskip ih =>
    intro h hu hdone
    have ho : other = s0.arena.lit ref j := h.af.lit_eq hr (by omega)
    obtain ⟨a1, a2, a2', a3, a4⟩ := ih h hu (fun k hk hne => by
      by_cases e : k = j
      · subst e
        rw [← ho] at hne ⊢
        simp only [Bool.or_eq_true, beq_iff_eq] at hskip
        rcases hskip with e1 | e2
        · exact absurd e1 hne
        · rcases hu with hu | hu
          · -- `unit = INVALID_LIT` is not a literal of a live clause
            exfalso
            have hf := (hante k (by omega) (by rw [← ho]; exact hne)).1
            rw [← ho, e2, hu] at hf; exact hb.invalid_not_false' hf
          · right; rw [e2]; exact hu
      · exact hdone k (by omega) hne)
    exact ⟨a1, a2, a2', a3, a4⟩
  | case2 s j u hj other hskip hnf =>
    intro h _ _
    exact ⟨h.post, fun _ h => h, fun _ h => Or.inl h, rfl, fun hf => absurd hf (by simp)⟩
  | case3 s j u hj other hskip hnf oidx hc ih =>
    intro h hu hdone
    have ho : other = s0.arena.lit ref j := h.af.lit_eq hr (by omega)
    obtain ⟨a1, a2, a2', a3, a4⟩ := ih h hu (fun k hk hne => by
      by_cases e : k = j
      · subst e
        rw [← ho] at hne ⊢
        simp only [Bool.or_eq_true, beq_iff_eq] at hc
        rcases hc with e1 | e2
        · left; rw [← h.af.lvl]; exact (levelIdx_eq_zero s _).mp (by simpa using e1)
        · right; exact e2
      · exact hdone k (by omega) hne)
    exact ⟨a1, a2, a2', a3, a4⟩
  | case4 s j u hj other hskip hnf oidx hc ih =>
    intro h hu hdone
    have ho : other = s0.arena.lit ref j := h.af.lit_eq hr (by omega)
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hskip
    have hne : s0.arena.lit ref j ≠ lit := by rw [← ho]; exact hskip.1
    have hA := hante j hj hne
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hc
    have hl0 : s0.lvl (s0.arena.lit ref j) ≠ 0 := by
      intro e; apply hc.1
      have := (levelIdx_eq_zero s (s0.arena.lit ref j)).mpr (by rw [h.af.lvl]; exact e)
      show s.levelIdx (IDX other) = 0
      rw [ho]; simpa using this
    have hl1 := h.lvl_one hb hA.1 hl0
    obtain ⟨q, hq, hqx⟩ := hb.ante_before hp hA (by omega)
    obtain ⟨p1, p2, p3, p4⟩ := h.push hb hA.1 hl1 (by rw [← ho]; exact hc.2) ⟨q, by omega, hqx⟩
    rw [← ho] at p1 p2 p3 p4
    obtain ⟨a1, a2, a2', a3, a4⟩ := ih p1 (hu.imp_right (p2 _)) (fun k hk hne' => by
      by_cases e : k = j
      · subst e; right; rw [← ho]; exact p3
      · exact (hdone k (by omega) hne').imp_right (p2 _))
    have hsz : oidx.toNat < s.asg.aBits.size := by
      show (IDX other).toNat < _
      rw [ho, h.af.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hA.1; unfold ValidLit at this; omega
    refine ⟨a1, fun i hi => a2 i (p2 i hi), fun i hi => ?_, by rw [a3, p4], a4⟩
    rcases a2' i hi with h' | h'
    · have : (s.pushAnalyzed oidx).abit i ABits.analyzed = true := h'
      rw [pushAnalyzed_abit s oidx i hsz _ (Or.inl rfl)] at this
      by_cases e : oidx = i
      · right; exact ⟨j, hj, hne, by rw [← e]; show IDX (s0.arena.lit ref j) = IDX other; rw [ho]⟩
      · simp [e] at this; exact Or.inl this
    · exact Or.inr h'
  | case5 s j u hj =>
    intro h _ hdone
    exact ⟨h.post, fun _ h => h, fun _ h => Or.inl h, rfl, fun _ => ⟨h, fun k hk hne => hdone k (by omega) hne⟩⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The walk invariant survives the optional unit push. -/
theorem walk_unit_step {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    (hc : ConflictOK s0 s0 c) {s : Solver} {t u : Nat} (h : FInv Φ s0 c (s0.crefSize c) s t u) {unit lit : Lit}
    (hun : unit = INVALID_LIT ∨ s.isAnalyzed (IDX unit) = true) {p : Nat} (hpt : p < t)
    (hp : s0.trailL[p]? = some lit) (hla : s.isAnalyzed (IDX lit) = true)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → s.isAnalyzed (IDX l) = false) :
    FInv Φ s0 c (s0.crefSize c) (if u == 1 then ({ s with clause := s.clause.push (NOT lit) } : Solver) else s) t u ∧
    ((if u == 1 then NOT lit else unit) = INVALID_LIT ∨
      (if u == 1 then ({ s with clause := s.clause.push (NOT lit) } : Solver) else s).isAnalyzed
        (IDX (if u == 1 then NOT lit else unit)) = true) ∧
    (∀ i b, (if u == 1 then ({ s with clause := s.clause.push (NOT lit) } : Solver) else s).abit i b = s.abit i b) ∧
    (if u == 1 then ({ s with clause := s.clause.push (NOT lit) } : Solver) else s).asg = s.asg ∧
    (if u == 1 then ({ s with clause := s.clause.push (NOT lit) } : Solver) else s).arena = s.arena := by
  by_cases hu1 : u = 1
  · have hb1 : (u == 1) = true := by simp [hu1]
    repeat rw [if_pos hb1]
    have hlt : s0.IsTrue lit := hb.inv.core.trailTrue _ (List.mem_of_getElem? hp)
    have hana : anaP s0 s 1 lit = true := by
      unfold anaP; rw [hla]
      obtain ⟨y, hy, hf, hl⟩ := h.anaAssigned _ hla
      have hnty := hb.true_on_trail hf hl
      have : NOT y = lit := hb.idx_unique hnty (List.mem_of_getElem? hp) (by rw [IDX_NOT, hy])
      have hl' := h.lvl_one hb hf (by omega)
      rw [← this, hb.inv.core.lvlVar, hl']; simp
    have hsplit := pendCount_split hpt h.tle hp hana (fun q h1 h2 l hl => by
      unfold anaP; rw [hgap q h1 h2 l hl]; simp)
    have hzero : pendCount s0 s 1 p = 0 := by rw [h.count] at hu1; omega
    have himp := failed_unit hb hc (hu1 ▸ h) hpt hp hzero (fun q h1 h2 l hl => by
      unfold anaP; rw [hgap q h1 h2 l hl]; simp)
    have hvl : s0.ValidLit (NOT lit) := by
      have := hb.inv.rsizes.valid hlt; unfold ValidLit at *; rw [IDX_NOT]; exact this
    generalize hs1 : ({ s with clause := s.clause.push (NOT lit) } : Solver) = s1
    have hcl1 : s1.clause = s.clause.push (NOT lit) := by rw [← hs1]
    have hab1 : ∀ i b, s1.abit i b = s.abit i b := by intro i b; rw [← hs1]; rfl
    have hana1 : ∀ i, s1.isAnalyzed i = s.isAnalyzed i := fun i => hab1 i _
    refine ⟨⟨by rw [← hs1]; exact AF.trans_left h.af af_rfl, fun y hy hyl hya => ?_, fun i hi => h.anaAssigned i (by rw [← hana1]; exact hi),
      by rw [h.count]; unfold pendCount anaP; congr 1; funext l; rw [hana1], h.tle,
      fun k hk => by rw [hana1]; exact h.conf k hk, fun x hx => ?_, by rw [← hs1]; exact h.listed,
      fun i b hb' => by rw [hab1]; exact h.others i b hb'⟩, Or.inr (by rw [hana1, IDX_NOT]; exact hla), hab1,
      by rw [← hs1], by rw [← hs1]⟩
    · rw [hana1] at hya
      rcases h.ana y hy hyl hya with h' | ⟨A, hA, hA'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨A, hA, fun x hx => (hA' x hx).imp_right (fun e => by rw [hana1]; exact e)⟩
    · rw [hcl1, U32Vec.view_push] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h.units x hx
      · simp at hx; subst hx; exact ⟨himp, hvl⟩
  · have hb1 : ¬ (u == 1) = true := by simpa using hu1
    repeat rw [if_neg hb1]
    exact ⟨h, hun, fun _ _ => rfl, rfl, rfl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem FPost.overflow {Φ : (Nat → Bool) → Prop} {s0 s : Solver} (h : FPost Φ s0 s) :
    FPost Φ s0 ({ s with overflowed := true } : Solver) := ⟨AF.trans_left h.af af_rfl, h.units, h.listed, h.others⟩

/-- The outcome of one resolution step. -/
def StepOK (Φ : (Nat → Bool) → Prop) (s0 : Solver) (c : CRef) (p : Nat) : Solver ⊕ (Solver × Nat × Lit) → Prop
  | .inl s => FPost Φ s0 s
  | .inr (s, u, unit) => FInv Φ s0 c (s0.crefSize c) s p u ∧ (unit = INVALID_LIT ∨ s.isAnalyzed (IDX unit) = true)

theorem failedResolve_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    (notFailed : Lit) {s : Solver} {t u : Nat} (h : FInv Φ s0 c (s0.crefSize c) s t u) {unit lit : Lit}
    (hun : unit = INVALID_LIT ∨ s.isAnalyzed (IDX unit) = true) {p : Nat} (hpt : p < t)
    (hp : s0.trailL[p]? = some lit) (hla : s.isAnalyzed (IDX lit) = true)
    (hgap : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → s.isAnalyzed (IDX l) = false) :
    StepOK Φ s0 c p (s.failedResolve notFailed lit u unit) := by
  have hlt : s0.IsTrue lit := hb.inv.core.trailTrue _ (List.mem_of_getElem? hp)
  have hll : s0.lvl lit = 1 := by
    obtain ⟨y, hy, hf, hl⟩ := h.anaAssigned _ hla
    have hnty := hb.true_on_trail hf hl
    have : NOT y = lit := hb.idx_unique hnty (List.mem_of_getElem? hp) (by rw [IDX_NOT, hy])
    rw [← this, hb.inv.core.lvlVar]; exact h.lvl_one hb hf (by omega)
  have hreas := hb.inv.reasons lit hlt (by omega)
  have eR : s.reasonIdx (IDX lit) = s0.reasonOf lit := by show s.reasonOf lit = _; rw [h.af.reasonOf]
  have eB : s.isBinaryReason (IDX lit) = s0.binOf lit := by show s.binOf lit = _; rw [h.af.binOf]
  -- the gap survives pushing literals whose negation is before `p`
  have gapPush : ∀ (s' : Solver), (∀ i, s'.isAnalyzed i = true → s.isAnalyzed i = true ∨
      ∃ x, s0.IsFalse x ∧ (∃ q < p, s0.trailL[q]? = some (NOT x)) ∧ IDX x = i) →
      ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → s'.isAnalyzed (IDX l) = false := by
    intro s' hs' q h1 h2 l hl
    cases hx : s'.isAnalyzed (IDX l)
    · rfl
    · exfalso
      rcases hs' _ hx with h' | ⟨x, hxf, ⟨q', hq', hq'x⟩, hxi⟩
      · rw [hgap q h1 h2 l hl] at h'; simp at h'
      · have : l = NOT x := hb.idx_unique (List.mem_of_getElem? hl) (List.mem_of_getElem? hq'x) (by rw [IDX_NOT, hxi])
        subst this
        have := nodup_pos_unique hb.trail_nodup hl hq'x
        omega
  unfold failedResolve
  dsimp only
  split
  · exact h.post.overflow
  rename_i hdec
  have hnd : s0.reasonOf lit ≠ DECISION_REASON := by intro e; apply hdec; rw [eR, e]; rfl
  split
  · -- binary reason
    rename_i hbin
    rw [eB] at hbin
    rcases hreas with e | ⟨b1, b2, b3⟩ | ⟨b1, _⟩
    · exact absurd e hnd
    · rw [eR]
      split
      · exact h.post
      split
      · exact h.post.overflow
      rename_i _ hl0
      have hl0' : s0.lvl (s0.reasonOf lit) ≠ 0 := by
        intro e; apply hl0
        have := (levelIdx_eq_zero s (s0.reasonOf lit)).mpr (by rw [h.af.lvl]; exact e)
        simpa using this
      have hl1 := h.lvl_one hb b3.1 hl0'
      obtain ⟨q, hq, hqx⟩ := hb.ante_before hp b3 (by omega)
      have hres : ∀ (s' : Solver), s'.isAnalyzed (IDX (s0.reasonOf lit)) = true → Resolved s0 s' lit :=
        fun s' ha => ⟨[s0.reasonOf lit], ⟨hlt, by omega, Or.inl ⟨b1, b2, rfl⟩⟩, fun x hx => by
          simp at hx; subst hx; exact Or.inr ha⟩
      split
      · rename_i hna
        have hna' : s.isAnalyzed (IDX (s0.reasonOf lit)) = false := by simpa using hna
        obtain ⟨p1, p2, p3, _⟩ := h.push hb b3.1 hl1 hna' ⟨q, by omega, hqx⟩
        have hga := gapPush (s.pushAnalyzed (IDX (s0.reasonOf lit))) (fun i hi => by
          have hsz : (IDX (s0.reasonOf lit)).toNat < s.asg.aBits.size := by
            rw [h.af.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false b3.1; unfold ValidLit at this; omega
          have : (s.pushAnalyzed (IDX (s0.reasonOf lit))).abit i ABits.analyzed = true := hi
          rw [pushAnalyzed_abit s _ i hsz _ (Or.inl rfl)] at this
          by_cases e : IDX (s0.reasonOf lit) = i
          · exact Or.inr ⟨_, b3.1, ⟨q, hq, hqx⟩, e⟩
          · simp [e] at this; exact Or.inl this)
        exact ⟨p1.move hb hpt hp (p2 _ hla) (hres _ p3) hga, hun.imp_right (p2 _)⟩
      · rename_i hna
        have ha : s.isAnalyzed (IDX (s0.reasonOf lit)) = true := by simpa using hna
        exact ⟨h.move hb hpt hp hla (hres _ ha) hgap, hun⟩
    · rw [b1] at hbin; exact absurd hbin (by simp)
  · -- large reason
    rename_i hbin
    rw [eB] at hbin
    rcases hreas with e | ⟨b1, _⟩ | ⟨b1, b2, b3, b4⟩
    · exact absurd e hnd
    · rw [b1] at hbin; exact absurd hbin (by simp)
    rw [eR]
    have hr : s0.reasonOf lit ∈ s0.arena.chain 0 s0.arena.sizeWards := b2.1
    have hsz : (s.arena.size (s0.reasonOf lit)).toNat = (s0.arena.size (s0.reasonOf lit)).toNat := by
      rw [h.af.arena.size _ hr]
    rw [hsz]
    have hante : ∀ k, k < (s0.arena.size (s0.reasonOf lit)).toNat → s0.arena.lit (s0.reasonOf lit) k ≠ lit →
        s0.Ante lit (s0.arena.lit (s0.reasonOf lit) k) :=
      fun k hk hne => b4 _ (lit_mem_litsL _ _ _ hk) hne
    obtain ⟨a1, a2, a2', _, a4⟩ := failedLarge_spec hb lit unit notFailed (s0.reasonOf lit)
      (s0.arena.size (s0.reasonOf lit)).toNat hr (Nat.le_refl _) hp hpt hante s 0 u h hun
      (fun k hk => absurd hk (by omega))
    generalize s.failedLarge lit unit notFailed (s0.reasonOf lit) 0 (s0.arena.size (s0.reasonOf lit)).toNat u = R
      at a1 a2 a2' a4 ⊢
    obtain ⟨stop, u', s'⟩ := R
    dsimp only at a1 a2 a2' a4 ⊢
    split
    · exact a1
    rename_i hstop
    have hstop' : stop = false := by simpa using hstop
    obtain ⟨k1, k2⟩ := a4 hstop'
    have hga := gapPush s' (fun i hi => by
      rcases a2' i hi with h' | ⟨k, hk, hne, hki⟩
      · exact Or.inl h'
      · have hA := hante k hk hne
        have hl0 : 0 < s0.lvl (s0.arena.lit (s0.reasonOf lit) k) := by
          obtain ⟨y', hy', hf', hl'⟩ := k1.anaAssigned _ hi
          have := hb.false_same_var hA.1 hf' (hy'.trans hki.symm); subst this; exact hl'
        obtain ⟨q, hq, hqx⟩ := hb.ante_before hp hA hl0
        exact Or.inr ⟨_, hA.1, ⟨q, hq, hqx⟩, hki⟩)
    have hres : Resolved s0 s' lit := by
      refine ⟨(s0.clauseL (s0.reasonOf lit)).filter (fun x => x != lit),
        ⟨hlt, by omega, Or.inr ⟨b1, hnd, b2, b3, fun x => by simp [List.mem_filter]⟩⟩, fun x hx => ?_⟩
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      obtain ⟨k, hk, rfl⟩ := mem_litsL_iff.mp hx1
      exact k2 k hk (by simpa using hx2)
    exact ⟨k1.move hb hpt hp (a2 _ hla) hres hga, hun.imp_right (a2 _)⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem failedStep_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    (hc : ConflictOK s0 s0 c) (notFailed : Lit) {s : Solver} {t u : Nat} (h : FInv Φ s0 c (s0.crefSize c) s t u)
    {unit : Lit} (hun : unit = INVALID_LIT ∨ s.isAnalyzed (IDX unit) = true) {p : Nat}
    (hpa : s.prevAnalyzed t = some p) :
    StepOK Φ s0 c p (s.failedStep notFailed p u unit) := by
  obtain ⟨hpt, hla, hgap⟩ := prevAnalyzed_spec s t p hpa
  have hplen : p < s0.trailL.length := by have := h.tle; omega
  have htr : s.asg.trail = s0.asg.trail := h.af.trail
  have hp : s0.trailL[p]? = some (s.asg.trail.get! p) := by
    unfold trailL at hplen ⊢
    rw [List.getElem?_eq_getElem hplen, U32Vec.get!_eq_view, htr, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hplen, Option.getD_some]
  have hgap' : ∀ q, p < q → q < t → ∀ l, s0.trailL[q]? = some l → s.isAnalyzed (IDX l) = false := by
    intro q h1 h2 l hl
    have hq : q < s0.trailL.length := (List.getElem?_eq_some_iff.mp hl).1
    have : s.asg.trail.get! q = l := by
      unfold trailL at hq hl
      rw [U32Vec.get!_eq_view, htr, List.getD_eq_getElem?_getD, hl]; rfl
    rw [← this]; exact hgap q h1 h2
  obtain ⟨w1, w2, w3, _, _⟩ := walk_unit_step hb hc h hun hpt hp hla hgap'
  unfold failedStep
  dsimp only
  by_cases hu1 : (u == 1) = true
  · rw [if_pos hu1] at w1 w3 ⊢
    rw [if_pos hu1, if_pos hu1] at w2
    exact failedResolve_spec hb notFailed w1 w2 hpt hp (by unfold Solver.isAnalyzed; rw [w3]; exact hla)
      (fun q h1 h2 l hl => by unfold Solver.isAnalyzed; rw [w3]; exact hgap' q h1 h2 l hl)
  · rw [if_neg hu1] at w1 w3 ⊢
    rw [if_neg hu1, if_neg hu1] at w2
    exact failedResolve_spec hb notFailed w1 w2 hpt hp hla hgap'

theorem failedWalk_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (hb : DBase Φ s0 1)
    (hc : ConflictOK s0 s0 c) (notFailed : Lit) :
    ∀ fuel (s : Solver) (t u : Nat) (unit : Lit), FInv Φ s0 c (s0.crefSize c) s t u →
      (unit = INVALID_LIT ∨ s.isAnalyzed (IDX unit) = true) →
      FPost Φ s0 (s.failedWalk notFailed t u unit fuel) := by
  intro fuel
  induction fuel with
  | zero => intro s t u unit h _; exact h.post
  | succ fuel ih =>
  intro s t u unit h hun
  rw [failedWalk]
  generalize hpa : s.prevAnalyzed t = P
  cases P with
  | none => exact h.post.overflow
  | some p =>
  dsimp only
  have hst := failedStep_spec hb hc notFailed h hun hpa
  generalize s.failedStep notFailed p u unit = R at hst ⊢
  cases R with
  | inl s' => exact hst
  | inr x =>
    obtain ⟨s', u', unit'⟩ := x
    obtain ⟨k1, k2⟩ := hst
    exact ih s' p u' unit' k1 k2

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The facts after the root-level units have been assigned. -/
structure UOut (Φ : (Nat → Bool) → Prop) (s t : Solver) : Prop where
  inv : SInv Φ t
  invS : ∀ c, t.InDB c → t.InvS c
  bits : ∀ i b, AnaBit b → t.abit i b = true → s.abit i b = true
  ana : anaSide t = anaSide s
  level : t.level = s.level
  mono : IrrMono s t

theorem learnUnits_spec {Φ : (Nat → Bool) → Prop} (n : Nat) :
    ∀ (s : Solver) (i : Nat), SInv Φ s → (∀ c, s.InDB c → s.InvS c) → s.level = 0 →
      (∀ j, i ≤ j → j < n → Implied Φ [s.clause.get! j] ∧ s.ValidLit (s.clause.get! j)) →
      (s.learnUnits i n).overflowed = true ∨ UOut Φ s (s.learnUnits i n) := by
  intro s i
  fun_induction learnUnits s i n with
  | case1 s i hi lit hv =>
    intro _ _ _ _; left; rfl
  | case2 s i hi lit hv ih =>
    intro hs hinv hl0 hu
    have hval : s.asg.values.get! lit.toNat = 0 := by simpa [value] using hv
    have hun : ¬ s.IsTrue lit ∧ ¬ s.IsFalse lit := by unfold IsTrue IsFalse; rw [hval]; simp [VAL_TRUE, VAL_FALSE]
    obtain ⟨hi1, hi2⟩ := hu i (Nat.le_refl _) hi
    obtain ⟨a1, a2, _, a4⟩ := assign_sinv hs (probing := s.probing) (k := 0) (bb := false) (rr := UNIT_REASON)
      hi2 hun (by simp) (fun h0 => absurd rfl h0) (fun _ => hi1)
    have hana : anaSide (s.learnedUnit lit) = anaSide s := assign_anaSide _ _ _ _ _ _
    have hcl : (s.learnedUnit lit).clause = s.clause := by
      have := hana; simp only [anaSide, Prod.mk.injEq] at this; exact this.1
    have hlev : (s.learnedUnit lit).level = s.level := by
      show (s.assign s.probing 0 false lit UNIT_REASON).level = _
      rw [assign_eq]; split
      · exact (markFixedLiteral_same s lit).level
      · rfl
    have hvars : (s.learnedUnit lit).vars = s.vars := by
      show (s.assign s.probing 0 false lit UNIT_REASON).vars = _
      rw [assign_eq]; split
      · exact (markFixedLiteral_same s lit).vars
      · rfl
    have hinv' : ∀ c, (s.learnedUnit lit).InDB c → (s.learnedUnit lit).InvS c := by
      intro c hc
      have hc' : s.InDB c := by
        have e := inDB_congr (t := s.learnedUnit lit) (s := s) (by
          show (s.assign s.probing 0 false lit UNIT_REASON).watches = _
          rw [assign_eq]; split
          · exact (markFixedLiteral_same s lit).watches
          · rfl) (by
          show (s.assign s.probing 0 false lit UNIT_REASON).arena = _
          rw [assign_eq]; split
          · exact (markFixedLiteral_same s lit).arena
          · rfl) c
        exact e.mp hc
      unfold InvS
      have := a4; show (s.assign s.probing 0 false lit UNIT_REASON).InvSAt (s.assign s.probing 0 false lit UNIT_REASON).propagate c
      rw [a4]; exact a2 _ c hs.levelOK.propLe (hinv c hc')
    rcases ih a1 hinv' (by rw [hlev, hl0]) (fun j hj1 hj2 => by
      rw [hcl]; obtain ⟨u1, u2⟩ := hu j (by omega) hj2
      exact ⟨u1, by unfold ValidLit at *; rw [hvars]; exact u2⟩) with h' | h'
    · exact Or.inl h'
    · right
      exact ⟨h'.inv, h'.invS, fun j b hb hj => assign_abit_le _ _ _ _ _ _ j b hb (h'.bits j b hb hj),
        by rw [h'.ana, hana], by rw [h'.level, hlev],
        (show IrrMono s (s.learnedUnit lit) from assign_irrMono hs.core hi2 hun).trans h'.mono⟩
  | case3 s i hi =>
    intro hs hinv _ _
    right
    exact ⟨hs, hinv, fun _ _ _ h => h, rfl, rfl, IrrMono.refl _⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- Preconditions of the failed-literal analysis. -/
structure FPre (Φ : (Nat → Bool) → Prop) (s : Solver) (c : CRef) : Prop where
  inv : SInv Φ s
  level : s.level.toNat = 1
  conflict : ConflictOK s s c
  invP : ∀ d, s.InDB d → s.InvSAt (s.framesL[0]!) d
  clean : ∀ i b, AnaBit b → s.abit i b = false
  clauseEmpty : s.clause.size = 0
  listed : Listed s

/-- The result of the failed-literal analysis (unless flagged). -/
structure FOut (Φ : (Nat → Bool) → Prop) (s t : Solver) : Prop where
  inv : SInv Φ t
  invS : ∀ c, t.InDB c → t.InvS c
  listed : Listed t
  others : ∀ i b, (b = ABits.poisoned ∨ b = ABits.removable ∨ b = ABits.shrinkable) → t.abit i b = false
  clauseEmpty : t.clause.size = 0
  incons : Flg t = Flg s
  mono : IrrMono s t

theorem decisionsOK_congr {s t : Solver} (ht : t.asg.trail = s.asg.trail) (hr : t.asg.aReason = s.asg.aReason)
    (failed : Lit) : ∀ i n, t.decisionsOK failed i n = s.decisionsOK failed i n := by
  intro i n
  fun_induction decisionsOK s failed i n with
  | case1 i hi x ih => rw [decisionsOK, dif_pos hi, ih]; simp [reasonIdx, ht, hr, x]
  | case2 i hi => rw [decisionsOK, dif_neg hi]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem failedCollect_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (h : FPre Φ s c) (notFailed : Lit) :
    FPost Φ s (s.failedCollect c notFailed) := by
  have hb : DBase Φ s 1 := ⟨h.inv, h.level, by omega⟩
  have hcv : s.clause.view = [] := List.eq_nil_of_length_eq_zero (by simp [h.clauseEmpty])
  have hF0 : FInv Φ s c 0 s s.trailL.length 0 := by
    refine ⟨AF.refl _, fun y _ _ hy => ?_, fun i hi => ?_, ?_, Nat.le_refl _, fun k hk => absurd hk (by omega),
      fun x hx => by rw [hcv] at hx; simp at hx, h.listed, fun i b hb' => h.clean i b
        (by rcases hb' with rfl | rfl | rfl <;> simp [AnaBit])⟩
    · rw [show s.isAnalyzed (IDX y) = false from h.clean _ _ anaBit_analyzed] at hy; simp at hy
    · rw [show s.isAnalyzed i = false from h.clean _ _ anaBit_analyzed] at hi; simp at hi
    · unfold pendCount; symm; rw [List.countP_eq_zero]; intro l _
      unfold anaP; rw [show s.isAnalyzed (IDX l) = false from h.clean _ _ anaBit_analyzed]; simp
  obtain ⟨i1, i2⟩ := failedInit_spec hb h.conflict notFailed s 0 0 hF0 (Nat.zero_le _)
    (fun k _ _ => h.clean _ _ anaBit_analyzed) (fun _ => rfl)
  unfold failedCollect
  generalize s.failedInit c notFailed (s.crefSize c) 0 0 = R at i1 i2 ⊢
  obtain ⟨done, u, s1⟩ := R
  dsimp only at i1 i2 ⊢
  split
  · exact i1
  · rename_i hd
    obtain ⟨k1, _⟩ := i2 (by simpa using hd)
    have htr : s1.asg.trail.size = s.trailL.length := by
      unfold trailL; rw [k1.af.trail]; simp
    rw [htr]
    exact failedWalk_spec hb h.conflict _ _ s1 _ u INVALID_LIT k1 (Or.inl rfl)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem Listed.of_le {s t : Solver} (h : Listed s) (hb : ∀ i b, AnaBit b → t.abit i b = true → s.abit i b = true)
    (hl : anaRest t = anaRest s) : Listed t := by
  intro b hbit i hi
  have := h b hbit i (hb i b hbit hi)
  have hl' := hl; unfold anaRest anaSide at hl'; simp only [Prod.mk.injEq] at hl'
  obtain ⟨e1, e2, e3, e4, _⟩ := hl'
  unfold anaList at this ⊢
  rw [e1, e2, e3, e4]; exact this

theorem failedFinish_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {c : CRef} (h : FPre Φ s0 c) {s : Solver}
    (hp : FPost Φ s0 s) :
    (s.failedFinish (s0.frameDecisionAt 1)).overflowed = true ∨ FOut Φ s0 (s.failedFinish (s0.frameDecisionAt 1)) := by
  have hb : DBase Φ s0 1 := ⟨h.inv, h.level, by omega⟩
  generalize hfd : s0.frameDecisionAt 1 = failed
  unfold failedFinish
  split
  · left; assumption
  split
  · left; rfl
  rename_i hov hchk
  have hchk' : (s.value failed == VAL_TRUE && s.decisionsOK failed (s.frameTrailAt 1).toNat s.asg.trail.size) = true := by
    simpa using hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk'
  obtain ⟨hft, hdec⟩ := hchk'
  have hdec0 : s0.decisionsOK failed (s0.frameTrailAt 1).toNat s0.asg.trail.size = true := by
    rw [← decisionsOK_congr hp.af.trail hp.af.aReason, ← hdec]
    unfold frameTrailAt; rw [hp.af.frameTrail, hp.af.trail]
  have himp : Implied Φ [NOT failed] := failed_notFailed hb h.conflict hdec0
  have hft0 : s0.IsTrue failed := by unfold IsTrue; rw [← hp.af.values]; exact hft
  have hvf : s0.ValidLit (NOT failed) := by
    have := hb.inv.rsizes.valid hft0; unfold ValidLit at *; rw [IDX_NOT]; exact this
  have hs1 : SInv Φ s := hp.af.sinv h.inv
  generalize hs2 : ({ s with clause := s.clause.push (NOT failed) } : Solver) = s2
  unfold failedLearn
  dsimp only
  have hS2 : Same s2 s := by rw [← hs2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcl2 : s2.clause = s.clause.push (NOT failed) := by rw [← hs2]
  have hab2 : ∀ i b, s2.abit i b = s.abit i b := by intro i b; rw [← hs2]; rfl
  have hrest2 : anaRest s2 = anaRest s := by rw [← hs2]; rfl
  have hq3 : Quiet (if !s2.probing then s2.updateLearned 0 1 else s2) s2 := by
    split
    · exact updateLearned_quiet _ _ _
    · exact Quiet.refl _
  generalize (if !s2.probing then s2.updateLearned 0 1 else s2) = s3 at hq3
  have hS3 : Same s3 s := ⟨hq3.same.asg.trans hS2.asg, hq3.same.arena.trans hS2.arena, hq3.same.watches.trans hS2.watches,
    hq3.same.delayed.trans hS2.delayed, hq3.same.vars.trans hS2.vars, hq3.same.level.trans hS2.level,
    hq3.same.frameTrail.trans hS2.frameTrail, hq3.same.propagate.trans hS2.propagate, hq3.same.options.trans hS2.options⟩
  have hs3 : SInv Φ s3 := hS3.sinv hs1
  have hlev3 : s3.level.toNat = 1 := by rw [hS3.level, hp.af.level, h.level]
  have hlt3 : (0 : UInt32) < s3.level := by rw [UInt32.lt_iff_toNat_lt, hlev3]; decide
  have hfr3 : s3.framesL = s0.framesL := by unfold framesL; rw [hS3.frameTrail, hp.af.frameTrail]
  have hlen0 : 0 < s0.framesL.length := by rw [h.inv.levelOK.len, h.level]; omega
  have hP3 : ∀ d, s3.InDB d → s3.InvSAt (s3.framesL[0]'(by rw [hfr3]; exact hlen0)) d := by
    intro d hd
    have hd0 : s0.InDB d := (hp.af.inDB d).mp ((hS3.inDB d).mp hd)
    have := h.invP d hd0
    rw [getElem!_pos s0.framesL 0 hlen0] at this
    have e1 : s3.InvSAt (s0.framesL[0]'hlen0) d ↔ s.InvSAt (s0.framesL[0]'hlen0) d :=
      invSAt_congr hS3.asg hS3.frameTrail _ d
    simp only [hfr3]
    exact e1.mpr ((hp.af.invSAt _ d).mpr this)
  obtain ⟨b1, b2, _, b4, b5⟩ := backtrack_spec hs3 hlt3 hP3 (Nat.le_refl _)
  have ba := backtrack_anaSide s3 0
  generalize s3.backtrackWithoutUpdatingPhases 0 = s4 at b1 b2 b4 b5 ba
  have hcl4 : s4.clause = s.clause.push (NOT failed) := by
    have := ba; simp only [anaSide, Prod.mk.injEq] at this; rw [this.1, hq3.clause, hcl2]
  have hunits : ∀ j, 0 ≤ j → j < s4.clause.size → Implied Φ [s4.clause.get! j] ∧ s4.ValidLit (s4.clause.get! j) := by
    intro j _ hj
    have hm := U32Vec.get!_mem_view _ _ hj
    generalize s4.clause.get! j = x at hm ⊢
    rw [hcl4, U32Vec.view_push] at hm
    have hv4 : s4.vars = s0.vars := by rw [b5.vars, hS3.vars, hp.af.vars]
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨u1, u2⟩ := hp.units _ hm
      exact ⟨u1, by unfold ValidLit at *; rw [hv4]; exact u2⟩
    · simp at hm; rw [hm]; exact ⟨himp, by unfold ValidLit at *; rw [hv4]; exact hvf⟩
  rcases learnUnits_spec s4.clause.size s4 0 b1 b4 b2 hunits with hov5 | hU
  · left
    generalize s4.learnUnits 0 s4.clause.size = s5 at hov5 ⊢
    split <;> exact hov5
  · right
    generalize s4.learnUnits 0 s4.clause.size = s5 at hU ⊢
    have key : ∀ t : Solver, Same t s5 → anaRest t = anaRest s5 → (∀ i b, t.abit i b = s5.abit i b) →
        t.clause.size = 0 → FOut Φ s0 t := by
      intro t hS7 hr7 hb7 hc7
      have hbits7 : ∀ i b, AnaBit b → t.abit i b = true → s.abit i b = true := by
        intro i b hb' h7
        rw [hb7] at h7
        have h4 := hU.bits i b hb' h7
        have e2 : s4.abit i b = s3.abit i b := by unfold Solver.abit Solver.abits; rw [b5.aBits]
        rw [e2, hq3.abit, hab2] at h4; exact h4
      have hrest7 : anaRest t = anaRest s := by
        rw [hr7]; unfold anaRest at *; rw [hU.ana, ba, hq3.ana]; exact hrest2
      have hinc : Flg t = Flg s0 := (flg_of_anaRest hrest7).trans hp.af.flg
      refine ⟨hS7.sinv hU.inv, fun d hd => ?_, hp.listed.of_le hbits7 hrest7, fun i b hb' => ?_, hc7, hinc,
        (((hp.af.irrMono.trans (IrrMono.of_eq hS3.asg hS3.arena hS3.watches)).trans b5.irrMono).trans
          hU.mono).trans (IrrMono.of_eq hS7.asg hS7.arena hS7.watches)⟩
      · unfold InvS; rw [invSAt_congr hS7.asg hS7.frameTrail, hS7.propagate]
        exact hU.invS d ((hS7.inDB d).mp hd)
      · cases e : t.abit i b
        · rfl
        · exfalso
          have := hbits7 i b (by rcases hb' with rfl | rfl | rfl <;> simp [AnaBit]) e
          rw [hp.others i b hb'] at this; simp at this
    split
    · exact key _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (fun _ _ => rfl)
        (by simp [U32Vec.clear, U32Vec.size_shrink])
    · exact key _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (fun _ _ => rfl)
        (by simp [U32Vec.clear, U32Vec.size_shrink])

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem analyzeFailedLiteral_spec {Φ : (Nat → Bool) → Prop} {s : Solver} {c : CRef} (h : FPre Φ s c) :
    (s.analyzeFailedLiteral c).overflowed = true ∨ FOut Φ s (s.analyzeFailedLiteral c) :=
  failedFinish_spec h (failedCollect_spec h _)

end Solver
end LeanKissat
