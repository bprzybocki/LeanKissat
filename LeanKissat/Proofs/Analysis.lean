import LeanKissat.Proofs.SortSpec

/-!
# The learned clause of conflict analysis

Composition of first-UIP deduction, sorting, minimization and shrinking: every literal of
the conflict clause is derivable from the final clause buffer.
-/

namespace LeanKissat
namespace Solver

theorem markClauseRemovable_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (n : Nat) :
    ∀ (s : Solver) (i : Nat), AF s s0 → Good s0 s B → s.clause.view = B → n ≤ s.clause.size →
    (∀ q, i ≤ q → q < n → s0.IsFalse (s.clause.get! q) ∧ 0 < s0.lvl (s.clause.get! q)) →
    MF (s.markClauseRemovable i n) s ∧ Good s0 (s.markClauseRemovable i n) B ∧
    ∀ q, i ≤ q → q < n → (s.markClauseRemovable i n).isRem (IDX (s.clause.get! q)) = true := by
  intro s i
  fun_induction markClauseRemovable s i n with
  | case1 s i hi ih =>
    intro hs hg hcl hn hpre
    obtain ⟨hf, hl⟩ := hpre i (Nat.le_refl _) hi
    have hsz : (IDX (s.clause.get! i)).toNat < s.asg.aBits.size := by
      rw [hs.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf; unfold ValidLit at this; omega
    obtain ⟨p1, p2, _, _⟩ := pushRemovable_mf s _ hsz
    have hg' := GoodE.push hb hg hs hf hl (Or.inl (by rw [← hcl]; exact get!_mem_view _ _ (by omega)))
    have hcl' := p1.clause
    obtain ⟨a1, a2, a3⟩ := ih (p1.af.trans hs) hg' (by rw [hcl']; exact hcl) (by rw [hcl']; exact hn)
      (fun q hq1 hq2 => by rw [hcl']; exact hpre q (by omega) hq2)
    refine ⟨a1.trans p1, a2, fun q hq1 hq2 => ?_⟩
    by_cases e : q = i
    · subst e; exact a1.rem _ p2
    · rw [← hcl']; exact a3 q (by omega) hq2
  | case2 s i hi =>
    intro _ hg _ _ _
    exact ⟨MF.refl _, hg, fun q hq1 hq2 => absurd hq2 (by omega)⟩

theorem minimizeLit_block {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (h : BPre s0 s) {p : Nat} (hp : p < s.clause.size) (hne : s.clause.get! p ≠ INVALID_LIT)
    (m : Bool) :
    MF (s.minimizeLiteral m s.options.minimizedepth (s.clause.get! p) 0).2 s ∧
    Good s0 (s.minimizeLiteral m s.options.minimizedepth (s.clause.get! p) 0).2 s.clause.view ∧
    ((s.minimizeLiteral m s.options.minimizedepth (s.clause.get! p) 0).1 = true →
      RCE s0 (s.minimizeLiteral m s.options.minimizedepth (s.clause.get! p) 0).2 [] (s.clause.get! p)) := by
  obtain ⟨hf, hl⟩ := h.lits p hp hne
  obtain ⟨m1, m2, _, m4⟩ := (minimize_all hb s.clause.view m s.options.minimizedepth).1 s
    (s.clause.get! p) 0 h.af h.good hf
  refine ⟨m1, m2, fun hok => ?_⟩
  rcases m4 hok with h' | ⟨h', _⟩ | ⟨_, h'⟩
  · omega
  · exact absurd rfl h'
  · exact h'

/-- Removing the literal at `p` (justified by a closed reason) keeps `BPre`. -/
theorem BPre.invalidate {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (_hb : DBase Φ s0 L)
    {s s' : Solver} (h : BPre s0 s) (t1 : MF s' s) (t2 : Good s0 s' s.clause.view) {p : Nat}
    (hp : p < s.clause.size) (hrce : RCE s0 s' [] (s.clause.get! p)) :
    BPre s0 { s' with clause := s'.clause.set! p INVALID_LIT } ∧
    (∀ q, ({ s' with clause := s'.clause.set! p INVALID_LIT } : Solver).clause.get! q =
      if q = p then INVALID_LIT else s.clause.get! q) ∧
    ({ s' with clause := s'.clause.set! p INVALID_LIT } : Solver).clause.size = s.clause.size ∧
    (∀ j, s'.isRem j = true → ({ s' with clause := s'.clause.set! p INVALID_LIT } : Solver).isRem j = true) := by
  have hcl := t1.clause
  generalize hs2 : ({ s' with clause := s'.clause.set! p INVALID_LIT } : Solver) = s2
  have cl2 : s2.clause = s.clause.set! p INVALID_LIT := by rw [← hs2, hcl]
  have hget2 : ∀ q, s2.clause.get! q = if q = p then INVALID_LIT else s.clause.get! q := by
    intro q; rw [cl2, U32Vec.get!_set!]
    by_cases eq : q = p
    · subst eq; simp [hp]
    · simp [Ne.symm eq, eq]
  have hsz2 : s2.clause.size = s.clause.size := by rw [cl2]; simp
  refine ⟨?_, hget2, hsz2, fun j hj => by rw [← hs2]; exact hj⟩
  have hb' := BPre.of_mf h t1 t2
  refine ⟨by rw [← hs2]; exact AF.trans_left hb'.af af_rfl, ?_, by rw [← hs2]; exact hb'.listed,
    by rw [← hs2]; exact hb'.noSh, fun q hq hne' => ?_⟩
  · have hg : Good s0 s2 s.clause.view := by rw [← hs2]; exact t2
    apply Good.replace hg
    intro y hy _ _
    by_cases eq : y = s.clause.get! p
    · right; rw [eq]; exact hrce.mono (fun i h' => by rw [← hs2]; exact h') (fun j hj => by simp at hj)
    · left
      obtain ⟨q, hq, hqy⟩ := mem_view_pos _ _ hy
      have hqp : q ≠ p := by intro e'; subst e'; exact eq hqy.symm
      have := get!_mem_view s2.clause q (by rw [hsz2]; exact hq)
      rw [hget2, ite_eq_right hqp, hqy] at this; exact this
  · rw [hget2] at hne' ⊢
    by_cases eq : q = p
    · rw [ite_eq_left eq] at hne'; exact absurd rfl hne'
    · rw [ite_eq_right eq] at hne' ⊢; exact h.lits q (by rw [← hsz2]; exact hq) hne'

theorem minimizeDown_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) :
    ∀ (i : Nat) (s : Solver), BPre s0 s → i ≤ s.clause.size →
    (∀ q, q < i → s.clause.get! q ≠ INVALID_LIT) →
    BPre s0 (s.minimizeDown i) ∧ (s.minimizeDown i).clause.size = s.clause.size ∧
    (∀ j, s.isRem j = true → (s.minimizeDown i).isRem j = true) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro s h hi hpre
    match i, ih, hi, hpre with
    | 0, _, _, _ => exact ⟨h, rfl, fun _ h => h⟩
    | 1, _, _, _ => exact ⟨h, rfl, fun _ h => h⟩
    | k + 2, ih, hi, hpre =>
      rw [minimizeDown]
      have hne := hpre (k + 1) (by omega)
      obtain ⟨t1, t2, t3⟩ := minimizeLit_block hb h (p := k + 1) (by omega) hne true
      generalize s.minimizeLiteral true s.options.minimizedepth (s.clause.get! (k + 1)) 0 = R at t1 t2 t3 ⊢
      obtain ⟨ok, s'⟩ := R
      simp only at t1 t2 t3 ⊢
      cases ok
      · simp only [Bool.false_eq_true, ite_false]
        have hcl := t1.clause
        obtain ⟨a1, a2, a3⟩ := ih (k + 1) (by omega) s' (BPre.of_mf h t1 t2) (by rw [hcl]; omega)
          (fun q hq => by rw [hcl]; exact hpre q (by omega))
        exact ⟨a1, by rw [a2, hcl], fun j hj => a3 j (t1.rem j hj)⟩
      · simp only [ite_true]
        obtain ⟨b1, b2, b3, b4⟩ := BPre.invalidate hb h t1 t2 (p := k + 1) (by omega) (t3 rfl)
        generalize ({ s' with clause := s'.clause.set! (k + 1) INVALID_LIT } : Solver) = s2 at b1 b2 b3 b4 ⊢
        obtain ⟨a1, a2, a3⟩ := ih (k + 1) (by omega) s2 b1 (by rw [b3]; omega)
          (fun q hq => by rw [b2, ite_eq_right (by omega)]; exact hpre q (by omega))
        exact ⟨a1, by rw [a2, b3], fun j hj => a3 j (b4 j (t1.rem j hj))⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Compaction followed by `resetPoisoned`. -/
theorem compactReset_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s1 : Solver} (l1 : BPre s0 s1) :
    BPre s0 s1.compactClause.resetPoisoned ∧
    (∀ q, q < s1.compactClause.resetPoisoned.clause.size →
      s1.compactClause.resetPoisoned.clause.get! q ≠ INVALID_LIT) ∧
    (∀ i, s1.compactClause.resetPoisoned.abit i ABits.poisoned = false) ∧
    (∀ i, s1.compactClause.resetPoisoned.isRem i = s1.isRem i) ∧
    s1.compactClause.resetPoisoned.options = s1.options := by
  have hv := compactClause_view s1
  have e2 : s1.compactClause = { s1 with clause := (compactLoop s1.clause 0 0).1.shrink (compactLoop s1.clause 0 0).2 } :=
    compactClause_eq s1
  generalize s1.compactClause = s2 at hv e2 ⊢
  have a2 : AF s2 s1 := by rw [e2]; exact af_rfl
  have li2 : Listed s2 := by rw [e2]; exact l1.listed
  have hmem : ∀ y ∈ s2.clause.view, y ∈ s1.clause.view ∧ y ≠ INVALID_LIT := by
    intro y hy; rw [hv, List.mem_filter] at hy; exact ⟨hy.1, by simpa using hy.2⟩
  have g2 : Good s0 s2 s2.clause.view := by
    have : Good s0 s2 s1.clause.view := by rw [e2]; exact l1.good
    apply Good.replace this
    intro y hy hf _
    left; rw [hv, List.mem_filter]
    exact ⟨hy, by simp; intro e; subst e; exact hb.invalid_not_false hf⟩
  obtain ⟨r1, r2, r3, r4, r5, _, _, r8⟩ := resetPoisoned_spec s2 li2
  have hsh2 : ∀ i, s2.isSh i = s1.isSh i := by intro i; rw [e2]; rfl
  have hrem2 : ∀ i, s2.isRem i = s1.isRem i := by intro i; rw [e2]; rfl
  have hopt : s2.options = s1.options := by rw [e2]
  have hnoinv : ∀ q, q < s2.resetPoisoned.clause.size → s2.resetPoisoned.clause.get! q ≠ INVALID_LIT := by
    intro q hq
    rw [r3] at hq ⊢
    exact (hmem _ (get!_mem_view _ _ hq)).2
  refine ⟨⟨r1.trans (a2.trans l1.af), ?_, r8, fun i => ?_, fun q hq hne => ?_⟩, hnoinv, r4,
    fun i => by rw [r2, hrem2], by rw [← hopt]; exact r1.options⟩
  · rw [r3]; exact g2.mono_mf (fun j => by rw [r2])
  · unfold isSh; rw [r5 i _ (Or.inr (Or.inl rfl))]; show s2.isSh i = false; rw [hsh2]; exact l1.noSh i
  · rw [r3] at hq hne ⊢
    obtain ⟨hy1, _⟩ := hmem _ (get!_mem_view _ _ hq)
    obtain ⟨q', hq', hqy⟩ := mem_view_pos _ _ hy1
    rw [← hqy] at hne ⊢
    exact l1.lits q' hq' hne

theorem minimizeClause_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (hs : AF s s0) (hl : Listed s) (hnr : ∀ i, s.isRem i = false) (hns : ∀ i, s.isSh i = false)
    (hlits : ∀ q, q < s.clause.size → s0.IsFalse (s.clause.get! q) ∧ 0 < s0.lvl (s.clause.get! q)) :
    BPre s0 s.minimizeClause ∧
    (∀ q, q < s.minimizeClause.clause.size → s.minimizeClause.clause.get! q ≠ INVALID_LIT) ∧
    (∀ y ∈ s.clause.view, s.minimizeClause.isRem (IDX y) = true) ∧
    (s.options.shrink ≤ 2 → ∀ i, s.minimizeClause.abit i ABits.poisoned = false) ∧
    s.minimizeClause.options = s.options := by
  have hg0 : Good s0 s s.clause.view := by intro i hi; rw [hnr] at hi; exact absurd hi (by simp)
  obtain ⟨m1, m2, m3⟩ := markClauseRemovable_spec hb s.clause.view s.clause.size s 0 hs hg0 rfl (Nat.le_refl _)
    (fun q _ hq => hlits q hq)
  have hcl := m1.clause
  have hb1 : BPre s0 (s.markClauseRemovable 0 s.clause.size) := by
    refine ⟨m1.af.trans hs, by rw [hcl]; exact m2, m1.listed hl, fun i => ?_, fun q hq hne => ?_⟩
    · have := m1.shrinkable i; unfold isSh; rw [this]; exact hns i
    · rw [hcl] at hq ⊢; exact hlits q hq
  have hrem1 : ∀ y ∈ s.clause.view, (s.markClauseRemovable 0 s.clause.size).isRem (IDX y) = true := by
    intro y hy
    obtain ⟨q, hq, hqy⟩ := mem_view_pos _ _ hy
    rw [← hqy]; exact m3 q (Nat.zero_le _) hq
  have hopt1 : (s.markClauseRemovable 0 s.clause.size).options = s.options := m1.af.options
  have hnoinv1 : ∀ q, q < (s.markClauseRemovable 0 s.clause.size).clause.size →
      (s.markClauseRemovable 0 s.clause.size).clause.get! q ≠ INVALID_LIT := by
    intro q hq; rw [hcl] at hq ⊢; intro e
    have := (hlits q hq).1; rw [e] at this; exact hb.invalid_not_false this
  unfold minimizeClause
  simp only
  generalize s.markClauseRemovable 0 s.clause.size = s1 at hb1 hrem1 hopt1 hnoinv1 hcl ⊢
  split
  · rename_i h2
    exact ⟨hb1, hnoinv1, hrem1, fun h' => absurd h2 (by rw [hopt1]; omega), hopt1⟩
  · obtain ⟨d1, d2, d3⟩ := minimizeDown_spec hb s.clause.size s1 hb1 (by rw [hcl]; exact Nat.le_refl _)
      (fun q hq => hnoinv1 q (by rw [hcl]; exact hq))
    have hopt2 : (s1.minimizeDown s.clause.size).options = s1.options := d1.af.options.trans hb1.af.options.symm
    obtain ⟨c1, c2, c3, c4, c5⟩ := compactReset_spec hb d1
    exact ⟨c1, c2, fun y hy => by rw [c4]; exact d3 _ (hrem1 y hy), fun _ => c3, by rw [c5, hopt2, hopt1]⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem DFinal.lits {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) {s : Solver}
    (h : DFinal s0 L s) :
    ∀ y ∈ s.clause.view, s0.IsFalse y ∧ 0 < s0.lvl y := by
  obtain ⟨uip, h0, hu, hul, _⟩ := h.uip
  intro y hy
  have hv : s.clause.view = NOT uip :: s.clause.view.drop 1 := by
    cases hc : s.clause.view with
    | nil => rw [hc] at h0; simp at h0
    | cons a t => rw [hc] at h0; simp at h0; subst h0; rfl
  rw [hv] at hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact ⟨(hb.inv.core.valCons uip).1.mp hu, by rw [hb.inv.core.lvlVar, hul]; exact hb.pos⟩
  · obtain ⟨a, b, _⟩ := h.tail y hy; exact ⟨a, b⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem DFinal.listed {s0 : Solver} {L : Nat} {s : Solver} (h : DFinal s0 L s) : Listed s := by
  intro c hc i hi
  rcases hc with rfl | rfl | rfl | rfl
  · have := h.list i hi; simpa [anaList] using this
  · rw [h.others i _ (Or.inl rfl)] at hi; exact absurd hi (by simp)
  · rw [h.others i _ (Or.inr (Or.inl rfl))] at hi; exact absurd hi (by simp)
  · rw [h.others i _ (Or.inr (Or.inr rfl))] at hi; exact absurd hi (by simp)

/-- The clause after minimization: false literals of positive level from which every
  deduced literal is derivable. -/
structure MOut (s0 : Solver) (B0 : List Lit) (t : Solver) : Prop where
  af : AF t s0
  lits : ∀ y ∈ t.clause.view, s0.IsFalse y ∧ 0 < s0.lvl y
  der : ∀ y ∈ B0, DerFalse s0 t.clause.view y
  listed : Listed t
  noSh : ∀ i, t.isSh i = false
  noPoison : ∀ i, t.abit i ABits.poisoned = false

theorem BPre.view_lits {s0 s : Solver} (h : BPre s0 s)
    (hn : ∀ q, q < s.clause.size → s.clause.get! q ≠ INVALID_LIT) :
    ∀ y ∈ s.clause.view, s0.IsFalse y ∧ 0 < s0.lvl y := by
  intro y hy
  obtain ⟨q, hq, hqy⟩ := mem_view_pos _ _ hy
  rw [← hqy]; exact h.lits q hq (hn q hq)

theorem minimizeDeduced_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (h : DFinal s0 L s) :
    s.minimizeDeduced.overflowed = true ∨ MOut s0 s.clause.view s.minimizeDeduced := by
  have hlits0 := h.lits hb
  have hl0 := h.listed
  unfold minimizeDeduced
  split
  · rcases sortDeducedClause_spec s with ho | ⟨sh, st, e2, hin, hout⟩
    · left; simp only; rw [ite_eq_left ho]; exact ho
    rw [e2]
    simp only
    generalize hs2 : ({ s with clause := sh, frameUsed := st } : Solver) = s2
    have hov : s2.overflowed = s.overflowed := by rw [← hs2]
    have hcl2 : s2.clause = sh := by rw [← hs2]
    by_cases hof : s.overflowed = true
    · left; rw [ite_eq_left hof, hov]; exact hof
    rw [ite_eq_right hof]
    right
    have a2 : AF s2 s0 := by rw [← hs2]; exact AF.trans_left h.af af_rfl
    have l2 : Listed s2 := by rw [← hs2]; exact hl0
    have nr2 : ∀ i, s2.isRem i = false := by intro i; rw [← hs2]; exact h.others i _ (Or.inr (Or.inl rfl))
    have ns2 : ∀ i, s2.isSh i = false := by intro i; rw [← hs2]; exact h.others i _ (Or.inr (Or.inr rfl))
    have hl2 : ∀ q, q < s2.clause.size → s0.IsFalse (s2.clause.get! q) ∧ 0 < s0.lvl (s2.clause.get! q) := by
      intro q hq; rw [hcl2] at hq ⊢; exact hlits0 _ (hin _ (get!_mem_view _ _ hq))
    obtain ⟨m1, m2, m3, m4, m5⟩ := minimizeClause_spec hb a2 l2 nr2 ns2 hl2
    have hB : ∀ y ∈ s.clause.view, s2.minimizeClause.isRem (IDX y) = true := by
      intro y hy; apply m3; rw [hcl2]; exact hout y hy
    have hopt : s2.minimizeClause.options = s2.options := m5
    generalize s2.minimizeClause = s3 at m1 m2 m3 m4 m5 hB hopt ⊢
    split
    · obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := shrinkClause_spec hb m1 m2
      exact ⟨r1, fun y hy => (r6 y hy).2, fun y hy => derFalse_of_good hb r2 y (hlits0 y hy).1 (hlits0 y hy).2 (r7 _ (hB y hy)),
        r3, r4, r5⟩
    · rename_i hsh
      have hsh' : s2.options.shrink = 0 := by rw [← hopt]; simpa using hsh
      exact ⟨m1.af, m1.view_lits m2, fun y hy => derFalse_of_good hb m1.good y (hlits0 y hy).1 (hlits0 y hy).2
        (hB y hy), m1.listed, m1.noSh, m4 (by omega)⟩
  · right
    exact ⟨h.af, hlits0, fun y hy => .inK hy, hl0, fun i => h.others i _ (Or.inr (Or.inr rfl)),
      fun i => h.others i _ (Or.inl rfl)⟩

end Solver
end LeanKissat
