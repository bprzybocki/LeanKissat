import LeanKissat.Proofs.Minimize

/-!
# Soundness of clause shrinking
-/

namespace LeanKissat
namespace Solver

def isSh (s : Solver) (i : UInt32) : Bool := s.abit i ABits.shrinkable

/-- Frame for shrinking steps: like `MF` but shrinkable marks may grow. -/
structure SF (t s : Solver) : Prop where
  af : AF t s
  clause : t.clause = s.clause
  rem : ∀ i, s.isRem i = true → t.isRem i = true
  listed : Listed s → Listed t

theorem SF.refl (s : Solver) : SF s s := ⟨AF.refl _, rfl, fun _ h => h, id⟩
theorem SF.trans {a b c : Solver} (h1 : SF a b) (h2 : SF b c) : SF a c :=
  ⟨h1.af.trans h2.af, h1.clause.trans h2.clause, fun i h => h1.rem i (h2.rem i h),
   fun h => h1.listed (h2.listed h)⟩
theorem MF.sf {t s : Solver} (h : MF t s) : SF t s := ⟨h.af, h.clause, h.rem, h.listed⟩

theorem pushShrinkable_spec (s : Solver) (idx : UInt32) (hsz : idx.toNat < s.asg.aBits.size) :
    SF (s.pushShrinkable idx) s ∧ (∀ i, (s.pushShrinkable idx).isRem i = s.isRem i) ∧
    (∀ i, (s.pushShrinkable idx).isSh i = true ↔ s.isSh i = true ∨ i = idx) ∧
    (s.pushShrinkable idx).shrinkable.view = s.shrinkable.view ++ [idx] ∧
    (s.pushShrinkable idx).minimize = s.minimize := by
  have hb : ∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.removable ∨ c = ABits.shrinkable) →
      (s.pushShrinkable idx).abit i c = if idx = i ∧ ABits.shrinkable = c then true else s.abit i c := by
    intro i c hc
    show (s.setABit idx ABits.shrinkable true).abit i c = _
    rw [abit_setABit s idx i _ c true hsz]
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inl ⟨rfl, by decide⟩
  have hr : ∀ i, (s.pushShrinkable idx).isRem i = s.isRem i := by
    intro i; unfold isRem; rw [hb i _ (Or.inr (Or.inr (Or.inl rfl)))]
    simp [show ABits.shrinkable ≠ ABits.removable by decide]
  refine ⟨⟨AF.trans_left (setABit_af s idx _ true shrinkable_bin) af_rfl, rfl, fun i h => by rw [hr]; exact h,
    pushShrinkable_listed s idx hsz⟩,
    hr, fun i => ?_, by show (s.shrinkable.push idx).view = _; rw [U32Vec.view_push], rfl⟩
  unfold isSh; rw [hb i _ (Or.inr (Or.inr (Or.inr rfl)))]
  by_cases e : idx = i
  · subst e; simp
  · simp [e, Ne.symm e]

/-- Specification of `shrinkLiteral` on a false literal. -/
theorem shrinkLiteral_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (s : Solver) (level : UInt32) (lit : Lit) (hs : AF s s0) (hg : Good s0 s B)
    (hf : s0.IsFalse lit) :
    SF (s.shrinkLiteral level lit).2 s ∧ Good s0 (s.shrinkLiteral level lit).2 B ∧
    (∀ i, (s.shrinkLiteral level lit).2.isSh i = true ↔
      s.isSh i = true ∨ ((s.shrinkLiteral level lit).1 = 1 ∧ i = IDX lit)) ∧
    (s.shrinkLiteral level lit).2.shrinkable.view =
      s.shrinkable.view ++ (if (s.shrinkLiteral level lit).1 = 1 then [IDX lit] else []) ∧
    ((s.shrinkLiteral level lit).1 = 0 → s0.lvl lit = 0 ∨ s.isSh (IDX lit) = true ∨
      (s.shrinkLiteral level lit).2.isRem (IDX lit) = true) ∧
    ((s.shrinkLiteral level lit).1 = 1 → s.isSh (IDX lit) = false ∧ s0.lvl lit ≠ 0) ∧
    ((s.shrinkLiteral level lit).1 = 0 ∨ (s.shrinkLiteral level lit).1 = 1 ∨
      (s.shrinkLiteral level lit).1 = -1) := by
  have hsz : (IDX lit).toNat < s.asg.aBits.size := by
    rw [hs.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf; unfold ValidLit at this; omega
  have hmin := (minimize_all hb B false s.options.minimizedepth).1 s lit 1
  unfold shrinkLiteral
  simp only
  split
  · rename_i h0
    have := (levelIdx_eq_zero s lit).mp h0
    rw [hs.lvl] at this
    exact ⟨SF.refl _, hg, fun i => by simp, by simp, fun _ => Or.inl this, fun h => absurd h (by simp),
      Or.inl rfl⟩
  split
  · rename_i _ hsh
    exact ⟨SF.refl _, hg, fun i => by simp, by simp, fun _ => Or.inr (Or.inl hsh),
      fun h => absurd h (by simp), Or.inl rfl⟩
  split
  · split
    · rename_i _ _ _ hr
      exact ⟨SF.refl _, hg, fun i => by simp, by simp, fun _ => Or.inr (Or.inr hr),
        fun h => absurd h (by simp), Or.inl rfl⟩
    split
    · obtain ⟨m1, m2, _, m4⟩ := hmin hs hg hf
      unfold minimizeLiteralTop
      simp only [Bool.false_eq_true, ite_false]
      split
      · rename_i hok
        refine ⟨m1.sf, m2, fun i => by rw [show (s.minimizeLiteral false s.options.minimizedepth lit 1).2.isSh i = s.isSh i from m1.shrinkable i]; simp, by simp [m1.shList], fun _ => ?_, fun h => absurd h (by simp), Or.inl rfl⟩
        · rcases m4 hok with h | ⟨_, h⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · omega
      · exact ⟨m1.sf, m2, fun i => by rw [show (s.minimizeLiteral false s.options.minimizedepth lit 1).2.isSh i = s.isSh i from m1.shrinkable i]; simp, by simp [m1.shList], fun h => absurd h (by simp), fun h => absurd h (by simp), Or.inr (Or.inr rfl)⟩
    · exact ⟨SF.refl _, hg, fun i => by simp, by simp, fun h => absurd h (by simp),
        fun h => absurd h (by simp), Or.inr (Or.inr rfl)⟩
  · rename_i h0 hsh _
    obtain ⟨p1, p2, p3, p4, _⟩ := pushShrinkable_spec s (IDX lit) hsz
    have hl0 : s0.lvl lit ≠ 0 := fun e => h0 ((levelIdx_eq_zero s lit).mpr (by rw [hs.lvl]; exact e))
    refine ⟨p1, hg.mono_mf (fun j => by rw [p2]), fun i => by rw [p3]; simp, by rw [p4]; simp,
      fun h => absurd h (by simp), fun _ => ⟨by
        have : s.abit (IDX lit) ABits.shrinkable = false := by simpa using hsh
        exact this, hl0⟩, Or.inr (Or.inl rfl)⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Shrinkable literals on the trail up to position `t`. -/
def shCount (s0 s : Solver) (t : Nat) : Nat := (s0.trailL.take (t + 1)).countP (fun l => s.isSh (IDX l))

/-- The shrinking invariant for scan position `t` with `opened` pending shrinkable literals. -/
structure ShInv (s0 : Solver) (B : List Lit) (s : Solver) (t opened : Nat) : Prop where
  af : AF s s0
  clause : s.clause.view = B
  good : Good s0 s B
  shA : ∀ i, s.isSh i = true → ∃ y, IDX y = i ∧ s0.IsFalse y ∧ 0 < s0.lvl y
  shL : ∀ i, s.isSh i = true → i ∈ s.shrinkable.view
  status : ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isSh (IDX y) = true →
    (∃ p, p ≤ t ∧ s0.trailL[p]? = some (NOT y)) ∨ RCE s0 s s.shrinkable.view y
  count : opened = shCount s0 s t
  tlt : t < s0.trailL.length
  listA : ∀ i ∈ s.shrinkable.view, ∃ y, IDX y = i ∧ s0.IsFalse y
  listSh : ∀ i ∈ s.shrinkable.view, s.isSh i = true
  listed : Listed s

theorem RCE.mono_list {s0 s t : Solver} {E E' : List UInt32} {y : Lit} (h : RCE s0 s E y)
    (hm : ∀ i, s.isRem i = true → t.isRem i = true) (hE : ∀ i ∈ E, i ∈ E') : RCE s0 t E' y :=
  h.mono hm (fun i hi => Or.inl (hE i hi))

/-- One `shrinkLiteral` on a false literal whose negation is on the trail at or before `t`. -/
theorem ShInv.shrinkLit {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {B : List Lit} {s : Solver} {t opened : Nat} (h : ShInv s0 B s t opened) (level : UInt32) {x : Lit}
    (hx : s0.IsFalse x) (hpos : 0 < s0.lvl x → ∃ p, p ≤ t ∧ s0.trailL[p]? = some (NOT x)) :
    ShInv s0 B (s.shrinkLiteral level x).2 t (opened + if (s.shrinkLiteral level x).1 = 1 then 1 else 0) ∧
    ((s.shrinkLiteral level x).1 = 0 → s0.lvl x = 0 ∨ (s.shrinkLiteral level x).2.isSh (IDX x) = true ∨
      (s.shrinkLiteral level x).2.isRem (IDX x) = true) ∧
    ((s.shrinkLiteral level x).1 = 1 → (s.shrinkLiteral level x).2.isSh (IDX x) = true) ∧
    (∀ i, (s.shrinkLiteral level x).2.isSh i = true → s.isSh i = true ∨ i = IDX x) ∧
    (∀ i, s.isSh i = true → (s.shrinkLiteral level x).2.isSh i = true) ∧
    ((s.shrinkLiteral level x).1 = 0 ∨ (s.shrinkLiteral level x).1 = 1 ∨
      (s.shrinkLiteral level x).1 = -1) ∧
    (∀ i, s.isRem i = true → (s.shrinkLiteral level x).2.isRem i = true) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := shrinkLiteral_spec hb B s level x h.af (h.clause ▸ h.good) hx
  generalize s.shrinkLiteral level x = R at r1 r2 r3 r4 r5 r6 r7 ⊢
  obtain ⟨tmp, s'⟩ := R
  simp only at r1 r2 r3 r4 r5 r6 r7 ⊢
  have hcl : s'.clause.view = B := by rw [r1.clause, h.clause]
  have mono : ∀ i, s.isSh i = true → s'.isSh i = true := fun i hi => (r3 i).mpr (Or.inl hi)
  have hlist : ∀ i ∈ s.shrinkable.view, i ∈ s'.shrinkable.view := by
    intro i hi; rw [r4]; exact List.mem_append_left _ hi
  refine ⟨⟨r1.af.trans h.af, hcl, r2, ?_, ?_, ?_, ?_, h.tlt, ?_, ?_, r1.listed h.listed⟩,
    fun h0 => ?_, fun h1 => (r3 _).mpr (Or.inr ⟨h1, rfl⟩), fun i hi => ?_, mono, r7, r1.rem⟩
  · intro i hi
    rcases (r3 i).mp hi with hold | ⟨_, rfl⟩
    · exact h.shA i hold
    · rename_i h1
      exact ⟨x, rfl, hx, Nat.pos_of_ne_zero (r6 h1).2⟩
  · intro i hi
    rcases (r3 i).mp hi with hold | ⟨h1, rfl⟩
    · exact hlist _ (h.shL i hold)
    · rw [r4, ite_eq_left h1]; simp
  · intro y hf hl hsh
    rcases (r3 _).mp hsh with hold | ⟨h1, hyx⟩
    · rcases h.status y hf hl hold with hp | hr
      · exact Or.inl hp
      · exact Or.inr (hr.mono_list r1.rem hlist)
    · have := hb.false_same_var hx hf hyx
      subst this
      exact Or.inl (hpos hl)
  · rw [h.count]
    unfold shCount
    have hnd : (s0.trailL.take (t + 1)).Nodup := hb.trail_nodup.sublist (List.take_sublist _ _)
    by_cases h1 : tmp = 1
    · rw [ite_eq_left h1]
      obtain ⟨hns, hl0⟩ := r6 h1
      obtain ⟨p, hp, hpx⟩ := hpos (Nat.pos_of_ne_zero hl0)
      have hmem : NOT x ∈ s0.trailL.take (t + 1) := by
        rw [List.mem_iff_getElem?]; exact ⟨p, by rw [List.getElem?_take]; simp [show p < t + 1 by omega, hpx]⟩
      symm
      apply countP_succ_of_unique _ _ _ (NOT x) hmem hnd
      · rw [IDX_NOT]; exact (r3 _).mpr (Or.inr ⟨h1, rfl⟩)
      · rw [IDX_NOT]; exact hns
      · intro z hz hne
        have : ¬ IDX z = IDX x := by
          intro e
          exact hne (hb.idx_unique (List.mem_of_mem_take hz) (List.mem_of_mem_take hmem) (by rw [IDX_NOT]; exact e))
        cases h2 : s'.isSh (IDX z) <;> cases h3 : s.isSh (IDX z)
        · rfl
        · exact absurd (mono _ h3) (by rw [h2]; simp)
        · rcases (r3 _).mp h2 with h4 | ⟨_, h4⟩
          · rw [h3] at h4; exact absurd h4 (by simp)
          · exact absurd h4 this
        · rfl
    · rw [ite_eq_right h1, Nat.add_zero]
      symm
      apply countP_eq_of_agree
      intro z _
      cases h2 : s'.isSh (IDX z) <;> cases h3 : s.isSh (IDX z)
      · rfl
      · exact absurd (mono _ h3) (by rw [h2]; simp)
      · rcases (r3 _).mp h2 with h4 | ⟨h4, _⟩
        · rw [h3] at h4; exact absurd h4 (by simp)
        · exact absurd h4 h1
      · rfl
  · intro i hi
    rw [r4] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact h.listA i hi
    · split at hi
      · simp at hi; subst hi; exact ⟨x, rfl, hx⟩
      · simp at hi
  · intro i hi
    rw [r4] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact mono _ (h.listSh i hi)
    · split at hi
      · rename_i h1; simp at hi; subst hi; exact (r3 _).mpr (Or.inr ⟨h1, rfl⟩)
      · simp at hi
  · rcases r5 h0 with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (mono _ h'))
    · exact Or.inr (Or.inr h')
  · rcases (r3 i).mp hi with hold | ⟨_, rfl⟩
    · exact Or.inl hold
    · exact Or.inr rfl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem findShrinkable_spec (s0 s : Solver) (hs : AF s s0) :
    ∀ t, t < s0.trailL.length → 1 ≤ shCount s0 s t →
    ∃ p, p ≤ t ∧ s0.trailL[p]? = some (s.findShrinkable t).1 ∧ s.isSh (IDX (s.findShrinkable t).1) = true ∧
      (s.findShrinkable t).2 = p - 1 ∧ shCount s0 s t = (s0.trailL.take p).countP (fun l => s.isSh (IDX l)) + 1 ∧
      (∀ q, p < q → q ≤ t → ∀ l, s0.trailL[q]? = some l → s.isSh (IDX l) = false) := by
  intro t
  induction t with
  | zero =>
    intro hlt hc
    rw [findShrinkable]
    have h0 : s0.trailL[0]? = some (s.asg.trail.get! 0) := by
      rw [← hs.trailL]; exact trailL_getElem? s 0 (by rw [← length_trailL, hs.trailL]; exact hlt)
    have hsh : s.abit (IDX (s.asg.trail.get! 0)) ABits.shrinkable = true := by
      unfold shCount at hc
      rw [List.take_add_one, List.take_zero, List.nil_append, h0] at hc
      simp only [Option.toList_some, List.countP_singleton] at hc
      unfold isSh at hc; split at hc <;> simp_all
    rw [ite_eq_left hsh]
    refine ⟨0, Nat.le_refl _, h0, hsh, rfl, ?_, fun q h1 h2 => absurd h2 (by omega)⟩
    unfold shCount
    rw [List.take_add_one, List.take_zero, List.nil_append, h0]
    simp [isSh, hsh]
  | succ t ih =>
    intro hlt hc
    rw [findShrinkable]
    have ht : s0.trailL[t + 1]? = some (s.asg.trail.get! (t + 1)) := by
      rw [← hs.trailL]; exact trailL_getElem? s (t + 1) (by rw [← length_trailL, hs.trailL]; exact hlt)
    have hsplit : shCount s0 s (t + 1) = shCount s0 s t +
        (if s.isSh (IDX (s.asg.trail.get! (t + 1))) = true then 1 else 0) := by
      unfold shCount
      rw [show t + 1 + 1 = (t + 1) + 1 from rfl, List.take_add_one (i := t + 1), ht]
      simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    by_cases hsh : s.abit (IDX (s.asg.trail.get! (t + 1))) ABits.shrinkable = true
    · rw [ite_eq_left hsh]
      refine ⟨t + 1, Nat.le_refl _, ht, hsh, rfl, ?_, fun q h1 h2 => absurd h2 (by omega)⟩
      rw [hsplit]; unfold shCount; simp [isSh, hsh]
    · rw [ite_eq_right hsh, dite_eq_right (by omega)]
      have hsh' : s.isSh (IDX (s.asg.trail.get! (t + 1))) = false := by simpa [isSh] using hsh
      rw [hsplit, hsh'] at hc
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hc
      obtain ⟨p, hp, h1, h2, h3, h4, h5⟩ := ih (by omega) hc
      refine ⟨p, by omega, h1, h2, h3, by rw [hsplit, hsh']; simpa using h4, fun q hq1 hq2 l hl => ?_⟩
      by_cases e : q = t + 1
      · subst e; rw [ht] at hl; cases hl; exact hsh'
      · exact h5 q hq1 (by omega) l hl

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem shrinkLargeLoop_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (level : UInt32) (uip : Lit) (ref : Ref) (n base t : Nat)
    (hr : ref ∈ s0.arena.chain 0 s0.arena.sizeWards) (hn : n ≤ (s0.arena.size ref).toNat)
    (hpre : ∀ k, k < n → s0.arena.lit ref k ≠ uip → s0.IsFalse (s0.arena.lit ref k) ∧
      (0 < s0.lvl (s0.arena.lit ref k) → ∃ q, q ≤ t ∧ s0.trailL[q]? = some (NOT (s0.arena.lit ref k)))) :
    ∀ (s : Solver) (i acc : Nat), ShInv s0 B s t (base + acc) →
    ShInv s0 B (s.shrinkLargeLoop level uip ref i n acc).2.2 t (base + (s.shrinkLargeLoop level uip ref i n acc).1) ∧
    ((s.shrinkLargeLoop level uip ref i n acc).2.1 = false → ∀ k, i ≤ k → k < n →
      s0.arena.lit ref k ≠ uip → s0.lvl (s0.arena.lit ref k) = 0 ∨
        (s.shrinkLargeLoop level uip ref i n acc).2.2.isSh (IDX (s0.arena.lit ref k)) = true ∨
        (s.shrinkLargeLoop level uip ref i n acc).2.2.isRem (IDX (s0.arena.lit ref k)) = true) ∧
    (∀ j, s.isSh j = true → (s.shrinkLargeLoop level uip ref i n acc).2.2.isSh j = true) ∧
    (∀ j, (s.shrinkLargeLoop level uip ref i n acc).2.2.isSh j = true → s.isSh j = true ∨
      ∃ k, i ≤ k ∧ k < n ∧ s0.arena.lit ref k ≠ uip ∧ j = IDX (s0.arena.lit ref k)) ∧
    (∀ j, s.isRem j = true → (s.shrinkLargeLoop level uip ref i n acc).2.2.isRem j = true) := by
  intro s i acc
  fun_induction shrinkLargeLoop s level uip ref i n acc with
  | case1 s i acc hi other heq ih =>
    intro h
    have ho : other = s0.arena.lit ref i := h.af.lit_eq hr (by omega)
    obtain ⟨a1, a2, a3, a4, a5⟩ := ih h
    refine ⟨a1, fun hf k hk1 hk2 hne => ?_, a3, fun j hj => ?_, a5⟩
    · by_cases e : k = i
      · subst e; exact absurd (ho ▸ beq_iff_eq.mp heq) hne
      · exact a2 hf k (by omega) hk2 hne
    · rcases a4 j hj with h' | ⟨k, hk1, hk2, hk3, hk4⟩
      · exact Or.inl h'
      · exact Or.inr ⟨k, by omega, hk2, hk3, hk4⟩
  | case2 s i acc hi other hne tmp s' heq hneg =>
    intro h
    have ho : other = s0.arena.lit ref i := h.af.lit_eq hr (by omega)
    have hne' : s0.arena.lit ref i ≠ uip := by rw [← ho]; intro e; exact hne (beq_iff_eq.mpr e)
    obtain ⟨p1, p2⟩ := hpre i hi hne'
    rw [← ho] at p1 p2
    obtain ⟨b1, _, _, b4, b5, b6, b7⟩ := h.shrinkLit hb level p1 p2
    rw [heq] at b1 b4 b5 b6 b7
    simp only at b1 b4 b5 b6 b7
    have : (if tmp = 1 then 1 else 0) = 0 := by
      rw [ite_eq_right]; intro e; rw [e] at hneg; simp at hneg
    rw [this, Nat.add_zero] at b1
    refine ⟨b1, fun hf => absurd hf (by simp), b5, fun j hj => ?_, b7⟩
    rcases b4 j hj with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨i, Nat.le_refl _, hi, hne', by rw [h', ho]⟩
  | case3 s i acc hi other hne tmp s' heq hneg ih =>
    intro h
    have ho : other = s0.arena.lit ref i := h.af.lit_eq hr (by omega)
    have hne' : s0.arena.lit ref i ≠ uip := by rw [← ho]; intro e; exact hne (beq_iff_eq.mpr e)
    obtain ⟨p1, p2⟩ := hpre i hi hne'
    rw [← ho] at p1 p2
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h.shrinkLit hb level p1 p2
    rw [heq] at b1 b2 b3 b4 b5 b6 b7
    simp only at b1 b2 b3 b4 b5 b6 b7
    have e : base + acc + (if tmp = 1 then 1 else 0) = base + (if tmp > 0 then acc + 1 else acc) := by
      rcases b6 with h0 | h0 | h0 <;> rw [h0] <;> simp <;> omega
    rw [e] at b1
    simp only [dite_eq_ite] at ih
    obtain ⟨a1, a2, a3, a4, a5⟩ := ih b1
    refine ⟨a1, fun hf k hk1 hk2 hk3 => ?_, fun j hj => a3 j (b5 j hj), fun j hj => ?_,
      fun j hj => a5 j (b7 j hj)⟩
    · by_cases e' : k = i
      · subst e'
        rw [← ho]
        rcases b6 with h0 | h0 | h0
        · rcases b2 h0 with h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl (a3 _ h'))
          · exact Or.inr (Or.inr (a5 _ h'))
        · exact Or.inr (Or.inl (a3 _ (b3 h0)))
        · rw [h0] at hneg; simp at hneg
      · exact a2 hf k (by omega) hk2 hk3
    · rcases a4 j hj with h' | ⟨k, hk1, hk2, hk3, hk4⟩
      · rcases b4 j h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨i, Nat.le_refl _, hi, hne', by rw [h'', ho]⟩
      · exact Or.inr ⟨k, by omega, hk2, hk3, hk4⟩
  | case4 s i acc hi =>
    intro h
    exact ⟨h, fun _ k hk1 hk2 => absurd hk2 (by omega), fun j hj => hj, fun j hj => Or.inl hj,
      fun j hj => hj⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem ShInv.ticks {s0 : Solver} {B : List Lit} {s : Solver} {t o : Nat} (h : ShInv s0 B s t o) (b : Bool) :
    ShInv s0 B (if b then INC! s search_ticks else s) t o ∧
    (∀ j, (if b then INC! s search_ticks else s).isSh j = s.isSh j) ∧
    (∀ j, (if b then INC! s search_ticks else s).isRem j = s.isRem j) ∧
    (if b then INC! s search_ticks else s).arena = s.arena := by
  cases b
  · exact ⟨h, fun _ => rfl, fun _ => rfl, rfl⟩
  · refine ⟨⟨AF.trans_left h.af af_rfl, h.clause, h.good.mono_mf (fun _ => Iff.rfl), h.shA, h.shL, h.status,
      h.count, h.tlt, h.listA, h.listSh, h.listed⟩, fun _ => rfl, fun _ => rfl, rfl⟩

/-- Resolving the reason of a shrinkable trail literal. -/
theorem shrinkAlongReason_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {B : List Lit} {s : Solver} {t opened : Nat} (h : ShInv s0 B s t opened) (level : UInt32)
    {uip : Lit} {p : Nat} (hp : s0.trailL[p]? = some uip) (hpt : p ≤ t) (hl : 0 < s0.lvl uip)
    (resolveLarge : Bool) :
    ShInv s0 B (s.shrinkAlongReason level uip resolveLarge).2.2 t
      (opened + (s.shrinkAlongReason level uip resolveLarge).1) ∧
    ((s.shrinkAlongReason level uip resolveLarge).2.1 = false →
      RCE s0 (s.shrinkAlongReason level uip resolveLarge).2.2
        (s.shrinkAlongReason level uip resolveLarge).2.2.shrinkable.view (NOT uip)) ∧
    (∀ j, s.isSh j = true → (s.shrinkAlongReason level uip resolveLarge).2.2.isSh j = true) ∧
    (∀ j, s.isRem j = true → (s.shrinkAlongReason level uip resolveLarge).2.2.isRem j = true) ∧
    (∀ j, (s.shrinkAlongReason level uip resolveLarge).2.2.isSh j = true → s.isSh j = true ∨
      ∃ x, s0.Ante uip x ∧ j = IDX x) := by
  have huT : s0.IsTrue uip := hb.inv.core.trailTrue _ (List.mem_of_getElem? hp)
  have hra := hb.inv.reasons uip huT hl
  have eB : s.isBinaryReason (IDX uip) = s0.binOf uip := by show s.binOf uip = _; rw [h.af.binOf]
  have eR : s.reasonIdx (IDX uip) = s0.reasonOf uip := by show s.reasonOf uip = _; rw [h.af.reasonOf]
  have hpos : ∀ x, s0.Ante uip x → 0 < s0.lvl x → ∃ q, q ≤ t ∧ s0.trailL[q]? = some (NOT x) := by
    intro x hx hlx
    obtain ⟨q, hq, hqx⟩ := hb.ante_before hp hx hlx
    exact ⟨q, by omega, hqx⟩
  have hNN : NOT (NOT uip) = uip := NOT_NOT uip
  unfold shrinkAlongReason
  simp only
  split
  · -- decision: fails
    exact ⟨by simpa using h, fun hf => absurd hf (by simp), fun j hj => hj, fun j hj => hj,
      fun j hj => Or.inl hj⟩
  rename_i hdec
  have hndec : s0.reasonOf uip ≠ DECISION_REASON := by
    intro e; apply hdec; rw [eR, e]; rfl
  split
  · -- binary
    rename_i hbin
    rw [eB] at hbin
    rcases hra with e | ⟨b1, b2, b3⟩ | ⟨b1, _⟩
    · exact absurd e hndec
    · rw [eR]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h.shrinkLit hb level b3.1 (hpos _ b3)
      generalize s.shrinkLiteral level (s0.reasonOf uip) = R at a1 a2 a3 a4 a5 a6 a7 ⊢
      obtain ⟨tmp, s'⟩ := R
      simp only at a1 a2 a3 a4 a5 a6 a7 ⊢
      have e : opened + (if tmp = 1 then 1 else 0) = opened + (if tmp > 0 then 1 else 0) := by
        rcases a6 with h0 | h0 | h0 <;> rw [h0] <;> simp
      rw [e] at a1
      refine ⟨a1, fun hf => ⟨[s0.reasonOf uip], ⟨by rw [hNN]; exact huT, by rw [hNN]; exact hl,
        Or.inl ⟨by rw [hNN]; exact b1, by rw [hNN]; exact b2, by rw [hNN]⟩⟩, fun x hx => ?_⟩, a5, a7,
        fun j hj => (a4 j hj).imp_right (fun e => ⟨_, b3, e⟩)⟩
      simp at hx; subst hx
      have h0 : tmp = 0 ∨ tmp = 1 := by
        rcases a6 with h0 | h0 | h0
        · exact Or.inl h0
        · exact Or.inr h0
        · rw [h0] at hf; simp at hf
      rcases h0 with h0 | h0
      · rcases a2 h0 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (a1.shL _ h'))
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (a1.shL _ (a3 h0)))
    · rw [b1] at hbin; exact absurd hbin (by simp)
  · split
    · -- large reason
      rename_i hbin _
      rw [eB] at hbin
      rcases hra with e | ⟨b1, _⟩ | ⟨b1, b2, b3, b4⟩
      · exact absurd e hndec
      · rw [b1] at hbin; exact absurd hbin (by simp)
      rw [eR]
      unfold shrinkAlongLarge
      obtain ⟨t1, t2, t3, t4⟩ := h.ticks (s.options.minimizeticks != 0)
      generalize (if (s.options.minimizeticks != 0) = true then INC! s search_ticks else s) = s1 at t1 t2 t3 t4 ⊢
      simp only
      have hr : s0.reasonOf uip ∈ s0.arena.chain 0 s0.arena.sizeWards := b2.1
      have hsz : (s1.arena.size (s0.reasonOf uip)).toNat = (s0.arena.size (s0.reasonOf uip)).toNat := by
        rw [t1.af.arena.size _ hr]
      rw [hsz]
      have spec := shrinkLargeLoop_spec hb B level uip (s0.reasonOf uip) (s0.arena.size (s0.reasonOf uip)).toNat
        opened t hr (Nat.le_refl _)
        (fun k hk hne => ⟨(b4 _ (lit_mem_litsL _ _ _ hk) hne).1,
          hpos _ (b4 _ (lit_mem_litsL _ _ _ hk) hne)⟩) s1 0 0 (by simpa using t1)
      generalize s1.shrinkLargeLoop level uip (s0.reasonOf uip) 0 (s0.arena.size (s0.reasonOf uip)).toNat 0 = R at spec ⊢
      obtain ⟨o, f, s'⟩ := R
      simp only at spec ⊢
      obtain ⟨c1, c2, c3, c4, c5⟩ := spec
      refine ⟨c1, fun hf => ⟨(s0.clauseL (s0.reasonOf uip)).filter (fun x => x != uip),
        ⟨by rw [hNN]; exact huT, by rw [hNN]; exact hl, Or.inr ⟨by rw [hNN]; exact b1, by rw [hNN]; exact hndec,
          by rw [hNN]; exact b2, by rw [hNN]; exact b3, fun x => by rw [hNN]; simp [List.mem_filter]⟩⟩,
        fun x hx => ?_⟩, fun j hj => c3 j (by rw [t2]; exact hj), fun j hj => c5 j (by rw [t3]; exact hj),
        fun j hj => ?_⟩
      · obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
        obtain ⟨k, hk, rfl⟩ := mem_litsL_iff.mp hx1
        rcases c2 hf k (Nat.zero_le _) hk (by simpa using hx2) with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (c1.shL _ h'))
        · exact Or.inr (Or.inl h')
      · rcases c4 j hj with h' | ⟨k, _, hk, hne, rfl⟩
        · exact Or.inl (by rw [← t2]; exact h')
        · exact Or.inr ⟨_, b4 _ (lit_mem_litsL _ _ _ hk) hne, rfl⟩
    · exact ⟨by simpa using h, fun hf => absurd hf (by simp), fun j hj => hj, fun j hj => hj,
        fun j hj => Or.inl hj⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The facts kept by shrinking states (without the scan bookkeeping). -/
structure ShFin (s0 : Solver) (B : List Lit) (s : Solver) : Prop where
  af : AF s s0
  clause : s.clause.view = B
  good : Good s0 s B
  shA : ∀ i, s.isSh i = true → ∃ y, IDX y = i ∧ s0.IsFalse y ∧ 0 < s0.lvl y
  shL : ∀ i, s.isSh i = true → i ∈ s.shrinkable.view
  listA : ∀ i ∈ s.shrinkable.view, ∃ y, IDX y = i ∧ s0.IsFalse y
  listSh : ∀ i ∈ s.shrinkable.view, s.isSh i = true
  listed : Listed s

theorem ShInv.fin {s0 : Solver} {B : List Lit} {s : Solver} {t o : Nat} (h : ShInv s0 B s t o) :
    ShFin s0 B s := ⟨h.af, h.clause, h.good, h.shA, h.shL, h.listA, h.listSh, h.listed⟩

def ShOut (s0 : Solver) (B : List Lit) (s : Solver) (r : Lit × Bool × Solver) : Prop :=
  ShFin s0 B r.2.2 ∧ (∀ j, s.isRem j = true → r.2.2.isRem j = true) ∧
  (∀ j, s.isSh j = true → r.2.2.isSh j = true) ∧
  (r.2.1 = false → s0.IsTrue r.1 ∧ 0 < s0.lvl r.1 ∧ r.2.2.isSh (IDX r.1) = true ∧
    ∀ y, s0.IsFalse y → 0 < s0.lvl y → r.2.2.isSh (IDX y) = true → IDX y ≠ IDX r.1 →
      RCE s0 r.2.2 r.2.2.shrinkable.view y)

theorem shrinkBlockLoop_succ (s : Solver) (level : UInt32) (rl : Bool) (opened t fuel : Nat) :
    s.shrinkBlockLoop level rl opened t (fuel + 1) =
      (if opened == 1 then ((s.findShrinkable t).1, false, s)
       else
         let r := s.shrinkAlongReason level (s.findShrinkable t).1 rl
         if r.2.1 then ((s.findShrinkable t).1, true, r.2.2)
         else r.2.2.shrinkBlockLoop level rl (opened + r.1 - 1) (s.findShrinkable t).2 fuel) := by
  rw [shrinkBlockLoop]

theorem shrinkBlockLoop_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (level : UInt32) (rl : Bool) :
    ∀ fuel (s : Solver) (opened t : Nat), ShInv s0 B s t opened → 1 ≤ opened →
    ShOut s0 B s (s.shrinkBlockLoop level rl opened t fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s opened t h _
    exact ⟨h.fin, fun j hj => hj, fun j hj => hj, fun hf => absurd hf (by simp [shrinkBlockLoop])⟩
  | succ fuel ih =>
    intro s opened t h hop
    rw [shrinkBlockLoop_succ]
    obtain ⟨p, hpt, hp, hsh, ht', hcnt, hgap⟩ :=
      findShrinkable_spec s0 s h.af t h.tlt (by rw [← h.count]; exact hop)
    generalize s.findShrinkable t = F at hp hsh ht' hcnt hgap ⊢
    obtain ⟨uip, t'⟩ := F
    simp only at hp hsh ht' hcnt hgap ⊢
    have hnd := hb.trail_nodup
    have huT : s0.IsTrue uip := hb.inv.core.trailTrue _ (List.mem_of_getElem? hp)
    have hul : 0 < s0.lvl uip := by
      obtain ⟨y, hy, hf, hl⟩ := h.shA _ hsh
      have hnty := hb.true_on_trail hf hl
      have : NOT y = uip := hb.idx_unique hnty (List.mem_of_getElem? hp) (by rw [IDX_NOT, hy])
      rw [← this, hb.inv.core.lvlVar]; exact hl
    split
    · rename_i h1
      have h1' : opened = 1 := by simpa using h1
      rw [h.count, hcnt] at h1'
      have hzero : (s0.trailL.take p).countP (fun l => s.isSh (IDX l)) = 0 := by omega
      refine ⟨h.fin, fun j hj => hj, fun j hj => hj, fun _ => ⟨huT, hul, hsh, fun y hf hl hy hne => ?_⟩⟩
      rcases h.status y hf hl hy with ⟨q, hq, hqy⟩ | hr
      · exfalso
        rcases Nat.lt_trichotomy q p with hlt | heq | hgt
        · rw [List.countP_eq_zero] at hzero
          have hmem : NOT y ∈ s0.trailL.take p := by
            rw [List.mem_iff_getElem?]; exact ⟨q, by rw [List.getElem?_take]; simp [hlt, hqy]⟩
          have := hzero _ hmem; rw [IDX_NOT, hy] at this; simp at this
        · subst heq; rw [hp] at hqy
          exact hne (by rw [← IDX_NOT, ← Option.some.inj hqy])
        · have := hgap q hgt hq _ hqy; rw [IDX_NOT, hy] at this; simp at this
      · exact hr
    · rename_i h1
      have h1' : opened ≠ 1 := by intro e; apply h1; simp [e]
      obtain ⟨r1, r2, r3, r4, r5⟩ := shrinkAlongReason_spec hb h level hp hpt hul rl
      generalize s.shrinkAlongReason level uip rl = R at r1 r2 r3 r4 r5 ⊢
      obtain ⟨o, failed, s'⟩ := R
      simp only at r1 r2 r3 r4 r5 ⊢
      split
      · exact ⟨r1.fin, r4, r3, fun hf => absurd hf (by simp)⟩
      rename_i hfl
      have hfl' : failed = false := by simpa using hfl
      have hres := r2 hfl'
      have hcp : 1 ≤ (s0.trailL.take p).countP (fun l => s.isSh (IDX l)) := by
        have := h.count; rw [hcnt] at this; omega
      have hp1 : 1 ≤ p := by
        apply Nat.pos_of_ne_zero; intro e; subst e; simp at hcp
      -- no shrinkable literal of `s'` strictly between `p` and `t`
      have hgap' : ∀ q, p < q → q ≤ t → ∀ l, s0.trailL[q]? = some l → s'.isSh (IDX l) = false := by
        intro q hq1 hq2 l hl
        cases hx : s'.isSh (IDX l)
        · rfl
        · exfalso
          rcases r5 _ hx with hold | ⟨x, hxa, hxe⟩
          · rw [hgap q hq1 hq2 l hl] at hold; simp at hold
          · obtain ⟨y, hy, hf, hly⟩ := r1.shA _ hx
            have hyx := hb.false_same_var hxa.1 hf (by rw [hy, hxe])
            subst hyx
            obtain ⟨q', hq', hq'x⟩ := hb.ante_before hp hxa hly
            have hlx : l = NOT y := hb.idx_unique (List.mem_of_getElem? hl) (List.mem_of_getElem? hq'x)
              (by rw [IDX_NOT, hy, hxe])
            subst hlx
            have := nodup_pos_unique hnd hl hq'x
            omega
      have hsh' : s'.isSh (IDX uip) = true := r3 _ hsh
      have hcnt' : shCount s0 s' t = (s0.trailL.take p).countP (fun l => s'.isSh (IDX l)) + 1 := by
        unfold shCount
        have := countP_take_split (fun l => s'.isSh (IDX l)) s0.trailL p uip hp hsh' (t - p)
          (fun q h1 h2 l hl => hgap' q h1 (by omega) l hl) (by have := h.tlt; omega)
        rwa [show p + 1 + (t - p) = t + 1 by omega] at this
      have hinv : ShInv s0 B s' (p - 1) (opened + o - 1) := by
        refine ⟨r1.af, r1.clause, r1.good, r1.shA, r1.shL, fun y hf hl hy => ?_, ?_, by
          have := h.tlt; omega, r1.listA, r1.listSh, r1.listed⟩
        · rcases r1.status y hf hl hy with ⟨q, hq, hqy⟩ | hr
          · rcases Nat.lt_trichotomy q p with hlt | heq | hgt
            · exact Or.inl ⟨q, by omega, hqy⟩
            · subst heq; rw [hp] at hqy
              have : NOT y = uip := (Option.some.inj hqy).symm
              have hy' : y = NOT uip := by rw [← this, NOT_NOT]
              rw [hy']; exact Or.inr hres
            · have := hgap' q hgt hq _ hqy; rw [IDX_NOT] at this; rw [this] at hy; simp at hy
          · exact Or.inr hr
        · unfold shCount
          rw [show p - 1 + 1 = p by omega]
          have := r1.count; rw [hcnt'] at this; omega
      obtain ⟨q1, q2, q3, q4⟩ := ih s' (opened + o - 1) (p - 1) hinv (by omega)
      rw [ht']
      exact ⟨q1, fun j hj => q2 j (r4 j hj), fun j hj => q3 j (r3 j hj), q4⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem DBase.invalid_not_false {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) :
    ¬ s0.IsFalse INVALID_LIT := by
  intro h
  have := hb.valid_false h
  have hv := hb.inv.ws.varsBound
  unfold ValidLit at this; rw [IDX_toNat] at this
  simp [INVALID_LIT] at this; omega

/-- `clearBitsDown` with a bit other than `removable`: frame and cleared bits. -/
theorem clearBitsDown_spec (v : U32Vec) (b : UInt8) (hb : b = ABits.shrinkable ∨ b = ABits.poisoned) (n : Nat) :
    ∀ (s : Solver) (k : Nat), (∀ j, j < n → (v.get! j).toNat < s.asg.aBits.size) →
    AF (s.clearBitsDown v b n k) s ∧ (∀ i, (s.clearBitsDown v b n k).isRem i = s.isRem i) ∧
    (s.clearBitsDown v b n k).clause = s.clause ∧
    (∀ i, (s.clearBitsDown v b n k).abit i b = true → s.abit i b = true ∧
      ∀ j, k ≤ j → j < n → v.get! (n - 1 - j) ≠ i) ∧
    (∀ i c, c ≠ b → (c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.shrinkable ∨ c = ABits.removable) →
      (s.clearBitsDown v b n k).abit i c = s.abit i c) ∧
    (∀ c, (s.clearBitsDown v b n k).anaList c = s.anaList c) := by
  intro s k
  fun_induction clearBitsDown s v b n k with
  | case1 s k hk ih =>
    intro hsz
    have hsz' : (v.get! (n - 1 - k)).toNat < s.asg.aBits.size := hsz _ (by omega)
    have hbin : b &&& ABits.binary = 0 := by rcases hb with rfl | rfl <;> decide
    have f := setABit_af s (v.get! (n - 1 - k)) b false hbin
    have hab : ∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.shrinkable ∨ c = ABits.removable) →
        (s.setABit (v.get! (n - 1 - k)) b false).abit i c =
          if v.get! (n - 1 - k) = i ∧ b = c then false else s.abit i c := by
      intro i c hc
      apply abit_setABit s _ i b c false hsz'
      by_cases e : b = c
      · exact Or.inl ⟨e, by subst e; rcases hb with rfl | rfl <;> decide⟩
      · refine Or.inr ⟨e, ?_⟩
        rcases hb with rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl e
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (fun j hj => by rw [f.bitsSize]; exact hsz j hj)
    refine ⟨a1.trans f, ?_, ?_, ?_, ?_, fun c => by rw [a6]; rfl⟩
    · intro i
      rw [a2]
      unfold isRem
      rw [hab i _ (Or.inr (Or.inr (Or.inr rfl)))]
      have : b ≠ ABits.removable := by rcases hb with rfl | rfl <;> decide
      simp [this]
    · rw [a3]; rfl
    · intro i hi
      obtain ⟨h1, h2⟩ := a4 i hi
      rw [hab i _ (by rcases hb with rfl | rfl <;> simp)] at h1
      by_cases e : v.get! (n - 1 - k) = i
      · simp [e] at h1
      · simp [e] at h1
        refine ⟨h1, fun j hj1 hj2 => ?_⟩
        by_cases ej : j = k
        · subst ej; exact e
        · exact h2 j (by omega) hj2
    · intro i c hc hc'
      rw [a5 i c hc hc', hab i c hc']
      simp [Ne.symm hc]
  | case2 s k hk =>
    intro _
    exact ⟨AF.refl _, fun _ => rfl, rfl, fun i hi => ⟨hi, fun j hj1 hj2 => absurd hj2 (by omega)⟩,
      fun _ _ _ _ => rfl, fun _ => rfl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem mem_view_get! (v : U32Vec) (i : UInt32) (h : i ∈ v.view) : ∃ j, j < v.size ∧ v.get! j = i := by
  obtain ⟨j, hj, hx⟩ := List.mem_iff_getElem.mp h
  refine ⟨j, by simpa using hj, ?_⟩
  rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hx]

theorem resetShrinkable_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {B : List Lit} {s : Solver} (h : ShFin s0 B s) :
    AF s.resetShrinkable s0 ∧ (∀ i, s.resetShrinkable.isRem i = s.isRem i) ∧
    s.resetShrinkable.clause = s.clause ∧ (∀ i, s.resetShrinkable.isSh i = false) ∧
    s.resetShrinkable.shrinkable.view = [] ∧ Good s0 s.resetShrinkable B ∧
    (∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned) → s.resetShrinkable.abit i c = s.abit i c) ∧
    Listed s.resetShrinkable := by
  have hsz : ∀ j, j < s.shrinkable.size → (s.shrinkable.get! j).toNat < s.asg.aBits.size := by
    intro j hj
    have hm : s.shrinkable.get! j ∈ s.shrinkable.view := by
      rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj),
        Option.getD_some]; exact List.getElem_mem _
    obtain ⟨y, hy, hf⟩ := h.listA _ hm
    rw [h.af.bitsSize, ← hy]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf
    unfold ValidLit at this; omega
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := clearBitsDown_spec s.shrinkable ABits.shrinkable (Or.inl rfl)
    s.shrinkable.size s 0 hsz
  have hclr : ∀ i, (s.clearBitsDown s.shrinkable ABits.shrinkable s.shrinkable.size 0).abit i ABits.shrinkable = false := by
    intro i
    cases hx : (s.clearBitsDown s.shrinkable ABits.shrinkable s.shrinkable.size 0).abit i ABits.shrinkable
    · rfl
    · exfalso
      obtain ⟨h1, h2⟩ := c4 i hx
      obtain ⟨j, hj, hjx⟩ := mem_view_get! _ _ (h.shL i h1)
      exact h2 (s.shrinkable.size - 1 - j) (Nat.zero_le _) (by omega) (by rw [show s.shrinkable.size - 1 - (s.shrinkable.size - 1 - j) = j by omega]; exact hjx)
  unfold resetShrinkable
  refine ⟨AF.trans_left h.af (AF.trans_left c1 af_rfl), c2, c3, fun i => ?_, ?_, ?_, fun i c hc => ?_, ?_⟩
  · cases hx : (s.clearBitsDown s.shrinkable ABits.shrinkable s.shrinkable.size 0).abit i ABits.shrinkable
    · exact hx
    · exfalso
      obtain ⟨h1, h2⟩ := c4 i hx
      obtain ⟨j, hj, hjx⟩ := mem_view_get! _ _ (h.shL i h1)
      exact h2 (s.shrinkable.size - 1 - j) (Nat.zero_le _) (by omega) (by rw [show s.shrinkable.size - 1 - (s.shrinkable.size - 1 - j) = j by omega]; exact hjx)
  · show (s.shrinkable.clear).view = []
    simp [U32Vec.clear, U32Vec.view_shrink]
  · exact h.good.mono_mf (fun j => by
      show (s.clearBitsDown s.shrinkable ABits.shrinkable s.shrinkable.size 0).isRem j = true ↔ _
      rw [c2])
  · exact c5 i c (by rcases hc with rfl | rfl <;> decide) (by rcases hc with rfl | rfl <;> simp)
  · intro c hc i hi
    have hi' : (s.clearBitsDown s.shrinkable ABits.shrinkable s.shrinkable.size 0).abit i c = true := hi
    by_cases ec : c = ABits.shrinkable
    · subst ec; rw [hclr] at hi'; exact absurd hi' (by simp)
    · have hne : c ≠ ABits.shrinkable := ec
      rw [c5 i c hne (by rcases hc with h | h | h | h <;> simp [h])] at hi'
      have := h.listed c hc i hi'
      rw [← c6 c] at this
      unfold anaList at this ⊢
      rcases hc with rfl | rfl | rfl | rfl
      · exact this
      · exact this
      · exact this
      · exact absurd rfl hne

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem blockPositionsOK_spec (s : Solver) (maxTrail e : Nat) :
    ∀ p, s.blockPositionsOK p e maxTrail = true → ∀ q, p ≤ q → q < e →
      s.clause.get! q ≠ INVALID_LIT ∧ (s.trailIdx (IDX (s.clause.get! q))).toNat ≤ maxTrail ∧
      (s.trailIdx (IDX (s.clause.get! q))).toNat < s.asg.trail.size ∧
      IDX (s.asg.trail.get! (s.trailIdx (IDX (s.clause.get! q))).toNat) = IDX (s.clause.get! q) := by
  intro p
  fun_induction blockPositionsOK s p e maxTrail with
  | case1 p hp lit q' ih =>
    intro hok q hq1 hq2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hok
    by_cases e' : q = p
    · subst e'; exact ⟨h1, h2, h3, h4⟩
    · exact ih h5 q (by omega) hq2
  | case2 p hp => intro _ q hq1 hq2; omega

theorem shrinkBlockLits_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (level : UInt32) (t b0 e : Nat)
    (hpre : ∀ q, b0 ≤ q → q < e → B.getD q 0 ≠ INVALID_LIT → s0.IsFalse (B.getD q 0) ∧
      (0 < s0.lvl (B.getD q 0) → ∃ p, p ≤ t ∧ s0.trailL[p]? = some (NOT (B.getD q 0)))) :
    ∀ (s : Solver) (p : Nat), b0 ≤ p → ShInv s0 B s t s.shrinkable.view.length →
    ShInv s0 B (s.shrinkBlockLits level p e) t (s.shrinkBlockLits level p e).shrinkable.view.length ∧
    (∃ N, (s.shrinkBlockLits level p e).shrinkable.view = s.shrinkable.view ++ N ∧ N.length ≤ e - p ∧
      (N.length = e - p → ∀ q, p ≤ q → q < e →
        (s.shrinkBlockLits level p e).isSh (IDX (s.clause.get! q)) = true)) ∧
    (∀ j, s.isSh j = true → (s.shrinkBlockLits level p e).isSh j = true) ∧
    (∀ j, s.isRem j = true → (s.shrinkBlockLits level p e).isRem j = true) ∧
    (s.shrinkBlockLits level p e).clause = s.clause := by
  intro s p
  fun_induction shrinkBlockLits s level p e with
  | case1 s p hp lit s' ih =>
    intro hbp h
    have hlit : lit = B.getD p 0 := by
      show s.clause.get! p = _; rw [U32Vec.get!_eq_view, h.clause]
    by_cases hinv : lit = INVALID_LIT
    · have hs' : s' = s := by simp [s', hinv]
      rw [hs'] at ih ⊢
      obtain ⟨i1, ⟨N, n1, n2, n3⟩, i3, i4, i5⟩ := ih (by omega) h
      refine ⟨i1, ⟨N, n1, by omega, fun hl => by omega⟩, i3, i4, i5⟩
    · obtain ⟨hf, hpos⟩ := hpre p hbp hp (by rw [← hlit]; exact hinv)
      rw [← hlit] at hf hpos
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := h.shrinkLit hb level hf hpos
      obtain ⟨_, _, _, r4', _⟩ := shrinkLiteral_spec hb B s level lit h.af (h.clause ▸ h.good) hf
      have hs' : s' = (s.shrinkLiteral level lit).2 := by simp [s', hinv]
      have hcl : s'.clause = s.clause := by
        rw [hs']; exact (shrinkLiteral_spec hb B s level lit h.af (h.clause ▸ h.good) hf).1.clause
      have hlen : s'.shrinkable.view.length =
          s.shrinkable.view.length + (if (s.shrinkLiteral level lit).1 = 1 then 1 else 0) := by
        rw [hs', r4']; split <;> simp
      have h' : ShInv s0 B s' t s'.shrinkable.view.length := by rw [hlen, hs']; exact r1
      obtain ⟨i1, ⟨N, n1, n2, n3⟩, i3, i4, i5⟩ := ih (by omega) h'
      refine ⟨i1, ⟨(if (s.shrinkLiteral level lit).1 = 1 then [IDX lit] else []) ++ N, ?_, ?_, ?_⟩,
        fun j hj => i3 j (by rw [hs']; exact r5 j hj), fun j hj => i4 j (by rw [hs']; exact r7 j hj),
        by rw [i5, hcl]⟩
      · rw [n1, hs', r4', List.append_assoc]
      · split <;> simp <;> omega
      · intro hl q hq1 hq2
        have h1 : (s.shrinkLiteral level lit).1 = 1 := by
          by_cases hc : (s.shrinkLiteral level lit).1 = 1
          · exact hc
          · rw [ite_eq_right hc] at hl; simp at hl; omega
        rw [ite_eq_left h1] at hl; simp at hl
        by_cases eq : q = p
        · subst eq
          exact i3 _ (by rw [hs']; exact r3 h1)
        · rw [← hcl]; exact n3 (by omega) q (by omega) hq2
  | case2 s p hp =>
    intro _ h
    exact ⟨h, ⟨[], by simp, by simp, fun hl q hq1 hq2 => absurd hq2 (by omega)⟩, fun j hj => hj,
      fun j hj => hj, rfl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem invalidateBlock_spec (e : Nat) :
    ∀ (s : Solver) (p cnt : Nat), ∃ c : U32Vec, (s.invalidateBlock p e cnt).2 = { s with clause := c } ∧
      c.size = s.clause.size ∧
      ∀ q, c.get! q = if p ≤ q ∧ q < e ∧ q < s.clause.size then INVALID_LIT else s.clause.get! q := by
  intro s p cnt
  fun_induction invalidateBlock s p e cnt with
  | case1 s p cnt hp hinv ih =>
    obtain ⟨c, h1, h2, h3⟩ := ih
    refine ⟨c, h1, h2, fun q => ?_⟩
    rw [h3]
    by_cases eq : q = p
    · subst eq
      have : s.clause.get! q = INVALID_LIT := beq_iff_eq.mp hinv
      by_cases hq : q < s.clause.size
      · simp [hq, hp, this]
      · simp [hq]
    · by_cases h' : p + 1 ≤ q ∧ q < e ∧ q < s.clause.size
      · rw [ite_eq_left h', ite_eq_left ⟨by omega, h'.2⟩]
      · rw [ite_eq_right h', ite_eq_right (fun h'' => h' ⟨by omega, h''.2⟩)]
  | case2 s p cnt hp hinv ih =>
    obtain ⟨c, h1, h2, h3⟩ := ih
    refine ⟨c, h1, by rw [h2]; simp, fun q => ?_⟩
    rw [h3]
    simp only [U32Vec.size_set!, U32Vec.get!_set!]
    by_cases eq : q = p
    · subst eq; by_cases hq : q < s.clause.size <;> simp [hq, hp]
    · by_cases h' : p + 1 ≤ q ∧ q < e ∧ q < s.clause.size
      · rw [ite_eq_left h', ite_eq_left ⟨by omega, h'.2⟩]
      · have n1 : ¬ (p = q ∧ q < s.clause.size) := fun h'' => eq h''.1.symm
        have n2 : ¬ (p ≤ q ∧ q < e ∧ q < s.clause.size) := fun h'' => h' ⟨by omega, h''.2⟩
        rw [ite_eq_right h', ite_eq_right n1, ite_eq_right n2]
  | case3 s p cnt hp =>
    refine ⟨s.clause, rfl, rfl, fun q => ?_⟩
    rw [ite_eq_right (fun h => hp (by omega))]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem setABit_abit' (s : Solver) (idx i : UInt32) (b c : UInt8) (on : Bool) (hsz : idx.toNat < s.asg.aBits.size)
    (hb : AnaBit b) (hc : AnaBit c) :
    (s.setABit idx b on).abit i c = if idx = i ∧ b = c then on else s.abit i c := by
  apply abit_setABit s idx i b c on hsz
  rcases hb with rfl | rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem markShrinkableLoop_spec (v : U32Vec) (n : Nat) :
    ∀ (s : Solver) (k : Nat), s.shrinkable = v → (∀ j, j < n → (v.get! j).toNat < s.asg.aBits.size) →
    AF (s.markShrinkableLoop n k) s ∧ (s.markShrinkableLoop n k).clause = s.clause ∧
    (s.markShrinkableLoop n k).shrinkable = s.shrinkable ∧
    (∀ i, s.isRem i = true → (s.markShrinkableLoop n k).isRem i = true) ∧
    (∀ j, k ≤ j → j < n → (s.markShrinkableLoop n k).isRem (v.get! (n - 1 - j)) = true) ∧
    (∀ i, (s.markShrinkableLoop n k).isRem i = true → s.isRem i = true ∨
      ∃ j, k ≤ j ∧ j < n ∧ v.get! (n - 1 - j) = i) ∧
    (∀ i, (s.markShrinkableLoop n k).isSh i = true → s.isSh i = true ∧
      ∀ j, k ≤ j → j < n → v.get! (n - 1 - j) ≠ i) ∧
    (∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned) → (s.markShrinkableLoop n k).abit i c = s.abit i c) ∧
    (s.markShrinkableLoop n k).analyzed = s.analyzed ∧ (s.markShrinkableLoop n k).poisoned = s.poisoned ∧
    ((∀ i, s.isRem i = true → i ∈ s.removable.view) →
      ∀ i, (s.markShrinkableLoop n k).isRem i = true → i ∈ (s.markShrinkableLoop n k).removable.view) := by
  intro s k
  fun_induction markShrinkableLoop s n k with
  | case1 s k hk idx s1 s2 ih =>
    intro hv hsz
    have hidx : idx = v.get! (n - 1 - k) := by show s.shrinkable.get! _ = _; rw [hv]
    have hsz0 : idx.toNat < s.asg.aBits.size := by rw [hidx]; exact hsz _ (by omega)
    have a1 : ∀ i c, AnaBit c → s1.abit i c = if idx = i ∧ ABits.shrinkable = c then false else s.abit i c :=
      fun i c hc => setABit_abit' s idx i _ c false hsz0 anaBit_shrinkable hc
    have f1 : AF s1 s := setABit_af s idx _ false shrinkable_bin
    have hsz1 : idx.toNat < s1.asg.aBits.size := by rw [f1.bitsSize]; exact hsz0
    have r1 : ∀ i, s1.isRem i = s.isRem i := by
      intro i; unfold isRem; rw [a1 i _ anaBit_removable]; simp [show ABits.shrinkable ≠ ABits.removable by decide]
    -- step facts for s2
    have st : AF s2 s ∧ s2.clause = s.clause ∧ s2.shrinkable = s.shrinkable ∧
        (∀ i, s2.isRem i = true ↔ s.isRem i = true ∨ i = idx) ∧
        (∀ i, s2.isSh i = if idx = i then false else s.isSh i) ∧
        (∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned) → s2.abit i c = s.abit i c) ∧
        s2.analyzed = s.analyzed ∧ s2.poisoned = s.poisoned ∧
        ((∀ i, s.isRem i = true → i ∈ s.removable.view) → ∀ i, s2.isRem i = true → i ∈ s2.removable.view) ∧
        (∀ j, j < n → (v.get! j).toNat < s2.asg.aBits.size) := by
      have hsh1 : ∀ i, s1.isSh i = if idx = i then false else s.isSh i := by
        intro i; unfold isSh; rw [a1 i _ anaBit_shrinkable]; simp
      have ho1 : ∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned) → s1.abit i c = s.abit i c := by
        intro i c hc
        rw [a1 i c (by rcases hc with rfl | rfl; exact anaBit_analyzed; exact anaBit_poisoned)]
        have : ABits.shrinkable ≠ c := by rcases hc with rfl | rfl <;> decide
        simp [this]
      by_cases hr : s1.abit idx ABits.removable = true
      · have e2 : s2 = s1 := by simp [s2, hr]
        rw [e2]
        refine ⟨f1, rfl, rfl, fun i => ?_, hsh1, ho1, rfl, rfl, fun hl i hi => ?_, fun j hj => by
          rw [f1.bitsSize]; exact hsz j hj⟩
        · rw [r1]; constructor
          · exact Or.inl
          · rintro (h | rfl)
            · exact h
            · rw [← r1]; exact hr
        · rw [r1] at hi; exact hl i hi
      · have e2 : s2 = s1.pushRemovable idx := by simp [s2, hr]
        rw [e2]
        obtain ⟨m1, m2, m3, _⟩ := pushRemovable_mf s1 idx hsz1
        refine ⟨m1.af.trans f1, rfl, rfl, fun i => ?_, fun i => by rw [← hsh1]; exact m1.shrinkable i, fun i c hc => ?_,
          rfl, rfl, fun hl i hi => ?_, fun j hj => by rw [m1.af.bitsSize, f1.bitsSize]; exact hsz j hj⟩
        · constructor
          · intro h; rcases m3 i h with h' | h'
            · exact Or.inl (by rw [← r1]; exact h')
            · exact Or.inr h'
          · rintro (h | rfl)
            · exact m1.rem i (by rw [r1]; exact h)
            · exact m2
        · rcases hc with rfl | rfl
          · rw [m1.analyzed]; exact ho1 i _ (Or.inl rfl)
          · show (s1.setABit idx ABits.removable true).abit i ABits.poisoned = _
            rw [setABit_true_abit s1 idx i _ _ hsz1 anaBit_removable anaBit_poisoned]
            simp [show ABits.removable ≠ ABits.poisoned by decide]; exact ho1 i _ (Or.inr rfl)
        · show i ∈ (s1.removable.push idx).view
          rw [U32Vec.view_push]
          rcases m3 i hi with h' | h'
          · exact List.mem_append_left _ (hl i (by rw [← r1]; exact h'))
          · subst h'; simp
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := st
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := ih (by rw [b3, hv]) b10
    refine ⟨c1.trans b1, by rw [c2, b2], by rw [c3, b3], fun i hi => c4 i ((b4 i).mpr (Or.inl hi)), ?_, ?_, ?_,
      fun i c hc => by rw [c8 i c hc, b6 i c hc], by rw [c9, b7], by rw [c10, b8], fun hl => c11 (b9 hl)⟩
    · intro j hj1 hj2
      by_cases ej : j = k
      · subst ej; rw [← hidx]; exact c4 _ ((b4 _).mpr (Or.inr rfl))
      · exact c5 j (by omega) hj2
    · intro i hi
      rcases c6 i hi with h' | ⟨j, hj1, hj2, hj3⟩
      · rcases (b4 i).mp h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨k, Nat.le_refl _, hk, by rw [← hidx, h'']⟩
      · exact Or.inr ⟨j, by omega, hj2, hj3⟩
    · intro i hi
      obtain ⟨h1, h2⟩ := c7 i hi
      rw [b5] at h1
      by_cases e : idx = i
      · simp [e] at h1
      · simp [e] at h1
        refine ⟨h1, fun j hj1 hj2 => ?_⟩
        by_cases ej : j = k
        · subst ej; rw [← hidx]; exact e
        · exact h2 j (by omega) hj2
  | case2 s k hk =>
    intro _ _
    exact ⟨AF.refl _, rfl, rfl, fun _ h => h, fun j hj1 hj2 => absurd hj2 (by omega), fun i h => Or.inl h,
      fun i h => ⟨h, fun j hj1 hj2 => absurd hj2 (by omega)⟩, fun _ _ _ => rfl, rfl, rfl, fun hl => hl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem get!_mem_view (v : U32Vec) (q : Nat) (hq : q < v.size) : v.get! q ∈ v.view :=
  U32Vec.get!_mem_view v q hq

theorem mem_view_pos (v : U32Vec) (y : UInt32) (h : y ∈ v.view) : ∃ q, q < v.size ∧ v.get! q = y :=
  U32Vec.mem_view_pos v y h

theorem markShrinkableAsRemovable_eq (s : Solver) :
    s.markShrinkableAsRemovable =
      { s.markShrinkableLoop s.shrinkable.size 0 with shrinkable := (s.markShrinkableLoop s.shrinkable.size 0).shrinkable.clear } := rfl

/-- Facts about `markShrinkableAsRemovable` on a shrinking state. -/
theorem markShrinkableAsRemovable_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (hs : AF s s0) (hl : Listed s)
    (hlistA : ∀ i ∈ s.shrinkable.view, ∃ y, IDX y = i ∧ s0.IsFalse y) :
    AF s.markShrinkableAsRemovable s0 ∧ s.markShrinkableAsRemovable.clause = s.clause ∧
    (∀ i, s.isRem i = true → s.markShrinkableAsRemovable.isRem i = true) ∧
    (∀ i ∈ s.shrinkable.view, s.markShrinkableAsRemovable.isRem i = true) ∧
    (∀ i, s.markShrinkableAsRemovable.isRem i = true → s.isRem i = true ∨ i ∈ s.shrinkable.view) ∧
    (∀ i, s.markShrinkableAsRemovable.isSh i = false) ∧ s.markShrinkableAsRemovable.shrinkable.view = [] ∧
    (∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned) → s.markShrinkableAsRemovable.abit i c = s.abit i c) ∧
    Listed s.markShrinkableAsRemovable := by
  have hsz : ∀ j, j < s.shrinkable.size → (s.shrinkable.get! j).toNat < s.asg.aBits.size := by
    intro j hj
    obtain ⟨y, hy, hf⟩ := hlistA _ (get!_mem_view _ _ hj)
    rw [hs.bitsSize, ← hy]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf
    unfold ValidLit at this; omega
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ :=
    markShrinkableLoop_spec s.shrinkable s.shrinkable.size s 0 rfl hsz
  rw [markShrinkableAsRemovable_eq]
  generalize s.markShrinkableLoop s.shrinkable.size 0 = t at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 ⊢
  have hidx : ∀ i ∈ s.shrinkable.view, ∃ j, 0 ≤ j ∧ j < s.shrinkable.size ∧ s.shrinkable.get! (s.shrinkable.size - 1 - j) = i := by
    intro i hi
    obtain ⟨q, hq, hqi⟩ := mem_view_pos _ _ hi
    exact ⟨s.shrinkable.size - 1 - q, Nat.zero_le _, by omega, by rw [show s.shrinkable.size - 1 - (s.shrinkable.size - 1 - q) = q by omega]; exact hqi⟩
  have hnosh : ∀ i, t.isSh i = false := by
    intro i
    cases hx : t.isSh i
    · rfl
    · exfalso
      obtain ⟨h1, h2⟩ := c7 i hx
      have := hl _ anaBit_shrinkable i h1
      simp only [anaList, show ABits.shrinkable ≠ ABits.analyzed by decide, show ABits.shrinkable ≠ ABits.poisoned by decide,
        show ABits.shrinkable ≠ ABits.removable by decide, ite_false] at this
      obtain ⟨j, _, hj, hji⟩ := hidx i this
      exact h2 j (Nat.zero_le _) hj hji
  refine ⟨AF.trans_left hs (AF.trans_left c1 af_rfl), c2, c4, fun i hi => ?_, fun i hi => ?_, hnosh,
    by show t.shrinkable.clear.view = []; simp [U32Vec.clear, U32Vec.view_shrink], c8, ?_⟩
  · obtain ⟨j, _, hj, hji⟩ := hidx i hi
    rw [← hji]; exact c5 j (Nat.zero_le _) hj
  · rcases c6 i hi with h' | ⟨j, _, hj, hji⟩
    · exact Or.inl h'
    · exact Or.inr (by rw [← hji]; exact get!_mem_view _ _ (by omega))
  · intro c hc i hi
    have hi' : t.abit i c = true := hi
    rcases hc with rfl | rfl | rfl | rfl
    · rw [c8 i _ (Or.inl rfl)] at hi'
      have := hl _ anaBit_analyzed i hi'
      show i ∈ (if ABits.analyzed = ABits.analyzed then t.analyzed.view else _)
      rw [ite_eq_left rfl, c9]; simpa [anaList] using this
    · rw [c8 i _ (Or.inr rfl)] at hi'
      have := hl _ anaBit_poisoned i hi'
      show i ∈ (if ABits.poisoned = ABits.analyzed then _ else if ABits.poisoned = ABits.poisoned then t.poisoned.view else _)
      rw [ite_eq_right (by decide), ite_eq_left rfl, c10]
      simpa [anaList, show ABits.poisoned ≠ ABits.analyzed by decide] using this
    · have := c11 (fun j hj => by
        have := hl _ anaBit_removable j hj
        simpa [anaList, show ABits.removable ≠ ABits.analyzed by decide,
          show ABits.removable ≠ ABits.poisoned by decide] using this) i hi'
      show i ∈ (if ABits.removable = ABits.analyzed then _ else if ABits.removable = ABits.poisoned then _
        else if ABits.removable = ABits.removable then t.removable.view else _)
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; exact this
    · have := hnosh i; unfold isSh at this; rw [this] at hi'; exact absurd hi' (by simp)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Replacing literals of `B` by others keeps `Good` as long as every lost false literal of
  positive level has a closed reason. -/
theorem Good.replace {s0 s : Solver} {B B' : List Lit} (h : Good s0 s B)
    (hB : ∀ y ∈ B, s0.IsFalse y → 0 < s0.lvl y → y ∈ B' ∨ RCE s0 s [] y) : Good s0 s B' := by
  intro i hi
  obtain ⟨y, h1, h2, h3, h4⟩ := h i hi
  refine ⟨y, h1, h2, h3, ?_⟩
  rcases h4 with h4 | h4
  · exact hB y h4 h2 h3
  · exact Or.inr h4

theorem shrunkenBlock_eq (s : Solver) (b e : Nat) (uip : Lit) (c : U32Vec)
    (hc : (s.invalidateBlock b e 0).2 = { s with clause := c }) :
    (s.shrunkenBlock b e uip).2 =
      (if !({ s with clause := c.set! b (NOT uip) } : Solver).isAnalyzed (IDX uip)
        then ({ s with clause := c.set! b (NOT uip) } : Solver).pushAnalyzed (IDX uip)
        else ({ s with clause := c.set! b (NOT uip) } : Solver)).markShrinkableAsRemovable := by
  have : s.invalidateBlock b e 0 = ((s.invalidateBlock b e 0).1, { s with clause := c }) := by
    rw [← hc]
  unfold shrunkenBlock
  rw [this]

theorem shrunkenBlock_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {B : List Lit} {s : Solver} (h : ShFin s0 B s) {b e : Nat} (hbe : b < e) (hes : e ≤ s.clause.size)
    {uip : Lit} (hu : s0.IsTrue uip) (_hul : 0 < s0.lvl uip) (_hush : s.isSh (IDX uip) = true)
    (hrce : ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isSh (IDX y) = true → IDX y ≠ IDX uip →
      RCE s0 s s.shrinkable.view y)
    (hblk : ∀ q, b ≤ q → q < e → s.isSh (IDX (s.clause.get! q)) = true) :
    AF (s.shrunkenBlock b e uip).2 s0 ∧ (s.shrunkenBlock b e uip).2.clause.size = s.clause.size ∧
    (∀ q, (s.shrunkenBlock b e uip).2.clause.get! q =
      if q = b then NOT uip else if b ≤ q ∧ q < e then INVALID_LIT else s.clause.get! q) ∧
    Good s0 (s.shrunkenBlock b e uip).2 (s.shrunkenBlock b e uip).2.clause.view ∧
    (∀ i, s.isRem i = true → (s.shrunkenBlock b e uip).2.isRem i = true) ∧
    (∀ i, (s.shrunkenBlock b e uip).2.isSh i = false) ∧ (s.shrunkenBlock b e uip).2.shrinkable.view = [] ∧
    Listed (s.shrunkenBlock b e uip).2 := by
  obtain ⟨c, hc1, hc2, hc3⟩ := invalidateBlock_spec e s b 0
  rw [shrunkenBlock_eq s b e uip c hc1]
  have hnu : s0.IsFalse (NOT uip) := (hb.inv.core.valCons uip).1.mp hu
  have hszu : (IDX uip).toNat < s.asg.aBits.size := by
    rw [h.af.bitsSize, ← IDX_NOT]; have := hb.inv.rsizes.2.1; have := hb.valid_false hnu
    unfold ValidLit at this; omega
  generalize hs2 : ({ s with clause := c.set! b (NOT uip) } : Solver) = s2
  have a2 : AF s2 s := by rw [← hs2]; exact af_rfl
  have cl2 : s2.clause = c.set! b (NOT uip) := by rw [← hs2]
  have ab2 : ∀ i c', s2.abit i c' = s.abit i c' := by intro i c'; rw [← hs2]; rfl
  have sh2 : s2.shrinkable = s.shrinkable := by rw [← hs2]
  have li2 : Listed s2 := by rw [← hs2]; exact h.listed
  -- s3: optionally mark the uip analyzed
  have st3 : ∀ s3 : Solver, s3 = (if !s2.isAnalyzed (IDX uip) then s2.pushAnalyzed (IDX uip) else s2) →
      AF s3 s ∧ s3.clause = s2.clause ∧ s3.shrinkable = s.shrinkable ∧ Listed s3 ∧
      (∀ i, s3.isRem i = s.isRem i) ∧ (∀ i, s3.isSh i = s.isSh i) := by
    intro s3 hs3
    have hsz2 : (IDX uip).toNat < s2.asg.aBits.size := by rw [a2.bitsSize]; exact hszu
    by_cases ha : s2.isAnalyzed (IDX uip) = true
    · have : s3 = s2 := by rw [hs3]; simp [ha]
      subst this
      exact ⟨a2, rfl, sh2, li2, fun i => ab2 i _, fun i => ab2 i _⟩
    · have : s3 = s2.pushAnalyzed (IDX uip) := by rw [hs3]; simp [ha]
      subst this
      refine ⟨(pushAnalyzed_af s2 _).trans a2, rfl, sh2, pushAnalyzed_listed s2 _ hsz2 li2, fun i => ?_, fun i => ?_⟩
      · unfold isRem; rw [pushAnalyzed_abit s2 _ i hsz2 _ (Or.inr (Or.inr (Or.inl rfl)))]
        simp [show ABits.removable ≠ ABits.analyzed by decide]; exact ab2 i _
      · unfold isSh; rw [pushAnalyzed_abit s2 _ i hsz2 _ (Or.inr (Or.inr (Or.inr rfl)))]
        simp [show ABits.shrinkable ≠ ABits.analyzed by decide]; exact ab2 i _
  generalize hs3 : (if !s2.isAnalyzed (IDX uip) then s2.pushAnalyzed (IDX uip) else s2) = s3
  obtain ⟨a3, cl3, sh3, li3, rm3, ish3⟩ := st3 s3 hs3.symm
  have hlistA : ∀ i ∈ s3.shrinkable.view, ∃ y, IDX y = i ∧ s0.IsFalse y := by
    rw [sh3]; exact h.listA
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, _, m9⟩ :=
    markShrinkableAsRemovable_spec hb (a3.trans h.af) li3 hlistA
  generalize s3.markShrinkableAsRemovable = t at m1 m2 m3 m4 m5 m6 m7 m9 ⊢
  have hcl : t.clause = c.set! b (NOT uip) := by rw [m2, cl3, cl2]
  have hsz : t.clause.size = s.clause.size := by rw [hcl]; simp [hc2]
  have hget : ∀ q, t.clause.get! q =
      if q = b then NOT uip else if b ≤ q ∧ q < e then INVALID_LIT else s.clause.get! q := by
    intro q
    rw [hcl, U32Vec.get!_set!, hc3, hc2]
    by_cases eq : q = b
    · subst eq; simp [show q < s.clause.size by omega]
    · rw [ite_eq_right (fun h' => eq h'.1.symm), ite_eq_right eq]
      by_cases h' : b ≤ q ∧ q < e
      · rw [ite_eq_left ⟨h'.1, h'.2, by omega⟩, ite_eq_left h']
      · rw [ite_eq_right (fun h'' => h' ⟨h''.1, h''.2.1⟩), ite_eq_right h']
  have hrem : ∀ i, s.isRem i = true → t.isRem i = true := fun i hi => m3 i (by rw [rm3]; exact hi)
  have hshrem : ∀ i ∈ s.shrinkable.view, t.isRem i = true := by
    intro i hi; exact m4 i (by rw [sh3]; exact hi)
  have hNotUip : NOT uip ∈ t.clause.view := by
    have := get!_mem_view t.clause b (by omega)
    rw [hget, ite_eq_left rfl] at this; exact this
  -- a shrinkable false literal is in the new clause or has a closed reason
  have hsh : ∀ y, s0.IsFalse y → 0 < s0.lvl y → s.isSh (IDX y) = true →
      y ∈ t.clause.view ∨ RCE s0 t [] y := by
    intro y hf hl hy
    by_cases eu : IDX y = IDX uip
    · left
      have : y = NOT uip := hb.false_same_var hnu hf (by rw [IDX_NOT, eu])
      rw [this]; exact hNotUip
    · right
      exact (hrce y hf hl hy eu).mono hrem (fun j hj => Or.inr (hshrem j hj))
  refine ⟨m1, hsz, hget, ?_, hrem, m6, m7, m9⟩
  intro i hi
  rcases m5 i hi with h' | h'
  · rw [rm3] at h'
    obtain ⟨y, h1, h2, h3, h4⟩ := h.good i h'
    refine ⟨y, h1, h2, h3, ?_⟩
    rcases h4 with h4 | h4
    · rw [← h.clause] at h4
      obtain ⟨q, hq, hqy⟩ := mem_view_pos _ _ h4
      by_cases hqb : b ≤ q ∧ q < e
      · have := hblk q hqb.1 hqb.2
        rw [hqy] at this
        exact hsh y h2 h3 this
      · left
        have := get!_mem_view t.clause q (by omega)
        rw [hget] at this
        by_cases eq : q = b
        · exact absurd ⟨by omega, by omega⟩ hqb
        · rw [ite_eq_right eq, ite_eq_right hqb, hqy] at this; exact this
    · right; exact h4.mono hrem (fun j hj => by simp at hj)
  · obtain ⟨y, h1, h2, h3⟩ := h.shA i (h.listSh i (by rw [← sh3]; exact h'))
    refine ⟨y, h1, h2, h3, ?_⟩
    exact hsh y h2 h3 (by rw [h1]; exact h.listSh i (by rw [← sh3]; exact h'))

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem invalidateBlock_count (e : Nat) :
    ∀ (s : Solver) (p cnt : Nat), (∀ q, p ≤ q → q < e → s.clause.get! q ≠ INVALID_LIT) →
      (s.invalidateBlock p e cnt).1 = cnt + (e - p) := by
  intro s p cnt
  fun_induction invalidateBlock s p e cnt with
  | case1 s p cnt hp hinv ih =>
    intro h; exact absurd (beq_iff_eq.mp hinv) (h p (Nat.le_refl _) hp)
  | case2 s p cnt hp hinv ih =>
    intro h
    rw [ih (fun q hq1 hq2 => by
      show (s.clause.set! p INVALID_LIT).get! q ≠ _
      rw [U32Vec.get!_set!_ne _ _ _ _ (by omega)]; exact h q (by omega) hq2)]
    omega
  | case3 s p cnt hp => intro _; omega

theorem shrunkenBlock_fst (s : Solver) (b e : Nat) (uip : Lit) :
    (s.shrunkenBlock b e uip).1 = (s.invalidateBlock b e 0).1 - 1 := rfl

/-- A checked block position yields the negation of the literal on the trail. -/
theorem trail_pos_of_check {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (hs : AF s s0) {lit : Lit} (hf : s0.IsFalse lit) {q : Nat}
    (hq : q < s.asg.trail.size) (hidx : IDX (s.asg.trail.get! q) = IDX lit) :
    s0.trailL[q]? = some (NOT lit) := by
  have hq' : q < s0.trailL.length := by unfold trailL; rw [← hs.trail]; simpa using hq
  have hx : s0.trailL[q]? = some (s.asg.trail.get! q) := by
    unfold trailL at hq' ⊢
    rw [List.getElem?_eq_getElem hq', U32Vec.get!_eq_view, hs.trail, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hq', Option.getD_some]
  rw [hx]
  have ht : s0.IsTrue (s.asg.trail.get! q) := hb.inv.core.trailTrue _ (List.mem_of_getElem? hx)
  rcases (IDX_eq_iff _ lit).mp hidx with e | e
  · rw [e] at ht; exact absurd ⟨ht, hf⟩ (hb.inv.core.valCons lit).2
  · rw [e]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The state invariant between blocks of `shrinkClause`. -/
structure BPre (s0 s : Solver) : Prop where
  af : AF s s0
  good : Good s0 s s.clause.view
  listed : Listed s
  noSh : ∀ i, s.isSh i = false
  lits : ∀ q, q < s.clause.size → s.clause.get! q ≠ INVALID_LIT →
    s0.IsFalse (s.clause.get! q) ∧ 0 < s0.lvl (s.clause.get! q)

/-- The result of processing one block. -/
def BOut (s0 s t : Solver) (b e : Nat) (n : Nat) : Prop :=
  BPre s0 t ∧ t.clause.size = s.clause.size ∧ (∀ i, s.isRem i = true → t.isRem i = true) ∧
  ((n = 0 ∧ t.clause.view = s.clause.view) ∨
   (n ≠ 0 ∧ ∃ x, s0.IsFalse x ∧ 0 < s0.lvl x ∧ ∀ q, t.clause.get! q =
      if q = b then x else if b ≤ q ∧ q < e then INVALID_LIT else s.clause.get! q))

theorem BPre.shInv {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (_hb : DBase Φ s0 L)
    {s : Solver} (h : BPre s0 s) (hse : s.shrinkable.view = []) {t : Nat} (ht : t < s0.trailL.length) :
    ShInv s0 s.clause.view s t s.shrinkable.view.length := by
  refine ⟨h.af, rfl, h.good, fun i hi => by rw [h.noSh] at hi; simp at hi,
    fun i hi => by rw [h.noSh] at hi; simp at hi, fun y _ _ hy => by rw [h.noSh] at hy; simp at hy,
    ?_, ht, fun i hi => by rw [hse] at hi; simp at hi, fun i hi => by rw [hse] at hi; simp at hi,
    h.listed⟩
  rw [hse]; unfold shCount; symm
  rw [List.length_nil, List.countP_eq_zero]; intro l _; rw [h.noSh]; simp

theorem shrinkBlock_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (h : BPre s0 s) {b e : Nat} (hbe : b + 2 ≤ e) (hes : e ≤ s.clause.size)
    (level : UInt32) (maxTrail : Nat) :
    BOut s0 s (s.shrinkBlock b e level maxTrail).2 b e (s.shrinkBlock b e level maxTrail).1 := by
  unfold shrinkBlock
  simp only
  split
  · exact ⟨h, rfl, fun _ h => h, Or.inl ⟨rfl, rfl⟩⟩
  rename_i hpos
  have hlitsv : ∀ (t : Solver), t.clause.view = s.clause.view → ∀ q, t.clause.get! q = s.clause.get! q := by
    intro t ht q; rw [U32Vec.get!_eq_view, U32Vec.get!_eq_view, ht]
  have hsizev : ∀ (t : Solver), t.clause.view = s.clause.view → t.clause.size = s.clause.size := by
    intro t ht; rw [← U32Vec.length_view, ← U32Vec.length_view, ht]
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or, Bool.not_eq_false,
    Decidable.not_not] at hpos
  obtain ⟨⟨hmt, hse0⟩, hok⟩ := hpos
  have hse : s.shrinkable.view = [] := by
    apply List.eq_nil_of_length_eq_zero; rw [U32Vec.length_view]; simpa using hse0
  have hps := blockPositionsOK_spec s maxTrail e b hok
  have hmt' : maxTrail < s0.trailL.length := by unfold trailL; rw [← h.af.trail]; simpa using hmt
  have hpre : ∀ q, b ≤ q → q < e → s.clause.view.getD q 0 ≠ INVALID_LIT → s0.IsFalse (s.clause.view.getD q 0) ∧
      (0 < s0.lvl (s.clause.view.getD q 0) → ∃ p, p ≤ maxTrail ∧
        s0.trailL[p]? = some (NOT (s.clause.view.getD q 0))) := by
    intro q hqb hq hne
    rw [← U32Vec.get!_eq_view] at hne ⊢
    obtain ⟨hf, _⟩ := h.lits q (by omega) hne
    refine ⟨hf, fun _ => ?_⟩
    obtain ⟨_, p1, p2, p3⟩ := hps q hqb hq
    exact ⟨_, p1, trail_pos_of_check hb h.af hf p2 p3⟩
  obtain ⟨i1, ⟨N, n1, n2, n3⟩, i3, i4, i5⟩ :=
    shrinkBlockLits_spec hb s.clause.view level maxTrail b e hpre s b (Nat.le_refl _) (h.shInv hb hse hmt')
  generalize s.shrinkBlockLits level b e = s1 at i1 n1 n3 i3 i4 i5 ⊢
  rw [hse, List.nil_append] at n1
  have hres : ∀ (t : Solver), ShFin s0 s.clause.view t → (∀ i, s.isRem i = true → t.isRem i = true) →
      BOut s0 s t.resetShrinkable b e 0 := by
    intro t ht hrm
    obtain ⟨r1, r2, r3, r4, r5, r6, _, r8⟩ := resetShrinkable_spec hb ht
    have hv : t.resetShrinkable.clause.view = s.clause.view := by rw [r3, ht.clause]
    refine ⟨⟨r1, by rw [hv]; exact r6, r8, r4, fun q hq hne => ?_⟩, hsizev _ hv,
      fun i hi => by rw [r2]; exact hrm i hi, Or.inl ⟨rfl, hv⟩⟩
    rw [hlitsv _ hv] at hne ⊢; exact h.lits q (by rw [← hsizev _ hv]; exact hq) hne
  split
  · exact hres s1 i1.fin i4
  rename_i hsz
  have hlen : N.length = e - b := by
    have : s1.shrinkable.size = s.shrinkable.size + (e - b) := by simpa using hsz
    rw [← U32Vec.length_view, ← U32Vec.length_view s.shrinkable, n1, hse] at this; simpa using this
  have hall := n3 hlen
  have hinv : ShInv s0 s.clause.view s1 maxTrail (e - b) := by
    have := i1; rw [n1, hlen] at this; exact this
  have hout := shrinkBlockLoop_spec hb s.clause.view level (s1.options.shrink > 1) (s1.asg.trail.size + 1)
    s1 (e - b) maxTrail hinv (by omega)
  generalize s1.shrinkBlockLoop level (s1.options.shrink > 1) (e - b) maxTrail (s1.asg.trail.size + 1) = R at hout ⊢
  obtain ⟨uip, failed, s2⟩ := R
  obtain ⟨o1, o2, o3, o4⟩ := hout
  simp only at o1 o2 o3 o4 ⊢
  split
  · exact hres s2 o1 (fun i hi => o2 i (i4 i hi))
  rename_i hfl
  have hfl' : failed = false := by simpa using hfl
  obtain ⟨u1, u2, u3, u4⟩ := o4 hfl'
  have hv2 := o1.clause
  have hes2 : e ≤ s2.clause.size := by rw [hsizev _ hv2]; exact hes
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := shrunkenBlock_spec hb o1 (b := b) (e := e) (by omega) hes2 u1 u2 u3 u4
    (fun q hq1 hq2 => by rw [hlitsv _ hv2]; exact o3 _ (hall q hq1 hq2))
  have hnu : s0.IsFalse (NOT uip) := (hb.inv.core.valCons uip).1.mp u1
  have hnul : 0 < s0.lvl (NOT uip) := by rw [hb.inv.core.lvlVar]; exact u2
  refine ⟨⟨w1, w4, w8, w6, fun q hq hne => ?_⟩, by rw [w2, hsizev _ hv2], fun i hi => w5 i (o2 i (i4 i hi)),
    Or.inr ⟨?_, NOT uip, hnu, hnul, fun q => by rw [w3, hlitsv _ hv2]⟩⟩
  · rw [w3] at hne ⊢
    by_cases eq : q = b
    · rw [ite_eq_left eq]; exact ⟨hnu, hnul⟩
    · rw [ite_eq_right eq] at hne ⊢
      by_cases hq' : b ≤ q ∧ q < e
      · rw [ite_eq_left hq'] at hne; exact absurd rfl hne
      · rw [ite_eq_right hq'] at hne ⊢
        rw [hlitsv _ hv2] at hne ⊢
        exact h.lits q (by rw [w2, hsizev _ hv2] at hq; exact hq) hne
  · rw [shrunkenBlock_fst, invalidateBlock_count e s2 b 0 (fun q hq1 hq2 => by
      rw [hlitsv _ hv2]; exact (hps q hq1 hq2).1)]
    omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem minimizeTop_block {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (h : BPre s0 s) {p : Nat} (hp : p < s.clause.size) (hne : s.clause.get! p ≠ INVALID_LIT) :
    MF (s.minimizeLiteralTop (s.clause.get! p) true).2 s ∧
    Good s0 (s.minimizeLiteralTop (s.clause.get! p) true).2 s.clause.view ∧
    ((s.minimizeLiteralTop (s.clause.get! p) true).1 = true →
      RCE s0 (s.minimizeLiteralTop (s.clause.get! p) true).2 [] (s.clause.get! p)) := by
  obtain ⟨hf, hl⟩ := h.lits p hp hne
  obtain ⟨m1, m2, _, m4⟩ := (minimize_all hb s.clause.view false s.options.minimizedepth).1 s
    (s.clause.get! p) 0 h.af h.good hf
  unfold minimizeLiteralTop
  simp only [ite_true]
  refine ⟨m1, m2, fun hok => ?_⟩
  rcases m4 hok with h' | ⟨h', _⟩ | ⟨_, h'⟩
  · omega
  · exact absurd rfl h'
  · exact h'

theorem BPre.of_mf {s0 s t : Solver} (h : BPre s0 s) (hm : MF t s) (hg : Good s0 t s.clause.view) : BPre s0 t := by
  refine ⟨hm.af.trans h.af, by rw [hm.clause]; exact hg, hm.listed h.listed, fun i => ?_,
    fun q hq hne => by rw [hm.clause] at hq hne ⊢; exact h.lits q hq hne⟩
  have := hm.shrinkable i; unfold isSh; rw [this]; exact h.noSh i

theorem minimizeBlockLoop_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) (e : Nat) :
    ∀ (s : Solver) (p m : Nat), BPre s0 s → e ≤ s.clause.size →
    (∀ q, p ≤ q → q < e → s.clause.get! q ≠ INVALID_LIT) →
    BPre s0 (s.minimizeBlockLoop p e m).2 ∧ (s.minimizeBlockLoop p e m).2.clause.size = s.clause.size ∧
    (∀ i, s.isRem i = true → (s.minimizeBlockLoop p e m).2.isRem i = true) ∧
    (∀ q, q < p → (s.minimizeBlockLoop p e m).2.clause.get! q = s.clause.get! q) := by
  intro s p m
  fun_induction minimizeBlockLoop s p e m with
  | case1 s p m hp lit ok s' heq hnok ih =>
    intro h hes hinv
    obtain ⟨t1, t2, _⟩ := minimizeTop_block hb h (p := p) (by omega) (hinv p (Nat.le_refl _) hp)
    have e1 : (s.minimizeLiteralTop lit true).2 = s' := by rw [heq]
    rw [e1] at t1 t2
    have hcl := t1.clause
    obtain ⟨a1, a2, a3, a4⟩ := ih (BPre.of_mf h t1 t2) (by rw [hcl]; exact hes)
      (fun q hq1 hq2 => by rw [hcl]; exact hinv q (by omega) hq2)
    exact ⟨a1, by rw [a2, hcl], fun i hi => a3 i (t1.rem i hi), fun q hq => by rw [a4 q (by omega), hcl]⟩
  | case2 s p m hp lit ok s' heq hnok ih =>
    intro h hes hinv
    have hne := hinv p (Nat.le_refl _) hp
    obtain ⟨t1, t2, t3⟩ := minimizeTop_block hb h (p := p) (by omega) hne
    have e1 : (s.minimizeLiteralTop lit true).2 = s' := by rw [heq]
    have e2 : (s.minimizeLiteralTop lit true).1 = ok := by rw [heq]
    have hok : ok = true := by simpa using hnok
    rw [e1] at t1 t2 t3; rw [e2] at t3
    have hrce := t3 hok
    have hcl := t1.clause
    obtain ⟨hf, hl⟩ := h.lits p (by omega) hne
    generalize hs2 : ({ s' with clause := s'.clause.set! p INVALID_LIT } : Solver) = s2 at ih ⊢
    have cl2 : s2.clause = s.clause.set! p INVALID_LIT := by rw [← hs2, hcl]
    have hget2 : ∀ q, s2.clause.get! q = if q = p then INVALID_LIT else s.clause.get! q := by
      intro q; rw [cl2, U32Vec.get!_set!]
      by_cases eq : q = p
      · subst eq; simp [show q < s.clause.size by omega]
      · simp [Ne.symm eq, eq]
    have hsz2 : s2.clause.size = s.clause.size := by rw [cl2]; simp
    have hpre2 : BPre s0 s2 := by
      have hb' := BPre.of_mf h t1 t2
      refine ⟨by rw [← hs2]; exact AF.trans_left hb'.af af_rfl, ?_, by rw [← hs2]; exact hb'.listed,
        by rw [← hs2]; exact hb'.noSh, fun q hq hne' => ?_⟩
      · have hg : Good s0 s2 s.clause.view := by rw [← hs2]; exact t2
        apply Good.replace hg
        intro y hy hyf hyl
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
    obtain ⟨a1, a2, a3, a4⟩ := ih hpre2 (by rw [hsz2]; exact hes)
      (fun q hq1 hq2 => by rw [hget2, ite_eq_right (by omega)]; exact hinv q (by omega) hq2)
    refine ⟨a1, by rw [a2, hsz2], fun i hi => a3 i (by rw [← hs2]; exact t1.rem i hi), fun q hq => ?_⟩
    rw [a4 q (by omega), hget2, ite_eq_right (by omega)]
  | case3 s p m hp =>
    intro h _ _
    exact ⟨h, rfl, fun _ h => h, fun _ _ => rfl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem minimizeAndShrinkBlock_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (h : BPre s0 s) {E : Nat} (hes : E ≤ s.clause.size)
    (hpre : ∀ q, q < E → s.clause.get! q ≠ INVALID_LIT) :
    BPre s0 (s.minimizeAndShrinkBlock E).2 ∧ (s.minimizeAndShrinkBlock E).2.clause.size = s.clause.size ∧
    (∀ i, s.isRem i = true → (s.minimizeAndShrinkBlock E).2.isRem i = true) ∧
    (∀ q, q < (s.minimizeAndShrinkBlock E).1 → q < E → (s.minimizeAndShrinkBlock E).2.clause.get! q ≠ INVALID_LIT) := by
  unfold minimizeAndShrinkBlock
  generalize s.nextBlock E = nb
  obtain ⟨b, level, maxTrail⟩ := nb
  simp only
  split
  · exact ⟨h, rfl, fun _ h => h, fun q _ hq => hpre q hq⟩
  rename_i hop
  have hbe : b + 2 ≤ E := by omega
  obtain ⟨o1, o2, o3, o4⟩ := shrinkBlock_spec hb h hbe hes level maxTrail
  generalize s.shrinkBlock b E level maxTrail = R at o1 o2 o3 o4 ⊢
  obtain ⟨n, s1⟩ := R
  simp only at o1 o2 o3 o4 ⊢
  have hprefix : ∀ q, q < b → s1.clause.get! q ≠ INVALID_LIT := by
    intro q hq
    rcases o4 with ⟨_, hv⟩ | ⟨_, x, _, _, hx⟩
    · rw [U32Vec.get!_eq_view, hv, ← U32Vec.get!_eq_view]; exact hpre q (by omega)
    · rw [hx, ite_eq_right (by omega), ite_eq_right (by omega)]; exact hpre q (by omega)
  split
  · rename_i hn
    have hn' : n = 0 := by simpa using hn
    have hv : s1.clause.view = s.clause.view := by
      rcases o4 with ⟨_, hv⟩ | ⟨h', _⟩
      · exact hv
      · exact absurd hn' h'
    have hblk : ∀ q, b ≤ q → q < E → s1.clause.get! q ≠ INVALID_LIT := by
      intro q _ hq; rw [U32Vec.get!_eq_view, hv, ← U32Vec.get!_eq_view]; exact hpre q hq
    unfold minimizeBlock
    obtain ⟨m1, m2, m3, m4⟩ := minimizeBlockLoop_spec hb E s1 b 0 o1 (by rw [o2]; exact hes) hblk
    generalize s1.minimizeBlockLoop b E 0 = R at m1 m2 m3 m4 ⊢
    obtain ⟨_, s2⟩ := R
    simp only at m1 m2 m3 m4 ⊢
    exact ⟨m1, by rw [m2, o2], fun i hi => m3 i (o3 i hi), fun q hq _ => by rw [m4 q hq]; exact hprefix q hq⟩
  · exact ⟨o1, o2, o3, fun q hq _ => hprefix q hq⟩

theorem shrinkClauseLoop_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L) :
    ∀ (s : Solver) (E : Nat), BPre s0 s → E ≤ s.clause.size → (∀ q, q < E → s.clause.get! q ≠ INVALID_LIT) →
    BPre s0 (s.shrinkClauseLoop E) ∧ (s.shrinkClauseLoop E).clause.size = s.clause.size ∧
    (∀ i, s.isRem i = true → (s.shrinkClauseLoop E).isRem i = true) := by
  intro s E
  induction E using Nat.strongRecOn generalizing s with
  | _ E ih =>
    intro h hes hpre
    rw [shrinkClauseLoop]
    split
    · exact ⟨h, rfl, fun _ h => h⟩
    obtain ⟨a1, a2, a3, a4⟩ := minimizeAndShrinkBlock_spec hb h hes hpre
    generalize s.minimizeAndShrinkBlock E = R at a1 a2 a3 a4 ⊢
    obtain ⟨b, s1⟩ := R
    simp only at a1 a2 a3 a4 ⊢
    split
    · rename_i hbE
      obtain ⟨c1, c2, c3⟩ := ih b hbE s1 a1 (by rw [a2]; omega) (fun q hq => a4 q hq (by omega))
      exact ⟨c1, by rw [c2, a2], fun i hi => c3 i (a3 i hi)⟩
    · exact ⟨a1, a2, a3⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem compactLoop_spec (L0 : List UInt32) :
    ∀ (c : U32Vec) (p q : Nat), q ≤ p → c.view.length = L0.length → c.view.drop p = L0.drop p →
      c.view.take q = (L0.take p).filter (fun x => x != INVALID_LIT) →
      ((compactLoop c p q).1.shrink (compactLoop c p q).2).view = L0.filter (fun x => x != INVALID_LIT) := by
  intro c p q
  fun_induction compactLoop c p q with
  | case1 c p q hp lit hne ih =>
    intro hqp hlen hdrop htake
    have hpL : p < L0.length := by rw [← hlen]; simpa using hp
    have hlit : L0[p] = lit := by
      have h1 : (c.view.drop p)[0]? = (L0.drop p)[0]? := by rw [hdrop]
      simp only [List.getElem?_drop, Nat.add_zero] at h1
      rw [List.getElem?_eq_getElem hpL, List.getElem?_eq_getElem (by rw [hlen]; exact hpL)] at h1
      have h2 := Option.some.inj h1
      show L0[p] = c.get! p
      rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hpL),
        Option.getD_some, h2]
    apply ih (by omega) (by rw [U32Vec.view_set!, List.length_set, hlen])
    · rw [U32Vec.view_set!, List.drop_set_of_lt (by omega), ← List.drop_drop, hdrop, List.drop_drop]
    · rw [U32Vec.view_set!, take_set_succ _ _ _ (by rw [hlen]; omega), htake, List.take_add_one,
        List.getElem?_eq_getElem hpL, hlit, List.filter_append]
      simp [hne]
  | case2 c p q hp lit hne ih =>
    intro hqp hlen hdrop htake
    have hpL : p < L0.length := by rw [← hlen]; simpa using hp
    have hlit : L0[p] = lit := by
      have h1 : (c.view.drop p)[0]? = (L0.drop p)[0]? := by rw [hdrop]
      simp only [List.getElem?_drop, Nat.add_zero] at h1
      rw [List.getElem?_eq_getElem hpL, List.getElem?_eq_getElem (by rw [hlen]; exact hpL)] at h1
      have h2 := Option.some.inj h1
      show L0[p] = c.get! p
      rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hpL),
        Option.getD_some, h2]
    have hinv : lit = INVALID_LIT := by simpa using hne
    apply ih (by omega) hlen
    · rw [← List.drop_drop, hdrop, List.drop_drop]
    · rw [htake, List.take_add_one, List.getElem?_eq_getElem hpL, hlit, List.filter_append, hinv]
      simp
  | case3 c p q hp =>
    intro hqp hlen hdrop htake
    have hpL : L0.length ≤ p := by rw [← hlen]; simpa using hp
    rw [U32Vec.view_shrink, htake, List.take_of_length_le hpL]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem compactClause_eq (s : Solver) :
    s.compactClause = { s with clause := (compactLoop s.clause 0 0).1.shrink (compactLoop s.clause 0 0).2 } := rfl

theorem compactClause_view (s : Solver) :
    s.compactClause.clause.view = s.clause.view.filter (fun x => x != INVALID_LIT) := by
  rw [compactClause_eq]
  exact compactLoop_spec s.clause.view s.clause 0 0 (Nat.le_refl _) rfl rfl (by simp)

/-- `clearBitsUp` with a bit other than `removable`. -/
theorem clearBitsUp_spec (v : U32Vec) (b : UInt8) (hb : b = ABits.shrinkable ∨ b = ABits.poisoned) (n : Nat) :
    ∀ (s : Solver) (k : Nat),
    AF (s.clearBitsUp v b k n) s ∧ (∀ i, (s.clearBitsUp v b k n).isRem i = s.isRem i) ∧
    (s.clearBitsUp v b k n).clause = s.clause ∧
    (∀ i, (s.clearBitsUp v b k n).abit i b = true → s.abit i b = true ∧ ∀ j, k ≤ j → j < n → v.get! j ≠ i) ∧
    (∀ i c, c ≠ b → (c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.shrinkable ∨ c = ABits.removable) →
      (s.clearBitsUp v b k n).abit i c = s.abit i c) ∧
    (∀ c, (s.clearBitsUp v b k n).anaList c = s.anaList c) := by
  intro s k
  fun_induction clearBitsUp s v b k n with
  | case1 s k hk ih =>
    have hbin : b &&& ABits.binary = 0 := by rcases hb with rfl | rfl <;> decide
    have f := setABit_af s (v.get! k) b false hbin
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih
    by_cases hsz : (v.get! k).toNat < s.asg.aBits.size
    · have hab : ∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.shrinkable ∨ c = ABits.removable) →
          (s.setABit (v.get! k) b false).abit i c =
            if v.get! k = i ∧ b = c then false else s.abit i c := by
        intro i c hc
        apply abit_setABit s _ i b c false hsz
        by_cases e : b = c
        · exact Or.inl ⟨e, by subst e; rcases hb with rfl | rfl <;> decide⟩
        · refine Or.inr ⟨e, ?_⟩
          rcases hb with rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl e
      refine ⟨a1.trans f, ?_, ?_, ?_, ?_, fun c => by rw [a6]; rfl⟩
      · intro i
        rw [a2]
        unfold isRem
        rw [hab i _ (Or.inr (Or.inr (Or.inr rfl)))]
        have : b ≠ ABits.removable := by rcases hb with rfl | rfl <;> decide
        simp [this]
      · rw [a3]; rfl
      · intro i hi
        obtain ⟨h1, h2⟩ := a4 i hi
        rw [hab i _ (by rcases hb with rfl | rfl <;> simp)] at h1
        by_cases e : v.get! k = i
        · simp [e] at h1
        · simp [e] at h1
          refine ⟨h1, fun j hj1 hj2 => ?_⟩
          by_cases ej : j = k
          · subst ej; exact e
          · exact h2 j (by omega) hj2
      · intro i c hc hc'
        rw [a5 i c hc hc', hab i c hc']
        simp [Ne.symm hc]
    · -- out of range: `setABit` does nothing to the bits
      have hsame : ∀ i c, (s.setABit (v.get! k) b false).abit i c = s.abit i c := by
        intro i c
        unfold abit abits
        rw [setABit_bits]
        congr 1
        rw [ite_eq_right (fun h => hsz h.2)]
      refine ⟨a1.trans f, fun i => by rw [a2]; exact hsame i _, by rw [a3]; rfl, ?_, fun i c _ _ => by rw [a5 i c ‹_› ‹_›, hsame],
        fun c => by rw [a6]; rfl⟩
      intro i hi
      obtain ⟨h1, h2⟩ := a4 i hi
      rw [hsame] at h1
      refine ⟨h1, fun j hj1 hj2 => ?_⟩
      by_cases ej : j = k
      · subst ej
        intro e
        apply hsz
        have : s.abit i b = true := h1
        unfold abit abits at this
        rw [e]
        apply Classical.byContradiction
        intro hn
        rw [ByteArray.get!_oob _ _ hn] at this
        simp at this
      · exact h2 j (by omega) hj2
  | case2 s k hk =>
    exact ⟨AF.refl _, fun _ => rfl, rfl, fun i hi => ⟨hi, fun j hj1 hj2 => absurd hj2 (by omega)⟩,
      fun _ _ _ _ => rfl, fun _ => rfl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem resetPoisoned_eq (s : Solver) :
    s.resetPoisoned = { s.clearBitsUp s.poisoned ABits.poisoned 0 s.poisoned.size with
      poisoned := (s.clearBitsUp s.poisoned ABits.poisoned 0 s.poisoned.size).poisoned.clear } := rfl

theorem resetPoisoned_spec (s : Solver) (hl : Listed s) :
    AF s.resetPoisoned s ∧ (∀ i, s.resetPoisoned.isRem i = s.isRem i) ∧ s.resetPoisoned.clause = s.clause ∧
    (∀ i, s.resetPoisoned.abit i ABits.poisoned = false) ∧
    (∀ i c, (c = ABits.analyzed ∨ c = ABits.shrinkable ∨ c = ABits.removable) →
      s.resetPoisoned.abit i c = s.abit i c) ∧
    s.resetPoisoned.poisoned.view = [] ∧ s.resetPoisoned.shrinkable = s.shrinkable ∧
    Listed s.resetPoisoned := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := clearBitsUp_spec s.poisoned ABits.poisoned (Or.inr rfl) s.poisoned.size s 0
  rw [resetPoisoned_eq]
  have hcl : ∀ i, (s.clearBitsUp s.poisoned ABits.poisoned 0 s.poisoned.size).abit i ABits.poisoned = false := by
    intro i
    cases hx : (s.clearBitsUp s.poisoned ABits.poisoned 0 s.poisoned.size).abit i ABits.poisoned
    · rfl
    · exfalso
      obtain ⟨h1, h2⟩ := c4 i hx
      have := hl _ anaBit_poisoned i h1
      simp only [anaList, show ABits.poisoned ≠ ABits.analyzed by decide, ite_false, ite_true] at this
      obtain ⟨j, hj, hji⟩ := mem_view_pos _ _ this
      exact h2 j (Nat.zero_le _) hj hji
  have hsh : (s.clearBitsUp s.poisoned ABits.poisoned 0 s.poisoned.size).shrinkable = s.shrinkable := by
    have := c6 ABits.shrinkable
    simp only [anaList, show ABits.shrinkable ≠ ABits.analyzed by decide, show ABits.shrinkable ≠ ABits.poisoned by decide,
      show ABits.shrinkable ≠ ABits.removable by decide, ite_false] at this
    -- only the views agree; the vector itself is untouched by `setABit`
    clear this
    generalize hk : 0 = k
    have : ∀ (t : Solver) k, (t.clearBitsUp s.poisoned ABits.poisoned k s.poisoned.size).shrinkable = t.shrinkable := by
      intro t k
      fun_induction clearBitsUp t s.poisoned ABits.poisoned k s.poisoned.size with
      | case1 t k hk ih => rw [ih]; rfl
      | case2 t k hk => rfl
    exact this s k
  refine ⟨AF.trans_left c1 af_rfl, c2, c3, hcl, fun i c hc => c5 i c (by rcases hc with rfl | rfl | rfl <;> decide)
    (by rcases hc with rfl | rfl | rfl <;> simp), by simp [U32Vec.clear, U32Vec.view_shrink], hsh, ?_⟩
  intro c hc i hi
  have hi' : (s.clearBitsUp s.poisoned ABits.poisoned 0 s.poisoned.size).abit i c = true := hi
  by_cases ec : c = ABits.poisoned
  · subst ec; rw [hcl] at hi'; exact absurd hi' (by simp)
  · rw [c5 i c ec (by rcases hc with h | h | h | h <;> simp [h])] at hi'
    have := hl c hc i hi'
    rw [← c6 c] at this
    unfold anaList at this ⊢
    rcases hc with rfl | rfl | rfl | rfl
    · exact this
    · exact absurd rfl ec
    · exact this
    · exact this

/-- Result of `shrinkClause`. -/
structure ShrinkOut (s0 s t : Solver) : Prop where
  af : AF t s0
  good : Good s0 t t.clause.view
  listed : Listed t
  noSh : ∀ i, t.isSh i = false
  noPoison : ∀ i, t.abit i ABits.poisoned = false
  lits : ∀ y ∈ t.clause.view, y ≠ INVALID_LIT ∧ s0.IsFalse y ∧ 0 < s0.lvl y
  rem : ∀ i, s.isRem i = true → t.isRem i = true

theorem shrinkClause_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} (h : BPre s0 s) (hall : ∀ q, q < s.clause.size → s.clause.get! q ≠ INVALID_LIT) :
    ShrinkOut s0 s s.shrinkClause := by
  obtain ⟨l1, l2, l3⟩ := shrinkClauseLoop_spec hb s s.clause.size h (Nat.le_refl _) hall
  unfold shrinkClause
  simp only
  generalize s.shrinkClauseLoop s.clause.size = s1 at l1 l2 l3 ⊢
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
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := resetPoisoned_spec s2 li2
  have hsh2 : ∀ i, s2.isSh i = s1.isSh i := by intro i; rw [e2]; rfl
  have hshl : s2.shrinkable = s1.shrinkable := by rw [e2]
  refine ⟨r1.trans (a2.trans l1.af), ?_, r8, fun i => ?_, r4, ?_, ?_⟩
  · rw [r3]; exact g2.mono_mf (fun j => by rw [r2])
  · unfold isSh; rw [r5 i _ (Or.inr (Or.inl rfl))]; show s2.isSh i = false; rw [hsh2]; exact l1.noSh i
  · intro y hy
    rw [r3] at hy
    obtain ⟨hy1, hy2⟩ := hmem y hy
    obtain ⟨q, hq, hqy⟩ := mem_view_pos _ _ hy1
    rw [← hqy] at hy2 ⊢
    exact ⟨hy2, l1.lits q hq hy2⟩
  · intro i hi; rw [r2]; show s2.isRem i = true; rw [e2]; exact l3 i hi

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Every removable false literal is derivable from the clause justifying the marks. -/
theorem derFalse_of_good {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {t : Solver} {K : List Lit} (hg : Good s0 t K) :
    ∀ y, s0.IsFalse y → 0 < s0.lvl y → t.isRem (IDX y) = true → DerFalse s0 K y := by
  have key : ∀ n : Nat, ∀ y : Lit, s0.trailL[n]? = some (NOT y) → s0.IsFalse y → 0 < s0.lvl y →
      t.isRem (IDX y) = true → DerFalse s0 K y := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro y hn hf hl hr
      obtain ⟨y', h1, h2, _, h4⟩ := hg _ hr
      have hyy : y' = y := hb.false_same_var hf h2 h1
      subst hyy
      rcases h4 with h4 | ⟨A, hA, hA'⟩
      · exact .inK h4
      · refine .reason hA (fun x hx => ?_)
        have hax := hb.ante_of_antecedents hA hx
        rcases hA' x hx with h0 | hrx | hE
        · exact .root hax.1 h0
        · by_cases hlx : 0 < s0.lvl x
          · obtain ⟨q, hq, hqx⟩ := hb.ante_before hn hax hlx
            exact ih q hq x hqx hax.1 hlx hrx
          · exact .root hax.1 (by omega)
        · simp at hE
  intro y hf hl hr
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (hb.true_on_trail hf hl)
  exact key n y hn hf hl hr

end Solver
end LeanKissat
