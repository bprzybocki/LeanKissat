import LeanKissat.Proofs.Deduce

/-!
# Soundness of clause minimization

`Good s0 s B`: every variable marked `removable` has a false literal that is in the clause
buffer `B` or whose reason has only root-level or removable antecedents.
-/

namespace LeanKissat
namespace Solver

def isRem (s : Solver) (i : UInt32) : Bool := s.abit i ABits.removable

/-- Reason closed w.r.t. removable marks and an extra set `E` of variables. -/
def RCE (s0 s : Solver) (E : List UInt32) (y : Lit) : Prop :=
  ∃ A, s0.Antecedents (NOT y) A ∧ ∀ x ∈ A, s0.lvl x = 0 ∨ s.isRem (IDX x) = true ∨ IDX x ∈ E

def GoodE (s0 s : Solver) (B : List Lit) (E : List UInt32) : Prop :=
  ∀ i, s.isRem i = true → ∃ y, IDX y = i ∧ s0.IsFalse y ∧ 0 < s0.lvl y ∧ (y ∈ B ∨ RCE s0 s E y)

abbrev Good (s0 s : Solver) (B : List Lit) : Prop := GoodE s0 s B []

theorem RCE.mono {s0 s t : Solver} {E E' : List UInt32} {y : Lit} (h : RCE s0 s E y)
    (hm : ∀ i, s.isRem i = true → t.isRem i = true) (hE : ∀ i ∈ E, i ∈ E' ∨ t.isRem i = true) :
    RCE s0 t E' y := by
  obtain ⟨A, hA, hA'⟩ := h
  refine ⟨A, hA, fun x hx => ?_⟩
  rcases hA' x hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (hm _ h))
  · rcases hE _ h with h' | h'
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl h')

/-- The minimization frame: only `poisoned`/`removable` marks, stacks and counters change. -/
structure MF (t s : Solver) : Prop where
  af : AF t s
  clause : t.clause = s.clause
  analyzed : ∀ i, t.abit i ABits.analyzed = s.abit i ABits.analyzed
  shrinkable : ∀ i, t.abit i ABits.shrinkable = s.abit i ABits.shrinkable
  rem : ∀ i, s.isRem i = true → t.isRem i = true
  shList : t.shrinkable = s.shrinkable
  listed : Listed s → Listed t

theorem MF.refl (s : Solver) : MF s s := ⟨AF.refl _, rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, rfl, id⟩

theorem MF.trans {a b c : Solver} (h1 : MF a b) (h2 : MF b c) : MF a c :=
  ⟨h1.af.trans h2.af, h1.clause.trans h2.clause, fun i => (h1.analyzed i).trans (h2.analyzed i),
   fun i => (h1.shrinkable i).trans (h2.shrinkable i), fun i h => h1.rem i (h2.rem i h),
   h1.shList.trans h2.shList, fun h => h1.listed (h2.listed h)⟩

theorem pushRemovable_mf (s : Solver) (idx : UInt32) (hsz : idx.toNat < s.asg.aBits.size) :
    MF (s.pushRemovable idx) s ∧ (s.pushRemovable idx).isRem idx = true ∧
    (∀ i, (s.pushRemovable idx).isRem i = true → s.isRem i = true ∨ i = idx) ∧
    (s.pushRemovable idx).minimize = s.minimize := by
  have hb : ∀ i c, (c = ABits.analyzed ∨ c = ABits.poisoned ∨ c = ABits.shrinkable ∨ c = ABits.removable) →
      (s.pushRemovable idx).abit i c = if idx = i ∧ ABits.removable = c then true else s.abit i c := by
    intro i c hc
    show (s.setABit idx ABits.removable true).abit i c = _
    rw [abit_setABit s idx i _ c true hsz]
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · exact Or.inl ⟨rfl, by decide⟩
  refine ⟨⟨AF.trans_left (setABit_af s idx _ true removable_bin) af_rfl, rfl, fun i => ?_, fun i => ?_,
    fun i hi => ?_, rfl, pushRemovable_listed s idx hsz⟩, ?_, fun i hi => ?_, rfl⟩
  · rw [hb i _ (Or.inl rfl)]; simp [show ABits.removable ≠ ABits.analyzed by decide]
  · rw [hb i _ (Or.inr (Or.inr (Or.inl rfl)))]; simp [show ABits.removable ≠ ABits.shrinkable by decide]
  · unfold isRem at *; rw [hb i _ (Or.inr (Or.inr (Or.inr rfl)))]; split <;> simp_all
  · unfold isRem; rw [hb idx _ (Or.inr (Or.inr (Or.inr rfl)))]; simp
  · unfold isRem at *; rw [hb i _ (Or.inr (Or.inr (Or.inr rfl)))] at hi
    by_cases e : idx = i
    · exact Or.inr e.symm
    · simp [e] at hi; exact Or.inl hi

theorem pushPoisoned_mf (s : Solver) (idx : UInt32) (hsz : idx.toNat < s.asg.aBits.size) :
    MF (s.pushPoisoned idx) s ∧ (∀ i, (s.pushPoisoned idx).isRem i = s.isRem i) ∧
    (s.pushPoisoned idx).minimize = s.minimize := by
  have hb : ∀ i c, (c = ABits.analyzed ∨ c = ABits.shrinkable ∨ c = ABits.removable) →
      (s.pushPoisoned idx).abit i c = s.abit i c := by
    intro i c hc
    show (s.setABit idx ABits.poisoned true).abit i c = _
    rw [abit_setABit s idx i _ c true hsz]
    · have : ABits.poisoned ≠ c := by rcases hc with rfl | rfl | rfl <;> decide
      simp [this]
    · rcases hc with rfl | rfl | rfl <;> exact Or.inr ⟨by decide, by decide⟩
  refine ⟨⟨AF.trans_left (setABit_af s idx _ true poisoned_bin) af_rfl, rfl,
    fun i => hb i _ (Or.inl rfl), fun i => hb i _ (Or.inr (Or.inl rfl)),
    fun i hi => by unfold isRem at *; rw [hb i _ (Or.inr (Or.inr rfl))]; exact hi, rfl,
    pushPoisoned_listed s idx hsz⟩,
    fun i => by unfold isRem; rw [hb i _ (Or.inr (Or.inr rfl))], rfl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

section Motives
variable (s0 : Solver) (B : List Lit) (m : Bool) (maxD : Nat)

def ChainPre (s : Solver) (saved : Nat) (next : Lit) : Prop :=
  saved ≤ s.minimize.size ∧ ∀ v ∈ s.minimize.view.drop saved, ∃ y, IDX y = v ∧ s0.IsFalse y ∧
    0 < s0.lvl y ∧ ∃ A, s0.Antecedents (NOT y) A ∧ ∀ x ∈ A, s0.lvl x = 0 ∨ s.isRem (IDX x) = true ∨
      IDX x ∈ s.minimize.view.drop saved ∨ IDX x = IDX next

def ChainPost (s : Solver) (saved : Nat) : Prop :=
  saved ≤ s.minimize.size ∧ ∀ v ∈ s.minimize.view.drop saved, ∃ y, IDX y = v ∧ s0.IsFalse y ∧
    0 < s0.lvl y ∧ ∃ A, s0.Antecedents (NOT y) A ∧ ∀ x ∈ A, s0.lvl x = 0 ∨ s.isRem (IDX x) = true ∨
      IDX x ∈ s.minimize.view.drop saved

def M1 (s : Solver) (lit : Lit) (depth : Nat) : Prop :=
  AF s s0 → Good s0 s B → s0.IsFalse lit →
  MF (s.minimizeLiteral m maxD lit depth).2 s ∧ Good s0 (s.minimizeLiteral m maxD lit depth).2 B ∧
  (s.minimizeLiteral m maxD lit depth).2.minimize.view = s.minimize.view ∧
  ((s.minimizeLiteral m maxD lit depth).1 = true → s0.lvl lit = 0 ∨
    (depth ≠ 0 ∧ (s.minimizeLiteral m maxD lit depth).2.isRem (IDX lit) = true) ∨
    (depth = 0 ∧ RCE s0 (s.minimizeLiteral m maxD lit depth).2 [] lit))

def M3 (s : Solver) (ref : Ref) (notLit : Lit) (depth : Nat) (hd : depth ≤ maxD) (n i : Nat) : Prop :=
  AF s s0 → Good s0 s B → ref ∈ s0.arena.chain 0 s0.arena.sizeWards → n ≤ (s0.arena.size ref).toNat →
  (∀ k, k < n → s0.arena.lit ref k ≠ notLit → s0.IsFalse (s0.arena.lit ref k)) →
  MF (s.minimizeRefLoop m maxD ref notLit depth hd n i).2 s ∧
  Good s0 (s.minimizeRefLoop m maxD ref notLit depth hd n i).2 B ∧
  (s.minimizeRefLoop m maxD ref notLit depth hd n i).2.minimize.view = s.minimize.view ∧
  ((s.minimizeRefLoop m maxD ref notLit depth hd n i).1 = true → ∀ k, i ≤ k → k < n →
    s0.arena.lit ref k ≠ notLit → s0.lvl (s0.arena.lit ref k) = 0 ∨
      (s.minimizeRefLoop m maxD ref notLit depth hd n i).2.isRem (IDX (s0.arena.lit ref k)) = true)

def M2 (s : Solver) (ref : Ref) (lit : Lit) (depth : Nat) (hd : depth ≤ maxD) : Prop :=
  AF s s0 → Good s0 s B → ref ∈ s0.arena.chain 0 s0.arena.sizeWards →
  (∀ k, k < (s0.arena.size ref).toNat → s0.arena.lit ref k ≠ NOT lit → s0.IsFalse (s0.arena.lit ref k)) →
  MF (s.minimizeReference m maxD ref lit depth hd).2 s ∧
  Good s0 (s.minimizeReference m maxD ref lit depth hd).2 B ∧
  (s.minimizeReference m maxD ref lit depth hd).2.minimize.view = s.minimize.view ∧
  ((s.minimizeReference m maxD ref lit depth hd).1 = true → ∀ k, k < (s0.arena.size ref).toNat →
    s0.arena.lit ref k ≠ NOT lit → s0.lvl (s0.arena.lit ref k) = 0 ∨
      (s.minimizeReference m maxD ref lit depth hd).2.isRem (IDX (s0.arena.lit ref k)) = true)

def M4 (s : Solver) (lit : Lit) (depth : Nat) (hd : depth < maxD) (fuel : Nat) : Prop :=
  AF s s0 → Good s0 s B → s0.IsFalse lit →
  MF (s.minimizeBinary m maxD lit depth hd fuel).2 s ∧ Good s0 (s.minimizeBinary m maxD lit depth hd fuel).2 B ∧
  (s.minimizeBinary m maxD lit depth hd fuel).2.minimize.view = s.minimize.view ∧
  ((s.minimizeBinary m maxD lit depth hd fuel).1 = true → s0.lvl lit = 0 ∨
    (s.minimizeBinary m maxD lit depth hd fuel).2.isRem (IDX lit) = true)

def M5 (s : Solver) (next : Lit) (depth : Nat) (hd : depth < maxD) (fuel : Nat) : Prop :=
  ∀ saved, AF s s0 → Good s0 s B → s0.IsFalse next → ChainPre s0 s saved next →
  MF (s.minimizeBinaryChain m maxD next depth hd fuel).2 s ∧
  Good s0 (s.minimizeBinaryChain m maxD next depth hd fuel).2 B ∧
  (∃ T, (s.minimizeBinaryChain m maxD next depth hd fuel).2.minimize.view = s.minimize.view ++ T) ∧
  (∀ v ∈ (s.minimizeBinaryChain m maxD next depth hd fuel).2.minimize.view.drop saved,
    ∃ y, IDX y = v ∧ s0.IsFalse y ∧ 0 < s0.lvl y) ∧
  ((s.minimizeBinaryChain m maxD next depth hd fuel).1 = true →
    ChainPost s0 (s.minimizeBinaryChain m maxD next depth hd fuel).2 saved ∧
    (s0.lvl next = 0 ∨ (s.minimizeBinaryChain m maxD next depth hd fuel).2.isRem (IDX next) = true ∨
      IDX next ∈ (s.minimizeBinaryChain m maxD next depth hd fuel).2.minimize.view.drop saved))

end Motives

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem minimizedIndex_pos {s0 s : Solver} (h : AF s s0) (m : Bool) (lit : Lit) (depth : Nat)
    (hp : s.minimizedIndex m (IDX lit) depth > 0) :
    s0.lvl lit = 0 ∨ (s.isRem (IDX lit) = true ∧ depth ≠ 0) := by
  unfold minimizedIndex at hp
  simp only at hp
  split at hp
  · rename_i h0; left
    have := (levelIdx_eq_zero s lit).mp h0; rwa [h.lvl] at this
  split at hp
  · rename_i h1; right; simp at h1; exact ⟨h1.1, h1.2⟩
  split at hp
  · simp at hp
  split at hp
  · simp at hp
  split at hp
  · simp at hp
  · simp at hp

theorem minimizedIndex_zero {s0 s : Solver} (h : AF s s0) (m : Bool) (lit : Lit) (depth : Nat)
    (hp : ¬ s.minimizedIndex m (IDX lit) depth > 0) (hn : ¬ s.minimizedIndex m (IDX lit) depth < 0) :
    s0.lvl lit ≠ 0 ∧ s0.reasonOf lit ≠ DECISION_REASON ∧ ¬ (s.isRem (IDX lit) = true ∧ depth ≠ 0) := by
  unfold minimizedIndex at hp hn
  simp only at hp hn
  split at hp
  · simp at hp
  rename_i h0
  have h0' : s0.lvl lit ≠ 0 := fun e => h0 ((levelIdx_eq_zero s lit).mpr (by rw [h.lvl]; exact e))
  split at hp
  · simp at hp
  rename_i h1
  rw [if_neg h0, if_neg h1] at hn
  split at hn
  · simp at hn
  rename_i h2
  refine ⟨h0', fun e => h2 ?_, fun ⟨a, b⟩ => h1 (by simp [isRem] at a; simp [a, b])⟩
  show (s.reasonOf lit == DECISION_REASON) = true
  rw [h.reasonOf, e]; rfl

theorem minimizedIndex_ne_zero_pos {s0 s : Solver} (h : AF s s0) (m : Bool) (lit : Lit)
    (hp : s.minimizedIndex m (IDX lit) 1 > 0) : s0.lvl lit = 0 ∨ s.isRem (IDX lit) = true := by
  rcases minimizedIndex_pos h m lit 1 hp with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'.1

theorem ticks_mf (s : Solver) (b : Bool) :
    MF (if b then INC! s search_ticks else s) s ∧
    (if b then INC! s search_ticks else s).minimize = s.minimize ∧
    (∀ i, (if b then INC! s search_ticks else s).isRem i = s.isRem i) := by
  cases b
  · exact ⟨MF.refl _, rfl, fun _ => rfl⟩
  · exact ⟨⟨af_rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, rfl, fun h => h⟩, rfl, fun _ => rfl⟩

theorem ticks_mf' (s : Solver) :
    MF (if h : (s.options.minimizeticks != 0) = true then INC! s search_ticks else s) s ∧
    (if h : (s.options.minimizeticks != 0) = true then INC! s search_ticks else s).minimize = s.minimize ∧
    (∀ i, (if h : (s.options.minimizeticks != 0) = true then INC! s search_ticks else s).isRem i = s.isRem i) := by
  split
  · exact ⟨⟨af_rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, rfl, fun h => h⟩, rfl, fun _ => rfl⟩
  · exact ⟨MF.refl _, rfl, fun _ => rfl⟩

theorem GoodE.mono_mf {s0 s t : Solver} {B : List Lit} {E : List UInt32} (h : GoodE s0 s B E)
    (hrem : ∀ i, t.isRem i = true ↔ s.isRem i = true) : GoodE s0 t B E := by
  intro i hi
  obtain ⟨y, h1, h2, h3, h4⟩ := h i ((hrem i).mp hi)
  refine ⟨y, h1, h2, h3, h4.imp_right (fun hr => hr.mono (fun j hj => (hrem j).mpr hj) (fun j hj => Or.inl hj))⟩

theorem GoodE.push {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {s : Solver} {B : List Lit} {E : List UInt32} (h : GoodE s0 s B E) (hs : AF s s0)
    {y : Lit} (hy : s0.IsFalse y) (hl : 0 < s0.lvl y) (hj : y ∈ B ∨ RCE s0 (s.pushRemovable (IDX y)) E y) :
    GoodE s0 (s.pushRemovable (IDX y)) B E := by
  have hsz : (IDX y).toNat < s.asg.aBits.size := by
    rw [hs.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hy; unfold ValidLit at this; omega
  obtain ⟨p1, _, p3, _⟩ := pushRemovable_mf s (IDX y) hsz
  intro i hi
  rcases p3 i hi with hold | rfl
  · obtain ⟨y', h1, h2, h3, h4⟩ := h i hold
    exact ⟨y', h1, h2, h3, h4.imp_right (fun hr => hr.mono p1.rem (fun j hj => Or.inl hj))⟩
  · exact ⟨y, rfl, hy, hl, hj⟩

theorem markMinimizeStack_spec {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (E : List UInt32) (res : Bool) (n : Nat) :
    ∀ (s : Solver) (i : Nat), AF s s0 → GoodE s0 s B E →
    (∀ j, i ≤ j → j < n → ∃ y, IDX y = s.minimize.get! j ∧ s0.IsFalse y ∧ 0 < s0.lvl y ∧
      RCE s0 s E y) →
    MF (s.markMinimizeStack res i n) s ∧ GoodE s0 (s.markMinimizeStack res i n) B E ∧
    (s.markMinimizeStack res i n).minimize = s.minimize ∧
    (res = true → ∀ j, i ≤ j → j < n → (s.markMinimizeStack res i n).isRem (s.minimize.get! j) = true) := by
  intro s i
  fun_induction markMinimizeStack s res i n with
  | case1 s i hi idx s' ih =>
    intro hs hg hj
    obtain ⟨y, hy, hf, hl, hr⟩ := hj i (Nat.le_refl _) hi
    have hsz : idx.toNat < s.asg.aBits.size := by
      rw [hs.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf
      unfold ValidLit at this; simp only [idx]; rw [← hy]; omega
    -- the step
    have hidx : idx = IDX y := hy.symm
    have step : MF s' s ∧ GoodE s0 s' B E ∧ s'.minimize = s.minimize ∧ (res = true → s'.isRem idx = true) := by
      cases res with
      | false =>
        have e : s' = s.pushPoisoned idx := by simp [s']
        rw [e]
        obtain ⟨p1, p2, p3⟩ := pushPoisoned_mf s idx hsz
        exact ⟨p1, hg.mono_mf (fun j => by rw [p2]), p3, fun h => absurd h (by simp)⟩
      | true =>
        have e : s' = s.pushRemovable idx := by simp [s']
        rw [e, hidx]
        rw [hidx] at hsz
        obtain ⟨p1, p2, _, p4⟩ := pushRemovable_mf s (IDX y) hsz
        exact ⟨p1, hg.push hb hs hf hl (Or.inr (hr.mono p1.rem (fun j hj => Or.inl hj))), p4, fun _ => p2⟩
    obtain ⟨t1, t2, t3, t4⟩ := step
    have hs' : AF s' s0 := t1.af.trans hs
    obtain ⟨r1, r2, r3, r4⟩ := ih hs' t2 (fun j hj1 hj2 => by
      obtain ⟨y', hy', hf', hl', hr'⟩ := hj j (by omega) hj2
      exact ⟨y', by rw [t3]; exact hy', hf', hl', hr'.mono t1.rem (fun k hk => Or.inl hk)⟩)
    refine ⟨r1.trans t1, r2, r3.trans t3, fun hres j hj1 hj2 => ?_⟩
    by_cases e : j = i
    · subst e; exact r1.rem _ (t4 hres)
    · have := r4 hres j (by omega) hj2; rw [t3] at this; exact this
  | case2 s i hi =>
    intro hs hg _
    exact ⟨MF.refl _, hg, rfl, fun _ j hj1 hj2 => absurd hj2 (by omega)⟩

theorem markMinimizeStack_false {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (n : Nat) :
    ∀ (s : Solver) (i : Nat), AF s s0 → Good s0 s B →
    (∀ j, i ≤ j → j < n → ∃ y, IDX y = s.minimize.get! j ∧ s0.IsFalse y) →
    MF (s.markMinimizeStack false i n) s ∧ Good s0 (s.markMinimizeStack false i n) B ∧
    (s.markMinimizeStack false i n).minimize = s.minimize := by
  intro s i
  fun_induction markMinimizeStack s false i n with
  | case1 s i hi idx s' ih =>
    intro hs hg hj
    obtain ⟨y, hy, hf⟩ := hj i (Nat.le_refl _) hi
    have hsz : idx.toNat < s.asg.aBits.size := by
      rw [hs.bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf
      unfold ValidLit at this; simp only [idx]; rw [← hy]; omega
    have e : s' = s.pushPoisoned idx := by simp [s']
    obtain ⟨p1, p2, p3⟩ := pushPoisoned_mf s idx hsz
    rw [e] at ih ⊢
    obtain ⟨r1, r2, r3⟩ := ih (p1.af.trans hs) (hg.mono_mf (fun j => by rw [p2]))
      (fun j hj1 hj2 => by rw [p3]; exact hj j (by omega) hj2)
    exact ⟨r1.trans p1, r2, r3.trans p3⟩
  | case2 s i hi =>
    intro hs hg _
    exact ⟨MF.refl _, hg, rfl⟩

theorem GoodE.of_all_rem {s0 s : Solver} {B : List Lit} {E : List UInt32} (h : GoodE s0 s B E)
    (hE : ∀ i ∈ E, s.isRem i = true) : Good s0 s B := by
  intro i hi
  obtain ⟨y, h1, h2, h3, h4⟩ := h i hi
  exact ⟨y, h1, h2, h3, h4.imp_right (fun hr => hr.mono (fun _ h => h) (fun j hj => Or.inr (hE j hj)))⟩

theorem GoodE.weaken {s0 s : Solver} {B : List Lit} {E : List UInt32} (h : Good s0 s B) : GoodE s0 s B E := by
  intro i hi
  obtain ⟨y, h1, h2, h3, h4⟩ := h i hi
  exact ⟨y, h1, h2, h3, h4.imp_right (fun hr => hr.mono (fun _ h => h) (fun j hj => by simp at hj))⟩

theorem reasonOf_NOT (s : Solver) (l : Lit) : s.reasonOf (NOT l) = s.reasonOf l := by
  simp [reasonOf, IDX_NOT]
theorem binOf_NOT (s : Solver) (l : Lit) : s.binOf (NOT l) = s.binOf l := by
  simp [binOf, IDX_NOT]

/-- The recursive call of `minimizeLiteral` on a literal with an unknown status. -/
theorem minimize_call {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    {B : List Lit} {m : Bool} {maxD : Nat} {s : Solver} {lit : Lit} {depth : Nat} (hd : ¬ depth ≥ maxD)
    (hp : ¬ s.minimizedIndex m (IDX lit) depth > 0) (hn : ¬ s.minimizedIndex m (IDX lit) depth < 0)
    {res : Bool} {s1 : Solver}
    (hcall : (if h : s.isBinaryReason (IDX lit) = true then
        s.minimizeBinary m maxD (s.reasonIdx (IDX lit)) depth (by omega) (s.vars.toNat + 1)
      else s.minimizeReference m maxD (s.reasonIdx (IDX lit)) lit depth (by omega)) = (res, s1))
    (ih4 : M4 s0 B m maxD s (s.reasonIdx (IDX lit)) depth (by omega) (s.vars.toNat + 1))
    (ih2 : M2 s0 B m maxD s (s.reasonIdx (IDX lit)) lit depth (by omega))
    (hs : AF s s0) (hg : Good s0 s B) (hf : s0.IsFalse lit) :
    MF s1 s ∧ Good s0 s1 B ∧ s1.minimize.view = s.minimize.view ∧
    (res = true → RCE s0 s1 [] lit) := by
  obtain ⟨z1, z2, _⟩ := minimizedIndex_zero hs m lit depth hp hn
  have hnt : s0.IsTrue (NOT lit) := by
    have := (hb.inv.core.valCons (NOT lit)).1; rw [NOT_NOT] at this; exact this.mpr hf
  have hra := hb.inv.reasons (NOT lit) hnt (by rw [hb.inv.core.lvlVar]; omega)
  have eR : s.reasonIdx (IDX lit) = s0.reasonOf (NOT lit) := by
    rw [reasonOf_NOT]; show s.reasonOf lit = _; rw [hs.reasonOf]
  have eB : s.isBinaryReason (IDX lit) = s0.binOf (NOT lit) := by
    rw [binOf_NOT]; show s.binOf lit = _; rw [hs.binOf]
  have hndec : s0.reasonOf (NOT lit) ≠ DECISION_REASON := by rw [reasonOf_NOT]; exact z2
  split at hcall
  · rename_i hbin
    rw [eB] at hbin
    rcases hra with e | ⟨b1, b2, b3⟩ | ⟨b1, _⟩
    · exact absurd e hndec
    · obtain ⟨r1, r2, r3, r4⟩ := ih4 hs hg (by rw [eR]; exact b3.1)
      rw [hcall] at r1 r2 r3 r4
      refine ⟨r1, r2, r3, fun hres => ⟨[s0.reasonOf (NOT lit)], ⟨hnt, by rw [hb.inv.core.lvlVar]; omega,
        Or.inl ⟨b1, b2, rfl⟩⟩, fun x hx => ?_⟩⟩
      simp at hx; subst hx
      rcases r4 hres with h | h
      · rw [eR] at h; exact Or.inl h
      · rw [eR] at h; exact Or.inr (Or.inl h)
    · rw [b1] at hbin; exact absurd hbin (by simp)
  · rename_i hbin
    rw [eB] at hbin
    rcases hra with e | ⟨b1, _⟩ | ⟨b1, b2, b3, b4⟩
    · exact absurd e hndec
    · rw [b1] at hbin; exact absurd hbin (by simp)
    · have hr : s.reasonIdx (IDX lit) ∈ s0.arena.chain 0 s0.arena.sizeWards := by rw [eR]; exact b2.1
      obtain ⟨r1, r2, r3, r4⟩ := ih2 hs hg hr (fun k hk hne => by
        rw [eR] at hk hne ⊢; exact (b4 _ (lit_mem_litsL _ _ _ hk) hne).1)
      rw [hcall] at r1 r2 r3 r4
      refine ⟨r1, r2, r3, fun hres => ⟨(s0.clauseL (s0.reasonOf (NOT lit))).filter (fun x => x != NOT lit),
        ⟨hnt, by rw [hb.inv.core.lvlVar]; omega, Or.inr ⟨b1, hndec, b2, b3, fun x => by simp [List.mem_filter]⟩⟩,
        fun x hx => ?_⟩⟩
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      obtain ⟨k, hk, rfl⟩ := mem_litsL_iff.mp hx1
      have := r4 hres k (by rw [eR]; exact hk) (by rw [eR]; simpa using hx2)
      rw [eR] at this
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

theorem get!_mem_drop (v : U32Vec) (saved j : Nat) (h1 : saved ≤ j) (h2 : j < v.size) :
    v.get! j ∈ v.view.drop saved := by
  rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2),
    Option.getD_some]
  rw [List.mem_iff_getElem]
  exact ⟨j - saved, by simp; omega, by simp [show saved + (j - saved) = j by omega]⟩

theorem mem_drop_get! (v : U32Vec) (saved : Nat) (x : UInt32) (h : x ∈ v.view.drop saved) :
    ∃ j, saved ≤ j ∧ j < v.size ∧ v.get! j = x := by
  obtain ⟨k, hk, hx⟩ := List.mem_iff_getElem.mp h
  simp at hk
  refine ⟨saved + k, by omega, by omega, ?_⟩
  rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
    Option.getD_some]
  simpa using hx

theorem MF.setMinimize (t : Solver) (v : U32Vec) : MF ({ t with minimize := v } : Solver) t :=
  ⟨af_rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, rfl, fun h => h⟩

theorem minimize_all {Φ : (Nat → Bool) → Prop} {s0 : Solver} {L : Nat} (hb : DBase Φ s0 L)
    (B : List Lit) (m : Bool) (maxD : Nat) :
    (∀ s lit depth, M1 s0 B m maxD s lit depth) ∧
    (∀ s ref lit depth hd, M2 s0 B m maxD s ref lit depth hd) ∧
    (∀ s ref notLit depth hd n i, M3 s0 B m maxD s ref notLit depth hd n i) ∧
    (∀ s lit depth hd fuel, M4 s0 B m maxD s lit depth hd fuel) ∧
    (∀ s next depth hd fuel, M5 s0 B m maxD s next depth hd fuel) := by
  refine minimizeLiteral.mutual_induct m maxD (M1 s0 B m maxD) (M2 s0 B m maxD) (M3 s0 B m maxD)
    (M4 s0 B m maxD) (M5 s0 B m maxD) ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17
  case c1 =>
    intro s lit depth hd hs hg hf
    rw [minimizeLiteral, dif_pos hd]
    exact ⟨MF.refl _, hg, rfl, fun h => absurd h (by simp)⟩
  case c2 =>
    intro s lit depth hd idx tmp hp' hs hg hf
    have hp : s.minimizedIndex m (IDX lit) depth > 0 := hp'
    rw [minimizeLiteral, dif_neg hd]
    simp only
    rw [if_pos hp]
    refine ⟨MF.refl _, hg, rfl, fun _ => ?_⟩
    rcases minimizedIndex_pos hs m lit depth hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
  case c3 =>
    intro s lit depth hd idx tmp hp' hn' hs hg hf
    have hp : ¬ s.minimizedIndex m (IDX lit) depth > 0 := hp'
    have hn : s.minimizedIndex m (IDX lit) depth < 0 := hn'
    rw [minimizeLiteral, dif_neg hd]
    simp only
    rw [if_neg hp, if_pos hn]
    exact ⟨MF.refl _, hg, rfl, fun h => absurd h (by simp)⟩
  case c4 =>
    intro s lit depth hd idx tmp hp' hn' res s1 hcall hdz ih4 ih2 hs hg hf
    have hp : ¬ s.minimizedIndex m (IDX lit) depth > 0 := hp'
    have hn : ¬ s.minimizedIndex m (IDX lit) depth < 0 := hn'
    obtain ⟨c1, c2, c3, c4⟩ := minimize_call hb hd hp hn hcall ih4 ih2 hs hg hf
    rw [minimizeLiteral, dif_neg hd]
    simp only
    have hcall2 := hcall
    simp (config := {zetaDelta := true}) only [dite_eq_ite] at hcall2
    rw [if_neg hp, if_neg hn, hcall2]
    simp only
    rw [if_pos hdz]
    have hd0 : depth = 0 := by simpa using hdz
    exact ⟨c1, c2, c3, fun h => Or.inr (Or.inr ⟨hd0, c4 h⟩)⟩
  case c5 =>
    intro s lit depth hd idx tmp hp' hn' res s1 hcall hdz hres ih4 ih2 hs hg hf
    have hp : ¬ s.minimizedIndex m (IDX lit) depth > 0 := hp'
    have hn : ¬ s.minimizedIndex m (IDX lit) depth < 0 := hn'
    obtain ⟨c1, c2, c3, c4⟩ := minimize_call hb hd hp hn hcall ih4 ih2 hs hg hf
    rw [minimizeLiteral, dif_neg hd]
    simp only
    have hcall2 := hcall
    simp (config := {zetaDelta := true}) only [dite_eq_ite] at hcall2
    rw [if_neg hp, if_neg hn, hcall2]
    simp only
    rw [if_neg hdz, if_pos hres]
    have hsz : (IDX lit).toNat < s1.asg.aBits.size := by
      rw [(c1.af.trans hs).bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf
      unfold ValidLit at this; omega
    obtain ⟨p1, p2, p3⟩ := pushPoisoned_mf s1 (IDX lit) hsz
    exact ⟨p1.trans c1, c2.mono_mf (fun j => by rw [p2]), by rw [p3]; exact c3,
      fun h => absurd h (by simpa using hres)⟩
  case c6 =>
    intro s lit depth hd idx tmp hp' hn' res s1 hcall hdz hres hrem ih4 ih2 hs hg hf
    have hp : ¬ s.minimizedIndex m (IDX lit) depth > 0 := hp'
    have hn : ¬ s.minimizedIndex m (IDX lit) depth < 0 := hn'
    obtain ⟨c1, c2, c3, c4⟩ := minimize_call hb hd hp hn hcall ih4 ih2 hs hg hf
    obtain ⟨z1, _, _⟩ := minimizedIndex_zero hs m lit depth hp hn
    rw [minimizeLiteral, dif_neg hd]
    simp only
    have hcall2 := hcall
    simp (config := {zetaDelta := true}) only [dite_eq_ite] at hcall2
    rw [if_neg hp, if_neg hn, hcall2]
    simp only
    rw [if_neg hdz, if_neg hres, if_pos hrem]
    have hres' : res = true := by simpa using hres
    have hsz : (IDX lit).toNat < s1.asg.aBits.size := by
      rw [(c1.af.trans hs).bitsSize]; have := hb.inv.rsizes.2.1; have := hb.valid_false hf
      unfold ValidLit at this; omega
    obtain ⟨p1, p2, _, p4⟩ := pushRemovable_mf s1 (IDX lit) hsz
    exact ⟨p1.trans c1, c2.push hb (c1.af.trans hs) hf (by omega)
        (Or.inr ((c4 hres').mono p1.rem (fun j hj => by simp at hj))),
      by rw [p4]; exact c3, fun _ => Or.inr (Or.inl ⟨by simpa using hdz, p2⟩)⟩
  case c7 =>
    intro s lit depth hd idx tmp hp' hn' res s1 hcall hdz hres hrem ih4 ih2 hs hg hf
    have hp : ¬ s.minimizedIndex m (IDX lit) depth > 0 := hp'
    have hn : ¬ s.minimizedIndex m (IDX lit) depth < 0 := hn'
    obtain ⟨c1, c2, c3, c4⟩ := minimize_call hb hd hp hn hcall ih4 ih2 hs hg hf
    rw [minimizeLiteral, dif_neg hd]
    simp only
    have hcall2 := hcall
    simp (config := {zetaDelta := true}) only [dite_eq_ite] at hcall2
    rw [if_neg hp, if_neg hn, hcall2]
    simp only
    rw [if_neg hdz, if_neg hres, if_neg hrem]
    have hr : s1.isRem (IDX lit) = true := by
      have : s1.abit idx ABits.removable = true := by simpa using hrem
      exact this
    exact ⟨c1, c2, c3, fun _ => Or.inr (Or.inl ⟨by simpa using hdz, hr⟩)⟩
  case c8 =>
    intro s ref lit depth hd notLit s1 ih3 hs hg hr hlits
    obtain ⟨t1, t2, t3⟩ := ticks_mf' s
    have t1' : MF s1 s := t1
    have t2' : s1.minimize = s.minimize := t2
    have t3' : ∀ i, s1.isRem i = s.isRem i := t3
    have hs1 : AF s1 s0 := t1'.af.trans hs
    have hsz : (s1.arena.size ref).toNat = (s0.arena.size ref).toNat := by
      rw [hs1.arena.size ref hr]
    obtain ⟨r1, r2, r3, r4⟩ := ih3 hs1 (hg.mono_mf (fun j => by rw [t3'])) hr (Nat.le_of_eq hsz) (by
      intro k hk hne; exact hlits k (by rw [hsz] at hk; exact hk) hne)
    have e : s.minimizeReference m maxD ref lit depth hd =
        s1.minimizeRefLoop m maxD ref notLit depth hd (s1.arena.size ref).toNat 0 := by
      rw [minimizeReference]
      simp only [s1, notLit, dite_eq_ite]
    rw [e]
    refine ⟨r1.trans t1', r2, by rw [r3, t2'], fun hres k hk hne => ?_⟩
    exact r4 hres k (Nat.zero_le _) (by rw [hsz]; exact hk) hne
  case c9 =>
    intro s ref notLit depth hd n i hi other heq ih hs hg hr hn hlits
    obtain ⟨r1, r2, r3, r4⟩ := ih hs hg hr hn hlits
    rw [minimizeRefLoop, dif_pos hi]
    simp only
    rw [if_pos heq]
    refine ⟨r1, r2, r3, fun hres k hk1 hk2 hne => ?_⟩
    by_cases e : k = i
    · subst e
      exfalso; apply hne
      have : other = s0.arena.lit ref k := hs.lit_eq hr (by omega)
      rw [← this]; exact beq_iff_eq.mp heq
    · exact r4 hres k (by omega) hk2 hne
  case c10 =>
    intro s ref notLit depth hd n i hi other hne res s1 hcall hres ih1 hs hg hr hn hlits
    have ho : other = s0.arena.lit ref i := hs.lit_eq hr (by omega)
    have hne' : s0.arena.lit ref i ≠ notLit := by rw [← ho]; intro e; exact hne (beq_iff_eq.mpr e)
    obtain ⟨r1, r2, r3, _⟩ := ih1 hs hg (by rw [ho]; exact hlits i hi hne')
    rw [hcall] at r1 r2 r3
    rw [minimizeRefLoop, dif_pos hi]
    simp only
    rw [if_neg hne, hcall]
    simp only
    rw [if_pos hres]
    exact ⟨r1, r2, r3, fun h => absurd h (by simp)⟩
  case c11 =>
    intro s ref notLit depth hd n i hi other hne res s1 hcall hres ih1 ih3 hs hg hr hn hlits
    have ho : other = s0.arena.lit ref i := hs.lit_eq hr (by omega)
    have hne' : s0.arena.lit ref i ≠ notLit := by rw [← ho]; intro e; exact hne (beq_iff_eq.mpr e)
    obtain ⟨r1, r2, r3, r4⟩ := ih1 hs hg (by rw [ho]; exact hlits i hi hne')
    rw [hcall] at r1 r2 r3 r4
    simp only at r4
    have hres' : res = true := by simpa using hres
    obtain ⟨q1, q2, q3, q4⟩ := ih3 (r1.af.trans hs) r2 hr hn hlits
    rw [minimizeRefLoop, dif_pos hi]
    simp only
    rw [if_neg hne, hcall]
    simp only
    rw [if_neg hres]
    refine ⟨q1.trans r1, q2, by rw [q3, r3], fun h k hk1 hk2 hk3 => ?_⟩
    by_cases e : k = i
    · subst e
      rcases r4 hres' with h1 | ⟨_, h1⟩ | ⟨h1, _⟩
      · exact Or.inl (by rw [← ho]; exact h1)
      · exact Or.inr (q1.rem _ (by rw [← ho]; exact h1))
      · omega
    · exact q4 h k (by omega) hk2 hk3
  case c12 =>
    intro s ref notLit depth hd n i hi hs hg hr hn hlits
    rw [minimizeRefLoop, dif_neg hi]
    exact ⟨MF.refl _, hg, rfl, fun _ k hk1 hk2 => absurd hk2 (by omega)⟩
  case c13 =>
    intro s lit depth hd fuel res s1 hch ih5 hs hg hf
    obtain ⟨r1, r2, ⟨T, r3⟩, r5, r4⟩ := ih5 s.minimize.size hs hg hf ⟨Nat.le_refl _, fun v hv => by
      simp [List.drop_of_length_le] at hv⟩
    rw [hch] at r1 r2 r3 r4 r5
    simp only at r1 r2 r3 r4 r5
    have hs1 : AF s1 s0 := r1.af.trans hs
    have hsize : s.minimize.size ≤ s1.minimize.size := by
      have := congrArg List.length r3; simp at this; omega
    rw [minimizeBinary]
    simp only [hch]
    unfold finishMinimizeStack
    have hview : ∀ (t : Solver), t.minimize = s1.minimize →
        ({ t with minimize := t.minimize.shrink s.minimize.size } : Solver).minimize.view = s.minimize.view := by
      intro t ht
      show (t.minimize.shrink s.minimize.size).view = _
      rw [U32Vec.view_shrink, ht, r3, List.take_append_of_le_length (by simp)]
      simp [List.take_of_length_le]
    cases res with
    | false =>
      obtain ⟨q1, q2, q3⟩ := markMinimizeStack_false hb B s1.minimize.size s1 s.minimize.size hs1 r2
        (fun j hj1 hj2 => by
          obtain ⟨y, hy, hf', _⟩ := r5 _ (get!_mem_drop _ _ _ hj1 hj2)
          exact ⟨y, hy, hf'⟩)
      exact ⟨(MF.setMinimize _ _).trans (q1.trans r1), q2, hview _ q3, fun h => absurd h (by simp)⟩
    | true =>
      obtain ⟨c1, c2⟩ := r4 rfl
      obtain ⟨_, c3⟩ := c1
      have hj : ∀ j, s.minimize.size ≤ j → j < s1.minimize.size → ∃ y, IDX y = s1.minimize.get! j ∧
          s0.IsFalse y ∧ 0 < s0.lvl y ∧ RCE s0 s1 (s1.minimize.view.drop s.minimize.size) y := by
        intro j hj1 hj2
        obtain ⟨y, hy, hf', hl', A, hA, hA'⟩ := c3 _ (get!_mem_drop _ _ _ hj1 hj2)
        exact ⟨y, hy, hf', hl', A, hA, hA'⟩
      obtain ⟨q1, q2, q3, q4⟩ := markMinimizeStack_spec hb B (s1.minimize.view.drop s.minimize.size) true
        s1.minimize.size s1 s.minimize.size hs1 r2.weaken hj
      have hallrem : ∀ x ∈ s1.minimize.view.drop s.minimize.size,
          (s1.markMinimizeStack true s.minimize.size s1.minimize.size).isRem x = true := by
        intro x hx
        obtain ⟨j, hj1, hj2, rfl⟩ := mem_drop_get! _ _ _ hx
        exact q4 rfl j hj1 hj2
      refine ⟨(MF.setMinimize _ _).trans (q1.trans r1), q2.of_all_rem hallrem, hview _ q3, fun _ => ?_⟩
      rcases c2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (q1.rem _ h)
      · exact Or.inr (hallrem _ h)
  case c14 =>
    intro s next depth hd saved hs hg hf hpre
    rw [minimizeBinaryChain]
    exact ⟨MF.refl _, hg, ⟨[], by simp⟩, fun v hv => by
      obtain ⟨y, h1, h2, h3, _⟩ := hpre.2 v hv; exact ⟨y, h1, h2, h3⟩, fun h => absurd h (by simp)⟩
  case c15 =>
    intro s next depth hd fuel idx tmp hne saved hs hg hf hpre
    have hne' : (s.minimizedIndex m (IDX next) 1 != 0) = true := hne
    rw [minimizeBinaryChain]
    simp only
    rw [if_pos hne']
    refine ⟨MF.refl _, hg, ⟨[], by simp⟩, fun v hv => by
      obtain ⟨y, h1, h2, h3, _⟩ := hpre.2 v hv; exact ⟨y, h1, h2, h3⟩, fun hpos => ?_⟩
    have hpos' : s.minimizedIndex m (IDX next) 1 > 0 := by simpa using hpos
    have hn := minimizedIndex_ne_zero_pos hs m next hpos'
    refine ⟨⟨hpre.1, fun v hv => ?_⟩, hn.imp_right Or.inl⟩
    obtain ⟨y, h1, h2, h3, A, hA, hA'⟩ := hpre.2 v hv
    refine ⟨y, h1, h2, h3, A, hA, fun x hx => ?_⟩
    rcases hA' x hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · have hxf : s0.IsFalse x := (hb.ante_of_antecedents hA hx).1
      have := hb.false_same_var hf hxf h
      subst this
      rcases hn with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  case c16 =>
    intro s next depth hd fuel idx tmp hz s1 hnb ih2 saved hs hg hf hpre
    have hz' : ¬ (s.minimizedIndex m (IDX next) 1 != 0) = true := hz
    have hz0 : ¬ s.minimizedIndex m (IDX next) 1 > 0 ∧ ¬ s.minimizedIndex m (IDX next) 1 < 0 := by
      constructor <;> intro h <;> apply hz' <;> simp <;> omega
    obtain ⟨z1, z2, _⟩ := minimizedIndex_zero hs m next 1 hz0.1 hz0.2
    have hs1m : MF s1 s := MF.setMinimize _ _
    have hs1 : AF s1 s0 := hs1m.af.trans hs
    have hv1 : s1.minimize.view = s.minimize.view ++ [IDX next] := by
      show (s.minimize.push (IDX next)).view = _; rw [U32Vec.view_push]
    have hnt : s0.IsTrue (NOT next) := by
      have := (hb.inv.core.valCons (NOT next)).1; rw [NOT_NOT] at this; exact this.mpr hf
    have hra := hb.inv.reasons (NOT next) hnt (by rw [hb.inv.core.lvlVar]; omega)
    have eR : s1.reasonIdx idx = s0.reasonOf (NOT next) := by
      rw [reasonOf_NOT]; show s1.reasonOf next = _; rw [hs1.reasonOf]
    have hnb' : s0.binOf (NOT next) = false := by
      rw [binOf_NOT, ← hs1.binOf]
      have : s1.isBinaryReason idx = false := by simpa using hnb
      exact this
    have hndec : s0.reasonOf (NOT next) ≠ DECISION_REASON := by rw [reasonOf_NOT]; exact z2
    rcases hra with e | ⟨b1, _⟩ | ⟨b1, b2, b3, b4⟩
    · exact absurd e hndec
    · rw [b1] at hnb'; exact absurd hnb' (by simp)
    have hr : s1.reasonIdx idx ∈ s0.arena.chain 0 s0.arena.sizeWards := by rw [eR]; exact b2.1
    obtain ⟨r1, r2, r3, r4⟩ := ih2 hs1 (hg.mono_mf (fun j => Iff.rfl)) hr (fun k hk hne => by
      rw [eR] at hk hne ⊢; exact (b4 _ (lit_mem_litsL _ _ _ hk) hne).1)
    have e : s.minimizeBinaryChain m maxD next depth hd (fuel + 1) =
        s1.minimizeReference m maxD (s1.reasonIdx idx) next (depth + 1) (by omega) := by
      rw [minimizeBinaryChain]
      simp only [s1, idx, tmp] at hz hnb ⊢
      rw [if_neg hz', if_pos hnb]
    rw [e]
    generalize s1.minimizeReference m maxD (s1.reasonIdx idx) next (depth + 1) _ = R at r1 r2 r3 r4 ⊢
    rw [eR] at r4
    have hdrop : (s.minimize.view ++ [IDX next]).drop saved = s.minimize.view.drop saved ++ [IDX next] :=
      List.drop_append_of_le_length (by simpa using hpre.1)
    refine ⟨r1.trans hs1m, r2, ⟨[IDX next], by rw [r3, hv1]⟩, fun v hv => ?_, fun hres => ?_⟩
    · rw [r3, hv1, hdrop] at hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨y, h1, h2, h3, _⟩ := hpre.2 v hv; exact ⟨y, h1, h2, h3⟩
      · simp at hv; subst hv; exact ⟨next, rfl, hf, by omega⟩
    have hmem : IDX next ∈ R.2.minimize.view.drop saved := by
      rw [r3, hv1, hdrop]; simp
    refine ⟨⟨by have := hpre.1; rw [← U32Vec.length_view, r3, hv1]; simp; omega, fun v hv => ?_⟩,
      Or.inr (Or.inr hmem)⟩
    rw [r3, hv1, hdrop] at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨y, h1, h2, h3, A, hA, hA'⟩ := hpre.2 v hv
      refine ⟨y, h1, h2, h3, A, hA, fun x hx => ?_⟩
      rcases hA' x hx with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (r1.rem _ h))
      · exact Or.inr (Or.inr (by rw [r3, hv1, hdrop]; exact List.mem_append_left _ h))
      · exact Or.inr (Or.inr (by rw [h]; exact hmem))
    · simp at hv; subst hv
      refine ⟨next, rfl, hf, by omega, (s0.clauseL (s0.reasonOf (NOT next))).filter (fun x => x != NOT next),
        ⟨hnt, by rw [hb.inv.core.lvlVar]; omega, Or.inr ⟨b1, hndec, b2, b3, fun x => by simp [List.mem_filter]⟩⟩,
        fun x hx => ?_⟩
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      obtain ⟨k, hk, rfl⟩ := mem_litsL_iff.mp hx1
      have := r4 hres k hk (by simpa using hx2)
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  case c17 =>
    intro s next depth hd fuel idx tmp hz s1 hnb ih5 saved hs hg hf hpre
    have hz' : ¬ (s.minimizedIndex m (IDX next) 1 != 0) = true := hz
    have hz0 : ¬ s.minimizedIndex m (IDX next) 1 > 0 ∧ ¬ s.minimizedIndex m (IDX next) 1 < 0 := by
      constructor <;> intro h <;> apply hz' <;> simp <;> omega
    obtain ⟨z1, z2, _⟩ := minimizedIndex_zero hs m next 1 hz0.1 hz0.2
    have hs1m : MF s1 s := MF.setMinimize _ _
    have hs1 : AF s1 s0 := hs1m.af.trans hs
    have hv1 : s1.minimize.view = s.minimize.view ++ [IDX next] := by
      show (s.minimize.push (IDX next)).view = _; rw [U32Vec.view_push]
    have hnt : s0.IsTrue (NOT next) := by
      have := (hb.inv.core.valCons (NOT next)).1; rw [NOT_NOT] at this; exact this.mpr hf
    have hra := hb.inv.reasons (NOT next) hnt (by rw [hb.inv.core.lvlVar]; omega)
    have eR : s1.reasonIdx idx = s0.reasonOf (NOT next) := by
      rw [reasonOf_NOT]; show s1.reasonOf next = _; rw [hs1.reasonOf]
    have hbb : s0.binOf (NOT next) = true := by
      rw [binOf_NOT, ← hs1.binOf]
      have : s1.isBinaryReason idx = true := by simpa using hnb
      exact this
    have hndec : s0.reasonOf (NOT next) ≠ DECISION_REASON := by rw [reasonOf_NOT]; exact z2
    have hbin : s0.binOf (NOT next) = true ∧ s0.BinWatched (NOT next) (s0.reasonOf (NOT next)) ∧
        s0.Ante (NOT next) (s0.reasonOf (NOT next)) := by
      rcases hra with e | h | ⟨b1, _⟩
      · exact absurd e hndec
      · exact h
      · rw [b1] at hbb; exact absurd hbb (by simp)
    obtain ⟨b1, b2, b3⟩ := hbin
    have hdrop : (s.minimize.view ++ [IDX next]).drop saved = s.minimize.view.drop saved ++ [IDX next] :=
      List.drop_append_of_le_length (by simpa using hpre.1)
    have hpre1 : ChainPre s0 s1 saved (s1.reasonIdx idx) := by
      refine ⟨by have := hpre.1; rw [← U32Vec.length_view, hv1]; simp; omega, fun v hv => ?_⟩
      rw [hv1, hdrop] at hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨y, h1, h2, h3, A, hA, hA'⟩ := hpre.2 v hv
        refine ⟨y, h1, h2, h3, A, hA, fun x hx => ?_⟩
        rcases hA' x hx with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl (by rw [hv1, hdrop]; exact List.mem_append_left _ h)))
        · exact Or.inr (Or.inr (Or.inl (by rw [hv1, hdrop, h]; simp)))
      · simp at hv; subst hv
        refine ⟨next, rfl, hf, by omega, [s0.reasonOf (NOT next)],
          ⟨hnt, by rw [hb.inv.core.lvlVar]; omega, Or.inl ⟨b1, b2, rfl⟩⟩, fun x hx => ?_⟩
        simp at hx; subst hx
        exact Or.inr (Or.inr (Or.inr (by rw [eR])))
    obtain ⟨r1, r2, ⟨T, r3⟩, r5, r4⟩ := ih5 saved hs1 (hg.mono_mf (fun j => Iff.rfl))
      (by rw [eR]; exact b3.1) hpre1
    have e : s.minimizeBinaryChain m maxD next depth hd (fuel + 1) =
        s1.minimizeBinaryChain m maxD (s1.reasonIdx idx) depth hd fuel := by
      rw [minimizeBinaryChain]
      simp only [s1, idx, tmp] at hz hnb ⊢
      rw [if_neg hz', if_neg hnb]
    rw [e]
    generalize s1.minimizeBinaryChain m maxD (s1.reasonIdx idx) depth hd fuel = R at r1 r2 r3 r4 r5 ⊢
    refine ⟨r1.trans hs1m, r2, ⟨IDX next :: T, by rw [r3, hv1]; simp⟩, r5, fun hres => ?_⟩
    obtain ⟨c1, _⟩ := r4 hres
    refine ⟨c1, Or.inr (Or.inr ?_)⟩
    rw [r3, hv1, List.append_assoc, List.drop_append_of_le_length (by simpa using hpre.1)]
    simp

end Solver
end LeanKissat
