import LeanKissat.Proofs.RedArena

/-!
# `reduce`: the literal loop of the sparse sweep
-/

namespace LeanKissat
namespace Solver
open Arena

/-- Accumulators of the literal loop for the kept literals `K`. -/
def LitAcc (s : Solver) (K : List Lit) (L : SweepLits) : Prop :=
  (∀ y ∈ K, y ≠ INVALID_LIT) ∧
  L.mfirst = K.getD 0 INVALID_LIT ∧ L.msecond = K.getD 1 INVALID_LIT ∧
  (L.forced ≠ INVALID_LIT → L.forced ∈ K ∧ vTrue (s.value L.forced) = true) ∧
  (L.other ≠ INVALID_LIT → L.other ∈ K ∧ vFalse (s.value L.other) = true)

theorem LitAcc.init (s : Solver) (L : SweepLits) (h1 : L.mfirst = INVALID_LIT) (h2 : L.msecond = INVALID_LIT)
    (h3 : L.forced = INVALID_LIT) (h4 : L.other = INVALID_LIT) : LitAcc s [] L :=
  ⟨by simp, by simp [h1], by simp [h2], fun h => absurd h3 h, fun h => absurd h4 h⟩

theorem LitAcc.step' {s : Solver} {K : List Lit} {L : SweepLits} (h : LitAcc s K L) (x : Lit) (hx : x ≠ INVALID_LIT) :
    let L1 := if vTrue (s.value x) then
          { L with forced := if L.nonFalse == 0 then x else INVALID_LIT, nonFalse := L.nonFalse + 1 }
        else if vFalse (s.value x) then { L with other := x } else L
    let L2 := if L1.mfirst == INVALID_LIT then { L1 with mfirst := x }
        else if L1.msecond == INVALID_LIT then { L1 with msecond := x } else L1
    ∀ (w : U32Vec) (q : Nat), LitAcc s (K ++ [x]) { L2 with words := w, qpos := q } := by
  intro L1 L2 w q
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hmem : ∀ y ∈ K, y ∈ K ++ [x] := fun y hy => List.mem_append_left _ hy
  have hxm : x ∈ K ++ [x] := by simp
  have hf1 : (L1.forced ≠ INVALID_LIT → L1.forced ∈ K ++ [x] ∧ vTrue (s.value L1.forced) = true) ∧
      (L1.other ≠ INVALID_LIT → L1.other ∈ K ++ [x] ∧ vFalse (s.value L1.other) = true) ∧
      L1.mfirst = L.mfirst ∧ L1.msecond = L.msecond := by
    simp only [L1]
    split
    · rename_i ht
      refine ⟨fun hne => ?_, fun hne => ⟨hmem _ (h4 hne).1, (h4 hne).2⟩, rfl, rfl⟩
      dsimp only at hne ⊢
      split
      · exact ⟨hxm, ht⟩
      · rename_i hn; simp only [hn, Bool.false_eq_true, ite_false, ne_eq, not_true_eq_false] at hne
    · split
      · rename_i _ hf
        exact ⟨fun hne => ⟨hmem _ (h3 hne).1, (h3 hne).2⟩, fun _ => ⟨hxm, hf⟩, rfl, rfl⟩
      · exact ⟨fun hne => ⟨hmem _ (h3 hne).1, (h3 hne).2⟩, fun hne => ⟨hmem _ (h4 hne).1, (h4 hne).2⟩, rfl, rfl⟩
  obtain ⟨g3, g4, g1, g2⟩ := hf1
  have h0' : ∀ y ∈ K ++ [x], y ≠ INVALID_LIT := by
    intro y hy; rcases List.mem_append.mp hy with hy | hy
    · exact h0 y hy
    · simp at hy; subst hy; exact hx
  have hK : K.length = 0 ∨ K.length = 1 ∨ 2 ≤ K.length := by omega
  rcases hK with hK | hK | hK
  · have e : K = [] := List.eq_nil_of_length_eq_zero hK
    subst e
    have hm : L1.mfirst = INVALID_LIT := by rw [g1, h1]; rfl
    have : L2 = { L1 with mfirst := x } := by simp only [L2, hm, beq_self_eq_true, ite_true]
    rw [this]
    exact ⟨h0', by simp, by simp [g2, h2], g3, g4⟩
  · obtain ⟨a, rfl⟩ : ∃ a, K = [a] := by
      match K, hK with
      | [a], _ => exact ⟨a, rfl⟩
    have ha : a ≠ INVALID_LIT := h0 a (by simp)
    have hm : (L1.mfirst == INVALID_LIT) = false := by rw [g1, h1]; simpa using ha
    have hm2 : L1.msecond = INVALID_LIT := by rw [g2, h2]; rfl
    have : L2 = { L1 with msecond := x } := by simp only [L2, hm, hm2, beq_self_eq_true, ite_true]; rfl
    rw [this]
    exact ⟨h0', by simp [g1, h1], by simp, g3, g4⟩
  · have e0 : K.getD 0 INVALID_LIT ≠ INVALID_LIT := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact h0 _ (List.getElem_mem _)
    have e1 : K.getD 1 INVALID_LIT ≠ INVALID_LIT := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact h0 _ (List.getElem_mem _)
    have hm : (L1.mfirst == INVALID_LIT) = false := by rw [g1, h1]; simpa using e0
    have hm2 : (L1.msecond == INVALID_LIT) = false := by rw [g2, h2]; simpa using e1
    have : L2 = L1 := by simp only [L2, hm, hm2]; rfl
    rw [this]
    have d0 : (K ++ [x]).getD 0 INVALID_LIT = K.getD 0 INVALID_LIT := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    have d1 : (K ++ [x]).getD 1 INVALID_LIT = K.getD 1 INVALID_LIT := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    exact ⟨h0', by rw [d0, g1, h1], by rw [d1, g2, h2], g3, g4⟩

theorem keep_words (L : SweepLits) (tmp : Value) (x : Lit) :
    (L.keep tmp x).words = L.words.set! L.qpos x ∧ (L.keep tmp x).qpos = L.qpos + 1 := by
  unfold SweepLits.keep
  dsimp only
  constructor <;> (repeat' split) <;> rfl

theorem LitAcc.step {s : Solver} {K : List Lit} {L : SweepLits} (h : LitAcc s K L) (x : Lit) (hx : x ≠ INVALID_LIT) :
    LitAcc s (K ++ [x]) (L.keep (s.value x) x) := by
  have := h.step' x hx
  simp only at this
  exact this _ _

theorem rootT_of_rootF {s : Solver} {x : Lit} (h : s.rootF x = true) : s.rootT x = false := by
  unfold rootF at h; unfold rootT
  simp only [Bool.and_eq_true, beq_iff_eq, vFalse] at h
  simp [vTrue, h.1]

theorem range'_succ_eq (i m : Nat) (h : i < m) : List.range' i (m - i) = i :: List.range' (i + 1) (m - (i + 1)) := by
  rw [show m - i = (m - (i + 1)) + 1 by omega, List.range'_succ]

/-- The literal loop copies the literals that are not false at the root level. -/
theorem sweepLits_spec (s : Solver) (srcBase n : Nat) (f : Nat → Lit) (hf : ∀ k < n, f k ≠ INVALID_LIT) :
    ∀ (L : SweepLits) (i : Nat) (K : List Lit),
    (∀ k, i ≤ k → k < n → L.words.get! (srcBase + k) = f k) → L.qpos ≤ srcBase + i → i ≤ n →
    srcBase + n ≤ L.words.size → LitAcc s K L →
    (sweepLits s srcBase n L i).2.words.size = L.words.size ∧
    L.qpos ≤ (sweepLits s srcBase n L i).2.qpos ∧ (sweepLits s srcBase n L i).2.qpos ≤ srcBase + n ∧
    (∀ j, (j < L.qpos ∨ (sweepLits s srcBase n L i).2.qpos ≤ j) →
      (sweepLits s srcBase n L i).2.words.get! j = L.words.get! j) ∧
    ((sweepLits s srcBase n L i).1 = false → ∃ x ∈ (List.range' i (n - i)).map f, s.rootT x = true) ∧
    ((sweepLits s srcBase n L i).1 = true → (∀ x ∈ (List.range' i (n - i)).map f, s.rootT x = false) ∧
      (sweepLits s srcBase n L i).2.qpos =
        L.qpos + (((List.range' i (n - i)).map f).filter (fun x => !s.rootF x)).length ∧
      (∀ k, k < (((List.range' i (n - i)).map f).filter (fun x => !s.rootF x)).length →
        (sweepLits s srcBase n L i).2.words.get! (L.qpos + k) =
          (((List.range' i (n - i)).map f).filter (fun x => !s.rootF x)).getD k 0) ∧
      LitAcc s (K ++ ((List.range' i (n - i)).map f).filter (fun x => !s.rootF x)) (sweepLits s srcBase n L i).2) := by
  intro L i
  induction L, i using sweepLits.induct s srcBase n with
  | case1 L i hi lit hrf ih =>
    intro K hw hq hin hsz hacc
    have hli : L.words.get! (srcBase + i) = f i := hw i (Nat.le_refl _) hi
    have hrf' : s.rootF (f i) = true := by rw [← hli]; exact hrf
    rw [sweepLits, ite_eq_left hi]; dsimp only; rw [hli, ite_eq_left hrf']
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih K (fun k h1 h2 => hw k (by omega) h2) (by omega) (by omega) hsz hacc
    rw [range'_succ_eq i n hi, List.map_cons, List.filter_cons, ite_eq_right (by simp [hrf'])]
    refine ⟨a1, a2, a3, a4, fun e => ?_, fun e => ?_⟩
    · obtain ⟨x, hx, hxt⟩ := a5 e; exact ⟨x, List.mem_cons_of_mem _ hx, hxt⟩
    · obtain ⟨b1, b2, b3, b4⟩ := a6 e
      refine ⟨fun x hx => ?_, b2, b3, b4⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact rootT_of_rootF hrf'
      · exact b1 x hx
  | case2 L i hi lit hrf hrt =>
    intro K hw hq hin hsz hacc
    have hli : L.words.get! (srcBase + i) = f i := hw i (Nat.le_refl _) hi
    have hrf' : ¬ s.rootF (f i) = true := by rw [← hli]; exact hrf
    have hrt' : s.rootT (f i) = true := by rw [← hli]; exact hrt
    rw [sweepLits, ite_eq_left hi]; dsimp only; rw [hli, ite_eq_right hrf', ite_eq_left hrt']
    refine ⟨rfl, Nat.le_refl _, show L.qpos ≤ srcBase + n by omega, fun _ _ => rfl, fun _ => ?_,
      fun e => by simp at e⟩
    exact ⟨f i, by rw [range'_succ_eq i n hi]; simp, hrt'⟩
  | case3 L i hi lit tmp hrf hrt ih =>
    intro K hw hq hin hsz hacc
    have hli : L.words.get! (srcBase + i) = f i := hw i (Nat.le_refl _) hi
    have hrf' : ¬ s.rootF (f i) = true := by rw [← hli]; exact hrf
    have hrt' : ¬ s.rootT (f i) = true := by rw [← hli]; exact hrt
    rw [sweepLits, ite_eq_left hi]; dsimp only; rw [hli, ite_eq_right hrf', ite_eq_right hrt']
    simp only [tmp, lit, hli] at ih
    obtain ⟨kw, kq⟩ := keep_words L (s.value (f i)) (f i)
    have hacc' := hacc.step (f i) (hf i hi)
    have p1 : ∀ k, i + 1 ≤ k → k < n → (L.keep (s.value (f i)) (f i)).words.get! (srcBase + k) = f k := by
      intro k h1 h2
      rw [kw]
      have hne : L.qpos ≠ srcBase + k := by omega
      rw [U32Vec.get!_set!_ne _ _ _ _ hne]; exact hw k (by omega) h2
    have p2 : (L.keep (s.value (f i)) (f i)).qpos ≤ srcBase + (i + 1) := by rw [kq]; omega
    have p3 : srcBase + n ≤ (L.keep (s.value (f i)) (f i)).words.size := by rw [kw, U32Vec.size_set!]; exact hsz
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (K ++ [f i]) p1 p2 (by omega) p3 hacc'
    rw [kw] at a1; rw [kq] at a2; rw [kw, kq] at a4; rw [kq] at a6
    rw [range'_succ_eq i n hi, List.map_cons, List.filter_cons, ite_eq_left (by simpa using hrf')]
    have hqs : L.qpos < L.words.size := by omega
    refine ⟨by rw [a1]; simp, by omega, a3, fun j hj => ?_, fun e => ?_, fun e => ?_⟩
    · rw [a4 j (by omega), U32Vec.get!_set!_ne _ _ _ _ (by omega)]
    · obtain ⟨x, hx, hxt⟩ := a5 e; exact ⟨x, List.mem_cons_of_mem _ hx, hxt⟩
    · obtain ⟨b1, b2, b3, b4⟩ := a6 e
      refine ⟨fun x hx => ?_, by rw [b2]; simp; omega, fun k hk => ?_, by simpa using b4⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · simpa using hrt'
        · exact b1 x hx
      · rcases Nat.eq_zero_or_pos k with rfl | hk0
        · show _ = _
          have e1 := a4 L.qpos (Or.inl (by omega))
          rw [U32Vec.get!_set!_self _ _ _ hqs] at e1
          simp only [Nat.add_zero, e1]; simp
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          simp only [List.length_cons] at hk
          rw [show L.qpos + (k' + 1) = L.qpos + 1 + k' by omega, b3 k' (by omega)]
          simp
  | case4 L i hi =>
    intro K hw hq hin hsz hacc
    rw [sweepLits, ite_eq_right hi]
    have e : n - i = 0 := by omega
    rw [e]
    refine ⟨rfl, Nat.le_refl _, show L.qpos ≤ srcBase + n by omega, fun _ _ => rfl, fun h => by simp at h,
      fun _ => ⟨by simp, by simp, by simp, by simpa using hacc⟩⟩

end Solver
end LeanKissat
