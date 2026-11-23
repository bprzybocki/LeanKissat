import LeanKissat.Proofs.RedArena

/-!
# `kissat_sort_literals`: a permutation that moves a non-false literal to the front
-/

namespace LeanKissat
open Solver

/-- The segment `[off, off + n)` of a vector. -/
def seg (v : U32Vec) (off n : Nat) : List UInt32 := (List.range n).map (fun k => v.get! (off + k))

theorem seg_length (v : U32Vec) (off n : Nat) : (seg v off n).length = n := by simp [seg]

theorem seg_getElem (v : U32Vec) (off n k : Nat) (h : k < (seg v off n).length) :
    (seg v off n)[k] = v.get! (off + k) := by simp [seg]

theorem seg_swap (v : U32Vec) (off n i j : Nat) (hi : i < n) (hj : j < n) (hs : off + n ≤ v.size) :
    (seg ((v.set! (off + i) (v.get! (off + j))).set! (off + j) (v.get! (off + i))) off n).Perm (seg v off n) := by
  have hi' : i < (seg v off n).length := by rw [seg_length]; exact hi
  have hj' : j < (seg v off n).length := by rw [seg_length]; exact hj
  have e : seg ((v.set! (off + i) (v.get! (off + j))).set! (off + j) (v.get! (off + i))) off n =
      ((seg v off n).set i (seg v off n)[j]).set j (seg v off n)[i] := by
    apply List.ext_getElem
    · simp [seg_length]
    · intro k h1 h2
      have hk : k < n := by simpa [seg_length] using h1
      simp only [List.getElem_set, seg, List.getElem_map, List.getElem_range]
      rw [U32Vec.get!_set!, U32Vec.get!_set!]
      simp only [U32Vec.size_set!]
      by_cases ekj : j = k
      · subst ekj; simp [show off + j < v.size by omega]
      · by_cases eki : i = k
        · subst eki
          have : off + j ≠ off + i := by omega
          simp [ekj, show off + i < v.size by omega]
        · have h1 : off + j ≠ off + k := by omega
          have h2 : off + i ≠ off + k := by omega
          simp [ekj, eki]
  rw [e]; exact List.set_set_perm hi' hj'

theorem vNeg_vPos : ∀ (v : UInt8), v ≠ 0 → vNeg v = false → vPos v = true := by decide

theorem vPos_vNeg : ∀ (v : UInt8), vPos v = true → vNeg v = false := by decide

/-- The scan loop of `move_smallest_literal_to_front`. -/
theorem moveSmallestLoop_spec (values : ByteArray) (level : UInt32 → UInt32) (sat : Bool) (lits : U32Vec)
    (off size start : Nat) :
    ∀ (pos : Nat) (best : Lit) (u : Value) (k : UInt32) (i : Nat),
    start + 1 ≤ i → (pos = 0 → best = lits.get! (off + start)) →
    (pos ≠ 0 → start < pos ∧ pos < size ∧ best = lits.get! (off + pos)) →
    u = values.get! best.toNat → u ≠ 0 →
    (sat = false → vNeg u = true → ∀ k, start ≤ k → k < i → vNeg (values.get! (lits.get! (off + k)).toNat) = true) →
    let r := moveSmallestLoop values level sat lits off size pos best u k i
    (r.1 = 0 → r.2.1 = lits.get! (off + start)) ∧
    (r.1 ≠ 0 → start < r.1 ∧ r.1 < size ∧ r.2.1 = lits.get! (off + r.1)) ∧
    r.2.2 = values.get! r.2.1.toNat ∧
    (sat = false → vNeg r.2.2 = true →
      ∀ k, start ≤ k → k < size → vNeg (values.get! (lits.get! (off + k)).toNat) = true) := by
  intro pos best u k i
  induction pos, best, u, k, i using moveSmallestLoop.induct values level sat lits off size with
  | case1 pos best u k i hi b v hv =>
    intro h1 h2 h3 h4 h5 h6
    rw [moveSmallestLoop, ite_eq_left hi]; dsimp only; rw [ite_eq_left hv]
    refine ⟨fun e => by omega, fun _ => ⟨by omega, hi, by first | rfl | trivial⟩, by first | rfl | trivial,
      fun hs hn => ?_⟩
    exfalso
    simp only [hs, Bool.and_false, Bool.or_false, beq_iff_eq] at hv
    simp only [v] at hv; rw [hv] at hn; simp [vNeg] at hn
  | case2 pos best u k i hi b v hv l better hb ih =>
    intro h1 h2 h3 h4 h5 h6
    rw [moveSmallestLoop, ite_eq_left hi]; dsimp only; rw [ite_eq_right hv]
    simp only [l, better, b, v, dite_eq_ite] at hb ih ⊢
    rw [ite_eq_left hb]
    have hv0 : values.get! (lits.get! (off + i)).toNat ≠ 0 := by
      intro e; apply hv; simp [v, b, e]
    apply ih (by omega) (fun e => by omega) (fun _ => ⟨by omega, hi, by first | rfl | trivial⟩)
      (by first | rfl | trivial) hv0
    intro hs hn k' hk1 hk2
    by_cases e : k' = i
    · subst e; exact hn
    · apply h6 hs _ k' hk1 (by omega)
      -- the previous best was false as well
      by_cases hu : vNeg u = true
      · exact hu
      · exfalso
        have hpu : vPos u = true := vNeg_vPos u h5 (by simpa using hu)
        have hnv : vNeg (values.get! (lits.get! (off + i)).toNat) = true := hn
        have : (vPos u && vNeg (values.get! (lits.get! (off + i)).toNat)) = true := by simp [hpu, hnv]
        rw [ite_eq_right (by simp [hu]), ite_eq_left this] at hb
        exact absurd hb (by simp)
  | case3 pos best u k i hi b v hv l better hb ih =>
    intro h1 h2 h3 h4 h5 h6
    rw [moveSmallestLoop, ite_eq_left hi]; dsimp only; rw [ite_eq_right hv]
    simp only [l, better, b, v, dite_eq_ite] at hb ih ⊢
    rw [ite_eq_right hb]
    apply ih (by omega) h2 h3 h4 h5
    intro hs hn k' hk1 hk2
    by_cases e : k' = i
    · subst e
      have hv0 : values.get! (lits.get! (off + k')).toNat ≠ 0 := by
        intro e; apply hv; simp [v, b, e]
      by_cases hneg : vNeg (values.get! (lits.get! (off + k')).toNat) = true
      · exact hneg
      · exfalso
        have hpv : vPos (values.get! (lits.get! (off + k')).toNat) = true := vNeg_vPos _ hv0 (by simpa using hneg)
        rw [ite_eq_left (by simp [hn, hpv])] at hb
        exact hb rfl
    · exact h6 hs hn k' hk1 (by omega)
  | case4 pos best u k i hi =>
    intro h1 h2 h3 h4 h5 h6
    rw [moveSmallestLoop, ite_eq_right hi]
    exact ⟨h2, h3, h4, fun hs hn k' hk1 hk2 => h6 hs hn k' hk1 (by omega)⟩

theorem moveSmallest_spec (values : ByteArray) (level : UInt32 → UInt32) (sat : Bool) (lits : U32Vec)
    (off start size : Nat) (hst : start < size) (hsz : off + size ≤ lits.size) :
    (moveSmallestLiteralToFront values level sat lits off start size).2.size = lits.size ∧
    (∀ j, j < off + start → (moveSmallestLiteralToFront values level sat lits off start size).2.get! j = lits.get! j) ∧
    (∀ j, off + size ≤ j → (moveSmallestLiteralToFront values level sat lits off start size).2.get! j = lits.get! j) ∧
    (seg (moveSmallestLiteralToFront values level sat lits off start size).2 off size).Perm (seg lits off size) ∧
    (sat = false → (∃ k, start ≤ k ∧ k < size ∧ vNeg (values.get! (lits.get! (off + k)).toNat) = false) →
      vNeg (values.get! ((moveSmallestLiteralToFront values level sat lits off start size).2.get! (off + start)).toNat)
        = false) := by
  unfold moveSmallestLiteralToFront
  dsimp only
  by_cases h0 : ((values.get! (lits.get! (off + start)).toNat == 0) ||
      (vPos (values.get! (lits.get! (off + start)).toNat) && sat)) = true
  · rw [ite_eq_left h0]
    refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, List.Perm.refl _, fun hs _ => ?_⟩
    simp only [hs, Bool.and_false, Bool.or_false, beq_iff_eq] at h0
    rw [h0]; rfl
  · rw [ite_eq_right h0]
    have hu0 : values.get! (lits.get! (off + start)).toNat ≠ 0 := by
      intro e; apply h0; simp [e]
    have L := moveSmallestLoop_spec values level sat lits off size start 0 (lits.get! (off + start))
      (values.get! (lits.get! (off + start)).toNat)
      (if values.get! (lits.get! (off + start)).toNat != 0 then level (IDX (lits.get! (off + start)))
        else UInt32.ofNat 4294967295) (start + 1) (Nat.le_refl _) (fun _ => rfl) (fun h => absurd rfl h) rfl hu0
      (fun _ hn k h1 h2 => by rw [show k = start by omega]; exact hn)
    generalize moveSmallestLoop values level sat lits off size 0 (lits.get! (off + start))
      (values.get! (lits.get! (off + start)).toNat)
      (if values.get! (lits.get! (off + start)).toNat != 0 then level (IDX (lits.get! (off + start)))
        else UInt32.ofNat 4294967295) (start + 1) = r at L ⊢
    obtain ⟨pos, best, u⟩ := r
    obtain ⟨l1, l2, l3, l4⟩ := L
    dsimp only at l1 l2 l3 l4 ⊢
    by_cases hp : pos = 0
    · rw [ite_eq_left (by simp [hp])]
      refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, List.Perm.refl _, fun hs ⟨k, hk1, hk2, hk3⟩ => ?_⟩
      apply Classical.byContradiction; intro hn
      have hneg : vNeg u = true := by rw [l3, l1 hp]; simpa using hn
      rw [l4 hs hneg k hk1 hk2] at hk3; exact absurd hk3 (by simp)
    · rw [ite_eq_right (by simp [hp])]
      obtain ⟨p1, p2, p3⟩ := l2 hp
      rw [p3]
      have hne : off + start ≠ off + pos := by omega
      refine ⟨by simp, fun j hj => ?_, fun j hj => ?_, seg_swap lits off size start pos hst p2 hsz,
        fun hs ⟨k, hk1, hk2, hk3⟩ => ?_⟩
      · rw [U32Vec.get!_set!_ne _ _ _ _ (by omega), U32Vec.get!_set!_ne _ _ _ _ (by omega)]
      · rw [U32Vec.get!_set!_ne _ _ _ _ (by omega), U32Vec.get!_set!_ne _ _ _ _ (by omega)]
      · rw [U32Vec.get!_set!_ne _ _ _ _ (Ne.symm hne), U32Vec.get!_set!_self _ _ _ (by omega)]
        apply Classical.byContradiction; intro hn
        have hneg : vNeg u = true := by rw [l3, p3]; simpa using hn
        rw [l4 hs hneg k hk1 hk2] at hk3; exact absurd hk3 (by simp)

theorem sortLiterals_spec (values : ByteArray) (level : UInt32 → UInt32) (lits : U32Vec) (off size : Nat)
    (h2 : 2 ≤ size) (hsz : off + size ≤ lits.size) :
    (sortLiterals values level lits off size).size = lits.size ∧
    (∀ j, (j < off ∨ off + size ≤ j) → (sortLiterals values level lits off size).get! j = lits.get! j) ∧
    (seg (sortLiterals values level lits off size) off size).Perm (seg lits off size) ∧
    ((∃ k, k < size ∧ vNeg (values.get! (lits.get! (off + k)).toNat) = false) →
      vNeg (values.get! ((sortLiterals values level lits off size).get! off).toNat) = false) := by
  unfold sortLiterals
  obtain ⟨a1, a2, a3, a4, a5⟩ := moveSmallest_spec values level false lits off 0 size (by omega) hsz
  generalize moveSmallestLiteralToFront values level false lits off 0 size = R at a1 a2 a3 a4 a5 ⊢
  obtain ⟨u, l1⟩ := R
  dsimp only at a1 a2 a3 a4 a5 ⊢
  have a5' : (∃ k, k < size ∧ vNeg (values.get! (lits.get! (off + k)).toNat) = false) →
      vNeg (values.get! (l1.get! off).toNat) = false := by
    intro ⟨k, hk1, hk2⟩; have := a5 rfl ⟨k, Nat.zero_le _, hk1, hk2⟩; simpa using this
  split
  · obtain ⟨b1, b2, b3, b4, _⟩ := moveSmallest_spec values level (!vNeg u) l1 off 1 size (by omega) (by omega)
    refine ⟨by rw [b1, a1], fun j hj => ?_, b4.trans a4, fun h => ?_⟩
    · rcases hj with hj | hj
      · rw [b2 j (by omega), a2 j (by omega)]
      · rw [b3 j hj, a3 j hj]
    · rw [b2 off (by omega)]; exact a5' h
  · refine ⟨a1, fun j hj => ?_, a4, a5'⟩
    rcases hj with hj | hj
    · exact a2 j (by omega)
    · exact a3 j hj

end LeanKissat
