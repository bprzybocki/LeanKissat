import LeanKissat.Util.U32Vec

/-
Port of Kissat's generic sorting macros (`sort.h`): `SORT`, `SORT_STACK`,
`QUICK_SORT`, `PARTITION`, `INSERTION_SORT`, `GREATER_SWAP`.

The algorithm is written once over an abstract swappable buffer (`SwapBuf`) and
instantiated for `Array α` and `U32Vec`. Every function sorts the half-open slice
`[lo, hi)` of the buffer (C: `SORT (TYPE, hi - lo, A + lo, LESS)`), which covers
both `SORT_STACK` (whole stack) and `SORT` on sub-ranges such as clause literals
stored inside the arena.

Faithfulness: the same comparisons are performed in the same order as C and the
resulting permutation (including the placement of equal elements) is identical,
provided `less` is a strict weak order (irreflexive) — which all Kissat comparators
are. Values of `less` on a pair not compared by C are never requested.

C's explicit `SORTER` stack is replaced by recursion (`quickSort` calls itself on the
smaller part first, then on the larger part); this is exactly the order in which the
C loop processes the parts (LIFO stack ⇒ depth-first, smaller part first), and the
parts are disjoint anyway, so the result is identical. Termination is by the size of
the range (`r - l`).

The only places where the Lean code adds guards that C does not have are the scans
that in C rely on sentinels (`A[R]` / the pivot stops the upward scan, the minimum
moved to the front stops the insertion scan). For irreflexive comparators the
sentinels stop the scans before the guards are reached, so the guards never change
behaviour.
-/
namespace LeanKissat
namespace Sorting

/-- Abstract mutable buffer supporting reads (with a default when out of bounds) and
  swaps; `toList` is the abstract content, used to state the permutation theorem. -/
class SwapBuf (β : Type) (α : outParam Type) where
  get : β → Nat → α
  swap : β → Nat → Nat → β
  toList : β → List α
  swap_perm : ∀ b i j, (toList (swap b i j)).Perm (toList b)

/-- Swap two elements of an array (no-op if out of bounds). -/
@[inline] def arraySwap {α : Type} (a : Array α) (i j : Nat) : Array α := a.swapIfInBounds i j

theorem arraySwap_perm {α : Type} (a : Array α) (i j : Nat) : (arraySwap a i j).toList.Perm a.toList := by
  unfold arraySwap
  rw [Array.swapIfInBounds_def]
  split
  · split
    · exact Array.perm_iff_toList_perm.mp (Array.swap_perm ..)
    · exact .refl _
  · exact .refl _

instance {α : Type} [Inhabited α] : SwapBuf (Array α) α where
  get a i := a[i]!
  swap := arraySwap
  toList a := a.toList
  swap_perm := arraySwap_perm

/-- Swap two elements of a `U32Vec` (no-op if out of bounds). -/
@[inline] def u32Swap (v : U32Vec) (i j : Nat) : U32Vec :=
  if hi : i < v.size then
    if hj : j < v.size then
      let x := v[i]
      let y := v[j]
      (v.set i y hi).set j x (by simpa using hj)
    else v
  else v

theorem U32Vec.toArray_spec (a : U32Vec) : a.toArray.size = a.size ∧
    ∀ i (h : i < a.size) (h' : i < a.toArray.size), a.toArray[i] = a[i] := by
  unfold U32Vec.toArray
  simp

@[simp] theorem U32Vec.getElem_toArray (a : U32Vec) (i : Nat) (h : i < a.toArray.size) :
    a.toArray[i] = a[i]'(by rw [(U32Vec.toArray_spec a).1] at h; exact h) :=
  (U32Vec.toArray_spec a).2 i _ h

theorem U32Vec.toArray_swap (v : U32Vec) (i j : Nat) (hi : i < v.size) (hj : j < v.size) :
    (u32Swap v i j).toArray =
      v.toArray.swap i j (by rw [(U32Vec.toArray_spec v).1]; exact hi)
        (by rw [(U32Vec.toArray_spec v).1]; exact hj) := by
  have hs := (U32Vec.toArray_spec v)
  have hs' := (U32Vec.toArray_spec (u32Swap v i j))
  have hsz : (u32Swap v i j).size = v.size := by simp [u32Swap, hi, hj]
  apply Array.ext
  · simp [hs.1, hs'.1, hsz]
  · intro k h1 h2
    have hk : k < v.size := by rw [hs'.1, hsz] at h1; exact h1
    rw [hs'.2 k (by rw [hsz]; exact hk) h1, Array.getElem_swap]
    have heq : u32Swap v i j = (v.set i v[j] hi).set j v[i] (by simpa using hj) := by
      simp [u32Swap, hi, hj]
    simp only [heq, U32Vec.getElem_set, U32Vec.getElem_toArray]
    by_cases e1 : k = i <;> by_cases e2 : k = j
    · subst e1; subst e2; simp
    · subst e1
      have e2' : ¬ j = k := fun h => e2 h.symm
      simp only [e2', ite_false, ite_true]; exact (U32Vec.getElem_set _ _ _ _ _ _).trans (ite_eq_left rfl)
    · subst e2; simp [e1]
    · have e1' : ¬ i = k := fun h => e1 h.symm
      have e2' : ¬ j = k := fun h => e2 h.symm
      simp only [e1, e2, e2', ite_false]; exact (U32Vec.getElem_set _ _ _ _ _ _).trans (ite_eq_right e1')

theorem u32Swap_perm (v : U32Vec) (i j : Nat) : (u32Swap v i j).toList.Perm v.toList := by
  by_cases hi : i < v.size
  · by_cases hj : j < v.size
    · simp only [U32Vec.toList]
      rw [U32Vec.toArray_swap v i j hi hj]
      exact Array.perm_iff_toList_perm.mp (Array.swap_perm ..)
    · simp [u32Swap, hi, hj]
  · simp [u32Swap, hi]

instance : SwapBuf U32Vec UInt32 where
  get v i := v.get! i
  swap := u32Swap
  toList v := v.toList
  swap_perm := u32Swap_perm

/-- `QUICK_SORT_LIMIT` (sort.h). -/
def QUICK_SORT_LIMIT : Nat := 10

variable {β α : Type} [SwapBuf β α]
open SwapBuf

/-- Port of `GREATER_SWAP` (sort.h): swap `A[p]` and `A[q]` if `LESS (A[q], A[p])`. -/
@[specialize] def greaterSwap (less : α → α → Bool) (b : β) (p q : Nat) : β :=
  if less (get b q) (get b p) then swap b p q else b

/-- Upward scan of `PARTITION` (sort.h): `while (LESS (A[++I], PIVOT));`, called with
  the already incremented `k`. Returns the first `k' ≥ k` with `!LESS (A[k'], PIVOT)`.
  The guard `k < bound` (with `bound = R` of `QUICK_SORT`, where `!LESS (A[R], PIVOT)`
  holds after median-of-three) is never reached for irreflexive comparators. -/
@[specialize] def scanUp (less : α → α → Bool) (b : β) (pivot : α) (bound k : Nat) :
    {k' : Nat // k ≤ k'} :=
  if h : k < bound then
    if less (get b k) pivot then
      let ⟨k', hk'⟩ := scanUp less b pivot bound (k + 1)
      ⟨k', by omega⟩
    else ⟨k, Nat.le_refl _⟩
  else ⟨k, Nat.le_refl _⟩
termination_by bound - k

/-- Downward scan of `PARTITION` (sort.h):
  `while (LESS (PIVOT, A[--J])) if (J == L) break;`, called with the already
  decremented `j`. -/
@[specialize] def scanDown (less : α → α → Bool) (b : β) (pivot : α) (lp : Nat) :
    (j : Nat) → {k : Nat // k ≤ j}
  | 0 => ⟨0, Nat.le_refl _⟩ -- `j = 0` implies `j = lp`: the scan stops here
  | j + 1 =>
    if less pivot (get b (j + 1)) then
      if j + 1 == lp then ⟨j + 1, Nat.le_refl _⟩
      else
        let ⟨k, hk⟩ := scanDown less b pivot lp j
        ⟨k, by omega⟩
    else ⟨j + 1, Nat.le_refl _⟩

/-- The `for (;;)` loop of `PARTITION` (sort.h). `i`, `j` are the values of
  `I_QUICK_SORT` and `J_PARTITION` before `++`/`--`. Returns the final buffer and
  `I_QUICK_SORT`. -/
@[specialize] def partitionLoop (less : α → α → Bool) (pivot : α) (lp bound : Nat) (b : β)
    (i j : Nat) : β × Nat :=
  let r1 := scanUp less b pivot bound (i + 1)
  let r2 := scanDown less b pivot lp (j - 1)
  if r1.1 ≥ r2.1 then (b, r1.1)
  else partitionLoop less pivot lp bound (swap b r1.1 r2.1) r1.1 r2.1
termination_by j - i
decreasing_by have := r1.2; have := r2.2; simp only [r1, r2] at *; omega

/-- One iteration of the `for (;;)` loop of `QUICK_SORT` (sort.h) on `[l, r]`
  (`r - l > QUICK_SORT_LIMIT`): median-of-three, `PARTITION (TYPE, L + 1, R - 1, A,
  LESS)` and the final pivot swap. Returns the buffer and `I_QUICK_SORT`. -/
@[specialize] def quickSortStep (less : α → α → Bool) (b : β) (l r : Nat) : β × Nat :=
  let m := l + (r - l) / 2
  let b := swap b m (r - 1)
  let b := greaterSwap less b l (r - 1)
  let b := greaterSwap less b l r
  let b := greaterSwap less b (r - 1) r
  let pivot := get b (r - 1)
  let p := partitionLoop less pivot (l + 1) r b l (r - 1)
  (swap p.1 p.2 (r - 1), p.2)

/-- Port of `QUICK_SORT` (sort.h) on the inclusive range `[l, r]`; ranges of at most
  `QUICK_SORT_LIMIT + 1` elements are left for insertion sort. -/
@[specialize] def quickSort (less : α → α → Bool) (b : β) (l r : Nat) : β :=
  if r - l ≤ QUICK_SORT_LIMIT then b
  else
    match quickSortStep less b l r with
    | (b, i) =>
      -- `L < I <= R` always holds (C asserts it); the test is needed for termination.
      if h : l < i ∧ i ≤ r then
        if i - l < r - i then
          let b := quickSort less b l (i - 1)
          quickSort less b (i + 1) r
        else
          let b := quickSort less b (i + 1) r
          quickSort less b l (i - 1)
      else b
termination_by r - l
decreasing_by all_goals omega

/-- First loop of `INSERTION_SORT` (sort.h): for `I = R` down to `L + 1`,
  `GREATER_SWAP (A[I - 1], A[I])` (moves a minimum to the front as sentinel). -/
@[specialize] def insertionSortBubble (less : α → α → Bool) (lo : Nat) (b : β) : Nat → β
  | i + 1 =>
    if lo < i + 1 then insertionSortBubble less lo (greaterSwap less b i (i + 1)) i
    else b
  | 0 => b

/-- Inner `while` loop of `INSERTION_SORT` (sort.h). The C code moves the pivot
  down by shifting; here the pivot is swapped down, which performs the same
  comparisons (`LESS (PIVOT, A[J - 1])`, the pivot being at `A[J]`) and yields the
  same array. The guard `lo < j` is never reached thanks to the sentinel. -/
@[specialize] def insertionSortSink (less : α → α → Bool) (lo : Nat) (b : β) : Nat → β
  | j + 1 =>
    if lo < j + 1 then
      if less (get b (j + 1)) (get b j) then insertionSortSink less lo (swap b j (j + 1)) j
      else b
    else b
  | 0 => b

/-- Second loop of `INSERTION_SORT` (sort.h): `for (I = L + 2; I <= R; I++)`. -/
@[specialize] def insertionSortLoop (less : α → α → Bool) (lo hi : Nat) (b : β) (i : Nat) : β :=
  if i < hi then insertionSortLoop less lo hi (insertionSortSink less lo b i) (i + 1)
  else b
termination_by hi - i

/-- Port of `INSERTION_SORT` (sort.h) on the slice `[lo, hi)` (`hi > lo`). -/
@[inline] def insertionSort (less : α → α → Bool) (b : β) (lo hi : Nat) : β :=
  let b := insertionSortBubble less lo b (hi - 1)
  insertionSortLoop less lo hi b (lo + 2)

/-- Port of `SORT (TYPE, hi - lo, A + lo, LESS)` (sort.h) on the slice `[lo, hi)`.
  `SORT_STACK` is `sortRange less b 0 size` (it skips sizes `≤ 1`, as does `SORT`
  in effect). -/
@[specialize] def sortRange (less : α → α → Bool) (b : β) (lo hi : Nat) : β :=
  if hi ≤ lo then b
  else
    let b := quickSort less b lo (hi - 1)
    insertionSort less b lo hi

/-! ### Entry points -/

/-- `SORT_STACK (TYPE, S, LESS)` for an `Array`. -/
@[inline] def sortArray [Inhabited α] (less : α → α → Bool) (a : Array α) : Array α :=
  if a.size ≤ 1 then a else sortRange less a 0 a.size

/-- `SORT (TYPE, hi - lo, A + lo, LESS)` for a slice of an `Array`. -/
@[inline] def sortArrayRange [Inhabited α] (less : α → α → Bool) (a : Array α) (lo hi : Nat) :
    Array α :=
  sortRange less a lo hi

/-- `SORT_STACK (unsigned, S, LESS)` for a `U32Vec`. -/
@[inline] def sortU32 (less : UInt32 → UInt32 → Bool) (v : U32Vec) : U32Vec :=
  if v.size ≤ 1 then v else sortRange less v 0 v.size

/-- `SORT (unsigned, hi - lo, A + lo, LESS)` for a slice of a `U32Vec` (e.g. clause
  literals inside the arena). -/
@[inline] def sortU32Range (less : UInt32 → UInt32 → Bool) (v : U32Vec) (lo hi : Nat) :
    U32Vec :=
  sortRange less v lo hi

/-- `INSERTION_SORT (TYPE, N, A, LESS)` alone (used by `profile.c`) for an `Array`. -/
@[inline] def insertionSortArray [Inhabited α] (less : α → α → Bool) (a : Array α) : Array α :=
  if a.size = 0 then a else insertionSort less a 0 a.size

/-! ### Permutation proofs -/

section Perm
variable (less : α → α → Bool)

local notation "L" => (SwapBuf.toList : β → List α)

theorem greaterSwap_perm (b : β) (p q : Nat) : (L (greaterSwap less b p q)).Perm (L b) := by
  unfold greaterSwap; split
  · exact swap_perm ..
  · exact .refl _

theorem partitionLoop_perm (pivot : α) (lp bound : Nat) (b : β) (i j : Nat) :
    (L (partitionLoop less pivot lp bound b i j).1).Perm (L b) := by
  rw [partitionLoop]
  split
  · exact .refl _
  · rename_i h
    exact (partitionLoop_perm pivot lp bound _ _ _).trans (swap_perm ..)
termination_by j - i
decreasing_by
  have := (scanUp less b pivot bound (i + 1)).2
  have := (scanDown less b pivot lp (j - 1)).2
  omega

theorem quickSortStep_perm (b : β) (l r : Nat) :
    (L (quickSortStep less b l r).1).Perm (L b) := by
  unfold quickSortStep
  exact (swap_perm ..).trans <| (partitionLoop_perm ..).trans <| (greaterSwap_perm ..).trans <|
    (greaterSwap_perm ..).trans <| (greaterSwap_perm ..).trans (swap_perm ..)

theorem quickSort_perm (b : β) (l r : Nat) : (L (quickSort less b l r)).Perm (L b) := by
  rw [quickSort]
  split
  · exact .refl _
  · split
    rename_i b' i hstep
    have hs : (L b').Perm (L b) := by
      have := quickSortStep_perm less b l r; rw [hstep] at this; exact this
    split
    · rename_i h
      split
      · exact (quickSort_perm _ _ _).trans ((quickSort_perm _ _ _).trans hs)
      · exact (quickSort_perm _ _ _).trans ((quickSort_perm _ _ _).trans hs)
    · exact hs
termination_by r - l
decreasing_by all_goals omega

theorem insertionSortBubble_perm (lo : Nat) (b : β) (i : Nat) :
    (L (insertionSortBubble less lo b i)).Perm (L b) := by
  induction i generalizing b with
  | zero => simp [insertionSortBubble]
  | succ i ih =>
    simp only [insertionSortBubble]
    split
    · exact (ih _).trans (greaterSwap_perm ..)
    · exact .refl _

theorem insertionSortSink_perm (lo : Nat) (b : β) (j : Nat) :
    (L (insertionSortSink less lo b j)).Perm (L b) := by
  induction j generalizing b with
  | zero => simp [insertionSortSink]
  | succ j ih =>
    simp only [insertionSortSink]
    split
    · split
      · exact (ih _).trans (swap_perm ..)
      · exact .refl _
    · exact .refl _

theorem insertionSortLoop_perm (lo hi : Nat) (b : β) (i : Nat) :
    (L (insertionSortLoop less lo hi b i)).Perm (L b) := by
  rw [insertionSortLoop]
  split
  · exact (insertionSortLoop_perm lo hi _ _).trans (insertionSortSink_perm ..)
  · exact .refl _
termination_by hi - i

theorem insertionSort_perm (b : β) (lo hi : Nat) :
    (L (insertionSort less b lo hi)).Perm (L b) :=
  (insertionSortLoop_perm ..).trans (insertionSortBubble_perm ..)

theorem sortRange_perm (b : β) (lo hi : Nat) : (L (sortRange less b lo hi)).Perm (L b) := by
  unfold sortRange
  split
  · exact .refl _
  · exact (insertionSort_perm ..).trans (quickSort_perm ..)

end Perm

/-- `sortArray` returns a permutation of its input. -/
theorem sortArray_perm [Inhabited α] (less : α → α → Bool) (a : Array α) :
    (sortArray less a).toList.Perm a.toList := by
  unfold sortArray; split
  · exact .refl _
  · exact sortRange_perm (β := Array α) less a 0 a.size

theorem sortArrayRange_perm [Inhabited α] (less : α → α → Bool) (a : Array α) (lo hi : Nat) :
    (sortArrayRange less a lo hi).toList.Perm a.toList :=
  sortRange_perm (β := Array α) less a lo hi

theorem insertionSortArray_perm [Inhabited α] (less : α → α → Bool) (a : Array α) :
    (insertionSortArray less a).toList.Perm a.toList := by
  unfold insertionSortArray; split
  · exact .refl _
  · exact insertionSort_perm (β := Array α) less a 0 a.size

/-- `sortU32` returns a permutation of its input. -/
theorem sortU32_perm (less : UInt32 → UInt32 → Bool) (v : U32Vec) :
    (sortU32 less v).toList.Perm v.toList := by
  unfold sortU32; split
  · exact .refl _
  · exact sortRange_perm (β := U32Vec) less v 0 v.size

theorem sortU32Range_perm (less : UInt32 → UInt32 → Bool) (v : U32Vec) (lo hi : Nat) :
    (sortU32Range less v lo hi).toList.Perm v.toList :=
  sortRange_perm (β := U32Vec) less v lo hi


end Sorting
end LeanKissat
