import LeanKissat.Util.U32Vec
import LeanKissat.Util.WVec

/-!
# Read/write lemmas for the packed vectors (`get!` level)

The executable code uses the total accessors `get!`/`set!`/`push`; these lemmas
describe them extensionally.
-/

namespace LeanKissat

theorem ByteArray.set!_eq_set (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    a.set! i v = a.set i v h := by
  cases a with
  | mk data =>
    have h' : i < data.size := h
    simp only [ByteArray.set!, ByteArray.set, Array.set!_eq_setIfInBounds, Array.setIfInBounds]
    rw [dif_pos h']

@[simp] theorem ByteArray.size_set!' (a : ByteArray) (i : Nat) (v : UInt8) :
    (a.set! i v).size = a.size := by
  simp

theorem ByteArray.getElem_set!' (a : ByteArray) (i : Nat) (v : UInt8) (j : Nat)
    (hj : j < (a.set! i v).size) :
    (a.set! i v)[j] = if i = j then v else a[j]'(by simpa using hj) := by
  by_cases hi : i < a.size
  · rw [show (a.set! i v)[j] = (a.set i v hi)[j]'(by simpa using hj) by
        congr 1; exact ByteArray.set!_eq_set a i v hi]
    exact ByteArray.getElem_set' a i v hi j _
  · have hij : i ≠ j := by intro e; subst e; simp at hj; omega
    simp only [hij, ite_false]
    exact ByteArray.getElem_set!_ne a i j v hij _

namespace U32Vec

theorem get!_eq (a : U32Vec) (i : Nat) :
    a.get! i = if h : i < a.size then a[i] else 0 := rfl

/-- Reading the bytes of word `j` after writing the 4 bytes of word `i`. -/
theorem getElem_set! (a : U32Vec) (i : Nat) (v : UInt32) (j : Nat) (hj : j < (a.set! i v).size) :
    (a.set! i v)[j] = if i = j then v else a[j]'(by simpa using hj) := by
  have hs := a.hsize
  have hj' : j < a.size := by simpa using hj
  show decode32 _ _ _ _ = _
  simp only [set!, ByteArray.getElem_set!']
  by_cases hij : i = j
  · subst hij; simp [decode32_encode]
  · simp only [hij, ite_false]
    have e : ∀ k, k < 4 → 4 * i + k ≠ 4 * j ∧ 4 * i + k ≠ 4 * j + 1 ∧
        4 * i + k ≠ 4 * j + 2 ∧ 4 * i + k ≠ 4 * j + 3 := by intro k hk; omega
    have e0 := e 0 (by omega); have e1 := e 1 (by omega)
    have e2 := e 2 (by omega); have e3 := e 3 (by omega)
    simp only [Nat.add_zero] at e0
    simp only [e0, e1, e2, e3, ite_false]
    rfl

theorem get!_set! (a : U32Vec) (i : Nat) (v : UInt32) (j : Nat) :
    (a.set! i v).get! j = if i = j ∧ j < a.size then v else a.get! j := by
  by_cases hj : j < a.size
  · have hj2 : j < (a.set! i v).size := by simpa using hj
    rw [get!_eq, dif_pos hj2, getElem_set!, get!_eq, dif_pos hj]
    by_cases hij : i = j
    · simp only [hij, true_and, hj, ite_true]
    · simp only [hij, false_and, ite_false]; rfl
  · have hj2 : ¬ j < (a.set! i v).size := by simpa using hj
    rw [get!_eq, dif_neg hj2, get!_eq, dif_neg hj]
    simp only [hj, and_false, ite_false]

@[simp] theorem get!_set!_self (a : U32Vec) (i : Nat) (v : UInt32) (h : i < a.size) :
    (a.set! i v).get! i = v := by
  simp [get!_set!, h]

theorem get!_set!_ne (a : U32Vec) (i j : Nat) (v : UInt32) (h : i ≠ j) :
    (a.set! i v).get! j = a.get! j := by
  simp [get!_set!, h]

theorem get!_push (a : U32Vec) (v : UInt32) (j : Nat) :
    (a.push v).get! j = if j < a.size then a.get! j else if j = a.size then v else 0 := by
  simp only [get!_eq, size_push]
  by_cases hj : j < a.size
  · have : j < a.size + 1 := by omega
    simp only [this, hj, dite_true, ite_true]
    rw [getElem_push]; simp [hj]
  · by_cases he : j = a.size
    · subst he; simp only [Nat.lt_add_one, dite_true, hj, ite_false, ite_true]
      rw [getElem_push]; simp
    · have : ¬ j < a.size + 1 := by omega
      simp [this, hj, he]

theorem get!_shrink (a : U32Vec) (n j : Nat) :
    (a.shrink n).get! j = if j < n then a.get! j else 0 := by
  simp only [get!_eq, size_shrink]
  by_cases hj : j < min n a.size
  · have h1 : j < n := by omega
    have h2 : j < a.size := by omega
    simp only [hj, dite_true, h1, ite_true, h2]
    rw [getElem_shrink]
  · simp only [hj, dite_false]
    by_cases h1 : j < n
    · have h2 : ¬ j < a.size := by omega
      simp [h1, h2]
    · simp [h1]

end U32Vec

namespace WVec

theorem get!_set! (a : WVec) (i : Nat) (v : UInt32) (j : Nat) :
    (a.set! i v).get! j = if i = j ∧ j < a.size then v else a.get! j := by
  simp only [get!, set!, size]
  by_cases hij : i = j
  · subst hij
    by_cases h : i < a.data.size
    · simp [h, Array.getElem!_set!_self]
    · simp only [h, and_false, ite_false]
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, h]
  · simp only [hij, false_and, ite_false]
    exact Array.getElem!_set!_ne _ _ _ _ hij

theorem get!_push (a : WVec) (v : UInt32) (j : Nat) :
    (a.push v).get! j = if j < a.size then a.get! j else if j = a.size then v else default := by
  simp only [get!, push, size, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_push]
  by_cases hj : j < a.data.size
  · have : j ≠ a.data.size := by omega
    simp [hj, this]
  · by_cases he : j = a.data.size
    · simp [he]
    · have : a.data[j]? = none := by simp; omega
      simp [hj, he, this]

end WVec
end LeanKissat

namespace LeanKissat
namespace U32Vec

/-- The logical content of a `U32Vec` as a list. -/
def view (a : U32Vec) : List UInt32 := List.ofFn (fun i : Fin a.size => a[i])

@[simp] theorem length_view (a : U32Vec) : a.view.length = a.size := by simp [view]

theorem getElem_view (a : U32Vec) (i : Nat) (h : i < a.view.length) :
    a.view[i] = a[i]'(by simpa using h) := by simp [view]

theorem get!_eq_view (a : U32Vec) (i : Nat) : a.get! i = a.view.getD i 0 := by
  rw [get!_eq, List.getD_eq_getElem?_getD]
  by_cases h : i < a.size
  · rw [dif_pos h, List.getElem?_eq_getElem (by simpa using h), Option.getD_some, getElem_view]
  · rw [dif_neg h, List.getElem?_eq_none (by simp; omega)]; rfl

theorem get!_mem_view (v : U32Vec) (q : Nat) (hq : q < v.size) : v.get! q ∈ v.view := by
  rw [get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hq),
    Option.getD_some]; exact List.getElem_mem _

theorem mem_view_pos (v : U32Vec) (y : UInt32) (h : y ∈ v.view) : ∃ q, q < v.size ∧ v.get! q = y := by
  obtain ⟨q, hq, hx⟩ := List.mem_iff_getElem.mp h
  refine ⟨q, by simpa using hq, ?_⟩
  rw [get!_eq_view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some, hx]

theorem view_ext {a b : U32Vec} (hs : a.size = b.size)
    (h : ∀ i (ha : i < a.size) (hb : i < b.size), a[i] = b[i]) : a.view = b.view := by
  apply List.ext_getElem (by simp [hs])
  intro i h1 h2
  rw [getElem_view, getElem_view]; exact h i _ _

theorem view_push (a : U32Vec) (v : UInt32) : (a.push v).view = a.view ++ [v] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [getElem_view, getElem_push]
  by_cases hi : i < a.size
  · rw [dif_pos hi, List.getElem_append_left (by simpa using hi), getElem_view]
  · rw [dif_neg hi]
    have : i = a.size := by simp at h1; omega
    subst this
    simp


theorem view_pushN (v : UInt32) : ∀ (k : Nat) (a : U32Vec), (a.pushN v k).view = a.view ++ List.replicate k v := by
  intro k
  induction k with
  | zero => intro a; simp [pushN]
  | succ k ih =>
    intro a
    rw [pushN, ih, view_push, List.replicate_succ, List.append_assoc]
    rfl

theorem view_replicate (n : Nat) (v : UInt32) : (replicate n v).view = List.replicate n v := by
  unfold replicate
  rw [view_pushN]
  have : (emptyWithCapacity n).view = [] := List.eq_nil_of_length_eq_zero (by simp [emptyWithCapacity])
  rw [this, List.nil_append]

theorem size_replicate (n : Nat) (v : UInt32) : (replicate n v).size = n := by
  rw [← length_view, view_replicate, List.length_replicate]

theorem view_set! (a : U32Vec) (i : Nat) (v : UInt32) : (a.set! i v).view = a.view.set i v := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [getElem_view, getElem_set!, List.getElem_set]
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ite_false]; rw [getElem_view]; rfl

theorem view_shrink (a : U32Vec) (n : Nat) : (a.shrink n).view = a.view.take n := by
  apply List.ext_getElem (by simp [size_shrink])
  intro j h1 h2
  rw [getElem_view, getElem_shrink, List.getElem_take, getElem_view]

end U32Vec
end LeanKissat

namespace LeanKissat

theorem ByteArray.get!_set! (b : ByteArray) (i : Nat) (v : UInt8) (j : Nat) :
    (b.set! i v).get! j = if i = j ∧ i < b.size then v else b.get! j := by
  cases b with
  | mk data =>
    show (data.set! i v)[j]! = if i = j ∧ i < data.size then v else data[j]!
    by_cases hij : i = j
    · subst hij
      by_cases h : i < data.size
      · simp [h, Array.getElem!_set!_self]
      · simp only [h, and_false, ite_false]
        simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, h]
    · simp only [hij, false_and, ite_false]
      exact Array.getElem!_set!_ne _ _ _ _ hij

theorem ByteArray.get!_set!_self (b : ByteArray) (i : Nat) (v : UInt8) (h : i < b.size) :
    (b.set! i v).get! i = v := by simp [ByteArray.get!_set!, h]

theorem ByteArray.get!_set!_ne (b : ByteArray) (i j : Nat) (v : UInt8) (h : i ≠ j) :
    (b.set! i v).get! j = b.get! j := by simp [ByteArray.get!_set!, h]

theorem ByteArray.get!_oob (b : ByteArray) (i : Nat) (h : ¬ i < b.size) : b.get! i = 0 := by
  cases b with
  | mk data =>
    show data[i]! = 0
    have h' : ¬ i < data.size := h
    simp [h']; rfl

end LeanKissat
