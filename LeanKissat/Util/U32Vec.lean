import LeanKissat.Util.BitTac

/-
Packed growable vectors of `UInt32`, stored little-endian in a `ByteArray`.

Lean has no packed `UInt32` array; `Array UInt32` uses 8-byte slots on a 64-bit
machine and benchmarked ~2x slower for random access (bench/ArrBench.lean).
Like a C stack, a `U32Vec` has a logical `size` and a capacity (`data.size / 4`), so
shrinking is O(1) and never reallocates.
-/
namespace LeanKissat

theorem ByteArray.size_eq_data_size (as : ByteArray) : as.size = as.data.size := rfl

@[simp] theorem ByteArray.size_set' (as : ByteArray) (i : Nat) (a : UInt8) (h : i < as.size) :
    (as.set i a h).size = as.size := by
  simp only [ByteArray.size_eq_data_size, ByteArray.data_set, Array.size_set]

theorem ByteArray.getElem_set' (as : ByteArray) (i : Nat) (a : UInt8) (h : i < as.size)
    (j : Nat) (hj : j < (as.set i a h).size) :
    (as.set i a h)[j] = if i = j then a else as[j]'(by simpa using hj) := by
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set]

@[simp] theorem ByteArray.size_push' (as : ByteArray) (a : UInt8) :
    (as.push a).size = as.size + 1 := ByteArray.size_push

theorem ByteArray.getElem_push' (as : ByteArray) (a : UInt8) (j : Nat)
    (hj : j < (as.push a).size) :
    (as.push a)[j] = if h : j < as.size then as[j] else a := by
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_push, Array.getElem_push]
  rfl

/-- Decode four little-endian bytes. -/
@[inline] def decode32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

theorem decode32_encode (v : UInt32) :
    decode32 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8 = v := by
  simp only [decode32]; bv_k

structure U32Vec where
  data : ByteArray
  size : Nat
  hsize : 4 * size ≤ data.size

namespace U32Vec

instance : Inhabited U32Vec := ⟨⟨.empty, 0, by simp⟩⟩

def empty : U32Vec := ⟨.empty, 0, by simp⟩

/-- Empty vector with room for `n` elements. -/
def emptyWithCapacity (n : Nat) : U32Vec := ⟨ByteArray.emptyWithCapacity (4 * n), 0, by simp⟩

@[inline] def get (a : U32Vec) (i : Nat) (h : i < a.size) : UInt32 :=
  have := a.hsize
  decode32 a.data[4*i] a.data[4*i+1] a.data[4*i+2] a.data[4*i+3]

private theorem word_index (i : Nat) (hi : 4 * i + 3 < USize.size) :
    (i.toUSize * 4).toNat = 4 * i := by
  have ei : i.toUSize.toNat = i := USize.toNat_ofNat_of_lt' (by omega)
  have e4 : (4 : USize).toNat = 4 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_mul, ei, e4]
  change (i * 4) % USize.size = 4 * i
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem word_offset (i k : Nat) (hi : 4 * i + 3 < USize.size) (hk : k ≤ 3) :
    (i.toUSize * 4 + k.toUSize).toNat = 4 * i + k := by
  have ek : k.toUSize.toNat = k :=
    USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)
  rw [USize.toNat_add, word_index i hi, ek]
  change (4 * i + k) % USize.size = 4 * i + k
  exact Nat.mod_eq_of_lt (by omega)

/-- Read a packed word with machine-sized byte indices. The literal bound fits on
  both supported word sizes; larger indices use the original reader. -/
@[inline] def getFast (a : U32Vec) (i : Nat) (h : i < a.size) : UInt32 :=
  if hs : i < 1073741824 then
    let j := i.toUSize * 4
    have hi : 4 * i + 3 < USize.size := by have := USize.le_size; omega
    decode32 (a.data.uget (j + (0 : Nat).toUSize)
        (by rw [word_offset i 0 hi (by omega)]; have := a.hsize; omega))
      (a.data.uget (j + (1 : Nat).toUSize)
        (by rw [word_offset i 1 hi (by omega)]; have := a.hsize; omega))
      (a.data.uget (j + (2 : Nat).toUSize)
        (by rw [word_offset i 2 hi (by omega)]; have := a.hsize; omega))
      (a.data.uget (j + (3 : Nat).toUSize)
        (by rw [word_offset i 3 hi (by omega)]; have := a.hsize; omega))
  else
    have := a.hsize
    decode32 a.data[4*i] a.data[4*i+1] a.data[4*i+2] a.data[4*i+3]

private theorem uget_eq_get (d : ByteArray) (i : USize) (h : i.toNat < d.size) :
    d.uget i h = d.get i.toNat h := by cases d; rfl

/-- The compiler rewrite is justified by a kernel-checked equality. -/
@[csimp] theorem get_eq_getFast : @get = @getFast := by
  funext a i h
  unfold getFast
  split
  · rename_i hs
    have hi : 4 * i + 3 < USize.size := by have := USize.le_size; omega
    dsimp only
    simp only [uget_eq_get, word_offset i 0 hi (by omega), word_offset i 1 hi (by omega),
      word_offset i 2 hi (by omega), word_offset i 3 hi (by omega), Nat.add_zero]
    rfl
  · rfl

instance : GetElem U32Vec Nat UInt32 (fun a i => i < a.size) where
  getElem a i h := a.get i h

/-- Read with default `0` when out of bounds. Keep the bounds branch out of callers
  so it does not prevent reuse of enclosing solver records. -/
@[noinline] def get! (a : U32Vec) (i : Nat) : UInt32 :=
  if h : i < a.size then a[i] else 0

@[inline] def setBytes (d : ByteArray) (j : Nat) (v : UInt32) (h : j + 3 < d.size) : ByteArray :=
  let d1 := d.set j v.toUInt8 (by omega)
  let d2 := d1.set (j+1) (v >>> 8).toUInt8 (by simp [d1]; omega)
  let d3 := d2.set (j+2) (v >>> 16).toUInt8 (by simp [d2, d1]; omega)
  d3.set (j+3) (v >>> 24).toUInt8 (by simp [d3, d2, d1]; omega)

@[simp] theorem size_setBytes (d : ByteArray) (j : Nat) (v : UInt32) (h : j + 3 < d.size) :
    (setBytes d j v h).size = d.size := by
  simp [setBytes]

theorem getElem_setBytes (d : ByteArray) (j : Nat) (v : UInt32) (h : j + 3 < d.size)
    (k : Nat) (hk : k < (setBytes d j v h).size) :
    (setBytes d j v h)[k] =
      if k = j then v.toUInt8 else if k = j+1 then (v >>> 8).toUInt8
      else if k = j+2 then (v >>> 16).toUInt8 else if k = j+3 then (v >>> 24).toUInt8
      else d[k]'(by simpa using hk) := by
  simp only [setBytes, ByteArray.getElem_set']
  rcases (show k = j ∨ k = j+1 ∨ k = j+2 ∨ k = j+3 ∨
      (k ≠ j ∧ k ≠ j+1 ∧ k ≠ j+2 ∧ k ≠ j+3) by omega) with rfl|rfl|rfl|rfl|⟨h0,h1,h2,h3⟩
  all_goals simp_all [eq_comm]

@[inline] def set (a : U32Vec) (i : Nat) (v : UInt32) (h : i < a.size) : U32Vec :=
  have := a.hsize
  ⟨setBytes a.data (4*i) v (by omega), a.size, by simpa using a.hsize⟩

/-- Write into allocated byte storage; each out-of-bounds byte is unchanged.
  Keep the writer behind a call so it does not prevent reuse of enclosing records. -/
@[noinline] def set! (a : U32Vec) (i : Nat) (v : UInt32) : U32Vec :=
  let j := 4 * i
  ⟨((((a.data.set! j v.toUInt8).set! (j+1) (v >>> 8).toUInt8).set! (j+2) (v >>> 16).toUInt8).set!
      (j+3) (v >>> 24).toUInt8), a.size, by simpa using a.hsize⟩

private theorem byte_offset (j k : Nat) (hj : j + 3 < USize.size) (hk : k ≤ 3) :
    (j.toUSize + k.toUSize).toNat = j + k := by
  have ej : j.toUSize.toNat = j := USize.toNat_ofNat_of_lt' (by omega)
  have ek : k.toUSize.toNat = k :=
    USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)
  rw [USize.toNat_add, ej, ek]
  change (j + k) % USize.size = j + k
  exact Nat.mod_eq_of_lt (by omega)

private theorem byte_uset_eq_set (d : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < d.size) :
    d.uset i v h = d.set i.toNat v h := by
  cases d
  simp only [ByteArray.uset, ByteArray.set, Array.uset_eq_set]

private theorem bytes_uset_size (d : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < d.size) :
    (d.uset i v h).size = d.size := by
  rw [byte_uset_eq_set]
  exact ByteArray.size_set' ..

/-- `setBytes` with machine-sized byte indices. The literal bound fits on both supported
  word sizes; larger indices use the original writer. -/
@[inline] def setBytesFast (d : ByteArray) (j : Nat) (v : UInt32) (h : j + 3 < d.size) : ByteArray :=
  if hs : j < 4294967293 then
    let u := j.toUSize
    have hj : j + 3 < USize.size := by have := USize.le_size; omega
    let d1 := d.uset (u + (0 : Nat).toUSize) v.toUInt8
      (by rw [byte_offset j 0 hj (by omega)]; omega)
    let d2 := d1.uset (u + (1 : Nat).toUSize) (v >>> 8).toUInt8
      (by simp only [d1, bytes_uset_size]; rw [byte_offset j 1 hj (by omega)]; omega)
    let d3 := d2.uset (u + (2 : Nat).toUSize) (v >>> 16).toUInt8
      (by simp only [d2, d1, bytes_uset_size]; rw [byte_offset j 2 hj (by omega)]; omega)
    d3.uset (u + (3 : Nat).toUSize) (v >>> 24).toUInt8
      (by simp only [d3, d2, d1, bytes_uset_size]; rw [byte_offset j 3 hj (by omega)]; omega)
  else
    let d1 := d.set j v.toUInt8 (by omega)
    let d2 := d1.set (j+1) (v >>> 8).toUInt8 (by simp [d1]; omega)
    let d3 := d2.set (j+2) (v >>> 16).toUInt8 (by simp [d2, d1]; omega)
    d3.set (j+3) (v >>> 24).toUInt8 (by simp [d3, d2, d1]; omega)

@[csimp] theorem setBytes_eq_setBytesFast : @setBytes = @setBytesFast := by
  funext d j v h
  unfold setBytesFast
  split
  · rename_i hs
    have hj : j + 3 < USize.size := by have := USize.le_size; omega
    dsimp only
    simp only [byte_uset_eq_set, byte_offset j 0 hj (by omega), byte_offset j 1 hj (by omega),
      byte_offset j 2 hj (by omega), byte_offset j 3 hj (by omega), Nat.add_zero]
    rfl
  · rfl

private theorem byte_set!_eq_set (d : ByteArray) (i : Nat) (v : UInt8) (h : i < d.size) :
    d.set! i v = d.set i v h := by
  cases d with
  | mk data =>
    have hi : i < data.size := h
    simp only [ByteArray.set!, ByteArray.set, Array.set!_eq_setIfInBounds,
      Array.setIfInBounds_def, hi, dite_true]

private theorem setBytes_eq_four (d : ByteArray) (j : Nat) (v : UInt32) (h : j + 3 < d.size) :
    setBytes d j v h =
      ((((d.set! j v.toUInt8).set! (j+1) (v >>> 8).toUInt8).set! (j+2) (v >>> 16).toUInt8).set!
        (j+3) (v >>> 24).toUInt8) := by
  unfold setBytes
  have h0 : j < d.size := by omega
  rw [byte_set!_eq_set d j _ h0]
  rw [byte_set!_eq_set _ (j+1) _ (by simp only [ByteArray.size_set']; omega)]
  rw [byte_set!_eq_set _ (j+2) _ (by simp only [ByteArray.size_set']; omega)]
  rw [byte_set!_eq_set _ (j+3) _ (by simp only [ByteArray.size_set']; omega)]

/-- `set!` using `setBytesFast` when the whole word is in bounds. -/
@[noinline] def setFast (a : U32Vec) (i : Nat) (v : UInt32) : U32Vec :=
  let j := 4 * i
  if h : j + 3 < a.data.size then
    ⟨setBytesFast a.data j v h, a.size,
      by rw [← setBytes_eq_setBytesFast, size_setBytes]; exact a.hsize⟩
  else
    ⟨((((a.data.set! j v.toUInt8).set! (j+1) (v >>> 8).toUInt8).set! (j+2) (v >>> 16).toUInt8).set!
      (j+3) (v >>> 24).toUInt8), a.size, by simpa using a.hsize⟩

@[csimp] theorem set!_eq_setFast : @set! = @setFast := by
  funext a i v
  unfold setFast
  dsimp only
  split
  · rename_i h
    simp only [set!, U32Vec.mk.injEq]
    constructor
    · rw [← setBytes_eq_setBytesFast, setBytes_eq_four]
    · trivial
  · rfl

/-- Grow the byte buffer by four zero bytes. -/
@[inline] def pushZero4 (d : ByteArray) : ByteArray := (((d.push 0).push 0).push 0).push 0

@[simp] theorem size_pushZero4 (d : ByteArray) : (pushZero4 d).size = d.size + 4 := by
  simp [pushZero4]

theorem getElem_pushZero4 (d : ByteArray) (k : Nat) (hk : k < d.size) :
    (pushZero4 d)[k]'(by simp; omega) = d[k] := by
  have h1 : k < d.size + 1 := by omega
  have h2 : k < d.size + 1 + 1 := by omega
  have h3 : k < d.size + 1 + 1 + 1 := by omega
  simp only [pushZero4, ByteArray.getElem_push', ByteArray.size_push', hk, h1, h2, h3, dite_true]

/-- Make room for one more element. -/
@[inline] def reserve1 (a : U32Vec) : U32Vec :=
  if 4 * a.size + 3 < a.data.size then a
  else ⟨pushZero4 a.data, a.size, by have := a.hsize; simp; omega⟩

@[simp] theorem size_reserve1 (a : U32Vec) : (reserve1 a).size = a.size := by
  unfold reserve1; split <;> rfl

theorem reserve1_room (a : U32Vec) : 4 * (reserve1 a).size + 3 < (reserve1 a).data.size := by
  have := a.hsize
  unfold reserve1; split
  · assumption
  · simp; omega

theorem data_reserve1 (a : U32Vec) (k : Nat) (hk : k < a.data.size) :
    ∃ hk' : k < (reserve1 a).data.size, (reserve1 a).data[k] = a.data[k] := by
  unfold reserve1; split
  · exact ⟨hk, rfl⟩
  · exact ⟨by simp; omega, getElem_pushZero4 _ _ hk⟩

/-- Push. Destructures `a` first so that the vector cell is reused in place. -/
@[noinline] def push (a : U32Vec) (v : UInt32) : U32Vec :=
  match a with
  | ⟨data, size, h⟩ =>
    if hc : 4 * size + 3 < data.size then
      ⟨setBytes data (4 * size) v hc, size + 1, by simp only [size_setBytes]; omega⟩
    else
      ⟨setBytes (pushZero4 data) (4 * size) v (by simp; omega), size + 1,
        by simp only [size_setBytes, size_pushZero4]; omega⟩

theorem push_eq (a : U32Vec) (v : UInt32) :
    a.push v = ⟨setBytes (reserve1 a).data (4 * (reserve1 a).size) v (reserve1_room a),
      (reserve1 a).size + 1, by have := reserve1_room a; simp only [size_setBytes]; omega⟩ := by
  obtain ⟨data, size, h⟩ := a
  simp only [push, reserve1]
  split <;> rfl

/-- Truncate to `n` elements (no-op if `n ≥ size`). O(1); capacity is kept. -/
@[noinline] def shrink (a : U32Vec) (n : Nat) : U32Vec :=
  if h : n ≤ a.size then ⟨a.data, n, by have := a.hsize; omega⟩ else a

@[inline] def clear (a : U32Vec) : U32Vec := a.shrink 0

@[inline] def back! (a : U32Vec) : UInt32 := a.get! (a.size - 1)

@[inline] def pop (a : U32Vec) : U32Vec := a.shrink (a.size - 1)

@[inline] def isEmpty (a : U32Vec) : Bool := a.size == 0

/-- Push `k` copies of `v`. -/
def pushN (a : U32Vec) (v : UInt32) : Nat → U32Vec
  | 0 => a
  | k + 1 => pushN (a.push v) v k

/-- Push `src[i..n)`. -/
def appendFrom (a src : U32Vec) (i n : Nat) : U32Vec :=
  if _h : i < n then appendFrom (a.push (src.get! i)) src (i + 1) n else a
termination_by n - i

/-- `n` copies of `v`. -/
def replicate (n : Nat) (v : UInt32) : U32Vec := pushN (emptyWithCapacity n) v n

def ofArray (xs : Array UInt32) : U32Vec := xs.foldl push (emptyWithCapacity xs.size)

def toArray (a : U32Vec) : Array UInt32 := Array.ofFn (fun i : Fin a.size => a[i])

def toList (a : U32Vec) : List UInt32 := a.toArray.toList

instance : Repr U32Vec := ⟨fun a _ => repr a.toArray⟩

/-! ### Specification lemmas -/

@[simp] theorem size_set (a : U32Vec) (i v h) : (a.set i v h).size = a.size := rfl

@[simp] theorem size_push (a : U32Vec) (v) : (a.push v).size = a.size + 1 := by
  rw [push_eq]; simp

theorem size_shrink (a : U32Vec) (n) : (a.shrink n).size = min n a.size := by
  unfold shrink; split <;> (try dsimp only) <;> omega

@[simp] theorem size_set! (a : U32Vec) (i : Nat) (v : UInt32) : (a.set! i v).size = a.size := rfl

theorem getElem_def (a : U32Vec) (i : Nat) (h : i < a.size) :
    a[i] = a.get i h := rfl

theorem getElem_set (a : U32Vec) (i : Nat) (v : UInt32) (h : i < a.size)
    (j : Nat) (hj : j < (a.set i v h).size) :
    (a.set i v h)[j] = if i = j then v else a[j]'(by simpa using hj) := by
  have hs := a.hsize
  simp only [getElem_def, get, set]
  simp only [getElem_setBytes]
  by_cases hij : i = j
  · subst hij; simp [decode32_encode]
  · simp only [hij, ite_false]
    have e : ∀ k, k < 4 → 4 * j + k ≠ 4 * i ∧ 4 * j + k ≠ 4 * i + 1 ∧
        4 * j + k ≠ 4 * i + 2 ∧ 4 * j + k ≠ 4 * i + 3 := by intro k hk; omega
    have e0 := e 0 (by omega); have e1 := e 1 (by omega)
    have e2 := e 2 (by omega); have e3 := e 3 (by omega)
    simp only [Nat.add_zero] at e0
    simp [e0, e1, e2, e3]
    rfl

theorem getElem_push (a : U32Vec) (v : UInt32) (j : Nat) (hj : j < (a.push v).size) :
    (a.push v)[j] = if h : j < a.size then a[j] else v := by
  have hs := a.hsize
  simp only [size_push] at hj
  rw [getElem_def]
  simp only [push_eq, get, getElem_setBytes, size_reserve1]
  by_cases hja : j < a.size
  · simp only [hja, dite_true]
    have : ∀ k, k < 4 → 4 * j + k ≠ 4 * a.size ∧ 4 * j + k ≠ 4 * a.size + 1 ∧
        4 * j + k ≠ 4 * a.size + 2 ∧ 4 * j + k ≠ 4 * a.size + 3 := by intro k hk; omega
    have e0 := this 0 (by omega); have e1 := this 1 (by omega)
    have e2 := this 2 (by omega); have e3 := this 3 (by omega)
    simp only [Nat.add_zero] at e0
    simp only [e0, e1, e2, e3, ite_false]
    obtain ⟨_, r0⟩ := data_reserve1 a (4*j) (by omega)
    obtain ⟨_, r1⟩ := data_reserve1 a (4*j+1) (by omega)
    obtain ⟨_, r2⟩ := data_reserve1 a (4*j+2) (by omega)
    obtain ⟨_, r3⟩ := data_reserve1 a (4*j+3) (by omega)
    simp only [r0, r1, r2, r3]
    rfl
  · have : j = a.size := by omega
    subst this; simp [decode32_encode]

theorem getElem_shrink (a : U32Vec) (n : Nat) (j : Nat) (hj : j < (a.shrink n).size) :
    (a.shrink n)[j] = a[j]'(by rw [size_shrink] at hj; omega) := by
  unfold shrink; split <;> rfl

end U32Vec
end LeanKissat
