/-
Growable `UInt32` vectors backed by `Array UInt32`, used for watch lists.
Sequential scans with in-place write-back are ~4x faster than with the
byte-packed `U32Vec` (bench2/ScanBench.lean); random-access data (the arena)
stays in `U32Vec`. The API mirrors `U32Vec`.
-/
namespace LeanKissat

structure WVec where
  data : Array UInt32
  deriving Inhabited

namespace WVec

@[inline] def empty : WVec := ⟨#[]⟩
@[inline] def size (a : WVec) : Nat := a.data.size
instance : GetElem WVec Nat UInt32 (fun a i => i < a.size) where
  getElem a i h := a.data[i]'h
@[inline] def get! (a : WVec) (i : Nat) : UInt32 := a.data[i]!
@[inline] def set! (a : WVec) (i : Nat) (v : UInt32) : WVec := ⟨a.data.set! i v⟩
@[inline] def push (a : WVec) (v : UInt32) : WVec := ⟨a.data.push v⟩
@[noinline] def shrink (a : WVec) (n : Nat) : WVec := ⟨a.data.shrink n⟩
@[inline] def clear (a : WVec) : WVec := ⟨a.data.shrink 0⟩
@[inline] def back! (a : WVec) : UInt32 := a.data.back!
@[inline] def pop (a : WVec) : WVec := ⟨a.data.pop⟩
@[inline] def toArray (a : WVec) : Array UInt32 := a.data

@[simp] theorem size_set! (a : WVec) (i : Nat) (v : UInt32) : (a.set! i v).size = a.size := by
  simp [set!, size]

@[simp] theorem size_push (a : WVec) (v : UInt32) : (a.push v).size = a.size + 1 := by
  simp [push, size]

end WVec
end LeanKissat
