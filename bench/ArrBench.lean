@[simp] theorem ByteArray.size_set' (as : ByteArray) (i : Nat) (a : UInt8) (h : i < as.size) :
    (as.set i a h).size = as.size := by
  show (as.set i a h).data.size = as.data.size
  rw [ByteArray.data_set]; exact Array.size_set ..

@[inline] def rd (b : ByteArray) (i : Nat) : UInt32 :=
  let j := 4*i
  (b.get! j).toUInt32 ||| ((b.get! (j+1)).toUInt32 <<< 8) ||| ((b.get! (j+2)).toUInt32 <<< 16) ||| ((b.get! (j+3)).toUInt32 <<< 24)
@[inline] def rd2 (b : ByteArray) (i : Nat) : UInt32 :=
  let j := 4*i
  if h : j+3 < b.size then
    (b[j]).toUInt32 ||| ((b[j+1]).toUInt32 <<< 8) ||| ((b[j+2]).toUInt32 <<< 16) ||| ((b[j+3]).toUInt32 <<< 24)
  else 0
@[inline] def wr2 (b : ByteArray) (i : Nat) (v : UInt32) : ByteArray :=
  let j := 4*i
  if h : j+3 < b.size then
    let b1 := b.set j v.toUInt8 (by omega)
    let b2 := b1.set (j+1) (v >>> 8).toUInt8 (by simp [b1]; omega)
    let b3 := b2.set (j+2) (v >>> 16).toUInt8 (by simp [b2, b1]; omega)
    b3.set (j+3) (v >>> 24).toUInt8 (by simp [b3, b2, b1]; omega)
  else b
@[inline] def wr (b : ByteArray) (i : Nat) (v : UInt32) : ByteArray :=
  let j := 4*i
  ((((b.set! j v.toUInt8).set! (j+1) (v >>> 8).toUInt8).set! (j+2) (v >>> 16).toUInt8).set! (j+3) (v >>> 24).toUInt8)

def loopA (a : Array UInt32) (n steps : Nat) : Array UInt32 × UInt32 := Id.run do
  let mut a := a; let mut x : UInt32 := 1; let mut acc : UInt32 := 0
  for _ in [0:steps] do
    x := x * 1664525 + 1013904223
    let i := (x >>> 8).toNat % n
    let v := a[i]!
    acc := acc + v
    a := a.set! i (v + 1)
  return (a, acc)

def loopB (b : ByteArray) (n steps : Nat) : ByteArray × UInt32 := Id.run do
  let mut b := b; let mut x : UInt32 := 1; let mut acc : UInt32 := 0
  for _ in [0:steps] do
    x := x * 1664525 + 1013904223
    let i := (x >>> 8).toNat % n
    let v := rd b i
    acc := acc + v
    b := wr b i (v + 1)
  return (b, acc)

def loopC (b : ByteArray) (n steps : Nat) : ByteArray × UInt32 := Id.run do
  let mut b := b; let mut x : UInt32 := 1; let mut acc : UInt32 := 0
  for _ in [0:steps] do
    x := x * 1664525 + 1013904223
    let i := (x >>> 8).toNat % n
    let v := rd2 b i
    acc := acc + v
    b := wr2 b i (v + 1)
  return (b, acc)

def main (args : List String) : IO Unit := do
  let n := 1 <<< 22; let steps := 50000000
  let t0 ← IO.monoMsNow
  let (_, r1) := loopA (Array.replicate n 0) n steps
  let t1 ← IO.monoMsNow
  IO.println s!"Array UInt32: {t1-t0} ms {r1}"
  let (_, r2) := loopB (ByteArray.mk (Array.replicate (4*n) 0)) n steps
  let t2 ← IO.monoMsNow
  IO.println s!"ByteArray:    {t2-t1} ms {r2}"
  let (_, r3) := loopC (ByteArray.mk (Array.replicate (4*n) 0)) n steps
  let t3 ← IO.monoMsNow
  IO.println s!"ByteArray dep: {t3-t2} ms {r3}"
