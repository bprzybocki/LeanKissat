import LeanKissat.Util.U32Vec

open LeanKissat

namespace WordBench

def packed (a : U32Vec) (mask : UInt32) (steps : Nat) : UInt32 := Id.run do
  let mut a := a
  let mut x : UInt32 := 1
  let mut sum : UInt32 := 0
  for _ in [0:steps] do
    x := x * 1664525 + 1013904223
    let i := ((x >>> 8) &&& mask).toNat
    let v := a.get! i
    sum := sum + v
    a := a.set! i (v + 1)
  return sum

def words (a : Array UInt32) (mask : UInt32) (steps : Nat) : UInt32 := Id.run do
  let mut a := a
  let mut x : UInt32 := 1
  let mut sum : UInt32 := 0
  for _ in [0:steps] do
    x := x * 1664525 + 1013904223
    let i := ((x >>> 8) &&& mask).toNat
    let v := a[i]!
    sum := sum + v
    a := a.set! i (v + 1)
  return sum

def rawFloats (a : FloatArray) (mask : UInt32) (steps : Nat) : UInt32 := Id.run do
  let mut a := a
  let mut x : UInt32 := 1
  let mut sum : UInt32 := 0
  for _ in [0:steps] do
    x := x * 1664525 + 1013904223
    let i := ((x >>> 8) &&& mask).toNat
    let v := (a.get! i).toBits.toUInt32
    sum := sum + v
    a := a.set! i (Float.ofBits (v + 1).toUInt64)
  return sum

@[specialize] def measure {α : Type} (label : String) (run : α → UInt32) (a : α) : IO UInt32 := do
  let start ← IO.monoNanosNow
  let sum := run a
  let stop ← IO.monoNanosNow
  IO.println s!"{label} {(stop - start).toFloat / 1000000.0} ms checksum {sum}"
  return sum

end WordBench

def main (args : List String) : IO UInt32 := do
  let steps := (args.head?.bind String.toNat?).getD 5000000
  for n in [1024, 65536, 4194304] do
    IO.println s!"elements {n}, updates {steps}"
    let mask := UInt32.ofNat (n - 1)
    let a ← WordBench.measure "packed" (fun a => WordBench.packed a mask steps) (U32Vec.replicate n 0)
    let b ← WordBench.measure "Array UInt32" (fun a => WordBench.words a mask steps) (Array.replicate n 0)
    let c ← WordBench.measure "FloatArray bits" (fun a => WordBench.rawFloats a mask steps)
      (FloatArray.mk (Array.replicate n 0.0))
    if a != b || a != c then return 1
  return 0
