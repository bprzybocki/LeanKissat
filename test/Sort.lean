import LeanKissat.Util.Sort
import LeanKissat.Util.Radix
import LeanKissat.Core.SortLits

/-
Differential test of the sorting routines: performs exactly the same sequence of
operations as `test/unit/sort_driver.c` and prints the same output (see
`test/unit/run_sort.sh`). Every U32 test is run on both the `U32Vec` and the
`Array UInt32` instantiation; a mismatch between them prints `MISMATCH`.
With argument `bench`, times sorting 10^6 random `UInt32` (stderr).
-/
open LeanKissat LeanKissat.Sorting LeanKissat.Radix

namespace SortTest

abbrev M := StateT UInt64 IO

def rnd32 : M UInt32 := modifyGet fun (s : UInt64) =>
  let s' := s * 6364136223846793005 + 1442695040888963407
  ((s' >>> 32).toUInt32, s')

def rndn (n : UInt32) : M UInt32 := return (← rnd32) % n

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
def MIX_INIT : UInt64 := 14695981039346656037

def printArray (tag : String) (a : Array UInt32) : IO Unit := do
  let h := a.foldl (fun h x => mix h x.toUInt64) MIX_INIT
  let mut s := s!"{tag} n={a.size} h={h}"
  if a.size ≤ 64 then
    for x in a do s := s ++ s!" {x}"
  IO.println s

def NGENS : Nat := 8

def generate (g n : Nat) : M (Array UInt32) := do
  let mut a := Array.emptyWithCapacity n
  for i in [0:n] do
    let x ← match g with
      | 0 => rnd32
      | 1 => rndn 10
      | 2 => pure 42
      | 3 => do let r ← rndn 100000; pure (7 * r + 3)
      | 4 => pure i.toUInt32
      | 5 => pure (n - i).toUInt32
      | 6 => pure (i / 3).toUInt32
      | _ => pure (if i < n - i then i else n - i).toUInt32
    a := a.push x
  return a

def sizesFixed : Array Nat := #[50, 63, 64, 65, 100, 127, 128, 200, 255, 256, 257, 500,
  1000, 1999, 2000]

def nsizes : Nat := 41 + sizesFixed.size + 30

def sizeAt (k : Nat) : M Nat := do
  if k ≤ 40 then return k
  if k < 41 + sizesFixed.size then return sizesFixed[k - 41]!
  return (← rndn 2001).toNat

def less0 (a b : UInt32) : Bool := a < b
def less1 (a b : UInt32) : Bool := a % 7 < b % 7
def less2 (a b : UInt32) : Bool := (a >>> 4) % 5 > (b >>> 4) % 5

def lessOf (c : Nat) : UInt32 → UInt32 → Bool :=
  match c with
  | 0 => less0
  | 1 => less1
  | _ => less2

/-- Sort `[lo, hi)` with both instantiations; report a mismatch. -/
def sortBoth (c : Nat) (a : Array UInt32) (lo hi : Nat) : IO (Array UInt32) := do
  let r1 := (sortU32Range (lessOf c) (U32Vec.ofArray a) lo hi).toArray
  let r2 := sortArrayRange (lessOf c) a lo hi
  if r1 != r2 then IO.println "MISMATCH sort U32Vec vs Array"
  return r1

def testSort : M Unit := do
  IO.println "== sort"
  for k in [0:nsizes] do
    let n ← sizeAt k
    for g in [0:NGENS] do
      for c in [0:3] do
        let a ← generate g n
        let r ← sortBoth c a 0 n
        -- also the `SORT_STACK` entry points
        if (sortU32 (lessOf c) (U32Vec.ofArray a)).toArray != r ||
           sortArray (lessOf c) a != r then
          IO.println "MISMATCH sort stack"
        printArray s!"sort g{g} c{c}" r
  IO.println "== sort range"
  for k in [0:300] do
    let n := (← rndn (if k < 100 then 60 else 2001)).toNat
    let g := (← rndn NGENS.toUInt32).toNat
    let c := (← rndn 3).toNat
    let a ← generate g n
    let lo := (← rndn (n + 1).toUInt32).toNat
    let hi := lo + (← rndn (n - lo + 1).toUInt32).toNat
    let r ← sortBoth c a lo hi
    printArray s!"range g{g} c{c} lo{lo} hi{hi}" r
  IO.println "== sort pairs"
  for k in [0:200] do
    let n := (← rndn (if k < 100 then 70 else 2001)).toNat
    let m := 1 + (← rndn 20)
    let mut p : Array (UInt32 × UInt32) := #[]
    for i in [0:n] do
      let key ← rndn m
      p := p.push (key, i.toUInt32)
    let q := sortArray (fun x y => x.1 < y.1) p
    printArray "pairs" (q.map (·.2))
  IO.println "== insertion sort"
  for n in [1:101] do
    let g := (← rndn NGENS.toUInt32).toNat
    let a ← generate g n
    let r := insertionSortArray less1 a
    if (insertionSort (β := U32Vec) less1 (U32Vec.ofArray a) 0 n).toArray != r then
      IO.println "MISMATCH insertion sort"
    printArray "insertion" r

/-! ### radix -/

def rank32Of (r : Nat) : UInt32 → UInt32 :=
  match r with
  | 0 => fun x => x
  | 1 => fun x => x % 7
  | 2 => fun x => x &&& 0xFF00FF00
  | 3 => fun x => x >>> 8
  | 4 => fun x => (x % 3) <<< 24
  | 5 => fun _ => 0x12345678
  | 6 => fun x => x &&& 0xFFFF
  | _ => fun x => (x >>> 16) ^^^ (x &&& 0xFF)

def NRANKS32 : Nat := 8

def K64 : UInt64 := 0x9E3779B97F4A7C15

def rank64Of (r : Nat) : UInt32 × UInt32 → UInt64 :=
  match r with
  | 0 => fun p => (p.1.toUInt64 <<< 32) ||| p.2.toUInt64
  | 1 => fun p => p.1.toUInt64 * K64
  | 2 => fun p => (p.1 % 5).toUInt64 <<< 56
  | _ => fun p => p.1.toUInt64

def NRANKS64 : Nat := 4

def radixBoth (r : Nat) (a : Array UInt32) (lo hi : Nat) : IO (Array UInt32) := do
  let r1 := (radixSortU32Range (rank32Of r) (U32Vec.ofArray a) lo hi).toArray
  let r2 := radixSortArrayRange32 (rank32Of r) a lo hi
  if r1 != r2 then IO.println "MISMATCH radix U32Vec vs Array"
  return r1

def testRadix : M Unit := do
  IO.println "== radix32"
  for k in [0:nsizes] do
    let n ← sizeAt k
    for g in [0:NGENS] do
      for r in [0:NRANKS32] do
        let a ← generate g n
        let res ← radixBoth r a 0 n
        if (radixSortU32 (rank32Of r) (U32Vec.ofArray a)).toArray != res ||
           radixSortArray32 (rank32Of r) a != res then
          IO.println "MISMATCH radix stack"
        printArray s!"radix g{g} r{r}" res
  IO.println "== radix range"
  for k in [0:300] do
    let n := (← rndn (if k < 100 then 60 else 2001)).toNat
    let g := (← rndn NGENS.toUInt32).toNat
    let r := (← rndn NRANKS32.toUInt32).toNat
    let a ← generate g n
    let lo := (← rndn (n + 1).toUInt32).toNat
    let hi := lo + (← rndn (n - lo + 1).toUInt32).toNat
    let res ← radixBoth r a lo hi
    printArray s!"rrange g{g} r{r} lo{lo} hi{hi}" res
  IO.println "== radix u64 rank"
  for k in [0:100] do
    let n := (← rndn (if k < 50 then 60 else 2001)).toNat
    let g := (← rndn NGENS.toUInt32).toNat
    let a ← generate g n
    let rk := fun (x : UInt32) => x.toUInt64 * K64
    let res := (radixSortU32By64 rk (U32Vec.ofArray a)).toArray
    if radixSortArray64 rk a != res then IO.println "MISMATCH radix u64"
    printArray "radixu64" res
  IO.println "== radix64 pairs"
  for k in [0:400] do
    let n := (← rndn (if k < 200 then 70 else 2001)).toNat
    let m := 1 + (← rndn (if k % 2 == 1 then 20 else 1000000))
    let r := k % NRANKS64
    let mut p : Array (UInt32 × UInt32) := #[]
    for _ in [0:n] do
      let key ← rndn m
      let id ← rndn 4
      p := p.push (key, id)
    let q := radixSortArray64 (rank64Of r) p
    printArray s!"radix64 r{r}" (q.map fun x => x.1 * 4 + x.2)

/-! ### sort literals -/

def testSortLiterals : M Unit := do
  IO.println "== sort literals"
  for k in [0:3000] do
    let V := 2 + (← rndn 30).toNat
    let mut values := ByteArray.mk (Array.replicate 80 0)
    let mut levels : Array UInt32 := Array.replicate 40 0
    let mut vars : Array UInt32 := Array.replicate 40 0
    for i in [0:V] do
      let r ← rndn 3
      let v : UInt8 := r.toUInt8 - 1
      values := values.set! (2 * i) v
      values := values.set! (2 * i + 1) (0 - v)
      levels := levels.set! i (← rndn 10)
      vars := vars.set! i i.toUInt32
    for i' in [0:V - 1] do
      let i := V - 1 - i'
      let j := (← rndn (i + 1).toUInt32).toNat
      vars := vars.swapIfInBounds i j
    let size := 2 + (← rndn (V - 1).toUInt32).toNat
    let mut lits : Array UInt32 := #[]
    for i in [0:size] do
      lits := lits.push (2 * vars[i]! + (← rndn 2))
    -- place the clause inside a larger buffer (like the arena)
    let off := k % 5
    let junk : UInt32 := 0xDEADBEEF
    let buf := U32Vec.ofArray (Array.replicate off junk ++ lits ++ Array.replicate 3 junk)
    let levelsV := levels
    let buf := sortLiterals values (fun idx => levelsV[idx.toNat]!) buf off size
    let all := buf.toArray
    if all.extract 0 off != Array.replicate off junk ||
       all.extract (off + size) all.size != Array.replicate 3 junk then
      IO.println "MISMATCH sort literals junk"
    printArray "lits" (all.extract off (off + size))

/-! ### bench -/

def bench : M Unit := do
  let n := 1000000
  let a ← generate 0 n
  let t ← IO.monoNanosNow
  let r := sortU32 less0 (U32Vec.ofArray a)
  let r := r.toArray
  let h := r.foldl (fun h x => mix h x.toUInt64) MIX_INIT
  let t' ← IO.monoNanosNow
  IO.eprintln s!"Lean sortU32 10^6 UInt32 (incl. ofArray/toArray): {(t' - t).toFloat / 1e9} s (h={h})"
  printArray "bench sort" r
  let a ← generate 0 n
  let t ← IO.monoNanosNow
  let r := (radixSortU32 id (U32Vec.ofArray a)).toArray
  let h := r.foldl (fun h x => mix h x.toUInt64) MIX_INIT
  let t' ← IO.monoNanosNow
  IO.eprintln s!"Lean radixSortU32 10^6 UInt32 (incl. ofArray/toArray): {(t' - t).toFloat / 1e9} s (h={h})"
  printArray "bench radix" r
  -- extra timings (not mirrored in C; after all C-mirrored output)
  let a ← generate 0 n
  let v := U32Vec.ofArray a
  let t ← IO.monoNanosNow
  let r := sortU32 less0 v
  let h := r.get! 0 + r.get! (n - 1)
  let t' ← IO.monoNanosNow
  IO.eprintln s!"Lean sortU32 10^6 UInt32 (sort only): {(t' - t).toFloat / 1e9} s ({h})"
  let a ← generate 0 n
  let v := U32Vec.ofArray a
  let t ← IO.monoNanosNow
  let r := radixSortU32 id v
  let h := r.get! 0 + r.get! (n - 1)
  let t' ← IO.monoNanosNow
  IO.eprintln s!"Lean radixSortU32 10^6 UInt32 (sort only): {(t' - t).toFloat / 1e9} s ({h})"
  let a ← generate 0 n
  let t ← IO.monoNanosNow
  let r := sortArray less0 a
  let h := r[0]! + r[n - 1]!
  let t' ← IO.monoNanosNow
  IO.eprintln s!"Lean sortArray 10^6 UInt32 (sort only): {(t' - t).toFloat / 1e9} s ({h})"
  let a ← generate 0 n
  let t ← IO.monoNanosNow
  let r := radixSortArray32 id a
  let h := r[0]! + r[n - 1]!
  let t' ← IO.monoNanosNow
  IO.eprintln s!"Lean radixSortArray32 10^6 UInt32 (sort only): {(t' - t).toFloat / 1e9} s ({h})"
  let a ← generate 0 n
  let t ← IO.monoNanosNow
  let r := a.qsort (· < ·)
  let h := r[0]! + r[n - 1]!
  let t' ← IO.monoNanosNow
  IO.eprintln s!"(reference) Array.qsort 10^6 UInt32: {(t' - t).toFloat / 1e9} s ({h})"

end SortTest

def main (args : List String) : IO Unit := do
  let seed : UInt64 := 0x9E3779B97F4A7C15
  if args == ["bench"] then
    let _ ← SortTest.bench.run seed
  else
    let _ ← (do SortTest.testSort; SortTest.testRadix; SortTest.testSortLiterals).run seed
