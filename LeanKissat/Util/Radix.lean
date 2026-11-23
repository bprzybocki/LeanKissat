import LeanKissat.Util.U32Vec

/-
Port of Kissat's LSD radix sort (`rank.h`): `RADIX_SORT`, `RADIX_STACK`.

The C macro sorts `N` elements of type `VTYPE` by a rank of type `RTYPE`
(`unsigned` or `uint64_t`) with one stable counting-sort pass per byte of the rank
(least significant byte first). Its exact behaviour is reproduced:
* the first pass (byte 0) always counts and computes `LOWER` (bitwise AND of all
  ranks) and `UPPER` (bitwise OR of all ranks);
* every later pass whose byte is constant (`(LOWER & SHIFT) == (UPPER & SHIFT)`) is
  skipped without looking at the data; the first pass is skipped after counting if
  byte 0 is constant;
* a pass whose byte sequence is already non-decreasing is skipped after counting;
* `COUNT` is reset only on `[MLOWER, MUPPER]` of the previous counted pass and prefix
  sums only run over `[MLOWER, MUPPER]` of the current one;
* elements ping-pong between the input and a temporary buffer (allocated on the
  first scatter pass) and are copied back at the end if they ended in the temporary.

Both `RTYPE`s are handled by one implementation computing on `UInt64` with
`bits ∈ {32, 64}` passes of 8 bits: a 32-bit rank zero-extended to 64 bits gives the
same bytes, and `LOWER` starts as `~0` of the right width.

The algorithm is written once over `RadixBuf` and instantiated for `Array α` and
`U32Vec`; all functions work on a slice `[lo, hi)` (C: `RADIX_SORT (VTYPE, RTYPE,
hi - lo, A + lo, RANK)`). All loops are `for` loops over ranges.
-/
namespace LeanKissat
namespace Radix

/-- Buffer interface needed by the radix sort. -/
class RadixBuf (β : Type) (α : outParam Type) where
  get : β → Nat → α
  set : β → Nat → α → β
  /-- An empty buffer (placeholder before the temporary is allocated). -/
  empty : β
  /-- Fresh buffer holding a copy of the slice `[lo, hi)` (the temporary; C uses
    uninitialised `kissat_malloc` memory, whose content is never read before being
    written). -/
  copySlice : β → Nat → Nat → β

instance {α : Type} [Inhabited α] : RadixBuf (Array α) α where
  get a i := a[i]!
  set a i x := a.set! i x
  empty := #[]
  copySlice a lo hi := a.extract lo hi

/-- Copy of the slice `[lo, hi)` of a `U32Vec`. -/
def u32CopySlice (v : U32Vec) (lo hi : Nat) : U32Vec := Id.run do
  let mut r := U32Vec.emptyWithCapacity (hi - lo)
  for k in [lo:hi] do
    r := r.push (v.get! k)
  return r

instance : RadixBuf U32Vec UInt32 where
  get v i := v.get! i
  set v i x := v.set! i x
  empty := U32Vec.empty
  copySlice := u32CopySlice

variable {β α : Type} [RadixBuf β α]
open RadixBuf

/-- Result of a counting pass: counts, `SORTED_RADIX`, `LOWER_RADIX`, `UPPER_RADIX`. -/
structure CountResult where
  count : Array Nat
  sorted : Bool
  lower : UInt64
  upper : UInt64

/-- Counting loop of `RADIX_SORT` (rank.h) over `src[off + k]` for `k ∈ [k, n)`
  (`SORTED_RADIX`/`LAST_RADIX` logic, `LOWER`/`UPPER` while not `BOUNDED`). -/
@[specialize] def countLoop (rank : α → UInt64) (src : β) (off n : Nat) (i : UInt64)
    (bounded : Bool) (k : Nat) (count : Array Nat) (sorted : Bool)
    (last lower upper : UInt64) : CountResult :=
  if k < n then
    let r := rank (get src (off + k))
    let lower := if bounded then lower else lower &&& r
    let upper := if bounded then upper else upper ||| r
    let m := (r >>> i) &&& 255
    -- if (SORTED_RADIX && LAST_RADIX > M_RADIX) SORTED_RADIX = false;
    -- else LAST_RADIX = M_RADIX;
    let unsorted := sorted && last > m
    let last := if unsorted then last else m
    let count := count.modify m.toNat (· + 1)
    countLoop rank src off n i bounded (k + 1) count (sorted && !unsorted) last lower upper
  else ⟨count, sorted, lower, upper⟩
termination_by n - k

/-- Scatter loop of `RADIX_SORT` (rank.h): `D[COUNT[M]++] = *P` for
  `P = src + soff + k`, `D = dst + doff`. -/
@[specialize] def scatterLoop (rank : α → UInt64) (src : β) (soff : Nat) (dst : β) (doff n : Nat)
    (i : UInt64) (k : Nat) (count : Array Nat) : β × Array Nat :=
  if k < n then
    let x := get src (soff + k)
    let m := ((rank x) >>> i) &&& 255
    let p := count[m.toNat]!
    let count := count.set! m.toNat (p + 1)
    scatterLoop rank src soff (set dst (doff + p) x) doff n i (k + 1) count
  else (dst, count)
termination_by n - k

/-- `memcpy (dst + doff, src + soff, n * sizeof *dst)`. -/
@[specialize] def copyLoop (src : β) (soff : Nat) (dst : β) (doff n k : Nat) : β :=
  if k < n then copyLoop src soff (set dst (doff + k) (get src (soff + k))) doff n (k + 1)
  else dst
termination_by n - k

/-- Port of `RADIX_SORT (VTYPE, RTYPE, hi - lo, A + lo, RANK)` (rank.h) where `RTYPE`
  has `bits` bits (`32` for `unsigned`, `64` for `uint64_t`); `rank` must return
  values below `2^bits`. -/
@[specialize] def radixSortCore (bits : Nat) (rank : α → UInt64) (a : β) (lo hi : Nat) : β :=
  Id.run do
  let n := hi - lo
  if n ≤ 1 then return a
  let lengthRadix : UInt64 := 8
  let mask : UInt64 := 255
  let mut a := a
  let mut t : β := empty
  let mut allocated := false
  -- `inA`: the current data (C: `C_RADIX`) is in `a` (else in `t`)
  let mut inA := true
  let mut count : Array Nat := Array.replicate 256 0
  let mut mlower : UInt64 := 0
  let mut mupper : UInt64 := mask
  let mut bounded := false
  let mut upper : UInt64 := 0
  let mut lower : UInt64 := if bits = 64 then ~~~0 else 0xFFFFFFFF
  for pass in [0:bits / 8] do
    let i : UInt64 := lengthRadix * pass.toUInt64
    let shift : UInt64 := mask <<< i
    if bounded && (lower &&& shift) == (upper &&& shift) then continue
    -- memset (COUNT + MLOWER, 0, (MUPPER - MLOWER + 1) * sizeof *COUNT)
    for j in [mlower.toNat:mupper.toNat + 1] do
      count := count.set! j 0
    let res := if inA then countLoop rank a lo n i bounded 0 count true 0 lower upper
      else countLoop rank t 0 n i bounded 0 count true 0 lower upper
    count := res.count
    lower := res.lower
    upper := res.upper
    let sorted := res.sorted
    mlower := (lower >>> i) &&& mask
    mupper := (upper >>> i) &&& mask
    if !bounded then
      bounded := true
      if (lower &&& shift) == (upper &&& shift) then continue
    if sorted then continue
    let mut pos := 0
    for j in [mlower.toNat:mupper.toNat + 1] do
      let delta := count[j]!
      count := count.set! j pos
      pos := pos + delta
    if !allocated then
      t := copySlice a lo hi
      allocated := true
    if inA then
      let (t', count') := scatterLoop rank a lo t 0 n i 0 count
      t := t'
      count := count'
    else
      let (a', count') := scatterLoop rank t 0 a lo n i 0 count
      a := a'
      count := count'
    inA := !inA
  if !inA then
    -- memcpy (A_RADIX, B_RADIX, N_RADIX * sizeof *A_RADIX)
    a := copyLoop t 0 a lo n 0
  return a

/-! ### Entry points -/

/-- `RADIX_STACK (VTYPE, unsigned, S, RANK)` for an `Array`. -/
@[inline] def radixSortArray32 [Inhabited α] (rank : α → UInt32) (a : Array α) : Array α :=
  radixSortCore 32 (fun x => (rank x).toUInt64) a 0 a.size

/-- `RADIX_STACK (VTYPE, uint64_t, S, RANK)` for an `Array`. -/
@[inline] def radixSortArray64 [Inhabited α] (rank : α → UInt64) (a : Array α) : Array α :=
  radixSortCore 64 rank a 0 a.size

/-- `RADIX_SORT (VTYPE, unsigned, hi - lo, A + lo, RANK)` for a slice of an `Array`. -/
@[inline] def radixSortArrayRange32 [Inhabited α] (rank : α → UInt32) (a : Array α)
    (lo hi : Nat) : Array α :=
  radixSortCore 32 (fun x => (rank x).toUInt64) a lo hi

/-- `RADIX_SORT (VTYPE, uint64_t, hi - lo, A + lo, RANK)` for a slice of an `Array`. -/
@[inline] def radixSortArrayRange64 [Inhabited α] (rank : α → UInt64) (a : Array α)
    (lo hi : Nat) : Array α :=
  radixSortCore 64 rank a lo hi

/-- `RADIX_STACK (unsigned, unsigned, S, RANK)` for a `U32Vec`. -/
@[inline] def radixSortU32 (rank : UInt32 → UInt32) (v : U32Vec) : U32Vec :=
  radixSortCore 32 (fun x => (rank x).toUInt64) v 0 v.size

/-- `RADIX_STACK (unsigned, uint64_t, S, RANK)` for a `U32Vec`. -/
@[inline] def radixSortU32By64 (rank : UInt32 → UInt64) (v : U32Vec) : U32Vec :=
  radixSortCore 64 rank v 0 v.size

/-- `RADIX_SORT (unsigned, unsigned, hi - lo, A + lo, RANK)` for a slice of a `U32Vec`. -/
@[inline] def radixSortU32Range (rank : UInt32 → UInt32) (v : U32Vec) (lo hi : Nat) : U32Vec :=
  radixSortCore 32 (fun x => (rank x).toUInt64) v lo hi

end Radix
end LeanKissat
