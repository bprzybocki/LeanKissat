import LeanKissat.Util.U32Vec
import LeanKissat.Core.Basic

/-
Port of `sort.c`: `move_smallest_literal_to_front` and `kissat_sort_literals`,
which move the two "best" watch candidates of a clause to its front.

Solver view: the C code reads `solver->values` (literal-indexed `value` array) and
`solver->assigned[idx].level`. Here they are parameters:
* `values : ByteArray` — the solver's literal-indexed value array (`1`, `0xFF` = -1,
  `0`), as in `Core/Basic.lean`;
* `level : UInt32 → UInt32` — maps a variable index to `assigned[idx].level`
  (only called for assigned variables).
The literals are the slice `[off, off + size)` of a `U32Vec` (e.g. the arena words of
a clause, `off` = index of the first literal, or a temporary literal stack with
`off = 0`). `size ≥ 2` as in C.

How the solver calls it: C `kissat_sort_literals (solver, size, lits)` (or the
`INLINE_SORT` variant with explicit `values`/`assigned`, used by `collect.c`,
`dense.c`, `watch.c`; both behave identically) becomes
`arena := sortLiterals s.asg.values (fun i => <level of i>) arena off size`.
-/
namespace LeanKissat

/-- C `value > 0` for a `signed char` stored in a byte. -/
@[inline] def vPos (v : UInt8) : Bool := v != 0 && v < 128
/-- C `value < 0` for a `signed char` stored in a byte. -/
@[inline] def vNeg (v : UInt8) : Bool := v ≥ 128

/-- Scan loop of `move_smallest_literal_to_front` (sort.c) over the positions `[i, size)`:
  the best position, literal, value and level found so far. -/
def moveSmallestLoop (values : ByteArray) (level : UInt32 → UInt32) (satisfiedIsEnough : Bool)
    (lits : U32Vec) (off size : Nat) (pos : Nat) (best : Lit) (u : Value) (k : UInt32) (i : Nat) :
    Nat × Lit × Value :=
  if i < size then
    let b := lits.get! (off + i)
    let v := values.get! b.toNat
    if v == 0 || (vPos v && satisfiedIsEnough) then (i, b, v)
    else
      let l : UInt32 := if v != 0 then level (IDX b) else UInt32.ofNat 0xFFFFFFFF
      let better : Bool :=
        if vNeg u && vPos v then true
        else if vPos u && vNeg v then false
        else if vNeg u then k < l
        else k > l
      if better then moveSmallestLoop values level satisfiedIsEnough lits off size i b v l (i + 1)
      else moveSmallestLoop values level satisfiedIsEnough lits off size pos best u k (i + 1)
  else (pos, best, u)
termination_by size - i

/-- Port of `move_smallest_literal_to_front` (sort.c, static). Returns the value `u`
  (as C `value`, stored as a byte) and the updated literal buffer. -/
@[inline] def moveSmallestLiteralToFront (values : ByteArray) (level : UInt32 → UInt32)
    (satisfiedIsEnough : Bool) (lits : U32Vec) (off start size : Nat) : Value × U32Vec :=
  let a := lits.get! (off + start)
  let u := values.get! a.toNat
  if u == 0 || (vPos u && satisfiedIsEnough) then (u, lits) else
  let k : UInt32 := if u != 0 then level (IDX a) else UInt32.ofNat 0xFFFFFFFF
  let r := moveSmallestLoop values level satisfiedIsEnough lits off size 0 a u k (start + 1)
  if r.1 == 0 then (r.2.2, lits) else
  (r.2.2, (lits.set! (off + start) r.2.1).set! (off + r.1) a)

/-- Port of `kissat_sort_literals` (sort.c) on the literals `[off, off + size)` of
  `lits` (see the module docstring for the solver view). -/
@[inline] def sortLiterals (values : ByteArray) (level : UInt32 → UInt32)
    (lits : U32Vec) (off size : Nat) : U32Vec :=
  let (u, lits) := moveSmallestLiteralToFront values level false lits off 0 size
  if size > 2 then
    (moveSmallestLiteralToFront values level (!vNeg u) lits off 1 size).2
  else lits

end LeanKissat
