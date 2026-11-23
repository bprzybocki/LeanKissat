/-
Random number generator (`random.h`): 64-bit linear congruential generator with
Knuth's MMIX constants. `generator` is a plain `uint64_t`; every function takes the
generator state and returns the result together with the new state.
-/
namespace LeanKissat

/-- C `typedef uint64_t generator`. -/
abbrev Generator := UInt64

namespace Generator

/-- `2^32` as a `double`. PERF: written as a `UInt64` conversion (exact) since the
  literal `4294967296.0` is otherwise evaluated with `Float.ofScientific` (GMP) at every
  call of the inlined functions below. -/
@[inline] def twoPow32 : Float := (4294967296 : UInt64).toFloat

/-- Port of `kissat_next_random64` (random.h). Wrapping multiply then add. -/
@[inline] def nextRandom64 (rng : Generator) : UInt64 × Generator :=
  let r := rng * 6364136223846793005 + 1442695040888963407
  (r, r)

/-- Port of `kissat_next_random32` (random.h): upper 32 bits of the next 64-bit value. -/
@[inline] def nextRandom32 (rng : Generator) : UInt32 × Generator :=
  let (r, rng) := nextRandom64 rng
  ((r >>> 32).toUInt32, rng)

/-- Port of `kissat_pick_random` (random.h): value in `[l, r)` (or `l` if `l = r`).
  Same `double` arithmetic as C: `fraction = tmp / 2^32` (exact), then
  `(unsigned) (delta * fraction)` which truncates toward zero (`Float.toUInt32`
  truncates and the product is in `[0, delta)`). Requires `l ≤ r` (C asserts it). -/
@[inline] def pickRandom (rng : Generator) (l r : UInt32) : UInt32 × Generator :=
  if l == r then (l, rng)
  else
    let delta := r - l
    let (tmp, rng) := nextRandom32 rng
    let fraction : Float := tmp.toFloat / twoPow32
    let scaled : UInt32 := (delta.toFloat * fraction).toUInt32
    (l + scaled, rng)

/-- Port of `kissat_pick_bool` (random.h). -/
@[inline] def pickBool (rng : Generator) : Bool × Generator :=
  let (v, rng) := pickRandom rng 0 2
  (v != 0, rng)

/-- Port of `kissat_pick_double` (random.h): value in `[0, 1)`. -/
@[inline] def pickDouble (rng : Generator) : Float × Generator :=
  let (v, rng) := nextRandom32 rng
  (v.toFloat / twoPow32, rng)

theorem nextRandom64_snd (rng : Generator) :
    (nextRandom64 rng).2 = (nextRandom64 rng).1 := rfl

theorem pickRandom_same (rng : Generator) (l : UInt32) : pickRandom rng l l = (l, rng) := by
  simp [pickRandom]

end Generator
end LeanKissat
