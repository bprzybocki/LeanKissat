/-
Reluctant doubling, i.e. Luby sequence restart scheduling (`reluctant.c/h`).
-/
namespace LeanKissat

/-- C `struct reluctant`. -/
structure Reluctant where
  limited : Bool := false
  trigger : Bool := false
  period : UInt64 := 0
  wait : UInt64 := 0
  u : UInt64 := 0
  v : UInt64 := 0
  limit : UInt64 := 0
  deriving Inhabited, Repr, BEq

namespace Reluctant

/-- Port of `kissat_enable_reluctant` (reluctant.c). -/
def enable (r : Reluctant) (period limit : UInt64) : Reluctant :=
  let period := if limit != 0 && period > limit then limit else period
  { r with limited := limit > 0, trigger := false, period := period, wait := period,
           u := 1, v := 1, limit := limit }

/-- Port of `kissat_disable_reluctant` (reluctant.c). -/
def disable (r : Reluctant) : Reluctant := { r with period := 0 }

/-- Port of `kissat_tick_reluctant` (reluctant.c).
  C asserts `wait > 0` (it is, since `period > 0` and `wait` is reset to `v * period`
  with `v ≥ 1`), `UINT64_MAX / 2 ≥ v` and `UINT64_MAX / v ≥ period`. We keep the
  C computation with `UInt64` wrap-around arithmetic: with the option bounds
  (`reluctantint ≤ 2^15`, `limit ≤ 2^30`, limited case) the values stay tiny; for
  the unlimited case `v` doubles only `O(log u)` times between resets of `v`, so the
  asserted bounds are far from being reached in any feasible run. -/
def tick (r : Reluctant) : Reluctant :=
  if r.period == 0 then r
  else if r.trigger then r
  else
    let wait := r.wait - 1
    if wait != 0 then { r with wait := wait }
    else
      let u := r.u
      let v := r.v
      let (u, v) := if (u &&& (0 - u)) == v then (u + 1, (1 : UInt64)) else (u, v * 2)
      let wait := v * r.period
      let (u, v, wait) :=
        if r.limited && wait > r.limit then ((1 : UInt64), (1 : UInt64), r.period)
        else (u, v, wait)
      { r with trigger := true, wait := wait, u := u, v := v }

/-- Port of `kissat_reluctant_triggered` (reluctant.h): returns whether triggered and
  clears the trigger. -/
@[inline] def triggered (r : Reluctant) : Bool × Reluctant :=
  if !r.trigger then (false, r) else (true, { r with trigger := false })

/-- Port of `kissat_init_reluctant` (reluctant.c) with the option values
  `reluctant`, `reluctantint`, `reluctantlim` passed explicitly (C `int`s
  converted to `uint64_t`; all options are non-negative). -/
def initFromOptions (r : Reluctant) (reluctant : Bool) (reluctantint reluctantlim : Nat) :
    Reluctant :=
  if reluctant then r.enable (UInt64.ofNat reluctantint) (UInt64.ofNat reluctantlim)
  else r.disable

theorem tick_disabled (r : Reluctant) (h : r.period = 0) : r.tick = r := by
  simp [tick, h]

end Reluctant
end LeanKissat
