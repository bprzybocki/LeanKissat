/-
Exponential moving averages with bias correction (`smooth.c/h`, non-`LOGGING`
build) and the `averages` bundle (`averages.c/h`, default build: the `#ifndef QUIET`
fields `level`, `size`, `trail` are present).
-/
namespace LeanKissat

/-- C `struct smooth` (without the `LOGGING`-only `name`/`updated`). -/
structure Smooth where
  value : Float := 0
  biased : Float := 0
  alpha : Float := 0
  beta : Float := 0
  exp : Float := 0
  deriving Inhabited, Repr

namespace Smooth

/-- Port of `kissat_init_smooth` (smooth.c). `window` is the (positive) `int`
  option value; C computes `1.0 / window` with `window` converted to `double`. -/
def init (window : Nat) : Smooth :=
  let alpha : Float := 1.0 / window.toFloat
  { value := 0, biased := 0, alpha := alpha, beta := 1.0 - alpha, exp := 1.0 }

/-- Port of `kissat_update_smooth` (smooth.c). Same operation order as C. -/
def update (s : Smooth) (y : Float) : Smooth :=
  let oldBiased := s.biased
  let delta := y - oldBiased
  let scaledDelta := s.alpha * delta
  let newBiased := oldBiased + scaledDelta
  let oldExp := s.exp
  -- C: `if (old_exp)` i.e. `old_exp != 0.0`
  if oldExp != 0.0 then
    let newExp := oldExp * s.beta
    if newExp == oldExp then
      { s with biased := newBiased, exp := 0, value := newBiased }
    else
      let div := 1 - newExp
      { s with biased := newBiased, exp := newExp, value := newBiased / div }
  else
    { s with biased := newBiased, value := newBiased }

end Smooth

/-- C `struct averages` (default build, i.e. with the `#ifndef QUIET` fields). -/
structure Averages where
  initialized : Bool := false
  fastGlue : Smooth := {}
  slowGlue : Smooth := {}
  level : Smooth := {}
  size : Smooth := {}
  trail : Smooth := {}
  decisionRate : Smooth := {}
  savedDecisions : UInt64 := 0
  deriving Inhabited, Repr

namespace Averages

/-- Port of `kissat_init_averages` (averages.c). `emafast` / `emaslow` are
  `GET_OPTION (emafast)` / `GET_OPTION (emaslow)`. No-op if already initialized
  (`savedDecisions` is never touched). The solver keeps two of these,
  `averages[stable]` (C macro `AVERAGES`). -/
def init (a : Averages) (emafast emaslow : Nat) : Averages :=
  if a.initialized then a
  else
    { a with
      level := Smooth.init emaslow
      size := Smooth.init emaslow
      trail := Smooth.init emaslow
      fastGlue := Smooth.init emafast
      slowGlue := Smooth.init emaslow
      decisionRate := Smooth.init emaslow
      initialized := true }

end Averages
end LeanKissat
