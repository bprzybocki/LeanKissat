import LeanKissat.Core.Macros

/-
Limit scheduling helpers (`kimits.c`, `kimits.h`).
-/
namespace LeanKissat

/-- Port of `kissat_logn`: `log10 (count + 9)`. -/
@[inline] def kLogn (count : UInt64) : Float := Float.log10 ((count + 9).toFloat)

/-- Port of `kissat_sqrt`. -/
@[inline] def kSqrt (count : UInt64) : Float := Float.sqrt count.toFloat

/-- Port of `kissat_nlogpown`. -/
def kNlogpown (count : UInt64) (exponent : Nat) : Float :=
  let tmp := Float.log10 ((count + 9).toFloat)
  let factor := Nat.repeat (fun f => f * tmp) exponent 1.0
  count.toFloat * factor

@[inline] def kLinear (count : UInt64) : Float := count.toFloat

/-- Unsigned 64-bit addition; flags overflow (C would wrap). -/
@[inline] def addOverflow (a b : UInt64) : UInt64 × Bool :=
  let r := a + b
  (r, r < a)

namespace Solver

@[inline] def binirrClauses (s : Solver) : UInt64 :=
  s.stats.clauses_binary + s.stats.clauses_irredundant

/-- Port of `kissat_scale_delta` (kimits.c). -/
def scaleDelta (s : Solver) (delta : UInt64) : UInt64 :=
  let c := s.binirrClauses
  let f := kLogn (c + 1) - 5
  let ff := f * f
  let fff := 4.5 * ff + 25
  (fff * delta.toFloat).toUInt64

/-- `CONFLICTS + delta`, setting `overflowed` on wrap-around. -/
def conflictsPlus (s : Solver) (delta : UInt64) : UInt64 × Solver :=
  let (r, o) := addOverflow s.stats.conflicts delta
  if o then (UInt64.ofNat 0xFFFFFFFFFFFFFFFF, { s with overflowed := true }) else (r, s)

/-- Generic `UPDATE_CONFLICT_LIMIT (NAME, COUNT, SCALE_COUNT_FUNCTION, SCALE_DELTA)`
  (kimits.h). Returns the new limit (or `none` if `inconsistent`, in which case the
  limit stays). `minDelta` is the provable lower bound clamp (`-- CLAMP:`), use 0 to
  disable. -/
def updateConflictLimitDelta (s : Solver) (int : Nat) (count : UInt64)
    (scale : UInt64 → Float) (scaleDeltaP : Bool) (minDelta : UInt64) : UInt64 :=
  let delta : UInt64 := UInt64.ofNat int
  let scaling := scale count
  let delta := (delta.toFloat * scaling).toUInt64
  let scaled := if scaleDeltaP then s.scaleDelta delta else delta
  max scaled minDelta

end Solver
end LeanKissat
