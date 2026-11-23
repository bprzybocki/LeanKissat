import Std.Tactic.BVDecide
/-
Literals, values and basic constants (`literal.h`, `value.h`, `reference.h`,
`assign.h`, `utilities.h`).
-/
namespace LeanKissat

/-- Internal literal: `2 * idx + sign`. -/
abbrev Lit := UInt32
/-- Clause reference: index of a 16-byte `ward` in the arena. -/
abbrev Ref := UInt32

def LD_MAX_VAR : Nat := 30
def EXTERNAL_MAX_VAR : Nat := (1 <<< LD_MAX_VAR) - 1
def INTERNAL_MAX_VAR : Nat := (1 <<< LD_MAX_VAR) - 2
def INTERNAL_MAX_LIT : Nat := 2 * INTERNAL_MAX_VAR + 1
def ILLEGAL_LIT : UInt32 := (1 <<< (1 + 30 : UInt32)) - 1
def INVALID_IDX : UInt32 := UInt32.ofNat 0xFFFFFFFF
def INVALID_LIT : UInt32 := UInt32.ofNat 0xFFFFFFFF
def INVALID_REF : UInt32 := UInt32.ofNat 0xFFFFFFFF
def INVALID_LEVEL : UInt32 := UInt32.ofNat 0xFFFFFFFF
def INVALID_TRAIL : UInt32 := UInt32.ofNat 0xFFFFFFFF
def DECISION_REASON : UInt32 := UInt32.ofNat 0xFFFFFFFF
def UNIT_REASON : UInt32 := UInt32.ofNat 0xFFFFFFFE
def LD_MAX_REF : Nat := 31
def MAX_REF : Nat := (1 <<< LD_MAX_REF) - 1

@[inline] def IDX (lit : Lit) : UInt32 := lit >>> 1
@[inline] def LIT (idx : UInt32) : Lit := idx <<< 1
@[inline] def NOT (lit : Lit) : Lit := lit ^^^ 1
@[inline] def NEGATED (lit : Lit) : Bool := (lit &&& 1) != 0
@[inline] def STRIP (lit : Lit) : Lit := lit &&& ~~~1

theorem NOT_NOT (l : Lit) : NOT (NOT l) = l := by
  simp [NOT, UInt32.xor_assoc]

theorem NOT_ne (l : Lit) : NOT l ≠ l := by
  simp only [NOT, ne_eq]; bv_decide

theorem IDX_NOT (l : Lit) : IDX (NOT l) = IDX l := by
  simp only [IDX, NOT]; bv_decide

/-- C `signed char` values stored in a `ByteArray`: `1` true, `0xFF` (-1) false,
  `0` unassigned. -/
abbrev Value := UInt8
def VAL_TRUE : Value := 1
def VAL_FALSE : Value := 0xFF
def VAL_UNASSIGNED : Value := 0
/-- `value > 0` in C. -/
@[inline] def vTrue (v : Value) : Bool := v == 1
/-- `value < 0` in C. -/
@[inline] def vFalse (v : Value) : Bool := v == 0xFF
/-- C `signed char` → `Int`. -/
@[inline] def Value.toInt (v : Value) : Int := if v < 128 then v.toNat else (v.toNat : Int) - 256
/-- `BOOL_TO_VALUE`. -/
@[inline] def boolToValue (b : Bool) : Value := if b then 0xFF else 1
@[inline] def Value.neg (v : Value) : Value := 0 - v

/-- `kissat_cache_lines (n, sizeof (watch))` with `ASSUMED_LD_CACHE_LINE_BYTES = 7`. -/
@[inline] def cacheLines (n : UInt64) : UInt64 :=
  if n == 0 then 0 else (n + 31) >>> 5

end LeanKissat

namespace LeanKissat
/-- `kissat_average`. -/
@[inline] def kissatAverage (a b : Float) : Float := if b != 0 then a / b else 0.0
/-- `kissat_percent`. -/
@[inline] def kissatPercent (a b : Float) : Float := kissatAverage (100.0 * a) b
end LeanKissat
