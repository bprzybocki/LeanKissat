import LeanKissat.Core.Solver

/-! `INC (name)`, `ADD (name, n)`, `DEC`, `SUB` statistics macros (`statistics.h`).
Only `COUNTER`s exist as fields; `METRIC`/`STATISTIC` updates are omitted in the
port (they are no-ops in the default build). -/
namespace LeanKissat
open Lean

syntax "INC!" term:max ident : term
syntax "DEC!" term:max ident : term
syntax "ADD!" term:max ident term:max : term
syntax "SUB!" term:max ident term:max : term
syntax "GET!" term:max ident : term

macro_rules
  | `(INC! $s $f) => do
      let ix := mkIdent (`LeanKissat.Counters ++ (Name.mkSimple ("idx_" ++ f.getId.toString)))
      `({ $s with stats := ($s).stats.add $ix 1 })
  | `(DEC! $s $f) => do
      let ix := mkIdent (`LeanKissat.Counters ++ (Name.mkSimple ("idx_" ++ f.getId.toString)))
      `({ $s with stats := ($s).stats.sub $ix 1 })
  | `(ADD! $s $f $n) => do
      let ix := mkIdent (`LeanKissat.Counters ++ (Name.mkSimple ("idx_" ++ f.getId.toString)))
      `({ $s with stats := ($s).stats.add $ix $n })
  | `(SUB! $s $f $n) => do
      let ix := mkIdent (`LeanKissat.Counters ++ (Name.mkSimple ("idx_" ++ f.getId.toString)))
      `({ $s with stats := ($s).stats.sub $ix $n })
  | `(GET! $s $f) => do
      let fn := mkIdent (`LeanKissat.Counters ++ f.getId)
      `($fn ($s).stats)

/-- `GET` of a `METRIC`/`STATISTIC` in the default build. -/
def GET_IGNORED : UInt64 := UInt64.ofNat 0xFFFFFFFFFFFFFFFF

end LeanKissat
