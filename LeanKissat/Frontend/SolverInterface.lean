import LeanKissat.Core.OptionsTable
import LeanKissat.Core.StatsTable

/-!
# Interface between the frontend and the solver core

The frontend (`Main.lean`, `Frontend/*`) only needs the following slice of the
`kissat.h` API, used in exactly this order by `application.c`:

1. `init options`            — `kissat_init` followed by all `kissat_set_option` calls
                               (options are fully resolved by the frontend: command
                               line, configurations, clamping).
2. `reserve s maxVar`        — `kissat_reserve` after the `p cnf` header (optional hint).
3. `add s lit` (repeatedly)  — `kissat_add`: external literal (`±1..EXTERNAL_MAX_VAR`),
                               `0` terminates a clause. Called in input order.
4. `solve s limits`          — `kissat_set_conflict_limit` / `kissat_set_decision_limit`
                               (and the `alarm` based `--time` limit) + `kissat_solve`.
                               Runs in `IO` so the core can print its verbose / report
                               lines (prefix `"c "`, verbosity from `options`) and read
                               the clock for the time limit.
5. after `solve`:
   * `value s elit`          — `kissat_value`: `elit` if true, `-elit` if false, `0` if
                               unassigned / not needed (only called after `.sat`, for
                               `1 ≤ elit ≤ maxVar` of the header).
   * `statistics s`          — the `COUNTER`s (and glue usage arrays) for `--statistics`.

The solver state is a pure value threaded through (CONVENTIONS.md: single `Solver`
structure updated functionally); keep it unique to get in-place updates.
-/

namespace LeanKissat.Frontend

open LeanKissat

/-- Result of `kissat_solve`. -/
inductive SolveResult where
  | unknown
  | sat
  | unsat
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Exit code / C return value of `kissat_solve`: 10, 20 or 0. -/
def SolveResult.code : SolveResult → UInt8
  | .sat => 10
  | .unsat => 20
  | .unknown => 0

/-- Search limits set by the application before `kissat_solve`. -/
structure Limits where
  /-- `--conflicts=N`: stop after `N` conflicts (relative to the current count). -/
  conflicts : Option Nat := none
  /-- `--decisions=N`: stop after `N` decisions. -/
  decisions : Option Nat := none
  /-- `--time=N`: wall/process time limit in seconds (C: `alarm` + `kissat_terminate`). -/
  time : Option Nat := none
  deriving Repr, Inhabited

/-- The solver as seen by the frontend. -/
class SolverInterface (σ : Type) where
  /-- `kissat_init` with the given option values (`kissat_set_option` for each). -/
  init : Options → σ
  /-- `kissat_reserve (solver, maxVar)` (hint, called once after the header). -/
  reserve : σ → Nat → σ := fun s _ => s
  /-- `kissat_add (solver, lit)`; `0` terminates the current clause. -/
  add : σ → Int32 → σ
  /-- Set limits and run `kissat_solve`. -/
  solve : σ → Limits → IO (SolveResult × σ)
  /-- `kissat_value (solver, elit)`. -/
  value : σ → Int32 → Int32
  /-- Statistics counters (`solver->statistics`). -/
  statistics : σ → Stats

/-! ## Trivial stub (until the real solver core exists) -/

/-- Stub solver: accepts all clauses, always answers `unknown`, zero statistics. -/
structure StubSolver where
  options : Options
  deriving Inhabited

instance : SolverInterface StubSolver where
  init o := ⟨o⟩
  add s _ := s
  solve s _ := pure (.unknown, s)
  value _ _ := 0
  statistics _ := {}

end LeanKissat.Frontend
