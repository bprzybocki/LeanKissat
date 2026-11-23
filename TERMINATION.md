# Termination of Kissat's search loop (`search.c: kissat_search`)

## Verdict
The outer CDCL loop **terminates mathematically**, assuming
(a) all inner procedures terminate (each probe/eliminate sub-procedure, walk, etc. —
audited separately, they are effort/ticks/rounds bounded),
(b) the chronological-backtracking propagation invariant (Möhle & Biere, SAT'19) holds
for Kissat's propagation code (to be proven as part of the port), and
(c) counters are unbounded.

With C's actual `uint64_t` counters and `double` scheduling arithmetic, termination is
**not provable**: the worst-case bound is astronomically larger than 2^64 conflicts,
after which `limits.X.conflicts = CONFLICTS + delta` wraps (and huge `double → uint64_t`
conversions are UB). See "Issues to decide" below.

## Argument

### Step kinds of one loop iteration
propagate (no conflict) / analyze (conflict) / iterate / SAT / reduce / mode switch /
restart / reorder / rephase (+walk) / probe / eliminate / decide.

### 1. Non-conflict steps between conflicts are bounded
* decide: trail grows; bounded by #vars.
* restart: focused — limit becomes `CONFLICTS + delta`, `delta ≥ restartint ≥ 1`;
  stable — needs reluctant `trigger`, which is set only by learning (`learn.c:124`) and
  consumed by the restart. ⇒ ≤ 1 restart per conflict.
* reduce, reorder, rephase, probe, eliminate: fire only when `CONFLICTS ≥ limit` and
  then set `limit = CONFLICTS + delta`, `delta ≥ 1` (option minima: reduceint ≥ 2,
  reorderint ≥ 1, rephaseint ≥ 10, probeint ≥ 2, eliminateint ≥ 10, scale factor ≥ 25).
  eliminate without changed variables does not fire and does not move its limit, but
  it can then fire at most once before its limit moves.
* mode switch: focused→stable needs `+modeint·nlog⁴n ≥ 10` conflicts; stable→focused
  needs ticks; so ≤ 2 switches per conflict.
* iterate: flag is set only by learning units.

### 2. "Missed implications" and post-backtrack learnings form bounded chains
Measure `M` = vector `(n_0, n_1, …)`, `n_i` = #literals assigned at level `i`, compared
lexicographically (finite domain: Σ n_i ≤ #vars).
* propagation (lit at level ≤ current) and decisions increase `M`.
* missed implication (`one_literal_on_conflict_level`): backtracks to
  `new_level ≥ jump_level` (keeps all levels ≤ new_level) and assigns the forced literal
  at `jump_level` ⇒ `M` increases.
* learning: backtrack to conflict level, then to `new_level ≥ jump`, UIP at `jump` ⇒
  `M` increases. Same for learned units / failed-literal units at level 0.
* Backtracking in a consistent state (restart, rephase, reorder, …) cannot produce a
  conflict before the next decision: the retained trail is a subset of a UP-closed,
  conflict-free assignment and unit propagation is monotone.
* After a decision with complete propagation, every literal assigned before the next
  backtrack has the decision level, so the next conflict has ≥ 2 literals on the current
  level ⇒ no missed implication.
Hence missed implications and "non-fresh" learnings (in the propagation directly after a
backtrack, before a decision) only occur in chains after a fresh learning, and each chain
strictly increases `M` ⇒ bounded length.

### 3. Fresh learnings strictly grow the subsumption closure
Let `Up(D)` = set of clauses subsumed by some clause of the DB `D` (root units included).
A **fresh** learned clause (conflict reached after a decision without intervening
backtrack) is not subsumed by any clause of `D`: such a clause would have been
falsified or unit before the last decision. So `Up(D)` strictly grows.
Within search, the only other clause changes are eager subsumption (removes clauses
subsumed by the new one), OTFS (replaces a clause by a strict subset), non-fresh learnings
(add clauses), root-satisfied clause removal (subsumed by a unit) — none shrinks `Up(D)`.
Note: non-fresh learnings *can* be subsumed by (even equal to) an existing clause, when
that clause is falsified but not yet propagated; so a plain "no clause is learned twice"
argument does **not** work for Kissat; this two-level argument is needed.

The clause universe is finite: fresh variables (BVA/`factor`) come from
`kissat_fresh_literal`, which refuses beyond `EXTERNAL_MAX_VAR` (`import.c:85`).
⇒ conflicts per *event-free window* (no reduce/probe/eliminate/rephase-walk, the only
steps that delete non-subsumed clauses, or add arbitrary ones) are bounded by a constant B.

### 4. Event gaps tend to infinity
Consecutive reduce / probe / eliminate / rephase events are separated by
`int·sqrt(k)`, `int·k·log(k)·scale`, `int·k·log²(k)·scale`, `int·k·log³(k)` conflicts —
each → ∞. Once every kind's gap exceeds 4B, any 5 consecutive events span ≤ 4B
conflicts (each window ≤ B) yet contain two events of the same kind (4 kinds):
contradiction.
So only finitely many events, then at most B more conflicts, then the loop stops (SAT,
UNSAT, or a user limit).

Formal measure (lexicographic): events-until-all-gaps-exceed-4B, remaining events (≤ 5),
`|universe \ Up(D)|`, chain measure (`M` from top), non-conflict-step measure.

## Issues to decide (port deviations needed for a *proof*)
1. **64-bit counters.** Proposal: use `Nat` for monotone statistics counters and limits.
   Identical to C below 2^64 (unreachable in practice); makes the argument go through.
2. **Floating-point scheduling.** Deltas use `sqrt`, `log10`, `double` multiplication
   (`kimits.c`, `restart.c:44`, `mode.c`). Lean's `Float` is opaque — nothing can be proven
   about it (not even `log10 x ≥ 1`). Proposal: keep the exact Float computation but clamp
   with an integer lower bound that is provably ≤ the exact real value and → ∞, e.g.
   `max(floatDelta, int · Nat.sqrt k)` for reduce, `max(…, restartint)` for restarts.
   For counts < 2^53 and a monotone correctly-rounded `sqrt`/`log10` this never changes
   behaviour. (Alternative: a pure-Lean softfloat implementation; costly, and libm `log10`
   is not specified bit-exactly anyway.)
3. Bound `B` is astronomically large (≈ 3^(2^28)); fine for a proof, irrelevant in practice.

## Decision (2026-11-22)
UInt64 counters with `unknown` on overflow. The Lean termination proof therefore only
needs: (1) finitely many loop iterations between consecutive conflicts (§1, plus the
OTFS increments inside `kissat_analyze`), and (2) the conflict counter cannot exceed
2^64 without returning. The closure/event-gap argument (§2–§4) is kept as the answer to
"does idealized Kissat terminate", not as part of the Lean proof.
Corrections after reviewing Codex's notes: OTFS increments `CONFLICTS` without finishing
a conflict (bounded by clause shrinkage); arena/variable exhaustion is a separate outcome.
