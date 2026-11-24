# LeanKissat

> **Disclaimer:** All code, proofs and documentation in this repository were written
> entirely by an AI model. No human has reviewed them.

LeanKissat is a port of the [Kissat](https://github.com/arminbiere/kissat) SAT solver
(version 4.0.4) to Lean 4. For the `--plain` configuration it comes with a
machine-checked proof that it is sound:

* if it reports **UNSATISFIABLE**, the formula has no satisfying assignment;
* if it reports **SATISFIABLE**, the model it returns satisfies the formula.

The code contains no `unsafe`, `partial`, `implemented_by`, `extern` or `sorry`, so every
function provably terminates. The soundness theorems depend only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). The proofs do not use `native_decide`
or `bv_decide`.

## Status and limitations

* **Supported configurations:** only `--plain` and `--basic` run to completion. Kissat's
  other techniques (preprocessing, inprocessing, mode switching, and others) are not ported.
  Under other configurations, including the default, the solver stops with
  `s UNKNOWN` when it reaches an unported procedure.
* **Faithfulness:** `--plain` was compared against C Kissat 4.0.4 on thousands of random
  instances. Results and search statistics (conflicts, decisions, propagations, restarts,
  reductions) matched exactly. A few small, documented deviations exist where the proof
  required a runtime check (see `LeanKissat/Proofs/PROOF_PLAN.md`).
* **Performance:** it is much slower than C Kissat, roughly 5–7× under `--plain` on the
  instances measured (random formulas and SAT Anniversary Track benchmarks).
* **Input:** plain DIMACS CNF only, from a file or standard input. Compressed input
  (`.gz`, `.xz`, ...) is not supported.
* **No proof output:** DRAT/LRAT proof output is not supported.
* **Resource limits:** counters are 64-bit. If a counter would overflow or the clause arena
  is exhausted, the solver answers `UNKNOWN` rather than giving a wrong answer.

## Building

You need [elan](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` (4.36.0), and the only dependency,
[Batteries](https://github.com/leanprover-community/batteries), is fetched by Lake.

```sh
lake build            # library plus all proofs (several minutes)
lake build lkissat    # the command-line solver: .lake/build/bin/lkissat
```

## Using the command-line solver

The interface follows Kissat's:

```sh
.lake/build/bin/lkissat --plain formula.cnf      # solve a DIMACS file
.lake/build/bin/lkissat --plain < formula.cnf    # read from standard input
.lake/build/bin/lkissat --plain -q formula.cnf   # only print the result
.lake/build/bin/lkissat --plain -n formula.cnf   # do not print the model
.lake/build/bin/lkissat --help                   # all options
```

Output uses the SAT competition format. The answer is an `s` line, and for satisfiable
formulas the model is printed on `v` lines:

```
s SATISFIABLE
v -1 2 3 0
```

| Exit code | Meaning |
|---|---|
| 10 | satisfiable |
| 20 | unsatisfiable |
| 0 | unknown (limit reached or unported procedure) |
| 1 | error (for example, a parse error or an unknown option) |

Useful options:

* `--plain`: the verified configuration. `--basic` is `--plain` without restarts,
  clause minimization or clause database reduction.
* `--conflicts=N`, `--decisions=N`, `--time=SECONDS`: stop with `UNKNOWN` once the limit is reached.
  The time limit is wall-clock time from startup. When it fires, no statistics are printed.
* `-s` / `--statistics`: print search statistics.
* `--relaxed` / `--strict`: change how strictly the DIMACS header is checked.
* Individual Kissat options are accepted, for example `--restartint=10`. Changing
  `jumpreasons`, `tumble`, `otfs`, `eagersubsume`, `bumpreasons`, `reorder`, `rephase`,
  `restartreusetrail`, `stable` or `compact` away from their `--plain` values puts the run
  outside the proven configuration.

## Using it from Lean

The verified entry point is `LeanKissat.solveCNF`. It takes options and a `Std.Sat.CNF Nat`,
and returns Kissat's result code (10, 20 or 0) together with the final solver state:

```lean
import LeanKissat
open LeanKissat Std.Sat

-- (x0 ∨ x1) ∧ ¬x0 ∧ (¬x1 ∨ x2)
def F : CNF Nat :=
  ⟨#[.ofLiterals [(0, true), (1, true)], .ofLiterals [(0, false)],
     .ofLiterals [(1, false), (2, true)]]⟩

#eval let (r, s) := solveCNF plainOptions F; (r, (List.range 3).map (modelOf s))
-- (10, [false, true, true])

example (h : CNF.ValidVars F) (r : (solveCNF plainOptions F).1 = 20) : F.Unsat :=
  solveCNF_unsat_sound plainOptions_config h r
```

The main theorems are in `LeanKissat/Proofs/Soundness.lean`:

```lean
theorem solveCNF_unsat_sound (hc : PlainConfig opts) (hv : CNF.ValidVars F) :
    (solveCNF opts F).1 = 20 → F.Unsat
theorem solveCNF_sat_sound (hc : PlainConfig opts) (hv : CNF.ValidVars F) :
    (solveCNF opts F).1 = 10 → F.Sat (modelOf (solveCNF opts F).2)
```

* `PlainConfig opts` says that the options fix the settings listed above to their
  `--plain` values. `plainOptions` (proved by `plainOptions_config`) is exactly the option
  set the command line produces for `--plain`.
* `CNF.ValidVars F` requires the variable indices to be below Kissat's limit of 2^30 − 1.

## What is and is not verified

Verified (checked by Lean's kernel):

* The whole search inside `solveCNF`: propagation, conflict analysis, minimization,
  learning, backtracking, restarts, decisions, clause database reduction and garbage
  collection, under `PlainConfig`.

Not verified (part of the trusted base):

* The DIMACS parser, option parsing and output printing of the command-line front end
  (`LeanKissat/Frontend`, `Main.lean`). The binary runs the same search code as `solveCNF`,
  but the path from file to formula is unproven.
* The Lean compiler, runtime and C toolchain that produce the binary.
* That the statements of the theorems express what you want. Read `Soundness.lean` and
  `Proofs/Spec.lean`.

## Repository layout

| Path | Contents |
|---|---|
| `LeanKissat/Core`, `LeanKissat/Search`, `LeanKissat/Util` | the solver |
| `LeanKissat/Frontend`, `Main.lean` | command-line front end (unverified) |
| `LeanKissat/Proofs` | correctness proofs; `PROOF_PLAN.md` has status and deviations from C |
| `LeanKissat/Util/BitTac.lean` | `bv_k`, a kernel-checked tactic for small bit-vector goals |
| `PLAN.md`, `CONVENTIONS.md`, `TERMINATION.md` | porting plan and conventions |
| `scripts/` | random CNF generator, differential tester, profiling helper |
| `test/` | unit tests against the C data structures |
| `bench/`, `bench2/` | Lean micro-benchmarks used for data-structure choices |

## Testing against C Kissat (optional)

The library and proofs are self-contained. Only the differential tests need a C Kissat
4.0.4, which you must build yourself:

```sh
# compare the Lean binary against C Kissat on random instances
KISSAT=/path/to/kissat/build/kissat \
  python3 -I scripts/difftest.py --candidate .lake/build/bin/lkissat \
  --count 500 --opts=--plain --jobs 8

# unit tests: compile Kissat's data structures next to the Lean versions and compare
KISSAT_SRC=/path/to/kissat/src sh test/unit/run.sh
```

`scripts/README.md` describes the generator and tester in detail.

## Acknowledgements

LeanKissat is a translation of Kissat by Armin Biere and contributors, which is distributed
under the MIT license. The algorithms, heuristics and options are Kissat's.

## License

MIT. See `LICENSE`, which also carries Kissat's copyright notices.
