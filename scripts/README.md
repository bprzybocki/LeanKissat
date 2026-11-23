# Test scripts

All scripts are Python 3 standard library only and are meant to be run as
`python3 -I scripts/<name>.py ...` (they add their own directory to
`sys.path`, so `-I` is fine). Paths default to the reference binary
`../kissat/build/kissat` (relative to `LeanKissat/`).

## cnfgen.py: random CNF generator

```sh
python3 -I scripts/cnfgen.py --list                     # list families
python3 -I scripts/cnfgen.py threshold3 --seed 7 --size 4 > f.cnf
python3 -I scripts/cnfgen.py ksat --seed 1 vars=80 ratio=4.1 k=3 kmin=2 kmax=6
python3 -I scripts/cnfgen.py mix --seed 42               # family chosen from seed
```

The output is fully determined by (family, seed, size, params) and does not
depend on `PYTHONHASHSEED` or the platform. `--size` (default 3) scales every
family. Sizes up to about 8 are solved in well under a second. Families:

| family | description |
|---|---|
| `ksat` | uniform random k-SAT (`vars`, `clauses` or `ratio`, `k`, `kmin`/`kmax`) |
| `threshold3` | 3-SAT at ratio 4.26 ± 0.1 |
| `mixedsat` | clause lengths 2..7 near the threshold |
| `planted` | 3-SAT with a planted solution, so always SAT |
| `php` | pigeonhole (UNSAT, or SAT with n pigeons) |
| `parity` | random XOR constraints, Tseitin-chained |
| `xorchain` | the same XOR encoded twice with conflicting parity (Urquhart-like; hardest family) |
| `circuit` | random AND/OR/XOR/ITE Tseitin circuits with random output units |
| `miter` | a circuit against an identical copy or a re-encoded equivalent copy (congruence/sweep target) |
| `coloring` | random graph 3/4-coloring |
| `equiv` | equivalence chains plus random clauses (substitution target) |
| `bin` | mostly binary clauses (probing, transitive reduction, SCC) |
| `amo` | exactly-one groups with pairwise AMO (factorization target) |
| `weird` | duplicate literals, tautologies, duplicate clauses, units, empty clause, unused variables |
| `cnfuzz` | layered random instances in the style of cnfuzz |

Module use: `cnfgen.generate(family, seed, size, **params).dimacs()`.

## difftest.py: differential testing (reference vs candidate)

```sh
# self test: reference against itself
python3 -I scripts/difftest.py --count 200 --jobs 8

# the Lean port against C kissat, several option sets
python3 -I scripts/difftest.py --candidate .lake/build/bin/leankissat \
    --count 500 --seed 1 --family mix --size 1-8 \
    --opts= --opts=--plain --opts=--sat --opts=--unsat --opts=--no-simplify

# given files or directories
python3 -I scripts/difftest.py --candidate ... --files ../kissat/test/cnf --opts=--basic

# minimize failures
python3 -I scripts/difftest.py --candidate ... --count 100 --minimize --max-failures 3
```

* Option sets: `--opts=STRING` can be repeated, and every instance runs once
  per set. Use the `=` form (`--opts=--plain`) because argparse rejects a
  separate value that starts with `-`. `--opts=` is the default
  configuration. `--statistics` is always added unless you pass `--no-stats`.
* `--reference` and `--candidate` are shell-split commands, so
  `--candidate "python3 -I wrapper.py --flag"` works. The candidate defaults
  to the reference.
* Checks, in order:
  1. Crash or timeout (exit code must be 0, 10 or 20).
  2. Malformed output (several `s` lines, or the exit code does not match the `s` line).
  3. SAT witness validity, using its own checker. The `v` lines must end with `v 0`.
  4. Exit code and status agree between the two solvers.
  5. Statistics. The counters in `--counters` (default `conflicts,decisions,propagations,restarts,reductions`) must be equal and present in both outputs. Every other counter that both outputs print must also be equal, unless you pass `--only-listed` or name it in `--ignore a,b`. The `glue usage` section is compared too, as pseudo-counters `glue_focused_N`/`glue_stable_N`.
  6. Optional: `--compare-report` also compares the progress report lines with the time and MB columns removed.
* Statistics parsing: only lines inside the `[ statistics ]` section of the
  form `c name: <number> ...` count. The first number is the counter value,
  and the per-second or percentage values after it are ignored. The
  `[ resources ]` section (memory, process-time) is never parsed, and names
  matching `time|second|resident|memory|MB|bytes` are excluded.
* Failure kinds: `crash`, `timeout`, `bad-output`, `bad-witness`,
  `status-mismatch`, `stats-mismatch`, `report-mismatch`, and `ref-*` (the
  reference itself failed). An instance where both solvers time out counts
  as `skip`, not as a failure.
* Failures go to `test/failures/<instance>-o<optset>-<kind>/` as
  `input.cnf`, `ref.out`, `cand.out` and `info.json` (options, argv,
  message, mismatching counters). `--minimize` adds `minimized.cnf`. It
  removes clauses ddmin-style, then single literals, then compacts variable
  indices, and keeps each step only if the failure kind stays the same.
  Limits are `--minimize-runs` (3000) and `--minimize-time` (300 s) per
  failure.
* Other flags: `--timeout` per run (20 s; a candidate timeout counts as `skip` if the reference itself needed more than `--timeout-slack` (0.5) of it), `--jobs`, `--size lo-hi`
  (per-instance size, derived from the seed), `--family a,b,c`
  (round-robin) or `mix`, `--no-model-check`, `--no-save`, `-v`.
* Exit status: 0 if no failures, 1 otherwise.

`scripts/testing/fake_candidate.py --fake=MODE` wraps the reference and
breaks its output on purpose: `flip`, `model`, `stats`, `crash` or `hang`.
Use it to check the checker and the minimizer:

```sh
python3 -I scripts/difftest.py --count 12 --minimize --max-failures 2 \
    --candidate "python3 -I scripts/testing/fake_candidate.py --fake=crash"
```

## bench.py: benchmark runs and comparison

```sh
python3 -I scripts/bench.py run --dir ../benchmarks/anni --timeout 300 --jobs 4 --out ref.csv
python3 -I scripts/bench.py run --solver .lake/build/bin/leankissat --options=--sat \
    --dir ../benchmarks/anni --timeout 300 --out lean.csv --resume
python3 -I scripts/bench.py compare ref.csv lean.csv [--all] [--top 20]
```

`run` writes one CSV row per file with these columns: `file`, `status`
(SAT, UNSAT, UNKNOWN, TIMEOUT, CRASH, ERROR, or WRONG for an invalid
witness), `exit`, `time` (wall seconds), `conflicts`, `decisions`,
`propagations`, `timeout` and `options`. It passes `--statistics` and `-n`.
`--check` validates witnesses instead of passing `-n`. `.gz`, `.xz` and
`.bz2` inputs work. `--resume` appends to an existing CSV and skips files
it already contains.

`compare` prints:

* SAT/UNSAT disagreements and WRONG/CRASH/ERROR rows at the top, marked with `!!!`. The exit status is then 3.
* Solved counts and PAR-2. The timeout is read from the CSV, or set with `--timeout`.
* Instances solved by only one side.
* The geometric mean, minimum and maximum of the per-instance time ratio.
* How many instances have identical conflict counts.
* The largest slowdowns.
