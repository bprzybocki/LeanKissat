# LeanKissat — Port & Verification Plan (draft)

## Decisions (2026-11-22)
* No Mathlib; Batteries allowed.
* Parser not verified. No DRAT/proof output. No compressed input.
* No runtime model check (Kissat only checks models in debug builds) — SAT direction is
  proven via the extension stack.
* Outer loop termination: real proof, see `TERMINATION.md` (no fuel).
* Benchmarks: download a sample of the SAT Anniversary Track.
* Counters/limits: `UInt64` (faster than `Nat`: unboxed fields, no bignum checks);
  return `unknown` when a scheduling-relevant counter or limit would overflow.
* Floats: Lean 4.36 models `+ - * / sqrt`, comparisons and conversions, but `log10` and
  `floor` are opaque. Float-computed scheduling deltas are clamped with provable integer
  lower bounds that do not change behaviour. No custom IEEE implementation.
* Resource exhaustion (arena capacity, fresh variables) is an explicit result, separate
  from SAT/UNSAT/unknown.

Target: Kissat 4.0.4 (~39K lines C, 206 files) → Lean 4.36.0, no `unsafe`,
no `partial`, no `implemented_by`/`@[extern]`, with soundness proofs against `Std.Sat.CNF`.

## 1. What Kissat is (as relevant to the port)

* Non-incremental (single `kissat_solve`; `internal.c:268` rejects a second solve).
* Core CDCL: 2-watched literals with blocking literals, binary clauses in watch lists,
  single clause arena (`arena.c`, clause header + inline lits, 32-bit references),
  chronological backtracking, 1UIP + minimization + shrinking, OTFS, eager subsumption,
  focused (VMTF queue) / stable (EVSIDS heap, reluctant doubling) mode switching,
  target/best phases, rephasing, restarts with EMA, 3-tier clause reduction, promotion,
  reorder, random decisions, warmup.
* Inprocessing / preprocessing: probing (failed literals), backbone, transitive reduction,
  substitute (equivalent literals via SCC), vivification, sweeping (uses `kitten`, an
  embedded mini-solver), BVE with gate extraction (ands, equivalences, ite, xor,
  definitions via kitten cores), forward subsumption, fastel, bounded variable addition
  (`factor`), clausal congruence closure (`congruence.c`, 4.6K lines), lucky phases,
  local search (`walk`), compacting/defragmentation, extension (witness) stack.
* Frontend: DIMACS parser (strict/relaxed, embedded options, compressed via popen),
  model printing, DRAT proofs (ASCII/binary), `-o` simplified-formula output, options,
  configurations (`basic`, `default`, `plain`, `sat`, `unsat`), limits, statistics.
* Nothing is labelled "experimental" in 4.0.4. Debug-only code (`check.c`, `logging.c`,
  `#if 0` blocks, `METRICS`, `COVERAGE`) is not ported.

## 2. Architecture of the port

* **Pure core, thin IO shell.** The solver is a pure state-transformer over a
  `Solver` structure (used linearly so `Array` updates are in place). IO only in the
  frontend (parsing, printing, proof file writing, time limits).
* **Bit-faithful data layout.** Literals `UInt32` (`2*idx+sign`), the arena as one flat
  `Array UInt32` with the same header layout/alignment as C, watches as packed `UInt32`
  (binary tag bit + lit/ref), same RNG, same `Float` (IEEE double) arithmetic, same
  `ticks` accounting. This makes the Lean solver follow *the same search trajectory* as
  C Kissat, so differential testing can compare not only SAT/UNSAT but
  conflicts/decisions/propagations counts and the model.
  (If `Array UInt32` boxing proves too slow/memory-hungry we switch the arena to a
  `ByteArray`-backed word buffer; decided by benchmark in Phase 1.)
* **Module mirroring.** One Lean file per C translation unit
  (`LeanKissat/Core/Propsearch.lean` ↔ `propsearch.c`, ...), with C function names kept
  in docstrings to make reviewing/diffing easy.
* **Bounds checks.** Hot loops use `a[i]'h` with proofs from structural invariants carried
  in subtypes (e.g. all literals in arena `< 2*vars`); elsewhere `a[i]!` initially and
  hardened later. (`!` is safe Lean — panics are not unsound — but each one is a place
  where the proof of "no panic" is missing; we track their count.)

## 3. Verification strategy

### 3.1 Top-level theorem (sketch)
```lean
theorem solve_sound (F : Std.Sat.CNF Nat) (opts : Options) :
  match solve opts F with
  | .sat m   => F.Sat m.toAssignment
  | .unsat   => F.Unsat
  | .unknown => True
```
The DIMACS parser is outside the trusted statement (theorem is about the parsed `CNF`);
we may additionally prove `parse ∘ print = id`-style lemmas later.

### 3.2 Invariant
Abstract state = (current clause set `D` over internal vars, extension stack `E`,
variable map internal↔external, units/trail). Invariant **INV**:
1. *Forward (UNSAT direction):* `Sat F → Sat (D ∪ units)` (over possibly more variables
   because BVA/`factor` introduces fresh variables).
2. *Backward (SAT direction):* for every `σ ⊨ D`, `extend E σ ⊨ F` (restricted to
   external vars).
Every solver step is shown to be one of a small set of abstract rules, proven once:
* add a clause entailed by `D` (learned clauses, strengthened/vivified clauses,
  resolvents, probing units, substitution) — proved via resolution/RUP lemmas;
* delete a clause (redundant: trivially fine for (1); for irredundant deletions, push
  witness onto `E` — BVE, blocked/covered style, sweeping, congruence equivalences);
* add a definition over a fresh variable (BVA) — satisfiability-preserving extension;
* rename variables (compaction) — via `Std.Sat.CNF.relabel` lemmas.
This mirrors the DRAT/"witness" semantics Kissat already uses for its proofs, so each
technique's soundness reduces to: "this step is a valid DRAT-with-witness step".

### 3.3 Termination
* All inner loops (propagation, analysis, minimization DFS with depth bound, heap ops,
  sorting, gate extraction, kitten, walk, etc.) get real termination measures
  (`termination_by`/`decreasing_by`), often from Kissat's own effort/ticks limits.
* The **outer CDCL loop** is proven terminating with the lexicographic measure in
  `TERMINATION.md` (no fuel). Requires `Nat` counters and integer-clamped Float deltas.

## 4. Testing & performance

* Build reference Kissat 4.0.4 (`./configure && make`) — plus a variant with
  the same options defaults — for differential testing.
* **Differential fuzzing:** random CNF generators (uniform k-SAT near threshold,
  structured generators, `cnfuzz`-style), compare result, model validity, and the
  `--statistics` counters (conflicts, decisions, propagations, per-technique counts).
  Each phase is tested with C Kissat run with *unported techniques disabled by option*
  (`--no-sweep`, `--no-congruence`, ...), so trajectories are comparable at every phase.
* DRAT output checked with `drat-trim` as an extra test.
* **Performance:** sample (e.g. 50–100) instances from the SAT Anniversary Track,
  fixed timeout, compare PAR-2 and time ratio vs C Kissat; profile Lean hot paths
  (propagation, analysis) early, since they dominate.

## 5. Phases (each ends with: builds, proofs complete, diff-tests green, benchmark run)

0. **Infrastructure**: project, reference C build, fuzzers, test harness, benchmark
   sampler. Core data structures: literals, arena, watches, vectors, heap, queue,
   options/configurations, RNG, statistics/limits.
1. **Plain CDCL** (`--basic`, then `--plain`): parse, propagate, decide, analyze,
   minimize/shrink, backtrack (incl. chrono), restarts, reduce, rephase, mode switching,
   VSIDS/VMTF, phases, model extraction. Full soundness + termination proof for this
   core. *This phase establishes the proof framework (INV, abstract rules).*
2. **Default search features**: OTFS, eager subsumption, tiers/promotion, bump reasons,
   jump reasons, reorder, random decisions, warmup, lucky, collect/compact/defrag.
3. **Simplifiers I**: probing, backbone, transitive reduction, substitute, vivify,
   forward subsumption, strengthen.
4. **Simplifiers II**: BVE + gate extraction (ands/equivalences/ite/xor), extension
   stack, fastel, preprocessing schedule.
5. **Kitten + its clients**: kitten, definitions, sweeping.
6. **BVA (`factor`) and congruence closure** (largest, most intricate parts).
7. **Walk, proofs (DRAT ASCII/binary), `-o` output, remaining frontend options**,
   performance tuning, final benchmark report.

## 6. Known risks
* Proof effort dominates (est. several times the code size in proof lines);
  congruence/factor/sweep are the hardest.
* Performance of Lean `Array` updates relies on uniqueness; any accidental sharing in a
  hot loop causes O(n) copies — guarded by benchmarking every phase.
* Bit-faithfulness may be broken where C behaviour depends on `sizeof`, pointer
  arithmetic, or undefined behaviour; each such spot is documented.
* Kissat bugs that block proofs will be reported to you before any deviation.
