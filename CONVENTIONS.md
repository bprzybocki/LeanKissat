# Porting conventions (Kissat 4.0.4 → Lean 4.36)

Reference C sources: `src/` of Kissat 4.0.4 (https://github.com/arminbiere/kissat, tag `rel-4.0.4`). Target = default release build
(`./configure && make`: `-DNDEBUG`, no `LOGGING`, not `QUIET`, no `EMBEDDED`,
no `STATISTICS`/`METRICS`). Code under `#ifndef NDEBUG`, `LOGGING`, `METRICS`,
`COVERAGE`, `#if 0`, proof (`proof.c`) and checker (`check.c`) is not ported.
Reporting/verbose printing is ported only where needed for user-visible output
(`-q`, `-v`, `--statistics`, banner may be simplified).

## Hard rules
* No `partial`, `unsafe`, `implemented_by`, `@[extern]`, `opaque` definitions with
  runtime behaviour, `sorry` in committed code (except clearly marked proof TODOs in
  `Proofs/`, never in executable defs), no `IO.Ref`-based mutation in the core.
* Termination: structural recursion or `termination_by` with an explicit measure.
  Loops over arrays: `for` over ranges / `Nat.fold` / well-founded recursion on
  `size - i`. Never use `while true` style loops without a measure.
* Dependencies: Lean core + `Std` + `Batteries` only (no Mathlib).

## Faithfulness
* The port must follow the *same search trajectory* as C Kissat: same order of
  operations, same tie-breaking, same RNG, same `double` arithmetic (Lean `Float` is
  IEEE binary64; use the same operation order as C to get identical rounding),
  same `ticks` accounting, same arena layout and reference values.
* C `unsigned` → `UInt32`, `uint64_t` → `UInt64`, `int` → `Int32` only when negative
  values matter, otherwise `UInt32`/`Nat` as documented. `size_t` → `Nat` or `UInt64`.
  Keep C's wrap-around semantics only where C relies on it; otherwise counters that
  could overflow must be checked (see below).
* Scheduling counters / limits (`statistics.*`, `limits.*`) are `UInt64`. If one would
  overflow, the solver stops with `unknown` (C behaviour there is undefined/wrapping).
* Float-computed scheduling deltas (`log10`, `sqrt`, ...) are computed exactly as in C,
  then clamped from below by a provable integer bound that never changes the value in
  practice (see `TERMINATION.md`). Comment each clamp with `-- CLAMP:`.
* Every deviation from C behaviour gets a `-- DEVIATION:` comment explaining why.
* Each Lean function that ports a C function names it in its docstring:
  `/-- Port of `kissat_bump_analyzed` (bump.c). -/`.

## Representation
* Literals: `UInt32`, `lit = 2*idx + sign`, `NOT lit = lit ^^^ 1`, `IDX lit = lit >>> 1`
  (`Core/Basic.lean`). `INVALID_LIT = UInt32.max`.
* Packed `UInt32` stacks: `U32Vec` (`Util/U32Vec.lean`, ByteArray-backed, ~2x faster
  than `Array UInt32`). Per-literal/per-variable byte data (values, marks, phases, flags):
  `ByteArray` (signed C `char` stored as `UInt8` two's complement).
  `double` arrays: `FloatArray`.
* Solver state is a single structure `Solver` updated functionally:
  write `def f (s : Solver) : Solver` / `Solver → α × Solver`, update with
  `{ s with field := s.field.set! i v }` (compiles to in-place update when `s` is
  unique — verified in `bench/StructBench.lean`). Never keep an old copy of `s` alive
  while updating it (this silently makes updates O(n)). Nested arrays (`Array U32Vec`
  for watches) are updated with `Array.modify`.
* Arena: one `U32Vec` of 32-bit words; a clause reference `ref` (C: index in 16-byte
  `ward`s) points at word `4*ref`. Header = 3 words (flags+glue+used, searched, size),
  then literals, padded to a multiple of 4 words, exactly like C (`Core/Clause.lean`).
* Watches: one `U32Vec` per literal with C's encoding (`binary` bit 31;
  large watch = blocking-literal word followed by reference word).

## Code style
Follow the Lean standard library guides: [style](https://github.com/leanprover/lean4/blob/master/doc/std/style.md)
and [naming](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md).
For example: `fun x =>` (not `↦`/`λ`), `snake_case` theorem names built from the statement
(`C_of_A_of_B`, `_iff`), `?`/`!` suffixes for `Option`/panicking variants, no `erw`,
squeezed non-terminal `simp`. Exceptions and additions for this project:

* **Names that mirror C.** Constants and macros keep their C spelling (`IDX`, `NOT`, `LIT`,
  `MAX_GLUE`, `INVALID_REF`). Option and statistics fields keep Kissat's names exactly
  (`eagersubsume`, `restartreusetrail`), because they are matched against command-line
  strings and `--statistics` output. Ported C functions use the lowerCamelCase form of the C
  name (`mark_fixed_literal` → `markFixedLiteral`). Local variables follow the C code
  (`s` for the solver, `lit`, `ref`, `idx`, `level`).
* **`unfold` and `simp only` on the solver.** The guide prefers `simp`/`rw` over `unfold`.
  Here, `unfold` is the normal way to open one step of a large or recursive definition, and
  goals mentioning `Solver` (≈90 fields) use `simp only`/`dsimp only`: a full `simp` or
  `simp_all` there is slow and unstable. Terminal `simp` elsewhere is fine.
* **Linters:** besides Lean's default linters, `lakefile.lean` enables
  `linter.extra.unreachableTactic`, `linter.extra.unnecessarySeqFocus` and
  `linter.extra.dupNamespace`. The build must produce no warnings.

## Proof style
* Executable code lives in `LeanKissat/<Area>/*.lean`; specifications and proofs in
  `LeanKissat/Proofs/...` (or next to the code for small lemmas).
* Prefer stating invariants as separate predicates on `Solver` over subtypes in hot
  data structures. Use `a[i]!` in code where a bounds proof would be invasive; record
  the needed invariant in the proof layer.

## Performance rules (learned the hard way; see git history of Search/Propagate.lean)
* The `Solver` record has ~50 fields. A structure update `{ s with … }` is in place
  only if the compiler can reuse `s`. Reuse is lost (the whole record is rebuilt:
  50 field copies + allocation + freeing) when the code between reading fields of
  `s` and building the new record contains a *branch*: an `if`/`match`, or an inlined
  helper that branches (e.g. `U32Vec.push`, any `{ v with … }` on a nested
  structure). Rules:
  - Do branching on scalars before the update, or write it branch-free
    (`Bool.toUInt32`, masks), or move it into a `@[noinline]` helper.
  - Mark helpers that update nested structures `@[noinline]` when they are used
    inside updates of `Solver`.
  - Check with: `grep -c "lean_alloc_ctor(0, 4[0-9]\|lean_alloc_ctor(0, 5[0-9]"
    .lake/build/ir/LeanKissat/<Module>.c` (should be 0 outside `reuseFailAlloc`).
* Hot loops: thread the needed parts of the state as separate parameters (take them
  out of `s` first: `let a := s.asg; let s := { s with asg := {} }`), and put them
  back once at the end. Return a single structure from a loop, not nested tuples.
* Never keep a reference to an array that is about to be updated (e.g. in an error
  branch, or `let x := s.f` followed by `{ s with f := s.f.push … }` while `x` is
  live): this silently copies the whole array.
* Statistics: use the `INC!`/`ADD!` macros (packed `Counters`), never a record.
* Profile with `scripts/profile.sh <cnf> <options>` (macOS `sample`).
