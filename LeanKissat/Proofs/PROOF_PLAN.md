# Proof plan (Phase 1: `--plain` core, then extended per technique)

Top-level statements (`Proofs/Spec.lean`):
* `solveCNF_sat   : (solveCNF o F).1 = 10 → F.Sat (modelOf (solveCNF o F).2)`
* `solveCNF_unsat : (solveCNF o F).1 = 20 → F.Unsat`
for all options, assuming `CNF.ValidVars F`.

## Semantic view of a solver state
* `DB s`: literals of all non-garbage arena clauses (arena layout = chain of
  `nextClause` from 0) plus all binary watches; `IrrDB s` the irredundant part
  (all binaries are irredundant in Kissat 4).
* Assignment: `values`, levels `aLevel`, trail positions `aTrail`, frames.
* `pushLevel s p`: the decision level current when trail position `p` was pushed
  (`max L` with `frame[L].trail ≤ p`).
* `ext s`: internal ↔ external literal maps (`importLit`, `exportMap`).

## Invariants
1. **WF** (structural): array sizes, literal ranges, trail/positions/levels/frames
   consistent, arena layout valid, each non-garbage large clause watched exactly
   by `lits[0]` and `lits[1]` (or pending in `delayed`), blocking literals belong
   to the clause, `level(l) ≤ pushLevel(pos l)`, root assignments never undone.
2. **Implied** (UNSAT direction): every clause of `DB s` and every root-true literal
   is implied by `F` (after `ext`). Reason invariant: the reason of every trail
   literal contains it, its other literals are false with smaller trail position
   and level ≤ its level.
3. **Covered** (SAT direction): every clause of `F` is a tautology, or has a
   root-true literal, or is a superset (modulo root-false literals) of a clause of
   `IrrDB s`.
4. **Watch invariant** (SAT direction only). For every non-garbage clause `C` with
   watches `w0 = lits[0]`, `w1 = lits[1]`: if *both* are false and both negations
   are at propagated trail positions `q0, q1 < propagate`, then `C` contains a true
   literal `t` with `level t ≤ max (pushLevel q0) (pushLevel q1)`. Binary clauses: the
   same with "both false and propagated" impossible. Exceptions: the current conflict
   clause and unvisited watches of the literal being propagated when a conflict is
   found (repaired by the subsequent backtrack, since every trail position
   `≥ frame[newLevel+1].trail` is re-propagated).
   Note: the stronger per-watch version (`¬w` propagated ⇒ witness with
   `level ≤ pushLevel`) is *not* preserved by Kissat: `rewatch_clauses` during
   `reduce` at decision level > 0 may watch a true literal of high level together
   with a false literal pushed earlier at a lower level. This only loses unit
   propagations (completeness), never a conflict, and the weaker invariant above is
   preserved and suffices for SAT soundness.

## Consequences
* SAT: when `unassigned = 0`, `propagate = trail.size` and no conflict, invariant 4
  implies every `DB` clause is satisfied (both watches false ⇒ witness true);
  with 3 every input clause is satisfied.
* UNSAT: `inconsistent` is only set on a conflict at level 0 (or an empty clause);
  all literals of the conflict clause are root-false, hence implied false; with 2,
  `F ⊨ ⊥`.
* Learned clauses: the clause produced by analysis (+ minimize / shrink / OTFS) is
  the negation of a cut of the implication graph: every literal of the conflict is
  derivable by reasons from the cut ⇒ implied (`Proofs/Analyze`).

## Termination
* Inner loops: structural / `termination_by`; FUEL bounds discharged by WF.
* Search loop: conflicts are bounded (`UInt64` overflow stop), between conflicts the
  measure (unassigned, remaining scheduled procedures per conflict count) decreases
  (see `TERMINATION.md`, §1).

## Layers / files
* `Proofs/Vec.lean`: get!/set!/push lemmas for `U32Vec`, `WVec`.
* `Proofs/Abstract/*.lean`: invariants 2–4 on an abstract list-based model of the
  trail / watches / clauses and the exact Kissat steps (propagate, backtrack,
  learn, reduce, restart). This is where a Kissat bug blocking the proof would show.
* `Proofs/Refine/*.lean`: the concrete functions refine the abstract steps.

## Status (2026-11-23)
Proven (no `sorry`):
* `PropSpec`: `propLoop` ↔ list spec `PS.run`.
* `PropSem`/`PropStep`: one propagation round preserves Core, the arena relation (clause
  permutations), the watch invariant; visit conditions; conflicts are all-false DB clauses.
* `PropWatch`: watch-list structure (`WSA`) across a round (replacement, delayed watches).
* `Justify`/`PropJust`: reasons (`ReasonOK`), root implications (`RootImplied`), value range,
  `unassigned` counter, trail nodup (`ReasonSizes`) across a round (`--plain`: jumpreasons=0).
* `PropLit`: `propagateLiteral_spec` (concrete code, watch flushing, delayed watches).
* `SearchProp`: `SInv`, `searchPropagateLoop_spec`, `searchPropagate_spec` (flush at root,
  conflict bookkeeping; `inconsistent` set on root conflicts).
* `Backtrack`: `backtrack_spec` (trail compaction, unassignment counter, watch invariant at the
  new propagation pointer, reasons keep trail order).
* `Derive`: `DerFalse` (literals derivable from a clause by reasons) ⇒ the clause is implied.
* `ArenaSame`/`AnaFrame`/`AnaBits`: analysis bookkeeping frame (`AF`), header-bit writes.
* `Deduce`: `deduceFirstUip_spec` (first-UIP clause; every conflict literal is derivable).
Code changes for provability (behavior-preserving, difftested): recursive helpers for the
deduction loops (`analyzeReasonLits`, `analyzeConflictLits`, `resolveReason`), fuel exhaustion in
`deduceLoop`/`analyzeLoop` sets `overflowed` (unknown) instead of returning garbage/UNSAT,
checked assertion "a resolved literal's reason is not a decision".
* `Minimize`/`Shrink`/`SortSpec`/`Analysis`: sorting, minimization (`minimizeClause`, all
  `shrink` values) and shrinking keep the `removable` marks justified (`Good`); every deduced
  literal is derivable from the final clause (`minimizeDeduced_spec`), whose literals are false
  with positive level; every set analysis bit is on its stack (`Listed`).
Code changes for provability (behavior-preserving, difftested `--plain`, `--basic`,
`--shrink=0..2`, `--minimize=0`): recursive `minimizeDown`, `sortWrite` (sorting split into
`sortStarts`/`sortWrite`/`sortRestore`), `U32Vec.replicate` via `pushN`, functional
`analyzeStep` (`minimizeDeduced`, `learnDeduced`, `finishAnalysis`; flagged states skip learning).
* Learning (done, `learnClause_spec` in `LearnRef`, eagersubsume = 0): `AssignSInv` (`assign_sinv`: assignments outside propagation),
  `BacktrackConflict` (`backtrackAfterConflict_spec`), `LearnSpec` (`learnedClauseOK_spec`),
  `Allocate` (`allocate_layout`: arena append keeps the layout), `WatchAdd` (watch-list pushes,
  `watchBinary_ws`, `allocWatch_ws`), `LearnAdd` (`sinv_extend`, `newLargeClause_spec`).
  Code changes: `learnReference` backtracks before allocating (disjoint state); checked
  assertions after backtracking (UIP unassigned, others false, no duplicate literal via marks,
  new level below the current one); `assignmentLevel` uses the recursive `asgAssignmentLevel`;
  `Arena.allocate` uses `appendFrom`/`pushN`; `incClause` via `incClauseStats`.
  Further refactors: `selectJump`, functional `learnReference`, `learnPrefix` (unit/binary),
  `markAddedFlags`, eager-subsumption flag read before learning.
* `Unwatch`/`ConflictLevel`: watch-list removal, watch re-ordering (`moveWatch_ws`, `MoveRel`),
  `oneLiteralOnConflictLevel_spec` (root conflict ⇒ UNSAT; forced literal; otherwise the analysis
  precondition `APost` on the conflict level). `FailedLit`: `analyzeFailedLiteral_spec` (all
  learned units implied: UIP units via the walk invariant `FInv`, `¬failed` via the checked
  assertion that `failed` is the only level-1 decision).
  Refactors: recursive `conflictLevelLoop`/`highestLoop`/`moveHighest`, `failedInit`/
  `prevAnalyzed`/`failedLarge`/`failedResolve`/`failedStep`/`failedWalk`/`learnUnits`.
  Checked assertions: first watch on the conflict level after re-ordering; forced literal
  unassigned and others false after backtracking; failed-literal walk: analyzed literal found,
  no decision resolved, binary reason literal not on the root level, `failed` the only level-1
  decision, units unassigned before assigning.
* `AnalyzeSpec`: `analyze_spec` (`--plain`: otfs = eagersubsume = bumpreasons = 0): result 20 ⇒
  UNSAT; result 0 ⇒ flagged, or `SInv`, watch invariant, clean analysis bits, empty clause.
  Refactors: field-only bump updates (`bumpVarPair`, `moveAnalyzedToFront` fold), resets via
  `clearBitsUp`, `zeroUsed`, `analyzeReasonSideLiteralsCore`, `updateAnalysisAverages`;
  `AF` now also fixes `watching`/`probing`.
* Search level (2026-11-23): `SearchInv`, `IrrMono` (irredundant database and root literals only
  grow, up to subsumption; threaded through the analysis chain), `decide_spec`, `restart_spec`,
  `searchStep_spec`, `searchLoop_spec`, `lucky_spec`, `kissatSearch_spec` (`Decide`, `SearchStep`,
  `Lucky`, `SearchTop`). Import: `init_reserve_spec`, literal phase `LitPhase`, `addClauseBody_spec`,
  `addClauseEnd_spec`, `importAll` (`Import`, `ImportAdd`). Final: `solveCNF_unsat`, `solveCNF_sat`
  (`Final`, `Main`) under `PlainConfig` and the hypothesis `ReduceOK (PhiF F) Solver.reduce`.
  `solveCNF` now reserves `maxVar F` variables (as the binary after the header).
  Refactors (difftested): decide (`decideStart`/`decideOn`/`randomDraw`/`randomStart`), lucky
  (`luckyAssume`/`luckyFlip`/`luckyFailed`/`luckySatLoop`/`luckyAssignLoop`/`luckySatPhases`),
  `initLimits` (`initLimitWith`), `startSearch` pipeline, functional `search`, `addClauseBody`/
  `addTail`/`clearClauseMarks`, `reserveImport`/`reserveActivate`, `growBytes`/`growU32`,
  `activateCore`, `markFlagBit`, `U32Vec.toArray` via `Array.ofFn`.
  Checked assertions added: lucky (decision preconditions, root-conflict `inconsistent`, complete
  assignment before `SAT`), flagged states end lucky / clause addition.
* Reduce (2026-11-23, done): `reduce_ok : ReduceOK Φ Solver.reduce` (`RedMain`), so
  `solveCNF_unsat_sound`/`solveCNF_sat_sound` (`Soundness`) hold under `PlainConfig` and
  `CNF.ValidVars F` alone. Files: `RadixMem` (radix sort keeps its elements), `RedFlush`
  (`flushAll_spec`), `RedArena` (arena segments `LayoutTo`), `RedSweepLits`/`RedSweep` (the sparse
  sweep: `sweepClause_spec`, `sweep_spec`, output `SwOut`), `RedSort` (`sortLiterals_spec`),
  `RedRewatch` (`rewatch_spec`), `RedCollect` (`sparseCollect_spec`, `CollOut.final`: `SInv`, watch
  invariant, `IrrMono`), `RedPre` (reason marking, candidates, garbage marking: `RF`/`RFN`/`GSame`),
  `RedMain` (flush or mark reasons, checks, assembly).
  Refactors (difftested `--plain`/`--basic`): recursive flush/sweep/move/rewatch/mark loops
  (`flushLoop`, `sweepLits`/`SweepLits.keep`, `sweepClause`/`sweepBinary`/`sweepLarge`,
  `sweepLoop`, `moveIrrLoop`/`moveRedLoop`, `rewatchClause`, `markReasonLoop`, `skipIrredundant`,
  `collectLoop`/`collectFrom`, `markGarbageLoop`, `moveSmallestLoop`), `rootF`/`rootT`.
  Design deviation (not observable): `flushLoop` keeps the large watches of clauses before
  `start` also for root-fixed literals (C drops them). After flushing the trail no root-level
  literal is propagated again, so these lists are never visited; keeping them keeps every live
  clause watched twice (`WatchStruct.live` unchanged).
  Checked conditions (`notPorted`, unknown; never fail in reachable states): `first_reducible` is a
  clause reference (`Arena.reaches`); unused watch lists (literals ≥ 2·vars) are empty;
  `mark_reason_clauses` sees no level-0 trail literal (C assert); propagation after backtracking
  has no conflict (C assert); `update_large_reason` moves the reason of the forced literal from the
  old position, `forced`/`other` valid, not binary (C asserts, strengthened); swept clauses have
  more than one literal (C assert); garbage candidates are redundant, non-reason and at or after
  `start`; `move_redundant_clauses_to_the_end` is replaced by a stop in the non-compacting collector
  (irredundant clauses after redundant ones only come from unported procedures).

### Findings (not bugs, implicit invariants made explicit)
* `shrink_along_binary` (shrink.c) ignores a failing `shrink_literal` on the binary reason
  literal. This is sound only because a binary reason literal always has the same level as
  the implied literal (binary propagation and `kissat_assign_binary` use the level of the other
  literal). The port fails the shrink explicitly in that (unreachable) case.
* Further checked assertions added (unreachable in practice, difftested): the sorted deduced
  clause contains every deduced literal and every position of it was written; the shrinkable
  stack is empty when a block is shrunk (`minimize_and_shrink_block`); every shrink block literal becomes shrinkable and its
  recorded trail position (`assigned[idx].trail`) is correct and ≤ `max_trail`; shrinking and
  resolution never resolve a decision.
* `Proofs/Minimize.lean`: `minimize_all` (the minimization recursion keeps `removable` marks
  justified).
