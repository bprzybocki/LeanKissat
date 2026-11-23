import LeanKissat.Core.Assign

/-
Clause creation and deletion (`clause.c`).
-/
namespace LeanKissat
namespace Solver

/-- The counter updates of `inc_clause` (clause.c). -/
def incClauseStats (c : Counters) (original redundant binary : Bool) : Counters :=
  let c := if binary then c.add Counters.idx_clauses_binary 1
    else if redundant then c.add Counters.idx_clauses_redundant 1
    else c.add Counters.idx_clauses_irredundant 1
  let c := c.add Counters.idx_clauses_added 1
  if original then c.add Counters.idx_clauses_original 1 else c

/-- `inc_clause` (clause.c). -/
@[inline] def incClause (s : Solver) (original redundant binary : Bool) : Solver :=
  { s with stats := incClauseStats s.stats original redundant binary }

/-- `dec_clause` (clause.c). -/
def decClause (s : Solver) (redundant binary : Bool) : Solver :=
  if binary then DEC! s clauses_binary
  else if redundant then DEC! s clauses_redundant
  else DEC! s clauses_irredundant

/-- `new_binary_clause` (clause.c). -/
def newBinaryClauseAux (s : Solver) (original watch : Bool) (first second : Lit) : Solver :=
  let s := if watch then s.watchBinary first second else s
  let s := s.markAddedLiteral first
  let s := s.markAddedLiteral second
  s.incClause original false true

/-- `new_large_clause` (clause.c). Returns `INVALID_REF` and sets
  `outOfResources` if the arena is exhausted. -/
def newLargeClause (s : Solver) (original redundant : Bool) (glue : UInt32)
    (lits : U32Vec) : Ref × Solver :=
  -- the arena is returned in both cases so that it stays unique (in-place push)
  let arena := s.arena
  let s := { s with arena := {} }
  match arena.allocate redundant glue lits with
  | (none, arena) => (INVALID_REF, { s with arena := arena, outOfResources := true })
  | (some res, arena) =>
    let s := { s with arena := arena }
    let s := if s.watching then s.watchReference (lits.get! 0) (lits.get! 1) res
      else s.connectClause res
    let s := if redundant then
        if s.firstReducible == INVALID_REF then { s with firstReducible := res } else s
      else
        let s := s.markAddedLiterals lits.toArray
        { s with lastIrredundant := res }
    (res, s.incClause original redundant false)

/-- `new_clause` (clause.c). `kissat_defrag_watches_if_needed` has no observable
  effect (watch lists are separate vectors here) and is omitted. -/
def newClause (s : Solver) (original redundant : Bool) (glue : UInt32) (lits : U32Vec) :
    Ref × Solver :=
  if lits.size == 2 then
    (INVALID_REF, s.newBinaryClauseAux original true (lits.get! 0) (lits.get! 1))
  else s.newLargeClause original redundant glue lits

/-- `kissat_new_binary_clause`. -/
@[inline] def newBinaryClause (s : Solver) (a b : Lit) : Solver :=
  s.newBinaryClauseAux false true a b

/-- `kissat_new_unwatched_binary_clause`. -/
@[inline] def newUnwatchedBinaryClause (s : Solver) (a b : Lit) : Solver :=
  s.newBinaryClauseAux false false a b

/-- `kissat_new_irredundant_clause`: clause in `s.clause`. -/
@[inline] def newIrredundantClause (s : Solver) : Ref × Solver :=
  s.newClause false false 0 s.clause

/-- `kissat_new_redundant_clause`: clause in `s.clause`. -/
@[inline] def newRedundantClause (s : Solver) (glue : UInt32) : Ref × Solver :=
  s.newClause false true glue s.clause

/-- `mark_clause_as_garbage` (clause.c). -/
def markClauseAsGarbage (s : Solver) (ref : Ref) : Solver :=
  let red := s.arena.redundant ref
  let s := if !red then s.markRemovedLiterals (s.arena.lits ref) else s
  let s := s.decClause red false
  -- `ADD (arena_garbage, bytes)` is a METRIC
  { s with arena := s.arena.setGarbage ref true }

/-- `kissat_delete_binary` (clause.c). -/
def deleteBinary (s : Solver) (a b : Lit) : Solver :=
  let s := s.markRemovedLiteral a
  let s := s.markRemovedLiteral b
  s.decClause false true
  -- `INC (clauses_deleted)` is a STATISTIC

end Solver
end LeanKissat
