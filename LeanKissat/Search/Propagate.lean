import LeanKissat.Core.NewClause

/-
Unit propagation: `proplit.h` instantiated as in `propsearch.c` (and parameterized
for the probing / beyond-conflict variants), `kissat_update_conflicts_and_trail`.
-/
namespace LeanKissat
namespace Solver

/-- Search for a replacement literal in `lits[i..stop)` that is not false
  (`value >= 0`). Returns its position, or `stop` if there is none. -/
def findReplacement (arena : Arena) (values : ByteArray) (ref : Ref) (i stop : Nat) : Nat :=
  if h : i < stop then
    let r := arena.lit ref i
    if !vFalse (values.get! r.toNat) then i
    else findReplacement arena values ref (i + 1) stop
  else stop
termination_by stop - i

/-- `kissat_watch_large_delayed` (proplit.h) on the watch array. -/
def watchLargeDelayedLoop (d : U32Vec) (wss : Array WVec) (k : Nat) : Array WVec :=
  if h : k + 2 < d.size then
    let lit := d.get! k
    let w := d.get! (k + 1)
    let ref := d.get! (k + 2)
    let wss := wss.modify lit.toNat (fun ws => (ws.push (blockingWatch (watchLit w))).push (largeWatch ref))
    watchLargeDelayedLoop d wss (k + 3)
  else wss
termination_by d.size - k

def watchLargeDelayed (s : Solver) : Solver :=
  let d := s.delayed
  let wss := s.watches
  let s := { s with delayed := .empty, watches := #[] }
  let wss := watchLargeDelayedLoop d wss 0
  { s with delayed := d.clear, watches := wss }

/-- Result of the watch loop (a single structure, allocated once per literal). -/
structure PropResult where
  ws : WVec
  p : Nat
  q : Nat
  a : Asg
  arena : Arena
  delayed : U32Vec
  s : Solver
  ticks : UInt64
  res : Option CRef

/-- The main watch-list loop of `PROPAGATE_LITERAL` (proplit.h).
  `ws` is the watch list of `notLit`, taken out of `s.watches`; `p` is the read and
  `q` the write position. The assignment record `a`, the `arena` and the `delayed`
  stack are taken out of `s` and threaded as parameters, so that no large structure
  is rebuilt per iteration. `jump` is `GET_OPTION (jumpreasons) && bigbig`. -/
def propLoop (ignore : Option Ref) (beyond probing jump : Bool) (level : UInt32)
    (notLit : Lit) (ws : WVec) (p q : Nat) (a : Asg) (arena : Arena) (delayed : U32Vec)
    (s : Solver) (ticks : UInt64) (res : Option CRef) : PropResult :=
  if hp : p < ws.size then
    if res.isSome && !beyond then ⟨ws, p, q, a, arena, delayed, s, ticks, res⟩ else
    let head := ws[p]
    let blocking := watchLit head
    let blockingValue := a.values.get! blocking.toNat
    if watchIsBinary head then
      let ws := ws.set! q head
      if vTrue blockingValue then
        propLoop ignore beyond probing jump level notLit ws (p + 1) (q + 1) a arena delayed s ticks res
      else if vFalse blockingValue then
        let s := { s with conflictLit0 := notLit, conflictLit1 := blocking }
        propLoop ignore beyond probing jump level notLit ws (p + 1) (q + 1) a arena delayed s ticks
          (some .binConflict)
      else
        -- `kissat_fast_binary_assign` (fastassign.h)
        let oidx := IDX notLit
        let reason :=
          if jump && level != 0 && (a.aBits.get! oidx.toNat &&& ABits.binary) != 0 then
            a.aReason.get! oidx.toNat
          else notLit
        let s := if level == 0 then s.markFixedLiteral blocking else s
        let a := a.assign probing level true blocking reason
        propLoop ignore beyond probing jump level notLit ws (p + 1) (q + 1) a arena delayed s
          (ticks + 1) res
    else
      let tail := ws.get! (p + 1)
      let ws := (ws.set! q head).set! (q + 1) tail
      let q := q + 2
      if vTrue blockingValue then
        propLoop ignore beyond probing jump level notLit ws (p + 2) q a arena delayed s ticks res
      else
      let ref := watchRef tail
      let ticks := ticks + 1
      if arena.garbage ref then
        propLoop ignore beyond probing jump level notLit ws (p + 2) (q - 2) a arena delayed s ticks res
      else
      let other := arena.lit ref 0 ^^^ arena.lit ref 1 ^^^ notLit
      let otherValue := a.values.get! other.toNat
      if vTrue otherValue then
        let ws := ws.set! (q - 2) (blockingWatch other)
        propLoop ignore beyond probing jump level notLit ws (p + 2) q a arena delayed s ticks res
      else
      let size := (arena.size ref).toNat
      let searched := (arena.searched ref).toNat
      let r := findReplacement arena a.values ref searched size
      let r := if r < size then r else
        let r' := findReplacement arena a.values ref 2 searched
        if r' < searched then r' else size
      if r < size then
        let replacement := arena.lit ref r
        let arena := (((arena.setSearched ref (UInt32.ofNat r)).setLit ref 0 other).setLit
            ref 1 replacement).setLit ref r notLit
        let delayed := ((delayed.push replacement).push (blockingWatch other)).push ref
        propLoop ignore beyond probing jump level notLit ws (p + 2) (q - 2) a arena delayed s
          (ticks + 1) res
      else if ignore == some ref then
        propLoop ignore beyond probing jump level notLit ws (p + 2) q a arena delayed s ticks res
      else if otherValue != 0 then
        propLoop ignore beyond probing jump level notLit ws (p + 2) q a arena delayed s ticks
          (some (.large ref))
      else
        -- `kissat_fast_assign_reference` (fastassign.h)
        let alevel := asgAssignmentLevel arena a.aLevel other ref 0 size 0
        let s := if alevel == 0 then s.markFixedLiteral other else s
        let a := a.assign probing alevel false other ref
        propLoop ignore beyond probing jump level notLit ws (p + 2) q a arena delayed s
          (ticks + 1) res
  else ⟨ws, p, q, a, arena, delayed, s, ticks, res⟩
termination_by ws.size - p
decreasing_by all_goals simp_all [WVec.size_set!] <;> omega

/-- `while (p != end_watches) *q++ = *p++;` -/
def copyRest (ws : WVec) (p q : Nat) : WVec × Nat :=
  if h : p < ws.size then copyRest (ws.set! q (ws[p])) (p + 1) (q + 1)
  else (ws, q)
termination_by ws.size - p
decreasing_by simp_all [WVec.size_set!]; omega

/-- Port of `PROPAGATE_LITERAL` (proplit.h). Adds the ticks to `s.ticks`. -/
def propagateLiteral (s : Solver) (ignore : Option Ref) (beyond : Bool) (lit : Lit) :
    Solver × Option CRef :=
  let notLit := NOT lit
  let a := s.asg
  let arena := s.arena
  let delayed := s.delayed
  let wss := s.watches
  let s := { s with asg := {}, arena := {}, delayed := .empty, watches := #[] }
  let ws := wss[notLit.toNat]!
  let wss := wss.set! notLit.toNat WVec.empty
  let ticks : UInt64 := 1 + cacheLines (UInt64.ofNat ws.size)
  let probing := s.probing
  let jump := s.options.jumpreasons != 0 && s.classification.bigbig
  let level := a.aLevel.get! (IDX lit).toNat
  match propLoop ignore beyond probing jump level notLit ws 0 0 a arena delayed s ticks none with
  | ⟨ws, p, q, a, arena, delayed, s, ticks, res⟩ =>
    let (ws, q) := copyRest ws p q
    let ws := ws.shrink q
    let wss := wss.set! notLit.toNat ws
    let wss := watchLargeDelayedLoop delayed wss 0
    ({ s with watches := wss, ticks := s.ticks + ticks, asg := a, arena := arena,
              delayed := delayed.clear }, res)

/-- `kissat_flush_trail` (trail.c). -/
def flushTrail (s : Solver) : Solver :=
  { s with asg := { s.asg with trail := s.asg.trail.clear, unflushed := 0 }, propagate := 0 }

/-- `kissat_update_conflicts_and_trail` (proplit.h); `countConflicts` is false for
  probing propagation. -/
def updateConflictsAndTrail (s : Solver) (conflict : Option CRef) (flush : Bool)
    (countConflicts : Bool) : Solver :=
  match conflict with
  | some _ =>
    let s := if countConflicts then INC! s conflicts else s
    if s.level == 0 then { s with inconsistent := true } else s
  | none =>
    if flush && s.level == 0 && s.asg.unflushed != 0 then s.flushTrail else s

/-- `search_propagate` (propsearch.c): propagate trail literals from position `i`.
  The local `propagate` pointer is the explicit parameter `i` as in C.
  -- FUEL: `bound` is the trail capacity (`vars`); the invariant
  `trail.size ≤ vars` guarantees the guard `i < bound` never stops early. -/
def searchPropagateLoop (bound : Nat) (s : Solver) (i : Nat) : Solver × Option CRef × Nat :=
  if _h : i < s.asg.trail.size ∧ i < bound then
    let lit := s.asg.trail.get! i
    let (s, res) := s.propagateLiteral none false lit
    if res.isSome then (s, res, i + 1) else searchPropagateLoop bound s (i + 1)
  else (s, none, i)
termination_by bound - i

/-- `update_search_propagation_statistics` (propsearch.c). -/
def updateSearchPropagationStatistics (s : Solver) (savedPropagate : Nat) : Solver :=
  let propagated := UInt64.ofNat (s.propagate - savedPropagate)
  let t := s.ticks
  let s := ADD! s propagations propagated
  -- ticks, search_propagations, {stable,focused}_{propagations,ticks}: METRIC/STATISTIC
  ADD! s search_ticks t

/-- Port of `kissat_search_propagate` (propsearch.c). -/
def searchPropagate (s : Solver) : Solver × Option CRef :=
  let s := { s with ticks := 0 }
  let saved := s.propagate
  let (s, conflict, i) := searchPropagateLoop s.vars.toNat s s.propagate
  let s := { s with propagate := i }
  let s := s.updateSearchPropagationStatistics saved
  let s := s.updateConflictsAndTrail conflict true true
  let s := if conflict.isSome && s.randec != 0 then { s with randec := s.randec - 1 } else s
  (s, conflict)

/-- Generic propagation loop over the trail with `ignore` (probing variants). -/
def propagateTrailLoop (bound : Nat) (ignore : Option Ref) (s : Solver) (i : Nat) :
    Solver × Option CRef × Nat :=
  if _h : i < s.asg.trail.size ∧ i < bound then
    let lit := s.asg.trail.get! i
    let (s, res) := s.propagateLiteral ignore false lit
    if res.isSome then (s, res, i + 1) else propagateTrailLoop bound ignore s (i + 1)
  else (s, none, i)
termination_by bound - i

/-- Port of `kissat_probing_propagate` (proprobe.c). -/
def probingPropagate (s : Solver) (ignore : Option Ref) (flush : Bool) : Solver × Option CRef :=
  let s := { s with ticks := 0 }
  let saved := s.propagate
  let (s, conflict, i) := propagateTrailLoop s.vars.toNat ignore s s.propagate
  let propagated := UInt64.ofNat (i - saved)
  let s := { s with propagate := i }
  let t := s.ticks
  let s := ADD! s propagations propagated
  -- probing_propagations: METRIC; ticks: STATISTIC
  let s := ADD! s probing_ticks t
  let s := s.updateConflictsAndTrail conflict flush false
  (s, conflict)

/-- `kissat_propagated` (trail.h? inline): all trail literals propagated. -/
@[inline] def propagated (s : Solver) : Bool := s.propagate == s.asg.trail.size

end Solver
end LeanKissat
