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
decreasing_by all_goals (simp_all [WVec.size_set!]; try omega)

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

/-- Result of `searchPropagateFused`: the solver (with its propagation buffers detached),
  the buffers, the ticks accumulated by the loop, the conflict and the trail position. -/
structure FusedResult where
  s : Solver
  a : Asg
  arena : Arena
  delayed : U32Vec
  wss : Array WVec
  ticks : UInt64
  res : Option CRef
  i : Nat

/-- `searchPropagateLoop` with the propagation buffers (assignment, arena, delayed watches,
  watch lists) taken out of the solver once for the whole loop rather than once per trail
  literal. The loop body is `propagateLiteral` without the detach and restore. -/
def searchPropagateFused (bound : Nat) (s : Solver) (a : Asg) (arena : Arena)
    (delayed : U32Vec) (wss : Array WVec) (ticks : UInt64) (i : Nat) : FusedResult :=
  if _h : i < a.trail.size ∧ i < bound then
    let lit := a.trail.get! i
    let notLit := NOT lit
    let ws := wss[notLit.toNat]!
    let wss := wss.set! notLit.toNat WVec.empty
    let t : UInt64 := 1 + cacheLines (UInt64.ofNat ws.size)
    let probing := s.probing
    let jump := s.options.jumpreasons != 0 && s.classification.bigbig
    let level := a.aLevel.get! (IDX lit).toNat
    match propLoop none false probing jump level notLit ws 0 0 a arena delayed s t none with
    | ⟨ws, p, q, a, arena, delayed, s, t, res⟩ =>
      let (ws, q) := copyRest ws p q
      let ws := ws.shrink q
      let wss := wss.set! notLit.toNat ws
      let wss := watchLargeDelayedLoop delayed wss 0
      let ticks := ticks + t
      if res.isSome then ⟨s, a, arena, delayed.clear, wss, ticks, res, i + 1⟩
      else searchPropagateFused bound s a arena delayed.clear wss ticks (i + 1)
  else ⟨s, a, arena, delayed, wss, ticks, none, i⟩
termination_by bound - i

/-- Executable version of `searchPropagateLoop`; see
  `searchPropagateLoop_eq_searchPropagateLoopFast`. -/
def searchPropagateLoopFast (bound : Nat) (s : Solver) (i : Nat) : Solver × Option CRef × Nat :=
  let a := s.asg
  let arena := s.arena
  let delayed := s.delayed
  let wss := s.watches
  let t0 := s.ticks
  let s := { s with asg := {}, arena := {}, delayed := .empty, watches := #[] }
  match searchPropagateFused bound s a arena delayed wss 0 i with
  | ⟨s, a, arena, delayed, wss, ticks, res, i⟩ =>
    ({ s with asg := a, arena := arena, delayed := delayed, watches := wss,
              ticks := t0 + ticks }, res, i)

/-- `propLoop` commutes with any solver update that commutes with the two updates it
  makes (recording a binary conflict, fixing a literal). -/
private theorem propLoop_map (g : Solver → Solver)
    (hc : ∀ s l0 l1, g { s with conflictLit0 := l0, conflictLit1 := l1 } =
      { g s with conflictLit0 := l0, conflictLit1 := l1 })
    (hm : ∀ s l, g (s.markFixedLiteral l) = (g s).markFixedLiteral l)
    (probing jump : Bool) (level : UInt32) (notLit : Lit) (ws : WVec) (p q : Nat) (a : Asg)
    (arena : Arena) (dl : U32Vec) (s : Solver) (ticks : UInt64) (res : Option CRef) :
    propLoop none false probing jump level notLit ws p q a arena dl (g s) ticks res =
      { propLoop none false probing jump level notLit ws p q a arena dl s ticks res with
        s := g (propLoop none false probing jump level notLit ws p q a arena dl s ticks res).s } := by
  have hmi : ∀ (c : Bool) s l, g (if c then s.markFixedLiteral l else s) =
      if c then (g s).markFixedLiteral l else g s := by
    intro c s l; cases c <;> simp [hm]
  fun_induction propLoop none false probing jump level notLit ws p q a arena dl s ticks res
  case case1 ws p q a arena dl s ticks res hp hres =>
    rw [propLoop, dite_eq_left hp, ite_eq_left hres]
  case case12 ws p q a arena dl s ticks res hp =>
    rw [propLoop, dite_eq_right hp]
  case case2 ws p q a arena dl s ticks res hp hres head blocking bv hb ws' hv ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_left hb, ite_eq_left hv]
    exact ih
  case case3 ws p q a arena dl s ticks res hp hres head blocking bv hb ws' hv hf s' ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_left hb, ite_eq_right hv, ite_eq_left hf, ← hc]
    exact ih
  case case4 ws p q a arena dl s ticks res hp hres head blocking bv hb ws' hv hf oidx reason s' a' ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_left hb, ite_eq_right hv, ite_eq_right hf, ← hmi]
    exact ih
  case case5 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_right hb, ite_eq_left hv]
    exact ih
  case case6 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_right hb, ite_eq_right hv, ite_eq_left hg]
    exact ih
  case case7 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov ws'' ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_right hb, ite_eq_right hv, ite_eq_right hg, ite_eq_left hov]
    exact ih
  case case8 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr replacement arena' dl' ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_right hb, ite_eq_right hv, ite_eq_right hg, ite_eq_right hov]
    have hr' := hr; simp only [r, r0, size, searched, ref, tail, dite_eq_ite] at hr'
    rw [ite_eq_left hr']; exact ih
  case case9 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr hig ih =>
    exact absurd hig (by simp)
  case case10 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr hig hov0 ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_right hb, ite_eq_right hv, ite_eq_right hg, ite_eq_right hov]
    have hr' := hr; simp only [r, r0, size, searched, ref, tail, dite_eq_ite] at hr'
    rw [ite_eq_right hr', ite_eq_right hig, ite_eq_left hov0]; exact ih
  case case11 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr hig hov0 alevel s' a' ih =>
    conv => lhs; rw [propLoop]
    rw [dite_eq_left hp, ite_eq_right hres]
    dsimp only
    rw [ite_eq_right hb, ite_eq_right hv, ite_eq_right hg, ite_eq_right hov]
    have hr' := hr; simp only [r, r0, size, searched, ref, tail, dite_eq_ite] at hr'
    rw [ite_eq_right hr', ite_eq_right hig, ite_eq_right hov0, ← hmi]; exact ih

/-- The solver as `propagateLiteral` passes it to `propLoop`: propagation buffers detached,
  ticks set to `T`. -/
private abbrev detached (T : UInt64) (x : Solver) : Solver :=
  { x with asg := {}, arena := {}, delayed := .empty, watches := #[], ticks := T }

private theorem detached_markFixedLiteral (T : UInt64) (x : Solver) (l : Lit) :
    detached T (x.markFixedLiteral l) = (detached T x).markFixedLiteral l := by
  unfold markFixedLiteral deactivateVariable setVarFlag
  by_cases h : x.scores.contains (IDX l) = true <;> simp only [h, detached, ↓reduceIte, Bool.false_eq_true] <;> rfl

/-- `searchPropagateLoop` on a solver whose buffers are `a`, `arena`, `dl`, `wss` and whose
  ticks are `T + tk` equals the fused loop followed by restoring the buffers. -/
private theorem searchPropagateLoop_eq_fused (bound : Nat) (s : Solver) (a : Asg) (arena : Arena)
    (dl : U32Vec) (wss : Array WVec) (T tk : UInt64) (i : Nat) :
    searchPropagateLoop bound
        { s with asg := a, arena := arena, delayed := dl, watches := wss, ticks := T + tk } i =
      let r := searchPropagateFused bound s a arena dl wss tk i
      ({ r.s with asg := r.a, arena := r.arena, delayed := r.delayed, watches := r.wss,
                  ticks := T + r.ticks }, r.res, r.i) := by
  fun_induction searchPropagateFused bound s a arena dl wss tk i
  case case3 s a ar dl wss tk i hg =>
    rw [searchPropagateLoop, dite_eq_right hg]
  case case1 s a ar dl wss tk i hg lit notLit ws wss1 t probing jump level ws2 p q a' ar' dl' s' t'
      res hpl ws3 q' hcr ws4 wss2 wss3 tk' hres =>
    have hp := propLoop_map (detached (T + tk)) (fun _ _ _ => rfl) (detached_markFixedLiteral _)
      probing jump level notLit ws 0 0 a ar dl s t none
    rw [hpl] at hp
    rw [searchPropagateLoop, dite_eq_left hg]
    unfold propagateLiteral
    dsimp only
    rw [hp]
    dsimp only
    rw [hcr]
    dsimp only
    rw [ite_eq_left hres, UInt64.add_assoc]
  case case2 s a ar dl wss tk i hg lit notLit ws wss1 t probing jump level ws2 p q a' ar' dl' s' t'
      res hpl ws3 q' hcr ws4 wss2 wss3 tk' hres ih =>
    have hp := propLoop_map (detached (T + tk)) (fun _ _ _ => rfl) (detached_markFixedLiteral _)
      probing jump level notLit ws 0 0 a ar dl s t none
    rw [hpl] at hp
    rw [searchPropagateLoop, dite_eq_left hg]
    unfold propagateLiteral
    dsimp only
    rw [hp]
    dsimp only
    rw [hcr]
    dsimp only
    rw [ite_eq_right hres, UInt64.add_assoc]
    exact ih

/-- The compiler runs `searchPropagateLoopFast`; proofs reason about `searchPropagateLoop`. -/
@[csimp] theorem searchPropagateLoop_eq_searchPropagateLoopFast :
    @searchPropagateLoop = @searchPropagateLoopFast := by
  funext bound s i
  have h := searchPropagateLoop_eq_fused bound
    { s with asg := {}, arena := {}, delayed := .empty, watches := #[] } s.asg s.arena s.delayed
    s.watches s.ticks 0 i
  rw [UInt64.add_zero] at h
  exact h

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

/-- With no ignored clause, the probing propagation loop is the search propagation loop. -/
theorem propagateTrailLoop_none (bound : Nat) (s : Solver) (i : Nat) :
    propagateTrailLoop bound none s i = searchPropagateLoop bound s i := by
  fun_induction propagateTrailLoop bound none s i with
  | case1 s i hg lit s' res hp hres =>
    rw [searchPropagateLoop, dite_eq_left hg]
    dsimp only
    rw [hp]
    dsimp only
    rw [ite_eq_left hres]
  | case2 s i hg lit s' res hp hres ih =>
    rw [searchPropagateLoop, dite_eq_left hg]
    dsimp only
    rw [hp]
    dsimp only
    rw [ite_eq_right hres]
    exact ih
  | case3 s i hg =>
    rw [searchPropagateLoop, dite_eq_right hg]

/-- Executable version of `propagateTrailLoop`; see
  `propagateTrailLoop_eq_propagateTrailLoopFast`. -/
def propagateTrailLoopFast (bound : Nat) (ignore : Option Ref) (s : Solver) (i : Nat) :
    Solver × Option CRef × Nat :=
  match ignore with
  | none => searchPropagateLoop bound s i
  | some _ => propagateTrailLoop bound ignore s i

/-- The compiler runs `propagateTrailLoopFast`; proofs reason about `propagateTrailLoop`. -/
@[csimp] theorem propagateTrailLoop_eq_propagateTrailLoopFast :
    @propagateTrailLoop = @propagateTrailLoopFast := by
  funext bound ignore s i
  cases ignore with
  | none => exact propagateTrailLoop_none bound s i
  | some _ => rfl

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
