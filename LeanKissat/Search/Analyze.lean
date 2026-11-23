import LeanKissat.Search.Minimize

/-
Conflict analysis: `analyze.c`, `deduce.c`, `strengthen.c`.
-/
namespace LeanKissat
namespace Solver

@[inline] def setCrefLit (s : Solver) (c : CRef) (i : Nat) (l : Lit) : Solver :=
  match c with
  | .binConflict => if i == 0 then { s with conflictLit0 := l } else { s with conflictLit1 := l }
  | .large ref => { s with arena := s.arena.setLit ref i l }

/-- The level loop of `one_literal_on_conflict_level` over the conflict literals `i..size`:
  `(jumpLevel, conflictLevel, onLevel, forcedLit)`. -/
def conflictLevelLoop (s : Solver) (conflict : CRef) (size i : Nat) (jumpLevel conflictLevel : UInt32)
    (onLevel : Nat) (forcedLit : Lit) : UInt32 × UInt32 × Nat × Lit :=
  if _h : i < size then
    let lit := s.crefLit conflict i
    let litLevel := s.level' lit
    let (jumpLevel, conflictLevel, onLevel, forcedLit) :=
      if conflictLevel == INVALID_LEVEL || conflictLevel < litLevel then
        (conflictLevel, litLevel, 1, lit)
      else
        let jumpLevel := if jumpLevel == INVALID_LEVEL || jumpLevel < litLevel then litLevel else jumpLevel
        (jumpLevel, conflictLevel, if conflictLevel == litLevel then onLevel + 1 else onLevel, forcedLit)
    if onLevel > 1 && conflictLevel == s.level then (jumpLevel, conflictLevel, onLevel, forcedLit)
    else s.conflictLevelLoop conflict size (i + 1) jumpLevel conflictLevel onLevel forcedLit
  else (jumpLevel, conflictLevel, onLevel, forcedLit)
termination_by size - i

/-- The search for the highest literal in `conflict[j..size)` (stopping at `conflictLevel`):
  `(highestPos, highestLit)`. -/
def highestLoop (s : Solver) (conflict : CRef) (size : Nat) (conflictLevel : UInt32) (j : Nat)
    (highestPos : Nat) (highestLit : Lit) (highestLevel : UInt32) : Nat × Lit :=
  if _h : j < size then
    let other := s.crefLit conflict j
    let level := s.level' other
    if highestLevel ≥ level then s.highestLoop conflict size conflictLevel (j + 1) highestPos highestLit highestLevel
    else if level == conflictLevel then (j, other)
    else s.highestLoop conflict size conflictLevel (j + 1) j other level
  else (highestPos, highestLit)
termination_by size - j

/-- One round of the watch update of `one_literal_on_conflict_level` (position `i`). -/
def moveHighest (s : Solver) (conflict : CRef) (size : Nat) (conflictLevel : UInt32) (i : Nat) : Solver :=
  let lit := s.crefLit conflict i
  let (highestPos, highestLit) :=
    s.highestLoop conflict size conflictLevel (i + 1) i lit (s.level' lit)
  if highestPos == i then s else
  let ref := match conflict with | .large r => r | .binConflict => INVALID_REF
  let s := if highestPos > 1 then s.unwatchBlocking lit ref else s
  let s := s.setCrefLit conflict highestPos lit
  let s := s.setCrefLit conflict i highestLit
  if highestPos > 1 then s.watchBlocking (s.crefLit conflict i) (s.crefLit conflict (1 - i)) ref else s

/-- `lit` is unassigned and every other literal of `conflict[i..size)` is false. -/
def forcedOKFrom (s : Solver) (conflict : CRef) (size : Nat) (lit : Lit) (i : Nat) : Bool :=
  if _h : i < size then
    let other := s.crefLit conflict i
    (other == lit || vFalse (s.value other)) && s.forcedOKFrom conflict size lit (i + 1)
  else true
termination_by size - i

/-- Checked assertion before assigning the forced literal of a conflict. -/
def forcedOK (s : Solver) (conflict : CRef) (size : Nat) (lit : Lit) : Bool :=
  s.value lit == 0 && s.forcedOKFrom conflict size lit 0

/-- Port of `one_literal_on_conflict_level` (analyze.c). Returns
  `(forced, conflictLevel)`. -/
def oneLiteralOnConflictLevel (s : Solver) (conflict : CRef) : Bool × UInt32 × Solver :=
  let size := s.crefSize conflict
  let (jumpLevel, conflictLevel, onLevel, forcedLit) :=
    s.conflictLevelLoop conflict size 0 INVALID_LEVEL INVALID_LEVEL 0 INVALID_LIT
  if conflictLevel == 0 then (false, conflictLevel, { s with inconsistent := true }) else
  let s := if conflictLevel < s.level then s.backtrackAfterConflict conflictLevel else s
  let s := if size > 2 then (s.moveHighest conflict size conflictLevel 0).moveHighest conflict size conflictLevel 1
    else s
  -- checked assertion: the first watch is on the conflict level
  if size > 2 && s.level' (s.crefLit conflict 0) != conflictLevel then
    (true, conflictLevel, { s with overflowed := true }) else
  if onLevel > 1 then (false, conflictLevel, s) else
  let (newLevel, s1) := s.determineNewLevel jumpLevel
  -- checked assertion: the jump level is below the conflict level
  if newLevel ≥ s1.level then (true, conflictLevel, { s1 with overflowed := true }) else
  let s := s1.backtrackAfterConflict newLevel
  -- checked assertion: the forced literal is unassigned and the other literals are false
  if !s.forcedOK conflict size forcedLit then (true, conflictLevel, { s with overflowed := true }) else
  match conflict with
  | .binConflict =>
    let other := s.conflictLit0 ^^^ s.conflictLit1 ^^^ forcedLit
    (true, conflictLevel, s.assignBinary forcedLit other)
  | .large ref => (true, conflictLevel, s.assignReference forcedLit ref)

/-- The conflict loop of `analyze_failed_literal` over `conflict[i..size)`:
  `(done, unresolved, s)`. -/
def failedInit (s : Solver) (conflict : CRef) (notFailed : Lit) (size i unresolved : Nat) :
    Bool × Nat × Solver :=
  if _h : i < size then
    let lit := s.crefLit conflict i
    if lit == notFailed then (true, unresolved, s)
    else
      let idx := IDX lit
      if s.levelIdx idx == 0 then s.failedInit conflict notFailed size (i + 1) unresolved
      else (s.pushAnalyzed idx).failedInit conflict notFailed size (i + 1) (unresolved + 1)
  else (false, unresolved, s)
termination_by size - i

/-- The previous analyzed trail position below `t` (`do lit = *--t; while (!analyzed)`). -/
def prevAnalyzed (s : Solver) : Nat → Option Nat
  | 0 => none
  | t + 1 => if s.isAnalyzed (IDX (s.asg.trail.get! t)) then some t else prevAnalyzed s t

/-- The large-reason loop of `analyze_failed_literal`: `(stop, unresolved, s)`. -/
def failedLarge (s : Solver) (lit unit notFailed : Lit) (ref : Ref) (j n unresolved : Nat) :
    Bool × Nat × Solver :=
  if _h : j < n then
    let other := s.arena.lit ref j
    if other == lit || other == unit then s.failedLarge lit unit notFailed ref (j + 1) n unresolved
    else if other == notFailed then (true, unresolved, s)
    else
      let oidx := IDX other
      if s.levelIdx oidx == 0 || s.isAnalyzed oidx then
        s.failedLarge lit unit notFailed ref (j + 1) n unresolved
      else (s.pushAnalyzed oidx).failedLarge lit unit notFailed ref (j + 1) n (unresolved + 1)
  else (false, unresolved, s)
termination_by n - j

/-- Resolving the analyzed trail literal `lit` in `analyze_failed_literal`: either the final
  state or the state to continue with (and the new `unresolved`, `unit`). -/
def failedResolve (s : Solver) (notFailed lit : Lit) (unresolved : Nat) (unit : Lit) :
    Solver ⊕ (Solver × Nat × Lit) :=
  let idx := IDX lit
  -- checked assertion: a resolved literal is not a decision
  if s.reasonIdx idx == DECISION_REASON then .inl { s with overflowed := true } else
  if s.isBinaryReason idx then
    let other := s.reasonIdx idx
    if other == notFailed then .inl s
    else
      let oidx := IDX other
      -- checked assertion: a binary reason literal is on the same level
      if s.levelIdx oidx == 0 then .inl { s with overflowed := true } else
      if !s.isAnalyzed oidx then .inr (s.pushAnalyzed oidx, unresolved + 1 - 1, unit)
      else .inr (s, unresolved - 1, unit)
  else
    let ref := s.reasonIdx idx
    let (stop, unresolved, s) := s.failedLarge lit unit notFailed ref 0 (s.arena.size ref).toNat unresolved
    if stop then .inl s else .inr (s, unresolved - 1, unit)

/-- One resolution step of `analyze_failed_literal` on the analyzed trail literal at `p`. -/
def failedStep (s : Solver) (notFailed : Lit) (p unresolved : Nat) (unit : Lit) :
    Solver ⊕ (Solver × Nat × Lit) :=
  let lit := s.asg.trail.get! p
  if unresolved == 1 then
    ({ s with clause := s.clause.push (NOT lit) } : Solver).failedResolve notFailed lit unresolved (NOT lit)
  else s.failedResolve notFailed lit unresolved unit

/-- The resolution loop of `analyze_failed_literal` (units are collected in `s.clause`).
  -- FUEL: each round moves `t` backwards; bounded by the trail size. -/
def failedWalk (s : Solver) (notFailed : Lit) (t unresolved : Nat) (unit : Lit) : Nat → Solver
  | 0 => s
  | fuel + 1 =>
    match s.prevAnalyzed t with
    | none => { s with overflowed := true }   -- checked assertion: an analyzed literal remains
    | some p =>
      match s.failedStep notFailed p unresolved unit with
      | .inl s => s
      | .inr (s, unresolved, unit) => s.failedWalk notFailed p unresolved unit fuel

/-- Every trail literal of `trail[i..n)` other than `failed` has a reason. -/
def decisionsOK (s : Solver) (failed : Lit) (i n : Nat) : Bool :=
  if _h : i < n then
    let x := s.asg.trail.get! i
    (s.reasonIdx (IDX x) != DECISION_REASON || x == failed) && s.decisionsOK failed (i + 1) n
  else true
termination_by n - i

/-- Assign the learned units `clause[i..n)` at the root level (checking they are unassigned). -/
def learnUnits (s : Solver) (i n : Nat) : Solver :=
  if _h : i < n then
    let lit := s.clause.get! i
    if s.value lit != 0 then { s with overflowed := true }   -- checked assertion
    else (s.learnedUnit lit).learnUnits (i + 1) n
  else s
termination_by n - i

/-- Backtracking to the root and assigning the units of `analyze_failed_literal`. -/
def failedLearn (s : Solver) : Solver :=
  let s := if !s.probing then s.updateLearned 0 1 else s
  let s := s.backtrackWithoutUpdatingPhases 0
  let s := s.learnUnits 0 s.clause.size
  let s := { s with clause := s.clause.clear }
  if !s.probing then
    let s := { s with iterating := true }
    INC! s iterations
  else s

/-- Learning the units collected by `analyze_failed_literal` and `NOT failed`. -/
def failedFinish (s : Solver) (failed : Lit) : Solver :=
  if s.overflowed then s else
  -- checked assertion: `failed` is the only decision on level 1
  if !(s.value failed == VAL_TRUE && s.decisionsOK failed (s.frameTrailAt 1).toNat s.asg.trail.size) then
    { s with overflowed := true } else
  ({ s with clause := s.clause.push (NOT failed) } : Solver).failedLearn

/-- The resolution phase of `analyze_failed_literal`. -/
def failedCollect (s : Solver) (conflict : CRef) (notFailed : Lit) : Solver :=
  let (done, unresolved, s) := s.failedInit conflict notFailed (s.crefSize conflict) 0 0
  if done then s else s.failedWalk notFailed s.asg.trail.size unresolved INVALID_LIT s.asg.trail.size

/-- Port of `analyze_failed_literal` (analyze.c). -/
def analyzeFailedLiteral (s : Solver) (conflict : CRef) : Solver :=
  let failed := s.frameDecisionAt 1
  (s.failedCollect conflict (NOT failed)).failedFinish failed

/-! ### `strengthen.c` -/

/-- Port of `large_on_the_fly_strengthen` (strengthen.c). -/
def largeOnTheFlyStrengthen (s : Solver) (ref : Ref) (lit : Lit) : Solver := Id.run do
  let mut s := s
  -- INC (on_the_fly_strengthened): STATISTIC
  if s.arena.lit ref 0 == lit then
    let l0 := s.arena.lit ref 0
    let l1 := s.arena.lit ref 1
    s := { s with arena := (s.arena.setLit ref 0 l1).setLit ref 1 l0 }
  s := s.unwatchBlocking lit ref
  let oldSize := (s.arena.size ref).toNat
  let mut newSize := 1
  let irredundant := !s.arena.redundant ref
  for i in [2:oldSize] do
    let other := s.arena.lit ref i
    if s.level' other == 0 then continue
    s := { s with arena := s.arena.setLit ref newSize other }
    newSize := newSize + 1
    if irredundant then s := s.markAddedLiteral other
  s := { s with arena := (s.arena.setSize ref (UInt32.ofNat newSize)).setSearched ref 2 }
  if s.arena.redundant ref && (s.arena.glue ref).toNat ≥ newSize then
    s := s.promoteClause ref (UInt32.ofNat (newSize - 1))
  if !s.arena.shrunken ref then
    s := { s with arena := (s.arena.setShrunken ref true).setLit ref (oldSize - 1) INVALID_LIT }
  let mut highestPos := 1
  let mut highestLevel := s.level' (s.arena.lit ref 1)
  for i in [2:newSize] do
    let level := s.level' (s.arena.lit ref i)
    if level ≤ highestLevel then continue
    highestPos := i
    highestLevel := level
  if highestPos != 1 then
    let a := s.arena.lit ref 1
    let b := s.arena.lit ref highestPos
    s := { s with arena := (s.arena.setLit ref 1 b).setLit ref highestPos a }
  let l0 := s.arena.lit ref 0
  let l1 := s.arena.lit ref 1
  s := s.watchBlocking l1 l0 ref
  -- update the blocking literal of the watch of `lits[0]`
  let ws := s.watchesOf l0
  let mut pos := ws.size
  let mut p := 0
  for _ in [0:ws.size] do
    if p ≥ ws.size then break
    let head := ws.get! p
    if watchIsBinary head then
      p := p + 1
      continue
    if ws.get! (p + 1) == ref then
      pos := p
      break
    p := p + 2
  if pos < ws.size then s := s.modifyWatches l0 (·.set! pos (blockingWatch l1))
  return s

/-- Port of `binary_on_the_fly_strengthen` (strengthen.c). -/
def binaryOnTheFlyStrengthen (s : Solver) (ref : Ref) (lit : Lit) : Solver := Id.run do
  let mut first := INVALID_LIT
  let mut second := INVALID_LIT
  for i in [0:(s.arena.size ref).toNat] do
    let other := s.arena.lit ref i
    if other == lit then continue
    if s.level' other == 0 then continue
    if first == INVALID_LIT then first := other
    else second := other
  let mut s := s.newBinaryClause first second
  s := s.unwatchBlocking (s.arena.lit ref 0) ref
  s := s.unwatchBlocking (s.arena.lit ref 1) ref
  s := s.markClauseAsGarbage ref
  return { s with conflictLit0 := first, conflictLit1 := second }

/-- Port of `kissat_on_the_fly_strengthen` (strengthen.c). -/
def onTheFlyStrengthen (s : Solver) (ref : Ref) (lit : Lit) : CRef × Solver :=
  let s := if !s.arena.redundant ref then s.markRemovedLiteral lit else s
  if s.antecedentSize == 3 then (.binConflict, s.binaryOnTheFlyStrengthen ref lit)
  else (.large ref, s.largeOnTheFlyStrengthen ref lit)

/-- Port of `kissat_on_the_fly_subsume` (strengthen.c): `c` subsumes the large
  conflict `d`. -/
def onTheFlySubsume (s : Solver) (c : CRef) (d : Ref) : Solver :=
  let s := s.markClauseAsGarbage d
  -- INC (on_the_fly_subsumed): STATISTIC
  -- the static binary conflict clause is never redundant
  let cRed := match c with | .binConflict => false | .large r => s.arena.redundant r
  if s.arena.redundant d then
    match c with
    | .large r => if cRed && s.arena.glue r > s.arena.glue d then s.promoteClause r (s.arena.glue d) else s
    | .binConflict => s
  else if !cRed then s
  else
    match c with
    | .binConflict => s
    | .large r =>
      let size := s.arena.size r
      let s := if size > 2 then
          ({ s with arena := s.arena.setRedundant r false }).updateLastIrredundant r
        else s
      let s := if size > 2 then INC! s clauses_irredundant else INC! s clauses_binary
      DEC! s clauses_redundant

/-! ### `deduce.c` -/

/-- Port of `analyze_literal` (deduce.c). Returns whether the literal is on the
  current level and newly analyzed. -/
def analyzeLiteral (s : Solver) (lit : Lit) : Bool × Solver :=
  let idx := IDX lit
  let level := s.levelIdx idx
  if level == 0 then (false, s) else
  let s := { s with antecedentSize := s.antecedentSize + 1 }
  if s.isAnalyzed idx then (false, s) else
  let s := s.pushAnalyzed idx
  let s := { s with resolventSize := s.resolventSize + 1 }
  if level == s.level then (true, s) else
  let s := { s with clause := s.clause.push lit }
  let used := s.frameUsedAt level
  let s := { s with frameUsed := s.frameUsed.set! level.toNat (used + 1) }
  if used != 0 then (false, s)
  else (false, { s with levels := s.levels.push level })

/-- Find the next analyzed literal on the current level going down the trail. -/
def findUip (s : Solver) (t : Nat) : Lit × Nat :=
  if h : t = 0 then (INVALID_LIT, 0) else
  let uip := s.asg.trail.get! (t - 1)
  let idx := IDX uip
  if s.isAnalyzed idx && s.levelIdx idx == s.level then (uip, t - 1)
  else findUip s (t - 1)
termination_by t

/-- The literal loop over a large reason clause in `kissat_deduce_first_uip_clause`
  (`analyze_literal` on every literal except `uip`; `u` counts new current-level ones). -/
def analyzeReasonLits (s : Solver) (ref : Ref) (uip : Lit) (i n : Nat) (u : Nat) : Nat × Solver :=
  if _h : i < n then
    let lit := s.arena.lit ref i
    if lit == uip then s.analyzeReasonLits ref uip (i + 1) n u
    else
      let (b, s) := s.analyzeLiteral lit
      s.analyzeReasonLits ref uip (i + 1) n (if b then u + 1 else u)
  else (u, s)
termination_by n - i

/-- The literal loop over the conflict in `kissat_deduce_first_uip_clause`. -/
def analyzeConflictLits (s : Solver) (c : CRef) (i n : Nat) (unres csize : Nat) : Nat × Nat × Solver :=
  if _h : i < n then
    let lit := s.crefLit c i
    let csize := if s.level' lit != 0 then csize + 1 else csize
    let (b, s) := s.analyzeLiteral lit
    s.analyzeConflictLits c (i + 1) n (if b then unres + 1 else unres) csize
  else (unres, csize, s)
termination_by n - i

/-- Resolve the reason of `uip` (analyze its antecedent literals). -/
def resolveReason (s : Solver) (uip : Lit) (unresolved : Nat) : Nat × Solver :=
  let idx := IDX uip
  if s.isBinaryReason idx then
    let (b, s) := s.analyzeLiteral (s.reasonIdx idx)
    (if b then unresolved + 1 else unresolved, s)
  else
    let ref := s.reasonIdx idx
    let (u, s) := s.analyzeReasonLits ref uip 0 (s.arena.size ref).toNat unresolved
    (u, s.markClauseAsUsed ref)

/-- Main resolution loop of `kissat_deduce_first_uip_clause`. Returns
  `none` when the 1st UIP is reached (clause in `s.clause`) or `some c` for a new
  conflict produced by on-the-fly strengthening.
  -- FUEL: each round consumes a trail position (`t` decreases). -/
def deduceLoop (s : Solver) (conflict : CRef) (otfs : Bool) (conflictSize : Nat)
    (unresolved resolved : Nat) (t : Nat) (fuel : Nat) : Option CRef × Solver :=
  match fuel with
  | 0 => (none, { s with overflowed := true })   -- unreachable (see FUEL); stop with `unknown`
  | fuel + 1 =>
    let (uip, t) := s.findUip t
    if unresolved == 1 then
      (none, { s with clause := s.clause.set! 0 (NOT uip) })
    else if s.reasonIdx (IDX uip) == DECISION_REASON then
      -- checked assertion: only the 1st UIP can be the decision (stop with `unknown`)
      (none, { s with overflowed := true })
    else
      let s := { s with antecedentSize := 1 }
      let resolved := resolved + 1
      let idx := IDX uip
      let (unresolved, s) := s.resolveReason uip unresolved
      let unresolved := unresolved - 1
      let s := { s with resolventSize := s.resolventSize - 1 }
      if otfs && s.antecedentSize > 2 && s.resolventSize < s.antecedentSize then
        let reasonRef := s.reasonIdx idx
        let (res, s) := s.onTheFlyStrengthen reasonRef uip
        let s :=
          if resolved == 1 && s.resolventSize.toNat < conflictSize then
            match conflict with
            | .large d => s.onTheFlySubsume res d
            | .binConflict => s
          else s
        (some res, s)
      else deduceLoop s conflict otfs conflictSize unresolved resolved t fuel

/-- Port of `kissat_deduce_first_uip_clause` (deduce.c). -/
def deduceFirstUipClause (s : Solver) (conflict : CRef) : Option CRef × Solver :=
  let s := if s.crefSize conflict > 2 then
      match conflict with
      | .large ref => s.markClauseAsUsed ref
      | .binConflict => s
    else s
  let s := { s with clause := s.clause.push INVALID_LIT, antecedentSize := 0, resolventSize := 0 }
  let (unresolved, conflictSize, s) := s.analyzeConflictLits conflict 0 (s.crefSize conflict) 0 0
  let otfs := s.options.otfs != 0
  -- ADD (literals_deduced, ...): METRIC
  s.deduceLoop conflict otfs conflictSize unresolved 0 s.asg.trail.size (s.asg.trail.size + 1)

/-! ### `analyze.c` -/

/-- Every literal of `c` occurs in `shadow` (`c[0]` at position 0, `c[i]` at `written[i-1]`). -/
def sortedOK (c shadow : U32Vec) (written : Array Nat) (i : Nat) : Bool :=
  if _h : i < c.size then
    written[i - 1]! < shadow.size && shadow.get! written[i - 1]! == c.get! i &&
      sortedOK c shadow written (i + 1)
  else true
termination_by c.size - i

/-- No entry of `c[i..)` is `INVALID_LIT`. -/
def allValid (c : U32Vec) (i : Nat) : Bool :=
  if _h : i < c.size then c.get! i != INVALID_LIT && allValid c (i + 1) else true
termination_by c.size - i

/-- Install the sorted clause after the checked assertion that it contains the deduced one
  and every one of its positions was filled. -/
def sortFinish (s : Solver) (shadow : U32Vec) (starts : U32Vec) (written : Array Nat) : Solver :=
  if 0 < shadow.size && shadow.get! 0 == s.clause.get! 0 && sortedOK s.clause shadow written 1 &&
    allValid shadow 0 then
    { s with clause := shadow, frameUsed := starts }
  else { s with frameUsed := starts, overflowed := true }

/-- Start positions of the levels of `sort_deduced_clause` (in order of decreasing level),
  with the saved `used` counters. -/
def sortStarts (levels : Array UInt32) (starts : U32Vec) : U32Vec × Array UInt32 := Id.run do
  let mut pos : UInt32 := 1
  let mut starts := starts
  let mut saved : Array UInt32 := #[]
  for k in [0:levels.size] do
    let level := levels[levels.size - 1 - k]!
    let used := starts.get! level.toNat
    saved := saved.push used
    starts := starts.set! level.toNat pos
    pos := pos + used
  return (starts, saved)

/-- The literal distribution loop of `sort_deduced_clause` over `clause[i..n)`. -/
def sortWrite (s : Solver) (starts shadow : U32Vec) (written : Array Nat) (i n : Nat) :
    U32Vec × U32Vec × Array Nat :=
  if _h : i < n then
    let lit := s.clause.get! i
    let level := s.level' lit
    let p := starts.get! level.toNat
    sortWrite s (starts.set! level.toNat (p + 1)) (shadow.set! p.toNat lit) (written.push p.toNat) (i + 1) n
  else (starts, shadow, written)
termination_by n - i

/-- Restore the `used` counters after `sort_deduced_clause`. -/
def sortRestore (levels : Array UInt32) (saved : Array UInt32) (starts : U32Vec) : U32Vec := Id.run do
  let mut starts := starts
  for k in [0:levels.size] do
    let level := levels[levels.size - 1 - k]!
    starts := starts.set! level.toNat saved[k]!
  return starts

/-- The sorted copy of the deduced clause (`sort_deduced_clause`): sort literals by decreasing
  level, keeping the relative order within a level (levels are distinct, so any sort of
  `levels` gives C's result). Returns `(shadow, used counters, written positions)`. -/
def sortShadow (s : Solver) (frameUsed : U32Vec) : U32Vec × U32Vec × Array Nat :=
  let levels := (s.levels.toArray.qsort (· < ·))
  let (starts, saved) := sortStarts levels frameUsed
  let n := s.clause.size
  let shadow := (U32Vec.replicate n INVALID_LIT).set! 0 (s.clause.get! 0)
  let (starts, shadow, written) := s.sortWrite starts shadow (Array.emptyWithCapacity n) 1 n
  (shadow, sortRestore levels saved starts, written)

/-- Port of `sort_deduced_clause` (analyze.c), see `sortShadow`. -/
def sortDeducedClause (s : Solver) : Solver :=
  -- Take `frameUsed` out of `s` first: `sortShadow` also reads `s`, so a shared `frameUsed`
  -- would be copied by its first write.
  let frameUsed := s.frameUsed
  let s := { s with frameUsed := .empty }
  let (shadow, starts, written) := s.sortShadow frameUsed
  sortFinish s shadow starts written

/-- Port of `reset_levels` (analyze.c). -/
def zeroUsed (levels : U32Vec) (fu : U32Vec) (i n : Nat) : U32Vec :=
  if _h : i < n then zeroUsed levels (fu.set! (levels.get! i).toNat 0) (i + 1) n else fu
termination_by n - i

def resetLevels (s : Solver) : Solver :=
  { s with frameUsed := zeroUsed s.levels s.frameUsed 0 s.levels.size, levels := s.levels.clear }

/-- Port of `kissat_reset_only_analyzed_literals` (analyze.c). -/
def resetOnlyAnalyzedLiterals (s : Solver) : Solver :=
  let s := s.clearBitsUp s.analyzed ABits.analyzed 0 s.analyzed.size
  { s with analyzed := s.analyzed.clear }

/-- Port of `reset_removable` (analyze.c). -/
def resetRemovable (s : Solver) : Solver :=
  let s := s.clearBitsUp s.removable ABits.removable 0 s.removable.size
  { s with removable := s.removable.clear }

/-- Port of `reset_analysis_but_not_analyzed_literals` (analyze.c). -/
def resetAnalysisButNotAnalyzedLiterals (s : Solver) : Solver :=
  let s := s.resetRemovable.resetLevels
  { s with clause := s.clause.clear }

/-- Port of `update_trail_average` (analyze.c). -/
def updateTrailAverage (s : Solver) : Solver :=
  let size := s.asg.trail.size
  let assigned := size - s.asg.unflushed.toNat
  let filled := kissatPercent (UInt64.ofNat assigned).toFloat (UInt64.ofNat s.active.toNat).toFloat
  s.modifyAverages fun a => { a with trail := a.trail.update filled }

/-- Port of `update_decision_rate_average` (analyze.c). -/
def updateDecisionRateAverage (s : Solver) : Solver :=
  let current := s.stats.decisions
  let previous := s.averagesCur.savedDecisions
  let decisions := current - previous
  s.modifyAverages fun a =>
    { a with savedDecisions := current, decisionRate := a.decisionRate.update decisions.toFloat }

/-- The body of `analyze_reason_side_literals` (analyze.c) once enabled. -/
def analyzeReasonSideLiteralsCore (s : Solver) : Solver := Id.run do
  -- DELAYING (bumpreasons)
  let d := s.delays.bumpreasons
  if d.count != 0 then
    return { s with delays := { s.delays with bumpreasons := { d with count := d.count - 1 } } }
  let decisionRate := s.averagesCur.decisionRate.value
  let limitRate := (UInt64.ofNat s.options.bumpreasonsrate).toFloat
  if decisionRate ≥ limitRate then return s
  let saved := s.analyzed.size
  let limit := s.options.bumpreasonslimit * saved
  let mut s := s
  for i in [0:s.clause.size] do
    let lit := s.clause.get! i
    let idx := IDX lit
    let r := s.reasonIdx idx
    if r != DECISION_REASON then
      if s.isBinaryReason idx then
        let other := r
        let oidx := IDX other
        if s.levelIdx oidx != 0 && !s.isAnalyzed oidx then s := s.pushAnalyzed oidx
      else
        s := INC! s search_ticks
        let notLit := NOT lit
        for j in [0:(s.arena.size r).toNat] do
          let other := s.arena.lit r j
          if other == notLit then continue
          let oidx := IDX other
          if s.levelIdx oidx != 0 && !s.isAnalyzed oidx then s := s.pushAnalyzed oidx
          if s.analyzed.size > limit then break
    if s.analyzed.size > limit then break
  if s.analyzed.size > limit then
    for _ in [0:s.analyzed.size - saved] do
      let idx := s.analyzed.back!
      s := { (s.setABit idx ABits.analyzed false) with analyzed := s.analyzed.pop }
    -- BUMP_DELAY (bumpreasons)
    let d := s.delays.bumpreasons
    let cur := d.current + (if d.current < UINT_MAX then 1 else 0)
    return { s with delays := { s.delays with bumpreasons := { current := cur, count := cur } } }
  else
    -- REDUCE_DELAY (bumpreasons)
    let d := s.delays.bumpreasons
    if d.current == 0 then return s
    let cur := d.current / 2
    return { s with delays := { s.delays with bumpreasons := { current := cur, count := cur } } }

/-- Port of `analyze_reason_side_literals` (analyze.c). -/
def analyzeReasonSideLiterals (s : Solver) : Solver :=
  if s.options.bump == 0 || s.options.bumpreasons == 0 || s.probing then s
  else s.analyzeReasonSideLiteralsCore

/-- Port of `update_tier_limits` (analyze.c). -/
def updateTierLimits (s : Solver) : Solver :=
  let s := INC! s retiered
  let s := s.computeAndSetTierLimits
  let iv : UInt64 := s.limits.glueInterval
  let iv : UInt64 := if iv < 65536 then 2 * iv else iv
  { s with limits := { s.limits with glueInterval := iv, glueConflicts := s.stats.conflicts + iv } }

/-- Sorting, minimization and shrinking of a deduced clause (in `kissat_analyze`). -/
def minimizeDeduced (s : Solver) : Solver :=
  if s.options.minimize != 0 then
    let s := s.sortDeducedClause
    if s.overflowed then s   -- checked assertion failed: stop with `unknown`
    else
      let s := s.minimizeClause
      if s.options.shrink != 0 then s.shrinkClause else s
  else s

/-- Learning the deduced clause (the non-OTFS branch of `kissat_analyze`). A state flagged
  `overflowed` (deduction or sorting stopped) skips learning; the search then stops with
  `unknown`. -/
def learnDeduced (s : Solver) : Solver :=
  if s.overflowed then s else
  let s := s.minimizeDeduced
  if s.overflowed then s else
  s.analyzeReasonSideLiterals.learnClause.resetAnalysisButNotAnalyzedLiterals

/-- Bumping and resetting the analyzed literals at the end of an analysis round. -/
def finishAnalysis (s : Solver) : Solver :=
  if s.analyzed.size != 0 then
    let s := if !s.probing && s.options.bump != 0 then s.bumpAnalyzed else s
    s.resetOnlyAnalyzedLiterals
  else s

/-- One iteration of the `do … while (!res)` loop in `kissat_analyze`:
  `1` done, `-1` inconsistent, or a new conflict to analyze. -/
def analyzeStep (s : Solver) (conflict : CRef) : (Int ⊕ CRef) × Solver :=
  let (forced, conflictLevel, s) := s.oneLiteralOnConflictLevel conflict
  if forced then (.inl 1, s.finishAnalysis)
  else if conflictLevel == 0 then (.inl (-1), s.finishAnalysis)
  else if conflictLevel == 1 then (.inl 1, (s.analyzeFailedLiteral conflict).finishAnalysis)
  else
    match s.deduceFirstUipClause conflict with
    | (some c, s) =>
      let s := s.resetAnalysisButNotAnalyzedLiterals
      let s := INC! s conflicts
      let s := if s.stats.conflicts > s.limits.glueConflicts then s.updateTierLimits else s
      (.inr c, s.finishAnalysis)
    | (none, s) => (.inl 1, s.learnDeduced.finishAnalysis)

/-- The analysis loop. Each extra round is caused by on-the-fly strengthening,
  which removes a literal from an arena clause.
  -- FUEL: bounded by the number of arena words plus one. -/
def analyzeLoop (s : Solver) (conflict : CRef) (fuel : Nat) : Int × Solver :=
  match fuel with
  | 0 => (1, { s with overflowed := true })   -- unreachable (see FUEL); stop with `unknown`
  | fuel + 1 =>
    match s.analyzeStep conflict with
    | (.inl r, s) => (r, s)
    | (.inr c, s) => analyzeLoop s c fuel

/-- The average updates at the start of `kissat_analyze`. -/
def updateAnalysisAverages (s : Solver) : Solver :=
  let s := s.updateTrailAverage.updateDecisionRateAverage
  let lvl := (UInt64.ofNat s.level.toNat).toFloat
  s.modifyAverages fun a => { a with level := a.level.update lvl }

/-- Port of `kissat_analyze` (analyze.c): returns `0` or `20`. -/
def analyze (s : Solver) (conflict : CRef) : UInt32 × Solver :=
  if s.inconsistent then (20, s) else
  let s := if !s.probing then s.updateAnalysisAverages else s
  let (res, s) := s.analyzeLoop conflict (s.arena.words.size + 1)
  (if res > 0 then 0 else 20, s)

end Solver
end LeanKissat
