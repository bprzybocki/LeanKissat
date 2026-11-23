import LeanKissat.Search.Decide

/-
Learning helpers: `promote.c`/`promote.h`, `tiers.c` (limits), `learn.c`,
`kissat_update_last_irredundant` (collect.c), `bump.c`.
-/
namespace LeanKissat
namespace Solver

/-! ### Clause view used during analysis -/

@[inline] def crefSize (s : Solver) : CRef → Nat
  | .binConflict => 2
  | .large ref => (s.arena.size ref).toNat

@[inline] def crefLit (s : Solver) : CRef → Nat → Lit
  | .binConflict, i => if i == 0 then s.conflictLit0 else s.conflictLit1
  | .large ref, i => s.arena.lit ref i

/-! ### `promote.h`, `promote.c` -/

@[inline] def framePromoteAt (s : Solver) (lvl : UInt32) : Bool := s.framePromote.get! lvl.toNat != 0
@[inline] def setFramePromote (s : Solver) (lvl : UInt32) (b : Bool) : Solver :=
  { s with framePromote := s.framePromote.set! lvl.toNat (if b then 1 else 0) }

/-- Port of `kissat_recompute_glue` (promote.h). -/
def recomputeGlue (s : Solver) (ref : Ref) (limit : UInt32) : UInt32 × Solver := Id.run do
  let n := (s.arena.size ref).toNat
  let mut s := s
  let mut res : UInt32 := 0
  for i in [0:n] do
    let lit := s.arena.lit ref i
    let level := s.level' lit
    if s.framePromoteAt level then continue
    res := res + 1
    if res == limit then break
    s := s.setFramePromote level true
    s := { s with promote := s.promote.push level }
  for i in [0:s.promote.size] do
    s := s.setFramePromote (s.promote.get! i) false
  return (res, { s with promote := s.promote.clear })

/-- Port of `kissat_promote_clause` (promote.c). Only the glue update and
  `clauses_improved` (STATISTIC) remain in the default build. -/
def promoteClause (s : Solver) (ref : Ref) (newGlue : UInt32) : Solver :=
  if s.options.promote == 0 then s
  else { s with arena := s.arena.setGlue ref newGlue }

/-- `recompute_and_promote` (deduce.c). -/
def recomputeAndPromote (s : Solver) (ref : Ref) : Solver :=
  let oldGlue := s.arena.glue ref
  let (newGlue, s) := s.recomputeGlue ref oldGlue
  if newGlue < oldGlue then s.promoteClause ref newGlue else s

/-- Port of `mark_clause_as_used` (deduce.c). -/
def markClauseAsUsed (s : Solver) (ref : Ref) : Solver :=
  if !s.arena.redundant ref then s else
  let s := INC! s clauses_used
  let s := { s with arena := s.arena.setUsed ref MAX_USED }
  let s := s.recomputeAndPromote ref
  let glue := min (s.arena.glue ref) 127
  let s := { s with stats := s.stats.add (Counters.usedBase s.stable + glue.toNat) 1 }
  if s.stable then INC! s clauses_used_stable else INC! s clauses_used_focused

/-! ### `tiers.c` -/

def TIER1RELATIVE (s : Solver) : Float := (UInt64.ofNat s.options.tier1relative).toFloat / 1000.0
def TIER2RELATIVE (s : Solver) : Float := (UInt64.ofNat s.options.tier2relative).toFloat / 1000.0

/-- Port of `compute_tier_limits` (tiers.c). -/
def computeTierLimits (s : Solver) (stable : Bool) : UInt32 × UInt32 := Id.run do
  let base := Counters.usedBase stable
  let used := (Array.range 128).map (fun g => s.stats.get (base + g))
  let mut total : UInt64 := 0
  for g in [0:128] do
    total := total + used[g]!
  let mut tier1 : Int := -1
  let mut tier2 : Int := -1
  if total != 0 then
    let acc1 : UInt64 := (total.toFloat * s.TIER1RELATIVE).toUInt64
    let acc2 : UInt64 := (total.toFloat * s.TIER2RELATIVE).toUInt64
    let mut acc : UInt64 := 0
    for g in [0:128] do
      acc := acc + used[g]!
      if acc ≥ acc1 then
        tier1 := g
        break
    if acc < acc2 then
      for g in [(tier1 + 1).toNat:128] do
        acc := acc + used[g]!
        if acc ≥ acc2 then
          tier2 := g
          break
  if tier1 < 0 then
    tier1 := s.options.tier1
    tier2 := max s.options.tier2 tier1.toNat
  else if tier2 < 0 then
    tier2 := tier1
  return (UInt32.ofNat tier1.toNat, UInt32.ofNat tier2.toNat)

/-- Port of `kissat_compute_and_set_tier_limits` (tiers.c). -/
def computeAndSetTierLimits (s : Solver) : Solver :=
  let st := s.stable
  let (t1, t2) := s.computeTierLimits st
  let i := if st then 1 else 0
  { s with tier1 := s.tier1.set! i t1, tier2 := s.tier2.set! i t2 }

/-! ### `learn.c` -/

/-- `backjump_limit` (learn.c). -/
@[inline] def backjumpLimit (s : Solver) : UInt32 :=
  if s.options.chrono != 0 then UInt32.ofNat s.options.chronolevels else UINT_MAX

/-- Port of `kissat_determine_new_level` (learn.c). -/
def determineNewLevel (s : Solver) (jump : UInt32) : UInt32 × Solver :=
  let back := s.level - 1
  let delta := back - jump
  let limit := s.backjumpLimit
  if delta == 0 then (jump, s)
  else if delta > limit then (back, INC! s chronological)
  else (jump, s)

/-- Port of `kissat_update_learned` (learn.c). -/
def updateLearned (s : Solver) (glue size : UInt32) : Solver :=
  let s := INC! s clauses_learned
  let s := if s.stable then { s with reluctant := s.reluctant.tick } else s
  -- ADD (literals_learned, size): METRIC
  let g := (UInt64.ofNat glue.toNat).toFloat
  s.modifyAverages fun a =>
    { a with
      size := a.size.update (UInt64.ofNat size.toNat).toFloat
      fastGlue := a.fastGlue.update g
      slowGlue := a.slowGlue.update g }

/-- Mark the literals `clause[i..n)`; `false` if a literal occurs twice. -/
def markClauseLits (s : Solver) (i n : Nat) : Bool × Solver :=
  if _h : i < n then
    let lit := s.clause.get! i
    if s.marks.size ≤ lit.toNat || s.mark lit != 0 then (false, s)
    else markClauseLits { s with marks := s.marks.set! lit.toNat 1 } (i + 1) n
  else (true, s)
termination_by n - i

/-- Clear the marks of the literals `clause[i..n)`. -/
def unmarkClauseLits (s : Solver) (i n : Nat) : Solver :=
  if _h : i < n then unmarkClauseLits { s with marks := s.marks.set! (s.clause.get! i).toNat 0 } (i + 1) n
  else s
termination_by n - i

/-- All literals `clause[i..n)` are false. -/
def clauseFalseFrom (s : Solver) (i n : Nat) : Bool :=
  if _h : i < n then vFalse (s.value (s.clause.get! i)) && s.clauseFalseFrom (i + 1) n else true
termination_by n - i

/-- Checked assertion on the learned clause after backtracking (C: assertions in
  `kissat_assign_*` and the clause invariants): the first literal is unassigned, the others
  are false, and no literal occurs twice. -/
def learnedClauseOK (s : Solver) : Bool × Solver :=
  let n := s.clause.size
  if 0 < n && s.value (s.clause.get! 0) == 0 && s.clauseFalseFrom 1 n then
    let (ok, s) := s.markClauseLits 0 n
    (ok, s.unmarkClauseLits 0 n)
  else (false, s)

/-- Backtracking before learning a unit or binary clause, with the checked assertions
  (new level below the current one; see `learnedClauseOK`). -/
@[inline] def learnPrefix (s : Solver) (jump : UInt32) (tail : Solver → Solver) : Solver :=
  let (newLevel, s) := s.determineNewLevel jump
  if newLevel ≥ s.level then { s with overflowed := true } else   -- checked assertion
  let s := s.backtrackAfterConflict newLevel
  let (ok, s) := s.learnedClauseOK
  if !ok then { s with overflowed := true } else tail s   -- checked assertion

/-- The assignment step of `learn_unit`. -/
def learnUnitTail (notUip : Lit) (s : Solver) : Solver :=
  let s := s.learnedUnit notUip
  if !s.probing then
    let s := { s with iterating := true }
    INC! s iterations
  else s

/-- Port of `learn_unit` (learn.c). -/
def learnUnit (s : Solver) (notUip : Lit) : Solver :=
  s.learnPrefix 0 (learnUnitTail notUip)

/-- The clause and assignment step of `learn_binary`. -/
def learnBinaryTail (notUip other : Lit) (s : Solver) : Solver :=
  let (_, s) := s.newRedundantClause 1
  s.assignBinary notUip other

/-- Port of `learn_binary` (learn.c). -/
def learnBinary (s : Solver) (notUip : Lit) : Solver :=
  let other := s.clause.get! 1
  s.learnPrefix (s.level' other) (learnBinaryTail notUip other)

/-- Port of `insert_last_learned` (learn.c). -/
def insertLastLearned (s : Solver) (ref : Ref) : Solver := Id.run do
  let n := s.options.eagersubsume
  let mut ll := s.lastLearned
  let mut prev := ref
  for i in [0:n] do
    let tmp := ll[i]!
    ll := ll.set! i prev
    prev := tmp
  return { s with lastLearned := ll }

/-- The jump literal loop of `learn_reference`: the first literal of maximal level in
  `clause[1..n)`, stopping early at `backtrackLevel`. Returns `(jumpLit, jumpLevel, qpos)`. -/
def selectJump (s : Solver) (backtrackLevel : UInt32) (i n : Nat) (jumpLit : Lit) (jumpLevel : UInt32)
    (qpos : Nat) : Lit × UInt32 × Nat :=
  if _h : i < n then
    let lit := s.clause.get! i
    let level := s.level' lit
    if jumpLevel ≥ level then s.selectJump backtrackLevel (i + 1) n jumpLit jumpLevel qpos
    else if level == backtrackLevel then (lit, level, i)
    else s.selectJump backtrackLevel (i + 1) n lit level i
  else (jumpLit, jumpLevel, qpos)
termination_by n - i

/-- Port of `learn_reference` (learn.c). -/
def learnReference (s : Solver) (notUip : Lit) (glue : UInt32) : Ref × Solver :=
  let n := s.clause.size
  let (jumpLit, jumpLevel, qpos) :=
    s.selectJump (s.level - 1) 2 n (s.clause.get! 1) (s.level' (s.clause.get! 1)) 1
  -- `*q = lits[1]; lits[1] = jump_lit;`
  let s := { s with clause := (s.clause.set! qpos (s.clause.get! 1)).set! 1 jumpLit }
  -- C allocates the clause before backtracking; the two steps touch disjoint state, so we
  -- backtrack first (then the new clause is never all-false in the database)
  let (newLevel, s) := s.determineNewLevel jumpLevel
  if newLevel ≥ s.level then (INVALID_REF, { s with overflowed := true }) else   -- checked assertion
  let s := s.backtrackAfterConflict newLevel
  let (ok, s) := s.learnedClauseOK
  if !ok then (INVALID_REF, { s with overflowed := true }) else   -- checked assertion
  let (ref, s) := s.newRedundantClause glue
  if ref == INVALID_REF then (ref, s) else   -- arena exhausted
  let s := { s with arena := s.arena.setUsed ref MAX_USED }
  (ref, s.assignReference notUip ref)

/-- Port of `flush_last_learned` (learn.c). -/
def flushLastLearned (s : Solver) : Solver := Id.run do
  let n := s.options.eagersubsume
  let ll := s.lastLearned
  let mut out : Array Ref := #[]
  for i in [0:n] do
    if ll[i]! != INVALID_REF then out := out.push ll[i]!
  let mut res := ll
  for i in [0:n] do
    res := res.set! i (if i < out.size then out[i]! else INVALID_REF)
  return { s with lastLearned := res }

/-- Port of `eagerly_subsume_last_learned` (learn.c). -/
def eagerlySubsumeLastLearned (s : Solver) : Solver := Id.run do
  let mut s := s
  for i in [0:s.clause.size] do
    s := { s with marks := s.marks.set! (s.clause.get! i).toNat 1 }
  let clauseSize := s.clause.size
  let mut subsumed := 0
  for i in [0:s.options.eagersubsume] do
    let ref := s.lastLearned[i]!
    if ref == INVALID_REF then continue
    if s.arena.garbage ref then continue
    if !s.arena.redundant ref then continue
    let cSize := (s.arena.size ref).toNat
    if cSize ≤ clauseSize then continue
    let mut needed := clauseSize
    let mut remain := cSize
    for j in [0:cSize] do
      let lit := s.arena.lit ref j
      -- `if (marks[lit] && !--needed) break; else if (--remain < needed) break;`
      if s.mark lit != 0 then
        needed := needed - 1
        if needed == 0 then break
      remain := remain - 1
      if remain < needed then break
    if needed != 0 then continue
    s := s.markClauseAsGarbage ref
    s := { s with lastLearned := s.lastLearned.set! i INVALID_REF }
    subsumed := subsumed + 1
    -- INC (eagerly_subsumed): STATISTIC
  for i in [0:s.clause.size] do
    s := { s with marks := s.marks.set! (s.clause.get! i).toNat 0 }
  if subsumed != 0 then s := s.flushLastLearned
  return s

/-- Port of `kissat_learn_clause` (learn.c). -/
def learnClause (s : Solver) : Solver :=
  let notUip := s.clause.get! 0
  let size := s.clause.size
  let glue := UInt32.ofNat s.levels.size
  let eager := s.options.eagersubsume != 0   -- options are constant
  let s := if !s.probing then s.updateLearned glue (UInt32.ofNat size) else s
  let (ref, s) :=
    if size == 1 then (INVALID_REF, s.learnUnit notUip)
    else if size == 2 then (INVALID_REF, s.learnBinary notUip)
    else s.learnReference notUip glue
  if eager then
    let s := s.eagerlySubsumeLastLearned
    if ref != INVALID_REF then s.insertLastLearned ref else s
  else s

/-! ### `collect.c` helpers -/

/-- Port of `kissat_update_last_irredundant` (collect.c). -/
def updateLastIrredundant (s : Solver) (ref : Ref) : Solver :=
  if s.lastIrredundant != INVALID_REF && ref ≤ s.lastIrredundant then s
  else if UInt32.ofNat s.arena.sizeWards ≤ ref then { s with lastIrredundant := INVALID_REF }
  else { s with lastIrredundant := ref }

/-! ### `bump.c` -/

def MAX_SCORE : Float := 1e150

/-- `kissat_rescale_scores` (bump.c) on the score heap and increment. -/
def rescalePair (scores : Heap) (scinc : Float) : Heap × Float :=
  -- INC (rescaled): METRIC
  let maxScore := scores.maxScore
  let rescale := if maxScore < scinc then scinc else maxScore   -- MAX (a, b)
  let factor := 1.0 / rescale
  (scores.rescale factor, scinc * factor)

/-- Port of `kissat_rescale_scores` (bump.c). -/
def rescaleScores (s : Solver) : Solver :=
  let (scores, scinc) := rescalePair s.scores s.scinc
  { s with scores := scores, scinc := scinc }

/-- `kissat_bump_score_increment` (bump.c) on the score heap and increment. -/
def bumpIncPair (decayOpt : Nat) (scores : Heap) (scinc : Float) : Heap × Float :=
  let decay := (UInt64.ofNat decayOpt).toFloat * 1e-3
  let factor := 1.0 / (1.0 - decay)
  let newScinc := scinc * factor
  if newScinc > MAX_SCORE then rescalePair scores newScinc else (scores, newScinc)

/-- Port of `kissat_bump_score_increment` (bump.c). -/
def bumpScoreIncrement (s : Solver) : Solver :=
  let (scores, scinc) := bumpIncPair s.options.decay s.scores s.scinc
  { s with scores := scores, scinc := scinc }

/-- `bump_analyzed_variable_score` (bump.c) on the score heap and increment. -/
def bumpVarPair (scores : Heap) (scinc : Float) (idx : UInt32) : Heap × Float :=
  let oldScore := scores.getScore idx
  let newScore := oldScore + scinc
  let scores := scores.update idx newScore
  if newScore > MAX_SCORE then rescalePair scores scinc else (scores, scinc)

/-- Port of `bump_analyzed_variable_score` (bump.c). -/
def bumpVariableScore (s : Solver) (idx : UInt32) : Solver :=
  let (scores, scinc) := bumpVarPair s.scores s.scinc idx
  { s with scores := scores, scinc := scinc }

/-- The loop of `bump_analyzed_variable_scores` over `analyzed[i..n)`. -/
def bumpScoresLoop (s : Solver) (scores : Heap) (scinc : Float) (i n : Nat) : Heap × Float :=
  if _h : i < n then
    let idx := s.analyzed.get! i
    let (scores, scinc) := if s.isActive idx then bumpVarPair scores scinc idx else (scores, scinc)
    s.bumpScoresLoop scores scinc (i + 1) n
  else (scores, scinc)
termination_by n - i

/-- Port of `bump_analyzed_variable_scores` (bump.c). -/
def bumpAnalyzedVariableScores (s : Solver) : Solver :=
  let (scores, scinc) := s.bumpScoresLoop s.scores s.scinc 0 s.analyzed.size
  let (scores, scinc) := bumpIncPair s.options.decay scores scinc
  { s with scores := scores, scinc := scinc }

/-- Port of `move_analyzed_variables_to_front_of_queue` (bump.c). Stamps are
  unique, so any correct sort yields C's order. -/
def moveAnalyzedToFront (s : Solver) : Solver :=
  let ranks := (Array.range s.analyzed.size).map (fun i =>
    let idx := s.analyzed.get! i
    (idx, s.queue.linkStamp idx))
  let sorted := ranks.qsort (fun a b => a.2 < b.2)
  let q := sorted.foldl (fun q (x : UInt32 × UInt32) =>
    if s.isActive x.1 then q.moveToFront x.1 (s.value (LIT x.1) != 0) else q) s.queue
  { s with queue := q }

/-- Port of `kissat_bump_analyzed` (bump.c). -/
def bumpAnalyzed (s : Solver) : Solver :=
  if !s.stable then s.moveAnalyzedToFront else s.bumpAnalyzedVariableScores
  -- ADD (literals_bumped, ...): METRIC

/-- Port of `kissat_update_scores` (bump.c). -/
def updateScoresLoop (n : Nat) (s : Solver) (i : Nat) : Solver :=
  if i < n then
    let idx := UInt32.ofNat i
    let s := if s.isActive idx && !s.scores.contains idx then { s with scores := s.scores.push idx } else s
    updateScoresLoop n s (i + 1)
  else s
termination_by n - i

def updateScores (s : Solver) : Solver := updateScoresLoop s.vars.toNat s 0

end Solver
end LeanKissat
