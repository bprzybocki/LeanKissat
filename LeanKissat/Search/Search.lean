import LeanKissat.Search.Init

/-
Search loop (`search.c`), limits initialization (`kimits.c`), restarts
(`restart.c`), mode switching (`mode.c`), classification (`classify.c`).
Scheduled procedures that are not ported yet set `notPorted` and stop the
search with `unknown`.
-/
namespace LeanKissat
namespace Solver

/-! ### `classify.c` -/

/-- Port of `kissat_classify` (classify.c). -/
def classify (s : Solver) : Solver :=
  let clauses := s.stats.clauses_binary + s.stats.clauses_irredundant
  if clauses ≤ UInt64.ofNat s.options.smallclauses then
    { s with classification := { small := true, bigbig := false } }
  else
    let percent := (UInt64.ofNat s.options.bigbigfraction).toFloat / 1000.0
    let actual := kissatPercent s.stats.clauses_binary.toFloat clauses.toFloat
    { s with classification := { small := false, bigbig := actual ≥ percent } }

/-! ### `kimits.c` -/

/-- Port of `init_enabled` (kimits.c). -/
def initEnabled (s : Solver) : Solver :=
  let o := s.options
  let probe :=
    if o.simplify == 0 then false
    else if o.probe == 0 then false
    else o.substitute != 0 || o.sweep != 0 || o.vivify != 0
  let eliminate := o.simplify != 0 && o.eliminate != 0
  { s with enabled := { s.enabled with probe := probe, eliminate := eliminate } }

/-- `INIT_CONFLICT_LIMIT (NAME, SCALE)` (kimits.c). -/
def initConflictLimit (s : Solver) (init : Nat) (scale : Bool) : UInt64 × Solver :=
  let delta : UInt64 := UInt64.ofNat init
  let scaled := if scale then s.scaleDelta delta else delta
  s.conflictsPlus scaled

/-- Port of `kissat_update_focused_restart_limit` (restart.c). -/
def updateFocusedRestartLimit (s : Solver) : Solver :=
  let restarts := s.stats.restarts
  let delta : UInt64 := UInt64.ofNat s.options.restartint
  let delta := if restarts != 0 then (delta.toFloat + (kLogn restarts - 1)).toUInt64 else delta
  -- CLAMP: `restartint ≥ 1` and `logn ≥ 1`, so C's delta is ≥ 1.
  let delta := max delta 1
  let (lim, s) := s.conflictsPlus delta
  { s with limits := { s.limits with restartConflicts := lim } }

/-- Port of `kissat_init_mode_limit` (mode.c). -/
def initModeLimit (s : Solver) : Solver :=
  if s.options.stable == 1 then
    let (lim, s) := s.conflictsPlus (UInt64.ofNat s.options.modeinit)
    let s := { s with limits := { s.limits with modeConflicts := lim, modeTicks := 0, modeCount := 0 } }
    { s with mode := { s.mode with ticks := s.stats.search_ticks, conflicts := s.stats.conflicts } }
  else s

/-- `INIT_CONFLICT_LIMIT` for one limit (kimits.c). -/
@[inline] def initLimitWith (s : Solver) (enabled : Bool) (init : Nat) (scale : Bool)
    (set : UInt64 → Solver → Solver) : Solver :=
  if enabled then
    let (l, s') := s.initConflictLimit init scale
    set l s'
  else s

/-- Port of `kissat_init_limits` (kimits.c). -/
def initLimits (s : Solver) : Solver :=
  let s := s.initEnabled
  let o := s.options
  let s := s.initLimitWith (o.randec != 0) o.randecinit false
    (fun l s => { s with limits := { s.limits with randecConflicts := l } })
  let s := s.initLimitWith (o.reduce != 0) o.reduceinit false
    (fun l s => { s with limits := { s.limits with reduceConflicts := l } })
  let s := s.initLimitWith (o.reorder != 0) o.reorderinit false
    (fun l s => { s with limits := { s.limits with reorderConflicts := l } })
  let s := s.initLimitWith (o.rephase != 0) o.rephaseinit false
    (fun l s => { s with limits := { s.limits with rephaseConflicts := l } })
  let s := if !s.stable then s.updateFocusedRestartLimit else s
  let s := s.initModeLimit
  let s := s.initLimitWith s.enabled.eliminate o.eliminateinit true
    (fun l s => { s with limits := { s.limits with eliminateConflicts := l },
                         bounds := { eliminateMaxBoundCompleted := 0, eliminateAdditionalClauses := 0 } })
  s.initLimitWith s.enabled.probe o.probeinit true
    (fun l s => { s with limits := { s.limits with probeConflicts := l } })

/-! ### `restart.c` -/

/-- Port of `kissat_restarting` (restart.c). -/
def restarting (s : Solver) : Bool × Solver :=
  if s.options.restart == 0 then (false, s)
  else if s.level == 0 then (false, s)
  else if s.stats.conflicts < s.limits.restartConflicts then (false, s)
  else if s.stable then
    let (t, r) := s.reluctant.triggered
    (t, { s with reluctant := r })
  else
    let fast := s.averagesCur.fastGlue.value
    let slow := s.averagesCur.slowGlue.value
    let margin := (100.0 + (UInt64.ofNat s.options.restartmargin).toFloat) / 100.0
    let limit := margin * slow
    (limit ≤ fast, s)

/-- `reuse_stable_trail` / `reuse_focused_trail` (restart.c). -/
def reuseTrail (s : Solver) : UInt32 × Solver := Id.run do
  if s.options.restartreusetrail == 0 then return (0, s)
  let (nextIdx, s) := s.nextDecisionVariable
  let level := s.level
  let mut res : UInt32 := 0
  if s.stable then
    let limit := s.scores.getScore nextIdx
    for _ in [0:level.toNat] do
      let idx := IDX (s.frameDecisionAt (res + 1))
      if s.scores.getScore idx ≤ limit then break
      res := res + 1
  else
    let limit := s.queue.linkStamp nextIdx
    for _ in [0:level.toNat] do
      let idx := IDX (s.frameDecisionAt (res + 1))
      if s.queue.linkStamp idx ≤ limit then break
      res := res + 1
  -- restarts_reused_trails / restarts_reused_levels: STATISTIC/METRIC
  return (res, s)

/-- Port of `kissat_restart` (restart.c). -/
def restart (s : Solver) : Solver :=
  let s := INC! s restarts
  -- restarts_levels: METRIC; {stable,focused}_restarts: COUNTER?
  let (level, s) := s.reuseTrail
  let s := s.backtrackInConsistentState level
  if !s.stable then s.updateFocusedRestartLimit else s

/-! ### `mode.c` -/

/-- Port of `kissat_init_reluctant` (reluctant.c). -/
def initReluctant (s : Solver) : Solver :=
  let r := s.reluctant.initFromOptions (s.options.reluctant != 0)
    s.options.reluctantint s.options.reluctantlim
  { s with reluctant := r }

/-- Port of `kissat_init_averages` (averages.c) for the current mode. -/
def initAverages (s : Solver) : Solver :=
  s.modifyAverages (·.init s.options.emafast s.options.emaslow)

/-- Port of `update_mode_limit` (mode.c). -/
def updateModeLimit (s : Solver) (deltaTicks : UInt64) : Solver :=
  let s := s.initAverages
  let s :=
    if s.limits.modeCount &&& 1 != 0 then
      let (t, o) := addOverflow s.stats.search_ticks deltaTicks
      let s := if o then { s with overflowed := true } else s
      { s with limits := { s.limits with modeTicks := t } }
    else
      let interval := UInt64.ofNat s.options.modeint
      let count := (s.stats.switched + 1) / 2
      let scaled := (interval.toFloat * kNlogpown count 4).toUInt64
      -- CLAMP: `modeint ≥ 10` and `nlog⁴n ≥ 1`.
      let scaled := max scaled 1
      let (lim, s) := s.conflictsPlus scaled
      { s with limits := { s.limits with modeConflicts := lim } }
  { s with mode := { s.mode with ticks := s.stats.search_ticks, conflicts := s.stats.conflicts } }

/-- Port of `kissat_switching_search_mode` (mode.c). -/
def switchingSearchMode (s : Solver) : Bool :=
  if s.options.stable != 1 then false
  else if s.limits.modeCount &&& 1 != 0 then s.stats.search_ticks ≥ s.limits.modeTicks
  else s.stats.conflicts ≥ s.limits.modeConflicts

/-- Port of `kissat_switch_search_mode` (mode.c). -/
def switchSearchMode (s : Solver) : Solver :=
  let s := INC! s switched
  let s := { s with limits := { s.limits with modeCount := s.limits.modeCount + 1 } }
  let deltaTicks := s.stats.search_ticks - s.mode.ticks
  let s :=
    if s.stable then
      -- switch_to_focused_mode
      let s := { s with stable := false }
      let s := s.updateModeLimit deltaTicks
      let s := { s with queue := s.queue.resetSearch }
      s.updateFocusedRestartLimit
    else
      -- switch_to_stable_mode
      let s := { s with stable := true }
      let s := s.updateModeLimit deltaTicks
      s.initReluctant.updateScores
  let s := s.modifyAverages fun a => { a with savedDecisions := s.stats.decisions }
  s.startRandomSequence

/-! ### `search.c` -/

/-- `init_tiers` (search.c). -/
def initTier (s : Solver) (st : Nat) : Solver :=
  if s.tier1[st]! == 0 then
    let t1 := UInt32.ofNat s.options.tier1
    let t2 := UInt32.ofNat s.options.tier2
    let t2 := if t2 ≤ t1 then t1 else t2
    let s := { s with tier1 := s.tier1.set! st t1, tier2 := s.tier2.set! st t2 }
    if s.limits.glueInterval == 0 then { s with limits := { s.limits with glueInterval := 2 } } else s
  else s

def initTiers (s : Solver) : Solver := (s.initTier 0).initTier 1

/-- `INC (searches)` and the initial mode (part of `start_search`). -/
def searchesInc (s : Solver) : Solver :=
  let s := INC! s searches
  { s with stable := s.options.stable == 2 }

/-- Stable-mode initialization (part of `start_search`). -/
def stableInit (s : Solver) : Solver := if s.stable then s.initReluctant.updateScores else s

/-- Seed the random number generator (part of `start_search`). -/
def setSeed (s : Solver) : Solver := { s with random := UInt64.ofNat s.options.seed }

/-- Port of `start_search` (search.c). -/
def startSearch (s : Solver) : Solver :=
  (((((s.searchesInc.initAverages).classify).stableInit).initTiers).initLimits).setSeed

/-- Port of `stop_search` (search.c). -/
def stopSearch (s : Solver) : Solver :=
  { s with limited := {}, terminationFlagged := false, stable := false }

/-- `conflict_limit_hit` (search.c). -/
@[inline] def conflictLimitHit (s : Solver) : Bool :=
  s.limited.conflicts && s.limits.conflicts ≤ s.stats.conflicts

/-- `decision_limit_hit` (search.c). -/
@[inline] def decisionLimitHit (s : Solver) : Bool :=
  s.limited.decisions && s.limits.decisions ≤ s.stats.decisions

/-- `searching` (search.c). -/
def searching (s : Solver) : Bool :=
  if !s.propagated then true
  else if s.options.probeinit == 0 then true
  else if s.options.eliminateinit == 0 then true
  else !s.conflictLimitHit

/-- Port of `kissat_reducing` (reduce.c). -/
def reducing (s : Solver) : Bool :=
  s.options.reduce != 0 && s.stats.clauses_redundant != 0 &&
    s.stats.conflicts ≥ s.limits.reduceConflicts

/-- Port of `kissat_reordering` (reorder.c). -/
def reordering (s : Solver) : Bool :=
  if s.options.reorder == 0 then false
  else if !s.stable && s.options.reorder < 2 then false
  else if s.level != 0 then false
  else s.stats.conflicts ≥ s.limits.reorderConflicts

/-- Port of `kissat_rephasing` (rephase.c). -/
def rephasing (s : Solver) : Bool :=
  s.options.rephase != 0 && s.stable && s.stats.conflicts > s.limits.rephaseConflicts

/-- Port of `kissat_probing` (probe.c). -/
def probingP (s : Solver) : Bool :=
  if !s.enabled.probe then false
  else if s.last.conflictsReduce == s.stats.conflicts then false
  else s.limits.probeConflicts < s.stats.conflicts

/-- Port of `kissat_eliminating` (eliminate.c). -/
def eliminating (s : Solver) : Bool :=
  if !s.enabled.eliminate then false
  else if s.stats.clauses_irredundant == 0 then false
  else if s.last.conflictsReduce == s.stats.conflicts then false
  else if s.limits.eliminateConflicts > s.stats.conflicts then false
  else if s.limits.eliminateVariablesEliminate < s.stats.variables_eliminate then true
  else s.limits.eliminateVariablesSubsume < s.stats.variables_subsume

/-- Hooks for procedures ported in later phases. They are set by modules that
  are imported after this one; until then the search stops with `unknown`. -/
structure Procedures where
  reduce : Solver → UInt32 × Solver := fun s => (0, { s with notPorted := true })
  reorder : Solver → Solver := fun s => { s with notPorted := true }
  rephase : Solver → Solver := fun s => { s with notPorted := true }
  probe : Solver → UInt32 × Solver := fun s => (0, { s with notPorted := true })
  eliminate : Solver → UInt32 × Solver := fun s => (0, { s with notPorted := true })
  preprocess : Solver → UInt32 × Solver := fun s => (0, { s with notPorted := true })

/-- One iteration of the `while (!res)` loop in `kissat_search`.
  Returns `some res` to stop the loop (`res` may be 0 for `break`). -/
def searchStep (P : Procedures) (s : Solver) : Option UInt32 × Solver :=
  let (s, conflict) := s.searchPropagate
  match conflict with
  | some c =>
    let (res, s) := s.analyze c
    if res != 0 then (some res, s) else (none, s)
  | none =>
    if s.iterating then (none, { s with iterating := false })
    else if s.asg.unassigned == 0 then (some 10, s)
    else if s.terminationFlagged then (some 0, s)
    else if s.reducing then
      let (res, s) := P.reduce s
      if res != 0 then (some res, s) else (none, s)
    else if s.switchingSearchMode then (none, s.switchSearchMode)
    else
      let (r, s) := s.restarting
      if r then (none, s.restart)
      else if s.reordering then (none, P.reorder s)
      else if s.rephasing then (none, P.rephase s)
      else if s.probingP then
        let (res, s) := P.probe s
        if res != 0 then (some res, s) else (none, s)
      else if s.eliminating then
        let (res, s) := P.eliminate s
        if res != 0 then (some res, s) else (none, s)
      else if s.conflictLimitHit then (some 0, s)
      else if s.decisionLimitHit then (some 0, s)
      else (none, s.decide)

/-- Conflict cap: the search stops with `unknown` (setting `overflowed`) when the
  conflict counter reaches `2^62` (C would eventually wrap around at `2^64`). -/
def CONFLICT_CAP : UInt64 := 0x4000000000000000

/-- Upper bound on the number of loop iterations without a new conflict.
  Between two conflicts every scheduled procedure fires at most twice (its limit
  moves beyond the current conflict count), and between two backtracking
  procedures there are at most `vars` decisions. -/
def stepBound (s : Solver) : Nat := 32 * (s.vars.toNat + 2)

/-- The search loop (`while (!res)` in `kissat_search`).
  Termination: the measure `(CONFLICT_CAP - conflicts, bound - steps)` decreases
  lexicographically in every iteration. `steps` counts iterations since the last
  conflict and `bound = stepBound` at that time. The two guards below (conflict
  counter decreasing, too many steps without a conflict) are never hit by Kissat's
  scheduling (see `Proofs/Termination.lean`); if they were, the search would stop
  with `unknown` (flagging `overflowed`), which keeps the result sound. -/
def searchLoop (P : Procedures) (s : Solver) (bound steps : Nat) : UInt32 × Solver :=
  if s.overflowed || s.outOfResources || s.notPorted then (0, s) else
  if _hc : s.stats.conflicts ≥ CONFLICT_CAP then (0, { s with overflowed := true }) else
  match searchStep P s with
  | (some res, s') => (res, s')
  | (none, s') =>
    if h1 : s'.stats.conflicts > s.stats.conflicts then
      searchLoop P s' (stepBound s') 0
    else if s'.stats.conflicts < s.stats.conflicts then (0, { s' with overflowed := true })
    else if h3 : steps < bound then searchLoop P s' bound (steps + 1)
    else (0, { s' with overflowed := true })
termination_by (CONFLICT_CAP.toNat - s.stats.conflicts.toNat, bound - steps)
decreasing_by
  · apply Prod.Lex.left
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, Nat.not_le] at h1 _hc
    omega
  · simp only [UInt64.lt_iff_toNat_lt, gt_iff_lt] at *
    have he : s'.stats.conflicts.toNat = s.stats.conflicts.toNat := by omega
    rw [he]
    apply Prod.Lex.right
    omega

/-- Port of `kissat_search` (search.c). -/
def search (P : Procedures) (s : Solver) : UInt32 × Solver :=
  if s.inconsistent then (20, s) else
  match (if s.options.luckyearly != 0 then s.lucky else (0, s)) with
  | (res, s) =>
    if res != 0 then (res, s) else
    match (if s.options.preprocess != 0 && s.options.probe != 0 && s.options.preprocessprobe != 0 then
        P.preprocess s else (0, s)) with
    | (res, s) =>
      if res != 0 then (res, s) else
      match (if s.options.luckylate != 0 then s.lucky else (0, s)) with
      | (res, s) =>
        if res != 0 then (res, s) else
        let s := s.classify
        if s.searching then
          let s := s.startSearch
          match searchLoop P s (stepBound s) 0 with
          | (r, s') => (r, s'.stopSearch)
        else (0, s)

end Solver
end LeanKissat
