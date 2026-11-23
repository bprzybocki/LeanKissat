import LeanKissat.Frontend.Parse
import LeanKissat.Frontend.Options
import LeanKissat.Frontend.Output
import LeanKissat.Search.Api

/-! Native phase timings for the plain search path. Run with a CNF and conflict limit.
The extra clock calls make these diagnostic timings unsuitable for end-to-end comparisons.
The driver below mirrors `Solver.search`; keep the two in step (compare the printed counters
with `lkissat --statistics`). -/

open LeanKissat LeanKissat.Frontend

namespace PhaseBench

structure Cost where
  nanos : UInt64 := 0
  allocations : Nat := 0

structure Times where
  propagation : Cost := {}
  analysis : Cost := {}
  decisions : Cost := {}
  reduction : Cost := {}
  restart : Cost := {}
  other : Cost := {}
  conflictLevel : Cost := {}
  deduction : Cost := {}
  minimization : Cost := {}
  learning : Cost := {}
  bumpCleanup : Cost := {}
  failedLiteral : Cost := {}
  steps : Nat := 0

@[specialize] def timed {α : Type} (f : Solver → α) (s : Solver) (total : Cost) :
    IO (α × Cost) := do
  let before ← IO.getNumHeartbeats
  let start ← IO.monoNanosNow
  let result := f s
  let stop ← IO.monoNanosNow
  let after ← IO.getNumHeartbeats
  return (result, { nanos := total.nanos + UInt64.ofNat (stop - start),
                    allocations := total.allocations + after - before })

def finishAnalysis (s : Solver) (t : Times) : IO (Solver × Times) := do
  let (s, ns) ← timed Solver.finishAnalysis s t.bumpCleanup
  return (s, { t with bumpCleanup := ns })

def analyze (s : Solver) (c : CRef) (t : Times) : IO (UInt32 × Solver × Times) := do
  if s.inconsistent then return (20, s, t)
  let s := if !s.probing then s.updateAnalysisAverages else s
  let ((forced, level, s), ns) ← timed (fun s => s.oneLiteralOnConflictLevel c) s t.conflictLevel
  let t := { t with conflictLevel := ns }
  if forced then
    let (s, t) ← finishAnalysis s t
    return (0, s, t)
  if level == 0 then
    let (s, t) ← finishAnalysis s t
    return (20, s, t)
  if level == 1 then
    let (s, ns) ← timed (fun s => s.analyzeFailedLiteral c) s t.failedLiteral
    let (s, t) ← finishAnalysis s { t with failedLiteral := ns }
    return (0, s, t)
  let ((conflict, s), ns) ← timed (fun s => s.deduceFirstUipClause c) s t.deduction
  let t := { t with deduction := ns }
  if conflict.isSome then throw (IO.userError "phasebench requires otfs=0")
  if s.overflowed then
    let (s, t) ← finishAnalysis s t
    return (0, s, t)
  let (s, ns) ← timed Solver.minimizeDeduced s t.minimization
  let t := { t with minimization := ns }
  let (s, t) ← if s.overflowed then pure (s, t) else do
    let (s, ns) ← timed
      (fun s => s.analyzeReasonSideLiterals.learnClause.resetAnalysisButNotAnalyzedLiterals)
      s t.learning
    pure (s, { t with learning := ns })
  let (s, t) ← finishAnalysis s t
  return (0, s, t)

def step (s : Solver) (t : Times) : IO (Option UInt32 × Solver × Times) := do
  let ((s, conflict), ns) ← timed Solver.searchPropagate s t.propagation
  let t := { t with propagation := ns, steps := t.steps + 1 }
  match conflict with
  | some c =>
    let before ← IO.getNumHeartbeats
    let start ← IO.monoNanosNow
    let (res, s, t) ← analyze s c t
    let stop ← IO.monoNanosNow
    let after ← IO.getNumHeartbeats
    let ns : Cost :=
      { nanos := t.analysis.nanos + UInt64.ofNat (stop - start)
        allocations := t.analysis.allocations + after - before }
    return (if res != 0 then some res else none, s, { t with analysis := ns })
  | none =>
    if s.iterating then return (none, { s with iterating := false }, t)
    if s.asg.unassigned == 0 then return (some 10, s, t)
    if s.terminationFlagged then return (some 0, s, t)
    if s.reducing then
      let ((res, s), ns) ← timed Solver.reduce s t.reduction
      return (if res != 0 then some res else none, s, { t with reduction := ns })
    let ((r, s), ns) ← timed Solver.restarting s t.other
    let t := { t with other := ns }
    if r then
      let (s, ns) ← timed Solver.restart s t.restart
      return (none, s, { t with restart := ns })
    if s.conflictLimitHit || s.decisionLimitHit then return (some 0, s, t)
    let (s, ns) ← timed Solver.decide s t.decisions
    return (none, s, { t with decisions := ns })

def loop (s : Solver) (t : Times) : Nat → IO (UInt32 × Solver × Times)
  | 0 => return (0, s, t)
  | fuel + 1 => do
    if s.overflowed || s.outOfResources || s.notPorted ||
        s.stats.conflicts ≥ Solver.CONFLICT_CAP then return (0, s, t)
    let (res, s, t) ← step s t
    match res with
    | some r => return (r, s, t)
    | none => loop s t fuel

def millis (c : Cost) : Float := c.nanos.toFloat / 1000000.0

end PhaseBench

def main (args : List String) : IO UInt32 := do
  let [path, limit] := args
    | IO.eprintln "usage: phasebench file.cnf conflict-limit"; return 1
  let some limit := limit.toNat?
    | IO.eprintln "invalid conflict limit"; return 1
  let opts := setConfiguration {} "plain"
  let sink : DimacsSink Solver :=
    { header := fun s vars _ => s.reserve vars.toNat
      add := fun s lit => s.add lit.toInt }
  let start ← IO.monoNanosNow
  let startAlloc ← IO.getNumHeartbeats
  let outcome ← parseFile (some path) .normal sink (Solver.init opts)
  let parsed ← IO.monoNanosNow
  let parsedAlloc ← IO.getNumHeartbeats
  let .ok r := outcome
    | IO.eprintln "parse error"; return 1
  let s := r.sink.setConflictLimit limit
  let (res, s) := if s.inconsistent then (20, s) else
    if opts.luckyearly != 0 then s.lucky else (0, s)
  let (res, s) := if res == 0 && opts.luckylate != 0 then s.lucky else (res, s)
  let lucky ← IO.monoNanosNow
  let searchAlloc ← IO.getNumHeartbeats
  let (res, s, t) ← if res != 0 then pure (res, s, ({} : PhaseBench.Times)) else
    PhaseBench.loop s.classify.startSearch {} 100000000
  let stop ← IO.monoNanosNow
  let stopAlloc ← IO.getNumHeartbeats
  IO.println s!"parse_ms {(parsed - start).toFloat / 1000000.0}"
  IO.println s!"lucky_ms {(lucky - parsed).toFloat / 1000000.0}"
  IO.println s!"search_ms {(stop - lucky).toFloat / 1000000.0}"
  IO.println s!"parse_small_allocations {parsedAlloc - startAlloc}"
  IO.println s!"search_small_allocations {stopAlloc - searchAlloc}"
  IO.println s!"propagation_ms {PhaseBench.millis t.propagation}"
  IO.println s!"analysis_ms {PhaseBench.millis t.analysis}"
  IO.println s!"decisions_ms {PhaseBench.millis t.decisions}"
  IO.println s!"reduction_ms {PhaseBench.millis t.reduction}"
  IO.println s!"restart_ms {PhaseBench.millis t.restart}"
  IO.println s!"other_ms {PhaseBench.millis t.other}"
  IO.println s!"conflict_level_ms {PhaseBench.millis t.conflictLevel}"
  IO.println s!"deduction_ms {PhaseBench.millis t.deduction}"
  IO.println s!"minimization_ms {PhaseBench.millis t.minimization}"
  IO.println s!"learning_ms {PhaseBench.millis t.learning}"
  IO.println s!"bump_cleanup_ms {PhaseBench.millis t.bumpCleanup}"
  IO.println s!"failed_literal_ms {PhaseBench.millis t.failedLiteral}"
  IO.println s!"propagation_small_allocations {t.propagation.allocations}"
  IO.println s!"analysis_small_allocations {t.analysis.allocations}"
  IO.println s!"deduction_small_allocations {t.deduction.allocations}"
  IO.println s!"minimization_small_allocations {t.minimization.allocations}"
  IO.println s!"learning_small_allocations {t.learning.allocations}"
  IO.println s!"bump_cleanup_small_allocations {t.bumpCleanup.allocations}"
  IO.println s!"steps {t.steps}"
  let s := s.stopSearch
  let p ← Printer.new { opts with statistics := 1 }
  IO.println (statusLine (if res == 10 then .sat else if res == 20 then .unsat else .unknown))
  printStatistics p { opts with statistics := 1 } s.stats.toStats
    ((stop - start).toFloat / 1000000000.0)
  return res
