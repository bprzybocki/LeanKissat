import LeanKissat.Frontend.Parse
import LeanKissat.Frontend.Options
import LeanKissat.Frontend.Output
import LeanKissat.Frontend.SolverInterface
import LeanKissat.Search.Api

/-!
# `lkissat` — port of `application.c` (`kissat_application`, `run_application`)

Generic over the solver (`SolverInterface`); `main` instantiates the stub.
-/

open LeanKissat LeanKissat.Frontend

/-- Seconds since `start` (DEVIATION: wall-clock instead of process time). -/
def elapsed (start : Nat) : IO Float := do
  return ((← IO.monoNanosNow) - start).toFloat / 1.0e9

/-- Wait for `t` until the monotonic clock passes `deadline` (polling every 10 ms); `none` on timeout.
  Fuel bounds the loop: 10^9 polls are more than 300 years. -/
def waitUntil {α} (t : Task (Except IO.Error α)) (deadline : Nat) : Nat → IO (Option α)
  | 0 => pure none
  | fuel + 1 => do
    if ← IO.hasFinished t then return some (← IO.ofExcept t.get)
    if (← IO.monoNanosNow) ≥ deadline then return none
    IO.sleep 10
    waitUntil t deadline fuel

/-- Port of `run_application` (application.c). Returns the exit code. Specialised for
  the concrete solver so that `SolverInterface.add` is inlined into the parser loop. -/
@[specialize] def runApplication (σ : Type) [SolverInterface σ] (args : List String) : IO UInt32 := do
  let start ← IO.monoNanosNow
  let out ← IO.getStdout
  if let [arg] := args then
    if let some ls := singleOptionOutput arg then
      out.putStr (String.join (ls.map (· ++ "\n")))
      return 0
  let app ← match ← parseOptions args with
    | .error e => printError e; return 1
    | .ok app => pure app
  let o := app.options
  let p ← Printer.new o
  p.section "banner"
  if o.quiet == 0 then
    out.putStr (String.join ((bannerLines true).map (· ++ "\n")))
    out.flush
  -- parse_input
  let entered ← elapsed start
  let path := app.inputPath.getD "<stdin>"
  let stream? : Option IO.FS.Stream ← match app.inputPath with
    | none => pure (some (← IO.getStdin))
    | some ip =>
      try pure (some (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk ip .read)))
      catch _ => pure none
  let some stream := stream?
    | printError s!"failed to open '{path}' for reading"; return 1
  p.section "parsing"
  p.message "opened and reading DIMACS file:"
  p.line
  p.message s!"  {path}"
  p.line
  let sink : DimacsSink σ :=
    { header := fun s vars _ => SolverInterface.reserve s vars.toNat
      add := SolverInterface.add }
  let outcome ← parseStream stream app.strict sink (SolverInterface.init o)
  let printHeader (h : DimacsHeader) : IO Unit :=
    p.message s!"parsed 'p cnf {h.variables} {h.clauses}' header"
  let r ← match outcome with
    | .error e header _ =>
      if let some h := header then printHeader h
      printError (e.render path)
      return 1
    | .ok r => printHeader r.header; pure r
  p.message s!"closing input after reading {formatBytes r.bytes}"
  p.message s!"finished parsing after {fmtFixed ((← elapsed start) - entered) 2} seconds"
  printOptions p o
  printLimits p app
  p.section "solving"
  let limits : Frontend.Limits :=
    { conflicts := if app.conflicts ≥ 0 then some app.conflicts.toNat else none
      decisions := if app.decisions ≥ 0 then some app.decisions.toNat else none
      time := if app.time > 0 then some app.time else none }
  -- `--time`: C arms `alarm` and `kissat_terminate`s the search. The search here is pure, so it
  -- runs on a dedicated thread and the main thread stops waiting at the deadline (DEVIATION:
  -- on timeout no statistics are printed, and the process exits without the final messages).
  let some (res, solver) ← (match limits.time with
    | none => some <$> SolverInterface.solve r.sink limits
    | some secs => do
      let solveTask ← IO.asTask (SolverInterface.solve r.sink limits) .dedicated
      let deadline := start + secs * 1000000000
      waitUntil solveTask deadline 1000000000)
    | do
      p.section "result"
      out.putStr (statusLine .unknown ++ "\n")
      out.flush
      p.message "terminated by time limit"
      IO.Process.exit 0
  p.section "result"
  out.putStr (statusLine res ++ "\n")
  out.flush
  if res == .sat && app.witness then
    printWitness (SolverInterface.value solver) r.header.variables.toNat app.partialWitness
  printStatistics p o (SolverInterface.statistics solver) (← elapsed start)
  p.section "shutting down"
  p.message s!"exit {res.code}"
  return res.code.toUInt32

def main (args : List String) : IO UInt32 := do
  let code ← runApplication LeanKissat.Solver args
  -- exit explicitly: with `--time`, a solver thread may still be running
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
