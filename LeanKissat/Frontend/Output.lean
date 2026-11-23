import LeanKissat.Core.StatsTable
import LeanKissat.Frontend.Options
import LeanKissat.Frontend.SolverInterface

/-!
# User visible output

* `printf`-style number formatting (`%.Nf` with exact round-half-even like the C
  library, field widths),
* messages / sections (`print.c`),
* witness printing (`witness.c`) and the status line (`application.c`),
* statistics (`statistics.c`, `kissat_print_statistics` in `internal.c`), glue usage
  (`tiers.c`) and resources (`resources.c`),
* banner and version information (`build.c`), option and limit listings
  (`application.c`).

DEVIATION: colors are never used (C uses them only when connected to a terminal).
DEVIATION: there is no process-time or resident-set-size API in Lean without FFI;
  "process time" is wall-clock time since start, the maximum resident set size is `0`.
-/

namespace LeanKissat.Frontend

open LeanKissat

/-! ## Number formatting -/

/-- `s` right-aligned in a field of width `w` (`%<w>s`). -/
def padLeft (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else "".pushn ' ' (w - s.length) ++ s

/-- `s` left-aligned in a field of width `w` (`%-<w>s`). -/
def padRight (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s.pushn ' ' (w - s.length)

/-- `printf ("%.<prec>f", x)`: exact decimal expansion of the binary64 value rounded
  half-to-even, as done by glibc and the macOS libc. -/
def fmtFixed (x : Float) (prec : Nat) : String :=
  if x.isNaN then "nan"
  else if x.isInf then (if x < 0 then "-inf" else "inf")
  else
    let bits := x.toBits
    let neg := (bits >>> 63) == 1
    let e := ((bits >>> 52) &&& 0x7FF).toNat
    let f := (bits &&& 0xFFFFFFFFFFFFF).toNat
    let (m, ex) : Nat × Int := if e == 0 then (f, -1074) else (f + 2 ^ 52, (e : Int) - 1075)
    let scale := 10 ^ prec
    let n : Nat :=
      if ex ≥ 0 then m * 2 ^ ex.toNat * scale
      else
        let num := m * scale
        let den := 2 ^ (-ex).toNat
        let qt := num / den
        let r := num % den
        if 2 * r > den then qt + 1
        else if 2 * r == den then (if qt % 2 == 1 then qt + 1 else qt)
        else qt
    let digits := toString n
    let body :=
      if prec == 0 then digits
      else
        let digits := if digits.length ≤ prec then "".pushn '0' (prec + 1 - digits.length) ++ digits
          else digits
        let k := digits.length - prec
        (digits.take k).toString ++ "." ++ (digits.drop k).toString
    if neg then "-" ++ body else body

/-- `%<w>.<prec>f`. -/
def fmtF (x : Float) (w prec : Nat) : String := padLeft (fmtFixed x prec) w

/-- `kissat_average` (utilities.h). -/
@[inline] def average (a b : Float) : Float := if b != 0 then a / b else 0.0

/-- `kissat_percent` (utilities.h). -/
@[inline] def percent (a b : Float) : Float := average (100.0 * a) b

/-- Port of `kissat_format_bytes` (format.c). -/
def formatBytes (bytes : Nat) : String :=
  if bytes < 1 <<< 10 then s!"{bytes} bytes"
  else if bytes < 1 <<< 20 then s!"{bytes} bytes ({(bytes + (1 <<< 9)) >>> 10} KB)"
  else if bytes < 1 <<< 30 then s!"{bytes} bytes ({(bytes + (1 <<< 19)) >>> 20} MB)"
  else s!"{bytes} bytes ({(bytes + (1 <<< 29)) >>> 30} GB)"

/-- C `round` (half away from zero) for non-negative values, as `Nat`. -/
private def roundNat (x : Float) : Nat := (x + 0.5).floor.toUInt64.toNat

/-- Port of `kissat_format_time` (format.c). -/
def formatTime (seconds : Float) : String :=
  if seconds == 0 then "0s"
  else
    let rounded := roundNat seconds
    let minutes := rounded / 60
    let rounded := rounded % 60
    let hours := minutes / 60
    let minutes := minutes % 60
    let days := hours / 24
    let hours := hours % 24
    let parts := (if days != 0 then [s!"{days}d"] else []) ++
      (if hours != 0 then [s!"{hours}h"] else []) ++
      (if minutes != 0 then [s!"{minutes}m"] else []) ++
      (if rounded != 0 then [s!"{rounded}s"] else [])
    " ".intercalate parts

/-! ## Messages (`print.c`) -/

/-- Message printer: verbosity (`-1` quiet) and whether a section was printed. -/
structure Printer where
  verbosity : Int
  sectioned : IO.Ref Bool

def PREFIX : String := "c "

/-- `verbosity` in `print.c`. -/
def verbosityOf (o : Options) : Int := if o.quiet != 0 then -1 else o.verbose

def Printer.new (o : Options) : IO Printer := do
  return { verbosity := verbosityOf o, sectioned := ← IO.mkRef false }

/-- `print_line`: the prefix without its trailing space. -/
def Printer.printLine (_ : Printer) : IO Unit := do
  let out ← IO.getStdout
  out.putStr "c\n" -- `PREFIX` without its trailing space
  out.flush

/-- `kissat_message`. -/
def Printer.message (p : Printer) (msg : String) : IO Unit := do
  if p.verbosity < 0 then return
  let out ← IO.getStdout
  out.putStr (PREFIX ++ msg ++ "\n")
  out.flush

/-- `kissat_verbose`. -/
def Printer.verbose (p : Printer) (msg : String) : IO Unit := do
  if p.verbosity < 1 then return
  let out ← IO.getStdout
  out.putStr (PREFIX ++ msg ++ "\n")
  out.flush

/-- `kissat_line`. -/
def Printer.line (p : Printer) : IO Unit := do
  if p.verbosity ≥ 0 then p.printLine

/-- `kissat_section`. -/
def Printer.section (p : Printer) (name : String) : IO Unit := do
  if p.verbosity < 0 then return
  if ← p.sectioned.get then p.line else p.sectioned.set true
  let out ← IO.getStdout
  out.putStr (PREFIX ++ "---- [ " ++ name ++ " ] " ++ "".pushn '-' (66 - name.length) ++ "\n")
  p.printLine

/-- `kissat_error`: `kissat: error: <msg>` on `<stderr>`. -/
def printError (msg : String) : IO Unit := do
  (← IO.getStdout).flush
  let err ← IO.getStderr
  err.putStr ("kissat: error: " ++ msg ++ "\n")
  err.flush

/-! ## Banner and build information (`build.c`) -/

def SOLVER_NAME : String := "Kissat SAT Solver"
def VERSION : String := "4.0.4"

/-- `kissat_copyright`. -/
def copyrightLines : List String :=
  ["Copyright (c) 2021-2024 Armin Biere University of Freiburg",
   "Copyright (c) 2019-2021 Armin Biere Johannes Kepler University Linz"]

/-- `kissat_id`. DEVIATION: no git id of the C sources; identifies the port. -/
def kissatId : String := "lean-port"

/-- `kissat_compiler`. DEVIATION: reports the Lean version. -/
def kissatCompiler : String := s!"Lean {Lean.versionString}"

/-- `kissat_build` lines. DEVIATION: no build date / host line. -/
def buildLines : List String := [s!"Version {VERSION} {kissatId}", kissatCompiler]

/-- `kissat_banner (prefix, name)`; `pre = ""` for `--banner`. -/
def bannerLines (withPrefix : Bool) : List String :=
  let pre := if withPrefix then PREFIX else ""
  [pre ++ SOLVER_NAME, pre] ++ copyrightLines.map (pre ++ ·) ++
    (if withPrefix then [pre] else []) ++ buildLines.map (pre ++ ·)

/-! ## Status line and witness (`application.c`, `witness.c`) -/

/-- The `s ...` status line. -/
def statusLine : SolveResult → String
  | .sat => "s SATISFIABLE"
  | .unsat => "s UNSATISFIABLE"
  | .unknown => "s UNKNOWN"

/-- Port of `kissat_print_witness` (witness.c): `v` lines wrapped as in C (a number is
  moved to the next line if the line content would exceed 77 characters). `value eidx`
  is `kissat_value`. Output is written in large blocks. -/
def printWitness (value : Int32 → Int32) (maxVar : Nat) (isPartial : Bool) : IO Unit := do
  let out ← IO.getStdout
  let mut buf : String := "v"
  let mut lineLen : Nat := 0
  for eidx in [1:maxVar+1] do
    let e : Int32 := (Int.ofNat eidx).toInt32
    let tmp := value e
    let tmp := if tmp == 0 && !isPartial then e else tmp
    if tmp != 0 then
      let s := " " ++ toString tmp.toInt
      if lineLen + s.length > 77 then
        buf := buf ++ "\nv"
        lineLen := 0
      buf := buf ++ s
      lineLen := lineLen + s.length
      if buf.utf8ByteSize > 65536 then
        out.putStr buf
        buf := ""
  if lineLen + 2 > 77 then
    buf := buf ++ "\nv"
  buf := buf ++ " 0\n"
  out.putStr buf
  out.flush

/-! ## Statistics (`statistics.c`) -/

/-- The secondary value of a counter: the `OTHER (NAME)` macros of `statistics.c` used
  by `COUNTER`s in the default build (no `STATISTICS`, so `PCNT_TICKS` and
  `PER_FLIPPED` are `-1`). `none` for an unknown macro name. -/
def secondaryValue (s : Stats) (time : Float) (other : String) (v : UInt64) : Option Float :=
  let f (x : UInt64) : Float := x.toFloat
  let rel (a b : UInt64) := average (f a) (f b)
  let pct (a b : UInt64) := percent (f a) (f b)
  let variables := s.variables_original
  match other with
  | "CONF_INT" => some (rel s.conflicts v)
  | "SWEEPS_PER_COMPLETED" => some (rel s.sweep v)
  | "NO_SECONDARY" => some 0
  | "PER_CLOSURE" => some (rel v s.closures)
  | "PER_CONFLICT" => some (rel v s.conflicts)
  | "PER_FLIPPED" => some (-1)
  | "PER_FORWARD_CHECK" => some (rel v s.forward_checks)
  | "PER_KITTEN_PROP" => some (rel v s.kitten_propagations)
  | "PER_KITTEN_SOLVED" => some (rel v s.kitten_solved)
  | "PER_SECOND" => some (average (f v) time)
  | "PER_VARIABLE" => some (rel v variables)
  | "PER_VIVIFICATION" => some (rel v s.vivifications)
  | "PER_VIVIFY_CHECK" => some (rel v s.vivify_checks)
  | "PER_WALKS" => some (rel v s.walks)
  | "PCNT_CLS_ADDED" => some (pct v s.clauses_added)
  | "PCNT_CLS_LEARNED" => some (pct v s.clauses_learned)
  | "PCNT_CLS_USED" => some (pct v s.clauses_used)
  | "PCNT_CONFLICTS" => some (pct v s.conflicts)
  | "PCNT_CONGRGATES" => some (pct v s.congruent_gates)
  | "PCNT_CONGRMATCHED" => some (pct v s.congruent_matched)
  | "PCNT_CONGRUENT" => some (pct v s.congruent)
  | "PCNT_ELIMINATED" => some (pct v s.eliminated)
  | "PCNT_KITTEN_SOLVED" => some (pct v s.kitten_solved)
  | "PCNT_PROPS" => some (pct v s.propagations)
  | "PCNT_STRENGTHENED" => some (pct v s.strengthened)
  | "PCNT_SUBSUMED" => some (pct v s.subsumed)
  | "PCNT_SUBSUMPTION_CHECK" => some (pct v s.subsumption_checks)
  | "PCNT_TICKS" => some (-1)
  | "PCNT_VARIABLES" => some (pct v variables)
  | "PCNT_VIVIFY_CHECK" => some (pct v s.vivify_checks)
  | "PCNT_VIVIFY_PROBES" => some (pct v s.vivify_probes)
  | "PCNT_WALKS" => some (pct v s.walks)
  | _ => none

-- every secondary macro used by a counter is known
#guard counterTable.all fun e => (secondaryValue {} 1.0 e.other 0).isSome

/-- `PRINT_STAT` (statistics.h): `c <name>:<pad 30> <value:12> <secondary> <type>`. -/
def formatStat (name : String) (primary : UInt64) (secondary : Float)
    (units type : Option String) : String :=
  let head := PREFIX ++ padRight (name ++ ":") 30 ++ " " ++ padLeft (toString primary) 12 ++ " "
  match type with
  | some ty =>
    if secondary ≥ 0 then
      let sec := match units with
        | some u => fmtF secondary 16 0 ++ " " ++ padRight u 2
        | none => fmtF secondary 19 2
      head ++ sec ++ " " ++ ty
    else head
  | none => head

/-- Port of `kissat_statistics_print` (statistics.c) for the `COUNTER`s. -/
def statisticsLines (s : Stats) (time : Float) (verbose : Bool) : List String :=
  counterTable.toList.filterMap fun e =>
    let v := e.get s
    if verbose || e.verbose == 0 || (e.verbose == 1 && v != 0) then
      let sec := (secondaryValue s time e.other v).getD (-1)
      some (formatStat e.name v sec e.units e.type)
    else none

/-! ## Glue usage (`tiers.c`) -/

def MAX_GLUE_USED : Nat := 127

/-- Port of `compute_tier_limits` (tiers.c). -/
def computeTierLimits (o : Options) (used : Array UInt64) : Nat × Nat := Id.run do
  let get (g : Nat) : UInt64 := used.getD g 0
  let mut total : UInt64 := 0
  for g in [0:MAX_GLUE_USED+1] do total := total + get g
  let mut tier1 : Int := -1
  let mut tier2 : Int := -1
  if total != 0 then
    let t1rel : Float := o.tier1relative.toFloat / 1000.0
    let t2rel : Float := o.tier2relative.toFloat / 1000.0
    let lim1 : UInt64 := (total.toFloat * t1rel).toUInt64
    let lim2 : UInt64 := (total.toFloat * t2rel).toUInt64
    let mut acc : UInt64 := 0
    let mut glue : Nat := 0
    for g in [0:MAX_GLUE_USED+1] do
      glue := g
      acc := acc + get g
      if acc ≥ lim1 then
        tier1 := g
        break
    let _ := glue
    if acc < lim2 then
      for g in [(tier1 + 1).toNat:MAX_GLUE_USED+1] do
        acc := acc + get g
        if acc ≥ lim2 then
          tier2 := g
          break
  if tier1 < 0 then
    tier1 := o.tier1
    tier2 := max o.tier2 o.tier1
  else if tier2 < 0 then
    tier2 := tier1
  return (tier1.toNat, tier2.toNat)

/-- `decimal_digits` (tiers.c). -/
private def decimalDigits (i : UInt64) : Nat := (toString i).length

/-- Port of `kissat_print_tier_usage_statistics` (tiers.c). -/
def tierUsageLines (o : Options) (used : Array UInt64) (stable : Bool) : List String := Id.run do
  let (tier1, tier2) := computeTierLimits o used
  let get (g : Nat) : UInt64 := used.getD g 0
  let mut total : UInt64 := 0
  for g in [0:MAX_GLUE_USED+1] do total := total + get g
  let mode := if stable then "stable" else "focused"
  let span := tier2 - tier1 + 1
  let maxPrinted := 5
  let (pfx, sfx) : Nat × Nat :=
    if span > maxPrinted then (tier1 + maxPrinted / 2 - 1, tier2 - maxPrinted / 2 + 1)
    else (0xFFFFFFFF, 0)
  let mut accMiddle : UInt64 := 0
  let mut glueDigits := 1
  let mut clausesDigits := 1
  for g in [0:MAX_GLUE_USED+1] do
    if g < tier1 then continue
    let u := get g
    let mut tg := 0
    let mut tc := 0
    if g ≤ pfx || sfx ≤ g then
      tg := decimalDigits g.toUInt64
      tc := decimalDigits u
    else
      accMiddle := accMiddle + u
      if g + 1 == sfx then
        tg := decimalDigits (pfx + 1).toUInt64 + decimalDigits g.toUInt64 + 1
        tc := decimalDigits accMiddle
    if tg > glueDigits then glueDigits := tg
    if tc > clausesDigits then clausesDigits := tc
    if g == tier2 then break
  let tf := total.toFloat
  accMiddle := 0
  let mut accumulated : UInt64 := 0
  let mut lines : Array String := #[]
  for g in [0:MAX_GLUE_USED+1] do
    let u := get g
    accumulated := accumulated + u
    if g < tier1 then continue
    let start := PREFIX ++ mode ++ " glue "
    if g ≤ pfx || sfx ≤ g then
      let mut l := start ++ padRight (toString g) glueDigits ++ " used " ++
        padLeft (toString u) clausesDigits ++
        s!" clauses {fmtF (percent u.toFloat tf) 5 2}% accumulated {fmtF (percent accumulated.toFloat tf) 5 2}%"
      if g == tier1 then l := l ++ " tier1"
      if g == tier2 then l := l ++ " tier2"
      lines := lines.push l
    else
      accMiddle := accMiddle + u
      if g + 1 == sfx then
        lines := lines.push (start ++ padRight s!"{pfx + 1}-{sfx - 1}" glueDigits ++ " used " ++
          padLeft (toString accMiddle) clausesDigits ++
          s!" clauses {fmtF (percent accMiddle.toFloat tf) 5 2}% accumulated {fmtF (percent accumulated.toFloat tf) 5 2}%")
    if g == tier2 then break
  return lines.toList

/-- Port of `kissat_print_glue_usage` (statistics.c). -/
def glueUsageLines (o : Options) (s : Stats) : List String :=
  let stable := s.clauses_used_stable
  let focused := s.clauses_used_focused
  if stable == 0 && focused == 0 then [PREFIX ++ "no clauses used at all"]
  else
    (if focused != 0 then tierUsageLines o s.usedFocused false else []) ++
    (if focused != 0 && stable != 0 then ["c"] else []) ++
    (if stable != 0 then tierUsageLines o s.usedStable true else [])

/-- Port of `kissat_print_resources` (resources.c). `rss` in bytes. -/
def resourcesLines (rss : Nat) (time : Float) : List String :=
  [PREFIX ++ padRight "maximum-resident-set-size:" 30 ++ " " ++ padLeft (toString rss) 12 ++ " " ++
     padRight "bytes" 5 ++ " " ++ fmtF (rss.toFloat / 1048576.0) 10 0 ++ " MB",
   PREFIX ++ "process-time: " ++ padLeft (formatTime time) 30 ++ " " ++ fmtF time 18 2 ++ " seconds"]

private def putLines (ls : List String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (String.join (ls.map (· ++ "\n")))
  out.flush

/-- Port of `kissat_print_statistics` (internal.c). DEVIATION: no "profiling" section
  (profiling is not ported). -/
def printStatistics (p : Printer) (o : Options) (s : Stats) (time : Float) : IO Unit := do
  if p.verbosity < 0 then return
  let complete := o.statistics != 0
  p.section "statistics"
  let verbose := complete || p.verbosity > 0
  putLines (statisticsLines s time verbose)
  p.section "glue usage"
  putLines (glueUsageLines o s)
  p.section "resources"
  -- DEVIATION: maximum resident set size not available (printed as 0).
  putLines (resourcesLines 0 time)

/-! ## Options and limits listing (`application.c`) -/

/-- Port of `print_options` (application.c). -/
def printOptions (p : Printer) (o : Options) : IO Unit := do
  if p.verbosity < 0 then return
  let mut printed := 0
  for opt in optTable do
    let value := o.getD opt.name
    if opt.value != value || p.verbosity > 0 then
      if printed == 0 then p.section "options"
      printed := printed + 1
      let b := opt.low == 0 && opt.high == 1
      let buffer := s!"{opt.name}={formatValue b value}"
      p.message s!"--{padRight buffer 30} ({if value == opt.value then "same as" else "different from"} default '{formatValue b opt.value}')"

/-- Port of `print_limits` (application.c). -/
def printLimits (p : Printer) (app : AppConfig) : IO Unit := do
  let verbosity := p.verbosity
  if verbosity < 1 && app.conflicts < 0 && app.decisions < 0 then return
  p.section "limits"
  if app.time == 0 && app.conflicts < 0 && app.decisions < 0 then
    p.message "no time, conflict nor decision limit set"
  else
    if app.time != 0 then p.message s!"time limit set to {app.time} seconds"
    else if verbosity > 0 then p.message "no time limit"
    if app.conflicts ≥ 0 then p.message s!"conflict limit set to {app.conflicts} conflicts"
    else if verbosity > 0 then p.message "no conflict limit"
    if app.decisions ≥ 0 then p.message s!"decision limit set to {app.decisions} decisions"
    else if verbosity > 0 then p.message "no decision limit"

/-! ## Usage (`application.c`) -/

/-- `print_force_usage` for a build without proofs and without compression. -/
private def forceUsage : List String :=
  ["  -f      force reading compressed as uncompressed files"]

/-- Port of `print_common_usage` (`-h`), `NPROOFS` and no compression. -/
def commonUsage : List String :=
  ["usage: kissat [ <option> ... ] [ <dimacs> ]", "",
   "where '<option>' is one of the following common options:", "",
   "  -h      print this list of common command line options",
   "  --help  print complete list of command line options", ""] ++ forceUsage ++
  ["  -n      do not print satisfying assignment", "",
   "  -q      suppress all messages",
   "  -s      print complete statistics",
   "  -v      increase verbose level", "",
   "Furthermore '<dimacs>' is the input file in DIMACS format."]

/-- Port of `print_complete_usage` (`--help`), `NPROOFS` and no compression. -/
def completeUsage : List String :=
  ["usage: kissat [ <option> ... ] [ <dimacs> ]", "",
   "where '<option>' is one of the following common options:", "",
   "  --help  print this list of all command line options",
   "  -h      print only reduced list of command line options", ""] ++ forceUsage ++
  ["  -n      do not print satisfying assignment", "",
   "  -q      suppress all messages (see also '--quiet')",
   "  -s      print all statistics (see also '--statistics')",
   "  -v      increase verbose level (see also '--verbose')", "",
   "Further '<option>' can be one of the following less frequent options:", "",
   "  --banner             print solver information",
   "  --build              print build information",
   "  --color              use colors (default if connected to terminal)",
   "  --no-color           no colors (default if not connected to terminal)",
   "  --compiler           print compiler information",
   "  --copyright          print copyright information",
   "  --id                 print 'git' identifier (SHA-1 hash)",
   "  --range              print option range list",
   "  --relaxed            relaxed parsing (ignore DIMACS header)",
   "  --strict             stricter parsing (no empty header lines)",
   "  --version            print version", "",
   "The following solving limits can be enforced:", "",
   "  --conflicts=<limit>",
   "  --decisions=<limit>",
   "  --time=<seconds>", "",
   "Satisfying assignments have by default values for all variables",
   "unless '--partial' is specified, then only values are printed",
   "for variables which are necessary to satisfy the formula.", "",
   "The following predefined 'configurations' (option settings) are supported:", ""] ++
  configurationUsage ++
  ["", "Or '<option>' is one of the following long options:", ""] ++
  optionsUsage ++
  ["", "Furthermore '<dimacs>' is the input file in DIMACS format.", "",
   "The solver was built without proof support. If you need proofs",
   "use a configuration without '--no-proofs' nor '--ultimate'."]

/-- Port of `parsed_one_option_and_return_zero_exit_code` (application.c): output for
  a single informational option, or `none`. -/
def singleOptionOutput (arg : String) : Option (List String) :=
  match arg with
  | "-h" => some commonUsage
  | "--help" => some completeUsage
  | "--banner" => some (bannerLines false)
  | "--build" => some buildLines
  | "--copyright" => some copyrightLines
  | "--compiler" => some [kissatCompiler]
  | "--id" => some [kissatId]
  | "--range" => some optionRangeList
  | "--version" => some [VERSION]
  | _ => none

end LeanKissat.Frontend
