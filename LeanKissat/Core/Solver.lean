import LeanKissat.Core.Basic
import LeanKissat.Core.Clause
import LeanKissat.Core.OptionsTable
import LeanKissat.Core.StatsTable
import LeanKissat.Core.CountersTable
import LeanKissat.Core.Heap
import LeanKissat.Core.Queue
import LeanKissat.Core.Smooth
import LeanKissat.Core.Reluctant
import LeanKissat.Core.Random
import LeanKissat.Util.WVec

/-
The solver state (`struct kissat` in `internal.h`), restricted to the default
release build. Fields used only by later phases are added as they are ported.
-/
namespace LeanKissat

/-! ### Small records from `kimits.h`, `classify.h`, `mode.h` -/

structure Bounds where
  eliminateMaxBoundCompleted : UInt64 := 0
  eliminateAdditionalClauses : UInt32 := 0
  deriving Inhabited, Repr

structure Limits where
  conflicts : UInt64 := 0
  decisions : UInt64 := 0
  reports : UInt64 := 0
  modeCount : UInt64 := 0
  modeTicks : UInt64 := 0
  modeConflicts : UInt64 := 0
  eliminateVariablesEliminate : UInt64 := 0
  eliminateVariablesSubsume : UInt64 := 0
  eliminateConflicts : UInt64 := 0
  factorMarked : UInt64 := 0
  probeConflicts : UInt64 := 0
  randecConflicts : UInt64 := 0
  reduceConflicts : UInt64 := 0
  reorderConflicts : UInt64 := 0
  rephaseConflicts : UInt64 := 0
  restartConflicts : UInt64 := 0
  glueConflicts : UInt64 := 0
  glueInterval : UInt64 := 0
  deriving Inhabited, Repr

structure Limited where
  conflicts : Bool := false
  decisions : Bool := false
  deriving Inhabited, Repr

structure Enabled where
  eliminate : Bool := false
  focus : Bool := false
  mode : Bool := false
  probe : Bool := false
  deriving Inhabited, Repr

structure Delay where
  count : UInt32 := 0
  current : UInt32 := 0
  deriving Inhabited, Repr

structure Delays where
  bumpreasons : Delay := {}
  congruence : Delay := {}
  sweep : Delay := {}
  vivifyirr : Delay := {}
  deriving Inhabited, Repr

structure Remember where
  ticksEliminate : UInt64 := 0
  ticksProbe : UInt64 := 0
  conflictsReduce : UInt64 := 0
  deriving Inhabited, Repr

structure Classification where
  small : Bool := false
  bigbig : Bool := false
  deriving Inhabited, Repr

/-- `struct mode` (non-METRICS; `entered` is process time, only for reporting). -/
structure Mode where
  ticks : UInt64 := 0
  entered : Float := 0
  conflicts : UInt64 := 0
  deriving Inhabited, Repr

/-- A clause as seen by conflict analysis: either the static binary conflict
  clause `solver->conflict` or a large clause in the arena. -/
inductive CRef where
  | binConflict
  | large (ref : Ref)
  deriving Inhabited, BEq, Repr

/-! ### Per-variable bit flags (`flags.h`) stored in one `UInt32` word -/
namespace VarFlags
def active : UInt32 := 1
def backbone0 : UInt32 := 2
def backbone1 : UInt32 := 4
def eliminate : UInt32 := 8
def eliminated : UInt32 := 16
def factorShift : UInt32 := 5   -- 2 bits
def factorMask : UInt32 := 0x60
def fixed : UInt32 := 0x80
def subsume : UInt32 := 0x100
def sweep : UInt32 := 0x200
def transitive : UInt32 := 0x400
end VarFlags

/-! ### Per-variable assignment bits (`struct assigned`) in one byte -/
namespace ABits
def analyzed : UInt8 := 1
def binary : UInt8 := 2
def poisoned : UInt8 := 4
def removable : UInt8 := 8
def shrinkable : UInt8 := 16
end ABits

-- Import record bits (`struct import`).
namespace ImportBits
def extension : UInt8 := 1
def imported : UInt8 := 2
def eliminated : UInt8 := 4
end ImportBits

/-- The assignment-related ("hot") part of `struct kissat`: everything that
  `kissat_assign` writes. Kept in its own small structure so that the propagation
  loop can thread it separately from the rest of the solver state. -/
structure Asg where
  /-- `values[lit]` (signed char). -/
  values : ByteArray := .empty
  trail : U32Vec := .empty
  /-- `assigned[idx]` split into parallel arrays. -/
  aLevel : U32Vec := .empty
  aTrail : U32Vec := .empty
  aReason : U32Vec := .empty
  aBits : ByteArray := .empty
  /-- `phases.saved[idx]`. -/
  phaseSaved : ByteArray := .empty
  unassigned : UInt32 := 0
  unflushed : UInt32 := 0
  deriving Inhabited

/-- `struct kissat`. -/
structure Solver where
  asg : Asg := {}
  -- flags
  extended : Bool := false
  inconsistent : Bool := false
  iterating : Bool := false
  preprocessing : Bool := false
  probing : Bool := false
  stable : Bool := false
  warming : Bool := false
  watching : Bool := true
  largeClausesWatchedAfterBinaryClauses : Bool := false
  /-- `termination.flagged` (set by time limits in the frontend). -/
  terminationFlagged : Bool := false
  /-- DEVIATION: set when a `UInt64` scheduling counter would overflow; search then
    stops with `unknown`. -/
  overflowed : Bool := false
  /-- DEVIATION: set instead of `kissat_fatal` when the arena or variable capacity
    is exhausted; search stops with `unknown`. -/
  outOfResources : Bool := false
  /-- Set when a scheduled procedure is reached that is not ported yet. -/
  notPorted : Bool := false

  vars : UInt32 := 0
  size : UInt32 := 0
  active : UInt32 := 0
  randec : UInt32 := 0

  /-- `export`: internal idx → external idx. -/
  exportMap : U32Vec := .empty
  /-- `units`: external literals fixed at root (as `Int32` bit patterns). -/
  units : U32Vec := .empty
  /-- `import`: external idx → internal lit (or eliminated position). -/
  importLit : U32Vec := .empty
  importBits : ByteArray := .empty
  /-- `witness` stack (external literals). -/
  witness : U32Vec := .empty

  /-- `flags[idx]`. -/
  flags : U32Vec := .empty
  /-- `marks[lit]` (signed char). -/
  marks : ByteArray := .empty
  /-- `phases.{best,saved,target}[idx]` (signed char). -/
  phaseBest : ByteArray := .empty
  phaseTarget : ByteArray := .empty

  /-- `eliminated` values of eliminated variables. -/
  eliminated : ByteArray := .empty
  etrail : U32Vec := .empty

  /-- VMTF queue together with `links`. -/
  queue : Queue := {}
  scores : Heap := {}
  scinc : Float := 1.0
  schedule : Heap := {}
  scoreshift : Float := 0

  level : UInt32 := 0
  /-- `frames` stack, as parallel arrays. -/
  framePromote : U32Vec := .empty
  frameDecision : U32Vec := .empty
  frameTrail : U32Vec := .empty
  frameUsed : U32Vec := .empty

  /-- index into `trail` of the next literal to propagate -/
  propagate : Nat := 0

  bestAssigned : UInt32 := 0
  targetAssigned : UInt32 := 0

  delayed : U32Vec := .empty
  resolventSize : UInt32 := 0
  antecedentSize : UInt32 := 0

  analyzed : U32Vec := .empty
  levels : U32Vec := .empty
  minimize : U32Vec := .empty
  poisoned : U32Vec := .empty
  promote : U32Vec := .empty
  removable : U32Vec := .empty
  shrinkable : U32Vec := .empty

  /-- `solver->conflict` (binary conflict clause literals). -/
  conflictLit0 : Lit := 0
  conflictLit1 : Lit := 0

  clauseSatisfied : Bool := false
  clauseShrink : Bool := false
  clauseTrivial : Bool := false

  clause : U32Vec := .empty
  shadow : U32Vec := .empty

  arena : Arena := {}
  firstReducible : Ref := INVALID_REF
  lastIrredundant : Ref := INVALID_REF
  /-- `watches[lit]` -/
  watches : Array WVec := #[]

  lastLearned : Array Ref := #[INVALID_REF, INVALID_REF, INVALID_REF, INVALID_REF]

  random : Generator := 0
  averages : Array Averages := #[{}, {}]
  tier1 : Array UInt32 := #[0, 0]
  tier2 : Array UInt32 := #[0, 0]
  reluctant : Reluctant := {}

  bounds : Bounds := {}
  classification : Classification := {}
  delays : Delays := {}
  enabled : Enabled := {}
  limited : Limited := {}
  limits : Limits := {}
  last : Remember := {}
  walked : UInt32 := 0

  mode : Mode := {}
  ticks : UInt64 := 0

  options : Options := {}
  stats : Counters := Counters.empty
  deriving Inhabited

namespace Solver

/-! ### Accessors -/

@[inline] def value (s : Solver) (lit : Lit) : Value := s.asg.values.get! lit.toNat
@[inline] def mark (s : Solver) (lit : Lit) : Value := s.marks.get! lit.toNat
@[inline] def level' (s : Solver) (lit : Lit) : UInt32 := s.asg.aLevel.get! (IDX lit).toNat
@[inline] def levelIdx (s : Solver) (idx : UInt32) : UInt32 := s.asg.aLevel.get! idx.toNat
@[inline] def reasonIdx (s : Solver) (idx : UInt32) : UInt32 := s.asg.aReason.get! idx.toNat
@[inline] def trailIdx (s : Solver) (idx : UInt32) : UInt32 := s.asg.aTrail.get! idx.toNat
@[inline] def abits (s : Solver) (idx : UInt32) : UInt8 := s.asg.aBits.get! idx.toNat
@[inline] def abit (s : Solver) (idx : UInt32) (b : UInt8) : Bool := (s.abits idx &&& b) != 0
@[inline] def isAnalyzed (s : Solver) (idx : UInt32) : Bool := s.abit idx ABits.analyzed
@[inline] def isBinaryReason (s : Solver) (idx : UInt32) : Bool := s.abit idx ABits.binary
@[inline] def setABit (s : Solver) (idx : UInt32) (b : UInt8) (on : Bool) : Solver :=
  let w := s.abits idx
  let w := if on then w ||| b else w &&& ~~~b
  { s with asg := { s.asg with aBits := s.asg.aBits.set! idx.toNat w } }

@[noinline] private def updateABit (a : Asg) (idx : UInt32) (b : UInt8) (on : Bool) : Asg :=
  let w := a.aBits.get! idx.toNat
  let w := if on then w ||| b else w &&& ~~~b
  { a with aBits := a.aBits.set! idx.toNat w }

/-- Keep the assignment-record update behind a call so the outer record is reusable. -/
@[inline] def setABitFast (s : Solver) (idx : UInt32) (b : UInt8) (on : Bool) : Solver :=
  { s with asg := updateABit s.asg idx b on }

@[csimp] theorem setABit_eq_setABitFast : @setABit = @setABitFast := rfl

@[inline] def varFlags (s : Solver) (idx : UInt32) : UInt32 := s.flags.get! idx.toNat
@[inline] def isActive (s : Solver) (idx : UInt32) : Bool := (s.varFlags idx &&& VarFlags.active) != 0
@[inline] def setVarFlag (s : Solver) (idx : UInt32) (b : UInt32) (on : Bool) : Solver :=
  let w := s.varFlags idx
  { s with flags := s.flags.set! idx.toNat (if on then w ||| b else w &&& ~~~b) }

@[inline] def opt (s : Solver) : Options := s.options
@[inline] def LITS (s : Solver) : UInt32 := 2 * s.vars
@[inline] def assignedCount (s : Solver) : UInt32 := s.vars - s.asg.unassigned
@[inline] def conflicts (s : Solver) : UInt64 := s.stats.conflicts
@[inline] def decisionsCount (s : Solver) : UInt64 := s.stats.decisions

@[inline] def tier1Limit (s : Solver) : UInt32 := s.tier1[0]!
@[inline] def tier2Limit (s : Solver) : UInt32 := s.tier2[1]!

@[inline] def averagesCur (s : Solver) : Averages := s.averages[if s.stable then 1 else 0]!
@[inline] def modifyAverages (s : Solver) (f : Averages → Averages) : Solver :=
  { s with averages := s.averages.modify (if s.stable then 1 else 0) f }

@[inline] def modifyStats (s : Solver) (f : Counters → Counters) : Solver :=
  { s with stats := f s.stats }

/-- Frame accessors. -/
@[inline] def frameDecisionAt (s : Solver) (lvl : UInt32) : Lit := s.frameDecision.get! lvl.toNat
@[inline] def frameTrailAt (s : Solver) (lvl : UInt32) : UInt32 := s.frameTrail.get! lvl.toNat
@[inline] def frameUsedAt (s : Solver) (lvl : UInt32) : UInt32 := s.frameUsed.get! lvl.toNat
@[inline] def frameCount (s : Solver) : Nat := s.frameDecision.size

/-- `kissat_push_frame` (frames.h / inlineframes.h). -/
@[inline] def pushFrame (s : Solver) (decision : Lit) : Solver :=
  { s with
    framePromote := s.framePromote.push 0
    frameDecision := s.frameDecision.push decision
    frameTrail := s.frameTrail.push (UInt32.ofNat s.asg.trail.size)
    frameUsed := s.frameUsed.push 0 }

/-- `SET_END_OF_STACK (frames, ...)`: keep frames `0..n-1`. -/
@[inline] def shrinkFrames (s : Solver) (n : Nat) : Solver :=
  { s with
    framePromote := s.framePromote.shrink n
    frameDecision := s.frameDecision.shrink n
    frameTrail := s.frameTrail.shrink n
    frameUsed := s.frameUsed.shrink n }

end Solver
end LeanKissat
