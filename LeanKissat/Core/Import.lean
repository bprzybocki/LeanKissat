import LeanKissat.Core.Macros

/-
Variable management: `resize.c`, `phases.c` (resize part), `import.c`, `flags.c`,
and the inline helpers `kissat_mark_added_literal`, `kissat_mark_removed_literal`,
`kissat_export_literal`, `kissat_fixed` from `inline.h`.
-/
namespace LeanKissat
namespace Solver

/-- Grow a `ByteArray` with zeros to size `n`. -/
def growBytes (b : ByteArray) (n : Nat) : ByteArray :=
  if b.size < n then growBytes (b.push 0) n else b
termination_by n - b.size
decreasing_by simp [ByteArray.size_push]; omega

/-- Grow a `U32Vec` with `v` to size `n`. -/
def growU32 (a : U32Vec) (n : Nat) (v : UInt32 := 0) : U32Vec :=
  if a.size < n then growU32 (a.push v) n v else a
termination_by n - a.size
decreasing_by simp [U32Vec.size_push]; omega

/-- Port of `kissat_increase_size` (resize.c). Per-variable arrays are grown to
  `newSize` (C capacity); only `[0, vars)` is ever read. -/
def increaseSize (s : Solver) (newSize : UInt32) : Solver :=
  let oldSize := s.size
  if oldSize ≥ newSize then s else
  let n := newSize.toNat
  let a := s.asg
  let s := { s with asg := {} }
  let a := { a with
    aLevel := growU32 a.aLevel n
    aTrail := growU32 a.aTrail n
    aReason := growU32 a.aReason n
    aBits := growBytes a.aBits n
    values := growBytes a.values (2 * n)
    phaseSaved := growBytes a.phaseSaved n }
  { s with
    asg := a
    flags := growU32 s.flags n
    queue := s.queue.resizeLinks n
    marks := growBytes s.marks (2 * n)
    watches := s.watches ++ Array.replicate (2 * n - s.watches.size) WVec.empty
    scores := s.scores.resize n
    phaseBest := growBytes s.phaseBest n
    phaseTarget := growBytes s.phaseTarget n
    size := newSize }

/-- `while (new_size < new_vars) new_size *= 2`. -/
def doubleUntil (newVars n : Nat) (hn : 0 < n) : Nat :=
  if h : n < newVars then doubleUntil newVars (2 * n) (by omega) else n
termination_by newVars - n

/-- Port of `kissat_enlarge_variables` (resize.c). -/
def enlargeVariables (s : Solver) (newVars : UInt32) : Solver :=
  if s.vars ≥ newVars then s else
  let oldSize := s.size.toNat
  let s :=
    if oldSize < newVars.toNat then
      let newSize :=
        if oldSize == 0 then newVars.toNat
        else
          let start := if oldSize &&& (oldSize - 1) == 0 then 2 * oldSize else 2
          doubleUntil newVars.toNat (max start 1) (by omega)
      s.increaseSize (UInt32.ofNat newSize)
    else s
  { s with vars := newVars }

/-! ### Import / export -/

@[inline] def importBitsAt (s : Solver) (eidx : Nat) : UInt8 := s.importBits.get! eidx

/-- `adjust_imports_for_external_literal` (import.c). -/
def adjustImports (s : Solver) (eidx : Nat) : Solver :=
  if eidx < s.importLit.size then s else
  { s with
    importLit := growU32 s.importLit (eidx + 1)
    importBits := growBytes s.importBits (eidx + 1) }

/-- `adjust_exports_for_external_literal` (import.c). -/
def adjustExports (s : Solver) (eidx : Nat) (extension : Bool) : Solver :=
  let iidx := s.vars
  let s := s.enlargeVariables (iidx + 1)
  let ilit := 2 * iidx
  let bits := (if extension then ImportBits.extension else 0) ||| ImportBits.imported
  let s := { s with
    importBits := s.importBits.set! eidx bits
    importLit := s.importLit.set! eidx ilit }
  let s := if extension then INC! s variables_extension else INC! s variables_original
  let ex := growU32 s.exportMap (iidx.toNat + 1)
  { s with exportMap := ex.set! iidx.toNat (UInt32.ofNat eidx) }

/-- `import_literal` (import.c). `elit` is a non-zero external literal. -/
def importLiteralAux (s : Solver) (elit : Int) (extension : Bool) : Lit × Solver :=
  let eidx := elit.natAbs
  let s := s.adjustImports eidx
  if s.importBitsAt eidx &&& ImportBits.eliminated != 0 then (INVALID_LIT, s) else
  let s := if s.importBitsAt eidx &&& ImportBits.imported == 0 then
      s.adjustExports eidx extension else s
  let ilit := s.importLit.get! eidx
  let ilit := if elit < 0 then NOT ilit else ilit
  (ilit, s)

/-- Import all external variables `other .. eidx` in order (tumble = 0 path). -/
def importUpTo (s : Solver) (other eidx : Nat) (ilit : Lit) : Lit × Solver :=
  if _h : other ≤ eidx then
    let (ilit, s) := s.importLiteralAux other false
    importUpTo s (other + 1) eidx ilit
  else (ilit, s)
termination_by eidx + 1 - other

/-- Port of `kissat_import_literal` (import.c). -/
def importLiteral (s : Solver) (elit : Int) : Lit × Solver :=
  if s.options.tumble != 0 then s.importLiteralAux elit false else
  let eidx := elit.natAbs
  let other := s.importLit.size
  if eidx < other then s.importLiteralAux elit false else
  let (s, other) := if other == 0 then (s.adjustImports 0, 1) else (s, other)
  let (ilit, s) := importUpTo s other eidx 0
  ((if elit < 0 then NOT ilit else ilit), s)

/-- Port of `kissat_export_literal` (inline.h). Returns 0 if not exported. -/
@[inline] def exportLiteral (s : Solver) (ilit : Lit) : Int :=
  let e := s.exportMap.get! (IDX ilit).toNat
  if e == 0 then 0 else if NEGATED ilit then -(e.toNat : Int) else (e.toNat : Int)

/-- Port of `kissat_fixed` (inline.h). -/
@[inline] def fixedValue (s : Solver) (lit : Lit) : Value :=
  let v := s.value lit
  if v == 0 then 0 else if s.level' lit != 0 then 0 else v

/-! ### Flags (`flags.c`, `inline.h`) -/

/-- Port of `kissat_mark_removed_literal` (inline.h). -/
@[inline] def markRemovedLiteral (s : Solver) (lit : Lit) : Solver :=
  let idx := IDX lit
  let f := s.varFlags idx
  if f &&& VarFlags.fixed != 0 then s
  else if f &&& VarFlags.eliminate == 0 then
    let s := s.setVarFlag idx VarFlags.eliminate true
    INC! s variables_eliminate
  else s

/-- Set flag `bit` of variable `i`, counting the first time in `counter`. -/
@[inline] def markFlagBit (p : U32Vec × Counters) (i : Nat) (bit : UInt32) (counter : Nat) : U32Vec × Counters :=
  if p.1.get! i &&& bit == 0 then (p.1.set! i (p.1.get! i ||| bit), p.2.add counter 1) else p

/-- The flag and counter updates of `kissat_mark_added_literal` (inline.h). -/
def markAddedFlags (flags : U32Vec) (stats : Counters) (lit : Lit) : U32Vec × Counters :=
  let i := (IDX lit).toNat
  let bit : UInt32 := ((1 : UInt32) <<< (if NEGATED lit then (1 : UInt32) else 0)) <<< VarFlags.factorShift
  markFlagBit (markFlagBit (flags, stats) i VarFlags.subsume Counters.idx_variables_subsume) i bit
    Counters.idx_literals_factor

/-- Port of `kissat_mark_added_literal` (inline.h). -/
@[inline] def markAddedLiteral (s : Solver) (lit : Lit) : Solver :=
  let (flags, stats) := markAddedFlags s.flags s.stats lit
  { s with flags := flags, stats := stats }

def markRemovedLiterals (s : Solver) (lits : Array Lit) : Solver :=
  lits.foldl markRemovedLiteral s

def markAddedLiterals (s : Solver) (lits : Array Lit) : Solver :=
  lits.foldl markAddedLiteral s

/-- The flag, counter, queue and heap updates of `activate_literal` (flags.c). -/
def activateCore (s : Solver) (idx : UInt32) : Solver :=
  let s := s.setVarFlag idx VarFlags.active true
  let s := { s with active := s.active + 1 }
  let s := INC! s variables_activated
  let s := { s with queue := s.queue.enqueue idx (s.value (LIT idx) != 0) }
  let score : Float := 1.0 - 1.0 / s.stats.variables_activated.toFloat
  let s := { s with scores := s.scores.update idx score }
  let s := { s with scores := if s.stable && s.value (LIT idx) == 0 then s.scores.push idx else s.scores }
  { s with asg := { s.asg with unassigned := s.asg.unassigned + 1 } }

/-- Port of `activate_literal` (flags.c). -/
def activateLiteral (s : Solver) (lit : Lit) : Solver :=
  let idx := IDX lit
  if s.isActive idx then s else
  ((s.activateCore idx).markRemovedLiteral (STRIP lit)).markAddedLiteral (STRIP lit)

def activateLiterals (s : Solver) (lits : Array Lit) : Solver :=
  lits.foldl activateLiteral s

/-- Port of `deactivate_variable` (flags.c). -/
def deactivateVariable (s : Solver) (idx : UInt32) : Solver :=
  let s := s.setVarFlag idx VarFlags.active false
  let s := { s with active := s.active - 1, queue := s.queue.dequeue idx }
  if s.scores.contains idx then { s with scores := s.scores.pop idx } else s

/-- Encode an external literal as the `int` bit pattern stored in `int` stacks. -/
@[inline] def intToU32 (i : Int) : UInt32 := (Int32.ofInt i).toUInt32
@[inline] def u32ToInt (u : UInt32) : Int := u.toInt32.toInt

/-- Port of `kissat_mark_fixed_literal` (flags.c). -/
@[noinline] def markFixedLiteral (s : Solver) (lit : Lit) : Solver :=
  let idx := IDX lit
  let s := s.setVarFlag idx VarFlags.fixed true
  let s := s.deactivateVariable idx
  let s := INC! s units
  let elit := s.exportLiteral lit
  { s with units := s.units.push (intToU32 elit) }

/-- Port of `kissat_mark_eliminated_variable` (flags.c). -/
def markEliminatedVariable (s : Solver) (idx : UInt32) : Solver :=
  let lit := LIT idx
  let s := s.setVarFlag idx VarFlags.eliminated true
  let s := s.deactivateVariable idx
  let elit := s.exportLiteral lit
  let eidx := elit.natAbs
  let pos := s.eliminated.size
  { s with
    importLit := s.importLit.set! eidx (UInt32.ofNat pos)
    importBits := s.importBits.set! eidx (s.importBitsAt eidx ||| ImportBits.eliminated)
    eliminated := s.eliminated.push 0
    asg := { s.asg with unassigned := s.asg.unassigned - 1 } }

/-- Port of `kissat_fresh_literal` (import.c). `INVALID_LIT` if no external
  variable is left. -/
def freshLiteral (s : Solver) : Lit × Solver :=
  let imported := s.importLit.size
  if imported ≥ EXTERNAL_MAX_VAR then (INVALID_LIT, s) else
  let (res, s) := s.importLiteralAux imported true
  -- `INC (fresh)` is a STATISTIC (ignored in the default build)
  (res, s.activateLiteral res)

/-- Port of `kissat_reserve` (internal.c), without argument checks. -/
def reserveImport (s : Solver) (idx n : Nat) : Solver :=
  if idx ≤ n then reserveImport (s.importLiteral idx).2 (idx + 1) n else s
termination_by n + 1 - idx

def reserveActivate (s : Solver) (idx n : Nat) : Solver :=
  if idx < n then reserveActivate (s.activateLiteral (LIT (UInt32.ofNat idx))) (idx + 1) n else s
termination_by n - idx

def reserve (s : Solver) (maxVar : Nat) : Solver :=
  let s := s.increaseSize (UInt32.ofNat maxVar)
  if s.options.tumble == 0 then (s.reserveImport 1 maxVar).reserveActivate 0 maxVar else s

end Solver
end LeanKissat
