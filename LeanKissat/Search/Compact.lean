import LeanKissat.Search.Search

/-
Compacting variable indices during garbage collection (`compact.c`) and
`kissat_map_literal` (inline.h) for `map = true`.

Compaction renumbers the internal variables: active variables (and the first fixed
one, which represents all fixed literals afterwards) get consecutive indices in
their old order. Remapped here, as in C: the import map (`importLit`), the export
map, the units, the trail and binary reasons, all per-variable arrays
(`assigned`, `flags`, phases, values), the queue links, the score heap and the
frames. The watch lists and arena literals are remapped by the compacting paths of
`collect.c` (see `Collect.lean`). The C function also compacts
`solver->sweep_schedule`, which is empty outside of sweeping (not ported yet).
-/
namespace LeanKissat
namespace Solver

/-- `kissat_map_literal (solver, ilit, true)` on the export and import maps. -/
@[inline] def mapLit (exportMap importLit : U32Vec) (importBits : ByteArray) (ilit : Lit) : Lit :=
  let e := exportMap.get! (IDX ilit).toNat
  if e == 0 then INVALID_LIT else
  let eidx := e.toNat
  if importBits.get! eidx &&& ImportBits.eliminated != 0 then INVALID_LIT else
  let mlit := importLit.get! eidx
  -- `elit < 0` iff `ilit` is negated (export entries are positive)
  if NEGATED ilit then NOT mlit else mlit

/-- Port of `kissat_map_literal (solver, ilit, true)` (inline.h). -/
def mapLiteral (s : Solver) (ilit : Lit) : Lit :=
  mapLit s.exportMap s.importLit s.importBits ilit

/-- Port of `map_idx` (compact.c). -/
def mapIdx (s : Solver) (iidx : UInt32) : UInt32 :=
  let e := s.exportMap.get! iidx.toNat
  if e == 0 then INVALID_IDX else
  let eidx := e.toNat
  if s.importBits.get! eidx &&& ImportBits.eliminated != 0 then INVALID_IDX else
  IDX (s.importLit.get! eidx)

/-- Port of `reimport_literal` (compact.c). -/
@[inline] def reimportLiteral (s : Solver) (eidx : Nat) (mlit : Lit) : Solver :=
  { s with importLit := s.importLit.set! eidx mlit }

/-- Port of `kissat_compact_literals` (compact.c). Returns the new number of
  variables and `mfixed`. INC (compacted): METRIC. -/
def compactLiterals (s : Solver) : UInt32 × Lit × Solver := Id.run do
  let mut importLit := s.importLit
  let mut importBits := s.importBits
  let mut exportMap := s.exportMap
  let s := { s with importLit := .empty, importBits := .empty, exportMap := .empty }
  let mut mfixed := INVALID_LIT
  let mut vars : UInt32 := 0
  for i in [0:s.vars.toNat] do
    let iidx := UInt32.ofNat i
    let f := s.varFlags iidx
    if f &&& VarFlags.eliminated != 0 then continue
    let ilit := LIT iidx
    let mut mlit := INVALID_LIT
    if f &&& VarFlags.fixed != 0 then
      let value := s.fixedValue ilit
      if mfixed == INVALID_LIT then
        mlit := LIT vars
        mfixed := mlit
        if vFalse value then mfixed := NOT mfixed
        vars := vars + 1
      else if vFalse value then
        mlit := NOT mfixed
      else
        mlit := mfixed
    else if f &&& VarFlags.active != 0 then
      mlit := LIT vars
      vars := vars + 1
    else
      let e := exportMap.get! i
      if e != 0 then
        let eidx := e.toNat
        importBits := importBits.set! eidx (importBits.get! eidx &&& ~~~ImportBits.imported)
        exportMap := exportMap.set! i 0
      continue
    if mlit == ilit then continue
    let eidx := (exportMap.get! i).toNat
    -- `elit < 0` never holds (export entries are positive); `reimport_literal`
    importLit := importLit.set! eidx mlit
  return (vars, mfixed, { s with importLit, importBits, exportMap })

/-- Port of `compact_trail` (compact.c). -/
def compactTrail (s : Solver) : Solver := Id.run do
  let mut a := s.asg
  let mut s := { s with asg := {} }
  for i in [0:a.trail.size] do
    let ilit := a.trail.get! i
    let mlit := s.mapLiteral ilit
    a := { a with trail := a.trail.set! i mlit }
    let idx := IDX ilit
    if a.aBits.get! idx.toNat &&& ABits.binary == 0 then continue
    let other := a.aReason.get! idx.toNat
    let mother := s.mapLiteral other
    a := { a with aReason := a.aReason.set! idx.toNat mother }
  return { s with asg := a }

/-- The `compact_literal` loop of `kissat_finalize_compacting` (compact.c): for every
  variable whose literal is mapped to a different literal, `compact_literal (mlit, ilit)`
  copies `assigned`, `flags`, the three phases and both values. -/
def compactLiteralsLoop (s : Solver) : Solver := Id.run do
  let mut a := s.asg
  let mut flags := s.flags
  let mut best := s.phaseBest
  let mut target := s.phaseTarget
  let s := { s with asg := {}, flags := .empty, phaseBest := .empty, phaseTarget := .empty }
  for i in [0:s.vars.toNat] do
    let srcLit := LIT (UInt32.ofNat i)
    let dstLit := s.mapLiteral srcLit
    if dstLit == INVALID_LIT || srcLit == dstLit then continue
    -- compact_literal (solver, dstLit, srcLit)
    let dst := (IDX dstLit).toNat
    let src := i
    a := { a with
      aLevel := a.aLevel.set! dst (a.aLevel.get! src)
      aTrail := a.aTrail.set! dst (a.aTrail.get! src)
      aReason := a.aReason.set! dst (a.aReason.get! src)
      aBits := a.aBits.set! dst (a.aBits.get! src)
      phaseSaved := a.phaseSaved.set! dst (a.phaseSaved.get! src)
      values := (a.values.set! dstLit.toNat (a.values.get! srcLit.toNat)).set!
        (NOT dstLit).toNat (a.values.get! (NOT srcLit).toNat) }
    flags := flags.set! dst (flags.get! src)
    best := best.set! dst (best.get! src)
    target := target.set! dst (target.get! src)
  return { s with asg := a, flags := flags, phaseBest := best, phaseTarget := target }

/-- Port of `compact_queue` (compact.c).
  -- FUEL: the queue is an acyclic chain of distinct variables, so it has at most
  `vars` elements (`fuel = vars + 1`). -/
def compactQueue (s : Solver) : Solver := Id.run do
  let mut q := s.queue
  let s := { s with queue := {} }
  q := { q with stamp := 0 }
  -- `p` is either `&queue.first` (`pOld = none`) or `&links[pOld].next`
  let mut pOld : Option UInt32 := none
  let mut prev := DISCONNECT
  for _ in [0:s.vars.toNat + 1] do
    let idx := match pOld with
      | none => q.first
      | some j => q.next.get! j.toNat
    if DISCONNECTED idx then break
    let midx := s.mapIdx idx
    let stamp := q.stamp + 1
    q := { q with
      prev := q.prev.set! idx.toNat prev
      stamps := q.stamps.set! idx.toNat stamp
      stamp := stamp }
    if idx == q.searchIdx then
      q := { q with searchIdx := midx, searchStamp := stamp }
    prev := midx
    q := match pOld with
      | none => { q with first := midx }
      | some j => { q with next := q.next.set! j.toNat midx }
    pOld := some idx
  q := { q with last := prev }
  q := match pOld with
    | none => { q with first := DISCONNECT }
    | some j => { q with next := q.next.set! j.toNat DISCONNECT }
  for i in [0:s.vars.toNat] do
    let midx := s.mapIdx (UInt32.ofNat i)
    if midx == INVALID_IDX then continue
    q := { q with
      prev := q.prev.set! midx.toNat (q.prev.get! i)
      next := q.next.set! midx.toNat (q.next.get! i)
      stamps := q.stamps.set! midx.toNat (q.stamps.get! i) }
  return { s with queue := q }

/-- Port of `compact_scores` (compact.c). -/
def compactScores (s : Solver) (vars : UInt32) : Solver := Id.run do
  let old := s.scores
  let s := { s with scores := {} }
  let mut h : Heap := ({} : Heap).resize vars.toNat
  if old.tainted then
    for i in [0:s.vars.toNat] do
      let idx := UInt32.ofNat i
      let midx := s.mapIdx idx
      if midx == INVALID_IDX then continue
      h := h.update midx (old.getScore idx)
  for i in [0:old.stack.size] do
    let midx := s.mapIdx (old.stack.get! i)
    if midx == INVALID_IDX then continue
    h := h.push midx
  return { s with scores := h }

/-- Port of `compact_frames` (compact.c). -/
def compactFrames (s : Solver) : Solver := Id.run do
  let mut d := s.frameDecision
  let s := { s with frameDecision := .empty }
  for level in [1:d.size] do
    d := d.set! level (s.mapLiteral (d.get! level))
  return { s with frameDecision := d }

/-- Port of `compact_export` (compact.c). -/
def compactExport (s : Solver) (vars : UInt32) : Solver := Id.run do
  let mut ex := s.exportMap
  let s := { s with exportMap := .empty }
  for iidx in [0:ex.size] do
    let elit := ex.get! iidx
    if elit == 0 then continue
    -- `map_idx (solver, iidx)`
    let eidx := elit.toNat
    if s.importBits.get! eidx &&& ImportBits.eliminated != 0 then continue
    let midx := IDX (s.importLit.get! eidx)
    ex := ex.set! midx.toNat elit
  return { s with exportMap := ex.shrink vars.toNat }

/-- Port of `compact_units` (compact.c). -/
def compactUnits (s : Solver) (mfixed : Lit) : Solver := Id.run do
  let mut il := s.importLit
  let s := { s with importLit := .empty }
  for i in [0:s.units.size] do
    let elit := u32ToInt (s.units.get! i)
    let eidx := elit.natAbs
    let mlit := if elit < 0 then NOT mfixed else mfixed
    let ilit := il.get! eidx
    -- `reimport_literal`
    if mlit != ilit then il := il.set! eidx mlit
  return { s with importLit := il }

/-- Port of `compact_best_and_target_values` (compact.c). -/
def compactBestAndTargetValues (s : Solver) (vars : UInt32) : Solver := Id.run do
  let mut bestAssigned : UInt32 := 0
  let mut targetAssigned : UInt32 := 0
  for idx in [0:vars.toNat] do
    if !s.isActive (UInt32.ofNat idx) then continue
    if s.phaseTarget.get! idx != 0 then targetAssigned := targetAssigned + 1
    if s.phaseBest.get! idx != 0 then bestAssigned := bestAssigned + 1
  return { s with targetAssigned := targetAssigned, bestAssigned := bestAssigned }

/-- Truncate a byte array to `n` entries (C: realloc to the smaller size). -/
@[inline] def truncBytes (b : ByteArray) (n : Nat) : ByteArray :=
  if b.size ≤ n then b else ⟨b.data.shrink n⟩

/-- Port of `kissat_decrease_size` (resize.c). The per-variable arrays are truncated
  to `vars` (and literal-indexed ones to `2 * vars`); `kissat_resize_heap` is a no-op
  since the compacted heap already has size `vars`. -/
def decreaseSize (s : Solver) : Solver :=
  let n := s.vars.toNat
  let a := s.asg
  let s := { s with asg := {} }
  let a := { a with
    aLevel := a.aLevel.shrink n
    aTrail := a.aTrail.shrink n
    aReason := a.aReason.shrink n
    aBits := truncBytes a.aBits n
    values := truncBytes a.values (2 * n)
    phaseSaved := truncBytes a.phaseSaved n }
  let wss := s.watches
  let s := { s with watches := #[] }
  { s with
    asg := a
    flags := s.flags.shrink n
    queue := s.queue.resizeLinks n
    marks := truncBytes s.marks (2 * n)
    watches := wss.shrink (2 * n)
    scores := s.scores.resize n
    phaseBest := truncBytes s.phaseBest n
    phaseTarget := truncBytes s.phaseTarget n
    size := s.vars }

/-- Port of `kissat_finalize_compacting` (compact.c). -/
def finalizeCompacting (s : Solver) (vars : UInt32) (mfixed : Lit) : Solver := Id.run do
  if vars == s.vars then return s
  let mut ex := s.exportMap
  let mut s := { s with exportMap := .empty }
  let mut first := true
  for i in [0:s.vars.toNat] do
    let f := s.varFlags (UInt32.ofNat i)
    if f &&& VarFlags.fixed != 0 && first then first := false
    else if f &&& VarFlags.active == 0 then
      ex := ex.set! i 0
  s := { s with exportMap := ex }
  s := s.compactTrail
  s := s.compactLiteralsLoop
  if mfixed != INVALID_LIT then s := s.compactUnits mfixed
  -- `memset` of `assigned`, `flags`, `values`, `watches` beyond `vars`: these
  -- entries are dropped by `decreaseSize` below.
  s := s.compactQueue
  -- compact_stack (solver, &solver->sweep_schedule): empty outside of sweeping
  s := s.compactScores vars
  s := s.compactFrames
  s := s.compactExport vars
  s := s.compactBestAndTargetValues vars
  s := { s with vars := vars }
  return s.decreaseSize

end Solver
end LeanKissat
