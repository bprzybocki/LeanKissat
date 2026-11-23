import LeanKissat.Search.Reduce
import LeanKissat.Util.Sort

/-
Reordering decisions by clause-size weights (`reorder.c`).
-/
namespace LeanKissat
namespace Solver

/-- Port of `compute_weights` (reorder.c). The result is indexed by literals,
  except that entry `idx` of every active variable `idx` is overwritten by its
  combined variable weight (exactly as in C, which reuses the array). -/
def computeWeights (s : Solver) : FloatArray := Id.run do
  let lits := 2 * s.vars.toNat
  let mut weights := FloatArray.mk (Array.replicate lits 0.0)
  let maxSize := s.options.reordermaxsize
  -- DEVIATION: C leaves `table[0]` and `table[1]` uninitialized; they are never read
  -- since at the root level after propagation every non-satisfied irredundant clause
  -- has at least two unassigned literals.
  let mut table := FloatArray.mk (Array.replicate (maxSize + 1) 0.0)
  let mut weight : Float := 1
  for size in [2:maxSize + 1] do
    table := table.set! size weight
    weight := weight / 2.0
  let last := s.lastIrredundant
  for c in s.arena.clauseRefsFrom 0 do
    if last != INVALID_REF && c > last then break
    if s.arena.redundant c then continue
    if s.arena.garbage c then continue
    let n := (s.arena.size c).toNat
    let mut size := 0
    let mut satisfied := false
    for i in [0:n] do
      let v := s.value (s.arena.lit c i)
      if vTrue v then
        satisfied := true
        break
      if v == 0 && size < maxSize then
        size := size + 1
        if size == maxSize then break
    if satisfied then continue
    let w := table.get! size
    for i in [0:n] do
      let lit := (s.arena.lit c i).toNat
      weights := weights.set! lit (weights.get! lit + w)
  let w := table.get! 2
  for l in [0:lits] do
    let lit := UInt32.ofNat l
    if !s.isActive (IDX lit) then continue
    let ws := s.watchesOf lit
    let mut p := 0
    for _ in [0:ws.size] do
      if p ≥ ws.size then break
      let watch := ws.get! p
      if !watchIsBinary watch then
        p := p + 2
        continue
      p := p + 1
      let other := watchLit watch
      if other < lit then continue
      if !s.isActive (IDX other) then continue
      weights := weights.set! l (weights.get! l + w)
      weights := weights.set! other.toNat (weights.get! other.toNat + w)
  for i in [0:s.vars.toNat] do
    if !s.isActive (UInt32.ofNat i) then continue
    let pos := weights.get! (2 * i)
    let neg := weights.get! (2 * i + 1)
    -- MAX (A, B) = (A) < (B) ? (B) : (A); MIN (A, B) = (A) < (B) ? (A) : (B)
    let maxPosNeg := if pos < neg then neg else pos
    let minPosNeg := if pos < neg then pos else neg
    let scaledMinPosNeg := 2 * minPosNeg
    weights := weights.set! i (maxPosNeg + scaledMinPosNeg)
  return weights

/-- Port of `less_focused_order` (reorder.c). -/
@[inline] def lessFocusedOrder (q : Queue) (weights : FloatArray) (a b : UInt32) : Bool :=
  let u := weights.get! a.toNat
  let v := weights.get! b.toNat
  if u < v then true
  else if u > v then false
  else q.linkStamp a < q.linkStamp b

/-- Port of `less_stable_order` (reorder.c). -/
@[inline] def lessStableOrder (h : Heap) (weights : FloatArray) (a b : UInt32) : Bool :=
  let u := weights.get! a.toNat
  let v := weights.get! b.toNat
  if u < v then true
  else if u > v then false
  else
    let s := h.getScore a
    let t := h.getScore b
    if s < t then true
    else if s > t then false
    else b < a

/-- Port of `sort_active_variables_by_weight` (reorder.c). -/
def sortActiveVariablesByWeight (s : Solver) (weights : FloatArray) : U32Vec := Id.run do
  let mut sorted := U32Vec.empty
  for i in [0:s.vars.toNat] do
    if s.isActive (UInt32.ofNat i) then sorted := sorted.push (UInt32.ofNat i)
  if s.stable then
    let h := s.scores
    return Sorting.sortU32 (lessStableOrder h weights) sorted
  else
    let q := s.queue
    return Sorting.sortU32 (lessFocusedOrder q weights) sorted

/-- Port of `reorder_focused` (reorder.c). INC (reordered_focused): STATISTIC. -/
def reorderFocused (s : Solver) : Solver := Id.run do
  let weights := s.computeWeights
  let sorted := s.sortActiveVariablesByWeight weights
  let mut q := s.queue
  let s := { s with queue := {} }
  for i in [0:sorted.size] do
    let idx := sorted.get! i
    let assigned := s.value (LIT idx) != 0
    q := q.moveToFront idx assigned
  return { s with queue := q }

/-- Port of `reorder_stable` (reorder.c). INC (reordered_stable): STATISTIC. -/
def reorderStable (s : Solver) : Solver := Id.run do
  let weights := s.computeWeights
  let mut s := s.rescaleScores
  let sorted := s.sortActiveVariablesByWeight weights
  let n := sorted.size
  let mut h := s.scores
  s := { s with scores := {} }
  for k in [0:n] do
    let idx := sorted.get! (n - 1 - k)
    let oldScore := h.getScore idx
    let weight := weights.get! idx.toNat
    let newScore := oldScore + weight
    h := h.update idx newScore
  return { s with scores := h }

/-- Port of `kissat_reorder` (reorder.c). -/
def reorder (s : Solver) : Solver :=
  let s := INC! s reordered
  let s := if s.stable then s.reorderStable else s.reorderFocused
  -- UPDATE_CONFLICT_LIMIT (reorder, reordered, LINEAR, false)
  if s.inconsistent then s else
  let delta := s.updateConflictLimitDelta s.options.reorderint s.stats.reordered kLinear false
    -- CLAMP: `reorderint ≥ 1` and `reordered ≥ 1`
    (UInt64.ofNat s.options.reorderint)
  let (lim, s) := s.conflictsPlus delta
  { s with limits := { s.limits with reorderConflicts := lim } }

end Solver
end LeanKissat
