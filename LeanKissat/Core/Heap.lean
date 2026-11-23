import LeanKissat.Util.U32Vec

/-
Binary max-heap of variable indices with `double` scores (`heap.c/h`, `inlineheap.h`).

Representation (C → Lean):
* `heap->stack` (unsigneds)            → `stack : U32Vec`
* `heap->pos`   (unsigned[size])       → `pos : U32Vec` with `pos.size = size`
* `heap->score` (double[size])         → `score : FloatArray` with `score.size = size`
* `heap->vars`, `heap->size` (unsigned) → `Nat` (always `< 2^32`, C asserts
  `new_size < DISCONTAIN`).
Entries with index in `[vars, size)` are uninitialized in C (`kissat_nrealloc`) and
never read; here they are `DISCONTAIN` / `0.0`. This is unobservable.
The C functions take `kissat *solver` only for logging/allocation; here they take
and return the heap. Positions are computed in `Nat` (C asserts no overflow in
`HEAP_CHILD`).
-/
namespace LeanKissat

/-- `DISCONTAIN` (heap.h). -/
def DISCONTAIN : UInt32 := UInt32.ofNat 0xFFFFFFFF

/-- `DISCONTAINED (IDX)`: `(int) IDX < 0`. -/
@[inline] def DISCONTAINED (x : UInt32) : Bool := x ≥ 0x80000000

/-- C `struct heap`. -/
structure Heap where
  tainted : Bool := false
  vars : Nat := 0
  size : Nat := 0
  stack : U32Vec := .empty
  score : FloatArray := .empty
  pos : U32Vec := .empty

instance : Inhabited Heap := ⟨{}⟩

namespace Heap

/-- Port of `kissat_heap_contains` (heap.h). -/
@[inline] def contains (h : Heap) (idx : UInt32) : Bool :=
  idx.toNat < h.vars && !DISCONTAINED (h.pos.get! idx.toNat)

/-- Port of `kissat_get_heap_pos` (heap.h). -/
@[inline] def getPos (h : Heap) (idx : UInt32) : UInt32 :=
  if idx.toNat < h.vars then h.pos.get! idx.toNat else DISCONTAIN

/-- Port of `kissat_get_heap_score` (heap.h). -/
@[inline] def getScore (h : Heap) (idx : UInt32) : Float :=
  if idx.toNat < h.vars then h.score.get! idx.toNat else 0.0

/-- Port of `kissat_empty_heap` (heap.h). -/
@[inline] def isEmpty (h : Heap) : Bool := h.stack.size == 0

/-- Port of `kissat_size_heap` (heap.h). -/
@[inline] def sizeHeap (h : Heap) : Nat := h.stack.size

/-- Port of `kissat_max_heap` (heap.h). Requires a non-empty heap. -/
@[inline] def maxHeap (h : Heap) : UInt32 := h.stack.get! 0

/-- `res = MAX (res, x)` with `MAX(A,B) = (A) < (B) ? (B) : (A)` (faithful for NaN and signed zeros). -/
@[inline] private def cmax (a b : Float) : Float := if a < b then b else a

private def maxScoreLoop (score : FloatArray) (vars : Nat) (i : Nat) (res : Float) : Float :=
  if i < vars then maxScoreLoop score vars (i + 1) (cmax res (score.get! i)) else res
termination_by vars - i

/-- Port of `kissat_max_score_on_heap` (heap.h). -/
def maxScore (h : Heap) : Float :=
  if !h.tainted then 0
  else maxScoreLoop h.score h.vars 1 (h.score.get! 0)

/-- Port of `kissat_release_heap` (heap.c). -/
def release (_h : Heap) : Heap := {}

private def pushN (a : U32Vec) (n : Nat) (v : UInt32) : U32Vec :=
  match n with
  | 0 => a
  | n + 1 => pushN (a.push v) n v

private def pushNF (a : FloatArray) (n : Nat) (v : Float) : FloatArray :=
  match n with
  | 0 => a
  | n + 1 => pushNF (a.push v) n v

/-- Port of `kissat_resize_heap` (heap.c). Untainted heaps get a fresh zeroed score
  array (C `calloc`); tainted ones keep old scores (C `nrealloc`). -/
def resize (h : Heap) (newSize : Nat) : Heap :=
  match h with
  | { tainted, vars, size, stack, score, pos } =>
    if size ≥ newSize then { tainted, vars, size, stack, score, pos }
    else
      let pos := pushN pos (newSize - size) DISCONTAIN
      let score :=
        if tainted then pushNF score (newSize - size) 0.0
        else pushNF (FloatArray.emptyWithCapacity newSize) newSize 0.0
      { tainted, vars, size := newSize, stack, score, pos }

private def scaleLoop (score : FloatArray) (factor : Float) (vars : Nat) (i : Nat) : FloatArray :=
  if i < vars then scaleLoop (score.set! i (score.get! i * factor)) factor vars (i + 1)
  else score
termination_by vars - i

/-- Port of `kissat_rescale_heap` (heap.c). -/
def rescale (h : Heap) (factor : Float) : Heap :=
  match h with
  | { tainted, vars, size, stack, score, pos } =>
    { tainted, vars, size, stack, score := scaleLoop score factor vars 0, pos }

private def fillPos (pos : U32Vec) (i stop : Nat) : U32Vec :=
  if i < stop then fillPos (pos.set! i DISCONTAIN) (i + 1) stop else pos
termination_by stop - i

private def fillScore (score : FloatArray) (i stop : Nat) : FloatArray :=
  if i < stop then fillScore (score.set! i 0.0) (i + 1) stop else score
termination_by stop - i

/-- Port of `kissat_enlarge_heap` (heap.c). Requires `vars < newVars ≤ size`. -/
def enlarge (h : Heap) (newVars : Nat) : Heap :=
  match h with
  | { tainted, vars, size, stack, score, pos } =>
    let pos := fillPos pos vars newVars
    let score := if tainted then fillScore score vars newVars else score
    { tainted, vars := newVars, size, stack, score, pos }

/-- Loop of `kissat_bubble_up`: returns updated stack/pos and final position. -/
def bubbleUpLoop (stack pos : U32Vec) (score : FloatArray) (idxScore : Float)
    (idxPos : Nat) : U32Vec × U32Vec × Nat :=
  if h0 : idxPos = 0 then (stack, pos, idxPos)
  else
    let parentPos := (idxPos - 1) / 2
    let parent := stack.get! parentPos
    if score.get! parent.toNat ≥ idxScore then (stack, pos, idxPos)
    else
      bubbleUpLoop (stack.set! idxPos parent) (pos.set! parent.toNat idxPos.toUInt32)
        score idxScore parentPos
termination_by idxPos
decreasing_by omega

/-- Port of `kissat_bubble_up` (inlineheap.h). -/
def bubbleUp (h : Heap) (idx : UInt32) : Heap :=
  match h with
  | { tainted, vars, size, stack, score, pos } =>
    let idxPos := (pos.get! idx.toNat).toNat
    let idxScore := score.get! idx.toNat
    let (stack, pos, p) := bubbleUpLoop stack pos score idxScore idxPos
    { tainted, vars, size, stack := stack.set! p idx, score,
      pos := pos.set! idx.toNat p.toUInt32 }

/-- Child selection of `kissat_bubble_down`: the right sibling `childPos + 1` is taken
  only if it exists and has a strictly larger score. -/
@[inline] def pickChild (stack : U32Vec) (score : FloatArray) (stop childPos : Nat) : Nat :=
  if childPos + 1 < stop then
    if score.get! (stack.get! (childPos + 1)).toNat > score.get! (stack.get! childPos).toNat
    then childPos + 1 else childPos
  else childPos

theorem pickChild_bounds (stack : U32Vec) (score : FloatArray) (stop childPos : Nat)
    (h : childPos < stop) :
    childPos ≤ pickChild stack score stop childPos ∧ pickChild stack score stop childPos < stop := by
  unfold pickChild; split
  · split <;> omega
  · omega

/-- Loop of `kissat_bubble_down`. `stop = SIZE_STACK (heap->stack)`. -/
def bubbleDownLoop (stack pos : U32Vec) (score : FloatArray) (stop : Nat) (idxScore : Float)
    (idxPos : Nat) : U32Vec × U32Vec × Nat :=
  if hc : 2 * idxPos + 1 ≥ stop then (stack, pos, idxPos)
  else
    let childPos := pickChild stack score stop (2 * idxPos + 1)
    let child := stack.get! childPos
    let childScore := score.get! child.toNat
    if childScore ≤ idxScore then (stack, pos, idxPos)
    else
      have := pickChild_bounds stack score stop (2 * idxPos + 1) (by omega)
      bubbleDownLoop (stack.set! idxPos child) (pos.set! child.toNat idxPos.toUInt32)
        score stop idxScore childPos
termination_by stop - idxPos
decreasing_by omega

/-- Port of `kissat_bubble_down` (inlineheap.h). -/
def bubbleDown (h : Heap) (idx : UInt32) : Heap :=
  match h with
  | { tainted, vars, size, stack, score, pos } =>
    let idxPos := (pos.get! idx.toNat).toNat
    let idxScore := score.get! idx.toNat
    let (stack, pos, p) := bubbleDownLoop stack pos score stack.size idxScore idxPos
    { tainted, vars, size, stack := stack.set! p idx, score,
      pos := pos.set! idx.toNat p.toUInt32 }

/-- `HEAP_IMPORT (IDX)` (inlineheap.h). -/
@[inline] def heapImport (h : Heap) (idx : UInt32) : Heap :=
  if h.vars ≤ idx.toNat then h.enlarge (idx.toNat + 1) else h

/-- Port of `kissat_push_heap` (inlineheap.h). Requires `!contains h idx` and
  `idx < size`. -/
def push (h : Heap) (idx : UInt32) : Heap :=
  let h := h.heapImport idx
  let h : Heap := match h with
    | { tainted, vars, size, stack, score, pos } =>
      -- read the size before pushing so that `stack` stays unique (in-place push)
      let n := stack.size
      { tainted, vars, size, stack := stack.push idx, score,
        pos := pos.set! idx.toNat n.toUInt32 }
  h.bubbleUp idx

/-- Port of `kissat_pop_heap` (inlineheap.h). Requires `contains h idx`. -/
def pop (h : Heap) (idx : UInt32) : Heap :=
  match h with
  | { tainted, vars, size, stack, score, pos } =>
    let last := stack.back!
    let stack := stack.pop
    let pos := pos.set! last.toNat DISCONTAIN
    if last == idx then { tainted, vars, size, stack, score, pos }
    else
      let idxPos := pos.get! idx.toNat
      let pos := pos.set! idx.toNat DISCONTAIN
      let stack := stack.set! idxPos.toNat last
      let pos := pos.set! last.toNat idxPos
      let h : Heap := { tainted, vars, size, stack, score, pos }
      (h.bubbleUp last).bubbleDown last

/-- Port of `kissat_pop_max_heap` (inlineheap.h). Requires a non-empty heap. -/
def popMax (h : Heap) : UInt32 × Heap :=
  match h with
  | { tainted, vars, size, stack, score, pos } =>
    let idx := stack.get! 0
    let last := stack.back!
    let stack := stack.pop
    let pos := pos.set! last.toNat DISCONTAIN
    if last == idx then (idx, { tainted, vars, size, stack, score, pos })
    else
      let pos := pos.set! idx.toNat DISCONTAIN
      let stack := stack.set! 0 last
      let pos := pos.set! last.toNat 0
      let h : Heap := { tainted, vars, size, stack, score, pos }
      (idx, h.bubbleDown last)

/-- `while (idx >= new_size) new_size *= 2` (in `kissat_adjust_heap`). -/
def doubleUntilAbove (idx n : Nat) (hn : 0 < n) : Nat :=
  if h : idx ≥ n then doubleUntilAbove idx (2 * n) (by omega) else n
termination_by idx + 1 - n

/-- Port of `kissat_adjust_heap` (inlineheap.h). -/
def adjust (h : Heap) (idx : UInt32) : Heap :=
  let newVars := idx.toNat + 1
  if newVars ≤ h.vars then h
  else
    let oldSize := h.size
    let h :=
      if idx.toNat ≥ oldSize then
        let start := if oldSize != 0 then 2 * oldSize else 1
        h.resize (doubleUntilAbove idx.toNat (max start 1) (by omega))
      else h
    h.enlarge (idx.toNat + 1)

/-- Port of `kissat_update_heap` (inlineheap.h). -/
def update (h : Heap) (idx : UInt32) (newScore : Float) : Heap :=
  let oldScore := h.getScore idx
  if oldScore == newScore then h
  else
    let h := h.heapImport idx
    let h : Heap := match h with
      | { tainted := _, vars, size, stack, score, pos } =>
        { tainted := true, vars, size, stack, score := score.set! idx.toNat newScore, pos }
    if !h.contains idx then h
    else if newScore > oldScore then h.bubbleUp idx
    else h.bubbleDown idx

/-! ### Basic lemmas -/

theorem bubbleUpLoop_size (stack pos : U32Vec) (score : FloatArray) (s : Float) (p : Nat) :
    (bubbleUpLoop stack pos score s p).1.size = stack.size := by
  fun_induction bubbleUpLoop stack pos score s p <;> simp_all [U32Vec.size_set!]

theorem bubbleDownLoop_size (stack pos : U32Vec) (score : FloatArray) (stop : Nat) (s : Float)
    (p : Nat) : (bubbleDownLoop stack pos score stop s p).1.size = stack.size := by
  fun_induction bubbleDownLoop stack pos score stop s p <;> simp_all [U32Vec.size_set!]

@[simp] theorem size_bubbleUp (h : Heap) (idx : UInt32) :
    (h.bubbleUp idx).stack.size = h.stack.size := by
  unfold bubbleUp; simp [U32Vec.size_set!, bubbleUpLoop_size]

@[simp] theorem size_bubbleDown (h : Heap) (idx : UInt32) :
    (h.bubbleDown idx).stack.size = h.stack.size := by
  unfold bubbleDown; simp [U32Vec.size_set!, bubbleDownLoop_size]

@[simp] theorem stack_enlarge (h : Heap) (n : Nat) : (h.enlarge n).stack = h.stack := rfl

theorem size_push (h : Heap) (idx : UInt32) :
    (h.push idx).stack.size = h.stack.size + 1 := by
  unfold push heapImport; split <;> simp

theorem size_pop (h : Heap) (idx : UInt32) (hne : 0 < h.stack.size) :
    (h.pop idx).stack.size = h.stack.size - 1 := by
  cases h; simp only [pop]; split <;> simp [U32Vec.size_set!, U32Vec.pop, U32Vec.size_shrink] at * <;> omega

theorem size_popMax (h : Heap) (hne : 0 < h.stack.size) :
    (h.popMax).2.stack.size = h.stack.size - 1 := by
  cases h; simp only [popMax]; split <;> simp [U32Vec.size_set!, U32Vec.pop, U32Vec.size_shrink] at * <;> omega

end Heap
end LeanKissat
