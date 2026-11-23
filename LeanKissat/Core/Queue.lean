import LeanKissat.Core.Basic
import LeanKissat.Util.U32Vec

/-
VMTF queue (`queue.c/h`, `inlinequeue.h`, plus the queue walks of `decide.c` and
`backtrack.c`).

Representation (C → Lean). C keeps `solver->links` (array of `struct links`
`{prev, next, stamp}` indexed by variable) and `solver->queue`
`{first, last, stamp, search.{idx, stamp}}` separately; here both live in one
structure `Queue`:
* `solver->links[idx].prev`  → `q.prev[idx]`   (`U32Vec`)
* `solver->links[idx].next`  → `q.next[idx]`   (`U32Vec`)
* `solver->links[idx].stamp` → `q.stamps[idx]` (`U32Vec`)
* `solver->queue.first/last/stamp` → `q.first/last/stamp`
* `solver->queue.search.idx/stamp` → `q.searchIdx/searchStamp`
The link vectors have length `solver->size` (C `NREALLOC_VARIABLE_INDEXED`, so new
entries are uninitialized in C; here they are `DISCONNECT`/`DISCONNECT`/`0`, which is
unobservable since `kissat_enqueue` initializes `prev`/`next` and the stamp).

Solver state read by the C code is passed explicitly:
* `kissat_enqueue` / `kissat_move_to_front` read `VALUE (LIT (idx))`; pass
  `assigned := values[LIT idx] != 0`.
* `kissat_reassign_queue_stamps` prints a `kissat_very_verbose` message
  ("need to reassign enqueue stamps on queue"). It is triggered from
  `enqueueLinks` exactly when `q.stamp == UINT_MAX` on entry; the solver can test
  `Queue.willReassign q` before calling `enqueue`, or before `moveToFront q idx` when
  `idx != q.last` (otherwise `moveToFront` returns early), and print.
-/
namespace LeanKissat

/-- C `UINT_MAX`. -/
def UINT_MAX : UInt32 := UInt32.ofNat 0xFFFFFFFF

/-- `DISCONNECT` (queue.h). -/
def DISCONNECT : UInt32 := UInt32.ofNat 0xFFFFFFFF

/-- `DISCONNECTED (IDX)`: `(int) IDX < 0`. -/
@[inline] def DISCONNECTED (x : UInt32) : Bool := x ≥ 0x80000000

/-- `solver->links` and `solver->queue`. -/
structure Queue where
  prev : U32Vec := .empty
  next : U32Vec := .empty
  stamps : U32Vec := .empty
  first : UInt32 := DISCONNECT
  last : UInt32 := DISCONNECT
  stamp : UInt32 := 0
  searchIdx : UInt32 := DISCONNECT
  searchStamp : UInt32 := 0

instance : Inhabited Queue := ⟨{}⟩

namespace Queue

/-- Port of `kissat_init_queue` (queue.c). C requires `stamp = search.stamp = 0`
  (fresh solver); we set them. -/
def init (q : Queue) : Queue :=
  { q with first := DISCONNECT, last := DISCONNECT, searchIdx := DISCONNECT }

private def resizeVec (a : U32Vec) (n : Nat) (v : UInt32) : U32Vec :=
  if a.size < n then resizeVec (a.push v) n v else a.shrink n
termination_by n - a.size
decreasing_by simp; omega

/-- Reallocation of `solver->links` to `newSize` variables (`resize.c`,
  `NREALLOC_VARIABLE_INDEXED (links, links)` in `kissat_increase_size` and
  `kissat_decrease_size`). -/
def resizeLinks (q : Queue) (newSize : Nat) : Queue :=
  match q with
  | { prev, next, stamps, first, last, stamp, searchIdx, searchStamp } =>
    { prev := resizeVec prev newSize DISCONNECT, next := resizeVec next newSize DISCONNECT,
      stamps := resizeVec stamps newSize 0, first, last, stamp, searchIdx, searchStamp }

/-- `solver->links[idx].stamp`. -/
@[inline] def linkStamp (q : Queue) (idx : UInt32) : UInt32 := q.stamps.get! idx.toNat
/-- `solver->links[idx].prev`. -/
@[inline] def linkPrev (q : Queue) (idx : UInt32) : UInt32 := q.prev.get! idx.toNat
/-- `solver->links[idx].next`. -/
@[inline] def linkNext (q : Queue) (idx : UInt32) : UInt32 := q.next.get! idx.toNat

/-- Port of `kissat_update_queue` (inlinequeue.h). -/
@[inline] def updateQueue (q : Queue) (idx : UInt32) : Queue :=
  { q with searchIdx := idx, searchStamp := q.stamps.get! idx.toNat }

/-- Port of `kissat_reset_search_of_queue` (queue.c). Requires a non-empty queue. -/
def resetSearch (q : Queue) : Queue := q.updateQueue q.last

/-- Loop of `kissat_reassign_queue_stamps`: stamps `1, 2, ...` along `next` from
  `idx`.
  -- FUEL: bounded by vars (`next.size`), needs invariant "the `next` chain from
  `first` is acyclic and visits distinct variables" to never run out. Running out
  after `next.size` steps returns the same result as reaching `DISCONNECT`. -/
def reassignLoop (next stamps : U32Vec) (idx stamp : UInt32) (fuel : Nat) :
    U32Vec × UInt32 :=
  match fuel with
  | 0 => (stamps, stamp)
  | fuel + 1 =>
    if DISCONNECTED idx then (stamps, stamp)
    else
      let stamp := stamp + 1
      reassignLoop next (stamps.set! idx.toNat stamp) (next.get! idx.toNat) stamp fuel

/-- Port of `kissat_reassign_queue_stamps` (queue.c), without the verbose message
  (see module comment). -/
def reassignStamps (q : Queue) : Queue :=
  match q with
  | { prev, next, stamps, first, last, stamp := _, searchIdx, searchStamp } =>
    let (stamps, stamp) := reassignLoop next stamps first 0 next.size
    let searchStamp :=
      if !DISCONNECTED searchIdx then stamps.get! searchIdx.toNat else searchStamp
    { prev, next, stamps, first, last, stamp, searchIdx, searchStamp }

/-- Whether the next `enqueueLinks` will call `kissat_reassign_queue_stamps`. -/
@[inline] def willReassign (q : Queue) : Bool := q.stamp == UINT_MAX

/-- Port of `kissat_enqueue_links` (inlinequeue.h). Requires `prev[i]` and `next[i]`
  disconnected. -/
def enqueueLinks (q : Queue) (i : UInt32) : Queue :=
  match q with
  | { prev, next, stamps, first, last, stamp, searchIdx, searchStamp } =>
    let j := last
    let prev := prev.set! i.toNat j
    let last := i
    let (first, next) :=
      if DISCONNECTED j then (i, next) else (first, next.set! j.toNat i)
    if stamp == UINT_MAX then
      reassignStamps { prev, next, stamps, first, last, stamp, searchIdx, searchStamp }
    else
      let stamp := stamp + 1
      { prev, next, stamps := stamps.set! i.toNat stamp, first, last, stamp,
        searchIdx, searchStamp }

/-- Port of `kissat_dequeue_links` (inlinequeue.h). -/
def dequeueLinks (q : Queue) (i : UInt32) : Queue :=
  match q with
  | { prev, next, stamps, first, last, stamp, searchIdx, searchStamp } =>
    let j := prev.get! i.toNat
    let k := next.get! i.toNat
    let prev := prev.set! i.toNat DISCONNECT
    let next := next.set! i.toNat DISCONNECT
    let (first, next) := if DISCONNECTED j then (k, next) else (first, next.set! j.toNat k)
    let (last, prev) := if DISCONNECTED k then (j, prev) else (last, prev.set! k.toNat j)
    { prev, next, stamps, first, last, stamp, searchIdx, searchStamp }

/-- Port of `kissat_enqueue` (inlinequeue.h). `assigned = (VALUE (LIT (idx)) != 0)`. -/
def enqueue (q : Queue) (idx : UInt32) (assigned : Bool) : Queue :=
  let q := match q with
    | { prev, next, stamps, first, last, stamp, searchIdx, searchStamp } =>
      { prev := prev.set! idx.toNat DISCONNECT, next := next.set! idx.toNat DISCONNECT,
        stamps, first, last, stamp, searchIdx, searchStamp : Queue }
  let q := q.enqueueLinks idx
  if !assigned then q.updateQueue idx else q

/-- Port of `kissat_dequeue` (inlinequeue.h). -/
def dequeue (q : Queue) (idx : UInt32) : Queue :=
  let q :=
    if q.searchIdx == idx then
      let search := q.next.get! idx.toNat
      let search := if search == DISCONNECT then q.prev.get! idx.toNat else search
      if search == DISCONNECT then { q with searchIdx := DISCONNECT, searchStamp := 0 }
      else q.updateQueue search
    else q
  q.dequeueLinks idx

/-- Port of `kissat_move_to_front` (inlinequeue.h). `assigned = (VALUE (LIT (idx)) != 0)`. -/
def moveToFront (q : Queue) (idx : UInt32) (assigned : Bool) : Queue :=
  if idx == q.last then q
  else
    let q :=
      if assigned && q.searchIdx == idx then
        let p := q.prev.get! idx.toNat
        if !DISCONNECTED p then q.updateQueue p
        else q.updateQueue (q.next.get! idx.toNat)
      else q
    let q := (q.dequeueLinks idx).enqueueLinks idx
    if !assigned then q.updateQueue idx else q

/-- Walk of `last_enqueued_unassigned_variable` (decide.c) along `prev` while the
  variable is assigned (`values` is the literal-indexed value array).
  -- FUEL: bounded by vars (`prev.size`), needs invariant "some variable on the `prev`
  chain from `search.idx` is unassigned (C asserts `solver->unassigned`) and the chain
  is acyclic" to never run out. Out of fuel returns the current index. -/
def walkPrevAssigned (prev : U32Vec) (values : ByteArray) (res : UInt32) (fuel : Nat) :
    UInt32 :=
  match fuel with
  | 0 => res
  | fuel + 1 =>
    if values.get! (LIT res).toNat != 0 then
      walkPrevAssigned prev values (prev.get! res.toNat) fuel
    else res

/-- Port of `last_enqueued_unassigned_variable` (decide.c, static). Returns the
  variable and the queue (search cursor updated if it moved). Requires at least one
  unassigned variable. -/
def lastEnqueuedUnassigned (q : Queue) (values : ByteArray) : UInt32 × Queue :=
  let res := q.searchIdx
  if values.get! (LIT res).toNat != 0 then
    let res := walkPrevAssigned q.prev values (q.prev.get! res.toNat) q.prev.size
    (res, q.updateQueue res)
  else (res, q)

/-- Port of `add_unassigned_variable_back_to_queue` (backtrack.c, static; focused mode). -/
@[inline] def addUnassignedBack (q : Queue) (idx : UInt32) : Queue :=
  if q.stamps.get! idx.toNat > q.searchStamp then q.updateQueue idx else q

/-! ### Basic lemmas -/

theorem size_reassignLoop (next stamps : U32Vec) (idx stamp : UInt32) (fuel : Nat) :
    (reassignLoop next stamps idx stamp fuel).1.size = stamps.size := by
  induction fuel generalizing stamps idx stamp with
  | zero => rfl
  | succ n ih =>
    simp only [reassignLoop]; split
    · rfl
    · rw [ih]; rfl

theorem updateQueue_searchIdx (q : Queue) (idx : UInt32) :
    (q.updateQueue idx).searchIdx = idx := rfl

end Queue
end LeanKissat
