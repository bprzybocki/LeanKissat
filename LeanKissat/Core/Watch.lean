import LeanKissat.Core.Import

/-
Watch lists (`watch.h`, `watch.c`, watch helpers in `inline.h`).
Encoding of a `union watch` as `UInt32` (little-endian bit-fields):
bits 0..30 = literal or reference, bit 31 = `binary`.
A large-clause watch is a blocking-literal word followed by a reference word.
-/
namespace LeanKissat

def WATCH_BINARY_BIT : UInt32 := 0x80000000

@[inline] def binaryWatch (lit : Lit) : UInt32 := (lit &&& 0x7FFFFFFF) ||| WATCH_BINARY_BIT
@[inline] def largeWatch (ref : Ref) : UInt32 := ref &&& 0x7FFFFFFF
@[inline] def blockingWatch (lit : Lit) : UInt32 := lit &&& 0x7FFFFFFF
@[inline] def watchIsBinary (w : UInt32) : Bool := w &&& WATCH_BINARY_BIT != 0
@[inline] def watchLit (w : UInt32) : Lit := w &&& 0x7FFFFFFF
@[inline] def watchRef (w : UInt32) : Ref := w &&& 0x7FFFFFFF

namespace Solver

@[inline] def watchesOf (s : Solver) (lit : Lit) : WVec := s.watches[lit.toNat]!

@[inline] def modifyWatches (s : Solver) (lit : Lit) (f : WVec → WVec) : Solver :=
  { s with watches := s.watches.modify lit.toNat f }

/-- `kissat_watch_other` / `kissat_push_binary_watch`. -/
@[inline] def watchOther (s : Solver) (lit other : Lit) : Solver :=
  s.modifyWatches lit (·.push (binaryWatch other))

/-- `kissat_watch_binary`. -/
@[inline] def watchBinary (s : Solver) (a b : Lit) : Solver :=
  (s.watchOther a b).watchOther b a

/-- `kissat_watch_blocking` / `kissat_push_blocking_watch`. -/
@[inline] def watchBlocking (s : Solver) (lit blocking : Lit) (ref : Ref) : Solver :=
  s.modifyWatches lit (fun w => (w.push (blockingWatch blocking)).push (largeWatch ref))

/-- `kissat_watch_reference`. -/
@[inline] def watchReference (s : Solver) (a b : Lit) (ref : Ref) : Solver :=
  (s.watchBlocking a b ref).watchBlocking b a ref

/-- `kissat_connect_literal` / `kissat_push_large_watch`. -/
@[inline] def connectLiteral (s : Solver) (lit : Lit) (ref : Ref) : Solver :=
  s.modifyWatches lit (·.push (largeWatch ref))

/-- `kissat_inlined_connect_clause`. -/
def connectClause (s : Solver) (ref : Ref) : Solver := Id.run do
  let n := (s.arena.size ref).toNat
  let mut s := s
  for i in [0:n] do
    s := s.connectLiteral (s.arena.lit ref i) ref
  return s

/-- `kissat_watch_clause`. -/
@[inline] def watchClause (s : Solver) (ref : Ref) : Solver :=
  s.watchReference (s.arena.lit ref 0) (s.arena.lit ref 1) ref

/-- Compaction loop shared by `kissat_remove_binary_watch` and
  `kissat_remove_blocking_watch`: copy `ws[p..]` to `ws[q..]`, dropping the
  first matching entry (all matching entries in the binary case, as C does). -/
def removeBinaryLoop (ws : WVec) (lit : Lit) (p q : Nat)   : WVec × Nat :=
  if h : p < ws.size then
    let w := ws[p]
    let ws := ws.set! q w
    if !watchIsBinary w then
      let t := ws.get! (p + 1)
      removeBinaryLoop (ws.set! (q + 1) t) lit (p + 2) (q + 2)
    else if watchLit w != lit then removeBinaryLoop ws lit (p + 1) (q + 1)
    else removeBinaryLoop ws lit (p + 1) q
  else (ws, q)
termination_by ws.size - p
decreasing_by all_goals simp_all [WVec.size_set!]; omega

/-- Port of `kissat_remove_binary_watch` (watch.c). -/
def removeBinaryWatch (ws : WVec) (lit : Lit) : WVec :=
  -- C shrinks the vector by exactly one element
  let (ws', _) := removeBinaryLoop ws lit 0 0
  ws'.shrink (ws.size - 1)

def removeBlockingLoop (ws : WVec) (ref : Ref) (p q : Nat) : WVec :=
  if h : p < ws.size then
    let w := ws[p]
    let ws := ws.set! q w
    if watchIsBinary w then removeBlockingLoop ws ref (p + 1) (q + 1)
    else
      let t := ws.get! (p + 1)
      let ws := ws.set! (q + 1) t
      if t != ref then removeBlockingLoop ws ref (p + 2) (q + 2)
      else removeBlockingLoop ws ref (p + 2) q
  else ws
termination_by ws.size - p
decreasing_by all_goals simp_all [WVec.size_set!]; omega

/-- Port of `kissat_remove_blocking_watch` (watch.c). -/
def removeBlockingWatch (ws : WVec) (ref : Ref) : WVec :=
  (removeBlockingLoop ws ref 0 0).shrink (ws.size - 2)

/-- `kissat_unwatch_blocking`. -/
@[inline] def unwatchBlocking (s : Solver) (lit : Lit) (ref : Ref) : Solver :=
  s.modifyWatches lit (removeBlockingWatch · ref)

/-- Port of `kissat_remove_from_vector` (vector.c): remove the first occurrence. -/
def removeFromVector (ws : WVec) (x : UInt32) : WVec := Id.run do
  let n := ws.size
  let mut i := n
  for j in [0:n] do
    if ws.get! j == x then
      i := j
      break
  let mut ws := ws
  for j in [i+1:n] do
    ws := ws.set! (j - 1) (ws.get! j)
  return if i < n then ws.shrink (n - 1) else ws

/-- `kissat_disconnect_binary`. -/
@[inline] def disconnectBinary (s : Solver) (lit other : Lit) : Solver :=
  s.modifyWatches lit (removeFromVector · (binaryWatch other))

/-- `kissat_disconnect_reference`. -/
@[inline] def disconnectReference (s : Solver) (lit : Lit) (ref : Ref) : Solver :=
  s.modifyWatches lit (removeFromVector · (largeWatch ref))

end Solver
end LeanKissat
