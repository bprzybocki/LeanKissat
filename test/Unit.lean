import LeanKissat.Core.Random
import LeanKissat.Core.Smooth
import LeanKissat.Core.Reluctant
import LeanKissat.Core.Heap
import LeanKissat.Core.Queue

/-
Differential unit test: performs exactly the same sequence of operations as
`test/unit/driver.c` and prints the same output (see `test/unit/run.sh`).
-/
open LeanKissat

namespace UnitTest

def hex16 (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - s.length) ++ s

def bits (f : Float) : String := hex16 f.toBits

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
def MIX_INIT : UInt64 := 14695981039346656037

/-- `printf ("%d", (int) b)` for `bool`. -/
def b2s (b : Bool) : String := if b then "1" else "0"

/-! ### random -/

def testRandom : IO Unit := do
  IO.println "== random"
  let mut rng : Generator := 42
  for _ in [0:20] do
    let (r, g) := rng.nextRandom64; rng := g
    IO.println s!"r64 {r}"
  for _ in [0:20] do
    let (r, g) := rng.nextRandom32; rng := g
    IO.println s!"r32 {r}"
  for i in [0:200] do
    let (a, g) := rng.nextRandom32; rng := g
    let (b, g) := rng.nextRandom32; rng := g
    let b := if i % 3 == 0 then a + (b &&& 255) else b
    let (a, b) := if b < a then (b, a) else (a, b)
    let b := if i % 10 == 0 then a else b
    let (r, g) := rng.pickRandom a b; rng := g
    IO.println s!"pick {a} {b} {r}"
  let (r, g) := rng.pickRandom 0 UINT_MAX; rng := g
  IO.println s!"pickfull {r}"
  for _ in [0:40] do
    let (r, g) := rng.pickBool; rng := g
    IO.println s!"bool {b2s r}"
  for _ in [0:40] do
    let (r, g) := rng.pickDouble; rng := g
    IO.println s!"double {bits r}"

/-! ### smooth / averages -/

def printSmooth (n : String) (s : Smooth) : IO Unit :=
  IO.println s!"{n} {bits s.value} {bits s.biased} {bits s.alpha} {bits s.beta} {bits s.exp}"

def testSmooth : IO Unit := do
  IO.println "== smooth"
  let windows : Array Nat := #[2, 3, 10, 33, 100000]
  let rounds : Array Nat := #[10, 2000, 300, 300, 300]
  let mut rng : Generator := 7
  for w in [0:5] do
    let mut s := Smooth.init windows[w]!
    printSmooth "init" s
    for i in [0:rounds[w]!] do
      let mut y : Float := 0
      if i % 3 == 0 then
        let (v, g) := rng.pickRandom 0 100; rng := g; y := v.toFloat
      else if i % 3 == 1 then
        let (v, g) := rng.pickDouble; rng := g; y := v * 1e6
      else
        let (v, g) := rng.pickDouble; rng := g; y := -v
      s := s.update y
      if w != 1 || i % 50 == 0 || i > 1800 then printSmooth "upd" s
    printSmooth "final" s
  let a : Averages := ({} : Averages).init 33 100000
  let a := { a with fastGlue := a.fastGlue.update 3.0 }
  let a := a.init 7 100000
  IO.println s!"avg {b2s a.initialized} {a.savedDecisions}"
  printSmooth "fast_glue" a.fastGlue
  printSmooth "slow_glue" a.slowGlue
  printSmooth "level" a.level
  printSmooth "size" a.size
  printSmooth "trail" a.trail
  printSmooth "decision_rate" a.decisionRate

/-! ### reluctant -/

def relStr (r : Reluctant) : String :=
  s!"rel {b2s r.limited} {b2s r.trigger} {r.period} {r.wait} {r.u} {r.v} {r.limit}"

def testReluctant : IO Unit := do
  IO.println "== reluctant"
  let periods : Array UInt64 := #[1024, 3, 2, 5, 1]
  let limits : Array UInt64 := #[(1 : UInt64) <<< 20, 100, 0, 3, 0]
  let ticks : Array Nat := #[3000000, 10000, 20000, 1000, 5000]
  for c in [0:5] do
    let mut r := ({} : Reluctant).enable periods[c]! limits[c]!
    IO.println (relStr r)
    for t in [1:ticks[c]! + 1] do
      r := r.tick
      if t % 7 != 3 then
        let (trig, r') := r.triggered
        r := r'
        if trig then IO.println s!"trig {t} {relStr r}"
    r := r.disable.tick
    IO.println (relStr r)
  let r := ({} : Reluctant).initFromOptions true (1 <<< 10) (1 <<< 20)
  IO.println (relStr r)
  let r := r.initFromOptions false (1 <<< 10) (1 <<< 20)
  IO.println (relStr r)

/-! ### heap -/

def heapHash (h : Heap) : UInt64 := Id.run do
  let mut r := MIX_INIT
  r := mix r (if h.tainted then 1 else 0)
  r := mix r h.vars.toUInt64
  r := mix r h.size.toUInt64
  r := mix r h.stack.size.toUInt64
  for i in [0:h.stack.size] do
    r := mix r (h.stack.get! i).toUInt64
  for i in [0:h.vars] do
    r := mix r (h.pos.get! i).toUInt64
  for i in [0:h.vars] do
    r := mix r (h.score.get! i).toBits
  return r

def heapDump (h : Heap) : IO Unit := do
  let mut s := "stack"
  for i in [0:h.stack.size] do s := s ++ s!" {h.stack.get! i}"
  IO.println s
  s := "pos"
  for i in [0:h.vars] do s := s ++ s!" {h.pos.get! i}"
  IO.println s
  s := "score"
  for i in [0:h.vars] do s := s ++ s!" {bits (h.score.get! i)}"
  IO.println s

def testHeap (drv0 : Generator) : IO Generator := do
  IO.println "== heap"
  let mut drv := drv0
  let mut H : Heap := ({} : Heap).resize 8
  for i in [0:4] do
    H := H.push (2 * i).toUInt32
  IO.println s!"init {hex16 (heapHash H)}"
  for op in [0:5000] do
    let (o, g) := drv.pickRandom 0 100; drv := g
    if o < 3 then
      if H.size < 512 then
        H := H.resize (2 * H.size)
        IO.println s!"resize {H.size}"
      else IO.println "noresize"
    else if o < 30 then
      let (idx, g) := drv.pickRandom 0 H.size.toUInt32; drv := g
      if !H.contains idx then
        H := H.push idx
        IO.println s!"push {idx}"
      else IO.println s!"nopush {idx}"
    else if o < 42 then
      let (idx, g) := drv.pickRandom 0 H.size.toUInt32; drv := g
      if H.contains idx then
        H := H.pop idx
        IO.println s!"pop {idx}"
      else IO.println s!"nopop {idx}"
    else if o < 55 then
      if !H.isEmpty then
        let m := H.maxHeap
        let (idx, H') := H.popMax
        H := H'
        IO.println s!"popmax {m} {idx}"
      else IO.println "empty"
    else if o < 93 then
      let (idx, g) := drv.pickRandom 0 H.size.toUInt32; drv := g
      let (kind, g) := drv.pickRandom 0 5; drv := g
      let old := H.getScore idx
      let mut s : Float := 0
      if kind == 0 then
        let (v, g) := drv.pickRandom 0 10; drv := g; s := v.toFloat
      else if kind == 1 then
        let (v, g) := drv.pickDouble; drv := g; s := v
      else if kind == 2 then
        let (v, g) := drv.pickDouble; drv := g; s := old + v * 1e3
      else if kind == 3 then
        let (v, g) := drv.pickDouble; drv := g; s := -v
      else s := old
      H := H.update idx s
      IO.println s!"update {idx} {kind} {bits s} pos {H.getPos idx}"
    else if o < 96 then
      let (v, g) := drv.pickRandom 0 2; drv := g
      let f : Float := if v != 0 then 1e-150 else 0.5
      H := H.rescale f
      IO.println s!"rescale {bits f}"
    else
      IO.println s!"maxscore {bits H.maxScore}"
    IO.println s!"h {op} {hex16 (heapHash H)} {H.sizeHeap}"
    if op % 500 == 499 then heapDump H
  heapDump H
  H := H.release
  IO.println s!"released {H.vars} {H.size} {b2s H.tainted}"
  let mut A : Heap := {}
  for i in [0:200] do
    let (idx, g) := drv.pickRandom 0 (if i < 100 then 50 else 3000); drv := g
    A := A.adjust idx
    if i == 60 || i == 150 then
      A := A.update idx (1.5 + i.toFloat)
    if i % 3 == 0 && idx.toNat < A.vars && !A.contains idx then
      A := A.push idx
    IO.println s!"adjust {idx} {A.vars} {A.size} {A.sizeHeap} {hex16 (heapHash A)}"
  IO.println s!"amax {bits A.maxScore}"
  for _ in [0:A.sizeHeap] do
    let (idx, A') := A.popMax
    A := A'
    IO.println s!"apop {idx}"
  return drv

/-! ### queue -/

def NQ : Nat := 64

def queueHash (q : Queue) : UInt64 := Id.run do
  let mut r := MIX_INIT
  r := mix r q.first.toUInt64
  r := mix r q.last.toUInt64
  r := mix r q.stamp.toUInt64
  r := mix r q.searchIdx.toUInt64
  r := mix r q.searchStamp.toUInt64
  for i in [0:NQ] do
    r := mix r (q.prev.get! i).toUInt64
    r := mix r (q.next.get! i).toUInt64
    r := mix r (q.stamps.get! i).toUInt64
  return r

def queueDump (q : Queue) : IO Unit := do
  let mut s := "queue"
  let mut idx := q.first
  -- FUEL: the list has at most NQ elements
  for _ in [0:NQ] do
    if DISCONNECTED idx then break
    s := s ++ s!" {idx}:{q.linkStamp idx}"
    idx := q.linkNext idx
  IO.println s

def reassignMsg (q : Queue) : IO Unit :=
  if q.willReassign then IO.println "very verbose: reassign" else pure ()

def testQueue (drv0 : Generator) : IO Unit := do
  IO.println "== queue"
  let mut drv := drv0
  let mut values : ByteArray := ByteArray.mk (Array.replicate (2 * NQ) 0)
  let mut q : Queue := (({} : Queue).resizeLinks NQ).init
  q := { q with stamp := UINT_MAX - 300 }
  let mut inq : Array Bool := Array.replicate NQ false
  let mut inqueue := 0
  for _ in [0:NQ] do
    let (idx, g) := drv.pickRandom 0 NQ.toUInt32; drv := g
    let mut idx := idx.toNat
    for _ in [0:NQ] do
      if inq[idx]! then idx := (idx + 1) % NQ else break
    reassignMsg q
    q := q.enqueue idx.toUInt32 false
    inq := inq.set! idx true
    inqueue := inqueue + 1
  IO.println s!"init {hex16 (queueHash q)}"
  queueDump q
  for op in [0:6000] do
    if op == 3000 then q := { q with stamp := UINT_MAX - 5 }
    let (o, g) := drv.pickRandom 0 100; drv := g
    let (idx32, g) := drv.pickRandom 0 NQ.toUInt32; drv := g
    let idx := idx32.toNat
    let lit := (LIT idx32).toNat
    let assigned := values.get! lit != 0
    if o < 25 then
      if !assigned then
        let (b, g) := drv.pickRandom 0 2; drv := g
        let v : UInt8 := if b != 0 then 1 else 0xFF
        values := (values.set! lit v).set! (lit + 1) (0 - v)
        IO.println s!"assign {idx} {if b != 0 then "1" else "-1"}"
      else IO.println s!"noassign {idx}"
    else if o < 45 then
      if assigned then
        values := (values.set! lit 0).set! (lit + 1) 0
        if inq[idx]! then q := q.addUnassignedBack idx32
        IO.println s!"unassign {idx}"
      else IO.println s!"nounassign {idx}"
    else if o < 70 then
      if inq[idx]! then
        if idx32 != q.last then reassignMsg q
        q := q.moveToFront idx32 assigned
        IO.println s!"mtf {idx}"
      else IO.println s!"nomtf {idx}"
    else if o < 78 then
      if inq[idx]! && inqueue > 8 then
        q := q.dequeue idx32
        inq := inq.set! idx false
        inqueue := inqueue - 1
        IO.println s!"dequeue {idx}"
      else IO.println s!"nodequeue {idx}"
    else if o < 86 then
      if !inq[idx]! then
        reassignMsg q
        q := q.enqueue idx32 assigned
        inq := inq.set! idx true
        inqueue := inqueue + 1
        IO.println s!"enqueue {idx}"
      else IO.println s!"noenqueue {idx}"
    else if o < 97 then
      let mut some := false
      for i in [0:NQ] do
        if inq[i]! && values.get! (2 * i) == 0 then some := true
      if some then
        let (res, q') := q.lastEnqueuedUnassigned values
        q := q'
        IO.println s!"decide {res}"
      else IO.println "nodecide"
    else
      q := q.resetSearch
      IO.println "reset"
    IO.println s!"q {op} {hex16 (queueHash q)}"
    if op % 500 == 499 then queueDump q
  queueDump q

end UnitTest

def main : IO Unit := do
  UnitTest.testRandom
  UnitTest.testSmooth
  UnitTest.testReluctant
  let drv ← UnitTest.testHeap 12345
  UnitTest.testQueue drv
