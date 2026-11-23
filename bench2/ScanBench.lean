structure Big where
  f0 : Array Nat := #[]
  f1 : Array Nat := #[]
  f2 : Array Nat := #[]
  f3 : Array Nat := #[]
  f4 : Array Nat := #[]
  f5 : Array Nat := #[]
  f6 : Array Nat := #[]
  f7 : Array Nat := #[]
  f8 : Array Nat := #[]
  f9 : Array Nat := #[]
  f10 : Array Nat := #[]
  f11 : Array Nat := #[]
  f12 : Array Nat := #[]
  f13 : Array Nat := #[]
  f14 : Array Nat := #[]
  f15 : Array Nat := #[]
  f16 : Array Nat := #[]
  f17 : Array Nat := #[]
  f18 : Array Nat := #[]
  f19 : Array Nat := #[]
  f20 : Array Nat := #[]
  f21 : Array Nat := #[]
  f22 : Array Nat := #[]
  f23 : Array Nat := #[]
  f24 : Array Nat := #[]
  f25 : Array Nat := #[]
  f26 : Array Nat := #[]
  f27 : Array Nat := #[]
  f28 : Array Nat := #[]
  f29 : Array Nat := #[]
  f30 : Array Nat := #[]
  f31 : Array Nat := #[]
  f32 : Array Nat := #[]
  f33 : Array Nat := #[]
  f34 : Array Nat := #[]
  f35 : Array Nat := #[]
  f36 : Array Nat := #[]
  f37 : Array Nat := #[]
  f38 : Array Nat := #[]
  f39 : Array Nat := #[]
  f40 : Array Nat := #[]
  f41 : Array Nat := #[]
  f42 : Array Nat := #[]
  f43 : Array Nat := #[]
  f44 : Array Nat := #[]
  f45 : Array Nat := #[]
  f46 : Array Nat := #[]
  b : ByteArray := ByteArray.mk (Array.replicate 1024 0)
  c : UInt64 := 0
  deriving Inhabited
@[noinline] def updBig (s : Big) (i : Nat) : Big := { s with b := s.b.set! (i % 1024) 1, c := s.c + 1 }
def loopBig (s : Big) (n : Nat) : Big := Id.run do
  let mut s := s
  for i in [0:n] do
    s := updBig s i
  return s

structure Small where
  f0 : Array Nat := #[]
  f1 : Array Nat := #[]
  f2 : Array Nat := #[]
  f3 : Array Nat := #[]
  f4 : Array Nat := #[]
  f5 : Array Nat := #[]
  f6 : Array Nat := #[]
  f7 : Array Nat := #[]
  b : ByteArray := ByteArray.mk (Array.replicate 1024 0)
  c : UInt64 := 0
  deriving Inhabited
@[noinline] def updSmall (s : Small) (i : Nat) : Small := { s with b := s.b.set! (i % 1024) 1, c := s.c + 1 }
def loopSmall (s : Small) (n : Nat) : Small := Id.run do
  let mut s := s
  for i in [0:n] do
    s := updSmall s i
  return s

def main : IO Unit := do
  let n := 50000000
  let t0 ← IO.monoMsNow
  let s := loopBig default n
  let t1 ← IO.monoMsNow
  let r := loopSmall default n
  let t2 ← IO.monoMsNow
  IO.println s!"big {t1-t0} ms ({s.c}), small {t2-t1} ms ({r.c})"
