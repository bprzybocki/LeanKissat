structure S where
  a : Array Nat
  b : ByteArray
  c : UInt64
  d : Nat

def step (s : S) (i : Nat) : S :=
  { s with b := s.b.set! (i % s.b.size) (s.b.get! (i % s.b.size) + 1), c := s.c + 1 }

def loop (s : S) (n : Nat) : S := Id.run do
  let mut s := s
  for i in [0:n] do
    s := step s (i * 7919)
  return s

def main : IO Unit := do
  let s : S := ⟨#[1,2,3], ByteArray.mk (Array.replicate (1 <<< 20) 0), 0, 0⟩
  let t0 ← IO.monoMsNow
  let s := loop s 10000000
  let t1 ← IO.monoMsNow
  IO.println s!"{t1-t0} ms {s.c} {s.b.get! 5}"
