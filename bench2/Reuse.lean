structure S where
  a : Array Nat
  b : ByteArray
  c : UInt64
  d : Nat
  e : Array Nat

@[noinline] def side (s : S) : S := { s with d := s.d + 1 }

-- pattern 1: conditional then update
def p1 (s : S) (flag : Bool) (i : Nat) : S :=
  let s := if flag then side s else s
  { s with b := s.b.set! i 1, c := s.c + 1 }

-- pattern 2: update in both branches
def p2 (s : S) (flag : Bool) (i : Nat) : S :=
  if flag then
    let s := side s
    { s with b := s.b.set! i 1, c := s.c + 1 }
  else { s with b := s.b.set! i 1, c := s.c + 1 }
