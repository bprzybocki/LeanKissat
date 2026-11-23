structure B where
  f0 : Array Nat
  f1 : Array Nat
  f2 : Array Nat
  f3 : Array Nat
  f4 : Array Nat
  f5 : Array Nat
  f6 : Array Nat
  f7 : Array Nat
  f8 : Array Nat
  f9 : Array Nat
  f10 : Array Nat
  f11 : Array Nat
  f12 : Array Nat
  f13 : Array Nat
  f14 : Array Nat
  f15 : Array Nat
  f16 : Array Nat
  f17 : Array Nat
  f18 : Array Nat
  f19 : Array Nat
  f20 : Array Nat
  f21 : Array Nat
  f22 : Array Nat
  f23 : Array Nat
  f24 : Array Nat
  f25 : Array Nat
  f26 : Array Nat
  f27 : Array Nat
  f28 : Array Nat
  f29 : Array Nat
  f30 : Array Nat
  f31 : Array Nat
  f32 : Array Nat
  f33 : Array Nat
  f34 : Array Nat
  f35 : Array Nat
  f36 : Array Nat
  f37 : Array Nat
  f38 : Array Nat
  f39 : Array Nat
  f40 : Array Nat
  f41 : Array Nat
  f42 : Array Nat
  f43 : Array Nat
  f44 : Array Nat
  f45 : Array Nat
  f46 : Array Nat
  f47 : Array Nat
  f48 : Array Nat
  f49 : Array Nat
  f50 : Array Nat
  f51 : Array Nat
  f52 : Array Nat
  f53 : Array Nat
  f54 : Array Nat
  f55 : Array Nat
  f56 : Array Nat
  f57 : Array Nat
  f58 : Array Nat
  f59 : Array Nat
  b : ByteArray
  c : UInt64

def q1 (s : B) (i : Nat) : B :=
  let t := s.f3.size
  { s with b := s.b.set! i 1, c := s.c + 1, f3 := s.f3.push t }

def q2 (s : B) (i : Nat) : B :=
  { s with b := s.b.set! i 1 }
