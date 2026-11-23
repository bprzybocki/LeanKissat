import LeanKissat.Core.Basic
import LeanKissat.Util.U32Vec

/-
Clause arena (`arena.c`, `clause.h`).

The C arena is a stack of 16-byte `ward`s; a clause starts at a ward boundary and
`reference` is its ward index. C layout (64-bit, non-COMPACT):
  word 0: glue:19 | garbage | quotient | reason | redundant | shrunken | subsume |
          swept | vivify | used:5
  word 1: searched
  word 2: size
  word 3..: literals; a shrunken clause is terminated by `INVALID_LIT` after
          its (reduced) literals.
Clause size in bytes is `align16 (12 + 4 * size)` (`kissat_bytes_of_clause`, which is
`sizeof (clause) + (size - 3) * 4` with `sizeof (clause) = 24`).
We store the same words in a `U32Vec`; ward index `r` = word index `4 * r`.
-/
namespace LeanKissat

def LD_MAX_GLUE : Nat := 19
def LD_MAX_USED : Nat := 5
def MAX_GLUE : UInt32 := ((1 : UInt32) <<< 19) - 1
def MAX_USED : UInt32 := ((1 : UInt32) <<< 5) - 1
/-- `LD_MAX_ARENA = LD_MAX_REF` on 64-bit; capacity in wards. -/
def MAX_ARENA : Nat := 1 <<< 31

namespace ClauseHeader
-- bit positions in word 0
def garbageBit : UInt32 := (1 : UInt32) <<< 19
def quotientBit : UInt32 := (1 : UInt32) <<< 20
def reasonBit : UInt32 := (1 : UInt32) <<< 21
def redundantBit : UInt32 := (1 : UInt32) <<< 22
def shrunkenBit : UInt32 := (1 : UInt32) <<< 23
def subsumeBit : UInt32 := (1 : UInt32) <<< 24
def sweptBit : UInt32 := (1 : UInt32) <<< 25
def vivifyBit : UInt32 := (1 : UInt32) <<< 26
def usedShift : UInt32 := 27
end ClauseHeader

/-- Number of wards occupied by a clause of `size` literals
  (`kissat_bytes_of_clause (size) / sizeof (ward)`). -/
@[inline] def wardsOfClause (size : Nat) : Nat := (3 + size + 3) / 4

/-- The clause arena. `words.size` is always a multiple of 4. -/
structure Arena where
  words : U32Vec := .empty
  deriving Inhabited

namespace Arena

/-- `SIZE_STACK (arena)` in wards. -/
@[inline] def sizeWards (a : Arena) : Nat := a.words.size / 4

@[inline] def base (ref : Ref) : Nat := 4 * ref.toNat

@[inline] def word0 (a : Arena) (ref : Ref) : UInt32 := a.words.get! (base ref)
@[inline] def setWord0 (a : Arena) (ref : Ref) (w : UInt32) : Arena :=
  { a with words := a.words.set! (base ref) w }

@[inline] def glue (a : Arena) (ref : Ref) : UInt32 := a.word0 ref &&& MAX_GLUE
@[inline] def flag (a : Arena) (ref : Ref) (bit : UInt32) : Bool := (a.word0 ref &&& bit) != 0
@[inline] def garbage (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.garbageBit
@[inline] def quotient (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.quotientBit
@[inline] def reason (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.reasonBit
@[inline] def redundant (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.redundantBit
@[inline] def shrunken (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.shrunkenBit
@[inline] def subsume (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.subsumeBit
@[inline] def swept (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.sweptBit
@[inline] def vivify (a : Arena) (ref : Ref) : Bool := a.flag ref ClauseHeader.vivifyBit
@[inline] def used (a : Arena) (ref : Ref) : UInt32 := a.word0 ref >>> ClauseHeader.usedShift

@[inline] def setFlag (a : Arena) (ref : Ref) (bit : UInt32) (b : Bool) : Arena :=
  let w := a.word0 ref
  a.setWord0 ref (if b then w ||| bit else w &&& ~~~bit)
@[inline] def setGarbage (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.garbageBit b
@[inline] def setQuotient (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.quotientBit b
@[inline] def setReason (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.reasonBit b
@[inline] def setRedundant (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.redundantBit b
@[inline] def setShrunken (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.shrunkenBit b
@[inline] def setSubsume (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.subsumeBit b
@[inline] def setSwept (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.sweptBit b
@[inline] def setVivify (a : Arena) (ref : Ref) (b : Bool) : Arena := a.setFlag ref ClauseHeader.vivifyBit b
/-- Set glue; caller ensures `g ≤ MAX_GLUE`. -/
@[inline] def setGlue (a : Arena) (ref : Ref) (g : UInt32) : Arena :=
  a.setWord0 ref ((a.word0 ref &&& ~~~MAX_GLUE) ||| (g &&& MAX_GLUE))
/-- Set used; caller ensures `u ≤ MAX_USED`. -/
@[inline] def setUsed (a : Arena) (ref : Ref) (u : UInt32) : Arena :=
  a.setWord0 ref ((a.word0 ref &&& ((1 <<< ClauseHeader.usedShift) - 1)) |||
    ((u &&& MAX_USED) <<< ClauseHeader.usedShift))

@[inline] def searched (a : Arena) (ref : Ref) : UInt32 := a.words.get! (base ref + 1)
@[inline] def setSearched (a : Arena) (ref : Ref) (v : UInt32) : Arena :=
  { a with words := a.words.set! (base ref + 1) v }
@[inline] def size (a : Arena) (ref : Ref) : UInt32 := a.words.get! (base ref + 2)
@[inline] def setSize (a : Arena) (ref : Ref) (v : UInt32) : Arena :=
  { a with words := a.words.set! (base ref + 2) v }
/-- Word index of literal `i` of clause `ref`. -/
@[inline] def litPos (ref : Ref) (i : Nat) : Nat := base ref + 3 + i
@[inline] def lit (a : Arena) (ref : Ref) (i : Nat) : Lit := a.words.get! (litPos ref i)
@[inline] def setLit (a : Arena) (ref : Ref) (i : Nat) (l : Lit) : Arena :=
  { a with words := a.words.set! (litPos ref i) l }

/-- Literals of a clause as an array (for non-hot code). -/
def lits (a : Arena) (ref : Ref) : Array Lit := Id.run do
  let n := (a.size ref).toNat
  let mut r := Array.emptyWithCapacity n
  for i in [0:n] do
    r := r.push (a.lit ref i)
  return r

/-- Port of `kissat_allocate_clause` + `init_clause` + `memcpy` of literals
  (`arena.c`, `clause.c`). Returns `none` (and the unchanged arena) if the capacity
  `MAX_ARENA` would be exceeded (C: `kissat_fatal`). -/
def allocate (a : Arena) (redundant : Bool) (glue : UInt32) (lits : U32Vec) :
    Option Ref × Arena :=
  match a with
  | { words } =>
  let res := words.size / 4
  let size := lits.size
  let needed := wardsOfClause size
  if res + needed > MAX_ARENA then (none, { words }) else
  let glue := if redundant then min MAX_GLUE glue else 0
  let w0 := glue ||| (if redundant then ClauseHeader.redundantBit else 0)
  let ws := words.push w0
  let ws := ws.push 2
  let ws := ws.push (UInt32.ofNat size)
  let ws := ws.appendFrom lits 0 size
  let ws := ws.pushN 0 (4 * needed - (3 + size))
  (some (UInt32.ofNat res), { words := ws })

/-- Port of `kissat_actual_bytes_of_clause` in wards: skips the `INVALID_LIT`
  terminated tail of shrunken clauses. -/
def actualWards (a : Arena) (ref : Ref) : Nat :=
  let start := litPos ref 0
  let stop := start + (a.size ref).toNat
  let stop :=
    if a.shrunken ref then
      -- `while (*p++ != INVALID_LIT)`: position after the terminator
      let limit := a.words.size
      let rec go (p : Nat) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => p
        | fuel + 1 => if a.words.get! p == INVALID_LIT then p + 1 else go (p + 1) fuel
      go stop (limit - stop)
    else stop
  (stop - base ref + 3) / 4

/-- Port of `kissat_next_clause`. -/
@[inline] def nextClause (a : Arena) (ref : Ref) : Ref :=
  ref + UInt32.ofNat (a.actualWards ref)

end Arena
end LeanKissat

namespace LeanKissat
namespace Arena

/-- The chain of clause references starting at `r` (at most `fuel` of them),
  stopping at the end of the arena. -/
def chain (a : Arena) (r : Ref) : Nat → List Ref
  | 0 => []
  | fuel + 1 => if r.toNat < a.sizeWards then r :: chain a (a.nextClause r) fuel else []

/-- `all_clauses (c)`: references of all clauses in arena order, from `start`.
  -- FUEL: every clause occupies at least one ward, so `sizeWards` steps suffice. -/
def clauseRefsFrom (a : Arena) (start : Ref) : Array Ref :=
  (a.chain start a.sizeWards).toArray

end Arena
end LeanKissat
