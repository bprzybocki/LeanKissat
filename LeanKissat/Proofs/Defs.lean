import LeanKissat.Proofs.Spec
import LeanKissat.Proofs.Vec

/-!
# Semantic view of a concrete solver state

Definitions used by the invariants (see `PROOF_PLAN.md`). All of them read the
concrete fields through the total accessors used by the code (`get!`), so that
lemmas about the executable functions can be stated directly.
-/

namespace LeanKissat
namespace Solver
open Std.Sat

/-! ### Literal values -/

/-- `values[l] > 0`. -/
def IsTrue (s : Solver) (l : Lit) : Prop := s.asg.values.get! l.toNat = VAL_TRUE
/-- `values[l] < 0`. -/
def IsFalse (s : Solver) (l : Lit) : Prop := s.asg.values.get! l.toNat = VAL_FALSE
/-- Level of the variable of `l`. -/
def lvl (s : Solver) (l : Lit) : Nat := (s.asg.aLevel.get! (IDX l).toNat).toNat
/-- `l` is true at decision level 0. -/
def RootTrue (s : Solver) (l : Lit) : Prop := s.IsTrue l ∧ s.lvl l = 0
/-- `l` is false at decision level 0. -/
def RootFalse (s : Solver) (l : Lit) : Prop := s.IsFalse l ∧ s.lvl l = 0

/-! ### Trail -/

def trailL (s : Solver) : List Lit := s.asg.trail.view

/-- Start positions of decision levels `1 .. level` (`frames[1..].trail`). -/
def framesL (s : Solver) : List Nat := (s.frameTrail.view.drop 1).map UInt32.toNat

/-- The decision level that was current when trail position `p` was pushed. -/
def pushLevel (s : Solver) (p : Nat) : Nat := s.framesL.countP (· ≤ p)

/-- The negation of `w` was propagated (relative to propagation pointer `P`), with
  push level `k`: either it sits on the trail before `P`, or it is a root-level
  literal that has already been flushed from the trail. -/
def PropFalseAt (s : Solver) (P : Nat) (w : Lit) (k : Nat) : Prop :=
  s.IsFalse w ∧
  ((∃ p, s.trailL[p]? = some (NOT w) ∧ p < P ∧ k = s.pushLevel p) ∨
   (NOT w ∉ s.trailL ∧ s.lvl w = 0 ∧ k = 0))

abbrev PropFalse (s : Solver) (w : Lit) (k : Nat) : Prop := s.PropFalseAt s.propagate w k

/-! ### Clauses -/

/-- Literals of the large clause at `r`. -/
def clauseL (s : Solver) (r : Ref) : List Lit :=
  (List.range (s.arena.size r).toNat).map (s.arena.lit r)

/-- Clause references of the arena, in arena order. -/
def refsL (s : Solver) : List Ref := s.arena.chain 0 s.arena.sizeWards

/-- `r` is a live (non-garbage) large clause. -/
def LiveRef (s : Solver) (r : Ref) : Prop := r ∈ s.refsL ∧ s.arena.garbage r = false

/-- A parsed watch-list entry. -/
inductive WEntry where
  | bin (other : Lit)
  | large (blocking : Lit) (ref : Ref)
  deriving DecidableEq, Repr

/-- Parse the raw words of a watch list into entries (a binary watch is one word,
  a large watch is a blocking-literal word followed by a reference word). -/
def parseWatches : List UInt32 → List WEntry
  | [] => []
  | w :: rest =>
    if watchIsBinary w then .bin (watchLit w) :: parseWatches rest
    else match rest with
      | t :: rest' => .large (watchLit w) (watchRef t) :: parseWatches rest'
      | [] => []

/-- Entries of the watch list of `l`. -/
def entries (s : Solver) (l : Lit) : List WEntry := parseWatches (s.watchesOf l).data.toList

/-- The binary clause `(a ∨ b)` is in the watch list of `a`. -/
def BinWatched (s : Solver) (a b : Lit) : Prop := WEntry.bin b ∈ s.entries a

/-- The clause database as lists of internal literals. -/
def InDB (s : Solver) (c : List Lit) : Prop :=
  (∃ r, s.LiveRef r ∧ c = s.clauseL r) ∨ (∃ a b, s.BinWatched a b ∧ c = [a, b])

/-- The irredundant part of the database (all binary clauses are irredundant). -/
def InIrrDB (s : Solver) (c : List Lit) : Prop :=
  (∃ r, s.LiveRef r ∧ s.arena.redundant r = false ∧ c = s.clauseL r) ∨
  (∃ a b, s.BinWatched a b ∧ c = [a, b])

/-! ### Watch invariant -/

/-- Watch invariant for a clause (first two literals are the watches), relative to
  propagation pointer `P`. -/
def InvSAt (s : Solver) (P : Nat) (c : List Lit) : Prop :=
  ∀ w0 w1 rest, c = w0 :: w1 :: rest →
  ∀ k0 k1, s.PropFalseAt P w0 k0 → s.PropFalseAt P w1 k1 →
  ∃ t ∈ c, s.IsTrue t ∧ s.lvl t ≤ max k0 k1

abbrev InvS (s : Solver) (c : List Lit) : Prop := s.InvSAt s.propagate c

/-! ### External view -/

/-- Internal literal of an external literal (`kissat_import_literal`, read only). -/
def intLit (s : Solver) (e : Int) : Lit :=
  let l := s.importLit.get! e.natAbs
  if e < 0 then NOT l else l

/-- Truth of an external literal under an assignment of the CNF variables
  (`v` is external variable `v + 1`). -/
def extSat (α : Nat → Bool) (e : Int) : Bool :=
  if e < 0 then !α (e.natAbs - 1) else α (e.natAbs - 1)

end Solver
end LeanKissat
