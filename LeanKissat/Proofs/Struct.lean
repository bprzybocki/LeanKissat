import LeanKissat.Proofs.Assign

/-!
# Structural invariants: levels/frames and watch lists
-/

namespace LeanKissat
namespace Solver

/-! ### Levels and frames -/

/-- Level bookkeeping (trail positions, frames, propagation pointer). -/
structure LevelOK (s : Solver) : Prop where
  /-- true literals have level at most the current level -/
  trueLe : ∀ l, s.IsTrue l → s.lvl l ≤ s.level.toNat
  /-- a trail literal's level is at most the level current when it was pushed -/
  pushLe : ∀ p l, s.trailL[p]? = some l → s.lvl l ≤ s.pushLevel p
  /-- frames are sorted -/
  sorted : s.framesL.Pairwise (· ≤ ·)
  /-- one frame per decision level -/
  len : s.framesL.length = s.level.toNat
  /-- every decision level started at or before the propagation pointer -/
  framesLe : ∀ f ∈ s.framesL, f ≤ s.propagate
  /-- the propagation pointer is inside the trail -/
  propLe : s.propagate ≤ s.trailL.length
  /-- frames are strictly increasing (every decision level starts with its decision) -/
  strict : s.framesL.Pairwise (· < ·)
  /-- every frame start holds a trail literal (the decision) -/
  framesLt : ∀ f ∈ s.framesL, f < s.trailL.length
  /-- the root frame exists -/
  frames0 : 1 ≤ s.frameTrail.size

/-- Positions at or after the propagation pointer were pushed at the current level. -/
theorem LevelOK.pushLevel_cur {s : Solver} (h : s.LevelOK) {p : Nat} (hp : s.propagate ≤ p) :
    s.pushLevel p = s.level.toNat := by
  unfold pushLevel
  rw [← h.len, List.countP_eq_length]
  intro f hf
  have := h.framesLe f hf
  simp only [decide_eq_true_eq]; omega

/-! ### Watch lists -/

/-- First / second watch of a large clause. -/
def lit0 (s : Solver) (r : Ref) : Lit := s.arena.lit r 0
def lit1 (s : Solver) (r : Ref) : Lit := s.arena.lit r 1

/-- Number of large entries for reference `r`. -/
def countRef (r : Ref) : List WEntry → Nat
  | [] => 0
  | .large _ r' :: es => (if r' = r then 1 else 0) + countRef r es
  | .bin _ :: es => countRef r es

/-- The raw words of a watch list parse completely (no dangling large head). -/
def WordsOK : List UInt32 → Prop
  | [] => True
  | w :: rest =>
    if watchIsBinary w then WordsOK rest
    else match rest with
      | t :: rest' => watchIsBinary t = false ∧ WordsOK rest'
      | [] => False

/-- Watch-list structure. -/
structure WatchStruct (s : Solver) : Prop where
  /-- all watch lists parse completely -/
  words : ∀ l, WordsOK (s.watchesOf l).data.toList
  /-- large entries point to arena clauses; for live clauses they are on a watch and
    the blocking literal belongs to the clause -/
  refOK : ∀ l b r, WEntry.large b r ∈ s.entries l → r ∈ s.refsL ∧
    (s.arena.garbage r = false → (l = s.lit0 r ∨ l = s.lit1 r) ∧ b ∈ s.clauseL r)
  /-- live clauses: shape and exactly one entry on each watch -/
  live : ∀ r, s.LiveRef r →
    3 ≤ (s.arena.size r).toNat ∧ (s.clauseL r).Nodup ∧
    2 ≤ (s.arena.searched r).toNat ∧ (s.arena.searched r).toNat < (s.arena.size r).toNat ∧
    countRef r (s.entries (s.lit0 r)) = 1 ∧ countRef r (s.entries (s.lit1 r)) = 1 ∧
    (∀ x ∈ s.clauseL r, s.ValidLit x)
  /-- binary watches are symmetric and use valid, distinct literals -/
  bin : ∀ a b, s.BinWatched a b → s.BinWatched b a ∧ s.ValidLit a ∧ s.ValidLit b ∧ a ≠ b
  /-- no pending delayed watches -/
  delayed : s.delayed.size = 0
  /-- one watch list per literal -/
  watchesSize : 2 * s.vars.toNat ≤ s.watches.size
  /-- `INTERNAL_MAX_VAR`: literals fit in 31 bits -/
  varsBound : s.vars.toNat < 2 ^ 30

end Solver
end LeanKissat
