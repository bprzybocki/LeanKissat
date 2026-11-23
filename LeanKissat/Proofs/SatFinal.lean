import LeanKissat.Proofs.Defs

/-!
# From the invariants to a model

`sat_of_complete`: in a fully propagated conflict-free state in which every
database literal is assigned, the watch invariant forces every database clause to
be satisfied; with coverage and the import/value consistency this gives a model of
the input CNF.
-/

namespace LeanKissat
namespace Solver
open Std.Sat

/-- Values of complementary literals are consistent. -/
def ValCons (s : Solver) : Prop :=
  ∀ l : Lit, (s.IsTrue l ↔ s.IsFalse (NOT l)) ∧ ¬ (s.IsTrue l ∧ s.IsFalse l)

/-- Every true literal is on the trail, or it is a (flushed) root literal. -/
def TrueOnTrail (s : Solver) : Prop :=
  ∀ l, s.IsTrue l → l ∈ s.trailL ∨ s.lvl l = 0

/-- Levels are per variable. -/
def LvlVar (s : Solver) : Prop := ∀ l, s.lvl (NOT l) = s.lvl l

/-- Every literal of a database clause is assigned (at the end of search). -/
def DBAssigned (s : Solver) : Prop :=
  ∀ c, s.InDB c → ∀ l ∈ c, s.IsTrue l ∨ s.IsFalse l

/-- Database clauses have at least two literals. -/
def DBLen (s : Solver) : Prop := ∀ c, s.InDB c → 2 ≤ c.length

/-- The watch invariant for every database clause. -/
def WatchInv (s : Solver) : Prop := ∀ c, s.InDB c → s.InvS c

/-- Coverage of the input clauses (see `PROOF_PLAN.md`, invariant 3). -/
def Covered (s : Solver) (F : CNF Nat) : Prop :=
  ∀ c ∈ F.clauses,
    (∃ v, (v, true) ∈ c.literals ∧ (v, false) ∈ c.literals) ∨
    (∃ l ∈ c.literals, s.RootTrue (s.intLit (extLit l))) ∨
    (∃ d, s.InIrrDB d ∧ ∀ x ∈ d, (∃ l ∈ c.literals, x = s.intLit (extLit l)) ∨ s.RootFalse x)

/-- The reported model agrees with the internal values on every input literal. -/
def ModelAgrees (s : Solver) (F : CNF Nat) : Prop :=
  ∀ c ∈ F.clauses, ∀ l ∈ c.literals,
    (s.IsTrue (s.intLit (extLit l)) → modelOf s l.1 = l.2)

theorem InDB_of_InIrrDB {s : Solver} {c : List Lit} (h : s.InIrrDB c) : s.InDB c := by
  rcases h with ⟨r, h1, _, h3⟩ | ⟨a, b, h1, h2⟩
  · exact Or.inl ⟨r, h1, h3⟩
  · exact Or.inr ⟨a, b, h1, h2⟩

/-- A false literal is propagated in a complete state. -/
theorem propFalse_of_complete {s : Solver} (hvc : ValCons s) (htt : TrueOnTrail s)
    (hlv : LvlVar s) (hprop : s.propagate = s.trailL.length) {w : Lit} (hw : s.IsFalse w) :
    ∃ k, s.PropFalse w k := by
  have hnw : s.IsTrue (NOT w) := by
    have := (hvc (NOT w)).1
    rw [NOT_NOT] at this
    exact this.mpr hw
  rcases htt _ hnw with hm | h0
  · obtain ⟨p, hp⟩ := List.getElem?_of_mem hm
    have hb : p < s.trailL.length := (List.getElem?_eq_some_iff.mp hp).1
    exact ⟨_, hw, Or.inl ⟨p, hp, by omega, rfl⟩⟩
  · by_cases hm : NOT w ∈ s.trailL
    · obtain ⟨p, hp⟩ := List.getElem?_of_mem hm
      have hb : p < s.trailL.length := (List.getElem?_eq_some_iff.mp hp).1
      exact ⟨_, hw, Or.inl ⟨p, hp, by omega, rfl⟩⟩
    · exact ⟨0, hw, Or.inr ⟨hm, by rw [← hlv w]; exact h0, rfl⟩⟩

/-- In a complete state every database clause has a true literal. -/
theorem db_satisfied {s : Solver} (hvc : ValCons s) (htt : TrueOnTrail s) (hlv : LvlVar s)
    (hprop : s.propagate = s.trailL.length) (hwi : WatchInv s) (hda : DBAssigned s)
    (hdl : DBLen s) {c : List Lit} (hc : s.InDB c) : ∃ t ∈ c, s.IsTrue t := by
  have hlen := hdl c hc
  match c, hlen, hc with
  | w0 :: w1 :: rest, _, hc =>
    refine Classical.byContradiction fun hno => ?_
    have hf : ∀ l ∈ w0 :: w1 :: rest, s.IsFalse l := by
      intro l hl
      rcases hda _ hc l hl with h' | h'
      · exact absurd ⟨l, hl, h'⟩ hno
      · exact h'
    obtain ⟨k0, h0⟩ := propFalse_of_complete hvc htt hlv hprop (hf w0 (by simp))
    obtain ⟨k1, h1⟩ := propFalse_of_complete hvc htt hlv hprop (hf w1 (by simp))
    obtain ⟨t, ht, htt', _⟩ := hwi _ hc w0 w1 rest rfl k0 k1 h0 h1
    exact hno ⟨t, ht, htt'⟩

/-- Main consequence: a complete state yields a model of the input. -/
theorem sat_of_complete {s : Solver} {F : CNF Nat} (hvc : ValCons s) (htt : TrueOnTrail s)
    (hlv : LvlVar s) (hprop : s.propagate = s.trailL.length) (hwi : WatchInv s)
    (hda : DBAssigned s) (hdl : DBLen s) (hcov : Covered s F) (hma : ModelAgrees s F) :
    F.Sat (modelOf s) := by
  rw [CNF.sat_iff_all_mem_sat]
  intro c hcF
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  rcases hcov c hcF with ⟨v, hp, hn⟩ | ⟨l, hl, hrt⟩ | ⟨d, hd, hsub⟩
  · -- tautology: one of `(v, true)`, `(v, false)` agrees with the model
    by_cases hm : modelOf s v = true
    · exact ⟨(v, true), hp, hm⟩
    · exact ⟨(v, false), hn, by simpa using hm⟩
  · exact ⟨l, hl, hma c hcF l hl hrt.1⟩
  · obtain ⟨t, ht, htt'⟩ := db_satisfied hvc htt hlv hprop hwi hda hdl (InDB_of_InIrrDB hd)
    rcases hsub t ht with ⟨l, hl, rfl⟩ | hrf
    · exact ⟨l, hl, hma c hcF l hl htt'⟩
    · exact absurd ⟨htt', hrf.1⟩ (hvc t).2

end Solver
end LeanKissat
