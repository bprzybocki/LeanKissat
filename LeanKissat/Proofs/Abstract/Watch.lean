/-!
# Abstract watch invariant (SAT direction)

An abstract model of Kissat's trail with chronological backtracking: the trail is a
list of literals, every literal has a level, `frames` lists the trail positions at
which decision levels `1, 2, …` started, and `prop` is the propagation pointer.

`pushLevel p` is the decision level that was current when trail position `p` was
pushed. The watch invariant `InvS` for a clause with watches `w0`, `w1` says: if
both watches are false and both negations sit at propagated positions, then the
clause has a true literal whose level is at most the larger of the two push levels.

Main results (used for `solveCNF_sat`):
* `InvS.push`      — assigning a literal at the end of the trail preserves it;
* `InvS.advance`   — moving the propagation pointer over a literal all of whose
                     watching clauses were visited preserves it;
* `InvS.backtrack` — Kissat's backtracking (keep literals of level `≤ b`, in order;
                     reset `prop` to the start of level `b + 1`) preserves it;
* `InvS.sat`       — with a total, fully propagated assignment, `InvS` implies that the
                     clause is satisfied.
-/

namespace LeanKissat.Abstract

variable {L : Type}

/-- Abstract trail state. `frames` are the start positions of levels `1..level`. -/
structure St (L : Type) where
  trail : List L
  lev : L → Nat
  frames : List Nat
  prop : Nat

namespace St

variable (s : St L)

/-- The decision level current when position `p` was pushed. -/
def pushLevel (p : Nat) : Nat := s.frames.countP (· ≤ p)

/-- `l` is on the trail at a propagated position `p`. -/
def Propagated (l : L) (p : Nat) : Prop := s.trail[p]? = some l ∧ p < s.prop

def IsTrue (l : L) : Prop := l ∈ s.trail

end St

/-- The watch invariant for one clause `c` (watches `c[0]`, `c[1]`). -/
def InvS (neg : L → L) (s : St L) (c : List L) : Prop :=
  ∀ w0 w1 rest, c = w0 :: w1 :: rest →
  ∀ q0 q1, s.Propagated (neg w0) q0 → s.Propagated (neg w1) q1 →
  ∃ t ∈ c, s.IsTrue t ∧ s.lev t ≤ max (s.pushLevel q0) (s.pushLevel q1)

theorem pushLevel_mono {s : St L} {p q : Nat} (h : p ≤ q) :
    s.pushLevel p ≤ s.pushLevel q := by
  unfold St.pushLevel
  apply List.countP_mono_left
  intro x _ hx
  simp only [decide_eq_true_eq] at *
  omega

/-! ### Assignment -/

/-- Assign `x` at level `k`: push it at the end of the trail. -/
def St.push [DecidableEq L] (s : St L) (neg : L → L) (x : L) (k : Nat) : St L :=
  { s with trail := s.trail ++ [x],
           lev := fun l => if l = x ∨ l = neg x then k else s.lev l }

theorem InvS.push [DecidableEq L] {neg : L → L} {s : St L} {c : List L} {x : L} {k : Nat}
    (h : InvS neg s c) (hprop : s.prop ≤ s.trail.length)
    (hx : x ∉ s.trail) (hnx : neg x ∉ s.trail) :
    InvS neg (s.push neg x k) c := by
  intro w0 w1 rest hc q0 q1 h0 h1
  have back : ∀ l q, (s.push neg x k).Propagated l q → s.Propagated l q := by
    intro l q ⟨ha, hq⟩
    refine ⟨?_, hq⟩
    have : q < s.trail.length := by
      have : q < s.prop := hq; omega
    simpa [St.push, List.getElem?_append_left this] using ha
  obtain ⟨t, ht, htt, hlev⟩ := h w0 w1 rest hc q0 q1 (back _ _ h0) (back _ _ h1)
  refine ⟨t, ht, List.mem_append_left _ htt, ?_⟩
  have h1 : t ≠ x := fun e => hx (e ▸ htt)
  have h2 : t ≠ neg x := fun e => hnx (e ▸ htt)
  simpa [St.push, h1, h2, St.pushLevel] using hlev

/-! ### Advancing the propagation pointer -/

theorem InvS.advance {neg : L → L} (hneg : ∀ l, neg (neg l) = l) {s : St L} {c : List L}
    {lit : L} (h : InvS neg s c) (hlit : s.trail[s.prop]? = some lit)
    (hvisit : ∀ w0 w1 rest, c = w0 :: w1 :: rest → (w0 = neg lit ∨ w1 = neg lit) →
      ∃ t ∈ c, s.IsTrue t ∧ s.lev t ≤ s.pushLevel s.prop) :
    InvS neg { s with prop := s.prop + 1 } c := by
  intro w0 w1 rest hc q0 q1 ⟨a0, b0⟩ ⟨a1, b1⟩
  simp only at a0 b0 a1 b1
  by_cases e0 : q0 = s.prop
  · subst e0
    have : neg w0 = lit := by rw [hlit] at a0; exact (Option.some.inj a0).symm
    have hw : w0 = neg lit := by rw [← this, hneg]
    obtain ⟨t, ht, htt, hl⟩ := hvisit w0 w1 rest hc (Or.inl hw)
    exact ⟨t, ht, htt, Nat.le_trans hl (Nat.le_max_left _ _)⟩
  by_cases e1 : q1 = s.prop
  · subst e1
    have : neg w1 = lit := by rw [hlit] at a1; exact (Option.some.inj a1).symm
    have hw : w1 = neg lit := by rw [← this, hneg]
    obtain ⟨t, ht, htt, hl⟩ := hvisit w0 w1 rest hc (Or.inr hw)
    exact ⟨t, ht, htt, Nat.le_trans hl (Nat.le_max_right _ _)⟩
  exact h w0 w1 rest hc q0 q1 ⟨a0, by omega⟩ ⟨a1, by omega⟩

/-! ### Backtracking -/

/-- Kissat's backtracking to level `b`: positions below `n = frames[b]` (the start of
  level `b + 1`) stay, later literals of level `≤ b` are kept in order; the
  propagation pointer is reset to `n`. -/
def St.backtrack (s : St L) (b n : Nat) : St L :=
  { s with trail := s.trail.take n ++ (s.trail.drop n).filter (fun l => decide (s.lev l ≤ b)),
           frames := s.frames.take b,
           prop := n }

theorem pushLevel_backtrack {s : St L} {b n p : Nat}
    (hsorted : s.frames.Pairwise (· ≤ ·)) (hn : s.frames[b]? = some n) (hp : p < n) :
    (s.backtrack b n).pushLevel p = s.pushLevel p ∧ s.pushLevel p ≤ b := by
  unfold St.pushLevel St.backtrack
  simp only
  have hsplit : s.frames = s.frames.take b ++ s.frames.drop b := (List.take_append_drop _ _).symm
  have hdrop : ∀ y ∈ s.frames.drop b, n ≤ y := by
    have hb : b < s.frames.length := by
      rcases Nat.lt_or_ge b s.frames.length with hc | hc
      · exact hc
      · simp [List.getElem?_eq_none hc] at hn
    have hd : s.frames.drop b = n :: s.frames.drop (b + 1) := by
      rw [List.drop_eq_getElem_cons hb]
      congr
      rw [List.getElem?_eq_getElem hb] at hn
      exact Option.some.inj hn
    intro y hy
    rw [hd] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Nat.le_refl _
    · -- `frames` is sorted: every element after position `b` is `≥ frames[b] = n`
      have hpw := hsorted
      rw [hsplit, hd] at hpw
      have := (List.pairwise_append.mp hpw).2.1
      exact (List.pairwise_cons.mp this).1 y hy
  have hzero : (s.frames.drop b).countP (· ≤ p) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy
    have := hdrop y hy
    simp only [decide_eq_true_eq]
    omega
  constructor
  · conv => rhs; rw [hsplit]
    rw [List.countP_append, hzero, Nat.add_zero]
  · conv => lhs; rw [hsplit]
    rw [List.countP_append, hzero, Nat.add_zero]
    exact Nat.le_trans (List.countP_le_length) (List.length_take_le _ _)

theorem InvS.backtrack {neg : L → L} {s : St L} {c : List L} {b n : Nat}
    (h : InvS neg s c) (hsorted : s.frames.Pairwise (· ≤ ·)) (hn : s.frames[b]? = some n)
    (hnprop : n ≤ s.prop) (hnlen : n ≤ s.trail.length) :
    InvS neg (s.backtrack b n) c := by
  intro w0 w1 rest hc q0 q1 ⟨a0, b0⟩ ⟨a1, b1⟩
  simp only [St.backtrack] at a0 b0 a1 b1
  have keep : ∀ l q, q < n → (s.trail.take n ++ (s.trail.drop n).filter
      (fun l => decide (s.lev l ≤ b)))[q]? = some l → s.trail[q]? = some l := by
    intro l q hq e
    have hq' : q < (s.trail.take n).length := by simp; omega
    rw [List.getElem?_append_left hq', List.getElem?_take] at e
    simpa [hq] using e
  obtain ⟨t, ht, htt, hl⟩ := h w0 w1 rest hc q0 q1
    ⟨keep _ _ b0 a0, by omega⟩ ⟨keep _ _ b1 a1, by omega⟩
  obtain ⟨e0, l0⟩ := pushLevel_backtrack hsorted hn b0
  obtain ⟨e1, l1⟩ := pushLevel_backtrack hsorted hn b1
  refine ⟨t, ht, ?_, ?_⟩
  · -- the witness survives: its level is `≤ b`
    have htb : s.lev t ≤ b := by omega
    show t ∈ s.trail.take n ++ (s.trail.drop n).filter (fun l => decide (s.lev l ≤ b))
    have : t ∈ s.trail.take n ++ s.trail.drop n := by rw [List.take_append_drop]; exact htt
    rcases List.mem_append.mp this with h1 | h1
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨h1, by simpa using htb⟩)
  · show s.lev t ≤ max ((s.backtrack b n).pushLevel q0) ((s.backtrack b n).pushLevel q1)
    rw [e0, e1]; exact hl

/-! ### Consequence: satisfied clauses -/

theorem InvS.sat {neg : L → L} {s : St L} {c : List L} (h : InvS neg s c)
    (hlen : 2 ≤ c.length) (hprop : s.prop = s.trail.length)
    (htotal : ∀ l ∈ c, s.IsTrue l ∨ s.IsTrue (neg l)) :
    ∃ t ∈ c, s.IsTrue t := by
  match c, hlen with
  | w0 :: w1 :: rest, _ =>
    refine Classical.byContradiction fun hno => ?_
    have hf : ∀ l ∈ w0 :: w1 :: rest, s.IsTrue (neg l) := by
      intro l hl
      rcases htotal l hl with h' | h'
      · exact absurd ⟨l, hl, h'⟩ hno
      · exact h'
    obtain ⟨q0, hq0⟩ := List.getElem?_of_mem (hf w0 (by simp))
    obtain ⟨q1, hq1⟩ := List.getElem?_of_mem (hf w1 (by simp))
    have hb0 : q0 < s.trail.length := (List.getElem?_eq_some_iff.mp hq0).1
    have hb1 : q1 < s.trail.length := (List.getElem?_eq_some_iff.mp hq1).1
    obtain ⟨t, ht, htt, _⟩ := h w0 w1 rest rfl q0 q1 ⟨hq0, by omega⟩ ⟨hq1, by omega⟩
    exact hno ⟨t, ht, htt⟩

end LeanKissat.Abstract
