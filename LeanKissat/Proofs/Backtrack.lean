import LeanKissat.Proofs.SearchProp

/-!
# Backtracking
-/

namespace LeanKissat
namespace Solver
open Arena

/-- Literals kept by backtracking. -/
def keepB (a0 : Asg) (newLevel : UInt32) (l : Lit) : Bool :=
  Decidable.decide (a0.aLevel.get! (IDX l).toNat ≤ newLevel)

/-- The processed segment of the trail. -/
def segB (a0 : Asg) (newEnd p : Nat) : List Lit := (a0.trail.view.drop newEnd).take (p - newEnd)

def removedB (a0 : Asg) (newLevel : UInt32) (newEnd p : Nat) : List Lit :=
  (segB a0 newEnd p).filter (fun l => !keepB a0 newLevel l)
def keptB (a0 : Asg) (newLevel : UInt32) (newEnd p : Nat) : List Lit :=
  (segB a0 newEnd p).filter (keepB a0 newLevel)

structure BLInv (a0 : Asg) (newLevel : UInt32) (newEnd : Nat) (a : Asg) (p q : Nat) : Prop where
  size : a.trail.size = a0.trail.size
  le : newEnd ≤ p
  pl : p ≤ a0.trail.size
  hq : q = newEnd + (keptB a0 newLevel newEnd p).length
  take : a.trail.view.take q = a0.trail.view.take newEnd ++ keptB a0 newLevel newEnd p
  drop : a.trail.view.drop p = a0.trail.view.drop p
  aLevel : a.aLevel = a0.aLevel
  aReason : a.aReason = a0.aReason
  aBits : a.aBits = a0.aBits
  vsize : a.values.size = a0.values.size
  values : ∀ j, a.values.get! j =
    if ∃ l ∈ removedB a0 newLevel newEnd p, j = l.toNat ∨ j = (NOT l).toNat then 0 else a0.values.get! j
  unassigned : a.unassigned.toNat = a0.unassigned.toNat + (removedB a0 newLevel newEnd p).length

theorem segB_succ (a0 : Asg) (newEnd p : Nat) (h1 : newEnd ≤ p) (h2 : p < a0.trail.view.length) :
    segB a0 newEnd (p + 1) = segB a0 newEnd p ++ [a0.trail.view[p]] := by
  unfold segB
  rw [show p + 1 - newEnd = (p - newEnd) + 1 by omega, List.take_add_one]
  congr
  rw [List.getElem?_drop]
  rw [show newEnd + (p - newEnd) = p by omega, List.getElem?_eq_getElem h2]
  rfl

theorem take_set_succ (L : List Lit) (q : Nat) (x : Lit) (hq : q < L.length) :
    (L.set q x).take (q + 1) = L.take q ++ [x] := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.getElem_take, List.getElem_set, List.getElem_append]
  by_cases e : j < q
  · simp [show q ≠ j by omega]; intro h; omega
  · have : j = q := by simp at h1; omega
    subst this; simp; intro h; omega

theorem backtrackLoop_spec (a0 : Asg) (newLevel : UInt32) (newEnd : Nat)
    (hvalid : ∀ l ∈ a0.trail.view, l.toNat < a0.values.size ∧ (NOT l).toNat < a0.values.size)
    (hun : a0.unassigned.toNat + a0.trail.size < 2 ^ 32)
    (a : Asg) (s : Solver) (p q : Nat) :
    BLInv a0 newLevel newEnd a p q →
    let r := backtrackLoop a s newLevel p q a0.trail.size
    BLInv a0 newLevel newEnd r.1 a0.trail.size r.2.2 := by
  fun_induction backtrackLoop a s newLevel p q a0.trail.size with
  | case1 a s p q hp lit idx level hkeep a' ih =>
    intro h
    apply ih
    have hlen : p < a0.trail.view.length := by simpa using hp
    have hsz : p < a.trail.view.length := by simp [h.size]; exact hp
    have hdp : a.trail.view[p] = a0.trail.view[p] := by
      have := congrArg (fun L => L[0]?) h.drop
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hsz,
        List.getElem?_eq_getElem hlen, Option.some.injEq] at this
      exact this
    have hlit : lit = a0.trail.view[p] := by
      simp only [lit, U32Vec.get!_eq_view, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hsz, Option.getD_some]; exact hdp
    have hk : keepB a0 newLevel a0.trail.view[p] = true := by
      unfold keepB; rw [← hlit, ← h.aLevel]; simpa using hkeep
    have hseg := segB_succ a0 newEnd p h.le hlen
    have hkept : keptB a0 newLevel newEnd (p + 1) = keptB a0 newLevel newEnd p ++ [a0.trail.view[p]] := by
      unfold keptB; rw [hseg, List.filter_append]; simp [hk]
    have hrem : removedB a0 newLevel newEnd (p + 1) = removedB a0 newLevel newEnd p := by
      unfold removedB; rw [hseg, List.filter_append]; simp [hk]
    have hqp : q ≤ p := by
      have := h.hq
      have : (keptB a0 newLevel newEnd p).length ≤ (segB a0 newEnd p).length := List.length_filter_le _ _
      have : (segB a0 newEnd p).length ≤ p - newEnd := by unfold segB; simp; omega
      have := h.le
      omega
    have hqv : q < a.trail.view.length := by omega
    refine ⟨?_, by have := h.le; omega, by omega, ?_, ?_, ?_, h.aLevel, h.aReason, h.aBits, h.vsize,
      by rw [hrem]; exact h.values, by rw [hrem]; exact h.unassigned⟩
    · simp [a', h.size]
    · rw [hkept, h.hq]; simp; omega
    · show (a.trail.set! q lit).view.take (q + 1) = _
      rw [U32Vec.view_set!, take_set_succ _ _ _ hqv, h.take, hkept, hlit]; simp
    · show (a.trail.set! q lit).view.drop (p + 1) = _
      rw [U32Vec.view_set!, List.drop_set_of_lt (by omega)]
      have := congrArg (List.drop 1) h.drop
      simpa [List.drop_drop, Nat.add_comm] using this
  | case2 a s p q hp lit idx level hkeep notLit a' s' ih =>
    intro h
    apply ih
    have hlen : p < a0.trail.view.length := by simpa using hp
    have hsz : p < a.trail.view.length := by simp [h.size]; exact hp
    have hdp : a.trail.view[p] = a0.trail.view[p] := by
      have := congrArg (fun L => L[0]?) h.drop
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hsz,
        List.getElem?_eq_getElem hlen, Option.some.injEq] at this
      exact this
    have hlit : lit = a0.trail.view[p] := by
      simp only [lit, U32Vec.get!_eq_view, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hsz, Option.getD_some]; exact hdp
    have hk : keepB a0 newLevel a0.trail.view[p] = false := by
      unfold keepB; rw [← hlit, ← h.aLevel]; simpa using hkeep
    have hseg := segB_succ a0 newEnd p h.le hlen
    have hkept : keptB a0 newLevel newEnd (p + 1) = keptB a0 newLevel newEnd p := by
      unfold keptB; rw [hseg, List.filter_append]; simp [hk]
    have hrem : removedB a0 newLevel newEnd (p + 1) = removedB a0 newLevel newEnd p ++ [a0.trail.view[p]] := by
      unfold removedB; rw [hseg, List.filter_append]; simp [hk]
    have hv := hvalid _ (List.getElem_mem hlen)
    have hremlen : (removedB a0 newLevel newEnd p).length ≤ p - newEnd := by
      have : (removedB a0 newLevel newEnd p).length ≤ (segB a0 newEnd p).length := List.length_filter_le _ _
      have : (segB a0 newEnd p).length ≤ p - newEnd := by unfold segB; simp; omega
      omega
    refine ⟨h.size, by have := h.le; omega, by omega, by rw [hkept]; exact h.hq,
      by rw [hkept]; exact h.take, ?_, h.aLevel, h.aReason, h.aBits, ?_, ?_, ?_⟩
    · have := congrArg (List.drop 1) h.drop
      simpa [List.drop_drop, Nat.add_comm, a'] using this
    · simp [a', h.vsize]
    · intro j
      show ((a.values.set! lit.toNat 0).set! notLit.toNat 0).get! j = _
      rw [ByteArray.get!_set!, ByteArray.get!_set!, h.values j, hrem]
      simp only [ByteArray.size_set!', h.vsize]
      rw [← hlit] at hv ⊢
      by_cases e1 : notLit.toNat = j
      · rw [ite_eq_left ⟨e1, hv.2⟩, ite_eq_left ⟨lit, by simp, Or.inr e1.symm⟩]
      · rw [ite_eq_right (fun h => e1 h.1)]
        by_cases e2 : lit.toNat = j
        · rw [ite_eq_left ⟨e2, hv.1⟩, ite_eq_left ⟨lit, by simp, Or.inl e2.symm⟩]
        · rw [ite_eq_right (fun h => e2 h.1)]
          have : (∃ l ∈ removedB a0 newLevel newEnd p ++ [lit], j = l.toNat ∨ j = (NOT l).toNat) ↔
              (∃ l ∈ removedB a0 newLevel newEnd p, j = l.toNat ∨ j = (NOT l).toNat) := by
            constructor
            · rintro ⟨l, hl, hj⟩
              rcases List.mem_append.mp hl with hl | hl
              · exact ⟨l, hl, hj⟩
              · simp at hl; subst hl
                rcases hj with hj | hj
                · exact absurd hj.symm e2
                · exact absurd hj.symm e1
            · rintro ⟨l, hl, hj⟩; exact ⟨l, List.mem_append_left _ hl, hj⟩
          simp only [this]
    · show (a.unassigned + 1).toNat = _
      rw [hrem, List.length_append, List.length_singleton, UInt32.toNat_add, h.unassigned]
      have := h.le
      have : (1 : UInt32).toNat = 1 := rfl
      rw [this, Nat.mod_eq_of_lt (by omega)]
      omega
  | case3 a s p q hp =>
    intro h
    have : p = a0.trail.size := by have := h.pl; omega
    subst this
    exact h

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The tail of `backtrackWithoutUpdatingPhases`. -/
def btFinish (newLevel : UInt32) (newEnd : Nat) (r : Asg × Solver × Nat) : Solver :=
  match r with
  | (a, s, q) => { s with asg := { a with trail := a.trail.shrink q }, level := newLevel, propagate := newEnd }

theorem backtrack_eq (s : Solver) (newLevel : UInt32) (h : s.level ≠ newLevel) :
    s.backtrackWithoutUpdatingPhases newLevel =
      btFinish newLevel (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat
        (backtrackLoop s.asg ({ s.shrinkFrames (newLevel.toNat + 1) with asg := {} }) newLevel
          (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat
          (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat s.asg.trail.size) := by
  unfold backtrackWithoutUpdatingPhases
  have : (s.level == newLevel) = false := by simpa using h
  rw [ite_eq_right (by simp [this])]
  rfl

/-- Fields not touched by the backtracking loop. -/
structure BTS (r s : Solver) : Prop where
  arena : r.arena = s.arena
  watches : r.watches = s.watches
  delayed : r.delayed = s.delayed
  vars : r.vars = s.vars
  frameTrail : r.frameTrail = s.frameTrail
  options : r.options = s.options
  importLit : r.importLit = s.importLit
  inconsistent : r.inconsistent = s.inconsistent
  c0 : r.conflictLit0 = s.conflictLit0
  c1 : r.conflictLit1 = s.conflictLit1

theorem BTS.refl (s : Solver) : BTS s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BTS.trans {a b c : Solver} (h1 : BTS a b) (h2 : BTS b c) : BTS a c :=
  ⟨h1.arena.trans h2.arena, h1.watches.trans h2.watches, h1.delayed.trans h2.delayed,
   h1.vars.trans h2.vars, h1.frameTrail.trans h2.frameTrail, h1.options.trans h2.options,
   h1.importLit.trans h2.importLit, h1.inconsistent.trans h2.inconsistent, h1.c0.trans h2.c0,
   h1.c1.trans h2.c1⟩

theorem backtrackLoop_s (a : Asg) (s : Solver) (newLevel : UInt32) (p q stop : Nat) :
    BTS (backtrackLoop a s newLevel p q stop).2.1 s := by
  fun_induction backtrackLoop a s newLevel p q stop with
  | case1 => assumption
  | case2 a s p q hp lit idx level hkeep notLit a' s' ih =>
    refine ih.trans ?_
    simp only [s']
    split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact BTS.refl _
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | case3 => exact BTS.refl _

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem frameTrailAt_eq (s : Solver) (hL : s.LevelOK) (j : Nat) (hj : j < s.level.toNat) :
    (s.frameTrailAt (UInt32.ofNat (j + 1))).toNat = s.framesL[j]'(by rw [hL.len]; exact hj) := by
  have hlen := hL.len
  unfold framesL at hlen ⊢
  simp only [List.getElem_map, List.getElem_drop]
  unfold frameTrailAt
  have hv : j + 1 < s.frameTrail.view.length := by simp at hlen; simp; omega
  rw [U32Vec.get!_eq_view, List.getD_eq_getElem?_getD]
  have : (UInt32.ofNat (j + 1)).toNat = j + 1 := by
    simp; have := s.level.toNat_lt; omega
  rw [this, List.getElem?_eq_getElem hv, Option.getD_some]
  congr 1; simp [Nat.add_comm]

/-- Relation between a state and the state after backtracking. -/
structure BTRel (s t : Solver) (newLevel : UInt32) : Prop where
  arena : t.arena = s.arena
  watches : t.watches = s.watches
  delayed : t.delayed = s.delayed
  vars : t.vars = s.vars
  options : t.options = s.options
  importLit : t.importLit = s.importLit
  inconsistent : t.inconsistent = s.inconsistent
  aLevel : t.asg.aLevel = s.asg.aLevel
  aReason : t.asg.aReason = s.asg.aReason
  aBits : t.asg.aBits = s.asg.aBits
  trueTo : ∀ l, t.IsTrue l → s.IsTrue l
  falseTo : ∀ l, t.IsFalse l → s.IsFalse l
  keep : ∀ l, s.IsTrue l → s.lvl l ≤ newLevel.toNat → t.IsTrue l

theorem countP_le_of_sorted : ∀ (L : List Nat) (k p : Nat), L.Pairwise (· ≤ ·) → (hk : k < L.length) →
    p < L[k] → L.countP (· ≤ p) = (L.take k).countP (· ≤ p)
  | [], _, _, _, hk, _ => by simp at hk
  | x :: xs, 0, p, hs, _, hp => by
    simp only [List.getElem_cons_zero] at hp
    simp only [List.take_zero, List.countP_nil]
    rw [List.countP_eq_zero]
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · simp; omega
    · have := (List.pairwise_cons.mp hs).1 y hy; simp; omega
  | x :: xs, k + 1, p, hs, hk, hp => by
    simp only [List.getElem_cons_succ] at hp
    rw [List.take_succ_cons, List.countP_cons, List.countP_cons,
      countP_le_of_sorted xs k p (List.pairwise_cons.mp hs).2 (by simpa using hk) hp]

theorem countP_take_sorted : ∀ (L : List Nat) (k p : Nat), L.Pairwise (· ≤ ·) → (hk : k < L.length) →
    L[k] ≤ p → (L.take k).countP (· ≤ p) = k
  | [], _, _, _, hk, _ => by simp at hk
  | x :: xs, 0, p, _, _, _ => by simp
  | x :: xs, k + 1, p, hs, hk, hp => by
    simp only [List.getElem_cons_succ] at hp
    have hx : x ≤ xs[k]'(by simpa using hk) :=
      (List.pairwise_cons.mp hs).1 _ (List.getElem_mem _)
    rw [List.take_succ_cons, List.countP_cons,
      countP_take_sorted xs k p (List.pairwise_cons.mp hs).2 (by simpa using hk) hp]
    simp; omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem countP_remove (p : Nat → Bool) (n : Nat) : ∀ (S : List Nat), S.Nodup → (∀ v ∈ S, v < n ∧ p v = true) →
    (List.range n).countP (fun v => p v && !(S.contains v)) + S.length = (List.range n).countP p := by
  intro S
  induction S with
  | nil => intro _ _; simp
  | cons v S ih =>
    intro hnd hS
    rw [List.nodup_cons] at hnd
    have h1 := ih hnd.2 (fun w hw => hS w (List.mem_cons_of_mem _ hw))
    have hv := hS v (List.mem_cons_self ..)
    have := countP_range_update (fun w => p w && !((v :: S).contains w)) (fun w => p w && !(S.contains w)) v
      (by simp [hv.2, hnd.1]) (by simp)
      (by intro w hw; simp [hw]) n hv.1
    simp only [List.length_cons]
    omega

theorem mem_take_pos {L : List Lit} {N : Nat} {l : Lit} (h : l ∈ L.take N) :
    ∃ p, p < N ∧ L[p]? = some l := by
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_take] at hp
  split at hp
  · exact ⟨p, by assumption, hp⟩
  · simp at hp

theorem le_of_mem_take_sorted {L : List Nat} (hs : L.Pairwise (· ≤ ·)) {k : Nat} (hk : k < L.length)
    {f : Nat} (hf : f ∈ L.take k) : f ≤ L[k] := by
  have e := List.take_append_drop k L
  rw [← e] at hs
  have hmem : L[k] ∈ L.drop k := by
    rw [List.mem_iff_getElem]; exact ⟨0, by simp; omega, by simp⟩
  exact (List.pairwise_append.mp hs).2.2 f hf _ hmem

theorem lt_of_mem_take_strict {L : List Nat} (hs : L.Pairwise (· < ·)) {k : Nat} (hk : k < L.length)
    {f : Nat} (hf : f ∈ L.take k) : f < L[k] := by
  have e := List.take_append_drop k L
  rw [← e] at hs
  have hmem : L[k] ∈ L.drop k := by
    rw [List.mem_iff_getElem]; exact ⟨0, by simp; omega, by simp⟩
  exact (List.pairwise_append.mp hs).2.2 f hf _ hmem

theorem backtrack_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {newLevel : UInt32}
    (hlt : newLevel < s.level) {P : Nat} (hP : ∀ c, s.InDB c → s.InvSAt P c)
    (hPle : s.framesL[newLevel.toNat]'(by rw [hs.levelOK.len]; exact UInt32.lt_iff_toNat_lt.mp hlt) ≤ P) :
    let t := s.backtrackWithoutUpdatingPhases newLevel
    SInv Φ t ∧ t.level = newLevel ∧
    t.propagate = s.framesL[newLevel.toNat]'(by rw [hs.levelOK.len]; exact UInt32.lt_iff_toNat_lt.mp hlt) ∧
    (∀ c, t.InDB c → t.InvS c) ∧ BTRel s t newLevel := by
  intro t
  have hL := hs.levelOK
  have hlt' : newLevel.toNat < s.level.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have hfl : newLevel.toNat < s.framesL.length := by rw [hL.len]; exact hlt'
  generalize hN : s.framesL[newLevel.toNat] = N at hPle ⊢
  have hNeq : (s.frameTrailAt (UInt32.ofNat (newLevel.toNat + 1))).toNat = N := by
    rw [frameTrailAt_eq s hL _ hlt', hN]
  have hNp : N ≤ s.propagate := by rw [← hN]; exact hL.framesLe _ (List.getElem_mem _)
  have hNt : N ≤ s.asg.trail.size := by have := hL.propLe; rw [length_trailL] at this; omega
  have ht : t = btFinish newLevel N (backtrackLoop s.asg ({ s.shrinkFrames (newLevel.toNat + 1) with asg := {} })
      newLevel N N s.asg.trail.size) := by
    simp only [t]; rw [backtrack_eq s newLevel (by intro e; rw [e] at hlt; exact UInt32.lt_irrefl _ hlt), hNeq]
  have hvalid : ∀ l ∈ s.asg.trail.view, l.toNat < s.asg.values.size ∧ (NOT l).toNat < s.asg.values.size := by
    intro l hl
    have hv := hs.rsizes.valid (hs.core.trailTrue l hl)
    have := hs.core.sizes.1
    exact ⟨by have := validLit_lt hv; omega, by have := validLit_lt (validLit_not hv); omega⟩
  have hun : s.asg.unassigned.toNat + s.asg.trail.size < 2 ^ 32 := by
    have h1 := hs.rsizes.2.2.2.1
    have h2 := hs.trail_le
    have h3 := hs.ws.varsBound
    rw [length_trailL] at h2
    omega
  have hinit : BLInv s.asg newLevel N s.asg N N := by
    refine ⟨rfl, Nat.le_refl _, hNt, by simp [keptB, segB], by simp [keptB, segB], rfl, rfl, rfl, rfl,
      rfl, fun j => by simp [removedB, segB], by simp [removedB, segB]⟩
  have bl := backtrackLoop_spec s.asg newLevel N hvalid hun s.asg
    ({ s.shrinkFrames (newLevel.toNat + 1) with asg := {} }) N N hinit
  have bs := backtrackLoop_s s.asg ({ s.shrinkFrames (newLevel.toNat + 1) with asg := {} }) newLevel N N
    s.asg.trail.size
  generalize backtrackLoop s.asg ({ s.shrinkFrames (newLevel.toNat + 1) with asg := {} })
    newLevel N N s.asg.trail.size = r at bl bs ht
  obtain ⟨af, s2, q⟩ := r
  simp only at bl bs
  have tA : t.asg = { af with trail := af.trail.shrink q } := by rw [ht]; rfl
  have tL : t.level = newLevel := by rw [ht]; rfl
  have tP : t.propagate = N := by rw [ht]; rfl
  have tS : BTS t s2 := by rw [ht]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have tFr : t.frameTrail = s.frameTrail.shrink (newLevel.toNat + 1) := by
    rw [(tS.trans bs).frameTrail]; rfl
  -- the removed literals
  have btake := bl.take
  have bval := bl.values
  have bun := bl.unassigned
  have bq := bl.hq
  have bLev := bl.aLevel
  have bRea := bl.aReason
  have bBit := bl.aBits
  have bvs := bl.vsize
  generalize hR : removedB s.asg newLevel N s.asg.trail.size = R at bval bun
  generalize hK : keptB s.asg newLevel N s.asg.trail.size = K at btake bq
  have tVal : t.asg.values = af.values := by rw [tA]
  have eTr : t.trailL = s.trailL.take N ++ K := by
    unfold trailL; rw [tA]; simp only [U32Vec.view_shrink]; exact btake
  have eVal : ∀ j, t.asg.values.get! j =
      if ∃ l ∈ R, j = l.toNat ∨ j = (NOT l).toNat then 0 else s.asg.values.get! j := by
    intro j; rw [tVal]; exact bval j
  have eLev : t.asg.aLevel = s.asg.aLevel := by rw [tA]; exact bLev
  have elvl : ∀ l, t.lvl l = s.lvl l := by intro l; simp [lvl, eLev]
  have hseg : segB s.asg N s.asg.trail.size = s.trailL.drop N := by
    unfold segB trailL; apply List.take_of_length_le; simp
  have hRmem : ∀ x ∈ R, x ∈ s.trailL.drop N ∧ newLevel.toNat < s.lvl x := by
    intro x hx
    rw [← hR] at hx; unfold removedB at hx; rw [hseg] at hx
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
    refine ⟨h1, ?_⟩
    simp [keepB] at h2; unfold lvl; exact UInt32.lt_iff_toNat_lt.mp h2
  have hKmem : ∀ x ∈ K, x ∈ s.trailL.drop N ∧ s.lvl x ≤ newLevel.toNat := by
    intro x hx
    rw [← hK] at hx; unfold keptB at hx; rw [hseg] at hx
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
    refine ⟨h1, ?_⟩
    simp [keepB] at h2; unfold lvl; exact UInt32.le_iff_toNat_le.mp h2
  have hsplit : ∀ x ∈ s.trailL.drop N, x ∈ R ∨ x ∈ K := by
    intro x hx
    by_cases hk : keepB s.asg newLevel x = true
    · right; rw [← hK]; unfold keptB; rw [hseg]; exact List.mem_filter.mpr ⟨hx, hk⟩
    · left; rw [← hR]; unfold removedB; rw [hseg]; exact List.mem_filter.mpr ⟨hx, by simpa using hk⟩
  -- zeroed literals
  have hZ : ∀ l, (∃ x ∈ R, l.toNat = x.toNat ∨ l.toNat = (NOT x).toNat) → newLevel.toNat < s.lvl l := by
    rintro l ⟨x, hx, hl⟩
    have := (hRmem x hx).2
    have e : IDX l = IDX x := by
      rcases hl with hl | hl
      · rw [UInt32.toNat_inj.mp hl]
      · rw [UInt32.toNat_inj.mp hl, IDX_NOT]
    unfold lvl at *; rw [e]; exact this
  have eT : ∀ l, t.IsTrue l ↔ ¬ (∃ x ∈ R, l.toNat = x.toNat ∨ l.toNat = (NOT x).toNat) ∧ s.IsTrue l := by
    intro l; unfold IsTrue; rw [eVal]
    split
    · rename_i h; simp [h, VAL_TRUE]
    · rename_i h; simp [h]
  have eF : ∀ l, t.IsFalse l ↔ ¬ (∃ x ∈ R, l.toNat = x.toNat ∨ l.toNat = (NOT x).toNat) ∧ s.IsFalse l := by
    intro l; unfold IsFalse; rw [eVal]
    split
    · rename_i h; simp [h, VAL_FALSE]
    · rename_i h; simp [h]
  have hlow : ∀ l, s.lvl l ≤ newLevel.toNat → (t.IsTrue l ↔ s.IsTrue l) := by
    intro l hl; rw [eT]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨fun hz => by have := hZ l hz; omega, h⟩
  have hlowF : ∀ l, s.lvl l ≤ newLevel.toNat → (t.IsFalse l ↔ s.IsFalse l) := by
    intro l hl; rw [eF]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨fun hz => by have := hZ l hz; omega, h⟩
  -- frames
  have hsorted := hL.sorted
  have eFr : t.framesL = s.framesL.take newLevel.toNat := by
    unfold framesL; rw [tFr, U32Vec.view_shrink, List.drop_take, List.map_take]; simp
  have hpushLow : ∀ p, p < N → t.pushLevel p = s.pushLevel p := by
    intro p hp
    unfold pushLevel; rw [eFr]
    exact (countP_le_of_sorted s.framesL newLevel.toNat p hsorted hfl (by rw [hN]; exact hp)).symm
  have hpushHigh : ∀ p, N ≤ p → t.pushLevel p = newLevel.toNat := by
    intro p hp
    unfold pushLevel; rw [eFr]
    exact countP_take_sorted s.framesL newLevel.toNat p hsorted hfl (by rw [hN]; exact hp)
  have hpushS : ∀ p, p < N → s.pushLevel p ≤ newLevel.toNat := by
    intro p hp; rw [← hpushLow p hp]
    unfold pushLevel; rw [eFr]
    exact Nat.le_trans List.countP_le_length (by simp; omega)
  have hsplitT : s.trailL = s.trailL.take N ++ s.trailL.drop N := (List.take_append_drop _ _).symm
  have hprefix : ∀ p l, p < N → s.trailL[p]? = some l → s.lvl l ≤ newLevel.toNat := by
    intro p l hp hl
    exact Nat.le_trans (hL.pushLe p l hl) (hpushS p hp)
  have hZn : ∀ l, (∃ x ∈ R, (NOT l).toNat = x.toNat ∨ (NOT l).toNat = (NOT x).toNat) ↔
      (∃ x ∈ R, l.toNat = x.toNat ∨ l.toNat = (NOT x).toNat) := by
    intro l
    simp only [toNat_eq_iff]
    constructor
    · rintro ⟨x, hx, h | h⟩
      · exact ⟨x, hx, Or.inr (by rw [← h, NOT_NOT])⟩
      · exact ⟨x, hx, Or.inl (NOT_inj h)⟩
    · rintro ⟨x, hx, h | h⟩
      · exact ⟨x, hx, Or.inr (by rw [h])⟩
      · exact ⟨x, hx, Or.inl (by rw [h, NOT_NOT])⟩
  -- every true literal of `t` has level at most `newLevel` and is on `t`'s trail or root
  have hTlvl : ∀ l, t.IsTrue l → s.lvl l ≤ newLevel.toNat ∧ (l ∈ t.trailL ∨ s.lvl l = 0) := by
    intro l hl
    obtain ⟨hz, hs'⟩ := (eT l).mp hl
    rcases hs.core.trueOnTrail l hs' with hm | h0
    · rw [hsplitT] at hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨p, hp, hpl⟩ := mem_take_pos hm
        exact ⟨hprefix p l hp hpl, Or.inl (by rw [eTr]; exact List.mem_append_left _ hm)⟩
      · rcases hsplit l hm with hr | hk
        · exact absurd ⟨l, hr, Or.inl rfl⟩ hz
        · exact ⟨(hKmem l hk).2, Or.inl (by rw [eTr]; exact List.mem_append_right _ hk)⟩
    · exact ⟨by omega, Or.inr h0⟩
  have hvars : t.vars = s.vars := (tS.trans bs).vars
  have hcore : t.Core := by
    have hc := hs.core
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l
      rw [eT, eF, eF, hZn]
      have := hc.valCons l
      constructor
      · constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, this.1.mp h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, this.1.mpr h2⟩
      · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; exact this.2 ⟨h1, h2⟩
    · intro l hl
      rcases (hTlvl l hl).2 with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [elvl]; exact h)
    · intro l hl
      rw [eTr] at hl
      rcases List.mem_append.mp hl with hm | hm
      · obtain ⟨p, hp, hpl⟩ := mem_take_pos hm
        exact (hlow l (hprefix p l hp hpl)).mpr (hc.trailTrue l (List.mem_of_getElem? hpl))
      · have hk := hKmem l hm
        exact (hlow l hk.2).mpr (hc.trailTrue l (List.mem_of_mem_drop hk.1))
    · intro l; rw [elvl, elvl]; exact hc.lvlVar l
    · have := hc.sizes; unfold Sizes at *; rw [hvars, tVal, bvs, eLev]; exact this
    · intro j; rw [eVal]; split
      · exact Or.inl rfl
      · exact hc.domain j
  have hTN : (s.trailL.take N).length = N := by
    rw [List.length_take]; have := length_trailL s; omega
  have hlevel : t.LevelOK := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; rw [tL, elvl]; exact (hTlvl l hl).1
    · intro p l hp
      rw [eTr] at hp
      by_cases hpN : p < N
      · rw [List.getElem?_append_left (by omega)] at hp
        rw [List.getElem?_take] at hp
        simp only [hpN, ite_true] at hp
        rw [elvl, hpushLow p hpN]; exact hL.pushLe p l hp
      · rw [List.getElem?_append_right (by omega)] at hp
        have hk := hKmem l (List.mem_of_getElem? hp)
        rw [elvl, hpushHigh p (by omega)]; exact hk.2
    · rw [eFr]; exact hsorted.sublist (List.take_sublist _ _)
    · rw [eFr, tL, List.length_take]; omega
    · intro f hf; rw [eFr] at hf; rw [tP, ← hN]; exact le_of_mem_take_sorted hsorted hfl hf
    · rw [tP, eTr, List.length_append, hTN]; omega
    · rw [eFr]; exact hL.strict.sublist (List.take_sublist _ _)
    · intro f hf; rw [eFr] at hf; rw [eTr, List.length_append, hTN]
      have := lt_of_mem_take_strict hL.strict hfl hf; rw [hN] at this; omega
    · rw [tFr, U32Vec.size_shrink]; have := hL.frames0; omega
  have hbts := tS.trans bs
  have tWa : t.watches = s.watches := hbts.watches
  have tAr : t.arena = s.arena := hbts.arena
  have tDe : t.delayed = s.delayed := hbts.delayed
  have tOp : t.options = s.options := hbts.options
  have tIm : t.importLit = s.importLit := hbts.importLit
  have tIn : t.inconsistent = s.inconsistent := hbts.inconsistent
  have hW : t.WatchStruct := WatchStruct.congr tWa tAr tDe hvars hs.ws
  have eE : t.entries = s.entries := by funext l; simp [entries, watchesOf, tWa]
  have eLive : ∀ r, t.LiveRef r ↔ s.LiveRef r := by intro r; simp [LiveRef, refsL, tAr]
  have eCl : ∀ r, t.clauseL r = s.clauseL r := by intro r; simp [clauseL, tAr]
  have eB : ∀ a b, t.BinWatched a b ↔ s.BinWatched a b := by intro a b; simp [BinWatched, eE]
  have hdb : ∀ c, t.InDB c ↔ s.InDB c := inDB_congr tWa tAr
  have eRO : ∀ l, t.reasonOf l = s.reasonOf l := by
    intro l; simp [reasonOf, reasonIdx, tA, bRea]
  have eBO : ∀ l, t.binOf l = s.binOf l := by
    intro l; simp [binOf, isBinaryReason, abit, abits, tA, bBit]
  have hkeepIff : ∀ l, keepB s.asg newLevel l = true ↔ s.lvl l ≤ newLevel.toNat := by
    intro l; simp [keepB, lvl, UInt32.le_iff_toNat_le]
  have hfilt : t.trailL = s.trailL.filter (keepB s.asg newLevel) := by
    rw [eTr]
    conv => rhs; rw [hsplitT]
    rw [List.filter_append, ← hK]
    unfold keptB; rw [hseg]
    congr 1
    symm; rw [List.filter_eq_self]
    intro l hl
    obtain ⟨p, hp, hpl⟩ := mem_take_pos hl
    exact (hkeepIff l).mpr (hprefix p l hp hpl)
  have hante : ∀ l x, s.lvl l ≤ newLevel.toNat → s.Ante l x → t.Ante l x := by
    intro l x hl ⟨a1, a2, a3⟩
    refine ⟨(hlowF _ (by omega)).mpr a1, by rw [elvl, elvl]; exact a2, fun hp => ?_⟩
    rw [elvl] at hp
    have hb := a3 hp
    unfold Before at *; rw [hfilt]
    have := hb.filter (keepB s.asg newLevel)
    have hk1 : keepB s.asg newLevel (NOT x) = true := by
      rw [hkeepIff, hs.core.lvlVar]; omega
    have hk2 : keepB s.asg newLevel l = true := (hkeepIff l).mpr hl
    simpa [List.filter, hk1, hk2] using this
  have hreasons : t.ReasonOK := by
    intro l hl hlv
    obtain ⟨hz, hs'⟩ := (eT l).mp hl
    have hll := (hTlvl l hl).1
    rw [elvl] at hlv
    unfold ReasonAt
    rw [eRO, eBO]
    rcases hs.reasons l hs' hlv with e | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨b1, (eB _ _).mpr b2, hante _ _ hll b3⟩)
    · refine Or.inr (Or.inr ⟨b1, (eLive _).mpr b2, by rw [eCl]; exact b3, fun x hx hne => ?_⟩)
      rw [eCl] at hx
      exact hante _ _ hll (b4 x hx hne)
  have hroots : RootImplied Φ t := by
    intro l hl hlv
    rw [elvl] at hlv
    exact hs.roots l ((eT l).mp hl).2 hlv
  have hKsub : K.Sublist (s.trailL.drop N) := by
    rw [← hK]; unfold keptB; rw [hseg]; exact List.filter_sublist
  have hRsub : R.Sublist (s.trailL.drop N) := by
    rw [← hR]; unfold removedB; rw [hseg]; exact List.filter_sublist
  have htsub : t.trailL.Sublist s.trailL := by
    rw [eTr]; conv => rhs; rw [hsplitT]
    exact List.Sublist.append_left hKsub _
  have hrs := hs.rsizes
  have hrsizes : t.ReasonSizes := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hvars, tA]; simp only; rw [bRea]; exact hrs.1
    · rw [hvars, tA]; simp only; rw [bBit]; exact hrs.2.1
    · intro j hj; rw [hvars] at hj; rw [eVal]; split
      · rfl
      · exact hrs.2.2.1 j hj
    · -- the counter
      have hS : (R.map (fun x => (IDX x).toNat)).Nodup := by
        have h1 : (R.map IDX).Nodup :=
          (hrs.2.2.2.2.sublist (List.Sublist.map _ (hRsub.trans (List.drop_sublist _ _))))
        have := List.Pairwise.map (R := fun a b : UInt32 => a ≠ b) (S := fun a b : Nat => a ≠ b)
          UInt32.toNat (fun a b hab e => hab (UInt32.toNat_inj.mp e)) h1
        rw [List.map_map] at this
        exact this
      have hSv : ∀ v ∈ R.map (fun x => (IDX x).toNat), v < s.vars.toNat ∧
          (s.asg.values.get! (2 * v) != 0) = true := by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
        have hxt : s.IsTrue x := hs.core.trailTrue x (List.mem_of_mem_drop (hRsub.subset hx))
        refine ⟨hs.rsizes.valid hxt, ?_⟩
        rcases two_mul_idx x with e | e <;> rw [e]
        · unfold IsTrue at hxt; rw [hxt]; decide
        · have hf := (hs.core.valCons x).1.mp hxt
          unfold IsFalse at hf; rw [hf]; decide
      have hcnt := countP_remove (fun v => s.asg.values.get! (2 * v) != 0) s.vars.toNat _ hS hSv
      have hpt : ∀ v, (t.asg.values.get! (2 * v) != 0) =
          ((s.asg.values.get! (2 * v) != 0) && !((R.map (fun x => (IDX x).toNat)).contains v)) := by
        intro v
        rw [eVal]
        have hiff : (∃ l ∈ R, 2 * v = l.toNat ∨ 2 * v = (NOT l).toNat) ↔
            (R.map (fun x => (IDX x).toNat)).contains v = true := by
          simp only [List.contains_iff_mem, List.mem_map]
          constructor
          · rintro ⟨x, hx, h⟩
            refine ⟨x, hx, ?_⟩
            have h1 := IDX_toNat x
            have h2 := IDX_toNat (NOT x); rw [IDX_NOT] at h2
            rcases h with h | h <;> omega
          · rintro ⟨x, hx, rfl⟩
            exact ⟨x, hx, two_mul_idx x⟩
        by_cases hz : ∃ l ∈ R, 2 * v = l.toNat ∨ 2 * v = (NOT l).toNat
        · rw [ite_eq_left hz, hiff.mp hz]; simp
        · rw [ite_eq_right hz]
          have : (R.map (fun x => (IDX x).toNat)).contains v = false := by
            cases h : (R.map (fun x => (IDX x).toNat)).contains v
            · rfl
            · exact absurd (hiff.mpr h) hz
          rw [this]; simp
      have hun' : t.asg.unassigned.toNat = s.asg.unassigned.toNat + R.length := by
        rw [tA]; exact bun
      rw [hvars, hun', List.countP_congr (fun v _ => by rw [hpt v])]
      have := hrs.2.2.2.1
      simp only [List.length_map] at hcnt
      omega
    · exact hrs.2.2.2.2.sublist (List.Sublist.map _ htsub)
  have hsinv : SInv Φ t := ⟨hcore, hlevel, hW, by rw [tAr]; exact hs.layout, hreasons, hroots,
    hrsizes, fun c hc => hs.db c ((hdb c).mp hc), by rw [tOp]; exact hs.jump⟩
  have hPF : ∀ w k, t.PropFalseAt N w k → s.PropFalseAt P w k ∧ k ≤ newLevel.toNat := by
    intro w k hf
    obtain ⟨hfw, ⟨p, hp, hpN, hk⟩ | ⟨hn, hl0, hk⟩⟩ := hf
    · rw [eTr, List.getElem?_append_left (by omega), List.getElem?_take] at hp
      simp only [hpN, ite_true] at hp
      refine ⟨⟨(eF w).mp hfw |>.2, Or.inl ⟨p, hp, by omega, by rw [hk, hpushLow p hpN]⟩⟩, ?_⟩
      rw [hk, hpushLow p hpN]; exact hpushS p hpN
    · have hsf := ((eF w).mp hfw).2
      have hnt : s.IsTrue (NOT w) := by
        have := (hs.core.valCons (NOT w)).1; rw [NOT_NOT] at this; exact this.mpr hsf
      have hl0' : s.lvl (NOT w) = 0 := by rw [hs.core.lvlVar, ← elvl]; exact hl0
      refine ⟨⟨hsf, Or.inr ⟨?_, by rw [← elvl]; exact hl0, hk⟩⟩, by omega⟩
      intro hm
      apply hn
      rw [hsplitT] at hm
      rcases List.mem_append.mp hm with hm | hm
      · rw [eTr]; exact List.mem_append_left _ hm
      · rcases hsplit _ hm with hr | hk'
        · have := hZ (NOT w) ⟨_, hr, Or.inl rfl⟩; omega
        · rw [eTr]; exact List.mem_append_right _ hk'
  refine ⟨hsinv, tL, tP, ?_, ?_⟩
  · intro c hc w0 w1 rs heq k0 k1 h0 h1
    unfold InvS at *
    rw [tP] at h0 h1
    obtain ⟨g0, e0⟩ := hPF w0 k0 h0
    obtain ⟨g1, e1⟩ := hPF w1 k1 h1
    obtain ⟨t0, ht0, htt, hlt0⟩ := hP c ((hdb c).mp hc) w0 w1 rs heq k0 k1 g0 g1
    have hle : s.lvl t0 ≤ newLevel.toNat := by omega
    exact ⟨t0, ht0, (hlow t0 hle).mpr htt, by rw [elvl]; exact hlt0⟩
  · exact ⟨tAr, tWa, tDe, hvars, tOp, tIm, tIn, eLev, by rw [tA]; exact bRea, by rw [tA]; exact bBit,
      fun l hl => ((eT l).mp hl).2, fun l hl => ((eF l).mp hl).2, fun l hl hlv => (hlow l hlv).mpr hl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem BTRel.irrMono {s t : Solver} {n : UInt32} (h : BTRel s t n) : IrrMono s t := by
  apply IrrMono.of_large
  · intro r h1 h2
    refine ⟨by simpa [LiveRef, refsL, h.arena] using h1, by rw [h.arena]; exact h2,
      fun x hx => by simpa [clauseL, h.arena] using hx⟩
  · intro a b hab; simpa [BinWatched, entries, watchesOf, h.watches] using hab
  · intro l ⟨h1, h2⟩
    exact ⟨h.keep l h1 (by omega), by simpa [lvl, h.aLevel] using h2⟩

end Solver
end LeanKissat
