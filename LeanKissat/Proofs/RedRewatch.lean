import LeanKissat.Proofs.RedSweep
import LeanKissat.Proofs.RedSort

/-!
# `reduce`: rewatching the swept clauses (`rewatch_clauses`)
-/

namespace LeanKissat
namespace Solver
open Arena

/-- The words after sorting the literals of the clause at `ref`. -/
def rwWords (s : Solver) (ref : Ref) : U32Vec :=
  sortLiterals s.asg.values (fun idx => s.asg.aLevel.get! idx.toNat) s.arena.words (litPos ref 0)
    (s.arena.size ref).toNat

/-- The arena after rewatching the clause at `ref`. -/
def rwArena (s : Solver) (ref : Ref) : Arena := ({ words := s.rwWords ref } : Arena).setSearched ref 2

/-- The solver with the arena of the rewatched clause (before adding its watches). -/
def rwS (s : Solver) (ref : Ref) : Solver := { s with arena := s.rwArena ref }

theorem rewatchClause_eq (s : Solver) (ref : Ref) :
    s.rewatchClause ref = ((s.rwS ref).watchBlocking ((s.rwArena ref).lit ref 0)
      ((s.rwArena ref).lit ref 1) ref).watchBlocking ((s.rwArena ref).lit ref 1) ((s.rwArena ref).lit ref 0) ref := rfl

/-- The arena effect of rewatching one clause. -/
theorem rwArena_spec (s : Solver) (ref : Ref) (h2 : 2 ≤ (s.arena.size ref).toNat)
    (hin : litPos ref 0 + (s.arena.size ref).toNat ≤ s.arena.words.size) :
    (s.rwArena ref).words.size = s.arena.words.size ∧
    (∀ j, j ≠ 4 * ref.toNat + 1 → (j < litPos ref 0 ∨ litPos ref 0 + (s.arena.size ref).toNat ≤ j) →
      (s.rwArena ref).words.get! j = s.arena.words.get! j) ∧
    (s.rwArena ref).word0 ref = s.arena.word0 ref ∧ (s.rwArena ref).size ref = s.arena.size ref ∧
    (s.rwArena ref).searched ref = 2 ∧
    ((s.rwArena ref).litsL ref).Perm (s.arena.litsL ref) ∧
    ((∃ x ∈ s.arena.litsL ref, vNeg (s.asg.values.get! x.toNat) = false) →
      vNeg (s.asg.values.get! ((s.rwArena ref).lit ref 0).toNat) = false) := by
  obtain ⟨a1, a2, a3, a4⟩ := sortLiterals_spec s.asg.values (fun idx => s.asg.aLevel.get! idx.toNat) s.arena.words
    (litPos ref 0) (s.arena.size ref).toNat h2 hin
  change (s.rwWords ref).size = _ at a1
  change ∀ j, _ → (s.rwWords ref).get! j = _ at a2
  change (seg (s.rwWords ref) _ _).Perm _ at a3
  change _ → vNeg (s.asg.values.get! ((s.rwWords ref).get! _).toNat) = false at a4
  have hb : 4 * ref.toNat + 1 < s.arena.words.size := by unfold litPos base at hin; omega
  have hget : ∀ j, (s.rwArena ref).words.get! j = if 4 * ref.toNat + 1 = j then 2 else
      (s.rwWords ref).get! j := by
    intro j
    show ((s.rwWords ref).set! (4 * ref.toNat + 1) 2).get! j = _
    rw [U32Vec.get!_set!]
    by_cases e : 4 * ref.toNat + 1 = j
    · rw [ite_eq_left ⟨e, by rw [a1, ← e]; exact hb⟩, ite_eq_left e]
    · rw [ite_eq_right (fun h => e h.1), ite_eq_right e]
  have hsz : (s.rwArena ref).words.size = s.arena.words.size := by
    show ((s.rwWords ref).set! (4 * ref.toNat + 1) 2).size = _
    rw [U32Vec.size_set!, a1]
  have hsame : ∀ j, j ≠ 4 * ref.toNat + 1 → (j < litPos ref 0 ∨ litPos ref 0 + (s.arena.size ref).toNat ≤ j) →
      (s.rwArena ref).words.get! j = s.arena.words.get! j := by
    intro j h1 h3; rw [hget, ite_eq_right (Ne.symm h1), a2 j h3]
  have hw0 : (s.rwArena ref).word0 ref = s.arena.word0 ref := by
    unfold word0 base; exact hsame _ (by omega) (Or.inl (by unfold litPos base; omega))
  have hs2 : (s.rwArena ref).size ref = s.arena.size ref := by
    unfold Arena.size base; exact hsame _ (by omega) (Or.inl (by unfold litPos base; omega))
  have hlit : ∀ k, k < (s.arena.size ref).toNat → (s.rwArena ref).lit ref k =
      (s.rwWords ref).get! (litPos ref 0 + k) := by
    intro k _; unfold Arena.lit; rw [hget, ite_eq_right (by unfold litPos base; omega)]; rfl
  have hseg : (s.rwArena ref).litsL ref = seg (s.rwWords ref) (litPos ref 0) (s.arena.size ref).toNat := by
    unfold litsL seg; rw [hs2]
    apply List.map_congr_left; intro k hk; simp at hk; exact hlit k hk
  have hseg0 : s.arena.litsL ref = seg s.arena.words (litPos ref 0) (s.arena.size ref).toNat := by
    unfold litsL seg; rfl
  refine ⟨hsz, hsame, hw0, hs2, by unfold searched base; rw [hget, ite_eq_left rfl], ?_, ?_⟩
  · rw [hseg, hseg0]; exact a3
  · intro ⟨x, hx, hxv⟩
    rw [hlit 0 (by omega), Nat.add_zero]
    apply a4
    rw [hseg0] at hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact ⟨k, List.mem_range.mp hk, hxv⟩

/-- The solver without arena and watch lists. -/
def stripRW (s : Solver) : Solver := { s with arena := default, watches := #[] }

/-- Invariant of `rewatch_clauses` (`Dn` done, `M` to do). -/
structure RWI (t : Solver) (start : Ref) (s : Solver) (Dn M : List Ref) : Prop where
  wsize : s.arena.words.size = t.arena.words.size
  pre : EqOn s.arena t.arena 0 (4 * start.toNat)
  todo : ∀ n ∈ M, EqOn s.arena t.arena (4 * n.toNat) (4 * n.toNat + 4 * wardsOfClause (t.arena.size n).toNat)
  done : ∀ n ∈ Dn, s.arena.word0 n = t.arena.word0 n ∧ s.arena.size n = t.arena.size n ∧
    s.arena.searched n = 2 ∧ (s.arena.litsL n).Perm (t.arena.litsL n) ∧
    ((∃ x ∈ t.arena.litsL n, vNeg (t.asg.values.get! x.toNat) = false) →
      vNeg (t.asg.values.get! (s.arena.lit n 0).toNat) = false)
  ent : ∀ l, ∃ E, s.entries l = t.entries l ++ E ∧
    (∀ e ∈ E, ∃ n ∈ Dn, (e = .large (s.arena.lit n 1) n ∧ l = s.arena.lit n 0) ∨
      (e = .large (s.arena.lit n 0) n ∧ l = s.arena.lit n 1)) ∧
    (∀ r, countRef r E = if r ∈ Dn then (if l = s.arena.lit r 0 then 1 else 0) + (if l = s.arena.lit r 1 then 1 else 0)
      else 0)
  words : ∀ l, WordsOK (s.watchesOf l).data.toList
  wsz : s.watches.size = t.watches.size
  frame : stripRW s = stripRW t

theorem countRef_single (r r' : Ref) (b : Lit) : countRef r [.large b r'] = if r' = r then 1 else 0 := by
  simp [countRef]

theorem watchBlocking_entries (s : Solver) (x b : Lit) (r : Ref) (hx : x.toNat < s.watches.size)
    (hb : b.toNat < 2 ^ 31) (hr : r.toNat < 2 ^ 31) (hW : ∀ l, WordsOK (s.watchesOf l).data.toList) :
    (∀ l, WordsOK ((s.watchBlocking x b r).watchesOf l).data.toList) ∧
    (∀ l, (s.watchBlocking x b r).entries l = s.entries l ++ (if l = x then [WEntry.large b r] else [])) ∧
    (s.watchBlocking x b r).watches.size = s.watches.size := by
  have h1 := (watchBlocking_adds s x b r hx).entries hW (show WEntry.WF (.large b r) from ⟨hb, hr⟩)
  refine ⟨fun l => (h1 l).2, fun l => ?_, modifyWatches_size _ _ _⟩
  rw [(h1 l).1]; split <;> simp

theorem lit_mem_litsL' (a : Arena) (r : Ref) (k : Nat) (hk : k < (a.size r).toNat) : a.lit r k ∈ a.litsL r := by
  unfold litsL; exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem watchBlocking_fields (t : Solver) (a b : Lit) (r : Ref) : (t.watchBlocking a b r).arena = t.arena ∧
    (t.watchBlocking a b r).asg = t.asg ∧ stripRW (t.watchBlocking a b r) = stripRW t := ⟨rfl, rfl, rfl⟩

theorem rwS_fields (s : Solver) (ref : Ref) : (s.rwS ref).arena = s.rwArena ref ∧ (s.rwS ref).asg = s.asg ∧
    stripRW (s.rwS ref) = stripRW s := by
  refine ⟨by dsimp only [rwS], by dsimp only [rwS], ?_⟩
  unfold stripRW rwS; rfl

theorem rw_step {t : Solver} {start : Ref} {s : Solver} {Dn M : List Ref} {ref : Ref}
    (hN : LayoutTo t.arena start t.arena.sizeWards (Dn ++ ref :: M))
    (hval : ∀ n ∈ Dn ++ ref :: M, ∀ x ∈ t.arena.litsL n, x.toNat < t.watches.size ∧ x.toNat < 2 ^ 31)
    (h2 : ∀ n ∈ Dn ++ ref :: M, 2 ≤ (t.arena.size n).toNat) (hlay : t.arena.Layout)
    (hI : RWI t start s Dn (ref :: M)) : RWI t start (s.rewatchClause ref) (Dn ++ [ref]) M := by
  have hasg : s.asg = t.asg := by have := congrArg Solver.asg hI.frame; exact this
  have href : ref ∈ Dn ++ ref :: M := by simp
  obtain ⟨b1, b2, b3⟩ := hN.mem_bounds ref href
  have hm4 := hlay.mult4
  have hbd := hlay.bound
  have hwf := wardsOfClause_fits (t.arena.size ref).toNat
  have hreg := hI.todo ref (by simp)
  obtain ⟨e0, e1, e2, e3⟩ := clause_eq_of_eqOn hreg.symm
  replace e0 := e0.symm; replace e1 := e1.symm; replace e2 := e2.symm; replace e3 := e3.symm
  have h2r : 2 ≤ (s.arena.size ref).toNat := by rw [e2]; exact h2 ref href
  have hin : litPos ref 0 + (s.arena.size ref).toNat ≤ s.arena.words.size := by
    rw [e2, hI.wsize]; unfold litPos base; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := rwArena_spec s ref h2r hin
  -- positions outside the clause at `ref` are unchanged
  have hout : ∀ j, (j < 4 * ref.toNat ∨ 4 * ref.toNat + 4 * wardsOfClause (t.arena.size ref).toNat ≤ j) →
      (s.rwArena ref).words.get! j = s.arena.words.get! j := by
    intro j hj
    apply r2 j (by omega)
    rw [e2]; unfold litPos base; omega
  have hnd := hN.nodup
  have hrefD : ref ∉ Dn := by
    intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 ref h ref (by simp) rfl
  have hdisj : ∀ n ∈ Dn ++ ref :: M, n ≠ ref →
      EqOn (s.rwArena ref) s.arena (4 * n.toNat) (4 * n.toNat + 4 * wardsOfClause (t.arena.size n).toNat) := by
    intro n hn hne j h1 h3
    apply hout j
    rcases hN.disjoint n hn ref href hne with h | h <;> omega
  -- the literals of the rewatched clause are valid
  have hl0 : (s.rwArena ref).lit ref 0 ∈ t.arena.litsL ref := by
    have := lit_mem_litsL' (s.rwArena ref) ref 0 (by rw [r4]; omega)
    rw [← e3]; exact r6.subset this
  have hl1 : (s.rwArena ref).lit ref 1 ∈ t.arena.litsL ref := by
    have := lit_mem_litsL' (s.rwArena ref) ref 1 (by rw [r4]; omega)
    rw [← e3]; exact r6.subset this
  obtain ⟨v0, v0'⟩ := hval ref href _ hl0
  obtain ⟨v1, v1'⟩ := hval ref href _ hl1
  have hr31 : ref.toNat < 2 ^ 31 := by omega
  have hrwW : (s.rwS ref).watches = s.watches := by dsimp only [rwS]
  have hW0 : ∀ l, WordsOK ((s.rwS ref).watchesOf l).data.toList := by
    intro l; unfold watchesOf; rw [hrwW]; exact hI.words l
  have hx0 : ((s.rwArena ref).lit ref 0).toNat < (s.rwS ref).watches.size := by rw [hrwW, hI.wsz]; exact v0
  obtain ⟨w1, w2, w3⟩ := watchBlocking_entries (s.rwS ref) ((s.rwArena ref).lit ref 0) ((s.rwArena ref).lit ref 1) ref
    hx0 v1' hr31 hW0
  generalize hS1 : (s.rwS ref).watchBlocking ((s.rwArena ref).lit ref 0) ((s.rwArena ref).lit ref 1) ref = s1
    at w1 w2 w3
  have hx1 : ((s.rwArena ref).lit ref 1).toNat < s1.watches.size := by rw [w3, hrwW, hI.wsz]; exact v1
  obtain ⟨w4, w5, w6⟩ := watchBlocking_entries s1 ((s.rwArena ref).lit ref 1) ((s.rwArena ref).lit ref 0) ref
    hx1 v0' hr31 w1
  obtain ⟨g1, g2, g3⟩ := rwS_fields s ref
  obtain ⟨k1, k2, k3⟩ := watchBlocking_fields (s.rwS ref) ((s.rwArena ref).lit ref 0) ((s.rwArena ref).lit ref 1) ref
  rw [hS1] at k1 k2 k3
  rw [rewatchClause_eq, hS1]
  obtain ⟨j1, j2, j3⟩ := watchBlocking_fields s1 ((s.rwArena ref).lit ref 1) ((s.rwArena ref).lit ref 0) ref
  generalize s1.watchBlocking ((s.rwArena ref).lit ref 1) ((s.rwArena ref).lit ref 0) ref = s' at w4 w5 w6 j1 j2 j3 ⊢
  have sA : s'.arena = s.rwArena ref := by rw [j1, k1, g1]
  have sW : ∀ l, s'.entries l = s.entries l ++
      (if l = (s.rwArena ref).lit ref 0 then [WEntry.large ((s.rwArena ref).lit ref 1) ref] else []) ++
      (if l = (s.rwArena ref).lit ref 1 then [WEntry.large ((s.rwArena ref).lit ref 0) ref] else []) := by
    intro l; rw [w5, w2]
    have : (s.rwS ref).entries l = s.entries l := by unfold entries watchesOf; rw [hrwW]
    rw [this]
  -- the other clauses keep their literals
  have hlitD : ∀ n ∈ Dn, (s.rwArena ref).litsL n = s.arena.litsL n ∧ (s.rwArena ref).word0 n = s.arena.word0 n ∧
      (s.rwArena ref).size n = s.arena.size n ∧ (s.rwArena ref).searched n = s.arena.searched n ∧
      (s.rwArena ref).lit n 0 = s.arena.lit n 0 ∧ (s.rwArena ref).lit n 1 = s.arena.lit n 1 := by
    intro n hn
    have hne : n ≠ ref := fun e => hrefD (e ▸ hn)
    have hD := hdisj n (by simp [hn]) hne
    obtain ⟨_, hs, _⟩ := hI.done n hn
    have hsN := congrArg UInt32.toNat hs
    rw [← hs] at hD
    obtain ⟨a0, a1, a2, a3⟩ := clause_eq_of_eqOn hD.symm
    refine ⟨a3.symm, a0.symm, a2.symm, a1.symm, ?_, ?_⟩
    · unfold Arena.lit Arena.litPos Arena.base
      exact hD _ (by omega) (by have := h2 n (by simp [hn]); have := wardsOfClause_fits (s.arena.size n).toNat; omega)
    · unfold Arena.lit Arena.litPos Arena.base
      exact hD _ (by omega) (by have := h2 n (by simp [hn]); have := wardsOfClause_fits (s.arena.size n).toNat; omega)
  have hsasg : s.asg.values = t.asg.values := by rw [hasg]
  refine ⟨by rw [sA, r1, hI.wsize], ?_, ?_, ?_, ?_, w4, by rw [w6, w3, hrwW, hI.wsz], by rw [j3, k3, g3, hI.frame]⟩
  · intro j h1 h3
    rw [sA, hout j (Or.inl (by omega))]
    exact hI.pre j h1 h3
  · intro n hn j h1 h3
    have hne : n ≠ ref := by
      intro e; subst e; rw [List.nodup_append] at hnd
      have := hnd.2.1; simp at this; exact this.1 hn
    rw [sA, hdisj n (by simp [hn]) hne j h1 h3]
    exact hI.todo n (by simp [hn]) j h1 h3
  · intro n hn
    rw [sA]
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hlitD n hn
      obtain ⟨o1, o2, o3, o4, o5⟩ := hI.done n hn
      exact ⟨d2.trans o1, d3.trans o2, d4.trans o3, by rw [d1]; exact o4, fun h => by rw [d5]; exact o5 h⟩
    · simp at hn; subst hn
      refine ⟨r3.trans e0, r4.trans e2, r5, by rw [← e3]; exact r6, fun h => ?_⟩
      have := r7 (by rw [e3]; obtain ⟨x, hx, hxv⟩ := h; exact ⟨x, hx, by rw [hsasg]; exact hxv⟩)
      rw [hsasg] at this; exact this
  · intro l
    obtain ⟨E, hE, hmem, hcnt⟩ := hI.ent l
    refine ⟨E ++ (if l = (s.rwArena ref).lit ref 0 then [WEntry.large ((s.rwArena ref).lit ref 1) ref] else []) ++
      (if l = (s.rwArena ref).lit ref 1 then [WEntry.large ((s.rwArena ref).lit ref 0) ref] else []), ?_, ?_, ?_⟩
    · rw [sW, hE]; simp
    · intro e he
      simp only [List.mem_append] at he
      rcases he with (he | he) | he
      · obtain ⟨n, hn, hc⟩ := hmem e he
        obtain ⟨_, _, _, _, d5, d6⟩ := hlitD n hn
        refine ⟨n, by simp [hn], ?_⟩
        rw [sA, d5, d6]; exact hc
      · split at he
        · rename_i hl; simp at he; subst he
          exact ⟨ref, by simp, Or.inl ⟨by rw [sA], by rw [sA]; exact hl⟩⟩
        · simp at he
      · split at he
        · rename_i hl; simp at he; subst he
          exact ⟨ref, by simp, Or.inr ⟨by rw [sA], by rw [sA]; exact hl⟩⟩
        · simp at he
    · intro r
      rw [countRef_append, countRef_append, hcnt r]
      have c0 : countRef r (if l = (s.rwArena ref).lit ref 0 then [WEntry.large ((s.rwArena ref).lit ref 1) ref] else [])
          = if r = ref ∧ l = (s.rwArena ref).lit ref 0 then 1 else 0 := by
        by_cases hl : l = (s.rwArena ref).lit ref 0
        · rw [ite_eq_left hl, countRef_single]
          by_cases hr : r = ref
          · rw [ite_eq_left hr.symm, ite_eq_left ⟨hr, hl⟩]
          · rw [ite_eq_right (Ne.symm hr), ite_eq_right (fun h => hr h.1)]
        · rw [ite_eq_right hl, ite_eq_right (fun h => hl h.2)]; rfl
      have c1 : countRef r (if l = (s.rwArena ref).lit ref 1 then [WEntry.large ((s.rwArena ref).lit ref 0) ref] else [])
          = if r = ref ∧ l = (s.rwArena ref).lit ref 1 then 1 else 0 := by
        by_cases hl : l = (s.rwArena ref).lit ref 1
        · rw [ite_eq_left hl, countRef_single]
          by_cases hr : r = ref
          · rw [ite_eq_left hr.symm, ite_eq_left ⟨hr, hl⟩]
          · rw [ite_eq_right (Ne.symm hr), ite_eq_right (fun h => hr h.1)]
        · rw [ite_eq_right hl, ite_eq_right (fun h => hl h.2)]; rfl
      rw [c0, c1, sA]
      by_cases hrD : r ∈ Dn
      · have hne : r ≠ ref := fun e => hrefD (e ▸ hrD)
        obtain ⟨_, _, _, _, d5, d6⟩ := hlitD r hrD
        have hm : r ∈ Dn ++ [ref] := by simp [hrD]
        simp only [hrD, hm, ite_true, hne, false_and, ite_false, Nat.add_zero, d5, d6]
      · by_cases hr : r = ref
        · subst hr
          have hm : r ∈ Dn ++ [r] := by simp
          simp only [hrD, hm, ite_true, ite_false, true_and, Nat.zero_add]
        · have hm : r ∉ Dn ++ [ref] := by simp [hrD, hr]
          simp only [hrD, hm, hr, ite_false, false_and, Nat.add_zero]

theorem rw_fold {t : Solver} {start : Ref} {N : List Ref}
    (hN : LayoutTo t.arena start t.arena.sizeWards N)
    (hval : ∀ n ∈ N, ∀ x ∈ t.arena.litsL n, x.toNat < t.watches.size ∧ x.toNat < 2 ^ 31)
    (h2 : ∀ n ∈ N, 2 ≤ (t.arena.size n).toNat) (hlay : t.arena.Layout) :
    ∀ (M Dn : List Ref) (s : Solver), Dn ++ M = N → RWI t start s Dn M → RWI t start (M.foldl rewatchClause s) N [] := by
  intro M
  induction M with
  | nil => intro Dn s e h; simp at e; subst e; exact h
  | cons ref M ih =>
    intro Dn s e h
    subst e
    have := rw_step hN hval h2 hlay h
    simp only [List.foldl_cons]
    exact ih (Dn ++ [ref]) _ (by simp) this

theorem rewatch_spec {t : Solver} {start : Ref} {N : List Ref}
    (hN : LayoutTo t.arena start t.arena.sizeWards N)
    (hval : ∀ n ∈ N, ∀ x ∈ t.arena.litsL n, x.toNat < t.watches.size ∧ x.toNat < 2 ^ 31)
    (h2 : ∀ n ∈ N, 2 ≤ (t.arena.size n).toNat) (hlay : t.arena.Layout)
    (hW : ∀ l, WordsOK (t.watchesOf l).data.toList) :
    RWI t start (t.rewatchClauses start) N [] := by
  unfold rewatchClauses
  rw [hN.chain_eq _ (by have := hN.length_le; omega)]
  exact rw_fold hN hval h2 hlay N [] t rfl ⟨rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun n hn => by simp at hn,
    fun l => ⟨[], by simp, fun e he => by simp at he, fun r => by simp [countRef]⟩, hW, rfl, rfl⟩

end Solver
end LeanKissat
