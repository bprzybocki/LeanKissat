import LeanKissat.Proofs.RedPre

/-!
# `reduce` keeps the search invariants
-/

namespace LeanKissat
namespace Solver
open Arena

/-! ### `inconsistent` is not changed by the garbage collection -/

theorem flushLoop_incons (lit : Lit) (litFixed : Value) (start : Ref) (ws : WVec) :
    ∀ (s : Solver) (out : WVec) (p : Nat),
    (flushLoop lit litFixed start ws s out p).1.inconsistent = s.inconsistent := by
  intro s out p
  induction s, out, p using flushLoop.induct lit litFixed start ws with
  | case1 s out p hp head hb other hfix ih =>
    rw [flushLoop, dite_eq_left hp]; dsimp only
    rw [ite_eq_left (show watchIsBinary ws[p] = true from hb),
      ite_eq_left (show (vTrue litFixed || vTrue (s.fixedValue (watchLit ws[p]))) = true from hfix)]
    have := ih; simp only [dite_eq_ite] at this; rw [this]
    split
    · have := congrArg Solver.inconsistent (strip_deleteBinary s lit (watchLit ws[p])); exact this
    · rfl
  | case2 s out p hp head hb other hfix ih =>
    rw [flushLoop, dite_eq_left hp]; dsimp only
    rw [ite_eq_left (show watchIsBinary ws[p] = true from hb),
      ite_eq_right (show ¬ (vTrue litFixed || vTrue (s.fixedValue (watchLit ws[p]))) = true from hfix)]
    exact ih
  | case3 s out p hp head hb tail hlt ih =>
    rw [flushLoop, dite_eq_left hp]; dsimp only
    rw [ite_eq_right (show ¬ watchIsBinary ws[p] = true from hb),
      ite_eq_left (show watchRef (ws.get! (p + 1)) < start from hlt)]
    exact ih
  | case4 s out p hp head hb tail hlt ih =>
    rw [flushLoop, dite_eq_left hp]; dsimp only
    rw [ite_eq_right (show ¬ watchIsBinary ws[p] = true from hb),
      ite_eq_right (show ¬ watchRef (ws.get! (p + 1)) < start from hlt)]
    exact ih
  | case5 s out p hp => rw [flushLoop, dite_eq_right hp]

theorem flushAll_incons (u : Solver) (start : Ref) :
    (u.flushAllWatchedClauses start).inconsistent = u.inconsistent := by
  unfold flushAllWatchedClauses
  generalize u.vars.toNat = n
  have : ∀ s i, (flushAllLoop start n s i).inconsistent = s.inconsistent := by
    intro s i
    induction s, i using flushAllLoop.induct start n with
    | case1 s i hi lit ih =>
      rw [flushAllLoop, ite_eq_left hi]; dsimp only
      rw [ih]
      unfold flushWatchedClausesByLiteral
      show (flushLoop _ _ _ _ (s.flushWatchedClausesByLiteral lit start) _ _).1.inconsistent = _
      rw [flushLoop_incons]
      unfold flushWatchedClausesByLiteral
      show (flushLoop _ _ _ _ s _ _).1.inconsistent = _
      rw [flushLoop_incons]
    | case2 s i hi => rw [flushAllLoop, ite_eq_right hi]
  exact this u 0

theorem sweepBinary_incons (s : Solver) (dst src : Ref) (L : SweepLits) :
    (s.sweepBinary dst src L).inconsistent = s.inconsistent := by
  unfold sweepBinary
  dsimp only
  repeat' split
  all_goals rfl

theorem sweepLarge_incons (s : Solver) (dst src : Ref) (n : Nat) (L : SweepLits) (st : SweepState) :
    (s.sweepLarge dst src n L st).1.inconsistent = s.inconsistent := by
  unfold sweepLarge updateLargeReasonFrom updateLargeReason
  dsimp only
  repeat' split
  all_goals rfl

theorem sweepClause_incons (s : Solver) (first : Ref) (st : SweepState) (src : Ref) :
    (s.sweepClause first st src).1.inconsistent = s.inconsistent := by
  unfold sweepClause
  split
  · rfl
  dsimp only
  rw [sweepLits_arena]
  generalize sweepLits s (litPos src 0) (s.arena.size src).toNat
    { words := (s.arena.copyWord0 st.dst src).words, qpos := litPos st.dst 0 } 0 = r
  obtain ⟨sat, L⟩ := r
  cases sat
  · have hc : ((!false) = true) = True := by simp
    simp only [hc, ite_true]; split <;> rfl
  · have hc : ((!true) = true) = False := by simp
    simp only [hc, ite_false]
    split
    · rw [sweepBinary_incons]
    · rw [sweepLarge_incons]

theorem sweepLoop_incons (first endRef : Ref) : ∀ (fuel : Nat) (s : Solver) (st : SweepState) (src : Ref),
    (s.sweepLoop first endRef st src fuel).1.inconsistent = s.inconsistent := by
  intro fuel
  induction fuel with
  | zero => intro s st src; rfl
  | succ n ih =>
    intro s st src
    unfold sweepLoop
    split
    · rfl
    · rw [ih, sweepClause_incons]

theorem sweep_incons (w : Solver) (start : Ref) :
    (w.sparseSweepGarbageClauses start).2.inconsistent = w.inconsistent := by
  unfold sparseSweepGarbageClauses
  dsimp only
  generalize hR : w.sweepLoop start (UInt32.ofNat w.arena.sizeWards) _ start w.arena.sizeWards = R
  have hi : R.1.inconsistent = w.inconsistent := by rw [← hR, sweepLoop_incons]
  obtain ⟨r1, st⟩ := R
  obtain ⟨_, _, _, _, f5⟩ := sweepFinal_fields r1 st.dst st.firstReducible st.lastIrredundant
  have h5 := Flg.inconsistent ((sfields_T f5).flg)
  dsimp only at hi ⊢
  rw [h5, hi]

theorem watchBlocking_incons (t : Solver) (a b : Lit) (r : Ref) :
    (t.watchBlocking a b r).inconsistent = t.inconsistent := rfl

theorem rewatch_incons (t : Solver) (start : Ref) : (t.rewatchClauses start).inconsistent = t.inconsistent := by
  unfold rewatchClauses
  generalize t.arena.chain start t.arena.sizeWards = L
  induction L generalizing t with
  | nil => rfl
  | cons x L ih =>
    simp only [List.foldl_cons]; rw [ih]
    rw [rewatchClause_eq, watchBlocking_incons, watchBlocking_incons]
    dsimp only [rwS]

theorem sparseCollect_incons (u : Solver) (start : Ref) :
    (u.sparseCollect false start).inconsistent = u.inconsistent := by
  unfold sparseCollect
  simp only [Bool.false_eq_true, ite_false]
  have h1 := flushAll_incons u start
  have h2 := sweep_incons (u.flushAllWatchedClauses start) start
  generalize (u.flushAllWatchedClauses start).sparseSweepGarbageClauses start = R at h2 ⊢
  obtain ⟨res, t⟩ := R
  dsimp only at h2 ⊢
  split
  · show t.inconsistent = _; rw [h2, h1]
  · rw [rewatch_incons, h2, h1]

/-! ### Flushing the trail or marking the reasons -/

/-- The large reasons at or after `start` are marked. -/
def RBP (t : Solver) (start : Ref) : Prop :=
  ∀ l, t.IsTrue l → MarkedR t start l → t.arena.reason (t.reasonOf l) = true

theorem rbp_level0 {Φ : (Nat → Bool) → Prop} {t : Solver} (h : SInv Φ t) (hl : t.level = 0) (start : Ref) :
    RBP t start := by
  intro l ht hm
  have h1 := h.levelOK.trueLe l ht; rw [hl] at h1; simp at h1; have := hm.1; omega

theorem flushAndMark_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hS : SearchInv Φ s)
    (hp : s.propagate = s.trailL.length) (start : Ref) :
    (s.flushAndMarkReasonClauses start).1 = true ∧
    ((s.flushAndMarkReasonClauses start).2.inconsistent = true → ¬ ∃ β, Φ β) ∧
    ((s.flushAndMarkReasonClauses start).2.notPorted = true ∨
      (SearchInv Φ (s.flushAndMarkReasonClauses start).2 ∧ IrrMono s (s.flushAndMarkReasonClauses start).2 ∧
       (s.flushAndMarkReasonClauses start).2.propagate = (s.flushAndMarkReasonClauses start).2.trailL.length ∧
       RBP (s.flushAndMarkReasonClauses start).2 start)) := by
  unfold flushAndMarkReasonClauses
  split
  · refine ⟨rfl, ?_⟩
    unfold backtrackPropagateAndFlushTrail
    split
    · rename_i _ hlv
      have hl0 : s.level ≠ 0 := by simpa using hlv
      unfold backtrackInConsistentState
      have h1 := updateTargetAndBestPhases_sf s
      have hS1 := h1.searchInv hS
      have hl1 : s.updateTargetAndBestPhases.level ≠ 0 := by rw [h1.same.level]; exact hl0
      obtain ⟨b1, b2, b3⟩ := backtrack0_spec hS1 hl1
      dsimp only
      generalize s.updateTargetAndBestPhases.backtrackWithoutUpdatingPhases 0 = b at b1 b2 b3 ⊢
      have hm0 : IrrMono s b := h1.irrMono.trans b2
      -- propagation (search or probing) without changing the level
      have key : IrrMono b (if b.probing then b.probingPropagate none true else b.searchPropagate).1 ∧
          ((if b.probing then b.probingPropagate none true else b.searchPropagate).2 = none →
            SearchInv Φ (if b.probing then b.probingPropagate none true else b.searchPropagate).1 ∧
            (if b.probing then b.probingPropagate none true else b.searchPropagate).1.propagate =
              (if b.probing then b.probingPropagate none true else b.searchPropagate).1.trailL.length ∧
            (if b.probing then b.probingPropagate none true else b.searchPropagate).1.level = 0) ∧
          (∀ c, (if b.probing then b.probingPropagate none true else b.searchPropagate).2 = some c →
            ((if b.probing then b.probingPropagate none true else b.searchPropagate).1.inconsistent = true →
              ¬ ∃ β, Φ β)) := by
        have hsp := searchPropagate_spec b1.inv b1.invS
        split
        · obtain ⟨m, hn, hc⟩ := probingProp_spec b1
          obtain ⟨_, e2, _, _⟩ := probingPropagate_sf b
          refine ⟨m, fun h => ⟨(hn h).1, (hn h).2, by rw [e2.same.level, hsp.level, b3]⟩,
            fun c h => (hc c h).2.1⟩
        · obtain ⟨m, hn, hc⟩ := searchProp_spec b1
          exact ⟨m, fun h => ⟨(hn h).1, (hn h).2, by rw [hsp.level, b3]⟩, fun c h => (hc c h).2.1⟩
      generalize (if b.probing then b.probingPropagate none true else b.searchPropagate) = R at key ⊢
      obtain ⟨t, res⟩ := R
      obtain ⟨k1, k2, k3⟩ := key
      dsimp only at k1 k2 k3 ⊢
      cases res with
      | none =>
        rw [ite_eq_right (by simp)]
        obtain ⟨n1, n2, n3⟩ := k2 rfl
        exact ⟨n1.incons, Or.inr ⟨n1, hm0.trans k1, n2, rbp_level0 n1.inv n3 start⟩⟩
      | some c =>
        rw [ite_eq_left (by simp)]
        exact ⟨k3 c rfl, Or.inl rfl⟩
    · rename_i _ hlv
      have hl0 : s.level = 0 := by simpa using hlv
      exact ⟨hS.incons, Or.inr ⟨hS, IrrMono.refl s, hp, rbp_level0 hS.inv hl0 start⟩⟩
  · obtain ⟨m1, m2⟩ := markReasonClauses_spec s start true hS.inv
    have hasg := m1.asg
    refine ⟨rfl, (m1.searchInv hS).incons, Or.inr ⟨m1.searchInv hS, m1.irrMono, ?_, fun l ht hm => ?_⟩⟩
    · have := congrArg Solver.propagate m1.strip
      have e : (s.markReasonClauses start true).propagate = s.propagate := this
      rw [e, hp]; simp [trailL, hasg]
    · have hT : s.IsTrue l := by unfold IsTrue at *; rw [← hasg]; exact ht
      have hM : MarkedR s start l := by
        unfold MarkedR lvl binOf reasonOf isBinaryReason abit abits reasonIdx at *; rw [← hasg]; exact hm
      have := m2 l hT hM
      have hro : (s.markReasonClauses start true).reasonOf l = s.reasonOf l := by
        unfold reasonOf reasonIdx; rw [hasg]
      rw [hro]; exact this

/-! ### The checked conditions -/

theorem reaches_split {a : Arena} {start : Ref} : ∀ (fuel : Nat) (r : Ref) (rest : List Ref),
    LayoutTo a r a.sizeWards rest → rest.length < fuel → a.reaches start r fuel = true →
    ∃ P Q, LayoutTo a r start.toNat P ∧ rest = P ++ Q ∧ LayoutTo a start a.sizeWards Q := by
  intro fuel
  induction fuel with
  | zero => intro r rest _ h; omega
  | succ n ih =>
    intro r rest hl hf hr
    unfold Arena.reaches at hr
    by_cases e : r = start
    · subst e; exact ⟨[], rest, rfl, by simp, hl⟩
    · rw [ite_eq_right (by simpa using e)] at hr
      split at hr
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases rest with
        | nil => exfalso; have : r.toNat = a.sizeWards := hl; omega
        | cons x rest' =>
          obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := hl
          obtain ⟨P, Q, h1, h2, h3⟩ := ih _ rest' hrest (by simp at hf; omega) hr
          refine ⟨x :: P, Q, ⟨rfl, ?_, hsh, hnext, h1⟩, by rw [h2]; rfl, h3⟩
          rw [UInt32.lt_iff_toNat_lt] at hc; exact hc.1
      · simp at hr

theorem unusedWatches_spec (s : Solver) : ∀ j, s.unusedWatchesEmpty j = true →
    ∀ k, j ≤ k → (h : k < s.watches.size) → s.watches[k].size = 0 := by
  intro j
  induction j using unusedWatchesEmpty.induct s with
  | case1 j hj ih =>
    intro h k hk hks
    rw [unusedWatchesEmpty, dite_eq_left hj] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    by_cases e : k = j
    · subst e; exact h.1
    · exact ih h.2 k (by omega) hks
  | case2 j hj =>
    intro _ k hk hks; omega

theorem unused_entries {Φ : (Nat → Bool) → Prop} {s : Solver} (_hs : SInv Φ s)
    (h : s.unusedWatchesEmpty (2 * s.vars.toNat) = true) :
    ∀ l, ¬ (IDX l).toNat < s.vars.toNat → s.entries l = [] := by
  intro l hl
  unfold entries watchesOf
  have hl' : 2 * s.vars.toNat ≤ l.toNat := by rw [IDX_toNat] at hl; omega
  by_cases hk : l.toNat < s.watches.size
  · rw [getElem!_pos s.watches l.toNat hk]
    have := unusedWatches_spec s _ h l.toNat hl' hk
    have e : s.watches[l.toNat].data = #[] := Array.eq_empty_of_size_eq_zero this
    rw [e]; rfl
  · rw [getElem!_neg s.watches l.toNat hk]; rfl

/-! ### The candidates keep the collection precondition -/

theorem colPre_rf {Φ : (Nat → Bool) → Prop} {x c : Solver} {start : Ref} {P Q : List Ref} (h : ColPre Φ x start P Q)
    (hrf : RF c x) (hr : ∀ y ∈ x.arena.chain 0 x.arena.sizeWards, c.arena.reason y = x.arena.reason y) :
    ColPre Φ c start P Q := by
  have hA := hrf.af
  obtain ⟨f1, _, _, _, _, f6, _, f8, f9⟩ := hrf.fields
  have hl := h.sinv.layout
  have hch := hrf.arena.chain
  have hsw : c.arena.sizeWards = x.arena.sizeWards := by simp [sizeWards, hrf.arena.wsize]
  have hss : ∀ y ∈ x.arena.chain 0 x.arena.sizeWards, x.arena.size y = c.arena.size y ∧ c.arena.shrunken y = false :=
    fun y hy => ⟨(hrf.arena.size y hy).symm, by rw [(hrf.arena.flags hy).2.2]; exact LayoutFrom.not_shrunken hl.chain y hy⟩
  have hP : ∀ y ∈ P, y ∈ x.arena.chain 0 x.arena.sizeWards := fun y hy => by
    show y ∈ x.refsL; rw [h.refs]; simp [hy]
  have hQ : ∀ y ∈ Q, y ∈ x.arena.chain 0 x.arena.sizeWards := fun y hy => by
    show y ∈ x.refsL; rw [h.refs]; simp [hy]
  refine ⟨hA.sinv h.sinv, fun d hd => ?_, by rw [f8, hA.trailL]; exact h.prop,
    h.lp.congr_ss (fun y hy => hss y (hP y hy)), by unfold refsL; rw [hch]; exact h.refs,
    by rw [hsw]; exact h.lq.congr_ss (fun y hy => hss y (hQ y hy)), fun l ht hl' hb hd hst => ?_,
    fun l hl' => by unfold entries watchesOf at *; rw [f6]; exact h.empty l (by rw [← f9]; exact hl')⟩
  · unfold InvS; rw [hA.invSAt, f8]; exact h.invS d ((hA.inDB d).mp hd)
  · rw [hA.isTrue] at ht; rw [hA.lvl] at hl'; rw [hA.binOf] at hb; rw [hA.reasonOf] at hd hst ⊢
    have := h.rb l ht hl' hb hd hst
    rw [hr _ (reason_live h.sinv.reasons ht hl' hb hd).1]; exact this

/-- The outcome required by `ReduceOK`. -/
def ROut (Φ : (Nat → Bool) → Prop) (s t : Solver) : Prop :=
  (t.inconsistent = true → ¬ ∃ β, Φ β) ∧ (Flagged t ∨ (SearchInv Φ t ∧ IrrMono s t))

theorem reduceFrom_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hS : SearchInv Φ s)
    (hp : s.propagate = s.trailL.length) (start : Ref) : ROut Φ s (s.reduceFrom false start) := by
  obtain ⟨a1, a2, a3⟩ := flushAndMark_spec hS hp start
  unfold reduceFrom
  dsimp only
  generalize s.flushAndMarkReasonClauses start = R at a1 a2 a3 ⊢
  obtain ⟨ok, x⟩ := R
  dsimp only at a1 a2 a3 ⊢
  subst a1
  rw [ite_eq_right (by simp)]
  by_cases hnp : x.notPorted = true
  · rw [ite_eq_left hnp]; exact ⟨a2, Or.inl (Or.inr (Or.inr hnp))⟩
  rw [ite_eq_right hnp]
  rcases a3 with h | ⟨hx, hmx, hpx, hrb⟩
  · exact absurd h hnp
  split
  · exact ⟨a2, Or.inl (Or.inr (Or.inr rfl))⟩
  rename_i hchk
  simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hchk
  obtain ⟨hreach, hunused⟩ := hchk
  have hlx := hx.inv.layout
  obtain ⟨P, Q, hP, hPQ, hQ⟩ := reaches_split (x.arena.sizeWards + 1) 0 _ (layoutFrom_iff.mp hlx.chain)
    (by have := LayoutFrom.length_le hlx.chain; simp at this; omega) hreach
  have hpre : ColPre Φ x start P Q :=
    ⟨hx.inv, hx.invS, hpx, hP, hPQ, hQ, fun l ht hl hb hd hst => hrb l ht ⟨hl, hb, hd, hst⟩,
      unused_entries hx.inv hunused⟩
  have hQc : x.arena.chain start x.arena.sizeWards = Q := hQ.chain_eq _ (by have := hQ.length_le; omega)
  have hQsub : ∀ y ∈ x.arena.chain start x.arena.sizeWards, y ∈ x.arena.chain 0 x.arena.sizeWards := by
    intro y hy; rw [hQc] at hy; rw [hPQ]; simp [hy]
  obtain ⟨c1, c2, c3⟩ := collectReducibles_spec x start hlx hQsub
  generalize x.collectReducibles start = C at c1 c2 c3 ⊢
  obtain ⟨ro, c⟩ := C
  dsimp only at c1 c2 c3 ⊢
  have hpc : ColPre Φ c start P Q := colPre_rf hpre c1 c2
  have hSc : SearchInv Φ c := c1.searchInv hx
  have hmc : IrrMono s c := hmx.trans c1.af.irrMono
  cases ro with
  | none =>
    dsimp only
    obtain ⟨m1, _⟩ := markReasonClauses_spec c start false hSc.inv
    have hSd := m1.searchInv hSc
    exact ⟨hSd.incons, Or.inr ⟨hSd, hmc.trans m1.irrMono⟩⟩
  | some reds =>
    dsimp only
    obtain ⟨hne, hreds⟩ := c3 reds rfl
    have hlc : c.arena.Layout := c1.arena.layout hlx
    have hcch : c.arena.chain 0 c.arena.sizeWards = x.arena.chain 0 x.arena.sizeWards := c1.arena.chain
    -- the sorted candidates are candidates (or `default`, at reference 0)
    have hall := Radix.radixSortArray64_allP (P := fun y : Reducible => y.ref ∈ Q ∨ y.ref = 0) (Or.inr rfl)
      (·.rank) reds (fun y hy => Or.inl (by rw [← hQc]; exact (hreds y hy).1))
    have hQne : start ∈ Q := by
      have h0 : 0 < reds.size := Nat.pos_of_ne_zero hne
      have hm := (hreds reds[0] (Array.getElem_mem h0)).1
      rw [hQc] at hm
      cases Q with
      | nil => simp at hm
      | cons q Q' => obtain ⟨rfl, _⟩ := hQ; simp
    have hsorted : ∀ i : Nat, start ≤ ((Radix.radixSortArray64 (·.rank) reds)[i]!).ref →
        ((Radix.radixSortArray64 (·.rank) reds)[i]!).ref ∈ c.arena.chain 0 c.arena.sizeWards := by
      intro i hi
      rw [hcch, hPQ]
      rcases hall i with h | h
      · simp [h]
      · have : start = 0 := by rw [h] at hi; exact UInt32.le_zero_iff.mp hi
        rw [h, ← this]; simp [hQne]
    unfold markLessUsefulClausesAsGarbage
    dsimp only
    generalize (min _ _ : Nat) = n
    obtain ⟨g1, g2⟩ := markGarbageLoop_spec start _ n c hlc hsorted c 0 rfl (GSame.refl _ _)
    generalize markGarbageLoop start (Radix.radixSortArray64 (·.rank) reds) n c 0 = v at g1 g2 ⊢
    obtain ⟨hpv, hmv, hbv, hclv, hflv⟩ := gsame_colPre hpc g1 g2
    have hincv : v.inconsistent = c.inconsistent := Flg.inconsistent hflv
    have hinc : (v.sparseCollect false start).inconsistent = true → ¬ ∃ β, Φ β := by
      rw [sparseCollect_incons, hincv]; exact hSc.incons
    rcases sparseCollect_spec hpv with hf | ⟨N, hC⟩
    · exact ⟨hinc, Or.inl (Or.inr (Or.inr hf))⟩
    · obtain ⟨f1, f2, f3⟩ := hC.final hpv
      refine ⟨hinc, Or.inr ⟨⟨f1, f2, fun i b hb => ?_, ?_, hinc, ?_, ?_, ?_⟩, hmc.trans (hmv.trans f3)⟩⟩
      · rw [hC.bits i b hb, hbv i b hb]; exact hSc.clean i b hb
      · rw [hC.clause, hclv]; exact hSc.clauseEmpty
      · rw [Flg.watching hC.flg, Flg.watching hflv]; exact hSc.watching
      · rw [Flg.options hC.flg, Flg.options hflv]; exact hSc.opts
      · exact (hSc.imp.flg hflv).flg hC.flg

/-! ### `kissat_reduce` -/

/-- A search frame that also keeps the stop flags. -/
structure SFF (t s : Solver) : Prop where
  sf : SFr t s
  fl : Flagged s → Flagged t

theorem ROut.sff {Φ : (Nat → Bool) → Prop} {s0 t u : Solver} (h : ROut Φ s0 t) (hf : SFF u t) : ROut Φ s0 u := by
  refine ⟨fun e => h.1 (by rw [← Flg.inconsistent hf.sf.flg]; exact e), ?_⟩
  rcases h.2 with hfl | ⟨hS, hm⟩
  · exact Or.inl (hf.fl hfl)
  · exact Or.inr ⟨hf.sf.searchInv hS, hm.trans hf.sf.irrMono⟩

theorem flagged_of_eq {s t : Solver} (h1 : t.notPorted = s.notPorted) (h2 : t.overflowed = s.overflowed)
    (h3 : t.outOfResources = s.outOfResources) : Flagged s → Flagged t := by
  unfold Flagged; rw [h1, h2, h3]; exact id

theorem classify_sff (s : Solver) : SFF s.classify s := by
  refine ⟨classify_sf s, flagged_of_eq ?_ ?_ ?_⟩ <;> (unfold classify; dsimp only; split <;> rfl)

theorem conflictsPlus_flags (s : Solver) (d : UInt64) : Flagged s → Flagged (s.conflictsPlus d).2 := by
  unfold conflictsPlus; dsimp only; split
  · intro _; exact Or.inl rfl
  · exact id

theorem updateReduceLimit_sff (s : Solver) : SFF s.updateReduceLimit s := by
  unfold updateReduceLimit
  dsimp only
  have h1 := conflictsPlus_sf s
    (s.updateConflictLimitDelta s.options.reduceint s.stats.reductions kSqrt false (UInt64.ofNat s.options.reduceint))
  have h2 := conflictsPlus_flags s
    (s.updateConflictLimitDelta s.options.reduceint s.stats.reductions kSqrt false (UInt64.ofNat s.options.reduceint))
  generalize s.conflictsPlus (s.updateConflictLimitDelta s.options.reduceint s.stats.reductions kSqrt false
    (UInt64.ofNat s.options.reduceint)) = R at h1 h2 ⊢
  obtain ⟨lim, t⟩ := R
  dsimp only at h1 h2 ⊢
  have h3 : SFr { t with limits := { t.limits with reduceConflicts := lim } } t := by sf_rfl
  exact ⟨h3.trans h1, fun hf => (h2 hf)⟩

theorem reduce_prefix_sff (s : Solver) : SFF (INC! s reductions).computeAndSetTierLimits s := by
  refine ⟨by unfold computeAndSetTierLimits; sf_rfl, id⟩

theorem last_sff (s : Solver) : SFF { s with last := { s.last with conflictsReduce := s.stats.conflicts } } s :=
  ⟨by sf_rfl, id⟩

theorem compacting_false (s : Solver) (h : s.options.compact = 0) : s.compacting = false := by
  unfold compacting; simp [h]

/-- `reduce` keeps the search invariants (for the `--plain` options). -/
theorem reduce_ok (Φ : (Nat → Bool) → Prop) : ReduceOK Φ Solver.reduce := by
  intro s hS hp _
  unfold Solver.reduce
  dsimp only
  have h1 := reduce_prefix_sff s
  generalize (INC! s reductions).computeAndSetTierLimits = s1 at h1 ⊢
  have hS1 := h1.sf.searchInv hS
  have hp1 : s1.propagate = s1.trailL.length := by
    rw [h1.sf.same.propagate, hp]; simp [trailL, h1.sf.same.asg]
  rw [compacting_false s1 hS1.opts.compact]
  simp only [Bool.false_eq_true, ite_false]
  have h2 : ROut Φ s (if s1.firstReducible != INVALID_REF then s1.reduceFrom false s1.firstReducible else s1) := by
    have hm1 := h1.sf.irrMono
    split
    · have := reduceFrom_spec hS1 hp1 s1.firstReducible
      exact ⟨this.1, this.2.elim Or.inl (fun ⟨a, b⟩ => Or.inr ⟨a, hm1.trans b⟩)⟩
    · exact ⟨hS1.incons, Or.inr ⟨hS1, hm1⟩⟩
  generalize (if s1.firstReducible != INVALID_REF then s1.reduceFrom false s1.firstReducible else s1) = s2 at h2 ⊢
  have h3 := h2.sff (classify_sff s2)
  generalize s2.classify = s3 at h3 ⊢
  have h4 : ROut Φ s (if !s3.inconsistent then s3.updateReduceLimit else s3) := by
    split
    · exact h3.sff (updateReduceLimit_sff s3)
    · exact h3
  generalize (if !s3.inconsistent then s3.updateReduceLimit else s3) = s4 at h4 ⊢
  have h5 := h4.sff (last_sff s4)
  refine ⟨fun e => h5.1 ?_, by split <;> simp, fun _ => h5.2⟩
  show s4.inconsistent = true
  by_cases hi : s4.inconsistent = true
  · exact hi
  · rw [ite_eq_right hi] at e; simp at e

end Solver
end LeanKissat
