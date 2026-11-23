import LeanKissat.Proofs.RedSweepLits

/-!
# `reduce`: the clause loop of the sparse sweep (`sparse_sweep_garbage_clauses`)

All statements are relative to the state `w` at the start of the sweep; `A = w.arena`,
`Q` is the old chain from `start`.
-/

namespace LeanKissat
namespace Solver
open Arena

/-- Literals of the clause at `o` that are not false at the root level. -/
def filt (w : Solver) (o : Ref) : List Lit := (w.clauseL o).filter (fun x => !w.rootF x)

/-- The clause at `o` is satisfied at the root level. -/
def SatW (w : Solver) (o : Ref) : Prop := ∃ x ∈ w.clauseL o, w.rootT x = true

/-- Facts about the state at the start of the sweep. -/
structure SwPre (w : Solver) (start : Ref) (Q : List Ref) : Prop where
  lay : w.arena.Layout
  lq : LayoutTo w.arena start w.arena.sizeWards Q
  live : ∀ r ∈ Q, w.arena.garbage r = false → (∀ x ∈ w.clauseL r, w.ValidLit x) ∧ (w.clauseL r).Nodup
  reasons : w.ReasonOK
  rb : ∀ l, w.IsTrue l → 0 < w.lvl l → w.binOf l = false → w.reasonOf l ≠ DECISION_REASON →
    start ≤ w.reasonOf l → w.arena.reason (w.reasonOf l) = true
  core : w.Core
  words : ∀ l, WordsOK (w.watchesOf l).data.toList
  watchesSize : 2 * w.vars.toNat ≤ w.watches.size
  varsBound : w.vars.toNat < 2 ^ 30
  rsize : w.vars.toNat ≤ w.asg.aReason.size ∧ w.vars.toNat ≤ w.asg.aBits.size
  pre : ∃ P, LayoutTo w.arena 0 start.toNat P ∧ w.refsL = P ++ Q

/-- Status of the reason of a true literal `l` during the sweep. -/
def RS (w : Solver) (start : Ref) (s : Solver) (rest N : List Ref) (l : Lit) : Prop :=
  if w.binOf l = false ∧ w.reasonOf l ≠ DECISION_REASON ∧ start ≤ w.reasonOf l then
    (w.reasonOf l ∈ rest ∧ s.reasonOf l = w.reasonOf l ∧ s.binOf l = false) ∨
    (s.binOf l = false ∧ ∃ n ∈ N, s.reasonOf l = n ∧ s.arena.litsL n = filt w (w.reasonOf l)) ∨
    (s.binOf l = true ∧ s.BinWatched l (s.reasonOf l) ∧ s.reasonOf l ∈ w.clauseL (w.reasonOf l) ∧
      s.reasonOf l ≠ l)
  else s.reasonOf l = w.reasonOf l ∧ s.binOf l = w.binOf l

/-- The solver without the fields changed by the sweep loop. -/
def stripS (s : Solver) : Solver :=
  { s with arena := default, asg := default, watches := #[], stats := default, notPorted := false }

/-- The invariant of the clause loop of the sweep. -/
structure SwI (w : Solver) (start : Ref) (Q : List Ref) (s : Solver) (st : SweepState) (src : Ref)
    (rest D N : List Ref) : Prop where
  qsplit : Q = D ++ rest
  lrest : LayoutTo w.arena src w.arena.sizeWards rest
  wsize : s.arena.words.size = w.arena.words.size
  untouched : EqOn s.arena w.arena (4 * src.toNat) w.arena.words.size
  pre : EqOn s.arena w.arena 0 (4 * start.toNat)
  dst1 : start.toNat ≤ st.dst.toNat
  dst2 : st.dst.toNat ≤ src.toNat
  lnew : LayoutTo s.arena start st.dst.toNat N
  newCl : ∀ n ∈ N, ∃ o ∈ D, w.arena.garbage o = false ∧ s.arena.litsL n = filt w o ∧
    s.arena.redundant n = w.arena.redundant o ∧ s.arena.garbage n = false ∧ s.arena.searched n = 2 ∧
    3 ≤ (s.arena.size n).toNat
  oldCl : ∀ o ∈ D, w.arena.garbage o = false → SatW w o ∨
    (∃ a b, filt w o = [a, b] ∧ s.BinWatched a b ∧ s.BinWatched b a) ∨
    (∃ n ∈ N, s.arena.litsL n = filt w o ∧ s.arena.redundant n = w.arena.redundant o)
  words : ∀ l, WordsOK (s.watchesOf l).data.toList
  ent : ∀ l, ∃ E : List Lit, s.entries l = w.entries l ++ E.map WEntry.bin
  binNew : ∀ a b, s.BinWatched a b → w.BinWatched a b ∨
    (s.BinWatched b a ∧ ∃ o ∈ D, w.arena.garbage o = false ∧ (filt w o = [a, b] ∨ filt w o = [b, a]))
  wsz : s.watches.size = w.watches.size
  asg : s.asg = { w.asg with aReason := s.asg.aReason, aBits := s.asg.aBits }
  rsz : s.asg.aReason.size = w.asg.aReason.size ∧ s.asg.aBits.size = w.asg.aBits.size
  bits : ∀ i b, AnaBit b → s.abit i b = w.abit i b
  reasons : ∀ l, w.IsTrue l → 0 < w.lvl l → RS w start s rest N l
  frame : stripS s = stripS w

/-! ### Basic facts -/

theorem lt_of_bound {w : Solver} (h : w.arena.Layout) {x : Ref} {e : Nat} (he : e ≤ w.arena.sizeWards)
    (hx : x.toNat < e) : x.toNat < 2 ^ 31 := by
  have := h.bound; omega

/-- Two true literals with the same large reason are equal. -/
theorem reason_unique {w : Solver} (hc : w.Core) (hr : w.ReasonOK) {l l' : Lit}
    (ht : w.IsTrue l) (hl : 0 < w.lvl l) (ht' : w.IsTrue l') (hl' : 0 < w.lvl l')
    (hb : w.binOf l = false) (hb' : w.binOf l' = false) (hd : w.reasonOf l ≠ DECISION_REASON)
    (he : w.reasonOf l' = w.reasonOf l) : l' = l := by
  rcases hr l ht hl with h | ⟨h1, _⟩ | ⟨_, _, _, h4⟩
  · exact absurd h hd
  · rw [hb] at h1; simp at h1
  · rcases hr l' ht' hl' with h | ⟨h1, _⟩ | ⟨_, _, h3, _⟩
    · rw [he] at h; exact absurd h hd
    · rw [hb'] at h1; simp at h1
    · rw [he] at h3
      apply Classical.byContradiction; intro hne
      exact (hc.valCons l').2 ⟨ht', (h4 l' h3 hne).1⟩

/-- The reason clause of `l` is not satisfied at the root level. -/
theorem reason_not_sat {w : Solver} (hc : w.Core) (hr : w.ReasonOK) {l : Lit}
    (ht : w.IsTrue l) (hl : 0 < w.lvl l) (hb : w.binOf l = false) (hd : w.reasonOf l ≠ DECISION_REASON) :
    ¬ SatW w (w.reasonOf l) := by
  rintro ⟨x, hx, hxt⟩
  rcases hr l ht hl with h | ⟨h1, _⟩ | ⟨_, _, _, h4⟩
  · exact hd h
  · rw [hb] at h1; simp at h1
  · unfold rootT at hxt
    simp only [Bool.and_eq_true, beq_iff_eq] at hxt
    have hxT : w.IsTrue x := (isTrue_iff_vTrue w x).mpr hxt.1
    by_cases e : x = l
    · subst e; unfold lvl at hl; unfold level' at hxt; rw [hxt.2] at hl; simp at hl
    · exact (hc.valCons x).2 ⟨hxT, (h4 x hx e).1⟩

theorem reason_live {w : Solver} (hr : w.ReasonOK) {l : Lit}
    (ht : w.IsTrue l) (hl : 0 < w.lvl l) (hb : w.binOf l = false) (hd : w.reasonOf l ≠ DECISION_REASON) :
    w.LiveRef (w.reasonOf l) := by
  rcases hr l ht hl with h | ⟨h1, _⟩ | ⟨_, h2, _, _⟩
  · exact absurd h hd
  · rw [hb] at h1; simp at h1
  · exact h2

theorem SwI.head {w : Solver} {start : Ref} {Q : List Ref} {s : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (h : SwI w start Q s st src (src :: rest) D N) :
    src.toNat < w.arena.sizeWards ∧ w.arena.shrunken src = false ∧
    (w.arena.nextClause src).toNat = src.toNat + wardsOfClause (w.arena.size src).toNat ∧
    LayoutTo w.arena (w.arena.nextClause src) w.arena.sizeWards rest ∧
    s.arena.word0 src = w.arena.word0 src ∧ s.arena.size src = w.arena.size src ∧
    s.arena.nextClause src = w.arena.nextClause src := by
  obtain ⟨_, hlt, hsh, hnext, hrest⟩ := h.lrest
  have hm4 : 4 * src.toNat + 3 ≤ w.arena.words.size := by
    have := LayoutTo.le hrest
    have := wardsOfClause_pos (w.arena.size src).toNat
    unfold sizeWards at *; omega
  obtain ⟨e0, _, e2⟩ := header_eq_of_eqOn (h.untouched.mono (Nat.le_refl _) hm4)
  exact ⟨hlt, hsh, hnext, hrest, e0, e2, nextClause_eq e0.symm e2.symm hsh |>.symm⟩

theorem RS.drop {w : Solver} {start : Ref} {s : Solver} {src : Ref} {rest N : List Ref} {l : Lit}
    (h : RS w start s (src :: rest) N l)
    (hne : w.binOf l = false ∧ w.reasonOf l ≠ DECISION_REASON ∧ start ≤ w.reasonOf l → w.reasonOf l ≠ src) :
    RS w start s rest N l := by
  unfold RS at *
  split
  · rename_i hc
    rw [if_pos hc] at h
    rcases h with ⟨h1, h2, h3⟩ | h | h
    · rcases List.mem_cons.mp h1 with e | h1
      · exact absurd e (hne hc)
      · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rename_i hc
    rw [if_neg hc] at h; exact h

theorem sweep_garbage {w : Solver} {start : Ref} {Q : List Ref} {s : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N)
    (hg : s.arena.garbage src = true) :
    SwI w start Q s (st.dropLast src start) (w.arena.nextClause src) rest (D ++ [src]) N := by
  obtain ⟨hlt, hsh, hnext, hrest, e0, e2, en⟩ := hI.head
  have hgA : w.arena.garbage src = true := by unfold garbage at *; rw [← flag_eq_of_word0 e0]; exact hg
  have hdst : (st.dropLast src start).dst = st.dst := by unfold SweepState.dropLast; split <;> rfl
  refine ⟨by rw [hI.qsplit]; simp, hrest, hI.wsize, hI.untouched.mono (by omega) (Nat.le_refl _), hI.pre,
    by rw [hdst]; exact hI.dst1, by rw [hdst]; have := hI.dst2; omega, by rw [hdst]; exact hI.lnew, ?_, ?_,
    hI.words, hI.ent, ?_, hI.wsz, hI.asg, hI.rsz, hI.bits, ?_, hI.frame⟩
  · intro n hn
    obtain ⟨o, ho, h⟩ := hI.newCl n hn
    exact ⟨o, List.mem_append_left _ ho, h⟩
  · intro o ho hgo
    rcases List.mem_append.mp ho with ho | ho
    · exact hI.oldCl o ho hgo
    · simp at ho; subst ho; rw [hgA] at hgo; simp at hgo
  · intro a b hab
    rcases hI.binNew a b hab with h | ⟨hba, o, ho, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hba, o, List.mem_append_left _ ho, h⟩
  · intro l ht hl
    apply (hI.reasons l ht hl).drop
    intro hc e
    have := (reason_live hp.reasons ht hl hc.1 hc.2.1).2
    rw [e, hgA] at this; simp at this

theorem rootF_congr {s w : Solver} (h : s.asg = { w.asg with aReason := s.asg.aReason, aBits := s.asg.aBits })
    (x : Lit) : s.rootF x = w.rootF x ∧ s.rootT x = w.rootT x ∧ s.value x = w.value x := by
  have hv : s.asg.values = w.asg.values := by rw [h]
  have hl : s.asg.aLevel = w.asg.aLevel := by rw [h]
  unfold rootF rootT value level'
  rw [hv, hl]; exact ⟨rfl, rfl, rfl⟩

theorem validLit_ne_invalid {w : Solver} (hv : w.vars.toNat < 2 ^ 30) {x : Lit} (h : w.ValidLit x) :
    x ≠ INVALID_LIT := by
  intro e; subst e
  unfold ValidLit at h; rw [IDX_toNat] at h
  simp [INVALID_LIT] at h; omega

theorem clauseL_eq_range' (w : Solver) (r : Ref) :
    (List.range' 0 ((w.arena.size r).toNat - 0)).map (fun k => w.arena.lit r k) = w.clauseL r := by
  unfold clauseL; rw [Nat.sub_zero, List.range_eq_range']

/-- The literal phase of sweeping a non-garbage clause. -/
theorem sweep_lits_phase {w : Solver} {start : Ref} {Q : List Ref} {s : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N)
    (hg : w.arena.garbage src = false) :
    let r := sweepLits s (litPos src 0) (s.arena.size src).toNat
      { words := (s.arena.copyWord0 st.dst src).words, qpos := litPos st.dst 0 } 0
    r.2.words.size = w.arena.words.size ∧
    litPos st.dst 0 ≤ r.2.qpos ∧ r.2.qpos ≤ litPos src 0 + (w.arena.size src).toNat ∧
    litPos src 0 + (w.arena.size src).toNat ≤ 4 * (w.arena.nextClause src).toNat ∧
    (∀ j, j ≠ 4 * st.dst.toNat → (j < litPos st.dst 0 ∨ r.2.qpos ≤ j) → r.2.words.get! j = s.arena.words.get! j) ∧
    r.2.words.get! (4 * st.dst.toNat) = w.arena.word0 src ∧
    (r.1 = false → SatW w src) ∧
    (r.1 = true → (∀ x ∈ w.clauseL src, w.rootT x = false) ∧ r.2.qpos = litPos st.dst 0 + (filt w src).length ∧
      (∀ k, k < (filt w src).length → r.2.words.get! (litPos st.dst 0 + k) = (filt w src).getD k 0) ∧
      LitAcc w (filt w src) r.2) := by
  intro r
  obtain ⟨hlt, hsh, hnext, hrest, e0, e2, en⟩ := hI.head
  have hsz := hI.wsize
  have hm4 := hp.lay.mult4
  have hwp := wardsOfClause_pos (w.arena.size src).toNat
  have hwf := wardsOfClause_fits (w.arena.size src).toNat
  have hle := LayoutTo.le hrest
  have hd2 := hI.dst2
  have hsrc : src ∈ Q := by rw [hI.qsplit]; simp
  obtain ⟨hval, _⟩ := hp.live src hsrc hg
  have hcopy : (s.arena.copyWord0 st.dst src).words = s.arena.words.set! (4 * st.dst.toNat) (w.arena.word0 src) := by
    unfold copyWord0 setWord0 base; rw [e0]
  have hqs : 4 * st.dst.toNat < s.arena.words.size := by omega
  -- the literal function
  let f : Nat → Lit := fun k => w.arena.lit src k
  have hf : ∀ k < (s.arena.size src).toNat, f k ≠ INVALID_LIT := by
    intro k hk
    rw [e2] at hk
    apply validLit_ne_invalid hp.varsBound
    apply hval
    unfold clauseL; exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  have hw : ∀ k, 0 ≤ k → k < (s.arena.size src).toNat →
      (({ words := (s.arena.copyWord0 st.dst src).words, qpos := litPos st.dst 0 } : SweepLits)).words.get!
        (litPos src 0 + k) = f k := by
    intro k _ hk
    rw [e2] at hk
    show (s.arena.copyWord0 st.dst src).words.get! (litPos src 0 + k) = w.arena.lit src k
    rw [hcopy, U32Vec.get!_set!_ne _ _ _ _ (by unfold litPos base; omega)]
    exact hI.untouched _ (by unfold litPos base; omega) (by unfold litPos base; omega)
  have hacc : LitAcc s [] ({ words := (s.arena.copyWord0 st.dst src).words, qpos := litPos st.dst 0 } : SweepLits) :=
    LitAcc.init _ _ rfl rfl rfl rfl
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := sweepLits_spec s (litPos src 0) (s.arena.size src).toNat f hf _ 0 [] hw
    (by dsimp only; unfold litPos base; omega) (Nat.zero_le _)
    (by dsimp only; rw [hcopy, U32Vec.size_set!, hsz, e2]; unfold litPos base; omega) hacc
  dsimp only at a1 a2 a3 a4 a6
  have hcl : (List.range' 0 ((s.arena.size src).toNat - 0)).map f = w.clauseL src := by
    rw [e2]; exact clauseL_eq_range' w src
  have hrF : ∀ x, s.rootF x = w.rootF x := fun x => (rootF_congr hI.asg x).1
  have hrT : ∀ x, s.rootT x = w.rootT x := fun x => (rootF_congr hI.asg x).2.1
  have hfl : ((List.range' 0 ((s.arena.size src).toNat - 0)).map f).filter (fun x => !s.rootF x) = filt w src := by
    rw [hcl]; unfold filt; congr 1; funext x; rw [hrF]
  rw [hfl] at a6; rw [hcl] at a5 a6
  refine ⟨by rw [a1, hcopy, U32Vec.size_set!, hsz], a2, by rw [← e2]; exact a3, by
      unfold litPos base; omega, fun j hj1 hj2 => ?_, ?_, fun e => ?_, fun e => ?_⟩
  · rw [a4 j hj2, hcopy, U32Vec.get!_set!_ne _ _ _ _ (Ne.symm hj1)]
  · rw [a4 _ (Or.inl (by unfold litPos base; omega)), hcopy, U32Vec.get!_set!_self _ _ _ hqs]
  · obtain ⟨x, hx, hxt⟩ := a5 e; exact ⟨x, hx, by rw [← hrT]; exact hxt⟩
  · obtain ⟨b1, b2, b3, b4⟩ := a6 e
    refine ⟨fun x hx => by rw [← hrT]; exact b1 x hx, b2, b3, ?_⟩
    obtain ⟨c0, c1, c2, c3, c4⟩ := b4
    have hv : ∀ x, s.value x = w.value x := fun x => (rootF_congr hI.asg x).2.2
    refine ⟨by simpa using c0, by simpa using c1, by simpa using c2, fun h => ?_, fun h => ?_⟩
    · obtain ⟨m1, m2⟩ := c3 h; exact ⟨by simpa using m1, by rw [← hv]; exact m2⟩
    · obtain ⟨m1, m2⟩ := c4 h; exact ⟨by simpa using m1, by rw [← hv]; exact m2⟩

/-- The new clauses are read from `[4 start, 4 dst)`. -/
theorem newPart_congr {a b : Arena} {start : Ref} {dst : Nat} {N : List Ref} (hN : LayoutTo a start dst N)
    (he : EqOn b a (4 * start.toNat) (4 * dst)) :
    LayoutTo b start dst N ∧ ∀ n ∈ N, b.word0 n = a.word0 n ∧ b.searched n = a.searched n ∧
      b.size n = a.size n ∧ b.litsL n = a.litsL n := by
  refine ⟨hN.congr he.symm, fun n hn => ?_⟩
  obtain ⟨h1, h2, _⟩ := hN.mem_bounds n hn
  have := clause_eq_of_eqOn (a := a) (b := b) (x := n) (he.symm.mono (by omega) (by omega))
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm⟩

/-- Invariant transfer when only arena words in `[4 dst, 4 next)` changed and nothing else
  relevant: the sweep of a satisfied clause. -/
theorem sweep_sat_inv {w : Solver} {start : Ref} {Q : List Ref} {s s2 : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N)
    (hg : w.arena.garbage src = false) (hsat : SatW w src)
    (ha : s2.arena.words.size = s.arena.words.size)
    (hlo : EqOn s2.arena s.arena 0 (4 * st.dst.toNat))
    (hhi : EqOn s2.arena s.arena (4 * (w.arena.nextClause src).toNat) s.arena.words.size)
    (hasg : s2.asg = s.asg) (hwat : s2.watches = s.watches) (hfr : stripS s2 = stripS s) :
    SwI w start Q s2 (st.dropLast src start) (w.arena.nextClause src) rest (D ++ [src]) N := by
  obtain ⟨hlt, hsh, hnext, hrest, e0, e2, en⟩ := hI.head
  have hdst : (st.dropLast src start).dst = st.dst := by unfold SweepState.dropLast; split <;> rfl
  have hd1 := hI.dst1
  have hd2 := hI.dst2
  have hwp := wardsOfClause_pos (w.arena.size src).toNat
  obtain ⟨n1, n2⟩ := newPart_congr hI.lnew (hlo.mono (Nat.zero_le _) (Nat.le_refl _))
  have eE : ∀ l, s2.entries l = s.entries l := by intro l; simp [entries, watchesOf, hwat]
  have eB : ∀ a b, s2.BinWatched a b ↔ s.BinWatched a b := by intro a b; simp [BinWatched, eE]
  have eR : ∀ l, s2.reasonOf l = s.reasonOf l := by intro l; simp [reasonOf, reasonIdx, hasg]
  have eBo : ∀ l, s2.binOf l = s.binOf l := by intro l; simp [binOf, isBinaryReason, abit, abits, hasg]
  have hlit : ∀ n ∈ N, s2.arena.litsL n = s.arena.litsL n := fun n hn => (n2 n hn).2.2.2
  refine ⟨by rw [hI.qsplit]; simp, hrest, by rw [ha, hI.wsize], ?_, ?_, by rw [hdst]; exact hd1,
    by rw [hdst]; omega, by rw [hdst]; exact n1, ?_, ?_, ?_, ?_, ?_, by rw [hwat]; exact hI.wsz,
    by rw [hasg]; exact hI.asg, by rw [hasg]; exact hI.rsz, ?_, ?_, by rw [hfr]; exact hI.frame⟩
  · intro j h1 h2
    rw [hhi j h1 (by rw [hI.wsize]; exact h2)]
    exact hI.untouched j (by omega) h2
  · intro j h1 h2
    rw [hlo j h1 (by omega)]; exact hI.pre j h1 h2
  · intro n hn
    obtain ⟨o, ho, h1, h2, h3, h4, h5, h6⟩ := hI.newCl n hn
    obtain ⟨m0, m1, m2, m3⟩ := n2 n hn
    refine ⟨o, List.mem_append_left _ ho, h1, by rw [m3, h2], ?_, ?_, by rw [m1, h5], by rw [m2]; exact h6⟩
    · unfold redundant; rw [flag_eq_of_word0 m0]; exact h3
    · unfold garbage; rw [flag_eq_of_word0 m0]; exact h4
  · intro o ho hgo
    rcases List.mem_append.mp ho with ho | ho
    · rcases hI.oldCl o ho hgo with h | ⟨a, b, h1, h2, h3⟩ | ⟨n, hn, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨a, b, h1, (eB a b).mpr h2, (eB b a).mpr h3⟩)
      · refine Or.inr (Or.inr ⟨n, hn, by rw [hlit n hn, h1], ?_⟩)
        unfold redundant; rw [flag_eq_of_word0 (n2 n hn).1]; exact h2
    · simp at ho; subst ho; exact Or.inl hsat
  · intro l; unfold watchesOf; rw [hwat]; exact hI.words l
  · intro l; rw [eE]; exact hI.ent l
  · intro a b hab
    rcases hI.binNew a b ((eB a b).mp hab) with h | ⟨hba, o, ho, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨(eB b a).mpr hba, o, List.mem_append_left _ ho, h⟩
  · intro i b hb; unfold abit abits; rw [hasg]; exact hI.bits i b hb
  · intro l ht hl
    have hR := (hI.reasons l ht hl).drop (fun hc e => by
      have := reason_not_sat hp.core hp.reasons ht hl hc.1 hc.2.1; rw [e] at this; exact this hsat)
    unfold RS at hR ⊢
    split
    · rename_i hc
      rw [if_pos hc] at hR
      rw [eR, eBo]
      rcases hR with h | ⟨h1, n, hn, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h1, n, hn, h2, by rw [hlit n hn, h3]⟩)
      · exact Or.inr (Or.inr ⟨h1, (eB _ _).mpr h2, h3, h4⟩)
    · rename_i hc
      rw [if_neg hc] at hR
      rw [eR, eBo]; exact hR

theorem src_ne_decision {w : Solver} {start : Ref} {Q : List Ref} {s : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N) :
    src ≠ DECISION_REASON := by
  obtain ⟨hlt, _⟩ := hI.head
  have := hp.lay.bound
  intro e; rw [e] at hlt; simp [DECISION_REASON] at hlt; omega

/-- A true literal whose current (large) reason is the clause being swept had it as old reason. -/
theorem forced_reason {w : Solver} {start : Ref} {Q : List Ref} {s : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N) {f : Lit}
    (ht : w.IsTrue f) (hl : 0 < w.lvl f) (hr : s.reasonOf f = src) (hb : s.binOf f = false) :
    w.reasonOf f = src ∧ w.binOf f = false ∧ start ≤ src := by
  have hdec := src_ne_decision hp hI
  have hss : start ≤ src := by
    have := hI.dst1; have := hI.dst2
    rw [UInt32.le_iff_toNat_le]; omega
  have hR := hI.reasons f ht hl
  unfold RS at hR
  split at hR
  · rename_i hc
    rcases hR with ⟨h1, h2, h3⟩ | ⟨h1, n, hn, h2, h3⟩ | ⟨h1, _⟩
    · rw [hr] at h2; exact ⟨h2.symm, hc.1, hss⟩
    · exfalso
      rw [hr] at h2; subst h2
      have := (hI.lnew.mem_bounds _ hn).2.1
      have := wardsOfClause_pos (s.arena.size src).toNat
      have := hI.dst2; omega
    · rw [hb] at h1; simp at h1
  · rename_i hc
    exfalso; apply hc
    rw [← hR.1, ← hR.2, hr, hb]
    exact ⟨rfl, hdec, hss⟩

theorem idx_ne_of_true {w : Solver} (hc : w.Core) {l f : Lit} (hl : w.IsTrue l) (hf : w.IsTrue f) (hne : l ≠ f) :
    IDX l ≠ IDX f := by
  intro e
  rcases (IDX_eq_iff l f).mp e with h | h
  · exact hne h
  · subst h
    exact (hc.valCons (NOT f)).2 ⟨hl, (hc.valCons f).1.mp hf⟩

theorem watchBinary_entries (s : Solver) (x y : Lit) (hx : x.toNat < s.watches.size) (hy : y.toNat < s.watches.size)
    (hx31 : x.toNat < 2 ^ 31) (hy31 : y.toNat < 2 ^ 31) (hW : ∀ l, WordsOK (s.watchesOf l).data.toList) :
    (∀ l, WordsOK ((s.watchBinary x y).watchesOf l).data.toList) ∧
    (∀ l, (s.watchBinary x y).entries l =
      s.entries l ++ (if l = x then [WEntry.bin y] else []) ++ (if l = y then [WEntry.bin x] else [])) ∧
    (s.watchBinary x y).watches.size = s.watches.size := by
  have h1 := (watchOther_adds s x y hx).entries hW (show WEntry.WF (.bin y) from hy31)
  have hsz1 : (s.watchOther x y).watches.size = s.watches.size := modifyWatches_size _ _ _
  have hW1 : ∀ l, WordsOK ((s.watchOther x y).watchesOf l).data.toList := fun l => (h1 l).2
  have h2 := (watchOther_adds (s.watchOther x y) y x (by rw [hsz1]; exact hy)).entries hW1
    (show WEntry.WF (.bin x) from hx31)
  refine ⟨fun l => (h2 l).2, fun l => ?_, by
    show ((s.watchOther x y).watchOther y x).watches.size = _
    rw [show ((s.watchOther x y).watchOther y x).watches.size = (s.watchOther x y).watches.size from
      modifyWatches_size _ _ _, hsz1]⟩
  unfold watchBinary
  rw [(h2 l).1, (h1 l).1]
  by_cases ex : l = x <;> by_cases ey : l = y
  · rw [if_pos ey, if_pos ex, if_pos ex, if_pos ey]; try simp
  · rw [if_neg ey, if_pos ex, if_pos ex, if_neg ey]; try simp
  · rw [if_pos ey, if_neg ex, if_neg ex, if_pos ey]; try simp
  · rw [if_neg ey, if_neg ex, if_neg ex, if_neg ey]; try simp

theorem abit_or_binary (v : UInt8) (b : UInt8) (hb : AnaBit b) :
    ((v ||| ABits.binary) &&& b != 0) = (v &&& b != 0) := by
  have key : ((v ||| ABits.binary) &&& b = 0) ↔ (v &&& b = 0) := by
    rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [ABits.analyzed, ABits.binary, ABits.poisoned, ABits.removable, ABits.shrinkable] <;>
      constructor <;> intro h <;> bv_decide
  cases h1 : ((v ||| ABits.binary) &&& b != 0) <;> cases h2 : (v &&& b != 0) <;> simp_all

/-- No true literal has the clause at `src` as large reason. -/
def NoReason (w : Solver) (start src : Ref) : Prop :=
  ∀ l, w.IsTrue l → 0 < w.lvl l → w.binOf l = false → w.reasonOf l ≠ DECISION_REASON → start ≤ w.reasonOf l →
    w.reasonOf l ≠ src

/-- The assignment update of a reason moved to `y` (`binary = true`: binary reason, else large). -/
def moveAsg (s : Solver) (f : Lit) (y : UInt32) (binary : Bool) : Asg :=
  if binary then
    { s.asg with aBits := s.asg.aBits.set! (IDX f).toNat (s.abits (IDX f) ||| ABits.binary),
                 aReason := s.asg.aReason.set! (IDX f).toNat y }
  else { s.asg with aReason := s.asg.aReason.set! (IDX f).toNat y }

theorem moveAsg_reads {s t : Solver} {f : Lit} {y : UInt32} {binary : Bool} (h : t.asg = moveAsg s f y binary)
    (hf : (IDX f).toNat < s.asg.aReason.size) (hfb : (IDX f).toNat < s.asg.aBits.size) (l : Lit) :
    t.reasonOf l = (if IDX l = IDX f then y else s.reasonOf l) ∧
    t.binOf l = (if IDX l = IDX f then (binary || s.binOf l) else s.binOf l) ∧
    (∀ b, AnaBit b → t.abit (IDX l) b = s.abit (IDX l) b) ∧
    t.asg.aReason.size = s.asg.aReason.size ∧ t.asg.aBits.size = s.asg.aBits.size := by
  have hR : t.asg.aReason = s.asg.aReason.set! (IDX f).toNat y := by rw [h]; unfold moveAsg; split <;> rfl
  have hB : t.asg.aBits = if binary then s.asg.aBits.set! (IDX f).toNat (s.abits (IDX f) ||| ABits.binary)
      else s.asg.aBits := by rw [h]; unfold moveAsg; split <;> rfl
  have hbit : ∀ b, t.abit (IDX l) b = if IDX l = IDX f ∧ binary = true then
      ((s.abits (IDX f) ||| ABits.binary) &&& b != 0) else s.abit (IDX l) b := by
    intro b
    unfold abit abits; rw [hB]
    cases binary
    · simp
    · simp only [ite_true, and_true]
      rw [ByteArray.get!_set!]
      by_cases e : IDX l = IDX f
      · rw [if_pos ⟨by rw [e], hfb⟩, if_pos e]; rfl
      · rw [if_neg (fun h => e (UInt32.toNat_inj.mp h.1.symm)), if_neg e]
  refine ⟨?_, ?_, fun b hb => ?_, by rw [hR]; simp, by rw [hB]; split <;> simp⟩
  · unfold reasonOf reasonIdx; rw [hR, U32Vec.get!_set!]
    by_cases e : IDX l = IDX f
    · rw [if_pos e, if_pos ⟨by rw [e], by rw [e]; exact hf⟩]
    · rw [if_neg e, if_neg (fun h => e (UInt32.toNat_inj.mp h.1.symm))]
  · unfold binOf isBinaryReason; rw [hbit]
    by_cases e : IDX l = IDX f
    · rw [if_pos e]
      cases binary
      · simp [e]
      · simp only [true_and, e, ite_true, Bool.true_or]
        have : (s.abits (IDX f) ||| ABits.binary) &&& ABits.binary = 2 := by unfold ABits.binary; bv_decide
        rw [this]; decide
    · rw [if_neg e, if_neg (fun h => e h.1)]
  · rw [hbit]
    split
    · rename_i hc
      rw [abit_or_binary _ b hb]; unfold abit abits; rw [hc.1]
    · rfl

theorem RS.mono {w : Solver} {start : Ref} {s s' : Solver} {rest N N' : List Ref} {l : Lit}
    (h : RS w start s rest N l) (he : s'.reasonOf l = s.reasonOf l ∧ s'.binOf l = s.binOf l)
    (hN : ∀ n ∈ N, n ∈ N' ∧ s'.arena.litsL n = s.arena.litsL n)
    (hB : ∀ a b, s.BinWatched a b → s'.BinWatched a b) : RS w start s' rest N' l := by
  unfold RS at *
  rw [he.1, he.2]
  split
  · rename_i hc
    rw [if_pos hc] at h
    rcases h with h | ⟨h1, n, hn, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, n, (hN n hn).1, h2, by rw [(hN n hn).2, h3]⟩)
    · exact Or.inr (Or.inr ⟨h1, hB _ _ h2, h3, h4⟩)
  · rename_i hc
    rw [if_neg hc] at h; exact h

/-- The new reason of the literal `f` forced by the clause at `src`. -/
def NewR (w : Solver) (src : Ref) (s : Solver) (N : List Ref) (f : Lit) : Prop :=
  (s.binOf f = false ∧ ∃ n ∈ N, s.reasonOf f = n ∧ s.arena.litsL n = filt w src) ∨
  (s.binOf f = true ∧ s.BinWatched f (s.reasonOf f) ∧ s.reasonOf f ∈ w.clauseL src ∧ s.reasonOf f ≠ f)

theorem rs_after {w : Solver} {start : Ref} {Q : List Ref} {s s' : Solver} {st : SweepState} {src : Ref}
    {rest D N N' : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N)
    (hN : ∀ n ∈ N, n ∈ N' ∧ s'.arena.litsL n = s.arena.litsL n)
    (hB : ∀ a b, s.BinWatched a b → s'.BinWatched a b)
    (hupd : ((∀ l, s'.reasonOf l = s.reasonOf l ∧ s'.binOf l = s.binOf l) ∧ NoReason w start src) ∨
      ∃ f, w.IsTrue f ∧ 0 < w.lvl f ∧ s.reasonOf f = src ∧ s.binOf f = false ∧
        (∀ l, w.IsTrue l → l ≠ f → s'.reasonOf l = s.reasonOf l ∧ s'.binOf l = s.binOf l) ∧
        NewR w src s' N' f) :
    ∀ l, w.IsTrue l → 0 < w.lvl l → RS w start s' rest N' l := by
  intro l ht hl
  have hR := hI.reasons l ht hl
  rcases hupd with ⟨he, hno⟩ | ⟨f, hft, hfl, hfr, hfb, he, hnew⟩
  · exact (hR.drop (fun hc => hno l ht hl hc.1 hc.2.1 hc.2.2)).mono (he l) hN hB
  · by_cases e : l = f
    · subst e
      obtain ⟨k1, k2, k3⟩ := forced_reason hp hI ht hl hfr hfb
      unfold RS
      rw [if_pos ⟨k2, by rw [k1]; exact src_ne_decision hp hI, by rw [k1]; exact k3⟩, k1]
      exact Or.inr hnew
    · apply (hR.drop _).mono (he l ht e) hN hB
      intro hc e2
      obtain ⟨k1, k2, _⟩ := forced_reason hp hI hft hfl hfr hfb
      exact e (reason_unique hp.core hp.reasons hft hfl ht hl k2 hc.1 (by rw [k1]; exact src_ne_decision hp hI)
        (by rw [e2, k1]))

theorem validLit_bounds {w : Solver} (hp2 : 2 * w.vars.toNat ≤ w.watches.size) (hv : w.vars.toNat < 2 ^ 30)
    {x : Lit} (h : w.ValidLit x) : x.toNat < w.watches.size ∧ x.toNat < 2 ^ 31 := by
  unfold ValidLit at h; rw [IDX_toNat] at h; omega

/-- Invariant transfer for a clause that became binary. -/
theorem sweep_bin_inv {w : Solver} {start : Ref} {Q : List Ref} {s s' : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N)
    (hg : w.arena.garbage src = false) {x y : Lit} (hK : filt w src = [x, y]) (hxv : w.ValidLit x) (hyv : w.ValidLit y)
    (ha : s'.arena.words.size = s.arena.words.size)
    (hlo : EqOn s'.arena s.arena 0 (4 * st.dst.toNat))
    (hhi : EqOn s'.arena s.arena (4 * (w.arena.nextClause src).toNat) s.arena.words.size)
    (hwat : s'.watches = (s.watchBinary x y).watches)
    (hasg : s'.asg = { w.asg with aReason := s'.asg.aReason, aBits := s'.asg.aBits })
    (hrsz : s'.asg.aReason.size = s.asg.aReason.size ∧ s'.asg.aBits.size = s.asg.aBits.size)
    (hbits : ∀ i b, AnaBit b → s'.abit i b = s.abit i b)
    (hupd : ((∀ l, s'.reasonOf l = s.reasonOf l ∧ s'.binOf l = s.binOf l) ∧ NoReason w start src) ∨
      ∃ f, w.IsTrue f ∧ 0 < w.lvl f ∧ s.reasonOf f = src ∧ s.binOf f = false ∧
        (∀ l, w.IsTrue l → l ≠ f → s'.reasonOf l = s.reasonOf l ∧ s'.binOf l = s.binOf l) ∧
        NewR w src s' N f)
    (hfr : stripS s' = stripS s) :
    SwI w start Q s' (st.dropLast src start) (w.arena.nextClause src) rest (D ++ [src]) N := by
  obtain ⟨hlt, hsh, hnext, hrest, e0, e2, en⟩ := hI.head
  have hdst : (st.dropLast src start).dst = st.dst := by unfold SweepState.dropLast; split <;> rfl
  have hd1 := hI.dst1
  have hd2 := hI.dst2
  have hwp := wardsOfClause_pos (w.arena.size src).toNat
  obtain ⟨n1, n2⟩ := newPart_congr hI.lnew (hlo.mono (Nat.zero_le _) (Nat.le_refl _))
  have hlit : ∀ n ∈ N, s'.arena.litsL n = s.arena.litsL n := fun n hn => (n2 n hn).2.2.2
  have hwsz := hI.wsz
  obtain ⟨bx1, bx2⟩ := validLit_bounds hp.watchesSize hp.varsBound hxv
  obtain ⟨by1, by2⟩ := validLit_bounds hp.watchesSize hp.varsBound hyv
  obtain ⟨wb1, wb2, wb3⟩ := watchBinary_entries s x y (by omega) (by omega) bx2 by2 hI.words
  have eE : ∀ l, s'.entries l = s.entries l ++ (if l = x then [WEntry.bin y] else []) ++
      (if l = y then [WEntry.bin x] else []) := by
    intro l; rw [← wb2 l]; simp [entries, watchesOf, hwat]
  have hB : ∀ a b, s.BinWatched a b → s'.BinWatched a b := by
    intro a b h; unfold BinWatched at *; rw [eE]; simp [h]
  have hBx : s'.BinWatched x y := by unfold BinWatched; rw [eE]; simp
  have hBy : s'.BinWatched y x := by unfold BinWatched; rw [eE]; simp
  refine ⟨by rw [hI.qsplit]; simp, hrest, by rw [ha, hI.wsize], ?_, ?_, by rw [hdst]; exact hd1,
    by rw [hdst]; omega, by rw [hdst]; exact n1, ?_, ?_, ?_, ?_, ?_, by rw [hwat, wb3, hwsz],
    hasg, by rw [hrsz.1, hrsz.2]; exact hI.rsz, fun i b hb => by rw [hbits i b hb]; exact hI.bits i b hb,
    rs_after hp hI (fun n hn => ⟨hn, hlit n hn⟩) hB hupd, by rw [hfr]; exact hI.frame⟩
  · intro j h1 h2
    rw [hhi j h1 (by rw [hI.wsize]; exact h2)]
    exact hI.untouched j (by omega) h2
  · intro j h1 h2
    rw [hlo j h1 (by omega)]; exact hI.pre j h1 h2
  · intro n hn
    obtain ⟨o, ho, h1, h2, h3, h4, h5, h6⟩ := hI.newCl n hn
    obtain ⟨m0, m1, m2, m3⟩ := n2 n hn
    refine ⟨o, List.mem_append_left _ ho, h1, by rw [m3, h2], ?_, ?_, by rw [m1, h5], by rw [m2]; exact h6⟩
    · unfold redundant; rw [flag_eq_of_word0 m0]; exact h3
    · unfold garbage; rw [flag_eq_of_word0 m0]; exact h4
  · intro o ho hgo
    rcases List.mem_append.mp ho with ho | ho
    · rcases hI.oldCl o ho hgo with h | ⟨a, b, h1, h2, h3⟩ | ⟨n, hn, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨a, b, h1, hB a b h2, hB b a h3⟩)
      · refine Or.inr (Or.inr ⟨n, hn, by rw [hlit n hn, h1], ?_⟩)
        unfold redundant; rw [flag_eq_of_word0 (n2 n hn).1]; exact h2
    · simp at ho; subst ho; exact Or.inr (Or.inl ⟨x, y, hK, hBx, hBy⟩)
  · intro l; unfold watchesOf; rw [hwat]; exact wb1 l
  · intro l
    obtain ⟨E, hE⟩ := hI.ent l
    refine ⟨E ++ (if l = x then [y] else []) ++ (if l = y then [x] else []), ?_⟩
    rw [eE, hE]
    have h1 : List.map WEntry.bin (if l = x then [y] else []) = (if l = x then [WEntry.bin y] else []) := by
      split <;> rfl
    have h2 : List.map WEntry.bin (if l = y then [x] else []) = (if l = y then [WEntry.bin x] else []) := by
      split <;> rfl
    simp only [List.map_append, List.append_assoc, h1, h2]
  · intro a b hab
    unfold BinWatched at hab; rw [eE] at hab
    simp only [List.mem_append] at hab
    rcases hab with (hab | hab) | hab
    · rcases hI.binNew a b hab with h | ⟨hba, o, ho, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hB b a hba, o, List.mem_append_left _ ho, h⟩
    · split at hab
      · rename_i e; simp at hab; subst hab; subst e
        exact Or.inr ⟨hBy, src, by simp, hg, Or.inl hK⟩
      · simp at hab
    · split at hab
      · rename_i e; simp at hab; subst hab; subst e
        exact Or.inr ⟨hBx, src, by simp, hg, Or.inr hK⟩
      · simp at hab

theorem wardsOfClause_mono {a b : Nat} (h : a ≤ b) : wardsOfClause a ≤ wardsOfClause b := by
  unfold wardsOfClause; omega

theorem litsL_of_lits {a : Arena} {x : Ref} {K : List Lit} (hs : (a.size x).toNat = K.length)
    (hl : ∀ k, k < K.length → a.lit x k = K.getD k 0) : a.litsL x = K := by
  unfold litsL
  apply List.ext_getElem
  · simp [hs]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hl i (by simpa using h2)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- Invariant transfer for a clause that stays large (moved to `dst`). -/
theorem sweep_large_inv {w : Solver} {start : Ref} {Q : List Ref} {s s' : Solver} {st st' : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N)
    (hg : w.arena.garbage src = false) (hK3 : 3 ≤ (filt w src).length)
    (ha : s'.arena.words.size = s.arena.words.size)
    (hlo : EqOn s'.arena s.arena 0 (4 * st.dst.toNat))
    (hhi : EqOn s'.arena s.arena (4 * (w.arena.nextClause src).toNat) s.arena.words.size)
    (hred : s'.arena.redundant st.dst = w.arena.redundant src) (hgar : s'.arena.garbage st.dst = false)
    (hshr : s'.arena.shrunken st.dst = false) (hsize : (s'.arena.size st.dst).toNat = (filt w src).length)
    (hsea : s'.arena.searched st.dst = 2)
    (hlits : ∀ k, k < (filt w src).length → s'.arena.lit st.dst k = (filt w src).getD k 0)
    (hst : st'.dst = s'.arena.nextClause st.dst)
    (hwat : s'.watches = s.watches)
    (hasg : s'.asg = { w.asg with aReason := s'.asg.aReason, aBits := s'.asg.aBits })
    (hrsz : s'.asg.aReason.size = s.asg.aReason.size ∧ s'.asg.aBits.size = s.asg.aBits.size)
    (hbits : ∀ i b, AnaBit b → s'.abit i b = s.abit i b)
    (hupd : ((∀ l, s'.reasonOf l = s.reasonOf l ∧ s'.binOf l = s.binOf l) ∧ NoReason w start src) ∨
      ∃ f, w.IsTrue f ∧ 0 < w.lvl f ∧ s.reasonOf f = src ∧ s.binOf f = false ∧
        (∀ l, w.IsTrue l → l ≠ f → s'.reasonOf l = s.reasonOf l ∧ s'.binOf l = s.binOf l) ∧
        NewR w src s' (N ++ [st.dst]) f)
    (hfr : stripS s' = stripS s) :
    SwI w start Q s' st' (w.arena.nextClause src) rest (D ++ [src]) (N ++ [st.dst]) := by
  obtain ⟨hlt, hsh, hnext, hrest, e0, e2, en⟩ := hI.head
  have hd1 := hI.dst1
  have hd2 := hI.dst2
  have hwp := wardsOfClause_pos (w.arena.size src).toNat
  have hKle : (filt w src).length ≤ (w.arena.size src).toNat := by
    unfold filt clauseL; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hwm := wardsOfClause_mono hKle
  have hwK := wardsOfClause_pos (filt w src).length
  have hbound := hp.lay.bound
  have hle := LayoutTo.le hrest
  obtain ⟨n1, n2⟩ := newPart_congr hI.lnew (hlo.mono (Nat.zero_le _) (Nat.le_refl _))
  have hlit : ∀ n ∈ N, s'.arena.litsL n = s.arena.litsL n := fun n hn => (n2 n hn).2.2.2
  have hnd : (s'.arena.nextClause st.dst).toNat = st.dst.toNat + wardsOfClause (filt w src).length := by
    unfold nextClause
    have hw32 : wardsOfClause (filt w src).length < 2 ^ 32 := by omega
    rw [actualWards_of_not_shrunken _ _ hshr, hsize, UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hw32]
    exact Nat.mod_eq_of_lt (by omega)
  have hdst' : st'.dst.toNat = st.dst.toNat + wardsOfClause (filt w src).length := by rw [hst, hnd]
  have hlay1 : LayoutTo s'.arena st.dst st'.dst.toNat [st.dst] :=
    ⟨rfl, by omega, hshr, by rw [hnd, hsize], by rw [← hst]; rfl⟩
  have hlitsD : s'.arena.litsL st.dst = filt w src := litsL_of_lits hsize hlits
  have eE : ∀ l, s'.entries l = s.entries l := by intro l; simp [entries, watchesOf, hwat]
  have eB : ∀ a b, s'.BinWatched a b ↔ s.BinWatched a b := by intro a b; simp [BinWatched, eE]
  refine ⟨by rw [hI.qsplit]; simp, hrest, by rw [ha, hI.wsize], ?_, ?_, by omega, by rw [hdst']; omega,
    n1.append hlay1, ?_, ?_, ?_, ?_, ?_, by rw [hwat]; exact hI.wsz,
    hasg, by rw [hrsz.1, hrsz.2]; exact hI.rsz, fun i b hb => by rw [hbits i b hb]; exact hI.bits i b hb,
    rs_after hp hI (fun n hn => ⟨List.mem_append_left _ hn, hlit n hn⟩) (fun a b h => (eB a b).mpr h) hupd,
    by rw [hfr]; exact hI.frame⟩
  · intro j h1 h2
    rw [hhi j h1 (by rw [hI.wsize]; exact h2)]
    exact hI.untouched j (by omega) h2
  · intro j h1 h2
    rw [hlo j h1 (by omega)]; exact hI.pre j h1 h2
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨o, ho, h1, h2, h3, h4, h5, h6⟩ := hI.newCl n hn
      obtain ⟨m0, m1, m2, m3⟩ := n2 n hn
      refine ⟨o, List.mem_append_left _ ho, h1, by rw [m3, h2], ?_, ?_, by rw [m1, h5], by rw [m2]; exact h6⟩
      · unfold redundant; rw [flag_eq_of_word0 m0]; exact h3
      · unfold garbage; rw [flag_eq_of_word0 m0]; exact h4
    · simp at hn; subst hn
      exact ⟨src, by simp, hg, hlitsD, hred, hgar, hsea, by rw [hsize]; exact hK3⟩
  · intro o ho hgo
    rcases List.mem_append.mp ho with ho | ho
    · rcases hI.oldCl o ho hgo with h | ⟨a, b, h1, h2, h3⟩ | ⟨n, hn, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨a, b, h1, (eB a b).mpr h2, (eB b a).mpr h3⟩)
      · refine Or.inr (Or.inr ⟨n, List.mem_append_left _ hn, by rw [hlit n hn, h1], ?_⟩)
        unfold redundant; rw [flag_eq_of_word0 (n2 n hn).1]; exact h2
    · simp at ho; subst ho; exact Or.inr (Or.inr ⟨st.dst, by simp, hlitsD, hred⟩)
  · intro l; unfold watchesOf; rw [hwat]; exact hI.words l
  · intro l; rw [eE]; exact hI.ent l
  · intro a b hab
    rcases hI.binNew a b ((eB a b).mp hab) with h | ⟨hba, o, ho, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨(eB b a).mpr hba, o, List.mem_append_left _ ho, h⟩

/-! ### The code of the clause step -/

theorem stripS_watchBinary (t : Solver) (a b : Lit) : stripS (t.watchBinary a b) = stripS t := rfl
theorem watchBinary_fields (t : Solver) (a b : Lit) : (t.watchBinary a b).arena = t.arena ∧
    (t.watchBinary a b).asg = t.asg ∧ (t.watchBinary a b).vars = t.vars ∧
    (t.watchBinary a b).notPorted = t.notPorted := ⟨rfl, rfl, rfl, rfl⟩
theorem watchBinary_watches {t u : Solver} (h : t.watches = u.watches) (a b : Lit) :
    (t.watchBinary a b).watches = (u.watchBinary a b).watches := by
  simp only [watchBinary, watchOther, modifyWatches, h]

theorem sweepBinary_shape (s : Solver) (dst src : Ref) (L : SweepLits) :
    ∃ sc : Solver, stripS sc = stripS s ∧ sc.arena = s.arena ∧ sc.asg = s.asg ∧ sc.vars = s.vars ∧
      sc.watches = (s.watchBinary L.mfirst L.msecond).watches ∧ sc.notPorted = s.notPorted ∧
      ((s.arena.reason dst = false ∧ s.sweepBinary dst src L = sc) ∨
       (s.arena.reason dst = true ∧ sc.reasonMoves L.forced src = true ∧ L.other ≠ INVALID_LIT ∧
         s.sweepBinary dst src L = { sc with asg := moveAsg sc L.forced L.other true }) ∨
       (s.sweepBinary dst src L).notPorted = true) := by
  unfold sweepBinary
  obtain ⟨s1, h1, e1⟩ : ∃ s1 : Solver, (stripS s1 = stripS s ∧ s1.arena = s.arena ∧ s1.asg = s.asg ∧
      s1.watches = s.watches ∧ s1.vars = s.vars ∧ s1.notPorted = s.notPorted) ∧
      (if (INC! s clauses_binary).arena.redundant dst then DEC! (INC! s clauses_binary) clauses_redundant
        else DEC! (INC! s clauses_binary) clauses_irredundant) = s1 :=
    ⟨_, by split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  dsimp only
  rw [e1]
  obtain ⟨f1, f2, f3, f4⟩ := watchBinary_fields s1 L.mfirst L.msecond
  refine ⟨s1.watchBinary L.mfirst L.msecond, (stripS_watchBinary _ _ _).trans h1.1, f1.trans h1.2.1,
    f2.trans h1.2.2.1, f3.trans h1.2.2.2.2.1, watchBinary_watches h1.2.2.2.1 _ _, f4.trans h1.2.2.2.2.2, ?_⟩
  have hra : (s1.watchBinary L.mfirst L.msecond).arena.reason dst = s.arena.reason dst := by rw [f1, h1.2.1]
  by_cases hr : s.arena.reason dst = true
  · rw [if_pos (hra.trans hr)]
    by_cases hg : ((s1.watchBinary L.mfirst L.msecond).reasonMoves L.forced src && L.other != INVALID_LIT) = true
    · rw [if_pos hg]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
      refine Or.inr (Or.inl ⟨hr, hg.1, hg.2, ?_⟩)
      unfold moveAsg setABit; simp only [ite_true]
    · rw [if_neg hg]; exact Or.inr (Or.inr rfl)
  · rw [if_neg (by rw [hra]; exact hr)]; exact Or.inl ⟨by simpa using hr, rfl⟩

/-- The header writes of `sweepLarge`. -/
def largeArena (a : Arena) (dst : Ref) (newSize : Nat) : Arena :=
  ((a.setSize dst (UInt32.ofNat newSize)).setShrunken dst false).setSearched dst 2

theorem sweepLarge_shape (s : Solver) (dst src : Ref) (newSize : Nat) (L : SweepLits) (st : SweepState) :
    (s.sweepLarge dst src newSize L st).1.notPorted = true ∨
    (3 ≤ newSize ∧ (s.sweepLarge dst src newSize L st).2.dst =
        (s.sweepLarge dst src newSize L st).1.arena.nextClause dst ∧
      (((((largeArena s.arena dst newSize).reason dst = false ∧
        (s.sweepLarge dst src newSize L st).1 = { s with arena := largeArena s.arena dst newSize }) ∨
       ((largeArena s.arena dst newSize).reason dst = true ∧ s.reasonMoves L.forced src = true ∧
        (s.sweepLarge dst src newSize L st).1 = { s with arena := (largeArena s.arena dst newSize).setReason dst false, asg := if s.reasonIdx (IDX L.forced) != dst then moveAsg s L.forced dst false else s.asg }))) ∨
       (s.sweepLarge dst src newSize L st).1.notPorted = true)) := by
  unfold sweepLarge
  by_cases h3 : newSize < 3
  · left
    rw [if_pos h3]
    dsimp only
    split
    · unfold updateLargeReasonFrom; split
      · unfold updateLargeReason; dsimp only; split <;> rfl
      · rfl
    · rfl
  · rw [if_neg h3]
    dsimp only
    right
    refine And.intro (by omega) (And.intro ?_ ?_)
    · split <;> rfl
    · show _ ∨ _
      unfold largeArena
      generalize ((s.arena.setSize dst (UInt32.ofNat newSize)).setShrunken dst false).setSearched dst 2 = A1
      have hrm : ({ s with arena := A1 } : Solver).reasonMoves L.forced src = s.reasonMoves L.forced src := rfl
      by_cases hr : A1.reason dst = true
      · rw [if_pos hr]
        unfold updateLargeReasonFrom
        rw [hrm]
        by_cases hg : s.reasonMoves L.forced src = true
        · rw [if_pos hg]
          refine Or.inl (Or.inr ⟨hr, hg, ?_⟩)
          unfold updateLargeReason moveAsg
          have hri : ({ s with arena := A1 } : Solver).reasonIdx (IDX L.forced) = s.reasonIdx (IDX L.forced) := rfl
          dsimp only
          rw [hri]
          split <;> rfl
        · rw [if_neg hg]; exact Or.inr rfl
      · rw [if_neg hr]
        exact Or.inl (Or.inl ⟨by simpa using hr, rfl⟩)

theorem largeArena_reads (a : Arena) (dst : Ref) (ns : Nat) (h : 4 * dst.toNat + 2 < a.words.size) :
    (largeArena a dst ns).words.size = a.words.size ∧
    (∀ j, j ≠ 4 * dst.toNat → j ≠ 4 * dst.toNat + 1 → j ≠ 4 * dst.toNat + 2 →
      (largeArena a dst ns).words.get! j = a.words.get! j) ∧
    (largeArena a dst ns).word0 dst = a.word0 dst &&& ~~~ClauseHeader.shrunkenBit ∧
    (largeArena a dst ns).size dst = UInt32.ofNat ns ∧ (largeArena a dst ns).searched dst = 2 := by
  simp only [largeArena, Arena.setSearched, Arena.setShrunken, Arena.setFlag, Arena.setWord0, Arena.setSize,
    Arena.word0, Arena.size, Arena.searched, Arena.base, Bool.false_eq_true, ite_false]
  refine ⟨by simp, fun j h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [U32Vec.get!_set!_ne _ _ _ _ (by omega), U32Vec.get!_set!_ne _ _ _ _ (by omega),
      U32Vec.get!_set!_ne _ _ _ _ (by omega)]
  · rw [U32Vec.get!_set!_ne _ _ _ _ (by omega), U32Vec.get!_set!_self _ _ _ (by simp; omega),
      U32Vec.get!_set!_ne _ _ _ _ (by omega)]
  · rw [U32Vec.get!_set!_ne _ _ _ _ (by omega), U32Vec.get!_set!_ne _ _ _ _ (by omega),
      U32Vec.get!_set!_self _ _ _ (by omega)]
  · rw [U32Vec.get!_set!_self _ _ _ (by simp; omega)]

theorem setReason_reads (a : Arena) (dst : Ref) (h : 4 * dst.toNat < a.words.size) :
    (a.setReason dst false).words.size = a.words.size ∧
    (∀ j, j ≠ 4 * dst.toNat → (a.setReason dst false).words.get! j = a.words.get! j) ∧
    (a.setReason dst false).word0 dst = a.word0 dst &&& ~~~ClauseHeader.reasonBit := by
  simp only [Arena.setReason, Arena.setFlag, Arena.setWord0, Arena.word0, Arena.base, Bool.false_eq_true, ite_false]
  refine ⟨by simp, fun j h1 => U32Vec.get!_set!_ne _ _ _ _ (by omega), U32Vec.get!_set!_self _ _ _ h⟩

theorem flags_clear_shrunken (w : UInt32) :
    ((w &&& ~~~ClauseHeader.shrunkenBit) &&& ClauseHeader.redundantBit != 0) = (w &&& ClauseHeader.redundantBit != 0) ∧
    ((w &&& ~~~ClauseHeader.shrunkenBit) &&& ClauseHeader.garbageBit != 0) = (w &&& ClauseHeader.garbageBit != 0) ∧
    ((w &&& ~~~ClauseHeader.shrunkenBit) &&& ClauseHeader.shrunkenBit != 0) = false ∧
    ((w &&& ~~~ClauseHeader.shrunkenBit) &&& ClauseHeader.reasonBit != 0) = (w &&& ClauseHeader.reasonBit != 0) ∧
    (((w &&& ~~~ClauseHeader.shrunkenBit) &&& ~~~ClauseHeader.reasonBit) &&& ClauseHeader.redundantBit != 0) =
      (w &&& ClauseHeader.redundantBit != 0) ∧
    (((w &&& ~~~ClauseHeader.shrunkenBit) &&& ~~~ClauseHeader.reasonBit) &&& ClauseHeader.garbageBit != 0) =
      (w &&& ClauseHeader.garbageBit != 0) ∧
    (((w &&& ~~~ClauseHeader.shrunkenBit) &&& ~~~ClauseHeader.reasonBit) &&& ClauseHeader.shrunkenBit != 0) = false := by
  simp only [ClauseHeader.shrunkenBit, ClauseHeader.redundantBit, ClauseHeader.garbageBit, ClauseHeader.reasonBit]
  have k : ∀ (x y : UInt32), (x = 0 ↔ y = 0) → (x != 0) = (y != 0) := by
    intro x y h; cases h1 : (x != 0) <;> cases h2 : (y != 0) <;> simp_all
  refine ⟨k _ _ (by constructor <;> intro h <;> bv_decide), k _ _ (by constructor <;> intro h <;> bv_decide), ?_,
    k _ _ (by constructor <;> intro h <;> bv_decide), k _ _ (by constructor <;> intro h <;> bv_decide),
    k _ _ (by constructor <;> intro h <;> bv_decide), ?_⟩
  · have : (w &&& ~~~((1 : UInt32) <<< 23)) &&& ((1 : UInt32) <<< 23) = 0 := by bv_decide
    rw [this]; rfl
  · have : ((w &&& ~~~((1 : UInt32) <<< 23)) &&& ~~~((1 : UInt32) <<< 21)) &&& ((1 : UInt32) <<< 23) = 0 := by
      bv_decide
    rw [this]; rfl

theorem asg_frame_trans {t s w : Asg} (h1 : t = { s with aReason := t.aReason, aBits := t.aBits })
    (h2 : s = { w with aReason := s.aReason, aBits := s.aBits }) :
    t = { w with aReason := t.aReason, aBits := t.aBits } := by
  rw [h1] at *; rw [h2]

theorem moveAsg_frame (s : Solver) (f : Lit) (y : UInt32) (b : Bool) :
    moveAsg s f y b = { s.asg with aReason := (moveAsg s f y b).aReason, aBits := (moveAsg s f y b).aBits } := by
  unfold moveAsg; split <;> rfl

theorem moveAsg_abit {s t : Solver} {f : Lit} {y : UInt32} {binary : Bool} (h : t.asg = moveAsg s f y binary)
    (hfb : (IDX f).toNat < s.asg.aBits.size) (i : UInt32) (b : UInt8) (hb : AnaBit b) : t.abit i b = s.abit i b := by
  unfold abit abits
  rw [h]; unfold moveAsg
  cases binary
  · rfl
  · simp only [ite_true]
    rw [ByteArray.get!_set!]
    split
    · rename_i hc
      rw [abit_or_binary (s.abits (IDX f)) b hb]
      unfold abits; rw [hc.1]
    · rfl

theorem lvl_pos_of_kept {w : Solver} {x : Lit} (hT : w.rootT x = false) (hv : vTrue (w.value x) = true) :
    0 < w.lvl x := by
  unfold rootT at hT; rw [hv] at hT
  simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hT
  unfold lvl; unfold level' at hT
  apply Nat.pos_of_ne_zero; intro e; apply hT; exact UInt32.toNat_inj.mp (by simpa using e)

theorem isTrue_of_vTrue {w : Solver} {x : Lit} (h : vTrue (w.value x) = true) : w.IsTrue x :=
  (isTrue_iff_vTrue w x).mpr h

theorem isFalse_of_vFalse {w : Solver} {x : Lit} (h : vFalse (w.value x) = true) : w.IsFalse x :=
  (isFalse_iff_vFalse w x).mpr h

theorem filt_sub {w : Solver} {o : Ref} {x : Lit} (h : x ∈ filt w o) : x ∈ w.clauseL o := by
  unfold filt at h; exact (List.mem_filter.mp h).1

theorem filt_valid {w : Solver} {start : Ref} {Q : List Ref} (hp : SwPre w start Q) {o : Ref} (ho : o ∈ Q)
    (hg : w.arena.garbage o = false) {x : Lit} (h : x ∈ filt w o) : w.ValidLit x :=
  (hp.live o ho hg).1 x (filt_sub h)

theorem stripS_arena (t : Solver) (A : Arena) : stripS { t with arena := A } = stripS t := rfl
theorem stripS_arena_asg (t : Solver) (A : Arena) (a : Asg) : stripS { t with arena := A, asg := a } = stripS t := rfl

/-- One step of the clause loop of the sweep. -/
theorem sweepClause_spec {w : Solver} {start : Ref} {Q : List Ref} {s : Solver} {st : SweepState} {src : Ref}
    {rest D N : List Ref} (hp : SwPre w start Q) (hI : SwI w start Q s st src (src :: rest) D N) :
    (s.sweepClause start st src).1.notPorted = true ∨
    ∃ N', SwI w start Q (s.sweepClause start st src).1 (s.sweepClause start st src).2 (w.arena.nextClause src)
      rest (D ++ [src]) N' := by
  obtain ⟨hlt, hsh, hnext, hrest, e0, e2, en⟩ := hI.head
  unfold sweepClause
  by_cases hg : s.arena.garbage src = true
  · rw [if_pos hg]; exact Or.inr ⟨N, sweep_garbage hp hI hg⟩
  rw [if_neg hg]
  dsimp only
  have hgA : w.arena.garbage src = false := by
    unfold garbage at *; rw [← flag_eq_of_word0 e0]; simpa using hg
  have ph := sweep_lits_phase hp hI hgA
  generalize sweepLits s (litPos src 0) (s.arena.size src).toNat
    { words := (s.arena.copyWord0 st.dst src).words, qpos := litPos st.dst 0 } 0 = r at ph ⊢
  obtain ⟨sat, L⟩ := r
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := ph
  dsimp only at p1 p2 p3 p4 p5 p6 p7 p8 ⊢
  have hd1 := hI.dst1
  have hd2 := hI.dst2
  have hwsz := hI.wsize
  have hm4 := hp.lay.mult4
  have hle := LayoutTo.le hrest
  have hwp := wardsOfClause_pos (w.arena.size src).toNat
  -- the arena after the literal phase
  have hlo : EqOn ({ words := L.words } : Arena) s.arena 0 (4 * st.dst.toNat) := by
    intro j _ hj; exact p5 j (by omega) (Or.inl (by unfold litPos base; omega))
  have hhi : EqOn ({ words := L.words } : Arena) s.arena (4 * (w.arena.nextClause src).toNat) s.arena.words.size := by
    intro j hj _; exact p5 j (by omega) (Or.inr (by omega))
  have hsz : L.words.size = s.arena.words.size := by rw [p1, hwsz]
  cases sat with
  | false =>
    have hc : ((!false) = true) = True := by simp
    simp only [hc, ite_true]
    right
    refine ⟨N, sweep_sat_inv hp hI hgA (p7 rfl) ?_ ?_ ?_ ?_ ?_ ?_⟩
    · split <;> exact hsz
    · split <;> exact hlo
    · split <;> exact hhi
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
  | true =>
    have hc : ((!true) = true) = False := by simp
    simp only [hc, ite_false]
    obtain ⟨q1, q2, q3, q4⟩ := p8 rfl
    have hns : L.qpos - litPos st.dst 0 = (filt w src).length := by rw [q2]; omega
    rw [hns]
    have hsrcQ : src ∈ Q := by rw [hI.qsplit]; simp
    have hrbit : ({ s with arena := { words := L.words } } : Solver).arena.reason st.dst = w.arena.reason src := by
      show Arena.flag ⟨L.words⟩ st.dst _ = _
      unfold Arena.flag Arena.word0 Arena.base; rw [p6]; rfl
    have hnoR : w.arena.reason src = false → NoReason w start src := by
      intro hr l ht hl hb hd hs e
      have := hp.rb l ht hl hb hd hs; rw [e, hr] at this; simp at this
    by_cases h2 : (filt w src).length = 2
    · rw [if_pos (by simp [h2])]
      obtain ⟨x, y, hK⟩ : ∃ x y, filt w src = [x, y] := by
        match hf : filt w src, h2 with
        | [x, y], _ => exact ⟨x, y, rfl⟩
      have hxv := filt_valid hp hsrcQ hgA (x := x) (by rw [hK]; simp)
      have hyv := filt_valid hp hsrcQ hgA (x := y) (by rw [hK]; simp)
      obtain ⟨a0, a1, a2, a3, a4⟩ := q4
      rw [hK] at a1 a2 a3 a4
      have hmf : L.mfirst = x := by rw [a1]; rfl
      have hms : L.msecond = y := by rw [a2]; rfl
      obtain ⟨sc, c1, c2, c3, c4, c5, c6, c7⟩ := sweepBinary_shape ({ s with arena := { words := L.words } } : Solver) st.dst src L
      rw [hmf, hms] at c5
      have hwat : sc.watches = (s.watchBinary x y).watches := c5.trans (watchBinary_watches rfl x y)
      have hfr : stripS sc = stripS s := c1.trans rfl
      have hasc : sc.asg = s.asg := c3
      rcases c7 with ⟨hr, e⟩ | ⟨hr, hgd, hoth, e⟩ | e
      · rw [e]; right
        refine ⟨N, sweep_bin_inv hp hI hgA hK hxv hyv (by rw [c2]; exact hsz) (by rw [c2]; exact hlo)
          (by rw [c2]; exact hhi) hwat (by rw [hasc]; exact hI.asg) (by rw [hasc]; exact ⟨rfl, rfl⟩)
          (fun i b _ => by unfold abit abits; rw [hasc]) (Or.inl ⟨fun l => ?_, hnoR (by rw [← hrbit]; exact hr)⟩) hfr⟩
        simp [reasonOf, reasonIdx, binOf, isBinaryReason, abit, abits, hasc]
      · rw [e]; right
        have hvars : s.vars = w.vars := by have := congrArg Solver.vars hI.frame; exact this
        unfold reasonMoves at hgd
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hgd
        obtain ⟨⟨⟨hfne, hfv⟩, hfb⟩, hgr⟩ := hgd
        obtain ⟨hfK, hfT⟩ := a3 hfne
        obtain ⟨hoK, hoF⟩ := a4 hoth
        have hfv' : (IDX L.forced).toNat < sc.vars.toNat := UInt32.lt_iff_toNat_lt.mp hfv
        rw [c4, hvars] at hfv'
        have hbR : (IDX L.forced).toNat < sc.asg.aReason.size := by rw [hasc, hI.rsz.1]; have := hp.rsize.1; omega
        have hbB : (IDX L.forced).toNat < sc.asg.aBits.size := by rw [hasc, hI.rsz.2]; have := hp.rsize.2; omega
        have hmr := moveAsg_reads (s := sc) (t := { sc with asg := moveAsg sc L.forced L.other true })
          (f := L.forced) (y := L.other) (binary := true) rfl hbR hbB
        have hscR : ∀ l, sc.reasonOf l = s.reasonOf l ∧ sc.binOf l = s.binOf l := by
          intro l; simp [reasonOf, reasonIdx, binOf, isBinaryReason, abit, abits, hasc]
        have hft : w.IsTrue L.forced := isTrue_of_vTrue hfT
        have hfl : 0 < w.lvl L.forced := lvl_pos_of_kept (q1 _ (filt_sub (by rw [hK]; exact hfK))) hfT
        have hof : w.IsFalse L.other := isFalse_of_vFalse hoF
        have hfo : L.forced ≠ L.other := by
          intro e; rw [e] at hft; exact (hp.core.valCons _).2 ⟨hft, hof⟩
        have hwat' : ({ sc with asg := moveAsg sc L.forced L.other true } : Solver).watches =
          (s.watchBinary x y).watches := hwat
        have hBW : ∀ a b, (a = x ∧ b = y) ∨ (a = y ∧ b = x) →
            ({ sc with asg := moveAsg sc L.forced L.other true } : Solver).BinWatched a b := by
          obtain ⟨bx1, bx2⟩ := validLit_bounds hp.watchesSize hp.varsBound hxv
          obtain ⟨by1, by2⟩ := validLit_bounds hp.watchesSize hp.varsBound hyv
          obtain ⟨_, wb2, _⟩ := watchBinary_entries s x y (by rw [hI.wsz]; omega) (by rw [hI.wsz]; omega) bx2 by2 hI.words
          intro a b hab
          unfold BinWatched entries watchesOf; rw [hwat']
          have := wb2 a; unfold entries watchesOf at this; rw [this]
          rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        refine ⟨N, sweep_bin_inv hp hI hgA hK hxv hyv (by rw [c2]; exact hsz) (by rw [c2]; exact hlo)
          (by rw [c2]; exact hhi) hwat ?_ ?_ ?_ (Or.inr ⟨L.forced, hft, hfl, by rw [← (hscR _).1]; exact hgr,
            by rw [← (hscR _).2]; exact hfb, fun l hl hne => ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩) hfr⟩
        · show moveAsg sc L.forced L.other true = _
          exact asg_frame_trans (moveAsg_frame sc L.forced L.other true) (by rw [hasc]; exact hI.asg)
        · rw [(hmr L.forced).2.2.2.1, (hmr L.forced).2.2.2.2, hasc]; exact ⟨rfl, rfl⟩
        · intro i b hb
          rw [moveAsg_abit (s := sc) (t := { sc with asg := moveAsg sc L.forced L.other true })
            (f := L.forced) (y := L.other) (binary := true) rfl hbB i b hb]
          unfold abit abits; rw [hasc]
        · have hidx := idx_ne_of_true hp.core hl hft hne
          rw [(hmr l).1, (hmr l).2.1, if_neg hidx, if_neg hidx]; exact hscR l
        · rw [(hmr _).2.1, if_pos rfl]; rfl
        · rw [(hmr _).1, if_pos rfl]
          apply hBW
          simp at hfK hoK
          rcases hfK with h1 | h1 <;> rcases hoK with h2 | h2
          · exact absurd (h1.trans h2.symm) hfo
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd (h1.trans h2.symm) hfo
        · rw [(hmr _).1, if_pos rfl]; exact filt_sub (by rw [hK]; exact hoK)
        · rw [(hmr _).1, if_pos rfl]; exact Ne.symm hfo
      · exact Or.inl (by rw [e])
    · rw [if_neg (by simp [h2])]
      have hvars : s.vars = w.vars := by have := congrArg Solver.vars hI.frame; exact this
      obtain ⟨a0, a1, a2, a3, a4⟩ := q4
      have hdq : 4 * st.dst.toNat + 2 < L.words.size := by
        have := wardsOfClause_pos (w.arena.size src).toNat; rw [p1]; omega
      have hshape := sweepLarge_shape ({ s with arena := { words := L.words } } : Solver) st.dst src
        (filt w src).length L st
      generalize (({ s with arena := { words := L.words } } : Solver).sweepLarge st.dst src (filt w src).length L st)
        = R at hshape ⊢
      obtain ⟨R1, st'⟩ := R
      dsimp only at hshape ⊢
      rcases hshape with e | ⟨h3, hst, hcases⟩
      · exact Or.inl e
      obtain ⟨l1, l2, l3, l4, l5⟩ := largeArena_reads ⟨L.words⟩ st.dst (filt w src).length hdq
      have hKlt : (filt w src).length < 2 ^ 32 := by
        have : (filt w src).length ≤ (w.arena.size src).toNat := by
          unfold filt clauseL; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
        have := (w.arena.size src).toNat_lt; omega
      have hsz' : ((largeArena ⟨L.words⟩ st.dst (filt w src).length).size st.dst).toNat = (filt w src).length := by
        rw [l4, UInt32.toNat_ofNat_of_lt' hKlt]
      have hw0 : (largeArena ⟨L.words⟩ st.dst (filt w src).length).word0 st.dst =
          w.arena.word0 src &&& ~~~ClauseHeader.shrunkenBit := by
        rw [l3]; show L.words.get! (4 * st.dst.toNat) &&& _ = _; rw [p6]
      obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := flags_clear_shrunken (w.arena.word0 src)
      have hlitL : ∀ k, k < (filt w src).length →
          (largeArena ⟨L.words⟩ st.dst (filt w src).length).lit st.dst k = (filt w src).getD k 0 := by
        intro k hk
        unfold Arena.lit Arena.litPos Arena.base
        rw [l2 _ (by omega) (by omega) (by omega)]
        have := q3 k hk; unfold litPos base at this; exact this
      have hLlo : EqOn (largeArena ⟨L.words⟩ st.dst (filt w src).length) s.arena 0 (4 * st.dst.toNat) := by
        intro j h1 h2; rw [l2 j (by omega) (by omega) (by omega)]; exact hlo j h1 h2
      have hLhi : EqOn (largeArena ⟨L.words⟩ st.dst (filt w src).length) s.arena
          (4 * (w.arena.nextClause src).toNat) s.arena.words.size := by
        intro j h1 h2; rw [l2 j (by omega) (by omega) (by omega)]; exact hhi j h1 h2
      rcases hcases with (⟨hr, e⟩ | ⟨hr, hgd, e⟩) | e
      · -- not a reason
        right
        have ka : R1.arena = largeArena ⟨L.words⟩ st.dst (filt w src).length := by rw [e]
        have kasg : R1.asg = s.asg := by rw [e]
        have kw : R1.watches = s.watches := by rw [e]
        have kfr : stripS R1 = stripS s := by rw [e, stripS_arena, stripS_arena]
        have hrr : (largeArena ⟨L.words⟩ st.dst (filt w src).length).reason st.dst = w.arena.reason src := by
          unfold Arena.reason Arena.flag; rw [hw0, f4]
        refine ⟨N ++ [st.dst], sweep_large_inv hp hI hgA h3 (by rw [ka, l1]; exact hsz) (by rw [ka]; exact hLlo)
          (by rw [ka]; exact hLhi) ?_ ?_ ?_ (by rw [ka]; exact hsz') (by rw [ka]; exact l5)
          (by rw [ka]; exact hlitL) hst kw (by rw [kasg]; exact hI.asg) (by rw [kasg]; exact ⟨rfl, rfl⟩)
          (fun _ _ _ => by unfold abit abits; rw [kasg])
          (Or.inl ⟨fun _ => by simp [reasonOf, reasonIdx, binOf, isBinaryReason, abit, abits, kasg],
            hnoR (by rw [← hrr]; exact hr)⟩) kfr⟩
        · rw [ka]; unfold Arena.redundant Arena.flag; rw [hw0, f1]
        · rw [ka]; unfold Arena.garbage Arena.flag; rw [hw0, f2]; exact hgA
        · rw [ka]; unfold Arena.shrunken Arena.flag; rw [hw0, f3]
      · -- a reason clause
        right
        unfold reasonMoves at hgd
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hgd
        obtain ⟨⟨⟨hfne, hfv⟩, hfb⟩, hgr⟩ := hgd
        obtain ⟨hfK, hfT⟩ := a3 hfne
        have hfv' : (IDX L.forced).toNat < w.vars.toNat := by
          have := UInt32.lt_iff_toNat_lt.mp hfv; rw [← hvars]; exact this
        have hbR : (IDX L.forced).toNat < s.asg.aReason.size := by rw [hI.rsz.1]; have := hp.rsize.1; omega
        have hbB : (IDX L.forced).toNat < s.asg.aBits.size := by rw [hI.rsz.2]; have := hp.rsize.2; omega
        have hft : w.IsTrue L.forced := isTrue_of_vTrue hfT
        have hfl : 0 < w.lvl L.forced := lvl_pos_of_kept (q1 _ (filt_sub hfK)) hfT
        have hd4 : 4 * st.dst.toNat < (largeArena ⟨L.words⟩ st.dst (filt w src).length).words.size := by
          rw [l1]; show 4 * st.dst.toNat < L.words.size; omega
        obtain ⟨r1, r2, r3⟩ := setReason_reads (largeArena ⟨L.words⟩ st.dst (filt w src).length) st.dst hd4
        have hA3 : ∀ j, j ≠ 4 * st.dst.toNat → j ≠ 4 * st.dst.toNat + 1 → j ≠ 4 * st.dst.toNat + 2 →
            ((largeArena ⟨L.words⟩ st.dst (filt w src).length).setReason st.dst false).words.get! j = L.words.get! j := by
          intro j h1 h2 h3; rw [r2 j h1, l2 j h1 h2 h3]
        have hw3 : ((largeArena ⟨L.words⟩ st.dst (filt w src).length).setReason st.dst false).word0 st.dst =
            (w.arena.word0 src &&& ~~~ClauseHeader.shrunkenBit) &&& ~~~ClauseHeader.reasonBit := by rw [r3, hw0]
        have ka : R1.arena = (largeArena ⟨L.words⟩ st.dst (filt w src).length).setReason st.dst false := by rw [e]
        have kw : R1.watches = s.watches := by rw [e]
        have kfr : stripS R1 = stripS s := by rw [e, stripS_arena_asg, stripS_arena]
        have hs1R : ∀ l, ({ s with arena := ⟨L.words⟩ } : Solver).reasonOf l = s.reasonOf l ∧
            ({ s with arena := ⟨L.words⟩ } : Solver).binOf l = s.binOf l := fun _ => ⟨rfl, rfl⟩
        -- the assignment after the update
        have key : R1.asg = { w.asg with aReason := R1.asg.aReason, aBits := R1.asg.aBits } ∧
            R1.asg.aReason.size = s.asg.aReason.size ∧ R1.asg.aBits.size = s.asg.aBits.size ∧
            (∀ i b, AnaBit b → R1.abit i b = s.abit i b) ∧
            R1.reasonOf L.forced = st.dst ∧ R1.binOf L.forced = false ∧
            (∀ l, IDX l ≠ IDX L.forced → R1.reasonOf l = s.reasonOf l ∧ R1.binOf l = s.binOf l) := by
          by_cases hif : (({ s with arena := ⟨L.words⟩ } : Solver).reasonIdx (IDX L.forced) != st.dst) = true
          · rw [if_pos hif] at e
            have hR1 : R1.asg = moveAsg ({ s with arena := ⟨L.words⟩ } : Solver) L.forced st.dst false := by rw [e]
            have hmr := moveAsg_reads (f := L.forced) (y := st.dst) (binary := false) hR1 hbR hbB
            refine ⟨?_, (hmr L.forced).2.2.2.1, (hmr L.forced).2.2.2.2, fun i b hb => ?_, ?_, ?_, fun l hl => ?_⟩
            · rw [hR1]; exact asg_frame_trans (moveAsg_frame _ _ _ _) hI.asg
            · exact moveAsg_abit hR1 hbB i b hb
            · rw [(hmr _).1, if_pos rfl]
            · rw [(hmr _).2.1, if_pos rfl]; exact hfb
            · rw [(hmr l).1, (hmr l).2.1, if_neg hl, if_neg hl]; exact ⟨rfl, rfl⟩
          · rw [if_neg hif] at e
            have hR1 : R1.asg = s.asg := by rw [e]
            have hrd : s.reasonIdx (IDX L.forced) = st.dst := by
              have := hif; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this; exact this
            refine ⟨by rw [hR1]; exact hI.asg, by rw [hR1], by rw [hR1], fun i b _ => by unfold abit abits; rw [hR1],
              ?_, ?_, fun l _ => ?_⟩
            · unfold reasonOf reasonIdx at *; rw [hR1]; exact hrd
            · unfold binOf isBinaryReason abit abits at *; rw [hR1]; exact hfb
            · simp [reasonOf, reasonIdx, binOf, isBinaryReason, abit, abits, hR1]
        obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
        have hlitL3 : ∀ k, k < (filt w src).length →
            ((largeArena ⟨L.words⟩ st.dst (filt w src).length).setReason st.dst false).lit st.dst k =
              (filt w src).getD k 0 := by
          intro k hk
          unfold Arena.lit Arena.litPos Arena.base
          rw [hA3 _ (by omega) (by omega) (by omega)]
          have := q3 k hk; unfold litPos base at this; exact this
        have hsz3 : ((((largeArena ⟨L.words⟩ st.dst (filt w src).length).setReason st.dst false).size st.dst).toNat) =
            (filt w src).length := by
          unfold Arena.size Arena.base; rw [r2 _ (by omega)]; exact hsz'
        have hsea3 : ((largeArena ⟨L.words⟩ st.dst (filt w src).length).setReason st.dst false).searched st.dst = 2 := by
          unfold Arena.searched Arena.base; rw [r2 _ (by omega)]; exact l5
        refine ⟨N ++ [st.dst], sweep_large_inv hp hI hgA h3 (by rw [ka, r1, l1]; exact hsz) ?_ ?_ ?_ ?_ ?_
          (by rw [ka]; exact hsz3) (by rw [ka]; exact hsea3) (by rw [ka]; exact hlitL3) hst kw k1 ⟨k2, k3⟩ k4
          (Or.inr ⟨L.forced, hft, hfl, hgr, hfb, fun l hl hne => k7 l (idx_ne_of_true hp.core hl hft hne),
            Or.inl ⟨k6, st.dst, by simp, k5, by rw [ka]; exact litsL_of_lits hsz3 hlitL3⟩⟩) kfr⟩
        · rw [ka]; intro j h1 h2; rw [hA3 j (by omega) (by omega) (by omega)]; exact hlo j h1 h2
        · rw [ka]; intro j h1 h2; rw [hA3 j (by omega) (by omega) (by omega)]; exact hhi j h1 h2
        · rw [ka]; unfold Arena.redundant Arena.flag; rw [hw3, f5]
        · rw [ka]; unfold Arena.garbage Arena.flag; rw [hw3, f6]; exact hgA
        · rw [ka]; unfold Arena.shrunken Arena.flag; rw [hw3, f7]
      · exact Or.inl e

/-! ### The clause loop -/

theorem sweepClause_np (s : Solver) (first : Ref) (st : SweepState) (src : Ref) (h : s.notPorted = true) :
    (s.sweepClause first st src).1.notPorted = true := by
  unfold sweepClause
  split
  · exact h
  dsimp only
  generalize sweepLits s (litPos src 0) (s.arena.size src).toNat
    { words := (s.arena.copyWord0 st.dst src).words, qpos := litPos st.dst 0 } 0 = r
  obtain ⟨sat, L⟩ := r
  cases sat
  · have hc : ((!false) = true) = True := by simp
    simp only [hc, ite_true]; split <;> exact h
  · have hc : ((!true) = true) = False := by simp
    simp only [hc, ite_false]
    split
    · obtain ⟨sc, _, _, _, _, _, c6, c7⟩ := sweepBinary_shape ({ s with arena := { words := L.words } } : Solver)
        st.dst src L
      rcases c7 with ⟨_, e⟩ | ⟨_, _, _, e⟩ | e
      · rw [e, c6]; exact h
      · rw [e]; exact c6.trans h
      · exact e
    · rcases sweepLarge_shape ({ s with arena := { words := L.words } } : Solver) st.dst src
        (L.qpos - litPos st.dst 0) L st with e | ⟨_, _, (⟨_, e⟩ | ⟨_, _, e⟩) | e⟩
      · exact e
      · rw [e]; exact h
      · rw [e]; exact h
      · exact e

theorem sweepLoop_np (first endRef : Ref) : ∀ (fuel : Nat) (s : Solver) (st : SweepState) (src : Ref),
    s.notPorted = true → (s.sweepLoop first endRef st src fuel).1.notPorted = true := by
  intro fuel
  induction fuel with
  | zero => intro s st src h; exact h
  | succ n ih =>
    intro s st src h
    unfold sweepLoop
    split
    · exact h
    · exact ih _ _ _ (sweepClause_np s first st src h)

theorem sweepLoop_spec {w : Solver} {start : Ref} {Q : List Ref} (hp : SwPre w start Q) :
    ∀ (fuel : Nat) (s : Solver) (st : SweepState) (src : Ref) (rest D N : List Ref), rest.length ≤ fuel →
    SwI w start Q s st src rest D N →
    (s.sweepLoop start (UInt32.ofNat w.arena.sizeWards) st src fuel).1.notPorted = true ∨
    ∃ src' N', SwI w start Q (s.sweepLoop start (UInt32.ofNat w.arena.sizeWards) st src fuel).1
      (s.sweepLoop start (UInt32.ofNat w.arena.sizeWards) st src fuel).2 src' [] Q N' := by
  have hb := hp.lay.bound
  have hE : (UInt32.ofNat w.arena.sizeWards).toNat = w.arena.sizeWards := by
    rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
  intro fuel
  induction fuel with
  | zero =>
    intro s st src rest D N hf hI
    have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    have hq : D = Q := by have := hI.qsplit; simp at this; exact this.symm
    subst hq
    right; exact ⟨src, N, hI⟩
  | succ n ih =>
    intro s st src rest D N hf hI
    unfold sweepLoop
    cases rest with
    | nil =>
      have hsrc : src.toNat = w.arena.sizeWards := hI.lrest
      rw [if_pos (by rw [ge_iff_le, UInt32.le_iff_toNat_le, hE]; omega)]
      have hq : D = Q := by have := hI.qsplit; simp at this; exact this.symm
      subst hq
      right; exact ⟨src, N, hI⟩
    | cons x rest' =>
      obtain ⟨rfl, hlt, _⟩ := hI.lrest
      rw [if_neg (by rw [ge_iff_le, UInt32.le_iff_toNat_le, hE]; omega)]
      dsimp only
      obtain ⟨_, _, _, _, _, _, en⟩ := hI.head
      rw [en]
      rcases sweepClause_spec hp hI with h | ⟨N', h⟩
      · left; exact sweepLoop_np _ _ _ _ _ _ h
      · exact ih _ _ _ rest' (D ++ [x]) N' (by simp at hf; omega) h

/-! ### The whole sweep -/

/-- The solver without the fields changed by the sweep. -/
def stripT (s : Solver) : Solver := { stripS s with firstReducible := 0, lastIrredundant := 0, lastLearned := #[] }

theorem stripT_of_stripS {s t : Solver} (h : stripS t = stripS s) : stripT t = stripT s := by
  unfold stripT; rw [h]

/-- The state after the sweep. -/
structure SwOut (w : Solver) (start : Ref) (Q : List Ref) (t : Solver) (N : List Ref) : Prop where
  lay : t.arena.Layout
  chain : ∃ P, LayoutTo w.arena 0 start.toNat P ∧ w.refsL = P ++ Q ∧ t.refsL = P ++ N ∧
    LayoutTo t.arena 0 start.toNat P
  pre : EqOn t.arena w.arena 0 (4 * start.toNat)
  lnew : LayoutTo t.arena start t.arena.sizeWards N
  newCl : ∀ n ∈ N, ∃ o ∈ Q, w.arena.garbage o = false ∧ t.arena.litsL n = filt w o ∧
    t.arena.redundant n = w.arena.redundant o ∧ t.arena.garbage n = false ∧ t.arena.searched n = 2 ∧
    3 ≤ (t.arena.size n).toNat
  oldCl : ∀ o ∈ Q, w.arena.garbage o = false → SatW w o ∨
    (∃ a b, filt w o = [a, b] ∧ t.BinWatched a b ∧ t.BinWatched b a) ∨
    (∃ n ∈ N, t.arena.litsL n = filt w o ∧ t.arena.redundant n = w.arena.redundant o)
  words : ∀ l, WordsOK (t.watchesOf l).data.toList
  ent : ∀ l, ∃ E : List Lit, t.entries l = w.entries l ++ E.map WEntry.bin
  binNew : ∀ a b, t.BinWatched a b → w.BinWatched a b ∨
    (t.BinWatched b a ∧ ∃ o ∈ Q, w.arena.garbage o = false ∧ (filt w o = [a, b] ∨ filt w o = [b, a]))
  wsz : t.watches.size = w.watches.size
  asg : t.asg = { w.asg with aReason := t.asg.aReason, aBits := t.asg.aBits }
  rsz : t.asg.aReason.size = w.asg.aReason.size ∧ t.asg.aBits.size = w.asg.aBits.size
  bits : ∀ i b, AnaBit b → t.abit i b = w.abit i b
  reasons : ∀ l, w.IsTrue l → 0 < w.lvl l → RS w start t [] N l
  frame : stripT t = stripT w

theorem sweep_init {w : Solver} {start : Ref} {Q : List Ref} (hp : SwPre w start Q) (st : SweepState)
    (hst : st.dst = start) : SwI w start Q w st start Q [] [] := by
  obtain ⟨P, hP, hR⟩ := hp.pre
  refine ⟨rfl, hp.lq, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, by rw [hst]; exact Nat.le_refl _,
    by rw [hst]; exact Nat.le_refl _, by rw [hst]; rfl,
    fun n hn => by simp at hn, fun o ho => by simp at ho, hp.words, fun l => ⟨[], by simp⟩,
    fun a b h => Or.inl h, rfl, rfl, ⟨rfl, rfl⟩, fun _ _ _ => rfl, fun l ht hl => ?_, rfl⟩
  unfold RS
  split
  · rename_i hc
    left
    refine ⟨?_, rfl, hc.1⟩
    have hlive := (reason_live hp.reasons ht hl hc.1 hc.2.1).1
    unfold refsL at hlive; rw [show w.arena.chain 0 w.arena.sizeWards = w.refsL from rfl, hR] at hlive
    rcases List.mem_append.mp hlive with h | h
    · exfalso
      have := (hP.mem_bounds _ h).2.1
      have := wardsOfClause_pos (w.arena.size (w.reasonOf l)).toNat
      have := hc.2.2; rw [UInt32.le_iff_toNat_le] at this; omega
    · exact h
  · exact ⟨rfl, rfl⟩

theorem sweepFinal_fields (r1 : Solver) (dst : Ref) (fr li : Option Ref) :
    let s3 := ((r1.updateFirstReducibleEnd dst fr).updateLastIrredundantEnd dst li).resetLastLearned
    s3.arena = r1.arena ∧ s3.asg = r1.asg ∧ s3.watches = r1.watches ∧ s3.notPorted = r1.notPorted ∧
      stripT s3 = stripT r1 := by
  intro s3
  have h1 : ∀ t : Solver, stripT (t.updateFirstReducibleEnd dst fr) = stripT t ∧
      (t.updateFirstReducibleEnd dst fr).arena = t.arena ∧ (t.updateFirstReducibleEnd dst fr).asg = t.asg ∧
      (t.updateFirstReducibleEnd dst fr).watches = t.watches ∧
      (t.updateFirstReducibleEnd dst fr).notPorted = t.notPorted := by
    intro t; unfold updateFirstReducibleEnd; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h2 : ∀ t : Solver, stripT (t.updateLastIrredundantEnd dst li) = stripT t ∧
      (t.updateLastIrredundantEnd dst li).arena = t.arena ∧ (t.updateLastIrredundantEnd dst li).asg = t.asg ∧
      (t.updateLastIrredundantEnd dst li).watches = t.watches ∧
      (t.updateLastIrredundantEnd dst li).notPorted = t.notPorted := by
    intro t; unfold updateLastIrredundantEnd; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 r1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2 (r1.updateFirstReducibleEnd dst fr)
  exact ⟨b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, (show stripT s3 = _ from rfl).trans (b1.trans a1)⟩

theorem sweep_spec {w : Solver} {start : Ref} {Q : List Ref} (hp : SwPre w start Q) :
    (w.sparseSweepGarbageClauses start).2.notPorted = true ∨
    ∃ N, SwOut w start Q (w.sparseSweepGarbageClauses start).2 N := by
  unfold sparseSweepGarbageClauses
  dsimp only
  have hlen := hp.lq.length_le
  have L := sweepLoop_spec hp w.arena.sizeWards w _ start Q [] [] (by omega) (sweep_init hp
    { dst := start, lastIrredundant := if start != 0 then
        (if w.lastIrredundant == INVALID_REF then none else some w.lastIrredundant) else none } rfl)
  generalize w.sweepLoop start (UInt32.ofNat w.arena.sizeWards)
    { dst := start, lastIrredundant := if start != 0 then
        (if w.lastIrredundant == INVALID_REF then none else some w.lastIrredundant) else none }
    start w.arena.sizeWards = R at L ⊢
  obtain ⟨r1, st⟩ := R
  dsimp only at L ⊢
  obtain ⟨f1, f2, f3, f4, f5⟩ := sweepFinal_fields r1 st.dst st.firstReducible st.lastIrredundant
  generalize ((r1.updateFirstReducibleEnd st.dst st.firstReducible).updateLastIrredundantEnd st.dst
    st.lastIrredundant).resetLastLearned = s3 at f1 f2 f3 f4 f5 ⊢
  rcases L with h | ⟨src', N, hI⟩
  · left; show s3.notPorted = true; rw [f4]; exact h
  right
  refine ⟨N, ?_⟩
  have hsrc : src'.toNat = w.arena.sizeWards := hI.lrest
  have hd1 := hI.dst1
  have hd2 := hI.dst2
  have hm4 := hp.lay.mult4
  have hbd := hp.lay.bound
  have hrs : r1.arena.words.size = 4 * w.arena.sizeWards := by rw [hI.wsize, hm4]
  generalize ht : ({ s3 with arena := { words := s3.arena.words.shrink (4 * st.dst.toNat) } } : Solver) = t
  have tA : t.arena.words = r1.arena.words.shrink (4 * st.dst.toNat) := by rw [← ht, f1]
  have tsz : t.arena.words.size = 4 * st.dst.toNat := by rw [tA, U32Vec.size_shrink]; omega
  have tsw : t.arena.sizeWards = st.dst.toNat := by unfold Arena.sizeWards; rw [tsz]; omega
  have tEq : EqOn t.arena r1.arena 0 (4 * st.dst.toNat) := by
    intro j _ hj; rw [tA, U32Vec.get!_shrink, if_pos hj]
  have tasg : t.asg = r1.asg := by rw [← ht]; exact f2
  have twat : t.watches = r1.watches := by rw [← ht]; exact f3
  have tfr : stripT t = stripT w := by
    rw [← ht, show stripT { s3 with arena := { words := s3.arena.words.shrink (4 * st.dst.toNat) } } = stripT s3
      from rfl, f5]
    exact stripT_of_stripS hI.frame
  obtain ⟨P, hP, hR⟩ := hp.pre
  have hP1 : LayoutTo r1.arena 0 start.toNat P := hP.congr (hI.pre.symm.mono (Nat.le_refl _) (Nat.le_refl _))
  have hPt : LayoutTo t.arena 0 start.toNat P := hP1.congr (tEq.symm.mono (Nat.le_refl _) (by omega))
  obtain ⟨n1, n2⟩ := newPart_congr hI.lnew (tEq.mono (Nat.zero_le _) (Nat.le_refl _))
  have hall : LayoutTo t.arena 0 t.arena.sizeWards (P ++ N) := by rw [tsw]; exact hPt.append n1
  have hch : t.arena.chain 0 t.arena.sizeWards = P ++ N := hall.chain_eq _ (by
    have := hall.length_le; simp at this ⊢; omega)
  have eE : ∀ l, t.entries l = r1.entries l := by intro l; simp [entries, watchesOf, twat]
  have eB : ∀ a b, t.BinWatched a b ↔ r1.BinWatched a b := by intro a b; simp [BinWatched, eE]
  have hlit : ∀ n ∈ N, t.arena.litsL n = r1.arena.litsL n := fun n hn => (n2 n hn).2.2.2
  have hbits' : ∀ i b, AnaBit b → t.abit i b = w.abit i b := by
    intro i b hb; rw [← hI.bits i b hb]; unfold abit abits; rw [tasg]
  refine ⟨⟨by rw [hch]; exact layoutFrom_iff.mpr hall, by rw [tsz, tsw], by rw [tsw]; omega⟩,
    ⟨P, hP, hR, hch, hPt⟩, fun j h1 h2 => by rw [tEq j h1 (by omega)]; exact hI.pre j h1 h2,
    by rw [tsw]; exact n1, ?_, ?_, fun l => by unfold watchesOf; rw [twat]; exact hI.words l,
    fun l => by rw [eE]; exact hI.ent l, fun a b h => ?_, by rw [twat]; exact hI.wsz,
    by rw [tasg]; exact hI.asg, by rw [tasg]; exact hI.rsz, hbits', fun l ht hl => (hI.reasons l ht hl).mono ⟨by simp [reasonOf, reasonIdx, tasg],
        by simp [binOf, isBinaryReason, abit, abits, tasg]⟩ (fun n hn => ⟨hn, hlit n hn⟩)
        (fun a b h => (eB a b).mpr h), tfr⟩
  · intro n hn
    obtain ⟨o, ho, h1, h2, h3, h4, h5, h6⟩ := hI.newCl n hn
    obtain ⟨m0, m1, m2, m3⟩ := n2 n hn
    refine ⟨o, ho, h1, by rw [m3, h2], ?_, ?_, by rw [m1, h5], by rw [m2]; exact h6⟩
    · unfold redundant; rw [flag_eq_of_word0 m0]; exact h3
    · unfold garbage; rw [flag_eq_of_word0 m0]; exact h4
  · intro o ho hgo
    rcases hI.oldCl o ho hgo with h | ⟨a, b, h1, h2, h3⟩ | ⟨n, hn, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, b, h1, (eB a b).mpr h2, (eB b a).mpr h3⟩)
    · refine Or.inr (Or.inr ⟨n, hn, by rw [hlit n hn, h1], ?_⟩)
      unfold redundant; rw [flag_eq_of_word0 (n2 n hn).1]; exact h2
  · rcases hI.binNew a b ((eB a b).mp h) with h' | ⟨hba, o, ho, h'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨(eB b a).mpr hba, o, ho, h'⟩

end Solver
end LeanKissat
