import LeanKissat.Proofs.RedCollect

/-!
# `reduce`: marking reasons, collecting candidates, marking garbage
-/

namespace LeanKissat
namespace Solver
open Arena

/-- The solver without arena, statistics and `first_reducible`. -/
def stripRF (s : Solver) : Solver := { s with arena := default, stats := default, firstReducible := 0 }

/-- Only header bits other than garbage/redundant/shrunken, statistics and `first_reducible` changed. -/
structure RF (t s : Solver) : Prop where
  strip : stripRF t = stripRF s
  arena : Arena.Same s.arena t.arena

theorem RF.refl (s : Solver) : RF s s := ⟨rfl, Arena.Same.refl _⟩

theorem RF.trans {a b c : Solver} (h1 : RF a b) (h2 : RF b c) : RF a c :=
  ⟨h1.strip.trans h2.strip, h2.arena.trans h1.arena⟩

theorem RF.af {t s : Solver} (h : RF t s) : AF t s := by
  have e : ∀ {α : Type} (g : Solver → α), (∀ x, g (stripRF x) = g x) → g t = g s := by
    intro α g hg; rw [← hg t, ← hg s, h.strip]
  refine ⟨e (fun x => x.asg.values) (fun _ => rfl), e (fun x => x.asg.trail) (fun _ => rfl),
    e (fun x => x.asg.aLevel) (fun _ => rfl), e (fun x => x.asg.aReason) (fun _ => rfl),
    e (fun x => x.asg.aBits.size) (fun _ => rfl), fun i => by rw [e (fun x => x.asg.aBits) (fun _ => rfl)],
    e (fun x => x.asg.unassigned) (fun _ => rfl), h.arena, e (fun x => x.watches) (fun _ => rfl),
    e (fun x => x.delayed) (fun _ => rfl), e (fun x => x.vars) (fun _ => rfl), e (fun x => x.level) (fun _ => rfl),
    e (fun x => x.frameTrail) (fun _ => rfl), e (fun x => x.propagate) (fun _ => rfl),
    e (fun x => x.options) (fun _ => rfl), e (fun x => x.importLit) (fun _ => rfl),
    e (fun x => x.inconsistent) (fun _ => rfl), e (fun x => x.conflictLit0) (fun _ => rfl),
    e (fun x => x.conflictLit1) (fun _ => rfl), e (fun x => x.watching) (fun _ => rfl),
    e (fun x => x.probing) (fun _ => rfl), e (fun x => x.importBits) (fun _ => rfl)⟩

theorem RF.fields {t s : Solver} (h : RF t s) : t.asg = s.asg ∧ t.clause = s.clause ∧ t.notPorted = s.notPorted ∧
    t.overflowed = s.overflowed ∧ t.outOfResources = s.outOfResources ∧ t.watches = s.watches ∧
    t.level = s.level ∧ t.propagate = s.propagate ∧ t.vars = s.vars := by
  have e : ∀ {α : Type} (g : Solver → α), (∀ x, g (stripRF x) = g x) → g t = g s := by
    intro α g hg; rw [← hg t, ← hg s, h.strip]
  exact ⟨e (fun x => x.asg) (fun _ => rfl), e (fun x => x.clause) (fun _ => rfl),
    e (fun x => x.notPorted) (fun _ => rfl), e (fun x => x.overflowed) (fun _ => rfl),
    e (fun x => x.outOfResources) (fun _ => rfl), e (fun x => x.watches) (fun _ => rfl),
    e (fun x => x.level) (fun _ => rfl), e (fun x => x.propagate) (fun _ => rfl), e (fun x => x.vars) (fun _ => rfl)⟩

theorem RF.searchInv {Φ : (Nat → Bool) → Prop} {t s : Solver} (h : RF t s) (hs : SearchInv Φ s) :
    SearchInv Φ t := by
  have hA := h.af
  obtain ⟨f1, f2, _, _, _, _, _, f8, _⟩ := h.fields
  have hflg := hA.flg
  refine ⟨hA.sinv hs.inv, fun c hc => ?_, fun i b hb => ?_, by rw [f2]; exact hs.clauseEmpty,
    fun e => hs.incons (by rw [← Flg.inconsistent hflg]; exact e), by rw [Flg.watching hflg]; exact hs.watching,
    by rw [Flg.options hflg]; exact hs.opts, hs.imp.flg hflg⟩
  · unfold InvS; rw [hA.invSAt, f8]; exact hs.invS c ((hA.inDB c).mp hc)
  · unfold abit abits; rw [f1]; exact hs.clean i b hb

theorem RF.flagged {t s : Solver} (h : RF t s) (hf : Flagged s) : Flagged t := by
  obtain ⟨_, _, f3, f4, f5, _⟩ := h.fields
  unfold Flagged at *; rw [f3, f4, f5]; exact hf

/-- `RF` up to `notPorted`. -/
def stripRFN (s : Solver) : Solver := { s with arena := default, stats := default, firstReducible := 0, notPorted := false }

structure RFN (t s : Solver) : Prop where
  strip : stripRFN t = stripRFN s
  arena : Arena.Same s.arena t.arena

theorem RFN.refl (s : Solver) : RFN s s := ⟨rfl, Arena.Same.refl _⟩

theorem flg_stripRFN (t : Solver) : Flg (stripRFN t) = Flg t := rfl

theorem RFN.trans {a b c : Solver} (h1 : RFN a b) (h2 : RFN b c) : RFN a c :=
  ⟨h1.strip.trans h2.strip, h2.arena.trans h1.arena⟩

theorem RF.rfn {t s : Solver} (h : RF t s) : RFN t s := by
  refine ⟨?_, h.arena⟩
  have := congrArg (fun x : Solver => { x with notPorted := false }) h.strip
  exact this

/-- Clearing `notPorted` turns `RFN` into `RF`. -/
theorem RFN.rf {t s : Solver} (h : RFN t s) : RF { t with notPorted := s.notPorted } s := by
  refine ⟨?_, h.arena⟩
  have := congrArg (fun x : Solver => { x with notPorted := s.notPorted }) h.strip
  exact this

theorem sfr_notPorted (t : Solver) (b : Bool) : SFr t { t with notPorted := b } := by sf_rfl

theorem RFN.searchInv {Φ : (Nat → Bool) → Prop} {t s : Solver} (h : RFN t s) (hs : SearchInv Φ s) :
    SearchInv Φ t :=
  (sfr_notPorted t s.notPorted).searchInv (h.rf.searchInv hs)

theorem RFN.irrMono {t s : Solver} (h : RFN t s) : IrrMono s t :=
  h.rf.af.irrMono.trans (sfr_notPorted t s.notPorted).irrMono

theorem RFN.asg {t s : Solver} (h : RFN t s) : t.asg = s.asg := by
  have := congrArg Solver.asg h.strip; exact this

/-! ### Marking reasons -/

theorem reasonBit_set (w : UInt32) (m : Bool) :
    ((if m then w ||| ClauseHeader.reasonBit else w &&& ~~~ClauseHeader.reasonBit) &&& ClauseHeader.reasonBit != 0)
      = m := by
  unfold ClauseHeader.reasonBit
  cases m
  · have : (w &&& ~~~((1 : UInt32) <<< 21)) &&& ((1 : UInt32) <<< 21) = 0 := by bv_k
    simp only [Bool.false_eq_true, ite_false, this]; decide
  · have : (w ||| ((1 : UInt32) <<< 21)) &&& ((1 : UInt32) <<< 21) = (1 : UInt32) <<< 21 := by bv_k
    simp only [ite_true, this]; decide

theorem setReason_reason (a : Arena) (h : a.Layout) {r x : Ref} (hr : r ∈ a.chain 0 a.sizeWards)
    (hx : x ∈ a.chain 0 a.sizeWards) (m : Bool) :
    (a.setReason r m).reason x = if x = r then m else a.reason x := by
  have hb := h.mem_bounds hr
  have hm := h.mult4
  have hw := wardsOfClause_pos (a.size r).toNat
  unfold reason flag setReason setFlag setWord0
  by_cases e : x = r
  · subst e
    rw [ite_eq_left rfl]
    show ((a.words.set! (base x) _).get! (base x) &&& _ != 0) = m
    rw [U32Vec.get!_set!_self _ _ _ (by unfold base; omega)]
    exact reasonBit_set _ m
  · rw [ite_eq_right e]
    show ((a.words.set! (base r) _).get! (base x) &&& _ != 0) = (a.word0 x &&& _ != 0)
    rw [U32Vec.get!_set!_ne _ _ _ _ ((header_ne h hr hx).2.2.2 (Ne.symm e))]
    rfl

/-- The reasons that `mark_reason_clauses` marks. -/
def MarkedR (s0 : Solver) (start : Ref) (l : Lit) : Prop :=
  0 < s0.lvl l ∧ s0.binOf l = false ∧ s0.reasonOf l ≠ DECISION_REASON ∧ start ≤ s0.reasonOf l

theorem markedR_chain {s0 : Solver} {Φ : (Nat → Bool) → Prop} (hs : SInv Φ s0) {start : Ref} {l : Lit}
    (hl : l ∈ s0.trailL) (hm : MarkedR s0 start l) : s0.reasonOf l ∈ s0.arena.chain 0 s0.arena.sizeWards :=
  (reason_live hs.reasons (hs.core.trailTrue l hl) hm.1 hm.2.1 hm.2.2.1).1

theorem markReasonLoop_spec {Φ : (Nat → Bool) → Prop} (start : Ref) (mark : Bool) (n : Nat) (s0 : Solver)
    (hs : SInv Φ s0) (hn : n ≤ s0.asg.trail.size) :
    ∀ s i, RFN s s0 → (∀ j l, j < i → s0.trailL[j]? = some l → MarkedR s0 start l →
      s.arena.reason (s0.reasonOf l) = mark) →
    RFN (markReasonLoop start mark n s i) s0 ∧
    ∀ j l, j < n → s0.trailL[j]? = some l → MarkedR s0 start l →
      (markReasonLoop start mark n s i).arena.reason (s0.reasonOf l) = mark := by
  intro s i
  induction s, i using markReasonLoop.induct start mark n with
  | case1 s i hi idx ref s' ih =>
    intro hR hP
    rw [markReasonLoop, ite_eq_left hi]
    dsimp only
    have ha := hR.asg
    have hlit : s0.trailL[i]? = some (s.asg.trail.get! i) := by
      rw [ha]; exact trailL_getElem? s0 i (by omega)
    have hlvl : s.levelIdx idx = s0.asg.aLevel.get! (IDX (s.asg.trail.get! i)).toNat := by
      show s.asg.aLevel.get! (IDX (s.asg.trail.get! i)).toNat = _; rw [ha]
    have hrf : s.reasonIdx idx = s0.reasonOf (s.asg.trail.get! i) := by
      show s.asg.aReason.get! (IDX (s.asg.trail.get! i)).toNat = s0.asg.aReason.get! (IDX (s.asg.trail.get! i)).toNat
      rw [ha]
    have hrf' : ref = s0.reasonOf (s.asg.trail.get! i) := hrf
    have hbf : s.isBinaryReason idx = s0.binOf (s.asg.trail.get! i) := by
      show (s.asg.aBits.get! (IDX (s.asg.trail.get! i)).toNat &&& _ != 0) =
        (s0.asg.aBits.get! (IDX (s.asg.trail.get! i)).toNat &&& _ != 0)
      rw [ha]
    -- the state after the step
    have hstep : RFN s' s0 ∧ ∀ j l, j < i + 1 → s0.trailL[j]? = some l → MarkedR s0 start l →
        s'.arena.reason (s0.reasonOf l) = mark := by
      simp only [s']
      split
      · rename_i hz
        refine ⟨⟨by rw [← hR.strip]; rfl, hR.arena⟩, fun j l hj hjl hm => ?_⟩
        by_cases e : j = i
        · subst e; rw [hlit] at hjl; cases hjl
          exfalso; have := hm.1; unfold lvl at this; rw [← hlvl] at this; simp at hz; rw [hz] at this
          simp at this
        · exact hP j l (by omega) hjl hm
      · split
        · rename_i _ hc
          refine ⟨hR, fun j l hj hjl hm => ?_⟩
          by_cases e : j = i
          · subst e; rw [hlit] at hjl; cases hjl
            exfalso
            obtain ⟨_, hb, hd, hst⟩ := hm
            rw [hbf, hrf'] at hc
            simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            rcases hc with (hc | hc) | hc
            · rw [hb] at hc; simp at hc
            · exact hd hc
            · exact absurd hst (by rw [UInt32.le_iff_toNat_le]; rw [UInt32.lt_iff_toNat_lt] at hc; omega)
          · exact hP j l (by omega) hjl hm
        · rename_i hz hc
          -- a genuine reason clause
          have hmi : MarkedR s0 start (s.asg.trail.get! i) := by
            rw [hbf, hrf'] at hc
            simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hc
            refine ⟨?_, by simpa using hc.1.1, hc.1.2, by rw [UInt32.le_iff_toNat_le]; rw [UInt32.lt_iff_toNat_lt] at hc; omega⟩
            unfold lvl; rw [← hlvl]
            apply Nat.pos_of_ne_zero; intro e; apply hz; simp only [beq_iff_eq]
            exact UInt32.toNat_inj.mp (by simpa using e)
          have hmem : s.asg.trail.get! i ∈ s0.trailL := List.mem_of_getElem? hlit
          have hch := markedR_chain hs hmem hmi
          have hlayS : s.arena.Layout := hR.arena.layout hs.layout
          have hchS : s.reasonIdx idx ∈ s.arena.chain 0 s.arena.sizeWards := by rw [hR.arena.chain, hrf]; exact hch
          refine ⟨⟨by rw [← hR.strip]; rfl, hR.arena.trans (setReason_same hlayS hchS mark)⟩,
            fun j l hj hjl hm => ?_⟩
          have hmemj : l ∈ s0.trailL := List.mem_of_getElem? hjl
          have hchj : s0.reasonOf l ∈ s.arena.chain 0 s.arena.sizeWards := by
            rw [hR.arena.chain]; exact markedR_chain hs hmemj hm
          show (s.arena.setReason (s.reasonIdx idx) mark).reason _ = mark
          rw [setReason_reason _ hlayS hchS hchj]
          split
          · rfl
          · rename_i hne
            by_cases e : j = i
            · subst e; rw [hlit] at hjl; cases hjl; exact absurd hrf.symm hne
            · exact hP j l (by omega) hjl hm
    exact ih hstep.1 hstep.2
  | case2 s i hi =>
    intro hR hP
    rw [markReasonLoop, ite_eq_right hi]
    exact ⟨hR, fun j l hj hjl hm => hP j l (by omega) hjl hm⟩

theorem markReasonClauses_spec {Φ : (Nat → Bool) → Prop} (s : Solver) (start : Ref) (mark : Bool)
    (hs : SInv Φ s) :
    RFN (s.markReasonClauses start mark) s ∧
    ∀ l, s.IsTrue l → MarkedR s start l → (s.markReasonClauses start mark).arena.reason (s.reasonOf l) = mark := by
  obtain ⟨h1, h2⟩ := markReasonLoop_spec start mark s.asg.trail.size s hs (Nat.le_refl _) s 0 (RFN.refl s)
    (fun j l hj => absurd hj (by omega))
  refine ⟨h1, fun l ht hm => ?_⟩
  rcases hs.core.trueOnTrail l ht with hl | hl
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hl
    have hb : j < s.trailL.length := (List.getElem?_eq_some_iff.mp hj).1
    exact h2 j l (by simpa [trailL] using hb) hj hm
  · have := hm.1; omega

/-! ### Collecting the candidates -/

theorem setUsed_reason (a : Arena) (h : a.Layout) {c x : Ref} (hc : c ∈ a.chain 0 a.sizeWards)
    (hx : x ∈ a.chain 0 a.sizeWards) (u : UInt32) : (a.setUsed c u).reason x = a.reason x := by
  have hb := h.mem_bounds hc
  have hm := h.mult4
  have hw := wardsOfClause_pos (a.size c).toNat
  unfold reason flag setUsed setWord0
  by_cases e : x = c
  · subst e
    show ((a.words.set! (base x) _).get! (base x) &&& _ != 0) = (a.word0 x &&& _ != 0)
    rw [U32Vec.get!_set!_self _ _ _ (by unfold base; omega)]
    have key : ∀ (w : UInt32), ((w &&& ((1 <<< ClauseHeader.usedShift) - 1)) |||
        ((u &&& MAX_USED) <<< ClauseHeader.usedShift)) &&& ClauseHeader.reasonBit = w &&& ClauseHeader.reasonBit := by
      intro w; simp only [ClauseHeader.usedShift, MAX_USED, ClauseHeader.reasonBit]; bv_k
    rw [key]
  · show ((a.words.set! (base c) _).get! (base x) &&& _ != 0) = (a.word0 x &&& _ != 0)
    rw [U32Vec.get!_set!_ne _ _ _ _ ((header_ne h hc hx).2.2.2 (Ne.symm e))]
    rfl

/-- The candidate loop of `collect_reducibles`. -/
theorem collectLoop_spec (refs : Array Ref) (tier1 tier2 : UInt32) (s0 : Solver) (hlay : s0.arena.Layout)
    (hrefs : ∀ x ∈ refs.toList, x ∈ s0.arena.chain 0 s0.arena.sizeWards) :
    ∀ s reds i, RF s s0 → (∀ x ∈ s0.arena.chain 0 s0.arena.sizeWards, s.arena.reason x = s0.arena.reason x) →
    (∀ x ∈ reds, x.ref ∈ refs.toList ∧ s0.arena.redundant x.ref = true ∧ s0.arena.reason x.ref = false) →
    RF (collectLoop refs tier1 tier2 s reds i).1 s0 ∧
    (∀ x ∈ s0.arena.chain 0 s0.arena.sizeWards,
      (collectLoop refs tier1 tier2 s reds i).1.arena.reason x = s0.arena.reason x) ∧
    (∀ x ∈ (collectLoop refs tier1 tier2 s reds i).2,
      x.ref ∈ refs.toList ∧ s0.arena.redundant x.ref = true ∧ s0.arena.reason x.ref = false) := by
  -- the `used` update
  have hU : ∀ (s : Solver) (c : Ref) (u : UInt32), RF s s0 → c ∈ refs.toList →
      (∀ x ∈ s0.arena.chain 0 s0.arena.sizeWards, s.arena.reason x = s0.arena.reason x) →
      let s' := if u != 0 then { s with arena := s.arena.setUsed c (u - 1) } else s
      RF s' s0 ∧ (∀ x ∈ s0.arena.chain 0 s0.arena.sizeWards, s'.arena.reason x = s0.arena.reason x) := by
    intro s c u h1 hc h2 s'
    simp only [s']
    split
    · have hl : s.arena.Layout := h1.arena.layout hlay
      have hc' : c ∈ s.arena.chain 0 s.arena.sizeWards := by rw [h1.arena.chain]; exact hrefs c hc
      refine ⟨⟨by rw [← h1.strip]; rfl, h1.arena.trans (setUsed_same hl hc' _)⟩, fun x hx => ?_⟩
      have hx' : x ∈ s.arena.chain 0 s.arena.sizeWards := by rw [h1.arena.chain]; exact hx
      show (s.arena.setUsed c (u - 1)).reason x = _
      rw [setUsed_reason _ hl hc' hx']; exact h2 x hx
    · exact ⟨h1, h2⟩
  intro s reds i
  induction s, reds, i using collectLoop.induct refs tier1 tier2 with
  | case1 s reds i hi c hc ih =>
    intro h1 h2 h3; rw [collectLoop, dite_eq_left hi]; dsimp only; rw [ite_eq_left hc]; exact ih h1 h2 h3
  | case2 s reds i hi c hc used s' hr ih =>
    intro h1 h2 h3
    rw [collectLoop, dite_eq_left hi]; dsimp only; rw [ite_eq_right hc]
    have hcm : c ∈ refs.toList := by simp [c]
    obtain ⟨k1, k2⟩ := hU s c used h1 hcm h2
    have hr' : (if used != 0 then { s with arena := s.arena.setUsed c (used - 1) } else s).arena.reason c = true := hr
    rw [ite_eq_left hr']
    exact ih k1 k2 h3
  | case3 s reds i hi c hc used s' hr glue hg ih =>
    intro h1 h2 h3
    rw [collectLoop, dite_eq_left hi]; dsimp only; rw [ite_eq_right hc]
    have hcm : c ∈ refs.toList := by simp [c]
    obtain ⟨k1, k2⟩ := hU s c used h1 hcm h2
    have hr' : ¬ (if used != 0 then { s with arena := s.arena.setUsed c (used - 1) } else s).arena.reason c = true := hr
    rw [ite_eq_right hr']; try dsimp only
    have hg' := hg; simp only [glue, s', used, c, dite_eq_ite] at hg'
    rw [ite_eq_left hg']
    exact ih k1 k2 h3
  | case4 s reds i hi c hc used s' hr glue hg negSize negGlue ih =>
    intro h1 h2 h3
    rw [collectLoop, dite_eq_left hi]; dsimp only; rw [ite_eq_right hc]
    have hcm : c ∈ refs.toList := by simp [c]
    obtain ⟨k1, k2⟩ := hU s c used h1 hcm h2
    have hr' : ¬ (if used != 0 then { s with arena := s.arena.setUsed c (used - 1) } else s).arena.reason c = true := hr
    rw [ite_eq_right hr']; try dsimp only
    have hg' := hg; simp only [glue, s', used, c, dite_eq_ite] at hg'
    rw [ite_eq_right hg']
    simp only [negSize, negGlue, glue, s', used, c, dite_eq_ite] at ih
    apply ih k1 k2
    intro x hx
    rcases Array.mem_push.mp hx with hx | hx
    · exact h3 x hx
    · subst hx
      refine ⟨hcm, ?_, ?_⟩
      · simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
        have := (h1.arena.flags (hrefs c hcm)).2.1; rw [← this]; exact hc.1
      · rw [← k2 c (hrefs c hcm)]; simpa using hr'
  | case5 s reds i hi => intro h1 h2 h3; rw [collectLoop, dite_eq_right hi]; exact ⟨h1, h2, h3⟩

theorem rf_firstReducible (s : Solver) (r : Ref) : RF { s with firstReducible := r } s := ⟨rfl, Arena.Same.refl _⟩

theorem collectFrom_spec (refs : Array Ref) (k : Nat) (s0 s : Solver) (hlay : s0.arena.Layout)
    (hrefs : ∀ x ∈ refs.toList, x ∈ s0.arena.chain 0 s0.arena.sizeWards) (hs : RF s s0) (ha : s.arena = s0.arena) :
    RF (collectFrom refs k s).2 s0 ∧
    (∀ x ∈ s0.arena.chain 0 s0.arena.sizeWards, (collectFrom refs k s).2.arena.reason x = s0.arena.reason x) ∧
    ∀ reds, (collectFrom refs k s).1 = some reds → reds.size ≠ 0 ∧
      ∀ x ∈ reds, x.ref ∈ refs.toList ∧ s0.arena.redundant x.ref = true ∧ s0.arena.reason x.ref = false := by
  have hr0 : ∀ x ∈ s0.arena.chain 0 s0.arena.sizeWards, s.arena.reason x = s0.arena.reason x := by
    intro x _; rw [ha]
  unfold collectFrom
  dsimp only
  generalize s.tier1Limit = t1
  generalize max t1 s.tier2Limit = t2
  obtain ⟨c1, c2, c3⟩ := collectLoop_spec refs t1 t2 s0 hlay hrefs s #[] k hs hr0 (fun x hx => by simp at hx)
  generalize collectLoop refs t1 t2 s #[] k = R at c1 c2 c3 ⊢
  obtain ⟨u, reds⟩ := R
  dsimp only at c1 c2 c3 ⊢
  split
  · exact ⟨c1, c2, fun reds h => by simp at h⟩
  · rename_i hne
    refine ⟨c1, c2, fun reds' h => ?_⟩
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨by simpa using hne, c3⟩

theorem collectReducibles_spec (s : Solver) (start : Ref) (hlay : s.arena.Layout)
    (hQ : ∀ x ∈ s.arena.chain start s.arena.sizeWards, x ∈ s.arena.chain 0 s.arena.sizeWards) :
    RF (s.collectReducibles start).2 s ∧
    (∀ x ∈ s.arena.chain 0 s.arena.sizeWards, (s.collectReducibles start).2.arena.reason x = s.arena.reason x) ∧
    ∀ reds, (s.collectReducibles start).1 = some reds → reds.size ≠ 0 ∧
      ∀ x ∈ reds, x.ref ∈ s.arena.chain start s.arena.sizeWards ∧ s.arena.redundant x.ref = true ∧
        s.arena.reason x.ref = false := by
  unfold collectReducibles
  dsimp only
  have hrefs : ∀ x ∈ (s.arena.clauseRefsFrom start).toList, x ∈ s.arena.chain 0 s.arena.sizeWards := by
    intro x hx; apply hQ; simpa [clauseRefsFrom] using hx
  split
  · exact ⟨⟨rfl, Arena.Same.refl _⟩, fun _ _ => rfl, fun reds h => by simp at h⟩
  · generalize skipIrredundant s.arena (s.arena.clauseRefsFrom start) 0 = k
    obtain ⟨c1, c2, c3⟩ := collectFrom_spec (s.arena.clauseRefsFrom start) k s
      ({ s with firstReducible := (s.arena.clauseRefsFrom start)[k]! } : Solver) hlay hrefs (rf_firstReducible _ _) rfl
    refine ⟨c1, c2, fun reds h => ?_⟩
    obtain ⟨k1, k2⟩ := c3 reds h
    exact ⟨k1, fun x hx => by obtain ⟨a, b, c⟩ := k2 x hx; exact ⟨by simpa [clauseRefsFrom] using a, b, c⟩⟩

/-! ### Marking garbage -/

/-- `b` is `a` with garbage bits set on some redundant non-reason clauses at or after `start`. -/
structure GSame (a b : Arena) (start : Ref) : Prop where
  wsize : b.words.size = a.words.size
  other : ∀ j, (∀ x ∈ a.chain 0 a.sizeWards, j ≠ base x) → b.words.get! j = a.words.get! j
  hdr : ∀ x ∈ a.chain 0 a.sizeWards, b.word0 x = a.word0 x ∨
    (b.word0 x = a.word0 x ||| ClauseHeader.garbageBit ∧ start ≤ x ∧ a.redundant x = true ∧ a.reason x = false)

theorem garbage_or_flags (w : UInt32) :
    ((w ||| ClauseHeader.garbageBit) &&& ClauseHeader.redundantBit != 0) = (w &&& ClauseHeader.redundantBit != 0) ∧
    ((w ||| ClauseHeader.garbageBit) &&& ClauseHeader.shrunkenBit != 0) = (w &&& ClauseHeader.shrunkenBit != 0) ∧
    ((w ||| ClauseHeader.garbageBit) &&& ClauseHeader.reasonBit != 0) = (w &&& ClauseHeader.reasonBit != 0) ∧
    ((w ||| ClauseHeader.garbageBit) &&& ClauseHeader.garbageBit != 0) = true ∧
    (w ||| ClauseHeader.garbageBit) ||| ClauseHeader.garbageBit = w ||| ClauseHeader.garbageBit := by
  simp only [ClauseHeader.shrunkenBit, ClauseHeader.redundantBit, ClauseHeader.garbageBit, ClauseHeader.reasonBit]
  have k : ∀ (x y : UInt32), (x = 0 ↔ y = 0) → (x != 0) = (y != 0) := by
    intro x y h; cases h1 : (x != 0) <;> cases h2 : (y != 0) <;> simp_all
  refine ⟨k _ _ (by constructor <;> intro h <;> bv_k), k _ _ (by constructor <;> intro h <;> bv_k),
    k _ _ (by constructor <;> intro h <;> bv_k), ?_, by bv_k⟩
  have : (w ||| ((1 : UInt32) <<< 19)) &&& ((1 : UInt32) <<< 19) = (1 : UInt32) <<< 19 := by bv_k
  rw [this]; decide

section G
variable {a b : Arena} {start : Ref}

theorem GSame.flags (h : GSame a b start) {x : Ref} (hx : x ∈ a.chain 0 a.sizeWards) :
    b.redundant x = a.redundant x ∧ b.shrunken x = a.shrunken x ∧ b.reason x = a.reason x ∧
    (a.garbage x = true → b.garbage x = true) ∧
    (b.garbage x = true → a.garbage x = true ∨ (start ≤ x ∧ a.redundant x = true ∧ a.reason x = false)) := by
  unfold redundant shrunken reason garbage flag
  rcases h.hdr x hx with e | ⟨e, h1, h2, h3⟩
  · rw [e]; exact ⟨rfl, rfl, rfl, id, Or.inl⟩
  · obtain ⟨f1, f2, f3, f4, _⟩ := garbage_or_flags (a.word0 x)
    rw [e, f1, f2, f3, f4]
    exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => Or.inr ⟨h1, h2, h3⟩⟩

theorem GSame.size (h : GSame a b start) (hl : a.Layout) {x : Ref} (hx : x ∈ a.chain 0 a.sizeWards) :
    b.size x = a.size x ∧ b.searched x = a.searched x ∧ b.litsL x = a.litsL x := by
  have hne : ∀ y ∈ a.chain 0 a.sizeWards, base y ≠ base x + 1 ∧ base y ≠ base x + 2 ∧
      (∀ k, k < (a.size x).toNat → base y ≠ litPos x k) ∧ (y ≠ x → base y ≠ base x) :=
    fun y hy => header_ne hl hy hx
  have hs : b.size x = a.size x := h.other _ (fun y hy => Ne.symm (hne y hy).2.1)
  refine ⟨hs, h.other _ (fun y hy => Ne.symm (hne y hy).1), ?_⟩
  unfold litsL; rw [hs]
  apply List.map_congr_left; intro k hk; simp at hk
  exact h.other _ (fun y hy => Ne.symm ((hne y hy).2.2.1 k hk))

theorem GSame.chain (h : GSame a b start) (hl : a.Layout) : b.chain 0 b.sizeWards = a.chain 0 a.sizeWards := by
  have hsw : b.sizeWards = a.sizeWards := by simp [sizeWards, h.wsize]
  rw [hsw]
  refine (chain_congr' hsw.symm _ 0 (fun x hx => ?_)).symm
  have hsh := LayoutFrom.not_shrunken hl.chain x hx
  exact ⟨(h.size hl hx).1.symm, hsh, by rw [(h.flags hx).2.1]; exact hsh⟩

theorem GSame.layout (h : GSame a b start) (hl : a.Layout) : b.Layout := by
  have hsw : b.sizeWards = a.sizeWards := by simp [sizeWards, h.wsize]
  refine ⟨?_, by rw [h.wsize, hsw]; exact hl.mult4, by rw [hsw]; exact hl.bound⟩
  rw [h.chain hl]
  apply layoutFrom_congr' hsw.symm _ 0 _ hl.chain
  intro x hx
  refine ⟨(h.size hl hx).1.symm, ?_⟩
  rw [(h.flags hx).2.1]; exact LayoutFrom.not_shrunken hl.chain x hx

theorem GSame.refl (a : Arena) (start : Ref) : GSame a a start := ⟨rfl, fun _ _ => rfl, fun _ _ => Or.inl rfl⟩

theorem GSame.trans {c : Arena} (h1 : GSame a b start) (h2 : GSame b c start) (hl : a.Layout) :
    GSame a c start := by
  have hch := h1.chain hl
  refine ⟨h2.wsize.trans h1.wsize, fun j hj => ?_, fun x hx => ?_⟩
  · rw [h2.other j (by rw [hch]; exact hj), h1.other j hj]
  · have hxb : x ∈ b.chain 0 b.sizeWards := by rw [hch]; exact hx
    obtain ⟨f1, _, f3, _⟩ := h1.flags hx
    rcases h2.hdr x hxb with e2 | ⟨e2, k1, k2, k3⟩ <;> rcases h1.hdr x hx with e1 | ⟨e1, m1, m2, m3⟩
    · exact Or.inl (e2.trans e1)
    · exact Or.inr ⟨e2.trans e1, m1, m2, m3⟩
    · exact Or.inr ⟨by rw [e2, e1], k1, by rw [← f1]; exact k2, by rw [← f3]; exact k3⟩
    · exact Or.inr ⟨by rw [e2, e1, (garbage_or_flags _).2.2.2.2], m1, m2, m3⟩

theorem setGarbage_gsame (hl : a.Layout) {r : Ref} (hr : r ∈ a.chain 0 a.sizeWards) (hs : start ≤ r)
    (hred : a.redundant r = true) (hreas : a.reason r = false) : GSame a (a.setGarbage r true) start := by
  have hb := hl.mem_bounds hr
  have hm := hl.mult4
  have hw := wardsOfClause_pos (a.size r).toNat
  have hget : ∀ j, (a.setGarbage r true).words.get! j = if base r = j then a.word0 r ||| ClauseHeader.garbageBit
      else a.words.get! j := by
    intro j
    show (a.words.set! (base r) (if true = true then a.word0 r ||| _ else _)).get! j = _
    rw [U32Vec.get!_set!]
    by_cases e : base r = j
    · rw [ite_eq_left ⟨e, by rw [← e]; unfold base; omega⟩, ite_eq_left e]; rfl
    · rw [ite_eq_right (fun h => e h.1), ite_eq_right e]
  refine ⟨by simp [setGarbage, setFlag, setWord0], fun j hj => ?_, fun x hx => ?_⟩
  · rw [hget, ite_eq_right (fun e => hj r hr e.symm)]
  · by_cases e : x = r
    · subst e; right
      refine ⟨by unfold word0; rw [hget, ite_eq_left rfl]; rfl, hs, hred, hreas⟩
    · left; unfold word0; rw [hget, ite_eq_right ((header_ne hl hr hx).2.2.2 (Ne.symm e))]

end G

theorem markClauseAsGarbage_red (s : Solver) (r : Ref) (hred : s.arena.redundant r = true) :
    stripRFN (s.markClauseAsGarbage r) = stripRFN s ∧ (s.markClauseAsGarbage r).arena = s.arena.setGarbage r true := by
  unfold markClauseAsGarbage decClause
  rw [hred]
  exact ⟨rfl, rfl⟩

theorem markGarbageLoop_spec (start : Ref) (reds : Array Reducible) (n : Nat) (s0 : Solver) (hl : s0.arena.Layout)
    (hreds : ∀ i : Nat, start ≤ (reds[i]!).ref → (reds[i]!).ref ∈ s0.arena.chain 0 s0.arena.sizeWards) :
    ∀ s i, stripRFN s = stripRFN s0 → GSame s0.arena s.arena start →
    stripRFN (markGarbageLoop start reds n s i) = stripRFN s0 ∧
      GSame s0.arena (markGarbageLoop start reds n s i).arena start := by
  intro s i
  induction s, i using markGarbageLoop.induct start reds n with
  | case1 s i hi r s' ih =>
    intro h1 h2
    rw [markGarbageLoop, ite_eq_left hi]
    apply ih
    · simp only [s']
      split
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        rw [(markClauseAsGarbage_red s r hc.1.2).1]; exact h1
      · rw [← h1]; rfl
    · simp only [s']
      split
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        rw [(markClauseAsGarbage_red s r hc.1.2).2]
        have hls : s.arena.Layout := h2.layout hl
        have hch : r ∈ s.arena.chain 0 s.arena.sizeWards := by rw [h2.chain hl]; exact hreds i hc.1.1
        exact h2.trans (setGarbage_gsame hls hch hc.1.1 hc.1.2 hc.2) hl
      · exact h2
  | case2 s i hi =>
    intro h1 h2; rw [markGarbageLoop, ite_eq_right hi]; exact ⟨h1, h2⟩

theorem _root_.LeanKissat.Arena.LayoutTo.congr_ss {a b : Arena} : ∀ {r : Ref} {e : Nat} {refs : List Ref},
    LayoutTo a r e refs → (∀ x ∈ refs, a.size x = b.size x ∧ b.shrunken x = false) → LayoutTo b r e refs := by
  intro r e refs
  induction refs generalizing r with
  | nil => intro h _; exact h
  | cons r' rs ih =>
    intro h hq
    obtain ⟨rfl, hlt, hsh, hnext, hrest⟩ := h
    obtain ⟨e2, hshb⟩ := hq r' (List.mem_cons_self ..)
    have hn : a.nextClause r' = b.nextClause r' := by
      unfold nextClause
      rw [actualWards_of_not_shrunken a r' hsh, actualWards_of_not_shrunken b r' hshb, e2]
    refine ⟨rfl, hlt, hshb, by rw [← hn, hnext, e2], ?_⟩
    rw [← hn]
    exact ih hrest (fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- Marking redundant non-reason clauses as garbage keeps the collection precondition. -/
theorem gsame_colPre {Φ : (Nat → Bool) → Prop} {u v : Solver} {start : Ref} {P Q : List Ref}
    (h : ColPre Φ u start P Q) (h1 : stripRFN v = stripRFN u) (h2 : GSame u.arena v.arena start) :
    ColPre Φ v start P Q ∧ IrrMono u v ∧ (∀ i b, AnaBit b → v.abit i b = u.abit i b) ∧ v.clause = u.clause ∧
      Flg v = Flg u := by
  have e : ∀ {α : Type} (g : Solver → α), (∀ x, g (stripRFN x) = g x) → g v = g u := by
    intro α g hg; rw [← hg v, ← hg u, h1]
  have ea : v.asg = u.asg := e (fun x => x.asg) (fun _ => rfl)
  have ew : v.watches = u.watches := e (fun x => x.watches) (fun _ => rfl)
  have ev : v.vars = u.vars := e (fun x => x.vars) (fun _ => rfl)
  have hs := h.sinv
  have hl := hs.layout
  have hch := h2.chain hl
  have hflg : Flg v = Flg u := by rw [← flg_stripRFN v, ← flg_stripRFN u, h1]
  have eFT : v.frameTrail = u.frameTrail := e (fun x => x.frameTrail) (fun _ => rfl)
  have eLv : v.level = u.level := e (fun x => x.level) (fun _ => rfl)
  have eP : v.propagate = u.propagate := e (fun x => x.propagate) (fun _ => rfl)
  have eD : v.delayed = u.delayed := e (fun x => x.delayed) (fun _ => rfl)
  have eCl : v.clause = u.clause := e (fun x => x.clause) (fun _ => rfl)
  have eRefs : v.refsL = u.refsL := hch
  have eE : v.entries = u.entries := by funext l; simp [entries, watchesOf, ew]
  have eB : ∀ a b, v.BinWatched a b ↔ u.BinWatched a b := by intro a b; simp [BinWatched, eE]
  -- clause views
  have hview : ∀ r ∈ u.refsL, v.clauseL r = u.clauseL r ∧ v.arena.size r = u.arena.size r ∧
      v.arena.searched r = u.arena.searched r ∧ v.arena.redundant r = u.arena.redundant r ∧
      (2 ≤ (u.arena.size r).toNat → v.lit0 r = u.lit0 r ∧ v.lit1 r = u.lit1 r) := by
    intro r hr
    obtain ⟨s1, s2, s3⟩ := h2.size hl hr
    refine ⟨s3, s1, s2, (h2.flags hr).1, fun h2' => ⟨lit_eq_of_litsL s1 s3 (by rw [s1]; omega),
      lit_eq_of_litsL s1 s3 (by rw [s1]; omega)⟩⟩
  have hliveV : ∀ r, v.LiveRef r → u.LiveRef r := by
    intro r ⟨h1r, h2r⟩
    rw [eRefs] at h1r
    refine ⟨h1r, ?_⟩
    cases hg : u.arena.garbage r
    · rfl
    · have := (h2.flags h1r).2.2.2.1 hg; rw [this] at h2r; simp at h2r
  have hdbV : ∀ c, v.InDB c → u.InDB c := by
    intro c hc
    rcases hc with ⟨r, hr, rfl⟩ | ⟨a, b, hab, rfl⟩
    · exact Or.inl ⟨r, hliveV r hr, (hview r (hliveV r hr).1).1⟩
    · exact Or.inr ⟨a, b, (eB a b).mp hab, rfl⟩
  have hT : v.IsTrue = u.IsTrue := by funext l; simp [IsTrue, ea]
  have hL : v.lvl = u.lvl := by funext l; simp [lvl, ea]
  have hTr : v.trailL = u.trailL := by simp [trailL, ea]
  have hFr : v.framesL = u.framesL := by simp [framesL, eFT]
  have hPL : v.pushLevel = u.pushLevel := by funext p; simp [pushLevel, hFr]
  have hRo : v.reasonOf = u.reasonOf := by funext l; simp [reasonOf, reasonIdx, ea]
  have hBo : v.binOf = u.binOf := by funext l; simp [binOf, isBinaryReason, abit, abits, ea]
  have hInvS : ∀ Pp c, v.InvSAt Pp c ↔ u.InvSAt Pp c := by
    intro Pp c
    have : v.PropFalseAt = u.PropFalseAt := by
      funext Pp w k; simp [PropFalseAt, IsFalse, trailL, lvl, pushLevel, framesL, ea, eFT]
    simp only [InvSAt, this, IsTrue, lvl, ea]
  have hW := hs.ws
  have hws : v.WatchStruct := by
    refine ⟨fun l => by unfold watchesOf; rw [ew]; exact hW.words l, fun l b r hm => ?_, fun r hr => ?_,
      fun a b hab => ?_, by rw [eD]; exact hW.delayed, by rw [ew, ev]; exact hW.watchesSize,
      by rw [ev]; exact hW.varsBound⟩
    · rw [eE] at hm
      obtain ⟨k1, k2⟩ := hW.refOK l b r hm
      refine ⟨by rw [eRefs]; exact k1, fun hg => ?_⟩
      have hgu : u.arena.garbage r = false := hliveV r ⟨by rw [eRefs]; exact k1, hg⟩ |>.2
      obtain ⟨k3, k4⟩ := k2 hgu
      have hlu : u.LiveRef r := ⟨k1, hgu⟩
      obtain ⟨h3, _⟩ := hW.live r hlu
      obtain ⟨v1, _, _, _, v5⟩ := hview r k1
      obtain ⟨l0, l1⟩ := v5 (by omega)
      exact ⟨by rw [l0, l1]; exact k3, by rw [v1]; exact k4⟩
    · have hlu := hliveV r hr
      obtain ⟨h3, hnd, hs1, hs2, c0, c1, hv⟩ := hW.live r hlu
      obtain ⟨v1, v2, v3, _, v5⟩ := hview r hlu.1
      obtain ⟨l0, l1⟩ := v5 (by omega)
      refine ⟨by rw [v2]; exact h3, by rw [v1]; exact hnd, by rw [v3]; exact hs1, by rw [v3, v2]; exact hs2,
        by rw [eE, l0]; exact c0, by rw [eE, l1]; exact c1, fun x hx => ?_⟩
      rw [v1] at hx; have := hv x hx; unfold ValidLit at *; rw [ev]; exact this
    · rw [eB] at hab
      obtain ⟨k1, k2, k3, k4⟩ := hW.bin a b hab
      exact ⟨(eB b a).mpr k1, by unfold ValidLit at *; rw [ev]; exact k2, by unfold ValidLit at *; rw [ev]; exact k3, k4⟩
  have hcore : v.Core := core_congr ea ev hs.core
  have hlev : v.LevelOK := by
    have hl := hs.levelOK
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hT, hL, eLv]; exact hl.trueLe
    · rw [hTr, hL, hPL]; exact hl.pushLe
    · rw [hFr]; exact hl.sorted
    · rw [hFr, eLv]; exact hl.len
    · rw [hFr, eP]; exact hl.framesLe
    · rw [hTr, eP]; exact hl.propLe
    · rw [hFr]; exact hl.strict
    · rw [hFr, hTr]; exact hl.framesLt
    · rw [eFT]; exact hl.frames0
  have hreas : v.ReasonOK := by
    intro l ht hl'
    rw [hT] at ht; rw [hL] at hl'
    have hR := hs.reasons l ht hl'
    unfold ReasonAt at hR ⊢
    rw [hRo, hBo]
    rcases hR with h0 | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨b1, (eB _ _).mpr b2, (ante_congr ea).mpr b3⟩)
    · refine Or.inr (Or.inr ⟨b1, ⟨by rw [eRefs]; exact b2.1, ?_⟩, by rw [(hview _ b2.1).1]; exact b3,
        fun x hx hne => (ante_congr ea).mpr (b4 x (by rw [← (hview _ b2.1).1]; exact hx) hne)⟩)
      cases hg : v.arena.garbage (u.reasonOf l)
      · rfl
      · exfalso
        rcases (h2.flags b2.1).2.2.2.2 hg with hg' | ⟨hst, _, hre⟩
        · rw [b2.2] at hg'; simp at hg'
        · have hdec : u.reasonOf l ≠ DECISION_REASON := by
            intro e
            have hb := hl.mem_bounds b2.1
            have hbd := hl.bound
            have := wardsOfClause_pos (u.arena.size (u.reasonOf l)).toNat
            have h4 : (u.reasonOf l).toNat < 2 ^ 31 := by omega
            rw [e] at h4; simp [DECISION_REASON] at h4
          have := h.rb l ht hl' b1 hdec hst
          rw [hre] at this; simp at this
  have hsv : SInv Φ v := ⟨hcore, hlev, hws, h2.layout hl, hreas,
    fun l ht hl' => by rw [hT] at ht; rw [hL] at hl'; exact hs.roots l ht hl',
    by have := hs.rsizes; unfold ReasonSizes at *; rw [ea, ev, hTr]; exact this,
    fun c hc => hs.db c (hdbV c hc), by rw [Flg.options hflg]; exact hs.jump⟩
  have hwP := fun x (hx : x ∈ P) => (show x ∈ u.refsL by rw [h.refs]; simp [hx])
  have hwQ := fun x (hx : x ∈ Q) => (show x ∈ u.refsL by rw [h.refs]; simp [hx])
  refine ⟨⟨hsv, fun c hc => ?_, by rw [eP, hTr]; exact h.prop,
    h.lp.congr_ss (fun x hx => ⟨((h2.size hl (hwP x hx)).1).symm, by
      rw [(h2.flags (hwP x hx)).2.1]; exact (h.lp.mem_bounds x hx).2.2⟩), by rw [eRefs]; exact h.refs,
    ?_, fun l ht hl' hb hd hst => ?_, fun l hl' => by rw [eE]; exact h.empty l (by rw [← ev]; exact hl')⟩,
    ?_, fun i b _ => by unfold abit abits; rw [ea], eCl, hflg⟩
  · unfold InvS; rw [hInvS, eP]; exact h.invS c (hdbV c hc)
  · have hsw : v.arena.sizeWards = u.arena.sizeWards := by simp [sizeWards, h2.wsize]
    rw [hsw]
    exact h.lq.congr_ss (fun x hx => ⟨((h2.size hl (hwQ x hx)).1).symm, by
      rw [(h2.flags (hwQ x hx)).2.1]; exact (h.lq.mem_bounds x hx).2.2⟩)
  · rw [hT] at ht; rw [hL] at hl'; rw [hBo] at hb; rw [hRo] at hd hst ⊢
    have := h.rb l ht hl' hb hd hst
    have hm := (reason_live hs.reasons ht hl' hb hd).1
    rw [(h2.flags hm).2.2.1]; exact this
  · refine ⟨fun d hd => Or.inr ⟨d, ?_, fun _ h => h⟩, fun l hl' => ?_⟩
    · rcases hd with ⟨r, hr, hred, rfl⟩ | ⟨a, b, hab, rfl⟩
      · refine Or.inl ⟨r, ⟨by rw [eRefs]; exact hr.1, ?_⟩, by rw [(hview r hr.1).2.2.2.1]; exact hred,
          (hview r hr.1).1.symm⟩
        cases hg : v.arena.garbage r
        · rfl
        · exfalso
          rcases (h2.flags hr.1).2.2.2.2 hg with hg' | ⟨_, hrd, _⟩
          · rw [hr.2] at hg'; simp at hg'
          · rw [hred] at hrd; simp at hrd
      · exact Or.inr ⟨a, b, (eB a b).mpr hab, rfl⟩
    · unfold RootTrue at *; rw [hT, hL]; exact hl'

end Solver
end LeanKissat
