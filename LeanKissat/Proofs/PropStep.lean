import LeanKissat.Proofs.PropSem

/-!
# Step lemmas for `PS.step`

Each case of `PS.step` preserves `RunInv`.
-/

namespace LeanKissat
namespace Solver
open Arena

theorem xor_self_left (a b : UInt32) : a ^^^ b ^^^ a = b := by bv_k
theorem xor_self_right (a b : UInt32) : a ^^^ b ^^^ b = a := by bv_k

theorem isTrue_iff_vTrue (s : Solver) (l : Lit) :
    s.IsTrue l ↔ vTrue (s.asg.values.get! l.toNat) = true := by
  simp [IsTrue, vTrue, VAL_TRUE]

theorem isFalse_iff_vFalse (s : Solver) (l : Lit) :
    s.IsFalse l ↔ vFalse (s.asg.values.get! l.toNat) = true := by
  simp [IsFalse, vFalse, VAL_FALSE]

theorem V_a (s0 : Solver) (st : PS) : (V s0 st).asg = st.a := rfl
theorem V_arena (s0 : Solver) (st : PS) : (V s0 st).arena = st.arena := rfl

/-- Only `a`, `arena`, `res` and (under a conflict) `s` of a spec state matter. -/
theorem RunInv.congr {s0 : Solver} {i : Nat} {n : Lit} {st st' : PS} {d : List WEntry}
    (h : RunInv s0 i n st d) (ha : st'.a = st.a) (har : st'.arena = st.arena)
    (hr : st'.res = none) (hr0 : st.res = none) : RunInv s0 i n st' d := by
  have hV : V s0 st' = V s0 st := by simp [V, ha, har]
  refine ⟨?_, ?_, ?_, ?_, har ▸ h.arena, ?_, fun _ => ?_, har ▸ h.untouched, ?_, ?_⟩ <;>
    (try rw [hV])
  · exact h.core
  · exact h.trail
  · exact h.extLevel
  · exact h.persist
  · exact h.inv
  · exact h.visit hr0
  · exact h.frames
  · intro c hc; simp [hr] at hc

/-- Keep entry `e` without changing the assignment or arena. -/
theorem RunInv.keep {s0 : Solver} {i : Nat} {n : Lit} {st : PS} {d : List WEntry}
    (h : RunInv s0 i n st d) (hr0 : st.res = none) (e : WEntry) (st' : PS)
    (ha : st'.a = st.a) (har : st'.arena = st.arena) (hr : st'.res = none)
    (hv : VisitOK s0 (V s0 st) n e) : RunInv s0 i n st' (d ++ [e]) := by
  have h' := h.congr ha har hr hr0
  have hV : V s0 st' = V s0 st := by simp [V, ha, har]
  refine ⟨h'.core, h'.trail, h'.extLevel, h'.persist, h'.arena, h'.inv, ?_, ?_, h'.frames,
    h'.conflict⟩
  · intro _ e' he'
    rw [hV]
    rcases List.mem_append.mp he' with he' | he'
    · exact h.visit hr0 e' he'
    · rw [List.mem_singleton.mp he']; exact hv
  · intro r hr' hn
    exact h'.untouched r hr' (fun b hb => hn b (List.mem_append_left _ hb))

/-- Record a conflict (assignment and arena unchanged). -/
theorem RunInv.conflict' {s0 : Solver} {i : Nat} {n : Lit} {st : PS} {d : List WEntry}
    (h : RunInv s0 i n st d) (hr0 : st.res = none) (e : WEntry) (st' : PS) (c : CRef)
    (ha : st'.a = st.a) (har : st'.arena = st.arena) (hr : st'.res = some c)
    (hc : ConflictOK (V s0 st) st'.s c) : RunInv s0 i n st' (d ++ [e]) := by
  have hV : V s0 st' = V s0 st := by simp [V, ha, har]
  refine ⟨?_, ?_, ?_, ?_, har ▸ h.arena, ?_, fun hn => by simp [hr] at hn, ?_, ?_, ?_⟩ <;>
    (try rw [hV])
  · exact h.core
  · exact h.trail
  · exact h.extLevel
  · exact h.persist
  · exact h.inv
  · intro r hr' hn; rw [har]
    exact h.untouched r hr' (fun b hb => hn b (List.mem_append_left _ hb))
  · exact h.frames
  · intro c' hc'; rw [hr] at hc'; cases hc'; exact hc

/-- Level bound for true literals of the virtual solver. -/
theorem RunInv.lvl_true {s0 : Solver} {i : Nat} {n : Lit} {st : PS} {d : List WEntry}
    (h : RunInv s0 i n st d) (hl : s0.LevelOK) {t : Lit} (ht : (V s0 st).IsTrue t) :
    (V s0 st).lvl t ≤ s0.level.toNat := by
  by_cases h0 : s0.IsTrue t
  · rw [(h.persist t h0).2]; exact hl.trueLe t h0
  · exact h.extLevel t ht h0

theorem RunInv.lvl_false {s0 : Solver} {i : Nat} {n : Lit} {st : PS} {d : List WEntry}
    (h : RunInv s0 i n st d) (hl : s0.LevelOK) {t : Lit} (ht : (V s0 st).IsFalse t) :
    (V s0 st).lvl t ≤ s0.level.toNat := by
  have ht' : (V s0 st).IsTrue (NOT t) := by
    have := (h.core.valCons (NOT t)).1.mpr; rw [NOT_NOT] at this; exact this ht
  have := h.lvl_true hl ht'
  rwa [h.core.lvlVar] at this

/-- Live references of the virtual solver are those of `s0`. -/
theorem ArenaRel.liveRef {s0 : Solver} {st : PS} (h : ArenaRel s0.arena st.arena) (r : Ref) :
    (V s0 st).LiveRef r ↔ s0.LiveRef r := by
  unfold LiveRef refsL
  simp only [V_arena]
  rw [h.chain]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    unfold garbage flag at *; rw [← h.word0 r h1]; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    unfold garbage flag at *; rw [h.word0 r h1]; exact h2

theorem ArenaRel.write {a b c : Arena} {x0 : Ref} (h : ArenaRel a b) (hw : WriteOK b c x0)
    (hp : (c.litsL x0).Perm (b.litsL x0)) : ArenaRel a c := by
  refine ⟨hw.layout, hw.sizeWards.trans h.sizeWards, hw.chain.trans h.chain, ?_, ?_, ?_⟩
  · intro x hx; rw [hw.word0 x (h.chain ▸ hx), h.word0 x hx]
  · intro x hx; rw [hw.size x (h.chain ▸ hx), h.size x hx]
  · intro x hx
    by_cases e : x = x0
    · subst e; exact hp.trans (h.perm x hx)
    · rw [(hw.others x (h.chain ▸ hx) e).1]; exact h.perm x hx

theorem countRef_append (r : Ref) (a b : List WEntry) :
    countRef r (a ++ b) = countRef r a + countRef r b := by
  induction a with
  | nil => simp [countRef]
  | cons e es ih =>
    cases e <;> simp [countRef, ih] <;> omega

theorem countRef_pos (r : Ref) : ∀ (L : List WEntry) (b : Lit), WEntry.large b r ∈ L →
    0 < countRef r L := by
  intro L
  induction L with
  | nil => intro b h; simp at h
  | cons e es ih =>
    intro b h
    rcases List.mem_cons.mp h with rfl | h
    · simp [countRef]; omega
    · have := ih b h; cases e <;> simp [countRef] <;> omega

/-- A live clause has exactly one entry in the watch lists of its watches. -/
theorem not_mem_done {done rest : List WEntry} {b : Lit} {r : Ref}
    (hc : countRef r (done ++ WEntry.large b r :: rest) = 1) :
    (∀ b', WEntry.large b' r ∉ done) ∧ (∀ b', WEntry.large b' r ∉ rest) := by
  rw [countRef_append] at hc
  simp only [countRef, ite_true] at hc
  constructor
  · intro b' hb; have := countRef_pos r done b' hb; omega
  · intro b' hb; have := countRef_pos r rest b' hb; omega

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- Hypotheses of a single step. -/
structure StepHyp (s0 : Solver) (i : Nat) (lit : Lit) (st : PS) (done rest : List WEntry)
    (e : WEntry) : Prop where
  ctx : Ctx s0 i lit
  run : RunInv s0 i (NOT lit) st done
  res : st.res = none
  split : s0.entries (NOT lit) = done ++ e :: rest

theorem StepHyp.mem {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {e : WEntry} (H : StepHyp s0 i lit st done rest e) : e ∈ s0.entries (NOT lit) := by
  rw [H.split]; simp

theorem StepHyp.notLitFalse {s0 : Solver} {i : Nat} {lit : Lit} {st : PS}
    {done rest : List WEntry} {e : WEntry} (H : StepHyp s0 i lit st done rest e) :
    (V s0 st).IsFalse (NOT lit) :=
  (H.run.core.valCons lit).1.mp (H.run.persist lit H.ctx.litTrue).1

theorem step_bin {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {b : Lit} (H : StepHyp s0 i lit st done rest (.bin b)) (probing jump : Bool) {lv : UInt32}
    (hlv : lv.toNat ≤ s0.level.toNat) :
    RunInv s0 i (NOT lit) (PS.step probing jump lv (NOT lit) st (.bin b))
      (done ++ [.bin b]) := by
  have hbw : s0.BinWatched (NOT lit) b := H.mem
  obtain ⟨_, _, hvb, _⟩ := H.ctx.ws.bin _ _ hbw
  unfold PS.step
  simp only
  by_cases h1 : vTrue (st.a.values.get! b.toNat) = true
  · rw [if_pos h1]
    exact H.run.keep H.res _ _ rfl rfl H.res ((isTrue_iff_vTrue _ _).mpr h1)
  rw [if_neg h1]
  by_cases h2 : vFalse (st.a.values.get! b.toNat) = true
  · rw [if_pos h2]
    exact H.run.conflict' H.res _ _ .binConflict rfl rfl rfl
      ⟨hbw, H.notLitFalse, (isFalse_iff_vFalse _ _).mpr h2⟩
  rw [if_neg h2]
  have hun : ¬ (V s0 st).IsTrue b ∧ ¬ (V s0 st).IsFalse b :=
    ⟨fun h => h1 ((isTrue_iff_vTrue _ _).mp h), fun h => h2 ((isFalse_iff_vFalse _ _).mp h)⟩
  refine RunInv.congr (st := { st with a := st.a.assign probing lv true b _ })
    ?_ rfl rfl H.res H.res
  refine H.run.assign H.ctx.lt_len H.res hvb hun hlv _ ?_ ?_
  · intro _
    show (V s0 st).withAssign _ _ _ _ _ |>.IsTrue b
    exact (assign_isTrue H.run.core.sizes hvb b).mpr (Or.inl rfl)
  · intro r _ hn b' hb'; exact hn b' (List.mem_append_left _ hb')

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The facts about a live large entry at the time it is visited. -/
structure LargeFacts (s0 : Solver) (lit : Lit) (st : PS) (done : List WEntry) (b : Lit)
    (r : Ref) : Prop where
  chain : r ∈ st.arena.chain 0 st.arena.sizeWards
  live0 : s0.LiveRef r
  size3 : 3 ≤ (st.arena.size r).toNat
  searched2 : 2 ≤ (st.arena.searched r).toNat
  searchedLt : (st.arena.searched r).toNat < (st.arena.size r).toNat
  nodup : (st.arena.litsL r).Nodup
  valid : ∀ x ∈ st.arena.litsL r, (V s0 st).ValidLit x
  blocking : b ∈ st.arena.litsL r
  watch : (st.arena.lit r 0 = NOT lit ∧
      st.arena.lit r 1 = st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit) ∨
    (st.arena.lit r 1 = NOT lit ∧
      st.arena.lit r 0 = st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit)
  ne01 : st.arena.lit r 0 ≠ st.arena.lit r 1
  notDone : ∀ b', WEntry.large b' r ∉ done

theorem lit_mem_litsL (a : Arena) (r : Ref) (k : Nat) (hk : k < (a.size r).toNat) :
    a.lit r k ∈ a.litsL r := by
  unfold litsL; exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem StepHyp.largeFacts {s0 : Solver} {i : Nat} {lit : Lit} {st : PS}
    {done rest : List WEntry} {b : Lit} {r : Ref} (H : StepHyp s0 i lit st done rest (.large b r))
    (hg : s0.arena.garbage r = false) : LargeFacts s0 lit st done b r := by
  obtain ⟨hr, hlive⟩ := H.ctx.ws.refOK _ _ _ H.mem
  obtain ⟨hw, hb⟩ := hlive hg
  have hl0 : s0.LiveRef r := ⟨hr, hg⟩
  obtain ⟨h3, hnd, hs2, hslt, hc0, hc1, hval⟩ := H.ctx.ws.live r hl0
  have hcount : countRef r (s0.entries (NOT lit)) = 1 := by
    rcases hw with hw | hw <;> rw [hw] <;> assumption
  rw [H.split] at hcount
  have hnd' := (not_mem_done hcount).1
  obtain ⟨hL, hS⟩ := H.run.untouched r hl0 hnd'
  have hsz := H.run.arena.size r hr
  have hsz' : (st.arena.size r).toNat = (s0.arena.size r).toNat := by rw [hsz]
  have hch : r ∈ st.arena.chain 0 st.arena.sizeWards := by
    rw [H.run.arena.chain]; exact hr
  have hlit : ∀ k, k < (st.arena.size r).toNat → st.arena.lit r k = s0.arena.lit r k := by
    intro k hk
    have h1 : k < (st.arena.litsL r).length := by rw [length_litsL]; exact hk
    rw [← getElem_litsL _ _ _ h1, ← getElem_litsL _ _ _ (by rw [← hL]; exact h1)]
    simp only [hL]
  have e0 := hlit 0 (by omega)
  have e1 := hlit 1 (by omega)
  have hnd2 : (st.arena.litsL r).Nodup := by rw [hL]; exact hnd
  have hne : st.arena.lit r 0 ≠ st.arena.lit r 1 := by
    intro e
    have h0 : 0 < (st.arena.litsL r).length := by rw [length_litsL]; omega
    have h1 : 1 < (st.arena.litsL r).length := by rw [length_litsL]; omega
    rw [← getElem_litsL _ _ _ h0, ← getElem_litsL _ _ _ h1] at e
    have := (List.Nodup.getElem_inj hnd2).mp e
    omega
  refine ⟨hch, hl0, by omega, by rw [hS]; exact hs2, by rw [hS, hsz]; exact hslt, hnd2,
    fun x hx => hval x (by rw [hL] at hx; exact hx), by rw [hL]; exact hb, ?_, hne, hnd'⟩
  unfold lit0 lit1 at hw
  rw [← e0, ← e1] at hw
  rcases hw with hw | hw
  · left; rw [← hw, xor_self_left]; exact ⟨rfl, rfl⟩
  · right; rw [← hw, xor_self_right]; exact ⟨rfl, rfl⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The two-phase replacement search of `propLoop`. -/
theorem search_spec (arena : Arena) (values : ByteArray) (ref : Ref) (searched size : Nat)
    (h2 : 2 ≤ searched) (hs : searched < size) :
    let r1 := findReplacement arena values ref searched size
    let rr := if r1 < size then r1 else
      (if findReplacement arena values ref 2 searched < searched then
        findReplacement arena values ref 2 searched else size)
    (rr < size → 2 ≤ rr ∧ vFalse (values.get! (arena.lit ref rr).toNat) = false) ∧
    (¬ rr < size → ∀ k, 2 ≤ k → k < size → vFalse (values.get! (arena.lit ref k).toNat) = true) := by
  intro r1 rr
  have A := findReplacement_spec arena values ref searched size
  have B := findReplacement_spec arena values ref 2 searched
  simp only at A B
  by_cases c1 : r1 < size
  · have hrr : rr = r1 := by simp [rr, c1]
    rw [hrr]
    exact ⟨fun _ => ⟨by have := (A.1 c1).1; omega, (A.1 c1).2⟩, fun h => absurd c1 h⟩
  · have A2 := (A.2 (by omega)).2
    by_cases c2 : findReplacement arena values ref 2 searched < searched
    · have hrr : rr = findReplacement arena values ref 2 searched := by simp [rr, c1, c2]
      rw [hrr]
      exact ⟨fun _ => B.1 c2, fun h => absurd (by omega) h⟩
    · have hrr : rr = size := by simp [rr, c1, c2]
      rw [hrr]
      refine ⟨fun h => absurd h (by omega), fun _ k hk1 hk2 => ?_⟩
      by_cases hk : k < searched
      · exact (B.2 (by omega)).2 k hk1 hk
      · exact A2 k (by omega) hk2

theorem lit_eq_of_litsL_eq {a b : Arena} {r : Ref} (h : a.litsL r = b.litsL r) {k : Nat}
    (hk : k < (a.size r).toNat) : a.lit r k = b.lit r k := by
  have h1 : k < (a.litsL r).length := by rw [length_litsL]; exact hk
  rw [← getElem_litsL _ _ _ h1, ← getElem_litsL _ _ _ (by rw [← h]; exact h1)]
  simp only [h]

theorem litsL_cons2 {a : Arena} {r : Ref} {w0 w1 : Lit} {rest : List Lit}
    (h : a.litsL r = w0 :: w1 :: rest) : a.lit r 0 = w0 ∧ a.lit r 1 = w1 := by
  have hl : 2 ≤ (a.litsL r).length := by rw [h]; simp
  constructor
  · rw [← getElem_litsL _ _ _ (by omega : 0 < (a.litsL r).length)]; simp [h]
  · rw [← getElem_litsL _ _ _ (by omega : 1 < (a.litsL r).length)]; simp [h]

/-- The two watches after a replacement. -/
theorem replaced_watches {a : Arena} (h : a.Layout) {x0 : Ref} (hx0 : x0 ∈ a.chain 0 a.sizeWards)
    {R : Nat} (hR2 : 2 ≤ R) (hRs : R < (a.size x0).toNat) (other notLit : Lit)
    (hw : (a.lit x0 0 = notLit ∧ a.lit x0 1 = other) ∨ (a.lit x0 1 = notLit ∧ a.lit x0 0 = other)) :
    (a.replaceArena x0 R other notLit).lit x0 0 = other ∧
    (a.replaceArena x0 R other notLit).lit x0 1 = a.lit x0 R := by
  obtain ⟨W, _, hL, _⟩ := replace_writeOK h hx0 hR2 hRs other notLit hw
  have hsz := W.size x0 hx0
  have hlen : ((a.replaceArena x0 R other notLit).litsL x0).length = (a.size x0).toNat := by
    rw [length_litsL, hsz]
  constructor
  · rw [← getElem_litsL _ _ _ (by omega : 0 < ((a.replaceArena x0 R other notLit).litsL x0).length)]
    simp [hL, List.getElem_set, show ¬ R = 0 by omega, show ¬ 0 = R by omega]
  · rw [← getElem_litsL _ _ _ (by omega : 1 < ((a.replaceArena x0 R other notLit).litsL x0).length)]
    simp [hL, List.getElem_set, show ¬ R = 1 by omega, show ¬ 1 = R by omega]

theorem RunInv.lit_eq {s0 : Solver} {i : Nat} {n : Lit} {st : PS} {d : List WEntry}
    (h : RunInv s0 i n st d) (hws : s0.WatchStruct) {r : Ref} (hl : s0.LiveRef r)
    {a' : Arena} (hL : a'.litsL r = st.arena.litsL r) (hsz : a'.size r = st.arena.size r) :
    a'.lit r 0 = st.arena.lit r 0 ∧ a'.lit r 1 = st.arena.lit r 1 := by
  have h3 := (hws.live r hl).1
  have hs := h.arena.size r hl.1
  have : (a'.size r).toNat = (s0.arena.size r).toNat := by rw [hsz, hs]
  exact ⟨lit_eq_of_litsL_eq hL (by omega), lit_eq_of_litsL_eq hL (by omega)⟩

section setArena
variable (s : Solver) (a : Arena)
theorem core_setArena : ({ s with arena := a } : Solver).Core ↔ s.Core :=
  ⟨fun h => ⟨h.valCons, h.trueOnTrail, h.trailTrue, h.lvlVar, h.sizes, h.domain⟩,
   fun h => ⟨h.valCons, h.trueOnTrail, h.trailTrue, h.lvlVar, h.sizes, h.domain⟩⟩
theorem trailL_setArena : ({ s with arena := a } : Solver).trailL = s.trailL := rfl
theorem isTrue_setArena (l : Lit) : ({ s with arena := a } : Solver).IsTrue l = s.IsTrue l := rfl
theorem isFalse_setArena (l : Lit) : ({ s with arena := a } : Solver).IsFalse l = s.IsFalse l := rfl
theorem lvl_setArena (l : Lit) : ({ s with arena := a } : Solver).lvl l = s.lvl l := rfl
theorem invSAt_setArena (P : Nat) (c : List Lit) :
    ({ s with arena := a } : Solver).InvSAt P c = s.InvSAt P c := rfl
theorem frames_setArena : ({ s with arena := a } : Solver).frameTrail = s.frameTrail ∧
    ({ s with arena := a } : Solver).propagate = s.propagate := ⟨rfl, rfl⟩
theorem inDB_setArena (c : List Lit) : ({ s with arena := a } : Solver).InDB c ↔
    (∃ r, ({ s with arena := a } : Solver).LiveRef r ∧ c = a.litsL r) ∨
    (∃ x y, s.BinWatched x y ∧ c = [x, y]) := Iff.rfl
theorem inDB_iff (c : List Lit) : s.InDB c ↔
    (∃ r, s.LiveRef r ∧ c = s.arena.litsL r) ∨ (∃ x y, s.BinWatched x y ∧ c = [x, y]) := Iff.rfl
theorem lit0_setArena (r : Ref) : ({ s with arena := a } : Solver).lit0 r = a.lit r 0 := rfl
theorem lit1_setArena (r : Ref) : ({ s with arena := a } : Solver).lit1 r = a.lit r 1 := rfl
theorem clauseL_setArena (r : Ref) : ({ s with arena := a } : Solver).clauseL r = a.litsL r := rfl
end setArena

theorem V_eq (s0 : Solver) (st : PS) : V s0 st = { s0 with asg := st.a, arena := st.arena } := rfl

theorem step_replace {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {b : Lit} {r : Ref} (H : StepHyp s0 i lit st done rest (.large b r))
    (F : LargeFacts s0 lit st done b r) (R : Nat) (hR2 : 2 ≤ R) (hRs : R < (st.arena.size r).toNat)
    (hnf : vFalse (st.a.values.get! (st.arena.lit r R).toNat) = false) (dl : List (Lit × Lit × Ref)) :
    RunInv s0 i (NOT lit)
      { st with
        arena := st.arena.replaceArena r R (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit) (NOT lit)
        delayed := dl } (done ++ [.large b r]) := by
  generalize hother : st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit = other
  have hw := F.watch
  rw [hother] at hw
  obtain ⟨W, hperm, _, _⟩ := replace_writeOK H.run.arena.layout F.chain hR2 hRs other (NOT lit) hw
  obtain ⟨hw0, hw1⟩ := replaced_watches H.run.arena.layout F.chain hR2 hRs other (NOT lit) hw
  have hrel := H.run.arena.write W hperm
  generalize st.arena.replaceArena r R other (NOT lit) = a' at W hperm hw0 hw1 hrel ⊢
  have hRnf : ¬ (V s0 st).IsFalse (st.arena.lit r R) := by
    rw [isFalse_iff_vFalse]; simp [V_a, hnf]
  have hneo : other ≠ NOT lit := by
    rcases hw with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · rw [← h0, ← h1]; exact F.ne01.symm
    · rw [← h0, ← h1]; exact F.ne01
  have hneR : st.arena.lit r R ≠ NOT lit := by
    intro e; rw [e] at hRnf; exact hRnf H.notLitFalse
  have hV : V s0 { st with arena := a', delayed := dl } = { V s0 st with arena := a' } := rfl
  have hlive : ∀ r'', ({ V s0 st with arena := a' } : Solver).LiveRef r'' ↔ s0.LiveRef r'' :=
    fun r'' => hrel.liveRef (st := { st with arena := a', delayed := dl }) r''
  refine ⟨?_, ?_, ?_, ?_, hrel, ?_, ?_, ?_, ?_, fun c hc => by simp [H.res] at hc⟩ <;>
    simp only [hV]
  · rw [core_setArena]; exact H.run.core
  · rw [trailL_setArena]; exact H.run.trail
  · simp only [isTrue_setArena, lvl_setArena]; exact H.run.extLevel
  · simp only [isTrue_setArena, lvl_setArena]; exact H.run.persist
  · intro c hc
    rw [invSAt_setArena]
    rcases (inDB_setArena _ _ c).mp hc with ⟨r'', hl'', rfl⟩ | hbin
    · have hl0 := (hlive r'').mp hl''
      by_cases e : r'' = r
      · subst e
        intro w0 w1 rs heq k0 k1 _ h1
        have := (litsL_cons2 heq).2
        rw [hw1] at this
        rw [← this] at h1
        exact absurd h1.1 hRnf
      · rw [(W.others r'' (by rw [H.run.arena.chain]; exact hl0.1) e).1]
        exact H.run.inv _ ((inDB_iff _ _).mpr (Or.inl ⟨r'', (H.run.arena.liveRef r'').mpr hl0, rfl⟩))
    · exact H.run.inv _ ((inDB_iff _ _).mpr (Or.inr hbin))
  · intro _ e' he'
    rcases List.mem_append.mp he' with hd | hs
    · have hv := H.run.visit H.res e' hd
      cases e' with
      | bin b' => exact hv
      | large b' r'' =>
        intro hl
        have hne : r'' ≠ r := by intro e; subst e; exact F.notDone b' hd
        have hch : r'' ∈ st.arena.chain 0 st.arena.sizeWards := by
          rw [H.run.arena.chain]; exact hl.1
        obtain ⟨hL'', _⟩ := W.others r'' hch hne
        obtain ⟨e0, e1⟩ := H.run.lit_eq H.ctx.ws hl hL'' (W.size r'' hch)
        rw [lit0_setArena, lit1_setArena, clauseL_setArena, e0, e1, hL'']
        simp only [isTrue_setArena, lvl_setArena]
        exact hv hl
    · rw [List.mem_singleton.mp hs]
      intro _
      left
      rw [lit0_setArena, lit1_setArena, hw0, hw1]
      exact ⟨hneo.symm, hneR.symm⟩
  · intro r'' hl hn
    have hne : r'' ≠ r := by
      intro e; subst e; exact hn b (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have hch : r'' ∈ st.arena.chain 0 st.arena.sizeWards := by
      rw [H.run.arena.chain]; exact hl.1
    obtain ⟨h1, h2⟩ := W.others r'' hch hne
    obtain ⟨h3, h4⟩ := H.run.untouched r'' hl (fun b' hb' => hn b' (List.mem_append_left _ hb'))
    exact ⟨h1.trans h3, h2.trans h4⟩
  · exact H.run.frames

theorem LargeFacts.false_except {s0 : Solver} {i : Nat} {lit : Lit} {st : PS}
    {done rest : List WEntry} {b : Lit} {r : Ref} (H : StepHyp s0 i lit st done rest (.large b r))
    (F : LargeFacts s0 lit st done b r)
    (hall : ∀ k, 2 ≤ k → k < (st.arena.size r).toNat →
      vFalse (st.a.values.get! (st.arena.lit r k).toNat) = true) :
    ∀ k, k < (st.arena.size r).toNat →
      st.arena.lit r k ≠ st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit →
      (V s0 st).IsFalse (st.arena.lit r k) := by
  intro k hk hne
  by_cases h2 : 2 ≤ k
  · exact (isFalse_iff_vFalse _ _).mpr (hall k h2 hk)
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> rcases F.watch with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · rw [h0]; exact H.notLitFalse
    · exact absurd h0 hne
    · exact absurd h1 hne
    · rw [h1]; exact H.notLitFalse

theorem value_false_of {s : Solver} (hc : s.Core) {l : Lit}
    (h1 : (s.asg.values.get! l.toNat != 0) = true) (h2 : ¬ vTrue (s.asg.values.get! l.toNat) = true) :
    s.IsFalse l := by
  rcases hc.domain l.toNat with h | h | h
  · simp [h] at h1
  · simp [h, vTrue, VAL_TRUE] at h2
  · exact h

theorem step_conflict {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {b : Lit} {r : Ref} (H : StepHyp s0 i lit st done rest (.large b r))
    (F : LargeFacts s0 lit st done b r)
    (hall : ∀ k, 2 ≤ k → k < (st.arena.size r).toNat →
      vFalse (st.a.values.get! (st.arena.lit r k).toNat) = true)
    (h1 : (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat != 0) = true)
    (h2 : ¬ vTrue (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat) = true)
    (st' : PS) (ha : st'.a = st.a) (har : st'.arena = st.arena) (hr : st'.res = some (.large r)) :
    RunInv s0 i (NOT lit) st' (done ++ [.large b r]) := by
  refine H.run.conflict' H.res _ st' _ ha har hr ⟨(H.run.arena.liveRef r).mpr F.live0, ?_⟩
  intro x hx
  have hx' : x ∈ st.arena.litsL r := hx
  unfold litsL at hx'
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx'
  have hk := List.mem_range.mp hk
  by_cases e : st.arena.lit r k = st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit
  · rw [e]; exact value_false_of H.run.core h1 h2
  · exact F.false_except H hall k hk e

theorem step_unit {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {b : Lit} {r : Ref} (H : StepHyp s0 i lit st done rest (.large b r))
    (F : LargeFacts s0 lit st done b r)
    (hall : ∀ k, 2 ≤ k → k < (st.arena.size r).toNat →
      vFalse (st.a.values.get! (st.arena.lit r k).toNat) = true)
    (h1 : ¬ (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat != 0) = true)
    (probing : Bool) (st' : PS)
    (ha : st'.a = st.a.assign probing
      (asgAssignmentLevel st.arena st.a.aLevel (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit) r 0
        (st.arena.size r).toNat 0) false (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit) r)
    (har : st'.arena = st.arena) (hr : st'.res = none) :
    RunInv s0 i (NOT lit) st' (done ++ [.large b r]) := by
  have hfe := F.false_except H hall
  generalize hother : st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit = other at h1 ha hfe
  have hw := F.watch
  rw [hother] at hw
  have hmem : other ∈ st.arena.litsL r := by
    rcases hw with ⟨_, h⟩ | ⟨_, h⟩
    · rw [← h]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
    · rw [← h]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
  have hv0 : st.a.values.get! other.toNat = 0 := by simpa using h1
  have hun : ¬ (V s0 st).IsTrue other ∧ ¬ (V s0 st).IsFalse other := by
    constructor
    · intro h; have : st.a.values.get! other.toNat = VAL_TRUE := h; rw [hv0] at this; simp [VAL_TRUE] at this
    · intro h; have : st.a.values.get! other.toNat = VAL_FALSE := h; rw [hv0] at this; simp [VAL_FALSE] at this
  have hlev : asgAssignmentLevel st.arena st.a.aLevel other r 0 (st.arena.size r).toNat 0 ≤ s0.level := by
    apply asgAssignmentLevel_le _ _ _ _ _ _ _ _ (UInt32.zero_le)
    intro k _ hk hne
    have := H.run.lvl_false H.ctx.levelOK (hfe k hk hne)
    rw [UInt32.le_iff_toNat_le]; exact this
  have hvalid := F.valid other hmem
  generalize asgAssignmentLevel st.arena st.a.aLevel other r 0 (st.arena.size r).toNat 0 = al at ha hlev
  refine RunInv.congr (st := { st with a := st.a.assign probing al false other r }) ?_ ha har hr H.res
  refine H.run.assign H.ctx.lt_len H.res hvalid hun (UInt32.le_iff_toNat_le.mp hlev) _ ?_ ?_
  · intro _ _
    right
    refine ⟨other, hmem, (assign_isTrue H.run.core.sizes hvalid other).mpr (Or.inl rfl), ?_⟩
    rw [assign_lvl H.run.core.sizes hvalid]
    simp only [ite_true]
    exact UInt32.le_iff_toNat_le.mp hlev
  · intro r' _ hn b' hb'; exact hn b' (List.mem_append_left _ hb')

theorem step_large {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {b : Lit} {r : Ref} (H : StepHyp s0 i lit st done rest (.large b r)) (probing jump : Bool)
    (lv : UInt32) :
    RunInv s0 i (NOT lit) (PS.step probing jump lv (NOT lit) st (.large b r))
      (done ++ [.large b r]) := by
  unfold PS.step
  simp only
  by_cases hbt : vTrue (st.a.values.get! b.toNat) = true
  · rw [if_pos hbt]
    refine H.run.keep H.res _ _ rfl rfl H.res ?_
    intro hl
    have F := H.largeFacts hl.2
    have ht := (isTrue_iff_vTrue (V s0 st) b).mpr hbt
    right; exact ⟨b, F.blocking, ht, H.run.lvl_true H.ctx.levelOK ht⟩
  rw [if_neg hbt]
  have hr0 := (H.ctx.ws.refOK _ _ _ H.mem).1
  have hgeq : st.arena.garbage r = s0.arena.garbage r := by
    unfold garbage flag; rw [H.run.arena.word0 r hr0]
  by_cases hg : st.arena.garbage r = true
  · rw [if_pos hg]
    refine H.run.keep H.res _ _ rfl rfl H.res ?_
    intro hl; rw [hgeq, hl.2] at hg; contradiction
  rw [if_neg hg]
  have F := H.largeFacts (by rw [← hgeq]; simpa using hg)
  by_cases hot : vTrue (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat) = true
  · rw [if_pos hot]
    refine H.run.keep H.res _ _ rfl rfl H.res ?_
    intro _
    have ht := (isTrue_iff_vTrue (V s0 st) _).mpr hot
    have hmem : st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit ∈ st.arena.litsL r := by
      rcases F.watch with ⟨_, h⟩ | ⟨_, h⟩
      · rw [← h]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
      · rw [← h]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
    right; exact ⟨_, hmem, ht, H.run.lvl_true H.ctx.levelOK ht⟩
  rw [if_neg hot]
  have SS := search_spec st.arena st.a.values r _ _ F.searched2 F.searchedLt
  simp only at SS
  generalize (if findReplacement st.arena st.a.values r (st.arena.searched r).toNat
      (st.arena.size r).toNat < (st.arena.size r).toNat then
      findReplacement st.arena st.a.values r (st.arena.searched r).toNat (st.arena.size r).toNat
    else if findReplacement st.arena st.a.values r 2 (st.arena.searched r).toNat <
      (st.arena.searched r).toNat then findReplacement st.arena st.a.values r 2 (st.arena.searched r).toNat
    else (st.arena.size r).toNat) = R at SS ⊢
  by_cases hR : R < (st.arena.size r).toNat
  · rw [if_pos hR]; exact step_replace H F R (SS.1 hR).1 hR (SS.1 hR).2 _
  rw [if_neg hR]
  have hall := SS.2 hR
  by_cases h1 : (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat != 0) = true
  · rw [if_pos h1]; exact step_conflict H F hall h1 hot _ rfl rfl rfl
  · rw [if_neg h1]; exact step_unit H F hall h1 probing _ rfl rfl H.res

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- After a conflict only the output list changes. -/
theorem RunInv.extend_conflict {s0 : Solver} {i : Nat} {n : Lit} {st : PS} {d : List WEntry}
    (h : RunInv s0 i n st d) (hres : st.res.isSome) (more : List WEntry) (st' : PS)
    (ha : st'.a = st.a) (har : st'.arena = st.arena) (hr : st'.res = st.res) (hs : st'.s = st.s) :
    RunInv s0 i n st' (d ++ more) := by
  have hV : V s0 st' = V s0 st := by simp [V, ha, har]
  refine ⟨?_, ?_, ?_, ?_, har ▸ h.arena, ?_, fun hn => by rw [hr] at hn; simp [hn] at hres, ?_, ?_, ?_⟩ <;>
    (try rw [hV])
  · exact h.core
  · exact h.trail
  · exact h.extLevel
  · exact h.persist
  · exact h.inv
  · intro r hr' hn; rw [har]
    exact h.untouched r hr' (fun b hb => hn b (List.mem_append_left _ hb))
  · exact h.frames
  · intro c hc; rw [hr] at hc; rw [hs]; exact h.conflict c hc

theorem run_inv {s0 : Solver} {i : Nat} {lit : Lit} (hctx : Ctx s0 i lit) (probing jump : Bool)
    {lv : UInt32} (hlv : lv.toNat ≤ s0.level.toNat) :
    ∀ (es : List WEntry) (st : PS) (done : List WEntry), RunInv s0 i (NOT lit) st done →
    s0.entries (NOT lit) = done ++ es →
    RunInv s0 i (NOT lit) (PS.run probing jump lv (NOT lit) st es) (done ++ es) := by
  intro es
  induction es with
  | nil => intro st done h _; simpa [PS.run] using h
  | cons e es ih =>
    intro st done h hsplit
    by_cases hres : st.res.isSome
    · rw [PS.run_of_res st hres]
      exact h.extend_conflict hres _ _ rfl rfl rfl rfl
    · have hres' : st.res = none := by simpa using hres
      rw [PS.run_cons_none st hres']
      have H : StepHyp s0 i lit st done es e := ⟨hctx, h, hres', hsplit⟩
      have hstep : RunInv s0 i (NOT lit) (PS.step probing jump lv (NOT lit) st e)
          (done ++ [e]) := by
        cases e with
        | bin b => exact step_bin H probing jump hlv
        | large b r => exact step_large H probing jump lv
      have := ih _ _ hstep (by rw [hsplit]; simp)
      simpa using this

theorem countRef_mem (r : Ref) : ∀ (L : List WEntry), 0 < countRef r L → ∃ b, WEntry.large b r ∈ L := by
  intro L
  induction L with
  | nil => intro h; simp [countRef] at h
  | cons e es ih =>
    intro h
    cases e with
    | bin x => obtain ⟨b, hb⟩ := ih (by simpa [countRef] using h); exact ⟨b, List.mem_cons_of_mem _ hb⟩
    | large x r' =>
      by_cases e : r' = r
      · subst e; exact ⟨x, List.mem_cons_self ..⟩
      · obtain ⟨b, hb⟩ := ih (by simpa [countRef, e] using h); exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-- A database clause watched by `NOT lit` is satisfied at the end of the round. -/
theorem RunInv.watched_sat {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} (hctx : Ctx s0 i lit)
    (h : RunInv s0 i (NOT lit) st (s0.entries (NOT lit))) (hres : st.res = none)
    {c : List Lit} (hc : (V s0 st).InDB c) {w0 w1 : Lit} {rs : List Lit} (heq : c = w0 :: w1 :: rs)
    (hw : w0 = NOT lit ∨ w1 = NOT lit) :
    ∃ t ∈ c, (V s0 st).IsTrue t ∧ (V s0 st).lvl t ≤ s0.level.toNat := by
  rcases (inDB_iff _ c).mp hc with ⟨r, hl, rfl⟩ | ⟨x, y, hxy, rfl⟩
  · have hl0 := (h.arena.liveRef r).mp hl
    obtain ⟨e0, e1⟩ := litsL_cons2 (a := st.arena) heq
    have hentry : ∃ b, WEntry.large b r ∈ s0.entries (NOT lit) := by
      apply Classical.byContradiction
      intro hn
      have hn' : ∀ b, WEntry.large b r ∉ s0.entries (NOT lit) := fun b hb => hn ⟨b, hb⟩
      obtain ⟨hL, _⟩ := h.untouched r hl0 hn'
      obtain ⟨f0, f1⟩ := h.lit_eq hctx.ws hl0 (a' := s0.arena) hL.symm (h.arena.size r hl0.1).symm
      obtain ⟨_, _, _, _, hc0, hc1, _⟩ := hctx.ws.live r hl0
      have : 0 < countRef r (s0.entries (NOT lit)) := by
        rcases hw with hw | hw
        · have : s0.lit0 r = NOT lit := by unfold lit0; rw [f0, e0, hw]
          rw [← this]; omega
        · have : s0.lit1 r = NOT lit := by unfold lit1; rw [f1, e1, hw]
          rw [← this]; omega
      exact hn (countRef_mem r _ this)
    obtain ⟨b, hb⟩ := hentry
    rcases h.visit hres _ hb hl0 with ⟨n0, n1⟩ | ⟨t, ht, htt, hlt⟩
    · exfalso
      rcases hw with hw | hw
      · exact n0 (by unfold lit0; simp only [V_arena]; rw [e0, hw])
      · exact n1 (by unfold lit1; simp only [V_arena]; rw [e1, hw])
    · exact ⟨t, ht, htt, hlt⟩
  · simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl, _⟩ := heq
    rcases hw with rfl | rfl
    · have htt : (V s0 st).IsTrue y := h.visit hres (.bin y) hxy
      exact ⟨y, by simp, htt, h.lvl_true hctx.levelOK htt⟩
    · have hyx := (hctx.ws.bin _ _ hxy).1
      have htt : (V s0 st).IsTrue x := h.visit hres (.bin x) hyx
      exact ⟨x, by simp, htt, h.lvl_true hctx.levelOK htt⟩

/-- Advancing the propagation pointer past `lit`. -/
theorem RunInv.propFalse_succ {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {d : List WEntry}
    (hctx : Ctx s0 i lit) (h : RunInv s0 i (NOT lit) st d) {w : Lit} {k : Nat}
    (hf : (V s0 st).PropFalseAt (i + 1) w k) :
    (V s0 st).PropFalseAt i w k ∨ (w = NOT lit ∧ k = s0.level.toNat) := by
  obtain ⟨hfw, ⟨p, hp, hlt, hk⟩ | hroot⟩ := hf
  · by_cases hpi : p < i
    · exact Or.inl ⟨hfw, Or.inl ⟨p, hp, hpi, hk⟩⟩
    · have hpe : p = i := by omega
      subst hpe
      obtain ⟨ext, hext⟩ := h.trail
      have : (V s0 st).trailL[p]? = some lit := by
        rw [hext, List.getElem?_append_left hctx.lt_len]; exact hctx.atI
      rw [this] at hp
      have hw : w = NOT lit := by
        have := congrArg NOT (Option.some.inj hp); rw [NOT_NOT] at this; exact this.symm
      refine Or.inr ⟨hw, ?_⟩
      rw [hk]
      exact hctx.levelOK.pushLevel_cur hctx.propLe
  · exact Or.inl ⟨hfw, Or.inr hroot⟩

/-- The watch invariant at the next pointer after a conflict-free round. -/
theorem RunInv.invNext {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} (hctx : Ctx s0 i lit)
    (h : RunInv s0 i (NOT lit) st (s0.entries (NOT lit))) (hres : st.res = none) :
    ∀ c, (V s0 st).InDB c → (V s0 st).InvSAt (i + 1) c := by
  intro c hc w0 w1 rs heq k0 k1 h0 h1
  rcases h.propFalse_succ hctx h0 with h0' | ⟨hw0, hk0⟩
  · rcases h.propFalse_succ hctx h1 with h1' | ⟨hw1, hk1⟩
    · exact h.inv c hc w0 w1 rs heq k0 k1 h0' h1'
    · obtain ⟨t, ht, htt, hlt⟩ := h.watched_sat hctx hres hc heq (Or.inr hw1)
      exact ⟨t, ht, htt, by omega⟩
  · obtain ⟨t, ht, htt, hlt⟩ := h.watched_sat hctx hres hc heq (Or.inl hw0)
    exact ⟨t, ht, htt, by omega⟩

end Solver
end LeanKissat
