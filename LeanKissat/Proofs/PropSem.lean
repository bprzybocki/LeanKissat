import LeanKissat.Proofs.PropSpec

/-!
# Semantics of one propagation round (`PS.run`)

Context: a solver `s0` satisfying the invariants, a trail position `i` with
`s0.propagate ≤ i` holding the literal `lit` being propagated, `notLit = NOT lit`.
`V s0 st` is the solver `s0` with the assignment record and arena of the spec state
`st`. We prove that every step preserves the core invariant, the arena relation, and
the watch invariant at pointer `i`, and establishes the visit condition for its
entry.
-/

namespace LeanKissat
namespace Solver
open Arena

/-- The virtual solver of a spec state. -/
def V (s0 : Solver) (st : PS) : Solver := { s0 with asg := st.a, arena := st.arena }

/-- Clause literal lists of two arenas over the same chain agree up to permutation. -/
structure ArenaRel (a b : Arena) : Prop where
  layout : b.Layout
  sizeWards : b.sizeWards = a.sizeWards
  chain : b.chain 0 b.sizeWards = a.chain 0 a.sizeWards
  word0 : ∀ x ∈ a.chain 0 a.sizeWards, b.word0 x = a.word0 x
  size : ∀ x ∈ a.chain 0 a.sizeWards, b.size x = a.size x
  perm : ∀ x ∈ a.chain 0 a.sizeWards, (b.litsL x).Perm (a.litsL x)

theorem ArenaRel.refl (a : Arena) (h : a.Layout) : ArenaRel a a :=
  ⟨h, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => List.Perm.refl _⟩

theorem clauseL_eq_litsL (s : Solver) (r : Ref) : s.clauseL r = s.arena.litsL r := rfl

/-- The visit condition established for an entry of the watch list of `notLit`. -/
def VisitOK (s0 v : Solver) (notLit : Lit) : WEntry → Prop
  | .bin b => v.IsTrue b
  | .large _ r => s0.LiveRef r →
      (notLit ≠ v.lit0 r ∧ notLit ≠ v.lit1 r) ∨
      (∃ t ∈ v.clauseL r, v.IsTrue t ∧ v.lvl t ≤ s0.level.toNat)

/-- Facts about a conflict found by the run (`s` carries the binary conflict literals). -/
def ConflictOK (v s : Solver) : CRef → Prop
  | .binConflict => v.BinWatched s.conflictLit0 s.conflictLit1 ∧
      v.IsFalse s.conflictLit0 ∧ v.IsFalse s.conflictLit1
  | .large r => v.LiveRef r ∧ ∀ x ∈ v.clauseL r, v.IsFalse x

/-- Invariant of the spec run after processing the entries `done`. -/
structure RunInv (s0 : Solver) (i : Nat) (notLit : Lit) (st : PS) (done : List WEntry) : Prop where
  core : (V s0 st).Core
  trail : ∃ ext, (V s0 st).trailL = s0.trailL ++ ext
  extLevel : ∀ l, (V s0 st).IsTrue l → ¬ s0.IsTrue l → (V s0 st).lvl l ≤ s0.level.toNat
  persist : ∀ l, s0.IsTrue l → (V s0 st).IsTrue l ∧ (V s0 st).lvl l = s0.lvl l
  arena : ArenaRel s0.arena st.arena
  inv : ∀ c, (V s0 st).InDB c → (V s0 st).InvSAt i c
  visit : st.res = none → ∀ e ∈ done, VisitOK s0 (V s0 st) notLit e
  untouched : ∀ r, s0.LiveRef r → (∀ b, WEntry.large b r ∉ done) →
    st.arena.litsL r = s0.arena.litsL r ∧ st.arena.searched r = s0.arena.searched r
  frames : (V s0 st).frameTrail = s0.frameTrail ∧ (V s0 st).propagate = s0.propagate
  conflict : ∀ c, st.res = some c → ConflictOK (V s0 st) st.s c

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem V_withAssign (s0 : Solver) (st : PS) (probing : Bool) (k : UInt32) (binary : Bool)
    (x : Lit) (reason : UInt32) :
    V s0 { st with a := st.a.assign probing k binary x reason } =
      (V s0 st).withAssign probing k binary x reason := rfl

theorem InDB_withAssign (s : Solver) (probing : Bool) (k : UInt32) (binary : Bool) (x : Lit)
    (reason : UInt32) (c : List Lit) :
    (s.withAssign probing k binary x reason).InDB c ↔ s.InDB c := Iff.rfl

theorem lit0_withAssign (s : Solver) (probing : Bool) (k : UInt32) (binary : Bool) (x : Lit)
    (reason : UInt32) (r : Ref) :
    (s.withAssign probing k binary x reason).lit0 r = s.lit0 r := rfl
theorem lit1_withAssign (s : Solver) (probing : Bool) (k : UInt32) (binary : Bool) (x : Lit)
    (reason : UInt32) (r : Ref) :
    (s.withAssign probing k binary x reason).lit1 r = s.lit1 r := rfl

/-- Truth and level of a previously true literal survive an assignment. -/
theorem withAssign_keep {s : Solver} {probing : Bool} {k : UInt32} {binary : Bool} {x : Lit}
    {reason : UInt32} (hc : s.Core) (hx : s.ValidLit x) (hun : ¬ s.IsTrue x ∧ ¬ s.IsFalse x)
    {t : Lit} (ht : s.IsTrue t) :
    (s.withAssign probing k binary x reason).IsTrue t ∧
    (s.withAssign probing k binary x reason).lvl t = s.lvl t := by
  have hs := hc.sizes
  have hnx : ¬ s.IsTrue (NOT x) := by
    intro h; have := (hc.valCons (NOT x)).1.mp h; rw [NOT_NOT] at this; exact hun.2 this
  constructor
  · exact (assign_isTrue hs hx t).mpr (Or.inr ⟨fun e => hnx (e ▸ ht), ht⟩)
  · rw [assign_lvl hs hx]
    by_cases e : IDX t = IDX x
    · rcases (IDX_eq_iff t x).mp e with rfl | rfl
      · exact absurd ht hun.1
      · exact absurd ht hnx
    · simp [e]

/-- An assignment step preserves the run invariant. -/
theorem RunInv.assign {s0 : Solver} {i : Nat} {notLit : Lit} {st : PS} {done : List WEntry}
    (h : RunInv s0 i notLit st done) (hi : i < s0.trailL.length) (hres0 : st.res = none)
    {probing : Bool} {k : UInt32} {binary : Bool} {x : Lit} {reason : UInt32}
    (hx : (V s0 st).ValidLit x) (hun : ¬ (V s0 st).IsTrue x ∧ ¬ (V s0 st).IsFalse x)
    (hk : k.toNat ≤ s0.level.toNat) (e : WEntry)
    (hvisit : st.res = none →
      VisitOK s0 ((V s0 st).withAssign probing k binary x reason) notLit e)
    (huntouched : ∀ r, s0.LiveRef r → (∀ b, WEntry.large b r ∉ done ++ [e]) →
      (∀ b, WEntry.large b r ∉ done)) :
    RunInv s0 i notLit { st with a := st.a.assign probing k binary x reason } (done ++ [e]) := by
  have hc := h.core
  obtain ⟨hc', hxt, hinvP⟩ := assign_core (probing := probing) (level := k) (binary := binary)
    (reason := reason) hc hx hun
  obtain ⟨ext, hext⟩ := h.trail
  refine ⟨by rw [V_withAssign]; exact hc', ?_, ?_, ?_, h.arena, ?_, ?_, ?_, h.frames,
    fun c hc => by simp [hres0] at hc⟩
  all_goals try rw [V_withAssign]
  · exact ⟨ext ++ [x], by rw [assign_trailL, hext, List.append_assoc]⟩
  · intro l hl hl0
    rw [assign_isTrue hc.sizes hx] at hl
    rw [assign_lvl hc.sizes hx]
    rcases hl with rfl | ⟨hne, hl⟩
    · simp; exact hk
    · by_cases e : IDX l = IDX x
      · rcases (IDX_eq_iff l x).mp e with rfl | rfl
        · simp; exact hk
        · exact absurd rfl hne
      · simp only [e, ite_false]; exact h.extLevel l hl hl0
  · intro l hl
    obtain ⟨h1, h2⟩ := h.persist l hl
    obtain ⟨h3, h4⟩ := withAssign_keep hc hx hun h1
    exact ⟨h3, h4.trans h2⟩
  · intro c hcdb
    rw [InDB_withAssign] at hcdb
    have hlen : i ≤ (V s0 st).trailL.length := by rw [hext]; simp; omega
    exact hinvP i c hlen (h.inv c hcdb)
  · intro hres e' he'
    rcases List.mem_append.mp he' with he' | he'
    · have := h.visit hres e' he'
      cases e' with
      | bin b =>
        exact (withAssign_keep hc hx hun this).1
      | large b r =>
        intro hlive
        rcases this hlive with hw | ⟨t, ht, htt, hlt⟩
        · left; simpa [lit0_withAssign, lit1_withAssign] using hw
        · right
          obtain ⟨h3, h4⟩ := withAssign_keep hc hx hun htt
          exact ⟨t, ht, h3, by rw [h4]; exact hlt⟩
    · rw [List.mem_singleton.mp he']; exact hvisit hres
  · intro r hr hnot
    exact h.untouched r hr (huntouched r hr hnot)

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem findReplacement_spec (arena : Arena) (values : ByteArray) (ref : Ref) (i stop : Nat) :
    let r := findReplacement arena values ref i stop
    (r < stop → i ≤ r ∧ vFalse (values.get! (arena.lit ref r).toNat) = false) ∧
    (stop ≤ r → r = stop ∧ ∀ k, i ≤ k → k < stop → vFalse (values.get! (arena.lit ref k).toNat) = true) := by
  fun_induction findReplacement arena values ref i stop with
  | case1 i hi r hr =>
    simp only [Bool.not_eq_true'] at hr
    exact ⟨fun _ => ⟨Nat.le_refl _, hr⟩, fun h => absurd hi (by omega)⟩
  | case2 i hi r hr ih =>
    have hr' : vFalse (values.get! (arena.lit ref i).toNat) = true := by
      simpa using hr
    simp only at ih ⊢
    refine ⟨fun h => ⟨by have := (ih.1 h).1; omega, (ih.1 h).2⟩, fun h => ⟨(ih.2 h).1, ?_⟩⟩
    intro k hk1 hk2
    by_cases e : k = i
    · subst e; exact hr'
    · exact (ih.2 h).2 k (by omega) hk2
  | case3 i hi =>
    exact ⟨fun h => absurd h (by omega), fun _ => ⟨rfl, fun k hk1 hk2 => absurd hk2 (by omega)⟩⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem asgAssignmentLevel_le (arena : Arena) (aLevel : U32Vec) (lit : Lit) (ref : Ref)
    (i n : Nat) (res B : UInt32) (hres : res ≤ B)
    (h : ∀ k, i ≤ k → k < n → arena.lit ref k ≠ lit → aLevel.get! (IDX (arena.lit ref k)).toNat ≤ B) :
    asgAssignmentLevel arena aLevel lit ref i n res ≤ B := by
  fun_induction asgAssignmentLevel arena aLevel lit ref i n res with
  | case1 i res hi other l ih =>
    have hl : l ≤ B := by
      by_cases e : other != lit
      · have : l = aLevel.get! (IDX other).toNat := by simp [l, e]
        rw [this]; exact h i (Nat.le_refl _) hi (by simpa using e)
      · have : l = 0 := by simp [l, e]
        rw [this]; exact UInt32.zero_le
    apply ih
    · split <;> assumption
    · intro k hk1 hk2 hne; exact h k (by omega) hk2 hne
  | case2 i res hi => exact hres

/-- The fixed context of one propagation round. -/
structure Ctx (s0 : Solver) (i : Nat) (lit : Lit) : Prop where
  core : s0.Core
  levelOK : s0.LevelOK
  ws : s0.WatchStruct
  layout : s0.arena.Layout
  atI : s0.trailL[i]? = some lit
  propLe : s0.propagate ≤ i
  inv : ∀ c, s0.InDB c → s0.InvSAt i c
  valid : s0.ValidLit lit

theorem Ctx.lt_len {s0 : Solver} {i : Nat} {lit : Lit} (h : Ctx s0 i lit) : i < s0.trailL.length :=
  (List.getElem?_eq_some_iff.mp h.atI).1

theorem Ctx.litTrue {s0 : Solver} {i : Nat} {lit : Lit} (h : Ctx s0 i lit) : s0.IsTrue lit :=
  h.core.trailTrue lit (List.mem_of_getElem? h.atI)

theorem Ctx.notLitFalse {s0 : Solver} {i : Nat} {lit : Lit} (h : Ctx s0 i lit) :
    s0.IsFalse (NOT lit) := (h.core.valCons lit).1.mp h.litTrue

/-- Initial spec state. -/
def PS.init (s0 : Solver) (cold : Solver) : PS := ⟨[], s0.asg, s0.arena, [], cold, none⟩

theorem RunInv.init {s0 : Solver} {i : Nat} {lit : Lit} (h : Ctx s0 i lit) (cold : Solver) :
    RunInv s0 i (NOT lit) (PS.init s0 cold) [] := by
  have hV : V s0 (PS.init s0 cold) = s0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ArenaRel.refl _ h.layout, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp only [hV]
  · exact h.core
  · exact ⟨[], by simp⟩
  · intro l h1 h2; exact absurd h1 h2
  · intro l hl; exact ⟨hl, by simp⟩
  · exact h.inv
  · intro _ e he; simp at he
  · intro r _ _; exact ⟨rfl, rfl⟩
  · exact ⟨trivial, trivial⟩
  · intro c hc; simp [PS.init] at hc

end Solver
end LeanKissat
