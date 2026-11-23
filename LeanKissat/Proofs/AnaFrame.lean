import LeanKissat.Proofs.Derive
import LeanKissat.Proofs.ArenaSame

/-!
# Analysis frame: states differing only in analysis bookkeeping
-/

namespace LeanKissat
namespace Solver
open Arena

/-- `t` differs from `s` only in analysis bookkeeping (non-binary assignment bits,
  clause usage header bits, temporary stacks, statistics, heuristics). -/
structure AF (t s : Solver) : Prop where
  values : t.asg.values = s.asg.values
  trail : t.asg.trail = s.asg.trail
  aLevel : t.asg.aLevel = s.asg.aLevel
  aReason : t.asg.aReason = s.asg.aReason
  bitsSize : t.asg.aBits.size = s.asg.aBits.size
  binBit : ∀ i, (t.asg.aBits.get! i &&& ABits.binary) = (s.asg.aBits.get! i &&& ABits.binary)
  unassigned : t.asg.unassigned = s.asg.unassigned
  arena : Arena.Same s.arena t.arena
  watches : t.watches = s.watches
  delayed : t.delayed = s.delayed
  vars : t.vars = s.vars
  level : t.level = s.level
  frameTrail : t.frameTrail = s.frameTrail
  propagate : t.propagate = s.propagate
  options : t.options = s.options
  importLit : t.importLit = s.importLit
  inconsistent : t.inconsistent = s.inconsistent
  c0 : t.conflictLit0 = s.conflictLit0
  c1 : t.conflictLit1 = s.conflictLit1
  watching : t.watching = s.watching
  probing : t.probing = s.probing
  importBits : t.importBits = s.importBits

theorem AF.refl (s : Solver) : AF s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, Arena.Same.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem AF.trans {a b c : Solver} (h1 : AF a b) (h2 : AF b c) : AF a c :=
  ⟨h1.values.trans h2.values, h1.trail.trans h2.trail, h1.aLevel.trans h2.aLevel,
   h1.aReason.trans h2.aReason, h1.bitsSize.trans h2.bitsSize,
   fun i => (h1.binBit i).trans (h2.binBit i), h1.unassigned.trans h2.unassigned,
   h2.arena.trans h1.arena, h1.watches.trans h2.watches, h1.delayed.trans h2.delayed,
   h1.vars.trans h2.vars, h1.level.trans h2.level, h1.frameTrail.trans h2.frameTrail,
   h1.propagate.trans h2.propagate, h1.options.trans h2.options, h1.importLit.trans h2.importLit,
   h1.inconsistent.trans h2.inconsistent, h1.c0.trans h2.c0, h1.c1.trans h2.c1,
   h1.watching.trans h2.watching, h1.probing.trans h2.probing, h1.importBits.trans h2.importBits⟩

section
variable {t s : Solver} (h : AF t s)
include h

theorem AF.isTrue : t.IsTrue = s.IsTrue := by funext l; simp [IsTrue, h.values]
theorem AF.isFalse : t.IsFalse = s.IsFalse := by funext l; simp [IsFalse, h.values]
theorem AF.lvl : t.lvl = s.lvl := by funext l; simp [Solver.lvl, h.aLevel]
theorem AF.trailL : t.trailL = s.trailL := by simp [Solver.trailL, h.trail]
theorem AF.reasonOf : t.reasonOf = s.reasonOf := by funext l; simp [Solver.reasonOf, reasonIdx, h.aReason]
theorem AF.binOf : t.binOf = s.binOf := by
  funext l; simp only [Solver.binOf, isBinaryReason, abit, abits]; rw [h.binBit]
theorem AF.entries : t.entries = s.entries := by funext l; simp [Solver.entries, watchesOf, h.watches]
theorem AF.binWatched : t.BinWatched = s.BinWatched := by
  funext a b; simp [Solver.BinWatched, h.entries]
theorem AF.refsL : t.refsL = s.refsL := by unfold Solver.refsL; exact h.arena.chain
theorem AF.liveRef : ∀ r, t.LiveRef r ↔ s.LiveRef r := by
  intro r; unfold LiveRef; rw [h.refsL]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← (h.arena.flags h1).1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [(h.arena.flags h1).1]; exact h2⟩
theorem AF.clauseL : ∀ r, r ∈ s.refsL → t.clauseL r = s.clauseL r := by
  intro r hr; exact h.arena.lits r hr
theorem AF.inDB : ∀ c, t.InDB c ↔ s.InDB c := by
  intro c
  rw [inDB_iff, inDB_iff, h.binWatched]
  constructor
  · rintro (⟨r, hl, rfl⟩ | hb)
    · have hl' := (h.liveRef r).mp hl
      exact Or.inl ⟨r, hl', h.arena.lits r hl'.1⟩
    · exact Or.inr hb
  · rintro (⟨r, hl, rfl⟩ | hb)
    · exact Or.inl ⟨r, (h.liveRef r).mpr hl, (h.arena.lits r hl.1).symm⟩
    · exact Or.inr hb
theorem AF.framesL : t.framesL = s.framesL := by simp [Solver.framesL, h.frameTrail]
theorem AF.pushLevel : t.pushLevel = s.pushLevel := by funext p; simp [Solver.pushLevel, h.framesL]
theorem AF.propFalseAt : t.PropFalseAt = s.PropFalseAt := by
  funext P w k; simp [PropFalseAt, h.isFalse, h.trailL, h.lvl, h.pushLevel]
theorem AF.invSAt : ∀ P c, t.InvSAt P c ↔ s.InvSAt P c := by
  intro P c; simp only [InvSAt, h.propFalseAt, h.isTrue, h.lvl]
theorem AF.ante : t.Ante = s.Ante := by
  funext l x; simp [Ante, Before, h.isFalse, h.lvl, h.trailL]

theorem AF.sinv {Φ : (Nat → Bool) → Prop} (hs : SInv Φ s) : SInv Φ t := by
  have hc := hs.core
  have hL := hs.levelOK
  have hW := hs.ws
  have hcore : t.Core := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; rw [h.isTrue, h.isFalse]; exact hc.valCons l
    · intro l hl; rw [h.isTrue] at hl; rw [h.trailL, h.lvl]; exact hc.trueOnTrail l hl
    · intro l hl; rw [h.trailL] at hl; rw [h.isTrue]; exact hc.trailTrue l hl
    · intro l; rw [h.lvl]; exact hc.lvlVar l
    · unfold Sizes; rw [h.values, h.aLevel, h.vars]; exact hc.sizes
    · intro j; rw [h.values]; exact hc.domain j
  have hlevel : t.LevelOK := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h.isTrue, h.lvl, h.level]; exact hL.trueLe
    · rw [h.trailL, h.lvl, h.pushLevel]; exact hL.pushLe
    · rw [h.framesL]; exact hL.sorted
    · rw [h.framesL, h.level]; exact hL.len
    · rw [h.framesL, h.propagate]; exact hL.framesLe
    · rw [h.trailL, h.propagate]; exact hL.propLe
    · rw [h.framesL]; exact hL.strict
    · rw [h.framesL, h.trailL]; exact hL.framesLt
    · rw [h.frameTrail]; exact hL.frames0
  have hws : t.WatchStruct := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; simp only [watchesOf, h.watches]; exact hW.words l
    · intro l b r hm
      rw [h.entries] at hm
      obtain ⟨h1, h2⟩ := hW.refOK l b r hm
      refine ⟨by rw [h.refsL]; exact h1, fun hg => ?_⟩
      have hg' : s.arena.garbage r = false := by rw [← (h.arena.flags h1).1]; exact hg
      obtain ⟨h3, h4⟩ := h2 hg'
      have e := h.arena.lits r h1
      have hsz := h.arena.size r h1
      have h3sz := (hW.live r ⟨h1, hg'⟩).1
      unfold lit0 lit1 at *
      refine ⟨?_, by show b ∈ t.arena.litsL r; rw [e]; exact h4⟩
      have e0 := lit_eq_of_litsL_eq e (k := 0) (by rw [hsz]; omega)
      have e1 := lit_eq_of_litsL_eq e (k := 1) (by rw [hsz]; omega)
      rw [e0, e1]; exact h3
    · intro r hr
      have hr' := (h.liveRef r).mp hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hW.live r hr'
      have e := h.arena.lits r hr'.1
      have hsz := h.arena.size r hr'.1
      have hse := h.arena.searched r hr'.1
      have e0 := lit_eq_of_litsL_eq e (k := 0) (by rw [hsz]; omega)
      have e1 := lit_eq_of_litsL_eq e (k := 1) (by rw [hsz]; omega)
      have ec : t.clauseL r = s.clauseL r := h.clauseL r hr'.1
      have el0 : t.lit0 r = s.lit0 r := e0
      have el1 : t.lit1 r = s.lit1 r := e1
      refine ⟨by rw [hsz]; exact h1, by rw [ec]; exact h2, by rw [hse]; exact h3,
        by rw [hse, hsz]; exact h4, by rw [h.entries, el0]; exact h5, by rw [h.entries, el1]; exact h6,
        fun x hx => by rw [ec] at hx; unfold ValidLit; rw [h.vars]; exact h7 x hx⟩
    · intro a b hab
      rw [h.binWatched] at hab
      unfold ValidLit; rw [h.binWatched, h.vars]; exact hW.bin a b hab
    · rw [h.delayed]; exact hW.delayed
    · rw [h.watches, h.vars]; exact hW.watchesSize
    · rw [h.vars]; exact hW.varsBound
  have hreasons : t.ReasonOK := by
    intro l hl hlv
    rw [h.isTrue] at hl; rw [h.lvl] at hlv
    have := hs.reasons l hl hlv
    unfold ReasonAt at *
    rw [h.reasonOf, h.binOf, h.binWatched, h.ante]
    rcases this with e | hb | ⟨b1, b2, b3, b4⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨b1, (h.liveRef _).mpr b2, by rw [h.clauseL _ b2.1]; exact b3,
        fun x hx hne => b4 x (by rw [h.clauseL _ b2.1] at hx; exact hx) hne⟩)
  refine ⟨hcore, hlevel, hws, h.arena.layout hs.layout, hreasons, ?_, ?_, ?_, by rw [h.options]; exact hs.jump⟩
  · intro l hl hlv; rw [h.isTrue] at hl; rw [h.lvl] at hlv; exact hs.roots l hl hlv
  · have := hs.rsizes
    unfold ReasonSizes at *
    rw [h.vars, h.aReason, h.bitsSize, h.values, h.unassigned, h.trailL]; exact this
  · intro c hc'; exact hs.db c ((h.inDB c).mp hc')

theorem AF.antecedents : t.Antecedents = s.Antecedents := by
  funext l A
  unfold Antecedents
  rw [h.isTrue, h.lvl, h.binOf, h.binWatched, h.reasonOf]
  apply propext
  constructor
  · rintro ⟨a1, a2, hb | ⟨b1, b2, b3, b4, b5⟩⟩
    · exact ⟨a1, a2, Or.inl hb⟩
    · have b3' := (h.liveRef _).mp b3
      rw [h.clauseL _ b3'.1] at b4 b5
      exact ⟨a1, a2, Or.inr ⟨b1, b2, b3', b4, b5⟩⟩
  · rintro ⟨a1, a2, hb | ⟨b1, b2, b3, b4, b5⟩⟩
    · exact ⟨a1, a2, Or.inl hb⟩
    · exact ⟨a1, a2, Or.inr ⟨b1, b2, (h.liveRef _).mpr b3, by rw [h.clauseL _ b3.1]; exact b4,
        by rw [h.clauseL _ b3.1]; exact b5⟩⟩

theorem AF.derFalse {K : List Lit} {y : Lit} : t.DerFalse K y ↔ s.DerFalse K y := by
  constructor
  · intro hd
    induction hd with
    | inK hy => exact .inK hy
    | root hf h0 => exact .root (by rw [← h.isFalse]; exact hf) (by rw [← h.lvl]; exact h0)
    | reason hA _ ih => exact .reason (by rw [← h.antecedents]; exact hA) ih
  · intro hd
    induction hd with
    | inK hy => exact .inK hy
    | root hf h0 => exact .root (by rw [h.isFalse]; exact hf) (by rw [h.lvl]; exact h0)
    | reason hA _ ih => exact .reason (by rw [h.antecedents]; exact hA) ih

end

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem AF.irrMono {t s : Solver} (h : AF t s) : IrrMono s t := by
  apply IrrMono.of_large
  · intro r h1 h2
    refine ⟨(h.liveRef r).mpr h1, ?_, fun x hx => by rw [h.clauseL r h1.1] at hx; exact hx⟩
    rw [(h.arena.flags h1.1).2.1]; exact h2
  · intro a b hab; rw [h.binWatched]; exact hab
  · intro l ⟨h1, h2⟩; exact ⟨by rw [h.isTrue]; exact h1, by rw [h.lvl]; exact h2⟩

end Solver
end LeanKissat
