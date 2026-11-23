import LeanKissat.Proofs.Final

/-!
# Initialization (`kissat_init`, `kissat_reserve`) and clause addition (`kissat_add`)
-/

namespace LeanKissat
namespace Solver
open Std.Sat

/-- A solver with `n` variables, no clauses and no assignments. -/
structure Fresh (s : Solver) : Prop where
  small : s.vars.toNat < 2 ^ 30
  values : ∀ j, s.asg.values.get! j = 0
  valuesSize : 2 * s.vars.toNat ≤ s.asg.values.size
  trail : s.asg.trail.size = 0
  aLevel : s.vars.toNat ≤ s.asg.aLevel.size
  aReason : s.vars.toNat ≤ s.asg.aReason.size
  aBits : ∀ j, s.asg.aBits.get! j = 0
  aBitsSize : s.vars.toNat ≤ s.asg.aBits.size
  unassigned : s.asg.unassigned.toNat = s.vars.toNat
  arena : s.arena.words.size = 0
  watches : ∀ j : Nat, ((s.watches[j]! : WVec)).data.size = 0
  watchesSize : 2 * s.vars.toNat ≤ s.watches.size
  delayed : s.delayed.size = 0
  level : s.level = 0
  frameTrail : s.frameTrail.size = 1
  propagate : s.propagate = 0

theorem Fresh.entries {s : Solver} (h : s.Fresh) (l : Lit) : s.entries l = [] := by
  unfold Solver.entries watchesOf
  have := h.watches l.toNat
  have e : ((s.watches[l.toNat]! : WVec)).data.toList = [] := by
    apply List.eq_nil_of_length_eq_zero; simpa using this
  rw [e]; rfl

theorem Fresh.refsL {s : Solver} (h : s.Fresh) : s.refsL = [] := by
  unfold Solver.refsL
  have : s.arena.sizeWards = 0 := by unfold Arena.sizeWards; rw [h.arena]
  rw [this]; rfl

theorem Fresh.not_inDB {s : Solver} (h : s.Fresh) (c : List Lit) : ¬ s.InDB c := by
  rintro (⟨r, ⟨hr, _⟩, _⟩ | ⟨a, b, hab, _⟩)
  · rw [h.refsL] at hr; simp at hr
  · unfold BinWatched at hab; rw [h.entries] at hab; simp at hab

theorem Fresh.not_true {s : Solver} (h : s.Fresh) (l : Lit) : ¬ s.IsTrue l := by
  unfold IsTrue; rw [h.values]; decide

theorem Fresh.not_false {s : Solver} (h : s.Fresh) (l : Lit) : ¬ s.IsFalse l := by
  unfold IsFalse; rw [h.values]; decide

theorem Fresh.trailL {s : Solver} (h : s.Fresh) : s.trailL = [] := by
  apply List.eq_nil_of_length_eq_zero; rw [length_trailL, h.trail]

theorem Fresh.framesL {s : Solver} (h : s.Fresh) : s.framesL = [] := by
  unfold Solver.framesL
  apply List.eq_nil_of_length_eq_zero
  simp [h.frameTrail]

theorem Fresh.sinv {Φ : (Nat → Bool) → Prop} {s : Solver} (h : s.Fresh) (hj : s.options.jumpreasons = 0) :
    SInv Φ s := by
  have hT := h.not_true
  have hF := h.not_false
  have hTr := h.trailL
  have hFr := h.framesL
  refine ⟨⟨fun l => ⟨⟨fun e => absurd e (hT _), fun e => absurd e (hF _)⟩, fun ⟨e, _⟩ => hT _ e⟩,
      fun l e => absurd e (hT l), fun l hl => by rw [hTr] at hl; simp at hl, fun l => by
        unfold lvl; rw [IDX_NOT], ⟨h.valuesSize, h.aLevel⟩, fun j => Or.inl (h.values j)⟩,
    ⟨fun l e => absurd e (hT l), fun p l hp => by rw [hTr] at hp; simp at hp, by rw [hFr]; simp,
      by rw [hFr, h.level]; rfl, fun f hf => by rw [hFr] at hf; simp at hf,
      by rw [hTr, h.propagate]; exact Nat.le_refl _, by rw [hFr]; simp, fun f hf => by rw [hFr] at hf; simp at hf,
      by rw [h.frameTrail]; exact Nat.le_refl _⟩,
    ⟨fun l => by unfold watchesOf; have := h.watches l.toNat
                 rw [show ((s.watches[l.toNat]! : WVec)).data.toList = [] from
                   List.eq_nil_of_length_eq_zero (by simpa using this)]; trivial,
      fun l b r hm => by rw [h.entries] at hm; simp at hm,
      fun r hr => by rw [LiveRef, h.refsL] at hr; simp at hr,
      fun a b hab => by unfold BinWatched at hab; rw [h.entries] at hab; simp at hab,
      h.delayed, h.watchesSize, h.small⟩,
    ⟨by
      have e : s.arena.sizeWards = 0 := by unfold Arena.sizeWards; rw [h.arena]
      rw [e]; show Arena.LayoutFrom s.arena 0 []; unfold Arena.LayoutFrom; rw [e]; rfl, by
      unfold Arena.sizeWards; rw [h.arena], by unfold Arena.sizeWards; rw [h.arena]; simp⟩,
    fun l e => absurd e (hT l), fun l e => absurd e (hT l),
    ⟨h.aReason, h.aBitsSize, fun j _ => h.values j, by
      rw [h.unassigned]
      have : (List.range s.vars.toNat).countP (fun v => s.asg.values.get! (2 * v) != 0) = 0 := by
        rw [List.countP_eq_zero]; intro v _; simp [h.values]
      omega, by rw [hTr]; simp⟩,
    fun c hc => absurd hc (h.not_inDB c), hj⟩

end Solver

theorem ByteArray.get!_push (b : ByteArray) (v : UInt8) (j : Nat) :
    (b.push v).get! j = if j < b.size then b.get! j else if j = b.size then v else 0 := by
  cases b with
  | mk data =>
    show (data.push v)[j]! = if j < data.size then data[j]! else if j = data.size then v else 0
    by_cases hj : j < data.size
    · simp [hj, Array.getElem_push, show j < data.size + 1 by omega]
    · by_cases he : j = data.size
      · subst he; simp
      · have : ¬ j < data.size + 1 := by omega
        simp [hj, he, this]; rfl

namespace Solver

theorem growBytes_size (b : ByteArray) (n : Nat) : (growBytes b n).size = max b.size n := by
  fun_induction growBytes b n with
  | case1 b h ih => rw [ih]; simp [ByteArray.size_push]; omega
  | case2 b h => omega

theorem growBytes_zero (b : ByteArray) (n : Nat) (h : ∀ j, b.get! j = 0) : ∀ j, (growBytes b n).get! j = 0 := by
  fun_induction growBytes b n with
  | case1 b hb ih =>
    apply ih; intro j; rw [ByteArray.get!_push]; split
    · exact h j
    · split <;> rfl
  | case2 b hb => exact h

theorem growBytes_get (b : ByteArray) (n : Nat) (j : Nat) :
    (growBytes b n).get! j = if j < b.size then b.get! j else 0 := by
  fun_induction growBytes b n with
  | case1 b hb ih =>
    rw [ih, ByteArray.get!_push]; simp only [ByteArray.size_push]
    by_cases h1 : j < b.size
    · simp [h1, show j < b.size + 1 by omega]
    · by_cases h2 : j = b.size
      · subst h2; simp
      · simp [h1, h2, show ¬ j < b.size + 1 by omega]
  | case2 b hb =>
    split
    · rfl
    · exact ByteArray.get!_oob _ _ ‹_›

theorem growU32_size (a : U32Vec) (n : Nat) (v : UInt32) : (growU32 a n v).size = max a.size n := by
  fun_induction growU32 a n v with
  | case1 a h ih => rw [ih]; simp [U32Vec.size_push]; omega
  | case2 a h => omega

theorem growU32_get (a : U32Vec) (n : Nat) (v : UInt32) (j : Nat) :
    (growU32 a n v).get! j = if j < a.size then a.get! j else if j < n then v else 0 := by
  fun_induction growU32 a n v with
  | case1 a h ih =>
    rw [ih, U32Vec.get!_push]; simp only [U32Vec.size_push]
    by_cases h1 : j < a.size
    · simp [h1, show j < a.size + 1 by omega]
    · by_cases h2 : j = a.size
      · subst h2; simp [h]
      · simp [h1, h2, show ¬ j < a.size + 1 by omega]
  | case2 a h =>
    by_cases h1 : j < a.size
    · simp [h1]
    · simp [h1, show ¬ j < n by omega, U32Vec.get!_eq]

/-- The import functions only touch the import/export maps, `vars` and statistics. -/
structure IFr (t s : Solver) : Prop where
  asg : t.asg = s.asg
  arena : t.arena = s.arena
  watches : t.watches = s.watches
  delayed : t.delayed = s.delayed
  level : t.level = s.level
  frameTrail : t.frameTrail = s.frameTrail
  propagate : t.propagate = s.propagate
  options : t.options = s.options
  clause : t.clause = s.clause
  marks : t.marks = s.marks
  inconsistent : t.inconsistent = s.inconsistent
  watching : t.watching = s.watching
  flags : t.flags = s.flags
  size : t.size = s.size
  probing : t.probing = s.probing
  stable : t.stable = s.stable
  cs : t.clauseSatisfied = s.clauseSatisfied
  ct : t.clauseTrivial = s.clauseTrivial
  csh : t.clauseShrink = s.clauseShrink
  overflowed : t.overflowed = s.overflowed
  outOfResources : t.outOfResources = s.outOfResources
  notPorted : t.notPorted = s.notPorted

theorem IFr.refl (s : Solver) : IFr s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem IFr.trans {a b c : Solver} (h1 : IFr a b) (h2 : IFr b c) : IFr a c :=
  ⟨h1.asg.trans h2.asg, h1.arena.trans h2.arena, h1.watches.trans h2.watches, h1.delayed.trans h2.delayed,
   h1.level.trans h2.level, h1.frameTrail.trans h2.frameTrail, h1.propagate.trans h2.propagate,
   h1.options.trans h2.options, h1.clause.trans h2.clause, h1.marks.trans h2.marks,
   h1.inconsistent.trans h2.inconsistent, h1.watching.trans h2.watching, h1.flags.trans h2.flags,
   h1.size.trans h2.size, h1.probing.trans h2.probing, h1.stable.trans h2.stable, h1.cs.trans h2.cs,
   h1.ct.trans h2.ct, h1.csh.trans h2.csh, h1.overflowed.trans h2.overflowed,
   h1.outOfResources.trans h2.outOfResources, h1.notPorted.trans h2.notPorted⟩

macro "ifr_rfl" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem enlargeVariables_noinc (s : Solver) (h1 : s.vars < s.vars + 1) (h2 : (s.vars + 1).toNat ≤ s.size.toNat) :
    s.enlargeVariables (s.vars + 1) = { s with vars := s.vars + 1 } := by
  unfold enlargeVariables
  have h1' := UInt32.lt_iff_toNat_lt.mp h1
  rw [if_neg (by simp only [ge_iff_le, UInt32.le_iff_toNat_le]; omega)]
  dsimp only
  rw [if_neg (by omega)]

/-- Importing the next external variable `e = vars + 1` (its entry is new). -/
theorem importLiteralAux_next (s : Solver) (e : Nat) (hsz : s.importLit.size = e) (hbs : s.importBits.size = e)
    (hv : s.vars.toNat + 1 = e) (hsize : e ≤ s.size.toNat) (he : e < 2 ^ 31) :
    (s.importLiteralAux (e : Int) false).1 = 2 * s.vars ∧
    (s.importLiteralAux (e : Int) false).2.vars = s.vars + 1 ∧
    (s.importLiteralAux (e : Int) false).2.importLit = (growU32 s.importLit (e + 1)).set! e (2 * s.vars) ∧
    (s.importLiteralAux (e : Int) false).2.importBits =
      (growBytes s.importBits (e + 1)).set! e ImportBits.imported ∧
    IFr (s.importLiteralAux (e : Int) false).2 s := by
  have hn : (e : Int).natAbs = e := by omega
  unfold importLiteralAux
  simp only [hn]
  have hA : s.adjustImports e = { s with importLit := growU32 s.importLit (e + 1), importBits := growBytes s.importBits (e + 1) } := by
    unfold adjustImports; rw [if_neg (by omega)]
  rw [hA]
  have hb0 : (growBytes s.importBits (e + 1)).get! e = 0 := by
    rw [growBytes_get, if_neg (by omega)]
  generalize hs1 : ({ s with importLit := growU32 s.importLit (e + 1), importBits := growBytes s.importBits (e + 1) } : Solver) = s1
  have e1 : s1.importBitsAt e = 0 := by rw [← hs1]; exact hb0
  have s1v : s1.vars = s.vars := by rw [← hs1]
  have s1s : s1.size = s.size := by rw [← hs1]
  have s1il : s1.importLit = growU32 s.importLit (e + 1) := by rw [← hs1]
  have s1ib : s1.importBits = growBytes s.importBits (e + 1) := by rw [← hs1]
  have fr1 : IFr s1 s := by rw [← hs1]; ifr_rfl
  simp only [e1, UInt8.zero_and, bne_self_eq_false, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  have hneg : ¬ ((e : Int) < 0) := by omega
  simp only [hneg, ite_false]
  unfold adjustExports
  dsimp only
  have hlt : s1.vars < s1.vars + 1 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, s1v]; simp; omega
  have hle : (s1.vars + 1).toNat ≤ s1.size.toNat := by
    rw [UInt32.toNat_add, s1s, s1v]; simp; omega
  rw [enlargeVariables_noinc s1 hlt hle]
  have hil : ((growU32 s.importLit (e + 1)).set! e (2 * s.vars)).get! e = 2 * s.vars := by
    rw [U32Vec.get!_set!]; simp [growU32_size]; omega
  simp only [Bool.false_eq_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [s1v, s1il, hil]
  · simp only [s1v]
  · simp only [s1v, s1il]
  · simp only [s1ib]; simp [ImportBits.imported]
  · exact (show IFr _ s1 by ifr_rfl).trans fr1

/-- The import maps after importing the external variables `1..k`. -/
def ImpMap (s : Solver) (k : Nat) : Prop :=
  (k = 0 → s.importLit.size = 0 ∧ s.importBits.size = 0) ∧
  (0 < k → s.importLit.size = k + 1 ∧ s.importBits.size = k + 1) ∧
  ∀ e, 1 ≤ e → e ≤ k → s.importLit.get! e = 2 * UInt32.ofNat (e - 1) ∧ s.importBits.get! e = ImportBits.imported

theorem importLiteral_next (s : Solver) (k : Nat) (hm : ImpMap s k) (hv : s.vars.toNat = k)
    (hsize : k + 1 ≤ s.size.toNat) (ht : s.options.tumble = 0) (hk : k + 1 < 2 ^ 31) :
    ImpMap (s.importLiteral ((k + 1 : Nat) : Int)).2 (k + 1) ∧
    (s.importLiteral ((k + 1 : Nat) : Int)).2.vars.toNat = k + 1 ∧ IFr (s.importLiteral ((k + 1 : Nat) : Int)).2 s := by
  obtain ⟨h0, hpos, hent⟩ := hm
  have hn : ((k + 1 : Nat) : Int).natAbs = k + 1 := by omega
  -- the state handed to `importUpTo`, with maps of size `k + 1`
  have key : ∀ u : Solver, u.importLit.size = k + 1 → u.importBits.size = k + 1 → u.vars = s.vars →
      u.size = s.size → IFr u s →
      (∀ e, 1 ≤ e → e ≤ k → u.importLit.get! e = 2 * UInt32.ofNat (e - 1) ∧ u.importBits.get! e = ImportBits.imported) →
      ImpMap (importUpTo u (k + 1) (k + 1) 0).2 (k + 1) ∧ (importUpTo u (k + 1) (k + 1) 0).2.vars.toNat = k + 1 ∧
      IFr (importUpTo u (k + 1) (k + 1) 0).2 s := by
    intro u h1 h2 h3 h4 h5 h6
    rw [importUpTo, dif_pos (Nat.le_refl _)]
    obtain ⟨a1, a2, a3, a4, a5⟩ := importLiteralAux_next u (k + 1) h1 h2 (by rw [h3, hv]) (by rw [h4]; exact hsize) hk
    generalize u.importLiteralAux ((k + 1 : Nat) : Int) false = R at a1 a2 a3 a4 a5
    obtain ⟨il, w⟩ := R
    dsimp only at a1 a2 a3 a4 a5 ⊢
    rw [importUpTo, dif_neg (by omega)]
    dsimp only
    have hvars : w.vars.toNat = k + 1 := by rw [a2, UInt32.toNat_add, h3, hv]; simp; omega
    refine ⟨⟨fun e => by omega, fun _ => ⟨by rw [a3]; simp [growU32_size]; omega,
      by rw [a4]; simp [growBytes_size, ByteArray.size_set!']; omega⟩, fun e he1 he2 => ?_⟩, hvars, a5.trans h5⟩
    rw [a3, a4]
    by_cases ee : e = k + 1
    · subst ee
      constructor
      · have hsv : s.vars = UInt32.ofNat k := by apply UInt32.toNat_inj.mp; simp; omega
        rw [U32Vec.get!_set!]; simp only [U32Vec.size_set!, growU32_size]
        rw [if_pos (by simp; omega), h3, hsv]; simp
      · rw [ByteArray.get!_set!]; simp [growBytes_size, h2]
    · have he3 : e ≤ k := by omega
      obtain ⟨g1, g2⟩ := h6 e he1 he3
      constructor
      · rw [U32Vec.get!_set!_ne _ _ _ _ (Ne.symm ee), growU32_get, if_pos (by omega), g1]
      · rw [ByteArray.get!_set!_ne _ _ _ _ (Ne.symm ee), growBytes_get, if_pos (by omega), g2]
  unfold importLiteral
  rw [if_neg (by simp [ht]), hn]
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨z1, z2⟩ := h0 rfl
    rw [if_neg (by omega)]
    simp only [z1, beq_self_eq_true, ite_true]
    have hA : s.adjustImports 0 = { s with importLit := growU32 s.importLit 1, importBits := growBytes s.importBits 1 } := by
      unfold adjustImports; rw [if_neg (by omega)]
    rw [hA]
    have := key { s with importLit := growU32 s.importLit 1, importBits := growBytes s.importBits 1 }
      (by simp [growU32_size, z1]) (by simp [growBytes_size, z2]) rfl rfl (by ifr_rfl) (fun e h1 h2 => by omega)
    simpa using this
  · obtain ⟨z1, z2⟩ := hpos (by omega)
    rw [if_neg (by omega)]
    simp only [z1, show (k + 1 == 0) = false by simp, Bool.false_eq_true, ite_false]
    have := key s z1 z2 rfl rfl (IFr.refl _) hent
    simpa using this

theorem reserveImport_spec (n : Nat) (hn : n < 2 ^ 30) : ∀ (s : Solver) (idx : Nat), 1 ≤ idx → idx ≤ n + 1 →
    ImpMap s (idx - 1) → s.vars.toNat = idx - 1 → n ≤ s.size.toNat → s.options.tumble = 0 →
    ImpMap (s.reserveImport idx n) n ∧ (s.reserveImport idx n).vars.toNat = n ∧ IFr (s.reserveImport idx n) s := by
  intro s idx
  fun_induction reserveImport s idx n with
  | case1 s idx h ih =>
    intro h1 h2 hm hv hsz ht
    have k1 : idx - 1 + 1 = idx := by omega
    obtain ⟨m1, m2, m3⟩ := importLiteral_next s (idx - 1) hm hv (by omega) ht (by omega)
    rw [k1] at m1 m2 m3
    obtain ⟨r1, r2, r3⟩ := ih (by omega) (by omega) (by simpa using m1) (by rw [m2]; omega)
      (by rw [m3.size]; exact hsz) (by rw [m3.options]; exact ht)
    exact ⟨r1, r2, r3.trans m3⟩
  | case2 s idx h =>
    intro h1 h2 hm hv _ _
    have : idx = n + 1 := by omega
    subst this
    exact ⟨by simpa using hm, by rw [hv]; simp, IFr.refl _⟩

/-- Activation only touches the flags, counters, heuristics and `unassigned`. -/
structure AFr (t s : Solver) : Prop where
  values : t.asg.values = s.asg.values
  trail : t.asg.trail = s.asg.trail
  aLevel : t.asg.aLevel = s.asg.aLevel
  aReason : t.asg.aReason = s.asg.aReason
  aBits : t.asg.aBits = s.asg.aBits
  arena : t.arena = s.arena
  watches : t.watches = s.watches
  delayed : t.delayed = s.delayed
  vars : t.vars = s.vars
  level : t.level = s.level
  frameTrail : t.frameTrail = s.frameTrail
  propagate : t.propagate = s.propagate
  options : t.options = s.options
  clause : t.clause = s.clause
  marks : t.marks = s.marks
  inconsistent : t.inconsistent = s.inconsistent
  watching : t.watching = s.watching
  importLit : t.importLit = s.importLit
  importBits : t.importBits = s.importBits
  stable : t.stable = s.stable
  cs : t.clauseSatisfied = s.clauseSatisfied
  ct : t.clauseTrivial = s.clauseTrivial
  csh : t.clauseShrink = s.clauseShrink
  overflowed : t.overflowed = s.overflowed
  outOfResources : t.outOfResources = s.outOfResources
  notPorted : t.notPorted = s.notPorted
  probing : t.probing = s.probing

theorem AFr.refl (s : Solver) : AFr s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem AFr.trans {a b c : Solver} (h1 : AFr a b) (h2 : AFr b c) : AFr a c :=
  ⟨h1.values.trans h2.values, h1.trail.trans h2.trail, h1.aLevel.trans h2.aLevel, h1.aReason.trans h2.aReason,
   h1.aBits.trans h2.aBits, h1.arena.trans h2.arena, h1.watches.trans h2.watches, h1.delayed.trans h2.delayed,
   h1.vars.trans h2.vars, h1.level.trans h2.level, h1.frameTrail.trans h2.frameTrail,
   h1.propagate.trans h2.propagate, h1.options.trans h2.options, h1.clause.trans h2.clause,
   h1.marks.trans h2.marks, h1.inconsistent.trans h2.inconsistent, h1.watching.trans h2.watching,
   h1.importLit.trans h2.importLit, h1.importBits.trans h2.importBits, h1.stable.trans h2.stable,
   h1.cs.trans h2.cs, h1.ct.trans h2.ct, h1.csh.trans h2.csh, h1.overflowed.trans h2.overflowed,
   h1.outOfResources.trans h2.outOfResources, h1.notPorted.trans h2.notPorted, h1.probing.trans h2.probing⟩

macro "afr_rfl" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem markRemovedLiteral_flags (s : Solver) (lit : Lit) :
    AFr (s.markRemovedLiteral lit) s ∧ (s.markRemovedLiteral lit).asg.unassigned = s.asg.unassigned ∧
    (∀ j, j ≠ (IDX lit).toNat → (s.markRemovedLiteral lit).flags.get! j = s.flags.get! j) ∧
    (s.isActive (IDX lit) = true → (s.markRemovedLiteral lit).isActive (IDX lit) = true) := by
  unfold markRemovedLiteral
  dsimp only
  split
  · exact ⟨AFr.refl _, rfl, fun _ _ => rfl, id⟩
  split
  · refine ⟨by afr_rfl, rfl, fun j hj => ?_, fun h => ?_⟩
    · simp only [setVarFlag]; rw [U32Vec.get!_set!_ne _ _ _ _ (Ne.symm hj)]
    · simp only [isActive, varFlags, setVarFlag] at h ⊢
      rw [U32Vec.get!_set!]; split
      · simp only [ite_true]; revert h; generalize s.flags.get! (IDX lit).toNat = w; intro h; simp at h ⊢; bv_k
      · exact h
  · exact ⟨AFr.refl _, rfl, fun _ _ => rfl, id⟩

theorem or_active (w b : UInt32) (h : (w &&& VarFlags.active != 0) = true) :
    ((w ||| b) &&& VarFlags.active != 0) = true := by
  simp only [bne_iff_ne, ne_eq] at *; intro e; apply h; revert e; unfold VarFlags.active; bv_k

theorem markFlagBit_get (p : U32Vec × Counters) (i : Nat) (bit : UInt32) (c : Nat) (j : Nat) :
    ((markFlagBit p i bit c).1.get! j = p.1.get! j ∨ j = i) ∧
    ((p.1.get! i &&& VarFlags.active != 0) = true → ((markFlagBit p i bit c).1.get! i &&& VarFlags.active != 0) = true) := by
  unfold markFlagBit
  split
  · constructor
    · by_cases hj : j = i
      · exact Or.inr hj
      · left; exact U32Vec.get!_set!_ne _ _ _ _ (Ne.symm hj)
    · intro h; dsimp only; rw [U32Vec.get!_set!]; split
      · exact or_active _ _ h
      · exact h
  · exact ⟨Or.inl rfl, id⟩

theorem markAddedFlags_get (flags : U32Vec) (stats : Counters) (lit : Lit) (j : Nat) :
    ((markAddedFlags flags stats lit).1.get! j = flags.get! j ∨ j = (IDX lit).toNat) ∧
    ((flags.get! (IDX lit).toNat &&& VarFlags.active != 0) = true →
      ((markAddedFlags flags stats lit).1.get! (IDX lit).toNat &&& VarFlags.active != 0) = true) := by
  unfold markAddedFlags
  dsimp only
  obtain ⟨a1, a2⟩ := markFlagBit_get (flags, stats) (IDX lit).toNat VarFlags.subsume Counters.idx_variables_subsume j
  generalize markFlagBit (flags, stats) (IDX lit).toNat VarFlags.subsume Counters.idx_variables_subsume = p at a1 a2
  obtain ⟨b1, b2⟩ := markFlagBit_get p (IDX lit).toNat
    ((1 : UInt32) <<< (if NEGATED lit then (1 : UInt32) else 0) <<< VarFlags.factorShift) Counters.idx_literals_factor j
  refine ⟨?_, fun h => b2 (a2 h)⟩
  rcases b1 with e | e
  · rw [e]; exact a1
  · exact Or.inr e

theorem markAddedLiteral_flags (s : Solver) (lit : Lit) :
    AFr (s.markAddedLiteral lit) s ∧ (s.markAddedLiteral lit).asg.unassigned = s.asg.unassigned ∧
    (∀ j, j ≠ (IDX lit).toNat → (s.markAddedLiteral lit).flags.get! j = s.flags.get! j) ∧
    (s.isActive (IDX lit) = true → (s.markAddedLiteral lit).isActive (IDX lit) = true) := by
  have hf : (s.markAddedLiteral lit).flags = (markAddedFlags s.flags s.stats lit).1 := rfl
  refine ⟨by afr_rfl, rfl, fun j hj => ?_, fun h => ?_⟩
  · rw [hf]; rcases (markAddedFlags_get s.flags s.stats lit j).1 with e | e
    · exact e
    · exact absurd e hj
  · unfold isActive varFlags at *; rw [hf]; exact (markAddedFlags_get s.flags s.stats lit 0).2 h

theorem IDX_LIT' (idx : UInt32) (h : idx.toNat < 2 ^ 31) : IDX (LIT idx) = idx :=
  UInt32.toNat_inj.mp (IDX_LIT_toNat idx h)

theorem activateCore_spec (s : Solver) (idx : UInt32) (hfs : idx.toNat < s.flags.size) :
    AFr (s.activateCore idx) s ∧ (s.activateCore idx).asg.unassigned = s.asg.unassigned + 1 ∧
    (s.activateCore idx).isActive idx = true ∧
    (∀ j, j ≠ idx.toNat → (s.activateCore idx).flags.get! j = s.flags.get! j) := by
  have hf : (s.activateCore idx).flags = (s.setVarFlag idx VarFlags.active true).flags := rfl
  have ha : AFr (s.activateCore idx) s := by afr_rfl
  have hu : (s.activateCore idx).asg.unassigned = s.asg.unassigned + 1 := rfl
  refine ⟨ha, hu, ?_, fun j hj => ?_⟩
  · unfold isActive varFlags; rw [hf]; simp only [setVarFlag, varFlags, ite_true]
    rw [U32Vec.get!_set!]; split
    · simp only [bne_iff_ne, ne_eq]; unfold VarFlags.active; generalize s.flags.get! idx.toNat = w; bv_k
    · rename_i hn; exfalso; apply hn; exact ⟨rfl, hfs⟩
  · rw [hf]; simp only [setVarFlag]; exact U32Vec.get!_set!_ne _ _ _ _ (Ne.symm hj)

theorem activateLiteral_spec (s : Solver) (idx : UInt32) (hidx : idx.toNat < 2 ^ 31)
    (hfs : idx.toNat < s.flags.size) (hna : s.isActive idx = false) :
    AFr (s.activateLiteral (LIT idx)) s ∧
    (s.activateLiteral (LIT idx)).asg.unassigned = s.asg.unassigned + 1 ∧
    (s.activateLiteral (LIT idx)).isActive idx = true ∧
    (∀ j, j ≠ idx.toNat → (s.activateLiteral (LIT idx)).flags.get! j = s.flags.get! j) := by
  have hI := IDX_LIT' idx hidx
  unfold activateLiteral
  rw [hI, if_neg (by simp [hna])]
  have hS : IDX (STRIP (LIT idx)) = idx := by
    unfold STRIP; rw [show LIT idx &&& ~~~1 = LIT idx by unfold LIT; bv_k]; exact hI
  obtain ⟨h1, h2, h3, h4⟩ := activateCore_spec s idx hfs
  generalize s.activateCore idx = X at h1 h2 h3 h4
  obtain ⟨r1, r2, r3, r4⟩ := markRemovedLiteral_flags X (STRIP (LIT idx))
  obtain ⟨q1, q2, q3, q4⟩ := markAddedLiteral_flags (X.markRemovedLiteral (STRIP (LIT idx))) (STRIP (LIT idx))
  rw [hS] at r3 r4 q3 q4
  exact ⟨q1.trans (r1.trans h1), by rw [q2, r2, h2], q4 (r4 h3), fun j hj => by rw [q3 j hj, r3 j hj, h4 j hj]⟩

theorem activateLiteral_flagsSize (s : Solver) (lit : Lit) : (s.activateLiteral lit).flags.size = s.flags.size := by
  unfold activateLiteral
  dsimp only
  split
  · rfl
  · have h1 : (s.activateCore (IDX lit)).flags.size = s.flags.size := by
      show (s.setVarFlag (IDX lit) VarFlags.active true).flags.size = _; simp [setVarFlag]
    have h2 : ∀ u : Solver, (u.markRemovedLiteral (STRIP lit)).flags.size = u.flags.size := by
      intro u; unfold markRemovedLiteral; dsimp only; split
      · rfl
      · split
        · simp [setVarFlag]
        · rfl
    have hb : ∀ (p : U32Vec × Counters) (i : Nat) (b : UInt32) (c : Nat), (markFlagBit p i b c).1.size = p.1.size := by
      intro p i b c; unfold markFlagBit; split <;> simp
    have h3 : ∀ u : Solver, (u.markAddedLiteral (STRIP lit)).flags.size = u.flags.size := by
      intro u; show (markAddedFlags u.flags u.stats (STRIP lit)).1.size = _
      unfold markAddedFlags; dsimp only; rw [hb, hb]
    rw [h3, h2, h1]

theorem reserveActivate_spec (n : Nat) (hn : n < 2 ^ 30) : ∀ (s : Solver) (idx : Nat), idx ≤ n →
    (∀ v, v < n → (s.isActive (UInt32.ofNat v) = true ↔ v < idx)) → n ≤ s.flags.size →
    s.asg.unassigned.toNat = idx →
    AFr (s.reserveActivate idx n) s ∧
    (s.reserveActivate idx n).asg.unassigned.toNat = n ∧
    (∀ v, v < n → (s.reserveActivate idx n).isActive (UInt32.ofNat v) = true) ∧
    (s.reserveActivate idx n).flags.size = s.flags.size := by
  intro s idx
  fun_induction reserveActivate s idx n with
  | case1 s idx h ih =>
    intro _ hact hfs hu0
    have hidx : (UInt32.ofNat idx).toNat = idx := by simp; omega
    have hna : s.isActive (UInt32.ofNat idx) = false := by
      cases e : s.isActive (UInt32.ofNat idx)
      · rfl
      · have := (hact idx h).mp e; omega
    obtain ⟨a1, a2, a3, a4⟩ := activateLiteral_spec s (UInt32.ofNat idx) (by omega) (by omega) hna
    have hsz := activateLiteral_flagsSize s (LIT (UInt32.ofNat idx))
    obtain ⟨r1, r2, r3, r4⟩ := ih (by omega) (fun v hv => by
        by_cases e : v = idx
        · subst e; simp [a3]
        · have hv' : (UInt32.ofNat v).toNat = v := by simp; omega
          have : (s.activateLiteral (LIT (UInt32.ofNat idx))).isActive (UInt32.ofNat v) = s.isActive (UInt32.ofNat v) := by
            unfold isActive varFlags; rw [a4 _ (by rw [hv', hidx]; exact e)]
          rw [this, hact v hv]; omega) (by rw [hsz]; exact hfs) (by rw [a2, UInt32.toNat_add, hu0]; simp; omega)
    exact ⟨r1.trans a1, r2, r3, by rw [r4, hsz]⟩
  | case2 s idx h =>
    intro hle hact _ hu0
    refine ⟨AFr.refl _, by omega, fun v hv => (hact v hv).mpr (by omega), rfl⟩

/-- `kissat_increase_size` on a solver with empty per-variable arrays. -/
structure Grown (t s : Solver) (n : Nat) : Prop where
  ifr : IFr { t with size := s.size, asg := s.asg, watches := s.watches, flags := s.flags, marks := s.marks } s
  vars : t.vars = s.vars
  importLit : t.importLit = s.importLit
  importBits : t.importBits = s.importBits
  values : ∀ j, t.asg.values.get! j = 0
  valuesSize : 2 * n ≤ t.asg.values.size
  trail : t.asg.trail.size = 0
  aLevel : n ≤ t.asg.aLevel.size
  aReason : n ≤ t.asg.aReason.size
  aBits : ∀ j, t.asg.aBits.get! j = 0
  aBitsSize : n ≤ t.asg.aBits.size
  unassigned : t.asg.unassigned = 0
  flags : ∀ j, t.flags.get! j = 0
  flagsSize : n ≤ t.flags.size
  marks : ∀ j, t.marks.get! j = 0
  marksSize : 2 * n ≤ t.marks.size
  watches : ∀ j : Nat, ((t.watches[j]! : WVec)).data.size = 0
  watchesSize : 2 * n ≤ t.watches.size
  size : n ≤ t.size.toNat

theorem increaseSize_empty (s : Solver) (n : Nat) (hn : n < 2 ^ 30) (ha : s.asg = {}) (hw : s.watches = #[])
    (hf : s.flags = .empty) (hm : s.marks = .empty) (hz : s.size = 0) :
    Grown (s.increaseSize (UInt32.ofNat n)) s n := by
  have hn' : (UInt32.ofNat n).toNat = n := by simp; omega
  have e0 : ∀ j, ByteArray.empty.get! j = 0 := fun j => ByteArray.get!_oob _ _ (by simp)
  have eU : ∀ j, (U32Vec.empty).get! j = 0 := fun j => by simp [U32Vec.get!_eq, U32Vec.empty]
  unfold increaseSize
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos (by rw [hz]; exact UInt32.zero_le)]
    refine ⟨by ifr_rfl, rfl, rfl, rfl, ?_, by omega, ?_, by omega, by omega, ?_, by omega, ?_, ?_, by omega, ?_, by omega,
      ?_, by omega, by omega⟩
    · intro j; rw [ha]; exact e0 j
    · simp [ha]; try rfl
    · intro j; rw [ha]; exact e0 j
    · simp [ha]; try rfl
    · intro j; rw [hf]; exact eU j
    · intro j; rw [hm]; exact e0 j
    · intro j; simp [hw]; rfl
  · rw [if_neg (by simp only [hz, ge_iff_le, UInt32.le_iff_toNat_le, hn']; simp; omega)]
    dsimp only
    rw [hn']
    refine ⟨by ifr_rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; exact growBytes_zero _ _ (by rw [ha]; exact e0) j
    · rw [growBytes_size]; omega
    · simp [ha]; try rfl
    · rw [growU32_size]; omega
    · rw [growU32_size]; omega
    · intro j; exact growBytes_zero _ _ (by rw [ha]; exact e0) j
    · rw [growBytes_size]; omega
    · simp [ha]; try rfl
    · intro j; rw [growU32_get, hf]; simp [U32Vec.empty]
    · rw [growU32_size]; omega
    · intro j; exact growBytes_zero _ _ (by rw [hm]; exact e0) j
    · rw [growBytes_size]; omega
    · intro j; rw [hw]
      simp only [Array.empty_append, List.size_toArray, List.length_nil, Nat.sub_zero]
      by_cases hj : j < 2 * n
      · simp [hj, WVec.empty]
      · simp [hj]; rfl
    · rw [hw]; simp
    · rw [hn']; exact Nat.le_refl _

/-- The state after `kissat_init` and `kissat_reserve (n)`. -/
structure Reserved (s : Solver) (opts : Options) (n : Nat) : Prop where
  fresh : s.Fresh
  imp : ImportOK s
  vars : s.vars.toNat = n
  active : ∀ v, v < n → s.isActive (UInt32.ofNat v) = true
  options : s.options = opts
  clause : s.clause.size = 0
  marks : ∀ j, s.marks.get! j = 0
  marksSize : 2 * n ≤ s.marks.size
  inconsistent : s.inconsistent = false
  watching : s.watching = true
  stable : s.stable = false
  cs : s.clauseSatisfied = false
  ct : s.clauseTrivial = false
  csh : s.clauseShrink = false
  notFlagged : s.overflowed = false ∧ s.outOfResources = false ∧ s.notPorted = false

theorem init_reserve_spec (opts : Options) (n : Nat) (hn : n < 2 ^ 30) (ht : opts.tumble = 0) :
    Reserved ((Solver.init opts).reserve n) opts n := by
  unfold reserve
  generalize hs0 : Solver.init opts = s0
  have i1 : s0.vars = 0 := by rw [← hs0]; rfl
  have i2 : s0.size = 0 := by rw [← hs0]; rfl
  have i3 : s0.importLit.size = 0 := by rw [← hs0]; rfl
  have i4 : s0.importBits.size = 0 := by rw [← hs0]; rfl
  have i5 : s0.options = opts := by rw [← hs0]; rfl
  have i6 : s0.asg = {} := by rw [← hs0]; rfl
  have i7 : s0.watches = #[] := by rw [← hs0]; rfl
  have i8 : s0.flags = .empty := by rw [← hs0]; rfl
  have i9 : s0.marks = .empty := by rw [← hs0]; rfl
  have i10 : s0.arena.words.size = 0 := by rw [← hs0]; rfl
  have i11 : s0.delayed.size = 0 := by rw [← hs0]; rfl
  have i12 : s0.level = 0 := by rw [← hs0]; rfl
  have i13 : s0.frameTrail.size = 1 := by rw [← hs0]; rfl
  have i14 : s0.propagate = 0 := by rw [← hs0]; rfl
  have i15 : s0.clause.size = 0 := by rw [← hs0]; rfl
  have i16 : s0.inconsistent = false := by rw [← hs0]; rfl
  have i17 : s0.watching = true := by rw [← hs0]; rfl
  have i18 : s0.stable = false := by rw [← hs0]; rfl
  have i19 : s0.clauseSatisfied = false ∧ s0.clauseTrivial = false ∧ s0.clauseShrink = false := by rw [← hs0]; exact ⟨rfl, rfl, rfl⟩
  have i20 : s0.overflowed = false ∧ s0.outOfResources = false ∧ s0.notPorted = false := by rw [← hs0]; exact ⟨rfl, rfl, rfl⟩
  dsimp only
  have G := increaseSize_empty s0 n hn i6 i7 i8 i9 i2
  generalize s0.increaseSize (UInt32.ofNat n) = s1 at G
  have g1 : s1.options = opts := by rw [← i5]; exact G.ifr.options
  rw [if_pos (by simp [g1, ht])]
  obtain ⟨m1, m2, m3⟩ := reserveImport_spec n hn s1 1 (by omega) (by omega)
    ⟨fun _ => ⟨by rw [G.importLit, i3], by rw [G.importBits, i4]⟩, fun h => by omega, fun e h1 h2 => by omega⟩
    (by rw [G.vars, i1]; rfl) G.size (by rw [g1]; exact ht)
  generalize s1.reserveImport 1 n = s2 at m1 m2 m3
  have hfl2 : s2.flags = s1.flags := m3.flags
  obtain ⟨a1, a2, a3, a4⟩ := reserveActivate_spec n hn s2 0 (by omega)
    (fun v hv => by
      constructor
      · intro h; unfold isActive varFlags at h; rw [hfl2, G.flags] at h; simp at h
      · intro h; omega)
    (by rw [hfl2]; exact G.flagsSize) (by rw [m3.asg, G.unassigned]; rfl)
  generalize s2.reserveActivate 0 n = s3 at a1 a2 a3 a4
  have eA : s3.asg.values = s1.asg.values := a1.values.trans (by rw [m3.asg])
  have hv3 : s3.vars.toNat = n := by rw [a1.vars, m2]
  have f1 : s1.arena = s0.arena := G.ifr.arena
  have f2 : s1.delayed = s0.delayed := G.ifr.delayed
  have f3 : s1.level = s0.level := G.ifr.level
  have f4 : s1.frameTrail = s0.frameTrail := G.ifr.frameTrail
  have f5 : s1.propagate = s0.propagate := G.ifr.propagate
  have f6 : s1.clause = s0.clause := G.ifr.clause
  have f7 : s1.inconsistent = s0.inconsistent := G.ifr.inconsistent
  have f8 : s1.watching = s0.watching := G.ifr.watching
  have f9 : s1.stable = s0.stable := G.ifr.stable
  have f10 : s1.clauseSatisfied = s0.clauseSatisfied ∧ s1.clauseTrivial = s0.clauseTrivial ∧
      s1.clauseShrink = s0.clauseShrink := ⟨G.ifr.cs, G.ifr.ct, G.ifr.csh⟩
  have f11 : s1.overflowed = s0.overflowed ∧ s1.outOfResources = s0.outOfResources ∧ s1.notPorted = s0.notPorted :=
    ⟨G.ifr.overflowed, G.ifr.outOfResources, G.ifr.notPorted⟩
  refine ⟨⟨by omega, fun j => by rw [eA]; exact G.values j, by rw [eA, hv3]; exact G.valuesSize,
    by rw [a1.trail, m3.asg]; exact G.trail, by rw [a1.aLevel, m3.asg, hv3]; exact G.aLevel,
    by rw [a1.aReason, m3.asg, hv3]; exact G.aReason, fun j => by rw [a1.aBits, m3.asg]; exact G.aBits j,
    by rw [a1.aBits, m3.asg, hv3]; exact G.aBitsSize, by rw [a2, hv3], by rw [a1.arena, m3.arena, f1]; exact i10,
    fun j => by rw [a1.watches, m3.watches]; exact G.watches j, by rw [a1.watches, m3.watches, hv3]; exact G.watchesSize,
    by rw [a1.delayed, m3.delayed, f2]; exact i11, by rw [a1.level, m3.level, f3]; exact i12,
    by rw [a1.frameTrail, m3.frameTrail, f4]; exact i13, by rw [a1.propagate, m3.propagate, f5]; exact i14⟩,
    ?_, hv3, a3, by rw [a1.options, m3.options, g1], by rw [a1.clause, m3.clause, f6]; exact i15,
    fun j => by rw [a1.marks, m3.marks]; exact G.marks j, by rw [a1.marks, m3.marks]; exact G.marksSize,
    by rw [a1.inconsistent, m3.inconsistent, f7]; exact i16, by rw [a1.watching, m3.watching, f8]; exact i17,
    by rw [a1.stable, m3.stable, f9]; exact i18, by rw [a1.cs, m3.cs, f10.1]; exact i19.1,
    by rw [a1.ct, m3.ct, f10.2.1]; exact i19.2.1, by rw [a1.csh, m3.csh, f10.2.2]; exact i19.2.2,
    ⟨by rw [a1.overflowed, m3.overflowed, f11.1]; exact i20.1,
      by rw [a1.outOfResources, m3.outOfResources, f11.2.1]; exact i20.2.1,
      by rw [a1.notPorted, m3.notPorted, f11.2.2]; exact i20.2.2⟩⟩
  intro v hv
  rw [hv3] at hv
  obtain ⟨_, m1b, m1c⟩ := m1
  obtain ⟨z1, z2⟩ := m1b (by omega)
  obtain ⟨e1, e2⟩ := m1c (v + 1) (by omega) (by omega)
  refine ⟨by rw [a1.importLit, z1]; omega, ?_, ?_, ?_⟩
  · rw [a1.importLit, e1]; simp only [Nat.add_sub_cancel]; unfold LIT; rw [UInt32.mul_comm, BitTac.u32_mul_two]
  · rw [a1.importBits, e2]; decide
  · rw [a1.importBits, e2]; decide

/-- The bookkeeping after watching a new large clause. -/
def nlcTailG (t : Solver) (orig red : Bool) (res : Ref) (lits : U32Vec) : Solver :=
  (if red then (if t.firstReducible == INVALID_REF then { t with firstReducible := res } else t)
   else { t.markAddedLiterals lits.toArray with lastIrredundant := res }).incClause orig red false

theorem markAddedLiterals_quiet (lits : List Lit) : ∀ (t : Solver), Quiet (lits.foldl markAddedLiteral t) t := by
  induction lits with
  | nil => intro t; exact Quiet.refl _
  | cons x xs ih => intro t; exact (ih _).trans (markAddedLiteral_quiet _ _)

theorem markAddedLiterals_marks (lits : List Lit) : ∀ (t : Solver), (lits.foldl markAddedLiteral t).marks = t.marks := by
  induction lits with
  | nil => intro t; rfl
  | cons x xs ih => intro t; exact (ih _).trans rfl

theorem nlcTailG_quiet (t : Solver) (orig red : Bool) (res : Ref) (lits : U32Vec) :
    Quiet (nlcTailG t orig red res lits) t ∧ (nlcTailG t orig red res lits).marks = t.marks := by
  unfold nlcTailG
  refine ⟨(incClause_quiet _ _ _ _).trans ?_, ?_⟩
  · split
    · split
      · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      · exact Quiet.refl _
    · have := markAddedLiterals_quiet lits.toArray.toList t
      unfold markAddedLiterals; rw [Array.foldl_toList] at this
      exact (show Quiet { t.markAddedLiterals lits.toArray with lastIrredundant := res } (t.markAddedLiterals lits.toArray)
        from ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩).trans this
  · show (if red then (if t.firstReducible == INVALID_REF then { t with firstReducible := res } else t)
      else { t.markAddedLiterals lits.toArray with lastIrredundant := res }).marks = t.marks
    split
    · split <;> rfl
    · have := markAddedLiterals_marks lits.toArray.toList t
      unfold markAddedLiterals; rw [Array.foldl_toList] at this; exact this

theorem newLargeClause_eqG (s : Solver) (orig red : Bool) (glue : UInt32) (lits : U32Vec) (b : Arena) (res : Ref)
    (h : s.arena.allocate red glue lits = (some res, b)) (hw : s.watching = true) :
    s.newLargeClause orig red glue lits =
      (res, nlcTailG ((({ s with arena := b } : Solver).watchBlocking (lits.get! 0) (lits.get! 1) res).watchBlocking
          (lits.get! 1) (lits.get! 0) res) orig red res lits) := by
  unfold newLargeClause
  simp only [h]
  simp only [hw, ite_true]
  unfold nlcTailG
  split <;> rfl

theorem newLargeClause_noneG (s : Solver) (orig red : Bool) (glue : UInt32) (lits : U32Vec) (b : Arena)
    (h : s.arena.allocate red glue lits = (none, b)) :
    (s.newLargeClause orig red glue lits).1 = INVALID_REF ∧ (s.newLargeClause orig red glue lits).2.outOfResources = true := by
  unfold newLargeClause; simp only [h]; simp

theorem alloc_redundant {a b : Arena} {r : Ref} {red : Bool} {glue : UInt32} {lits : U32Vec}
    (h : Arena.Alloc a b r red glue lits) : b.redundant r = red := by
  unfold Arena.redundant Arena.flag; rw [h.word0]
  cases red
  · simp [ClauseHeader.redundantBit]
  · simp only [ite_true]
    have : ∀ g : UInt32, ((min MAX_GLUE g ||| ClauseHeader.redundantBit) &&& ClauseHeader.redundantBit != 0) = true := by
      intro g; simp only [bne_iff_ne, ne_eq]; unfold ClauseHeader.redundantBit; bv_k
    exact this glue

/-- Adding a large clause (original or learned, redundant or irredundant). -/
theorem newLargeClause_specG {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) (hw : s.watching = true)
    (orig red : Bool) (glue : UInt32) (lits : U32Vec) (hn : 3 ≤ lits.size) (hnd : lits.view.Nodup)
    (hv : ∀ x ∈ lits.view, s.ValidLit x) (himp : Implied Φ lits.view)
    (hok : (s.newLargeClause orig red glue lits).1 ≠ INVALID_REF) :
    SInv Φ (s.newLargeClause orig red glue lits).2 ∧
    (s.newLargeClause orig red glue lits).2.LiveRef (s.newLargeClause orig red glue lits).1 ∧
    (s.newLargeClause orig red glue lits).2.clauseL (s.newLargeClause orig red glue lits).1 = lits.view ∧
    (s.newLargeClause orig red glue lits).2.arena.redundant (s.newLargeClause orig red glue lits).1 = red ∧
    (∀ c, (s.newLargeClause orig red glue lits).2.InDB c ↔ s.InDB c ∨ c = lits.view) ∧
    (s.newLargeClause orig red glue lits).2.asg = s.asg ∧ anaSide (s.newLargeClause orig red glue lits).2 = anaSide s ∧
    (s.newLargeClause orig red glue lits).2.level = s.level ∧
    (s.newLargeClause orig red glue lits).2.propagate = s.propagate ∧
    (s.newLargeClause orig red glue lits).2.frameTrail = s.frameTrail ∧
    (s.newLargeClause orig red glue lits).2.delayed = s.delayed ∧
    (s.newLargeClause orig red glue lits).2.marks = s.marks ∧
    IrrMono s (s.newLargeClause orig red glue lits).2 := by
  have hn32 : lits.size < 2 ^ 32 := by
    have := nodup_valid_length hs.ws _ hnd hv; simpa using this
  generalize hal : s.arena.allocate red glue lits = R
  obtain ⟨o, b⟩ := R
  cases o with
  | none => exact absurd (newLargeClause_noneG s orig red glue lits b hal).1 hok
  | some res =>
  rw [newLargeClause_eqG s orig red glue lits b res hal hw]
  simp only
  obtain ⟨hA, hLb, hch⟩ := Arena.allocate_layout hs.layout hal hn32
  obtain ⟨w1, w2, w3, w4, w5⟩ := allocWatch_ws hs.ws hs.layout hA hch hn hn32 hnd hv rfl rfl rfl rfl
  generalize hT : ((({ s with arena := b } : Solver).watchBlocking (lits.get! 0) (lits.get! 1) res).watchBlocking (lits.get! 1) (lits.get! 0) res) = t0 at w1 w2 w3 w4 w5 ⊢
  have f1 : t0.asg = s.asg := by rw [← hT]; rfl
  have f2 : t0.arena = b := by rw [← hT]; rfl
  have f3 : anaSide t0 = anaSide s := by rw [← hT]; rfl
  have f4 : t0.level = s.level := by rw [← hT]; rfl
  have f5 : t0.propagate = s.propagate := by rw [← hT]; rfl
  have f6 : t0.frameTrail = s.frameTrail := by rw [← hT]; rfl
  have f7 : t0.vars = s.vars := by rw [← hT]; rfl
  have f8 : t0.options = s.options := by rw [← hT]; rfl
  have f9 : t0.marks = s.marks := by rw [← hT]; rfl
  have f10 : t0.delayed = s.delayed := by rw [← hT]; rfl
  have hdb : ∀ c, t0.InDB c ↔ s.InDB c ∨ c = lits.view := by
    intro c
    unfold InDB
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨a, b', hab, rfl⟩)
      · rcases (w3 x).mp hx with hx' | rfl
        · exact Or.inl (Or.inl ⟨x, hx', w4 x hx'⟩)
        · exact Or.inr w5
      · exact Or.inl (Or.inr ⟨a, b', (w2 a b').mp hab, rfl⟩)
    · rintro ((⟨x, hx, rfl⟩ | ⟨a, b', hab, rfl⟩) | rfl)
      · exact Or.inl ⟨x, (w3 x).mpr (Or.inl hx), (w4 x hx).symm⟩
      · exact Or.inr ⟨a, b', (w2 a b').mpr hab, rfl⟩
      · exact Or.inl ⟨res, (w3 res).mpr (Or.inr rfl), w5.symm⟩
  have hs0 : SInv Φ t0 := sinv_extend hs f1 f7 f4 f6 f5 f8 w1 (by rw [f2]; exact hLb)
    (fun x hx => (w3 x).mpr (Or.inl hx)) (fun x hx y => by rw [w4 x hx]) (fun a b' h => (w2 a b').mpr h)
    (fun c hc => by rcases (hdb c).mp hc with h | rfl; exact Or.inl h; exact Or.inr himp)
  have hmono : IrrMono s t0 := by
    apply IrrMono.of_large
    · intro r hr hred
      refine ⟨(w3 r).mpr (Or.inl hr), ?_, fun x hx => by rw [w4 r hr] at hx; exact hx⟩
      rw [f2, redundant_of_word0 (hA.oldReads hs.layout hr.1).1]; exact hred
    · intro a b' h; exact (w2 a b').mpr h
    · intro l hl; simpa [RootTrue, IsTrue, lvl, f1] using hl
  obtain ⟨hq, hqm⟩ := nlcTailG_quiet t0 orig red res lits
  have hS := hq.same
  refine ⟨hS.sinv hs0, ?_, ?_, ?_, fun c => (hS.inDB c).trans (hdb c), by rw [hS.asg, f1], by rw [hq.ana, f3],
    by rw [hS.level, f4], by rw [hS.propagate, f5], by rw [hS.frameTrail, f6], by rw [hS.delayed, f10],
    by rw [hqm, f9], hmono.trans (IrrMono.of_eq hS.asg hS.arena hS.watches)⟩
  · have := (w3 res).mpr (Or.inr rfl)
    unfold LiveRef refsL at *; rw [hS.arena]; exact this
  · unfold Solver.clauseL at *; rw [hS.arena]; exact w5
  · rw [hS.arena, f2]; exact alloc_redundant hA

end Solver
end LeanKissat
