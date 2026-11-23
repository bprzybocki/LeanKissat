import LeanKissat.Proofs.WatchAdd

/-!
# Adding a learned clause to the database
-/

namespace LeanKissat
namespace Solver
open Arena

/-- Extending the database with implied clauses (same assignment) preserves `SInv`. -/
theorem sinv_extend {Φ : (Nat → Bool) → Prop} {s t : Solver} (hs : SInv Φ s)
    (ha : t.asg = s.asg) (hv : t.vars = s.vars) (hlev : t.level = s.level) (hf : t.frameTrail = s.frameTrail)
    (hp : t.propagate = s.propagate) (ho : t.options = s.options)
    (hW : t.WatchStruct) (hL : t.arena.Layout)
    (hlive : ∀ x, s.LiveRef x → t.LiveRef x) (hcl : ∀ x, s.LiveRef x → ∀ y, y ∈ t.clauseL x ↔ y ∈ s.clauseL x)
    (hbin : ∀ a b, s.BinWatched a b → t.BinWatched a b) (hdb : ∀ c, t.InDB c → s.InDB c ∨ Implied Φ c) :
    SInv Φ t := by
  have hcore : t.Core := by
    have e1 : ∀ l, t.IsTrue l ↔ s.IsTrue l := by intro l; simp [IsTrue, ha]
    have e2 : ∀ l, t.IsFalse l ↔ s.IsFalse l := by intro l; simp [IsFalse, ha]
    have e3 : ∀ l, t.lvl l = s.lvl l := by intro l; simp [lvl, ha]
    have e4 : t.trailL = s.trailL := by simp [trailL, ha]
    have hc := hs.core
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l; rw [e1, e2, e2]; exact hc.valCons l
    · intro l hl; rw [e1] at hl; rw [e4, e3]; exact hc.trueOnTrail l hl
    · intro l hl; rw [e4] at hl; rw [e1]; exact hc.trailTrue l hl
    · intro l; rw [e3, e3]; exact hc.lvlVar l
    · unfold Sizes; rw [ha, hv]; exact hc.sizes
    · intro j; rw [ha]; exact hc.domain j
  have hlvl : t.LevelOK := by
    have eT : t.IsTrue = s.IsTrue := by funext l; simp [IsTrue, ha]
    have eL : t.lvl = s.lvl := by funext l; simp [lvl, ha]
    have eTr : t.trailL = s.trailL := by simp [trailL, ha]
    have eFr : t.framesL = s.framesL := by simp [framesL, hf]
    have eP : t.pushLevel = s.pushLevel := by funext p; simp [pushLevel, eFr]
    have hl := hs.levelOK
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eT, eL, hlev]; exact hl.trueLe
    · rw [eTr, eL, eP]; exact hl.pushLe
    · rw [eFr]; exact hl.sorted
    · rw [eFr, hlev]; exact hl.len
    · rw [eFr, hp]; exact hl.framesLe
    · rw [eTr, hp]; exact hl.propLe
    · rw [eFr]; exact hl.strict
    · rw [eFr, eTr]; exact hl.framesLt
    · rw [hf]; exact hl.frames0
  have hreas : t.ReasonOK := by
    have eT : t.IsTrue = s.IsTrue := by funext l; simp [IsTrue, ha]
    have eL : t.lvl = s.lvl := by funext l; simp [lvl, ha]
    intro l hlt hlv
    rw [eT] at hlt; rw [eL] at hlv
    exact reasonAt_congr ha hlive hcl hbin (hs.reasons l hlt hlv)
  refine ⟨hcore, hlvl, hW, hL, hreas, rootImplied_transfer ha hs.roots, ?_, ?_, by rw [ho]; exact hs.jump⟩
  · have := hs.rsizes; unfold ReasonSizes at *; rw [ha, hv, show t.trailL = s.trailL by simp [trailL, ha]]
    exact this
  · intro c hc
    rcases hdb c hc with h | h
    · exact hs.db c h
    · exact h

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

def quietTuple (s : Solver) := (s.asg, s.arena, s.watches, s.delayed, s.vars, s.level, s.frameTrail,
  s.propagate, s.options, anaSide s)

theorem Quiet.of_tuple {t s : Solver} (h : quietTuple t = quietTuple s) : Quiet t s := by
  simp only [quietTuple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩

theorem incClause_quiet (s : Solver) (o r b : Bool) : Quiet (s.incClause o r b) s :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The bookkeeping after watching a new redundant clause. -/
def nlcTail (t : Solver) (res : Ref) : Solver :=
  (if t.firstReducible == INVALID_REF then { t with firstReducible := res } else t).incClause false true false

theorem nlcTail_quiet (t : Solver) (res : Ref) : Quiet (nlcTail t res) t := by
  unfold nlcTail
  apply (incClause_quiet _ _ _ _).trans
  split
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · exact Quiet.refl _

theorem newLargeClause_eq (s : Solver) (glue : UInt32) (lits : U32Vec) (b : Arena) (res : Ref)
    (h : s.arena.allocate true glue lits = (some res, b)) (hw : s.watching = true) :
    s.newLargeClause false true glue lits =
      (res, nlcTail ((({ s with arena := b } : Solver).watchBlocking (lits.get! 0) (lits.get! 1) res).watchBlocking
          (lits.get! 1) (lits.get! 0) res) res) := by
  unfold newLargeClause
  simp only [h]
  simp only [hw, ite_true]
  rfl

theorem newLargeClause_none (s : Solver) (glue : UInt32) (lits : U32Vec) (b : Arena)
    (h : s.arena.allocate true glue lits = (none, b)) :
    (s.newLargeClause false true glue lits).1 = INVALID_REF := by
  unfold newLargeClause; simp only [h]

theorem nodup_valid_length {s : Solver} (hW : s.WatchStruct) (L : List Lit) (hnd : L.Nodup)
    (hv : ∀ x ∈ L, s.ValidLit x) : L.length < 2 ^ 32 := by
  have := nodup_length_le (2 * s.vars.toNat) (L.map UInt32.toNat)
    (List.Pairwise.map UInt32.toNat (fun a b hab e => hab (UInt32.toNat_inj.mp e)) hnd)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨l, hl, rfl⟩ := hx; exact (validLit_toNat hW (hv l hl)).1)
  have := hW.varsBound
  simp at *; omega

/-- Adding the learned large clause `lits` (redundant, watched). -/
theorem newLargeClause_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) (hw : s.watching = true)
    (glue : UInt32) (lits : U32Vec) (hn : 3 ≤ lits.size) (hnd : lits.view.Nodup)
    (hv : ∀ x ∈ lits.view, s.ValidLit x) (himp : Implied Φ lits.view)
    (hok : (s.newLargeClause false true glue lits).1 ≠ INVALID_REF) :
    SInv Φ (s.newLargeClause false true glue lits).2 ∧
    (s.newLargeClause false true glue lits).2.LiveRef (s.newLargeClause false true glue lits).1 ∧
    (s.newLargeClause false true glue lits).2.clauseL (s.newLargeClause false true glue lits).1 = lits.view ∧
    (∀ c, (s.newLargeClause false true glue lits).2.InDB c ↔ s.InDB c ∨ c = lits.view) ∧
    (s.newLargeClause false true glue lits).2.asg = s.asg ∧
    anaSide (s.newLargeClause false true glue lits).2 = anaSide s ∧
    (s.newLargeClause false true glue lits).2.level = s.level ∧
    (s.newLargeClause false true glue lits).2.propagate = s.propagate ∧
    (s.newLargeClause false true glue lits).2.frameTrail = s.frameTrail ∧
    (s.newLargeClause false true glue lits).2.vars = s.vars ∧
    (s.newLargeClause false true glue lits).2.options = s.options ∧
    IrrMono s (s.newLargeClause false true glue lits).2 := by
  have hn32 : lits.size < 2 ^ 32 := by
    have := nodup_valid_length hs.ws _ hnd hv; simpa using this
  generalize hal : s.arena.allocate true glue lits = R
  obtain ⟨o, b⟩ := R
  cases o with
  | none => exact absurd (newLargeClause_none s glue lits b hal) hok
  | some res =>
  rw [newLargeClause_eq s glue lits b res hal hw]
  simp only
  obtain ⟨hA, hLb, hch⟩ := allocate_layout hs.layout hal hn32
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
  have hq := nlcTail_quiet t0 res
  have hS := hq.same
  have hmono : IrrMono s t0 := by
    apply IrrMono.of_large
    · intro r hr hred
      refine ⟨(w3 r).mpr (Or.inl hr), ?_, fun x hx => by rw [w4 r hr] at hx; exact hx⟩
      rw [f2, redundant_of_word0 (hA.oldReads hs.layout hr.1).1]; exact hred
    · intro a b' h; exact (w2 a b').mpr h
    · intro l hl; simpa [RootTrue, IsTrue, lvl, f1] using hl
  refine ⟨hS.sinv hs0, ?_, ?_, fun c => (hS.inDB c).trans (hdb c), by rw [hS.asg, f1], by rw [hq.ana, f3],
    by rw [hS.level, f4], by rw [hS.propagate, f5], by rw [hS.frameTrail, f6], by rw [hS.vars, f7],
    by rw [hS.options, f8], hmono.trans (IrrMono.of_eq hS.asg hS.arena hS.watches)⟩
  · have := (w3 res).mpr (Or.inr rfl)
    unfold LiveRef refsL at *; rw [hS.arena]; exact this
  · unfold Solver.clauseL at *; rw [hS.arena]; exact w5

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem markAddedLiteral_asg (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).asg = s.asg := by
  rfl
theorem markAddedLiteral_arena (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).arena = s.arena := by
  rfl
theorem markAddedLiteral_watches (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).watches = s.watches := by
  rfl
theorem markAddedLiteral_delayed (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).delayed = s.delayed := by
  rfl
theorem markAddedLiteral_vars (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).vars = s.vars := by
  rfl
theorem markAddedLiteral_level (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).level = s.level := by
  rfl
theorem markAddedLiteral_frameTrail (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).frameTrail = s.frameTrail := by
  rfl
theorem markAddedLiteral_propagate (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).propagate = s.propagate := by
  rfl
theorem markAddedLiteral_options (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).options = s.options := by
  rfl
theorem markAddedLiteral_clause (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).clause = s.clause := by
  rfl
theorem markAddedLiteral_analyzed (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).analyzed = s.analyzed := by
  rfl
theorem markAddedLiteral_removable (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).removable = s.removable := by
  rfl
theorem markAddedLiteral_poisoned (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).poisoned = s.poisoned := by
  rfl
theorem markAddedLiteral_shrinkable (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).shrinkable = s.shrinkable := by
  rfl
theorem markAddedLiteral_minimize (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).minimize = s.minimize := by
  rfl
theorem markAddedLiteral_levels (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).levels = s.levels := by
  rfl
theorem markAddedLiteral_inconsistent (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).inconsistent = s.inconsistent := by
  rfl
theorem markAddedLiteral_overflowed (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).overflowed = s.overflowed := by
  rfl
theorem markAddedLiteral_watching (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).watching = s.watching := by
  rfl
theorem markAddedLiteral_probing (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).probing = s.probing := by
  rfl
theorem markAddedLiteral_outOfResources (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).outOfResources = s.outOfResources := by
  rfl
theorem markAddedLiteral_conflictLit0 (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).conflictLit0 = s.conflictLit0 := by
  rfl
theorem markAddedLiteral_conflictLit1 (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).conflictLit1 = s.conflictLit1 := by
  rfl
theorem markAddedLiteral_importLit (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).importLit = s.importLit := by
  rfl
theorem markAddedLiteral_importBits (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).importBits = s.importBits := by
  rfl
theorem markAddedLiteral_notPorted (s : Solver) (lit : Lit) : (s.markAddedLiteral lit).notPorted = s.notPorted := by
  rfl
theorem markAddedLiteral_ana (s : Solver) (lit : Lit) : anaSide (s.markAddedLiteral lit) = anaSide s := by
  simp only [anaSide, markAddedLiteral_importLit, markAddedLiteral_importBits, markAddedLiteral_vars,
    markAddedLiteral_notPorted, markAddedLiteral_clause, markAddedLiteral_analyzed, markAddedLiteral_removable,
    markAddedLiteral_poisoned, markAddedLiteral_shrinkable, markAddedLiteral_minimize, markAddedLiteral_levels,
    markAddedLiteral_options, markAddedLiteral_inconsistent, markAddedLiteral_overflowed,
    markAddedLiteral_watching, markAddedLiteral_probing, markAddedLiteral_outOfResources,
    markAddedLiteral_conflictLit0, markAddedLiteral_conflictLit1]

theorem markAddedLiteral_quiet (s : Solver) (lit : Lit) : Quiet (s.markAddedLiteral lit) s :=
  ⟨⟨markAddedLiteral_asg s lit, markAddedLiteral_arena s lit, markAddedLiteral_watches s lit,
    markAddedLiteral_delayed s lit, markAddedLiteral_vars s lit, markAddedLiteral_level s lit,
    markAddedLiteral_frameTrail s lit, markAddedLiteral_propagate s lit, markAddedLiteral_options s lit⟩,
   markAddedLiteral_ana s lit⟩

/-- Adding the learned binary clause `a ∨ b` (watched). -/
theorem newBinaryClause_spec {Φ : (Nat → Bool) → Prop} {s : Solver} (hs : SInv Φ s) {a b : Lit}
    (ha : s.ValidLit a) (hb : s.ValidLit b) (hab : a ≠ b) (himp : Implied Φ [a, b]) :
    SInv Φ (s.newBinaryClauseAux false true a b) ∧
    (∀ c, (s.newBinaryClauseAux false true a b).InDB c ↔ s.InDB c ∨ c = [a, b] ∨ c = [b, a]) ∧
    (s.newBinaryClauseAux false true a b).BinWatched a b ∧
    (s.newBinaryClauseAux false true a b).asg = s.asg ∧
    anaSide (s.newBinaryClauseAux false true a b) = anaSide s ∧
    (s.newBinaryClauseAux false true a b).level = s.level ∧
    (s.newBinaryClauseAux false true a b).propagate = s.propagate ∧
    (s.newBinaryClauseAux false true a b).frameTrail = s.frameTrail ∧
    (s.newBinaryClauseAux false true a b).vars = s.vars ∧
    (s.newBinaryClauseAux false true a b).options = s.options ∧
    IrrMono s (s.newBinaryClauseAux false true a b) := by
  obtain ⟨w1, w2, w3, w4⟩ := watchBinary_ws hs.ws ha hb hab
  have hq : Quiet (s.newBinaryClauseAux false true a b) (s.watchBinary a b) := by
    unfold newBinaryClauseAux
    simp only [ite_true]
    exact (incClause_quiet _ _ _ _).trans ((markAddedLiteral_quiet _ _).trans (markAddedLiteral_quiet _ _))
  generalize s.newBinaryClauseAux false true a b = t at hq ⊢
  have hS := hq.same
  have hdb0 : ∀ c, (s.watchBinary a b).InDB c ↔ s.InDB c ∨ c = [a, b] ∨ c = [b, a] := by
    intro c
    have eLive : ∀ r, (s.watchBinary a b).LiveRef r ↔ s.LiveRef r := fun r => Iff.rfl
    have eCl : ∀ r, (s.watchBinary a b).clauseL r = s.clauseL r := fun r => rfl
    unfold InDB
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, y, hxy, rfl⟩)
      · exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
      · rcases (w2 x y).mp hxy with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (Or.inr ⟨x, y, h, rfl⟩)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro ((⟨x, hx, rfl⟩ | ⟨x, y, hxy, rfl⟩) | rfl | rfl)
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, y, (w2 x y).mpr (Or.inl hxy), rfl⟩
      · exact Or.inr ⟨a, b, (w2 a b).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), rfl⟩
      · exact Or.inr ⟨b, a, (w2 b a).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), rfl⟩
  have himp' : Implied Φ [b, a] := himp.perm (fun x hx => by simp at hx ⊢; rcases hx with rfl | rfl <;> simp)
  have hs0 : SInv Φ (s.watchBinary a b) := sinv_extend hs rfl rfl rfl rfl rfl rfl w1 hs.layout
    (fun x hx => hx) (fun x _ _ => Iff.rfl) (fun x y h => (w2 x y).mpr (Or.inl h))
    (fun c hc => by
      rcases (hdb0 c).mp hc with h | rfl | rfl
      · exact Or.inl h
      · exact Or.inr himp
      · exact Or.inr himp')
  have hmono : IrrMono s (s.watchBinary a b) := by
    apply IrrMono.of_large
    · intro r hr hred; exact ⟨hr, hred, fun x hx => hx⟩
    · intro x y h; exact (w2 x y).mpr (Or.inl h)
    · intro l hl; exact hl
  refine ⟨hS.sinv hs0, fun c => (hS.inDB c).trans (hdb0 c), ?_, hS.asg, hq.ana, hS.level, hS.propagate,
    hS.frameTrail, hS.vars, hS.options, hmono.trans (IrrMono.of_eq hS.asg hS.arena hS.watches)⟩
  have : (s.watchBinary a b).BinWatched a b := (w2 a b).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  unfold BinWatched entries watchesOf at *; rw [hS.watches]; exact this

end Solver
end LeanKissat
