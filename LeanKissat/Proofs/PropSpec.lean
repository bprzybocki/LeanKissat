import LeanKissat.Proofs.Struct
import LeanKissat.Proofs.ArenaWrites

/-!
# List-level specification of the propagation loop

`propLoop` works on the raw words of a watch list with a read pointer `p` and a
write pointer `q`. `PropSpec.run` is the same computation on parsed entries
(`WEntry`). `propLoop_eq_spec` relates the two; all semantic reasoning is done on
`PropSpec.run`.

Restrictions (the `--plain` configuration): `ignore = none`, `beyond = false`.
-/

namespace LeanKissat
namespace Solver

/-- Words of an entry. -/
def WEntry.words : WEntry → List UInt32
  | .bin b => [binaryWatch b]
  | .large b r => [blockingWatch b, largeWatch r]

def encodeWatches (es : List WEntry) : List UInt32 := es.flatMap WEntry.words

/-- State of the specification loop. -/
structure PS where
  out : List WEntry
  a : Asg
  arena : Arena
  delayed : List (Lit × Lit × Ref)
  s : Solver
  res : Option CRef

namespace PS

/-- One step on entry `e` (no conflict yet). Mirrors the body of `propLoop`. -/
def step (probing jump : Bool) (level : UInt32) (notLit : Lit) (st : PS) : WEntry → PS
  | .bin blocking =>
    let v := st.a.values.get! blocking.toNat
    if vTrue v then { st with out := st.out ++ [.bin blocking] }
    else if vFalse v then
      { st with out := st.out ++ [.bin blocking],
                s := { st.s with conflictLit0 := notLit, conflictLit1 := blocking },
                res := some .binConflict }
    else
      let oidx := IDX notLit
      let reason :=
        if jump && level != 0 && (st.a.aBits.get! oidx.toNat &&& ABits.binary) != 0 then
          st.a.aReason.get! oidx.toNat
        else notLit
      let s := if level == 0 then st.s.markFixedLiteral blocking else st.s
      { st with out := st.out ++ [.bin blocking], s := s,
                a := st.a.assign probing level true blocking reason }
  | .large blocking ref =>
    let v := st.a.values.get! blocking.toNat
    if vTrue v then { st with out := st.out ++ [.large blocking ref] }
    else if st.arena.garbage ref then st
    else
    let arena := st.arena
    let other := arena.lit ref 0 ^^^ arena.lit ref 1 ^^^ notLit
    let otherValue := st.a.values.get! other.toNat
    if vTrue otherValue then { st with out := st.out ++ [.large other ref] }
    else
    let size := (arena.size ref).toNat
    let searched := (arena.searched ref).toNat
    let r := Solver.findReplacement arena st.a.values ref searched size
    let r := if r < size then r else
      let r' := Solver.findReplacement arena st.a.values ref 2 searched
      if r' < searched then r' else size
    if r < size then
      let replacement := arena.lit ref r
      { st with
        arena := arena.replaceArena ref r other notLit,
        delayed := st.delayed ++ [(replacement, other, ref)] }
    else if otherValue != 0 then
      { st with out := st.out ++ [.large blocking ref], res := some (.large ref) }
    else
      let alevel := Solver.asgAssignmentLevel arena st.a.aLevel other ref 0 size 0
      let s := if alevel == 0 then st.s.markFixedLiteral other else st.s
      { st with out := st.out ++ [.large blocking ref], s := s,
                a := st.a.assign probing alevel false other ref }

/-- Process all entries; after a conflict the remaining entries are copied. -/
def run (probing jump : Bool) (level : UInt32) (notLit : Lit) : PS → List WEntry → PS
  | st, [] => st
  | st, e :: es =>
    if st.res.isSome then { st with out := st.out ++ e :: es }
    else run probing jump level notLit (step probing jump level notLit st e) es

end PS
end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-! ### Words ↔ entries -/

theorem binaryWatch_watchLit (w : UInt32) (h : watchIsBinary w = true) :
    binaryWatch (watchLit w) = w := by
  simp only [watchIsBinary, bne_iff_ne, ne_eq] at h
  simp only [binaryWatch, watchLit, WATCH_BINARY_BIT] at *
  bv_decide

theorem blockingWatch_watchLit (w : UInt32) (h : watchIsBinary w = false) :
    blockingWatch (watchLit w) = w := by
  simp only [watchIsBinary, bne_eq_false_iff_eq] at h
  simp only [blockingWatch, watchLit, WATCH_BINARY_BIT] at *
  bv_decide

theorem largeWatch_watchRef (w : UInt32) (h : watchIsBinary w = false) :
    largeWatch (watchRef w) = w := by
  simp only [watchIsBinary, bne_eq_false_iff_eq] at h
  simp only [largeWatch, watchRef, WATCH_BINARY_BIT] at *
  bv_decide

theorem encode_parse : ∀ (W : List UInt32), WordsOK W → encodeWatches (parseWatches W) = W
  | [], _ => rfl
  | w :: rest, h => by
    unfold WordsOK at h
    unfold parseWatches
    by_cases hb : watchIsBinary w = true
    · simp only [hb, ite_true] at h ⊢
      have ih := encode_parse rest h
      simp only [encodeWatches, List.flatMap_cons, WEntry.words] at *
      rw [binaryWatch_watchLit w hb, ih]; rfl
    · have hb' : watchIsBinary w = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ite_false] at h ⊢
      match rest, h with
      | t :: rest', ⟨ht, h'⟩ =>
        have ih := encode_parse rest' h'
        simp only [encodeWatches, List.flatMap_cons, WEntry.words] at *
        rw [blockingWatch_watchLit w hb', largeWatch_watchRef t ht, ih]; rfl

theorem encode_append (a b : List WEntry) :
    encodeWatches (a ++ b) = encodeWatches a ++ encodeWatches b := by
  simp [encodeWatches]

/-- Parsing at a binary head. -/
theorem parse_drop_bin {W : List UInt32} {p : Nat} (hp : p < W.length)
    (hb : watchIsBinary W[p] = true) :
    parseWatches (W.drop p) = .bin (watchLit W[p]) :: parseWatches (W.drop (p + 1)) := by
  rw [List.drop_eq_getElem_cons hp, parseWatches.eq_def]; simp only [hb, ite_true]

/-- Parsing at a large head. -/
theorem parse_drop_large {W : List UInt32} {p : Nat} (hp : p + 1 < W.length)
    (hb : watchIsBinary (W[p]'(by omega)) = false) :
    parseWatches (W.drop p) =
      .large (watchLit (W[p]'(by omega))) (watchRef W[p + 1]) :: parseWatches (W.drop (p + 2)) := by
  rw [List.drop_eq_getElem_cons (by omega : p < W.length),
    List.drop_eq_getElem_cons (by omega : p + 1 < W.length), parseWatches.eq_def]
  simp only [hb, Bool.false_eq_true, ite_false]

theorem wordsOK_drop_bin {W : List UInt32} {p : Nat} (hp : p < W.length)
    (hb : watchIsBinary W[p] = true) (h : WordsOK (W.drop p)) : WordsOK (W.drop (p + 1)) := by
  rw [List.drop_eq_getElem_cons hp] at h; unfold WordsOK at h; simpa [hb] using h

theorem wordsOK_drop_large {W : List UInt32} {p : Nat} (hp : p < W.length)
    (hb : watchIsBinary W[p] = false) (h : WordsOK (W.drop p)) :
    ∃ hl : p + 1 < W.length, watchIsBinary W[p + 1] = false ∧ WordsOK (W.drop (p + 2)) := by
  rw [List.drop_eq_getElem_cons hp] at h
  unfold WordsOK at h
  simp only [hb, Bool.false_eq_true, ite_false] at h
  have hd : W.drop (p + 1) = W.drop (p + 1) := rfl
  revert h
  generalize hD : W.drop (p + 1) = D
  intro h
  match D, hD, h with
  | t :: rest', hD, ⟨ht, h'⟩ =>
    have hl : p + 1 < W.length := by have := congrArg List.length hD; simp at this; omega
    refine ⟨hl, ?_, ?_⟩
    · have e : (W.drop (p + 1))[0]? = some t := by rw [hD]; rfl
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hl] at e
      cases e; exact ht
    · have : W.drop (p + 2) = rest' := by
        have := congrArg (List.drop 1) hD; simpa [List.drop_drop] using this
      rw [this]; exact h'

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem WVec.toList_set! (w : WVec) (i : Nat) (v : UInt32) :
    (w.set! i v).data.toList = w.data.toList.set i v := by
  simp [WVec.set!, Array.set!_eq_setIfInBounds]

theorem list_set_take_drop {α : Type} (L : List α) (q p : Nat) (v : α) (h : q ≤ p)
    (hq : q < L.length) :
    (L.set q v).take (q + 1) ++ (L.set q v).drop (p + 1) = L.take q ++ ([v] ++ L.drop (p + 1)) := by
  have hq' : q < (L.set q v).length := by simpa using hq
  rw [List.take_succ_eq_append_getElem hq', List.take_set_of_le (Nat.le_refl q),
    List.getElem_set_self, List.drop_set_of_lt (by omega : q < p + 1), List.append_assoc]

theorem copyRest_spec : ∀ (ws : WVec) (p q : Nat), q ≤ p →
    let r := copyRest ws p q
    r.1.data.toList.take r.2 = ws.data.toList.take q ++ ws.data.toList.drop p := by
  intro ws p q hqp
  fun_induction copyRest ws p q with
  | case1 ws p q hp ih =>
    simp only at ih ⊢
    rw [ih (by omega)]
    rw [WVec.toList_set!]
    have hpl : p < ws.data.toList.length := by rw [Array.length_toList]; exact hp
    have hql : q < ws.data.toList.length := by omega
    rw [list_set_take_drop _ _ _ _ hqp hql, List.drop_eq_getElem_cons hpl]
    rfl
  | case2 ws p q hp =>
    simp only
    have : ws.data.toList.drop p = [] := by
      apply List.drop_eq_nil_of_le; simp [WVec.size] at hp; simpa using hp
    rw [this, List.append_nil]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- Flattened `delayed` stack. -/
def flatDelayed (d : List (Lit × Lit × Ref)) : List UInt32 :=
  d.flatMap (fun x => [x.1, blockingWatch x.2.1, x.2.2])

/-- Invariant relating the words being processed to the spec state. -/
structure LoopRel (W0 : List UInt32) (ws : WVec) (p q : Nat) (out : List WEntry) : Prop where
  len : ws.data.toList.length = W0.length
  qp : q ≤ p
  pl : p ≤ W0.length
  drop : ws.data.toList.drop p = W0.drop p
  ok : WordsOK (W0.drop p)
  take : ws.data.toList.take q = encodeWatches out

theorem LoopRel.size_eq {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) : ws.size = W0.length := by
  have := h.len; simpa [WVec.size] using this

theorem LoopRel.getElem_eq {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) (hp : p < ws.size) :
    ws[p] = W0[p]'(by rw [← h.size_eq]; exact hp) := by
  have e := congrArg (·[0]?) h.drop
  simp only [List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [h.len, ← h.size_eq]; exact hp),
    List.getElem?_eq_getElem (by rw [← h.size_eq]; exact hp)] at e
  have := Option.some.inj e
  simp only [Array.getElem_toList] at this
  exact this

theorem LoopRel.bin {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) (hp : p < ws.size) (hb : watchIsBinary ws[p] = true) :
    LoopRel W0 (ws.set! q ws[p]) (p + 1) (q + 1) (out ++ [.bin (watchLit ws[p])]) := by
  have hpl : p < W0.length := by rw [← h.size_eq]; exact hp
  have hge := h.getElem_eq hp
  have hb0 : watchIsBinary W0[p] = true := by rw [← hge]; exact hb
  have hql : q < ws.data.toList.length := by
    have := h.qp; have := h.len; have := h.size_eq; omega
  refine ⟨by simp [WVec.toList_set!, h.len], by have := h.qp; omega, by omega, ?_, ?_, ?_⟩
  · rw [WVec.toList_set!, List.drop_set_of_lt (by have := h.qp; omega)]
    have := congrArg (List.drop 1) h.drop
    simpa [List.drop_drop, Nat.add_comm] using this
  · exact wordsOK_drop_bin hpl hb0 h.ok
  · rw [WVec.toList_set!]
    have hq' : q < (ws.data.toList.set q ws[p]).length := by simpa using hql
    rw [List.take_succ_eq_append_getElem hq', List.take_set_of_le (Nat.le_refl q),
      List.getElem_set_self, h.take, encode_append]
    simp [encodeWatches, WEntry.words, binaryWatch_watchLit _ hb]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem list_set2_take {α : Type} (L : List α) (q : Nat) (x y : α) (hq : q + 1 < L.length) :
    ((L.set q x).set (q + 1) y).take (q + 2) = L.take q ++ [x, y] := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    have hm : min q L.length = q := by omega
    simp only [List.getElem_take, List.getElem_set, List.getElem_append, List.length_take, hm]
    by_cases hi : i < q
    · have : ¬ q + 1 = i := by omega
      have : ¬ q = i := by omega
      simp [*]
    · have : i = q ∨ i = q + 1 := by simp at h1; omega
      rcases this with rfl | rfl
      · simp
      · simp; intro h; omega

/-- The words after the two writes of a large entry. -/
theorem LoopRel.large_common {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) (hp : p < ws.size) (hb : watchIsBinary ws[p] = false) :
    ∃ hl : p + 1 < W0.length, ws.get! (p + 1) = W0[p + 1] ∧ watchIsBinary W0[p + 1] = false ∧
      WordsOK (W0.drop (p + 2)) ∧
      parseWatches (W0.drop p) =
        .large (watchLit ws[p]) (watchRef (ws.get! (p + 1))) :: parseWatches (W0.drop (p + 2)) ∧
      ((ws.set! q ws[p]).set! (q + 1) (ws.get! (p + 1))).data.toList.drop (p + 2) = W0.drop (p + 2) ∧
      q + 1 < ws.data.toList.length := by
  have hpl : p < W0.length := by rw [← h.size_eq]; exact hp
  have hge := h.getElem_eq hp
  have hb0 : watchIsBinary W0[p] = false := by rw [← hge]; exact hb
  obtain ⟨hl, ht, hok⟩ := wordsOK_drop_large hpl hb0 h.ok
  have hget : ws.get! (p + 1) = W0[p + 1] := by
    have e := congrArg (·[1]?) h.drop
    simp only [List.getElem?_drop] at e
    have hl' : p + 1 < ws.data.toList.length := by rw [h.len]; exact hl
    rw [List.getElem?_eq_getElem hl', List.getElem?_eq_getElem hl] at e
    have := Option.some.inj e
    simp only [Array.getElem_toList] at this
    simp only [WVec.get!, Array.getElem!_eq_getD, Array.getD, dif_pos (by simpa using hl')]
    exact this
  refine ⟨hl, hget, ht, hok, ?_, ?_, ?_⟩
  · rw [parse_drop_large hl hb0, hget, hge]
  · rw [WVec.toList_set!, WVec.toList_set!, List.drop_set_of_lt (by have := h.qp; omega),
      List.drop_set_of_lt (by have := h.qp; omega)]
    have := congrArg (List.drop 2) h.drop
    simpa [List.drop_drop, Nat.add_comm] using this
  · have := h.qp; rw [h.len]; omega

theorem LoopRel.large_keep {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) (hp : p < ws.size) (hb : watchIsBinary ws[p] = false) (o : Lit) :
    let ws2 := (ws.set! q ws[p]).set! (q + 1) (ws.get! (p + 1))
    LoopRel W0 (ws2.set! q (blockingWatch o)) (p + 2) (q + 2)
      (out ++ [.large o (watchRef (ws.get! (p + 1)))]) := by
  obtain ⟨hl, hget, ht, hok, _, hdrop, hq1⟩ := h.large_common hp hb
  have hlen := h.len
  refine ⟨by simp [WVec.toList_set!, h.len], by have := h.qp; omega, by omega, ?_, hok, ?_⟩
  · rw [WVec.toList_set!, List.drop_set_of_lt (by have := h.qp; omega)]; exact hdrop
  · rw [WVec.toList_set!, WVec.toList_set!, WVec.toList_set!]
    have e1 : ((ws.data.toList.set q ws[p]).set (q + 1) (ws.get! (p + 1))).set q (blockingWatch o) =
        (ws.data.toList.set q (blockingWatch o)).set (q + 1) (ws.get! (p + 1)) := by
      rw [List.set_comm _ _ (by omega : q + 1 ≠ q), List.set_set]
    rw [e1, list_set2_take _ _ _ _ hq1, h.take, encode_append]
    simp only [encodeWatches, List.flatMap_cons, List.flatMap_nil, WEntry.words, List.append_nil]
    rw [hget, largeWatch_watchRef _ ht]

theorem LoopRel.large_drop {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) (hp : p < ws.size) (hb : watchIsBinary ws[p] = false) :
    LoopRel W0 ((ws.set! q ws[p]).set! (q + 1) (ws.get! (p + 1))) (p + 2) q out := by
  obtain ⟨hl, hget, ht, hok, _, hdrop, hq1⟩ := h.large_common hp hb
  refine ⟨by simp [WVec.toList_set!, h.len], by have := h.qp; omega, by omega, hdrop, hok, ?_⟩
  rw [WVec.toList_set!, WVec.toList_set!, List.take_set_of_le (by omega),
    List.take_set_of_le (by omega)]
  exact h.take

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

theorem LoopRel.large_same {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) (hp : p < ws.size) (hb : watchIsBinary ws[p] = false) :
    LoopRel W0 ((ws.set! q ws[p]).set! (q + 1) (ws.get! (p + 1))) (p + 2) (q + 2)
      (out ++ [.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))]) := by
  obtain ⟨hl, hget, ht, hok, _, hdrop, hq1⟩ := h.large_common hp hb
  refine ⟨by simp [WVec.toList_set!, h.len], by have := h.qp; omega, by omega, hdrop, hok, ?_⟩
  rw [WVec.toList_set!, WVec.toList_set!, list_set2_take _ _ _ _ hq1, h.take, encode_append]
  simp only [encodeWatches, List.flatMap_cons, List.flatMap_nil, WEntry.words, List.append_nil]
  rw [blockingWatch_watchLit _ hb, hget, largeWatch_watchRef _ ht]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver

/-- The conclusion of `propLoop_spec`. -/
def Corr (R : PropResult) (st : PS) : Prop :=
  R.a = st.a ∧ R.arena = st.arena ∧ R.s = st.s ∧ R.res = st.res ∧
  R.delayed.view = flatDelayed st.delayed ∧
  (copyRest R.ws R.p R.q).1.data.toList.take (copyRest R.ws R.p R.q).2 = encodeWatches st.out

theorem PS.run_of_res {probing jump : Bool} {level : UInt32} {notLit : Lit} (st : PS)
    (h : st.res.isSome) (es : List WEntry) :
    PS.run probing jump level notLit st es = { st with out := st.out ++ es } := by
  cases es with
  | nil => simp [PS.run]
  | cons e es => simp [PS.run, h]

theorem PS.run_cons_none {probing jump : Bool} {level : UInt32} {notLit : Lit} (st : PS)
    (h : st.res = none) (e : WEntry) (es : List WEntry) :
    PS.run probing jump level notLit st (e :: es) =
      PS.run probing jump level notLit (PS.step probing jump level notLit st e) es := by
  simp [PS.run, h]

theorem flatDelayed_append (d : List (Lit × Lit × Ref)) (x : Lit × Lit × Ref) :
    flatDelayed (d ++ [x]) = flatDelayed d ++ [x.1, blockingWatch x.2.1, x.2.2] := by
  simp [flatDelayed]

theorem LoopRel.parse_bin {W0 : List UInt32} {ws : WVec} {p q : Nat} {out : List WEntry}
    (h : LoopRel W0 ws p q out) (hp : p < ws.size) (hb : watchIsBinary ws[p] = true) :
    parseWatches (W0.drop p) = .bin (watchLit ws[p]) :: parseWatches (W0.drop (p + 1)) := by
  have hpl : p < W0.length := by rw [← h.size_eq]; exact hp
  have hge := h.getElem_eq hp
  rw [parse_drop_bin hpl (by rw [← hge]; exact hb), hge]

theorem propLoop_spec (probing jump : Bool) (level : UInt32) (notLit : Lit) (W0 : List UInt32)
    (ws : WVec) (p q : Nat) (a : Asg) (arena : Arena) (dl : U32Vec) (s : Solver) (ticks : UInt64)
    (res : Option CRef) :
    ∀ (out : List WEntry) (dlist : List (Lit × Lit × Ref)),
    LoopRel W0 ws p q out → dl.view = flatDelayed dlist →
    Corr (propLoop none false probing jump level notLit ws p q a arena dl s ticks res)
      (PS.run probing jump level notLit ⟨out, a, arena, dlist, s, res⟩ (parseWatches (W0.drop p))) := by
  fun_induction propLoop none false probing jump level notLit ws p q a arena dl s ticks res
  case case1 ws p q a arena dl s ticks res hp hres =>
    intro out dlist hrel hdl
    have hs : res.isSome := by simpa using hres
    rw [PS.run_of_res _ (by simpa using hs)]
    refine ⟨rfl, rfl, rfl, rfl, hdl, ?_⟩
    simp only
    rw [copyRest_spec ws p q hrel.qp, hrel.take, hrel.drop, encode_append,
      encode_parse _ hrel.ok]
  case case12 ws p q a arena dl s ticks res hp =>
    intro out dlist hrel hdl
    have hpw : W0.length ≤ p := by have := hrel.size_eq; omega
    rw [List.drop_eq_nil_of_le hpw]
    simp only [parseWatches, PS.run]
    refine ⟨rfl, rfl, rfl, rfl, hdl, ?_⟩
    simp only
    rw [copyRest_spec ws p q hrel.qp, hrel.take, hrel.drop, List.drop_eq_nil_of_le hpw,
      List.append_nil]
  case case2 ws p q a arena dl s ticks res hp hres head blocking bv hb ws' hv ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    rw [hrel.parse_bin hp hb, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩ (.bin (watchLit ws[p])) =
        ⟨out ++ [.bin (watchLit ws[p])], a, arena, dlist, s, res⟩ := by
      simp only [PS.step]; rw [if_pos hv]
    rw [hstep]
    exact ih _ _ (hrel.bin hp hb) hdl
  case case3 ws p q a arena dl s ticks res hp hres head blocking bv hb ws' hv hf s' ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    rw [hrel.parse_bin hp hb, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩ (.bin (watchLit ws[p])) =
        ⟨out ++ [.bin (watchLit ws[p])], a, arena, dlist, s', some .binConflict⟩ := by
      simp only [PS.step]; rw [if_neg hv, if_pos hf]
    rw [hstep]
    exact ih _ _ (hrel.bin hp hb) hdl
  case case4 ws p q a arena dl s ticks res hp hres head blocking bv hb ws' hv hf oidx reason s' a' ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    rw [hrel.parse_bin hp hb, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩ (.bin (watchLit ws[p])) =
        ⟨out ++ [.bin (watchLit ws[p])], a', arena, dlist, s', res⟩ := by
      simp only [PS.step]; rw [if_neg hv, if_neg hf]; rfl
    rw [hstep]
    exact ih _ _ (hrel.bin hp hb) hdl
  case case5 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    have hb' : watchIsBinary ws[p] = false := by simpa using hb
    obtain ⟨_, _, _, _, hparse, _, _⟩ := hrel.large_common hp hb'
    rw [hparse, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩
        (.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))) =
        ⟨out ++ [.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))], a, arena, dlist, s, res⟩ := by
      simp only [PS.step]; rw [if_pos hv]
    rw [hstep]
    exact ih _ _ (hrel.large_same hp hb') hdl
  case case6 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    have hb' : watchIsBinary ws[p] = false := by simpa using hb
    obtain ⟨_, _, _, _, hparse, _, _⟩ := hrel.large_common hp hb'
    rw [hparse, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩
        (.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))) =
        ⟨out, a, arena, dlist, s, res⟩ := by
      simp only [PS.step]; rw [if_neg hv, if_pos hg]
    rw [hstep]
    have : q' - 2 = q := by simp [q']
    rw [this] at ih
    exact ih _ _ (hrel.large_drop hp hb') hdl
  case case7 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov ws'' ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    have hb' : watchIsBinary ws[p] = false := by simpa using hb
    obtain ⟨_, _, _, _, hparse, _, _⟩ := hrel.large_common hp hb'
    rw [hparse, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩
        (.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))) =
        ⟨out ++ [.large other (watchRef (ws.get! (p + 1)))], a, arena, dlist, s, res⟩ := by
      simp only [PS.step]; rw [if_neg hv, if_neg hg, if_pos hov]
    rw [hstep]
    have : q' - 2 = q := by simp [q']
    simp only [ws'', this] at ih
    exact ih _ _ (hrel.large_keep hp hb' other) hdl
  case case8 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr replacement arena' dl' ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    have hb' : watchIsBinary ws[p] = false := by simpa using hb
    obtain ⟨_, _, _, _, hparse, _, _⟩ := hrel.large_common hp hb'
    rw [hparse, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩
        (.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))) =
        ⟨out, a, arena', dlist ++ [(replacement, other, ref)], s, res⟩ := by
      simp only [PS.step]; rw [if_neg hv, if_neg hg, if_neg hov]
      have hr' := hr; simp only [r, r0, size, searched, ref, tail, dite_eq_ite] at hr'
      rw [if_pos hr']; rfl
    rw [hstep]
    have : q' - 2 = q := by simp [q']
    rw [this] at ih
    refine ih _ _ (hrel.large_drop hp hb') ?_
    simp only [dl', U32Vec.view_push, hdl, flatDelayed_append]
    simp
  case case9 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr hig ih =>
    exact absurd hig (by simp)
  case case10 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr hig hov0 ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    have hb' : watchIsBinary ws[p] = false := by simpa using hb
    obtain ⟨_, _, _, _, hparse, _, _⟩ := hrel.large_common hp hb'
    rw [hparse, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩
        (.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))) =
        ⟨out ++ [.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))], a, arena, dlist, s,
          some (.large ref)⟩ := by
      simp only [PS.step]; rw [if_neg hv, if_neg hg, if_neg hov]
      have hr' := hr; simp only [r, r0, size, searched, ref, tail, dite_eq_ite] at hr'
      rw [if_neg hr', if_pos hov0]
    rw [hstep]
    exact ih _ _ (hrel.large_same hp hb') hdl
  case case11 ws p q a arena dl s ticks res hp hres head blocking bv hb tail ws' q' hv ref ticks' hg
      other ov hov size searched r0 r hr hig hov0 alevel s' a' ih =>
    intro out dlist hrel hdl
    have hres' : res = none := by simpa using hres
    have hb' : watchIsBinary ws[p] = false := by simpa using hb
    obtain ⟨_, _, _, _, hparse, _, _⟩ := hrel.large_common hp hb'
    rw [hparse, PS.run_cons_none _ hres']
    have hstep : PS.step probing jump level notLit ⟨out, a, arena, dlist, s, res⟩
        (.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))) =
        ⟨out ++ [.large (watchLit ws[p]) (watchRef (ws.get! (p + 1)))], a', arena, dlist, s', res⟩ := by
      simp only [PS.step]; rw [if_neg hv, if_neg hg, if_neg hov]
      have hr' := hr; simp only [r, r0, size, searched, ref, tail, dite_eq_ite] at hr'
      rw [if_neg hr', if_neg hov0]; rfl
    rw [hstep]
    exact ih _ _ (hrel.large_same hp hb') hdl

end Solver
end LeanKissat
