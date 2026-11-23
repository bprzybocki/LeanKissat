import LeanKissat.Proofs.LearnRef

/-!
# Removing a large watch (`kissat_unwatch_blocking`)
-/

namespace LeanKissat
namespace Solver
open Arena

/-- Entries kept by `removeBlockingWatch ref`. -/
def keepRef (ref : Ref) : WEntry → Bool
  | .bin _ => true
  | .large _ r => r != ref

theorem drop_cons_getElem {α : Type} (L : List α) (p : Nat) (w : α) (rest : List α) (h : L.drop p = w :: rest) :
    ∃ hp : p < L.length, L[p] = w ∧ L.drop (p + 1) = rest := by
  have hp : p < L.length := by
    apply Classical.byContradiction; intro hn
    rw [List.drop_eq_nil_of_le (by omega)] at h; simp at h
  rw [List.drop_eq_getElem_cons hp] at h
  obtain ⟨h1, h2⟩ := List.cons.inj h
  exact ⟨hp, h1, h2⟩

theorem wvec_getElem_eq (ws : WVec) (p : Nat) (hp : p < ws.size) : ws[p] = ws.data.toList[p]'(by simpa [WVec.size] using hp) := by
  rfl

theorem wvec_get!_eq (ws : WVec) (p : Nat) (hp : p < ws.data.toList.length) : ws.get! p = ws.data.toList[p] := by
  show ws.data[p]! = _
  rw [getElem!_pos ws.data p (by simpa using hp)]; simp

theorem take_set_one {α : Type} (L : List α) (q : Nat) (v : α) (hq : q < L.length) :
    (L.set q v).take (q + 1) = L.take q ++ [v] := by
  have hq' : q < (L.set q v).length := by simpa using hq
  rw [List.take_succ_eq_append_getElem hq', List.take_set_of_le (Nat.le_refl q), List.getElem_set_self]

theorem take_set_two {α : Type} (L : List α) (q : Nat) (v u : α) (hq : q + 1 < L.length) :
    ((L.set q v).set (q + 1) u).take (q + 2) = L.take q ++ [v, u] := by
  have h1 : q + 1 < (L.set q v).length := by simpa using hq
  rw [show q + 2 = (q + 1) + 1 by omega, take_set_one _ _ _ h1, take_set_one _ _ _ (by omega)]
  simp

theorem blocking_not_binary (b : Lit) (hb : b.toNat < 2 ^ 31) : watchIsBinary (blockingWatch b) = false := by
  have := lt31 hb
  simp only [watchIsBinary, blockingWatch, WATCH_BINARY_BIT, bne_eq_false_iff_eq]; bv_decide

theorem binary_is_binary (b : Lit) (hb : b.toNat < 2 ^ 31) : watchIsBinary (binaryWatch b) = true := by
  have := lt31 hb
  simp only [watchIsBinary, binaryWatch, WATCH_BINARY_BIT, bne_iff_ne, ne_eq]; bv_decide

theorem largeWatch_eq (r : Ref) (hr : r.toNat < 2 ^ 31) : largeWatch r = r := by
  have := lt31 hr
  simp only [largeWatch]; bv_decide

theorem removeBlockingLoop_size (ref : Ref) : ∀ (ws : WVec) (p q : Nat), q ≤ p →
    (removeBlockingLoop ws ref p q).size = ws.size := by
  intro ws p q
  fun_induction removeBlockingLoop ws ref p q with
  | case1 ws p q hp w ws' hb ih => intro h; rw [ih (by omega)]; simp [ws', WVec.size, WVec.set!]
  | case2 ws p q hp w ws' hb t ws'' ht ih => intro h; rw [ih (by omega)]; simp [ws'', ws', WVec.size, WVec.set!]
  | case3 ws p q hp w ws' hb t ws'' ht ih => intro h; rw [ih (by omega)]; simp [ws'', ws', WVec.size, WVec.set!]
  | case4 => intro _; rfl

theorem removeBlockingLoop_spec (ref : Ref) (href : ref.toNat < 2 ^ 31) :
    ∀ (ws : WVec) (p q : Nat) (R : List WEntry), q ≤ p → ws.data.toList.drop p = encodeWatches R →
    (∀ e ∈ R, e.WF) →
    (removeBlockingLoop ws ref p q).data.toList.take (q + (encodeWatches (R.filter (keepRef ref))).length) =
      ws.data.toList.take q ++ encodeWatches (R.filter (keepRef ref)) := by
  intro ws p q
  fun_induction removeBlockingLoop ws ref p q with
  | case1 ws p q hp w ws' hb ih =>
    intro R hqp hd hwf
    cases R with
    | nil =>
      exfalso
      have h0 : ws.data.toList.drop p = [] := by simpa [encodeWatches] using hd
      rw [List.drop_eq_nil_iff] at h0; simp [WVec.size] at hp h0; omega
    | cons e R =>
    have hL : p < ws.data.toList.length := by simpa [WVec.size] using hp
    have hw : w = ws.data.toList[p] := wvec_getElem_eq ws p hp
    cases e with
    | large b r =>
      exfalso
      have hd' : ws.data.toList.drop p = blockingWatch b :: (largeWatch r :: encodeWatches R) := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, _⟩ := drop_cons_getElem _ _ _ _ hd'
      rw [← hw] at h1
      have := blocking_not_binary b (hwf _ (List.mem_cons_self ..)).1
      rw [← h1] at this; rw [this] at hb; simp at hb
    | bin b =>
      have hd' : ws.data.toList.drop p = binaryWatch b :: encodeWatches R := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, h2⟩ := drop_cons_getElem _ _ _ _ hd'
      rw [← hw] at h1
      have hws' : ws'.data.toList = ws.data.toList.set q w := WVec.toList_set! _ _ _
      have ih' := ih R (by omega) (by rw [hws', List.drop_set_of_lt (by omega)]; exact h2)
        (fun e he => hwf e (List.mem_cons_of_mem _ he))
      have hf : (WEntry.bin b :: R).filter (keepRef ref) = WEntry.bin b :: R.filter (keepRef ref) := by
        simp [List.filter, keepRef]
      rw [hf]
      have he : encodeWatches (WEntry.bin b :: R.filter (keepRef ref)) =
          binaryWatch b :: encodeWatches (R.filter (keepRef ref)) := by simp [encodeWatches, WEntry.words]
      rw [he, List.length_cons, show q + ((encodeWatches (R.filter (keepRef ref))).length + 1) =
        q + 1 + (encodeWatches (R.filter (keepRef ref))).length by omega, ih', hws', take_set_one _ _ _ (by omega), h1]
      simp
  | case2 ws p q hp w ws' hb t ws'' ht ih =>
    intro R hqp hd hwf
    have hL : p < ws.data.toList.length := by simpa [WVec.size] using hp
    have hw : w = ws.data.toList[p] := wvec_getElem_eq ws p hp
    cases R with
    | nil =>
      exfalso
      have h0 : ws.data.toList.drop p = [] := by simpa [encodeWatches] using hd
      rw [List.drop_eq_nil_iff] at h0; simp [WVec.size] at hp h0; omega
    | cons e R =>
    cases e with
    | bin b =>
      exfalso
      have hd' : ws.data.toList.drop p = binaryWatch b :: encodeWatches R := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, _⟩ := drop_cons_getElem _ _ _ _ hd'
      rw [← hw] at h1
      have := binary_is_binary b (hwf _ (List.mem_cons_self ..))
      rw [← h1] at this; rw [this] at hb; simp at hb
    | large b r =>
      have hwf0 := hwf _ (List.mem_cons_self ..)
      have hd' : ws.data.toList.drop p = blockingWatch b :: (largeWatch r :: encodeWatches R) := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, h2⟩ := drop_cons_getElem _ _ _ _ hd'
      obtain ⟨hp1, h3, h4⟩ := drop_cons_getElem _ _ _ _ h2
      rw [← hw] at h1
      have hws' : ws'.data.toList = ws.data.toList.set q w := WVec.toList_set! _ _ _
      have ht' : t = largeWatch r := by
        show ws'.get! (p + 1) = _
        rw [wvec_get!_eq _ _ (by rw [hws']; simpa using hp1), ]
        simp only [hws']
        rw [List.getElem_set_ne (by omega)]; exact h3
      have hws'' : ws''.data.toList = (ws.data.toList.set q w).set (q + 1) t := by
        rw [show ws''.data.toList = ws'.data.toList.set (q + 1) t from WVec.toList_set! _ _ _, hws']
      have hdrop : ws''.data.toList.drop (p + 2) = encodeWatches R := by
        rw [hws'', List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega),
          show p + 2 = (p + 1) + 1 by omega]; exact h4
      have hr : largeWatch r = r := largeWatch_eq r hwf0.2
      have hne : r ≠ ref := by intro e; apply bne_iff_ne.mp ht; rw [ht', hr, e]
      have ih' := ih R (by omega) hdrop (fun e he => hwf e (List.mem_cons_of_mem _ he))
      have hf : (WEntry.large b r :: R).filter (keepRef ref) = WEntry.large b r :: R.filter (keepRef ref) := by
        have : (r != ref) = true := bne_iff_ne.mpr hne
        simp [List.filter, keepRef, this]
      rw [hf]
      have he : encodeWatches (WEntry.large b r :: R.filter (keepRef ref)) =
          blockingWatch b :: largeWatch r :: encodeWatches (R.filter (keepRef ref)) := by
        simp [encodeWatches, WEntry.words]
      rw [he, List.length_cons, List.length_cons, show q + ((encodeWatches (R.filter (keepRef ref))).length + 1 + 1) =
        q + 2 + (encodeWatches (R.filter (keepRef ref))).length by omega, ih', hws'',
        take_set_two _ _ _ _ (by omega), h1, ht']
      simp
  | case3 ws p q hp w ws' hb t ws'' ht ih =>
    intro R hqp hd hwf
    have hL : p < ws.data.toList.length := by simpa [WVec.size] using hp
    have hw : w = ws.data.toList[p] := wvec_getElem_eq ws p hp
    cases R with
    | nil =>
      exfalso
      have h0 : ws.data.toList.drop p = [] := by simpa [encodeWatches] using hd
      rw [List.drop_eq_nil_iff] at h0; simp [WVec.size] at hp h0; omega
    | cons e R =>
    cases e with
    | bin b =>
      exfalso
      have hd' : ws.data.toList.drop p = binaryWatch b :: encodeWatches R := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, _⟩ := drop_cons_getElem _ _ _ _ hd'
      rw [← hw] at h1
      have := binary_is_binary b (hwf _ (List.mem_cons_self ..))
      rw [← h1] at this; rw [this] at hb; simp at hb
    | large b r =>
      have hwf0 := hwf _ (List.mem_cons_self ..)
      have hd' : ws.data.toList.drop p = blockingWatch b :: (largeWatch r :: encodeWatches R) := by
        rw [hd]; simp [encodeWatches, WEntry.words]
      obtain ⟨_, h1, h2⟩ := drop_cons_getElem _ _ _ _ hd'
      obtain ⟨hp1, h3, h4⟩ := drop_cons_getElem _ _ _ _ h2
      rw [← hw] at h1
      have hws' : ws'.data.toList = ws.data.toList.set q w := WVec.toList_set! _ _ _
      have ht' : t = largeWatch r := by
        show ws'.get! (p + 1) = _
        rw [wvec_get!_eq _ _ (by rw [hws']; simpa using hp1), ]
        simp only [hws']
        rw [List.getElem_set_ne (by omega)]; exact h3
      have hws'' : ws''.data.toList = (ws.data.toList.set q w).set (q + 1) t := by
        rw [show ws''.data.toList = ws'.data.toList.set (q + 1) t from WVec.toList_set! _ _ _, hws']
      have hdrop : ws''.data.toList.drop (p + 2) = encodeWatches R := by
        rw [hws'', List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega),
          show p + 2 = (p + 1) + 1 by omega]; exact h4
      have hr : largeWatch r = r := largeWatch_eq r hwf0.2
      have heq : r = ref := by
        have : t = ref := by simpa using ht
        rw [ht', hr] at this; exact this
      have ih' := ih R (by omega) hdrop (fun e he => hwf e (List.mem_cons_of_mem _ he))
      have hf : (WEntry.large b r :: R).filter (keepRef ref) = R.filter (keepRef ref) := by
        simp [List.filter, keepRef, heq]
      rw [hf, ih', hws'', List.take_set_of_le (by omega), List.take_set_of_le (by omega)]
  | case4 ws p q hp =>
    intro R _ hd _
    have : R = [] := by
      have h0 : ws.data.toList.drop p = [] := List.drop_eq_nil_of_le (by simp [WVec.size] at hp; simpa using hp)
      rw [h0] at hd
      cases R with
      | nil => rfl
      | cons e R => cases e <;> simp [encodeWatches, WEntry.words] at hd
    subst this; simp [encodeWatches]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem encode_filter_length (ref : Ref) : ∀ (E : List WEntry), countRef ref E = 1 →
    (encodeWatches (E.filter (keepRef ref))).length + 2 = (encodeWatches E).length := by
  intro E
  induction E with
  | nil => intro h; simp [countRef] at h
  | cons e E ih =>
    intro h
    cases e with
    | bin b =>
      simp only [countRef] at h
      have := ih h
      simp [List.filter, keepRef, encodeWatches, WEntry.words] at this ⊢; omega
    | large b r =>
      simp only [countRef] at h
      by_cases e : r = ref
      · subst e
        simp at h
        have h0 : ∀ L : List WEntry, countRef r L = 0 → L.filter (keepRef r) = L := by
          intro L
          induction L with
          | nil => intro _; rfl
          | cons x L ih' =>
            intro hx
            cases x with
            | bin b' => simp only [countRef] at hx; simp [List.filter, keepRef, ih' hx]
            | large b' r' =>
              simp only [countRef] at hx
              have hr' : r' ≠ r := by intro e; subst e; simp at hx
              have : (r' != r) = true := bne_iff_ne.mpr hr'
              simp [hr'] at hx
              simp [List.filter, keepRef, this, ih' hx]
        simp [List.filter, keepRef, h0 E h, encodeWatches, WEntry.words]
      · simp [e] at h
        have := ih h
        have hb : (r != ref) = true := bne_iff_ne.mpr e
        simp [List.filter, keepRef, hb, encodeWatches, WEntry.words] at this ⊢; omega

theorem removeBlockingWatch_spec (ws : WVec) (ref : Ref) (href : ref.toNat < 2 ^ 31)
    (hW : WordsOK ws.data.toList) (hc : countRef ref (parseWatches ws.data.toList) = 1) :
    (removeBlockingWatch ws ref).data.toList = encodeWatches ((parseWatches ws.data.toList).filter (keepRef ref)) := by
  have he := encode_parse _ hW
  have hwf := parse_wf ws.data.toList
  have hlen := encode_filter_length ref _ hc
  rw [he] at hlen
  have h := removeBlockingLoop_spec ref href ws 0 0 (parseWatches ws.data.toList) (Nat.le_refl _)
    (by rw [List.drop_zero, he]) hwf
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at h
  unfold removeBlockingWatch
  show ((removeBlockingLoop ws ref 0 0).data.shrink (ws.size - 2)).toList = _
  rw [Array.toList_shrink]
  have hsz : ws.size = ws.data.toList.length := by simp [WVec.size]
  rw [hsz, ← hlen, Nat.add_sub_cancel]
  exact h

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem highestLoop_spec (s : Solver) (c : CRef) (size : Nat) (cl : UInt32) (i0 : Nat) :
    ∀ (j hp : Nat) (hl : Lit) (hlev : UInt32), i0 ≤ j → hl = s.crefLit c hp → i0 ≤ hp → hp < size →
      (s.highestLoop c size cl j hp hl hlev).2 = s.crefLit c (s.highestLoop c size cl j hp hl hlev).1 ∧
      i0 ≤ (s.highestLoop c size cl j hp hl hlev).1 ∧ (s.highestLoop c size cl j hp hl hlev).1 < size := by
  intro j hp hl hlev
  fun_induction highestLoop s c size cl j hp hl hlev with
  | case1 j hp hl hlev hj other level hge ih =>
    intro h0 h1 h2 h3
    exact ih (by omega) h1 h2 h3
  | case2 j hp hl hlev hj other level hge heq =>
    intro h0 _ _ _
    exact ⟨rfl, h0, hj⟩
  | case3 j hp hl hlev hj other level hge heq ih =>
    intro h0 _ _ _
    exact ih (by omega) rfl h0 hj
  | case4 j hp hl hlev hj =>
    intro _ h1 h2 h3
    exact ⟨h1, h2, h3⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Arena

/-- Swapping the literals at positions `i` and `j` of the chain clause `r`. -/
theorem swap_writeOK {a : Arena} (h : a.Layout) {r : Ref} (hr : r ∈ a.chain 0 a.sizeWards) {i j : Nat}
    (hi : i < (a.size r).toNat) (hj : j < (a.size r).toNat) (hij : i ≠ j) :
    WriteOK a ((a.setLit r j (a.lit r i)).setLit r i (a.lit r j)) r ∧
    ((a.setLit r j (a.lit r i)).setLit r i (a.lit r j)).litsL r = ((a.litsL r).set j (a.lit r i)).set i (a.lit r j) ∧
    (((a.setLit r j (a.lit r i)).setLit r i (a.lit r j)).litsL r).Perm (a.litsL r) ∧
    ((a.setLit r j (a.lit r i)).setLit r i (a.lit r j)).searched r = a.searched r ∧
    ∀ k, k < (a.size r).toNat → ((a.setLit r j (a.lit r i)).setLit r i (a.lit r j)).lit r k =
      if k = i then a.lit r j else if k = j then a.lit r i else a.lit r k := by
  obtain ⟨w1, l1, s1⟩ := setLit_writeOK h hr hj (a.lit r i)
  have hr1 : r ∈ (a.setLit r j (a.lit r i)).chain 0 (a.setLit r j (a.lit r i)).sizeWards := by rw [w1.chain]; exact hr
  have hsz1 := w1.size r hr
  obtain ⟨w2, l2, s2⟩ := setLit_writeOK w1.layout hr1 (by rw [hsz1]; exact hi) (a.lit r j)
  have hsz2 := w2.size r hr1
  have hlen : (a.litsL r).length = (a.size r).toNat := length_litsL _ _
  have hL : ((a.setLit r j (a.lit r i)).setLit r i (a.lit r j)).litsL r = ((a.litsL r).set j (a.lit r i)).set i (a.lit r j) := by
    rw [l2, l1]
  have gi : (a.litsL r)[i]'(by omega) = a.lit r i := getElem_litsL _ _ _ _
  have gj : (a.litsL r)[j]'(by omega) = a.lit r j := getElem_litsL _ _ _ _
  refine ⟨w1.trans w2, hL, ?_, by rw [s2, s1], fun k hk => ?_⟩
  · rw [hL, ← gi, ← gj]
    exact List.set_set_perm (by omega) (by omega)
  · have hk' : k < (((a.setLit r j (a.lit r i)).setLit r i (a.lit r j)).litsL r).length := by
      rw [length_litsL, hsz2, hsz1]; exact hk
    rw [← getElem_litsL _ _ _ hk']
    simp only [hL, List.getElem_set]
    by_cases e1 : k = i
    · subst e1; simp
    · rw [if_neg (Ne.symm e1)]
      by_cases e2 : k = j
      · subst e2; simp [e1]
      · rw [if_neg (Ne.symm e2), if_neg e1, if_neg e2]; exact getElem_litsL _ _ _ _

end Arena
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem unwatchBlocking_spec {s : Solver} (hW : s.WatchStruct) {lit : Lit} (hl : s.ValidLit lit) {r : Ref}
    (hr : r.toNat < 2 ^ 31) (hc : countRef r (s.entries lit) = 1) :
    (∀ l, (s.unwatchBlocking lit r).entries l = (if l = lit then (s.entries l).filter (keepRef r) else s.entries l) ∧
      WordsOK ((s.unwatchBlocking lit r).watchesOf l).data.toList) ∧
    (s.unwatchBlocking lit r).watches.size = s.watches.size := by
  obtain ⟨_, _, hlw⟩ := validLit_toNat hW hl
  have hsz : (s.unwatchBlocking lit r).watches.size = s.watches.size := by
    simp [unwatchBlocking, modifyWatches]
  refine ⟨fun l => ?_, hsz⟩
  have hwl : ((s.unwatchBlocking lit r).watchesOf l).data.toList =
      if l = lit then encodeWatches ((s.entries l).filter (keepRef r)) else (s.watchesOf l).data.toList := by
    show ((s.watches.modify lit.toNat (removeBlockingWatch · r))[l.toNat]!).data.toList = _
    by_cases hlt : l.toNat < s.watches.size
    · rw [getElem!_pos (s.watches.modify lit.toNat (removeBlockingWatch · r)) l.toNat (by simpa using hlt),
        Array.getElem_modify]
      by_cases e : l = lit
      · subst e
        simp only [ite_true]
        have h1 := removeBlockingWatch_spec (s.watchesOf l) r hr (hW.words l) hc
        rw [show s.watches[l.toNat] = s.watchesOf l by simp [watchesOf, getElem!_pos s.watches l.toNat hlt]]
        exact h1
      · have : lit.toNat ≠ l.toNat := fun h => e (UInt32.toNat_inj.mp h).symm
        simp only [this, ite_false, e]
        simp [watchesOf, getElem!_pos s.watches l.toNat hlt]
    · have e : l ≠ lit := by intro h; subst h; exact hlt hlw
      simp only [watchesOf, e, ite_false]
      rw [getElem!_neg _ l.toNat (by simpa using hlt), getElem!_neg s.watches l.toNat hlt]
  unfold Solver.entries
  rw [hwl]
  split
  · rename_i e; subst e
    exact parse_encode _ (fun x hx => parse_wf _ x (List.mem_filter.mp hx).1)
  · exact ⟨rfl, hW.words l⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem countRef_zero (r : Ref) : ∀ (L : List WEntry), (∀ b, WEntry.large b r ∉ L) → countRef r L = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons e L ih =>
    intro h
    cases e with
    | bin b => exact ih (fun b' hb => h b' (List.mem_cons_of_mem _ hb))
    | large b x =>
      simp only [countRef]
      have : x ≠ r := by intro e; subst e; exact h b (List.mem_cons_self ..)
      rw [if_neg this, ih (fun b' hb => h b' (List.mem_cons_of_mem _ hb))]

theorem countRef_filter_self (r : Ref) (L : List WEntry) : countRef r (L.filter (keepRef r)) = 0 := by
  apply countRef_zero; intro b hb
  have := (List.mem_filter.mp hb).2; simp [keepRef] at this

theorem countRef_filter_ne (r x : Ref) (hx : x ≠ r) : ∀ (L : List WEntry),
    countRef x (L.filter (keepRef r)) = countRef x L := by
  intro L
  induction L with
  | nil => rfl
  | cons e L ih =>
    cases e with
    | bin b => simp [List.filter, keepRef, countRef, ih]
    | large b y =>
      by_cases e : y = r
      · subst e
        have : (y != y) = false := by simp
        simp only [List.filter, keepRef, this, countRef, ih, if_neg (Ne.symm hx)]
        simp
      · have : (y != r) = true := bne_iff_ne.mpr e
        simp only [List.filter, keepRef, this, countRef, ih]

theorem mem_filter_keepRef {r : Ref} {L : List WEntry} {e : WEntry} :
    e ∈ L.filter (keepRef r) ↔ e ∈ L ∧ ∀ b, e ≠ WEntry.large b r := by
  rw [List.mem_filter]
  cases e with
  | bin b => simp [keepRef]
  | large b x => simp [keepRef]

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem mw_frame (s : Solver) (lit hl' other : Lit) (r : Ref) (A : Arena) :
    (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r).vars = s.vars ∧
    (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r).delayed = s.delayed ∧
    (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r).asg = s.asg ∧
    anaSide (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r) = anaSide s ∧
    (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r).level = s.level ∧
    (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r).propagate = s.propagate ∧
    (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r).frameTrail = s.frameTrail ∧
    (({ s.unwatchBlocking lit r with arena := A } : Solver).watchBlocking hl' other r).arena = A :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Moving the watch of position `i ∈ {0,1}` of the live clause `r` to position `j ≥ 2`. -/
theorem moveWatch_ws {s : Solver} (hW : s.WatchStruct) (hl : s.arena.Layout) {r : Ref} (hr : s.LiveRef r)
    {i j : Nat} (hi : i ≤ 1) (hj2 : 2 ≤ j) (hj : j < (s.arena.size r).toNat)
    {t : Solver}
    (ht : t = ({ s.unwatchBlocking (s.arena.lit r i) r with
        arena := (s.arena.setLit r j (s.arena.lit r i)).setLit r i (s.arena.lit r j) } : Solver).watchBlocking
        (s.arena.lit r j) (s.arena.lit r (1 - i)) r) :
    t.WatchStruct ∧ t.arena.Layout ∧ WriteOK s.arena t.arena r ∧ (t.clauseL r).Perm (s.clauseL r) ∧
    (∀ a b, t.BinWatched a b ↔ s.BinWatched a b) ∧ t.arena.lit r i = s.arena.lit r j ∧
    t.asg = s.asg ∧ t.vars = s.vars ∧ anaSide t = anaSide s ∧ t.level = s.level ∧ t.propagate = s.propagate ∧
    t.frameTrail = s.frameTrail ∧ t.delayed = s.delayed := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hW.live r hr
  have hsz3 : 3 ≤ (s.arena.size r).toNat := g1
  generalize hlit : s.arena.lit r i = lit at ht
  generalize hhl : s.arena.lit r j = hl' at ht
  generalize hoth : s.arena.lit r (1 - i) = other at ht
  have hrr : r.toNat < 2 ^ 31 := by
    have := hl.mem_bounds hr.1; have := hl.bound; have := wardsOfClause_pos (s.arena.size r).toNat; omega
  -- distinctness from the clause being duplicate free
  have hnd := g2
  have hget : ∀ k (hk : k < (s.arena.size r).toNat), (s.clauseL r)[k]'(by unfold clauseL; simp; omega) = s.arena.lit r k := by
    intro k hk; unfold clauseL; simp
  have hdist : ∀ a b, a < (s.arena.size r).toNat → b < (s.arena.size r).toNat → a ≠ b → s.arena.lit r a ≠ s.arena.lit r b := by
    intro a b ha hb hab e
    rw [List.Nodup, List.pairwise_iff_getElem] at hnd
    rcases Nat.lt_or_gt_of_ne hab with h' | h'
    · exact hnd a b (by unfold clauseL; simp; omega) (by unfold clauseL; simp; omega) h' (by rw [hget a ha, hget b hb]; exact e)
    · exact hnd b a (by unfold clauseL; simp; omega) (by unfold clauseL; simp; omega) h' (by rw [hget a ha, hget b hb]; exact e.symm)
  have hne1 : hl' ≠ lit := by rw [← hhl, ← hlit]; exact hdist j i hj (by omega) (by omega)
  have hne2 : hl' ≠ other := by rw [← hhl, ← hoth]; exact hdist j (1 - i) hj (by omega) (by omega)
  have hne3 : lit ≠ other := by rw [← hlit, ← hoth]; exact hdist i (1 - i) (by omega) (by omega) (by omega)
  have hwatch : (lit = s.lit0 r ∧ other = s.lit1 r) ∨ (lit = s.lit1 r ∧ other = s.lit0 r) := by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · left; exact ⟨hlit.symm, hoth.symm⟩
    · right; exact ⟨hlit.symm, hoth.symm⟩
  have hclit : countRef r (s.entries lit) = 1 := by rcases hwatch with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> assumption
  have hcoth : countRef r (s.entries other) = 1 := by rcases hwatch with ⟨_, h1⟩ | ⟨_, h1⟩ <;> rw [h1] <;> assumption
  have hmem : ∀ k, k < (s.arena.size r).toNat → s.arena.lit r k ∈ s.clauseL r := fun k hk => lit_mem_litsL _ _ _ hk
  have hvlit : s.ValidLit lit := by rw [← hlit]; exact g7 _ (hmem i (by omega))
  have hvhl : s.ValidLit hl' := by rw [← hhl]; exact g7 _ (hmem j hj)
  have hvoth : s.ValidLit other := by rw [← hoth]; exact g7 _ (hmem (1 - i) (by omega))
  obtain ⟨eV, eD, eAsg, eAna, eLev, eProp, eFr, eA⟩ := mw_frame s lit hl' other r
    ((s.arena.setLit r j lit).setLit r i hl')
  rw [← ht] at eV eD eAsg eAna eLev eProp eFr eA
  -- step 1: unwatch
  obtain ⟨u1, u2⟩ := unwatchBlocking_spec hW hvlit hrr hclit
  -- step 2: the arena swap
  obtain ⟨sw1, sw2, sw3, sw4, sw5⟩ := swap_writeOK hl hr.1 (i := i) (j := j) (by omega) hj (by omega)
  rw [hlit, hhl] at sw1 sw2 sw3 sw4 sw5
  generalize hs3 : ({ s.unwatchBlocking lit r with arena := (s.arena.setLit r j lit).setLit r i hl' } : Solver) = s3 at ht
  have e3a : s3.arena = (s.arena.setLit r j lit).setLit r i hl' := by rw [← hs3]
  have e3w : s3.watches = (s.unwatchBlocking lit r).watches := by rw [← hs3]
  have e3E : s3.entries = (s.unwatchBlocking lit r).entries := by funext l; simp [entries, watchesOf, e3w]
  -- step 3: the new watch
  have hsz3w : s3.watches.size = s.watches.size := by rw [e3w, u2]
  have ad := watchBlocking_adds s3 hl' other r (by rw [hsz3w]; exact (validLit_toNat hW hvhl).2.2)
  have adE := ad.entries (fun l => by simp only [watchesOf, e3w]; exact (u1 l).2)
    (show WEntry.WF (.large other r) from ⟨(validLit_toNat hW hvoth).2.1, hrr⟩)
  rw [← ht] at adE
  have hent : ∀ l, t.entries l = (if l = hl' then
      ((if l = lit then (s.entries l).filter (keepRef r) else s.entries l) ++ [WEntry.large other r])
      else (if l = lit then (s.entries l).filter (keepRef r) else s.entries l)) := by
    intro l; rw [(adE l).1, e3E, (u1 l).1]
  have hch : t.arena.chain 0 t.arena.sizeWards = s.arena.chain 0 s.arena.sizeWards := by rw [eA]; exact sw1.chain
  have hgar : ∀ x ∈ s.arena.chain 0 s.arena.sizeWards, t.arena.garbage x = s.arena.garbage x := by
    intro x hx; unfold garbage flag; rw [eA, sw1.word0 x hx]
  have hLive : ∀ x, t.LiveRef x ↔ s.LiveRef x := by
    intro x; unfold LiveRef refsL; rw [hch]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← hgar x h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hgar x h1]; exact h2⟩
  have hclr : t.clauseL r = ((s.clauseL r).set j lit).set i hl' := by
    rw [clauseL_eq_litsL, eA, sw2]; rfl
  have hperm : (t.clauseL r).Perm (s.clauseL r) := by rw [clauseL_eq_litsL, eA]; exact sw3
  have hcl_other : ∀ x ∈ s.arena.chain 0 s.arena.sizeWards, x ≠ r → t.clauseL x = s.clauseL x := by
    intro x hx hxr; rw [clauseL_eq_litsL, clauseL_eq_litsL, eA]; exact (sw1.others x hx hxr).1
  have hsize_r : (t.arena.size r).toNat = (s.arena.size r).toNat := by rw [eA, sw1.size r hr.1]
  have hlit_t : ∀ k, k < (s.arena.size r).toNat → t.arena.lit r k =
      if k = i then hl' else if k = j then lit else s.arena.lit r k := by
    intro k hk; rw [eA]; exact sw5 k hk
  have hti : t.arena.lit r i = hl' := by rw [hlit_t i (by omega)]; simp
  have hto : t.arena.lit r (1 - i) = other := by
    rw [hlit_t (1 - i) (by omega), if_neg (by omega), if_neg (by omega), hoth]
  have hlit_other : ∀ x ∈ s.arena.chain 0 s.arena.sizeWards, x ≠ r → ∀ k, k < (s.arena.size x).toNat →
      t.arena.lit x k = s.arena.lit x k := by
    intro x hx hxr k hk
    have := (sw1.others x hx hxr).1
    rw [← eA] at this
    have hk' : k < (t.arena.litsL x).length := by rw [length_litsL, eA, sw1.size x hx]; exact hk
    rw [← getElem_litsL _ _ _ hk', ← getElem_litsL _ _ _ (by rw [length_litsL]; exact hk)]
    simp only [this]
  -- counts
  have hcnt_hl : countRef r (s.entries hl') = 0 := by
    apply countRef_zero; intro b hb
    have := (hW.refOK hl' b r hb).2 hr.2
    rcases this.1 with e | e
    · rcases hwatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne1 (e.trans h1.symm)
      · exact hne2 (e.trans h2.symm)
    · rcases hwatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne2 (e.trans h2.symm)
      · exact hne1 (e.trans h1.symm)
  have hcount_ne : ∀ l x, x ≠ r → countRef x (t.entries l) = countRef x (s.entries l) := by
    intro l x hx
    rw [hent]
    by_cases e1 : l = hl' <;> by_cases e2 : l = lit
    · subst e1; exact absurd e2 hne1
    · rw [if_pos e1, if_neg e2, countRef_append]; simp [countRef, Ne.symm hx]
    · rw [if_neg e1, if_pos e2]; exact countRef_filter_ne r x hx _
    · rw [if_neg e1, if_neg e2]
  have hBin : ∀ a b, t.BinWatched a b ↔ s.BinWatched a b := by
    intro a b; unfold BinWatched; rw [hent]
    by_cases e1 : a = hl' <;> by_cases e2 : a = lit
    · subst e1; exact absurd e2 hne1
    · rw [if_pos e1, if_neg e2]; simp
    · rw [if_neg e1, if_pos e2, mem_filter_keepRef]; simp
    · rw [if_neg e1, if_neg e2]
  refine ⟨⟨fun l => (adE l).2, ?_, ?_, ?_, by rw [eD]; exact hW.delayed, ?_,
    by rw [eV]; exact hW.varsBound⟩, by rw [eA]; exact sw1.layout, by rw [eA]; exact sw1, hperm, hBin, hti, eAsg, eV, eAna,
    eLev, eProp, eFr, eD⟩
  · -- refOK
    intro l b x hm
    rw [hent] at hm
    unfold refsL; rw [hch]
    have old : ∀ (hm' : WEntry.large b x ∈ s.entries l), (x = r → l ≠ lit) →
        x ∈ s.arena.chain 0 s.arena.sizeWards ∧ (t.arena.garbage x = false →
          (l = t.lit0 x ∨ l = t.lit1 x) ∧ b ∈ t.clauseL x) := by
      intro hm' hxl
      obtain ⟨k1, k2⟩ := hW.refOK l b x hm'
      refine ⟨k1, fun hg => ?_⟩
      rw [hgar x k1] at hg
      obtain ⟨k3, k4⟩ := k2 hg
      by_cases hxr : x = r
      · subst hxr
        have hl0 : l = other := by
          rcases k3 with e | e <;> rcases hwatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd (e.trans h1.symm) (hxl rfl)
          · exact e.trans h2.symm
          · exact e.trans h2.symm
          · exact absurd (e.trans h1.symm) (hxl rfl)
        refine ⟨?_, hperm.mem_iff.mpr k4⟩
        rw [hl0]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · right; unfold lit1; exact hto.symm
        · left; unfold lit0; exact hto.symm
      · have hlv := (hW.live x ⟨k1, hg⟩).1
        refine ⟨?_, by rw [hcl_other x k1 hxr]; exact k4⟩
        rcases k3 with e | e
        · left; unfold lit0 at *; rw [hlit_other x k1 hxr 0 (by omega)]; exact e
        · right; unfold lit1 at *; rw [hlit_other x k1 hxr 1 (by omega)]; exact e
    by_cases e1 : l = hl'
    · rw [if_pos e1] at hm
      rcases List.mem_append.mp hm with hm | hm
      · rw [if_neg (by rw [e1]; exact hne1)] at hm
        exact old hm (fun _ => by rw [e1]; exact hne1)
      · simp at hm; obtain ⟨rfl, rfl⟩ := hm
        refine ⟨hr.1, fun _ => ⟨?_, by rw [hperm.mem_iff]; rw [← hoth]; exact hmem _ (by omega)⟩⟩
        rw [e1]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · left; unfold lit0; exact hti.symm
        · right; unfold lit1; exact hti.symm
    · rw [if_neg e1] at hm
      by_cases e2 : l = lit
      · rw [if_pos e2] at hm
        obtain ⟨hm1, hm2⟩ := mem_filter_keepRef.mp hm
        exact old hm1 (fun hx => absurd (by rw [hx]) (hm2 b))
      · rw [if_neg e2] at hm
        exact old hm (fun _ => e2)
  · -- live
    intro x hx
    have hx' := (hLive x).mp hx
    by_cases hxr : x = r
    · subst hxr
      refine ⟨by rw [hsize_r]; exact g1, by rw [hperm.nodup_iff]; exact g2, by rw [eA, sw4]; exact g3,
        by rw [eA, sw4, ← eA, hsize_r]; exact g4, ?_, ?_, fun y hy => by
          unfold ValidLit; rw [eV]; exact g7 y (hperm.mem_iff.mp hy)⟩
      · rcases (by omega : i = 0 ∨ i = 1) with h0 | h0
        · subst h0
          rw [show t.lit0 x = hl' from hti, hent, if_pos rfl, if_neg hne1, countRef_append, hcnt_hl]; simp [countRef]
        · subst h0
          rw [show t.lit0 x = other from hto, hent, if_neg (Ne.symm hne2), if_neg (Ne.symm hne3)]; exact hcoth
      · rcases (by omega : i = 0 ∨ i = 1) with h0 | h0
        · subst h0
          rw [show t.lit1 x = other from hto, hent, if_neg (Ne.symm hne2), if_neg (Ne.symm hne3)]; exact hcoth
        · subst h0
          rw [show t.lit1 x = hl' from hti, hent, if_pos rfl, if_neg hne1, countRef_append, hcnt_hl]; simp [countRef]
    · obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hW.live x hx'
      have hlv : 3 ≤ (s.arena.size x).toNat := k1
      have esz : t.arena.size x = s.arena.size x := by rw [eA]; exact sw1.size x hx'.1
      have esr : t.arena.searched x = s.arena.searched x := by rw [eA]; exact (sw1.others x hx'.1 hxr).2
      refine ⟨by rw [esz]; exact k1, by rw [hcl_other x hx'.1 hxr]; exact k2, by rw [esr]; exact k3,
        by rw [esr, esz]; exact k4, ?_, ?_, fun y hy => by
          rw [hcl_other x hx'.1 hxr] at hy; unfold ValidLit; rw [eV]; exact k7 y hy⟩
      · rw [show t.lit0 x = s.lit0 x by unfold lit0; exact hlit_other x hx'.1 hxr 0 (by omega), hcount_ne _ _ hxr]
        exact k5
      · rw [show t.lit1 x = s.lit1 x by unfold lit1; exact hlit_other x hx'.1 hxr 1 (by omega), hcount_ne _ _ hxr]
        exact k6
  · -- bin
    intro a b hab
    rw [hBin] at hab
    obtain ⟨k1, k2, k3, k4⟩ := hW.bin a b hab
    exact ⟨(hBin b a).mpr k1, by unfold ValidLit; rw [eV]; exact k2, by unfold ValidLit; rw [eV]; exact k3, k4⟩
  · -- watches size
    show 2 * t.vars.toNat ≤ t.watches.size
    have : t.watches.size = s.watches.size := by
      rw [ht]; simp [watchBlocking, modifyWatches]; rw [hsz3w]
    rw [this, eV]; exact hW.watchesSize

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

/-- The relation between the solver before and after re-ordering the literals of the live
  clause `r` (watches follow). -/
structure MoveRel (s t : Solver) (r : Ref) : Prop where
  ws : t.WatchStruct
  layout : t.arena.Layout
  write : WriteOK s.arena t.arena r
  perm : (t.clauseL r).Perm (s.clauseL r)
  bin : ∀ a b, t.BinWatched a b ↔ s.BinWatched a b
  asg : t.asg = s.asg
  vars : t.vars = s.vars
  ana : anaSide t = anaSide s
  level : t.level = s.level
  propagate : t.propagate = s.propagate
  frameTrail : t.frameTrail = s.frameTrail
  delayed : t.delayed = s.delayed

theorem MoveRel.refl {s : Solver} (hW : s.WatchStruct) (hl : s.arena.Layout) (r : Ref) : MoveRel s s r :=
  ⟨hW, hl, WriteOK.refl _ _ hl, List.Perm.refl _, fun _ _ => Iff.rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MoveRel.trans {s t u : Solver} {r : Ref} (h1 : MoveRel s t r) (h2 : MoveRel t u r) : MoveRel s u r :=
  ⟨h2.ws, h2.layout, h1.write.trans h2.write, h2.perm.trans h1.perm, fun a b => (h2.bin a b).trans (h1.bin a b),
   h2.asg.trans h1.asg, h2.vars.trans h1.vars, h2.ana.trans h1.ana, h2.level.trans h1.level,
   h2.propagate.trans h1.propagate, h2.frameTrail.trans h1.frameTrail, h2.delayed.trans h1.delayed⟩

theorem MoveRel.live {s t : Solver} {r : Ref} (h : MoveRel s t r) : ∀ x, t.LiveRef x ↔ s.LiveRef x := by
  intro x; unfold LiveRef refsL; rw [h.write.chain]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by unfold garbage flag at *; rw [← h.write.word0 x h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by unfold garbage flag at *; rw [h.write.word0 x h1]; exact h2⟩

theorem MoveRel.clauseL {s t : Solver} {r : Ref} (h : MoveRel s t r) :
    ∀ x ∈ s.arena.chain 0 s.arena.sizeWards, x ≠ r → t.clauseL x = s.clauseL x := by
  intro x hx hxr; rw [clauseL_eq_litsL, clauseL_eq_litsL]; exact (h.write.others x hx hxr).1

theorem MoveRel.irrMono {s t : Solver} {r : Ref} (h : MoveRel s t r) : IrrMono s t := by
  apply IrrMono.of_large
  · intro x h1 h2
    refine ⟨(h.live x).mpr h1, ?_, fun y hy => ?_⟩
    · rw [redundant_of_word0 (h.write.word0 x h1.1)]; exact h2
    · by_cases hxr : x = r
      · subst hxr; exact h.perm.mem_iff.mp hy
      · rw [h.clauseL x h1.1 hxr] at hy; exact hy
  · intro a b hab; exact (h.bin a b).mpr hab
  · intro l hl; unfold RootTrue IsTrue lvl at *; rw [h.asg]; exact hl

theorem anaSide_arena (s : Solver) (A : Arena) : anaSide ({ s with arena := A } : Solver) = anaSide s := rfl

/-- Swapping the two watched literals of a live clause. -/
theorem swap01_rel {s : Solver} (hW : s.WatchStruct) (hl : s.arena.Layout) {r : Ref} (hr : s.LiveRef r) :
    MoveRel s ({ s with arena := (s.arena.setLit r 1 (s.arena.lit r 0)).setLit r 0 (s.arena.lit r 1) } : Solver) r := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hW.live r hr
  obtain ⟨sw1, sw2, sw3, sw4, sw5⟩ := swap_writeOK hl hr.1 (i := 0) (j := 1) (by omega) (by omega) (by omega)
  generalize ht : ({ s with arena := (s.arena.setLit r 1 (s.arena.lit r 0)).setLit r 0 (s.arena.lit r 1) } : Solver) = t
  have eA : t.arena = (s.arena.setLit r 1 (s.arena.lit r 0)).setLit r 0 (s.arena.lit r 1) := by rw [← ht]
  have eW : t.watches = s.watches := by rw [← ht]
  have eE : t.entries = s.entries := by funext l; simp [entries, watchesOf, eW]
  have eV : t.vars = s.vars := by rw [← ht]
  have hch : t.arena.chain 0 t.arena.sizeWards = s.arena.chain 0 s.arena.sizeWards := by rw [eA]; exact sw1.chain
  have hgar : ∀ x ∈ s.arena.chain 0 s.arena.sizeWards, t.arena.garbage x = s.arena.garbage x := by
    intro x hx; unfold garbage flag; rw [eA, sw1.word0 x hx]
  have hperm : (t.clauseL r).Perm (s.clauseL r) := by rw [clauseL_eq_litsL, eA]; exact sw3
  have hl0 : t.lit0 r = s.lit1 r := by unfold lit0 lit1; rw [eA, sw5 0 (by omega)]; simp
  have hl1 : t.lit1 r = s.lit0 r := by unfold lit0 lit1; rw [eA, sw5 1 (by omega)]; simp
  have hlit_other : ∀ x ∈ s.arena.chain 0 s.arena.sizeWards, x ≠ r → ∀ k, k < (s.arena.size x).toNat →
      t.arena.lit x k = s.arena.lit x k := by
    intro x hx hxr k hk
    have := (sw1.others x hx hxr).1
    rw [← eA] at this
    have hk' : k < (t.arena.litsL x).length := by rw [length_litsL, eA, sw1.size x hx]; exact hk
    rw [← getElem_litsL _ _ _ hk', ← getElem_litsL _ _ _ (by rw [length_litsL]; exact hk)]
    simp only [this]
  have hcl_other : ∀ x ∈ s.arena.chain 0 s.arena.sizeWards, x ≠ r → t.clauseL x = s.clauseL x := by
    intro x hx hxr; rw [clauseL_eq_litsL, clauseL_eq_litsL, eA]; exact (sw1.others x hx hxr).1
  have hLive : ∀ x, t.LiveRef x ↔ s.LiveRef x := by
    intro x; unfold LiveRef refsL; rw [hch]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← hgar x h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hgar x h1]; exact h2⟩
  refine ⟨⟨fun l => by simp only [watchesOf, eW]; exact hW.words l, ?_, ?_, ?_, by rw [← ht]; exact hW.delayed,
    by rw [eW, eV]; exact hW.watchesSize, by rw [eV]; exact hW.varsBound⟩, by rw [eA]; exact sw1.layout,
    by rw [eA]; exact sw1, hperm, fun a b => by unfold BinWatched; rw [eE], by rw [← ht], eV, by rw [← ht]; exact anaSide_arena _ _,
    by rw [← ht], by rw [← ht], by rw [← ht], by rw [← ht]⟩
  · intro l b x hm
    rw [eE] at hm
    obtain ⟨k1, k2⟩ := hW.refOK l b x hm
    unfold refsL; rw [hch]
    refine ⟨k1, fun hg => ?_⟩
    rw [hgar x k1] at hg
    obtain ⟨k3, k4⟩ := k2 hg
    by_cases hxr : x = r
    · subst hxr
      exact ⟨by rw [hl0, hl1]; exact k3.symm, hperm.mem_iff.mpr k4⟩
    · have hlv := (hW.live x ⟨k1, hg⟩).1
      refine ⟨?_, by rw [hcl_other x k1 hxr]; exact k4⟩
      rcases k3 with e | e
      · left; unfold lit0 at *; rw [hlit_other x k1 hxr 0 (by omega)]; exact e
      · right; unfold lit1 at *; rw [hlit_other x k1 hxr 1 (by omega)]; exact e
  · intro x hx
    have hx' := (hLive x).mp hx
    by_cases hxr : x = r
    · subst hxr
      have esz : t.arena.size x = s.arena.size x := by rw [eA]; exact sw1.size x hx'.1
      refine ⟨by rw [esz]; exact g1, by rw [hperm.nodup_iff]; exact g2, by rw [eA, sw4]; exact g3,
        by rw [eA, sw4, ← eA, esz]; exact g4, by rw [hl0, eE]; exact g6, by rw [hl1, eE]; exact g5,
        fun y hy => by unfold ValidLit; rw [eV]; exact g7 y (hperm.mem_iff.mp hy)⟩
    · obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hW.live x hx'
      have hlv : 3 ≤ (s.arena.size x).toNat := k1
      have esz : t.arena.size x = s.arena.size x := by rw [eA]; exact sw1.size x hx'.1
      have esr : t.arena.searched x = s.arena.searched x := by rw [eA]; exact (sw1.others x hx'.1 hxr).2
      refine ⟨by rw [esz]; exact k1, by rw [hcl_other x hx'.1 hxr]; exact k2, by rw [esr]; exact k3,
        by rw [esr, esz]; exact k4, ?_, ?_, fun y hy => by
          rw [hcl_other x hx'.1 hxr] at hy; unfold ValidLit; rw [eV]; exact k7 y hy⟩
      · rw [show t.lit0 x = s.lit0 x by unfold lit0; exact hlit_other x hx'.1 hxr 0 (by omega), eE]; exact k5
      · rw [show t.lit1 x = s.lit1 x by unfold lit1; exact hlit_other x hx'.1 hxr 1 (by omega), eE]; exact k6
  · intro a b hab
    have hab' : s.BinWatched a b := by unfold BinWatched at *; rw [eE] at hab; exact hab
    obtain ⟨k1, k2, k3, k4⟩ := hW.bin a b hab'
    exact ⟨by unfold BinWatched at *; rw [eE]; exact k1, by unfold ValidLit; rw [eV]; exact k2,
      by unfold ValidLit; rw [eV]; exact k3, k4⟩

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem moveHighest_rel {s : Solver} (hW : s.WatchStruct) (hl : s.arena.Layout) {r : Ref} (hr : s.LiveRef r)
    (cl : UInt32) {i : Nat} (hi : i ≤ 1) :
    MoveRel s (s.moveHighest (.large r) (s.arena.size r).toNat cl i) r := by
  have hsz3 := (hW.live r hr).1
  unfold moveHighest
  dsimp only
  obtain ⟨h1, h2, h3⟩ := highestLoop_spec s (.large r) (s.arena.size r).toNat cl i (i + 1) i (s.crefLit (.large r) i)
    (s.level' (s.crefLit (.large r) i)) (by omega) rfl (Nat.le_refl _) (by omega)
  generalize s.highestLoop (.large r) (s.arena.size r).toNat cl (i + 1) i (s.crefLit (.large r) i)
    (s.level' (s.crefLit (.large r) i)) = H at h1 h2 h3 ⊢
  obtain ⟨hp, hlit⟩ := H
  dsimp only at h1 h2 h3 ⊢
  split
  · exact MoveRel.refl hW hl r
  rename_i hne
  have hne' : hp ≠ i := by simpa using hne
  have hcl : ∀ (t : Solver) k, t.crefLit (.large r) k = t.arena.lit r k := fun _ _ => rfl
  rw [hcl] at h1
  by_cases hgt : hp > 1
  · simp only [hgt, ite_true, decide_true]
    obtain ⟨sw1, sw2, sw3, sw4, sw5⟩ := swap_writeOK hl hr.1 (i := i) (j := hp) (by omega) h3 (by omega)
    have hread : ∀ k, k < (s.arena.size r).toNat →
        ((s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp)).lit r k =
          if k = i then s.arena.lit r hp else if k = hp then s.arena.lit r i else s.arena.lit r k := sw5
    have e1 : ((s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp)).lit r i = s.arena.lit r hp := by
      rw [hread i (by omega)]; simp
    have e2 : ((s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp)).lit r (1 - i) =
        s.arena.lit r (1 - i) := by
      rw [hread (1 - i) (by omega), if_neg (by omega), if_neg (by omega)]
    have key : ∀ t, t = ({ s.unwatchBlocking (s.arena.lit r i) r with arena := (s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp) } : Solver).watchBlocking (s.arena.lit r hp) (s.arena.lit r (1 - i)) r → MoveRel s t r := by
      intro t ht
      obtain ⟨m1, m2, m3, m4, m5, _, m7, m8, m9, m10, m11, m12, m13⟩ := moveWatch_ws hW hl hr hi hgt h3 ht
      exact ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10, m11, m12, m13⟩
    apply key
    rw [h1]
    have f1 : ({ s.unwatchBlocking (s.arena.lit r i) r with arena := (s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp) } : Solver).crefLit (.large r) i = s.arena.lit r hp := e1
    have f2 : ({ s.unwatchBlocking (s.arena.lit r i) r with arena := (s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp) } : Solver).crefLit (.large r) (1 - i) = s.arena.lit r (1 - i) := e2
    show (({ s.unwatchBlocking (s.arena.lit r i) r with arena := (s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp) } : Solver).watchBlocking (({ s.unwatchBlocking (s.arena.lit r i) r with arena := (s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp) } : Solver).crefLit (.large r) i) (({ s.unwatchBlocking (s.arena.lit r i) r with arena := (s.arena.setLit r hp (s.arena.lit r i)).setLit r i (s.arena.lit r hp) } : Solver).crefLit (.large r) (1 - i)) r) = _
    rw [f1, f2]

  · have hp1 : hp = 1 := by omega
    have hi0 : i = 0 := by omega
    subst hp1; subst hi0
    simp only [hgt, ite_false, decide_false]
    rw [h1]
    exact swap01_rel hW hl hr

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem clStep {s : Solver} {c : CRef} {i : Nat} {jl cl : UInt32} {on : Nat} {fl : Lit}
    {jl' cl' : UInt32} {on' : Nat} {fl' : Lit} (hL : s.level < INVALID_LEVEL)
    (hall : ∀ k, k ≤ i → s.level' (s.crefLit c k) ≤ s.level)
    (hinv : (i = 0 ∧ cl = INVALID_LEVEL) ∨ (1 ≤ i ∧ (∃ k, k < i ∧ fl = s.crefLit c k ∧ s.level' fl = cl) ∧
        ∀ k, k < i → s.level' (s.crefLit c k) ≤ cl))
    (hstep : (if (cl == INVALID_LEVEL || Decidable.decide (cl < s.level' (s.crefLit c i))) = true then
        (cl, s.level' (s.crefLit c i), 1, s.crefLit c i)
      else ((if (jl == INVALID_LEVEL || Decidable.decide (jl < s.level' (s.crefLit c i))) = true then
          s.level' (s.crefLit c i) else jl), cl,
        (if (cl == s.level' (s.crefLit c i)) = true then on + 1 else on), fl)) = (jl', cl', on', fl')) :
    (∃ k, k < i + 1 ∧ fl' = s.crefLit c k ∧ s.level' fl' = cl') ∧
      ∀ k, k < i + 1 → s.level' (s.crefLit c k) ≤ cl' := by
  have hli : s.level' (s.crefLit c i) ≤ s.level := hall i (Nat.le_refl _)
  have hinvL : s.level' (s.crefLit c i) ≠ INVALID_LEVEL := by
    intro e; rw [e] at hli; exact absurd (UInt32.lt_of_le_of_lt hli hL) (UInt32.lt_irrefl _)
  split at hstep
  · rename_i hc
    simp only [Prod.mk.injEq] at hstep
    obtain ⟨_, rfl, _, rfl⟩ := hstep
    refine ⟨⟨i, by omega, rfl, rfl⟩, fun k hk => ?_⟩
    by_cases e : k = i
    · subst e; exact UInt32.le_refl _
    · rcases hinv with ⟨h0, _⟩ | ⟨h1, ⟨k0, hk0, hfl, hcl⟩, h3⟩
      · omega
      · have hclL : cl ≠ INVALID_LEVEL := by
          rw [← hcl, hfl]; intro e
          have := hall k0 (by omega); rw [e] at this; exact absurd (UInt32.lt_of_le_of_lt this hL) (UInt32.lt_irrefl _)
        simp only [Bool.or_eq_true, beq_iff_eq, hclL, false_or, decide_eq_true_eq] at hc
        exact UInt32.le_of_lt (UInt32.lt_of_le_of_lt (h3 k (by omega)) hc)
  · rename_i hc
    simp only [Prod.mk.injEq] at hstep
    obtain ⟨_, rfl, _, rfl⟩ := hstep
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hc
    obtain ⟨hc1, hc2⟩ := hc
    rcases hinv with ⟨_, h0⟩ | ⟨h1, ⟨k0, hk0, hfl, hcl⟩, h3⟩
    · exact absurd h0 hc1
    · refine ⟨⟨k0, by omega, hfl, hcl⟩, fun k hk => ?_⟩
      by_cases e : k = i
      · subst e; exact UInt32.not_lt.mp hc2
      · exact h3 k (by omega)

theorem conflictLevelLoop_spec (s : Solver) (c : CRef) (size : Nat) (hL : s.level < INVALID_LEVEL)
    (hall : ∀ k, k < size → s.level' (s.crefLit c k) ≤ s.level) :
    ∀ (i : Nat) (jl cl : UInt32) (on : Nat) (fl : Lit), i ≤ size →
      ((i = 0 ∧ cl = INVALID_LEVEL) ∨ (1 ≤ i ∧ (∃ k, k < i ∧ fl = s.crefLit c k ∧ s.level' fl = cl) ∧
        ∀ k, k < i → s.level' (s.crefLit c k) ≤ cl)) → 1 ≤ size →
      (∃ k, k < size ∧ (s.conflictLevelLoop c size i jl cl on fl).2.2.2 = s.crefLit c k ∧
        s.level' (s.conflictLevelLoop c size i jl cl on fl).2.2.2 = (s.conflictLevelLoop c size i jl cl on fl).2.1) ∧
      ∀ k, k < size → s.level' (s.crefLit c k) ≤ (s.conflictLevelLoop c size i jl cl on fl).2.1 := by
  intro i jl cl on fl
  fun_induction conflictLevelLoop s c size i jl cl on fl with
  | case1 i jl cl on fl hi lit litLevel jl' cl' on' fl' hstep hbrk =>
    intro _ hinv _
    obtain ⟨⟨k, hk, h1, h2⟩, h3⟩ := clStep hL (fun k hk => hall k (by omega)) hinv hstep
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbrk
    refine ⟨⟨k, by omega, h1, h2⟩, fun k' hk' => ?_⟩
    by_cases e : k' < i + 1
    · exact h3 k' e
    · show s.level' (s.crefLit c k') ≤ cl'
      rw [hbrk.2]; exact hall k' hk'
  | case2 i jl cl on fl hi lit litLevel jl' cl' on' fl' hstep hbrk ih =>
    intro _ hinv hsz
    obtain ⟨h1, h3⟩ := clStep hL (fun k hk => hall k (by omega)) hinv hstep
    exact ih (by omega) (Or.inr ⟨by omega, h1, h3⟩) hsz
  | case3 i jl cl on fl hi =>
    intro hle hinv hsz
    have hi' : i = size := by omega
    subst hi'
    rcases hinv with ⟨h0, _⟩ | ⟨_, h1, h2⟩
    · omega
    · exact ⟨h1, h2⟩

end Solver
end LeanKissat
