import LeanKissat.Proofs.PropStep

/-!
# Watch-list structure across a propagation round

`WSA a vars E`: the structural watch facts for arena `a` and abstract watch lists `E`.
During the round the abstract watch lists are `WL`: the list of `notLit` is the output
so far followed by the unprocessed entries, every other list is its original content
followed by the delayed watches targeting it.
-/

namespace LeanKissat
namespace Solver
open Arena

/-- Entries whose literals and references fit in 31 bits (so they survive encoding). -/
def WEntry.WF : WEntry → Prop
  | .bin b => b.toNat < 2 ^ 31
  | .large b r => b.toNat < 2 ^ 31 ∧ r.toNat < 2 ^ 31

theorem lt31 {b : UInt32} (h : b.toNat < 2 ^ 31) : b < 0x80000000 := by
  rw [UInt32.lt_iff_toNat_lt]; simpa using h

theorem watchLit_lt (w : UInt32) : (watchLit w).toNat < 2 ^ 31 := by
  have : watchLit w < 0x80000000 := by simp only [watchLit]; bv_k
  rw [UInt32.lt_iff_toNat_lt] at this; simpa using this

theorem parse_wf : ∀ (W : List UInt32), ∀ e ∈ parseWatches W, e.WF
  | [] => by simp [parseWatches]
  | w :: rest => by
    rw [parseWatches.eq_def]
    simp only
    split
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact watchLit_lt w
      · exact parse_wf rest e he
    · match rest with
      | t :: rest' =>
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨watchLit_lt w, watchLit_lt t⟩
        · exact parse_wf rest' e he
      | [] => simp

theorem parse_encode : ∀ (E : List WEntry), (∀ e ∈ E, e.WF) →
    parseWatches (encodeWatches E) = E ∧ WordsOK (encodeWatches E)
  | [], _ => ⟨rfl, trivial⟩
  | .bin b :: E, h => by
    have hb := lt31 (h (.bin b) (List.mem_cons_self ..))
    obtain ⟨ih1, ih2⟩ := parse_encode E (fun e he => h e (List.mem_cons_of_mem _ he))
    have h1 : watchIsBinary (binaryWatch b) = true := by
      simp only [watchIsBinary, binaryWatch, WATCH_BINARY_BIT, bne_iff_ne, ne_eq]; bv_k
    have h2 : watchLit (binaryWatch b) = b := by
      simp only [watchLit, binaryWatch, WATCH_BINARY_BIT]; bv_k
    have e : encodeWatches (.bin b :: E) = binaryWatch b :: encodeWatches E := rfl
    rw [e]
    constructor
    · rw [parseWatches.eq_def]; simp only [h1, ite_true, h2, ih1]
    · unfold WordsOK; simp only [h1, ite_true]; exact ih2
  | .large b r :: E, h => by
    obtain ⟨hb, hr⟩ := h (.large b r) (List.mem_cons_self ..)
    have hb := lt31 hb
    have hr := lt31 hr
    obtain ⟨ih1, ih2⟩ := parse_encode E (fun e he => h e (List.mem_cons_of_mem _ he))
    have h1 : watchIsBinary (blockingWatch b) = false := by
      simp only [watchIsBinary, blockingWatch, WATCH_BINARY_BIT, bne_eq_false_iff_eq]; bv_k
    have h2 : watchLit (blockingWatch b) = b := by
      simp only [watchLit, blockingWatch]; bv_k
    have h3 : watchIsBinary (largeWatch r) = false := by
      simp only [watchIsBinary, largeWatch, WATCH_BINARY_BIT, bne_eq_false_iff_eq]; bv_k
    have h4 : watchRef (largeWatch r) = r := by
      simp only [watchRef, largeWatch]; bv_k
    have e : encodeWatches (.large b r :: E) = blockingWatch b :: largeWatch r :: encodeWatches E := rfl
    rw [e]
    constructor
    · rw [parseWatches.eq_def]; simp only [h1, Bool.false_eq_true, ite_false, h2, h4, ih1]
    · unfold WordsOK; simp only [h1, Bool.false_eq_true, ite_false]; exact ⟨h3, ih2⟩

structure WSA (a : Arena) (vars : UInt32) (E : Lit → List WEntry) : Prop where
  refOK : ∀ l b r, WEntry.large b r ∈ E l → r ∈ a.chain 0 a.sizeWards ∧
    (a.garbage r = false → (l = a.lit r 0 ∨ l = a.lit r 1) ∧ b ∈ a.litsL r)
  live : ∀ r, r ∈ a.chain 0 a.sizeWards → a.garbage r = false →
    3 ≤ (a.size r).toNat ∧ (a.litsL r).Nodup ∧ 2 ≤ (a.searched r).toNat ∧
    (a.searched r).toNat < (a.size r).toNat ∧
    countRef r (E (a.lit r 0)) = 1 ∧ countRef r (E (a.lit r 1)) = 1 ∧
    (∀ x ∈ a.litsL r, (IDX x).toNat < vars.toNat)
  bin : ∀ x y, WEntry.bin y ∈ E x → WEntry.bin x ∈ E y ∧ (IDX x).toNat < vars.toNat ∧
    (IDX y).toNat < vars.toNat ∧ x ≠ y

theorem WatchStruct.wsa {s : Solver} (h : s.WatchStruct) : WSA s.arena s.vars s.entries :=
  ⟨h.refOK, fun r hr hg => h.live r ⟨hr, hg⟩, h.bin⟩

def delayedFor (d : List (Lit × Lit × Ref)) (l : Lit) : List WEntry :=
  d.filterMap (fun x => if x.1 = l then some (.large x.2.1 x.2.2) else none)

theorem delayedFor_nil (l : Lit) : delayedFor [] l = [] := rfl

theorem delayedFor_append (d : List (Lit × Lit × Ref)) (x : Lit × Lit × Ref) (l : Lit) :
    delayedFor (d ++ [x]) l = delayedFor d l ++ (if x.1 = l then [.large x.2.1 x.2.2] else []) := by
  unfold delayedFor; rw [List.filterMap_append]; by_cases h : x.1 = l <;> simp [h]

theorem mem_delayedFor {d : List (Lit × Lit × Ref)} {l : Lit} {e : WEntry} :
    e ∈ delayedFor d l ↔ ∃ x ∈ d, x.1 = l ∧ e = .large x.2.1 x.2.2 := by
  unfold delayedFor
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    by_cases hl : x.1 = l
    · simp [hl] at h; exact ⟨x, hx, hl, h.symm⟩
    · simp [hl] at h
  · rintro ⟨x, hx, hl, rfl⟩; exact ⟨x, hx, by simp [hl]⟩

/-- Abstract watch lists during the round. -/
def WL (s0 : Solver) (notLit : Lit) (st : PS) (rest : List WEntry) (l : Lit) : List WEntry :=
  if l = notLit then st.out ++ rest else s0.entries l ++ delayedFor st.delayed l

structure WSInv (s0 : Solver) (notLit : Lit) (st : PS) (rest : List WEntry) : Prop where
  wsa : WSA st.arena s0.vars (WL s0 notLit st rest)
  delayedNe : ∀ d ∈ st.delayed, d.1 ≠ notLit
  bins : ∀ x y, WEntry.bin y ∈ WL s0 notLit st rest x ↔ WEntry.bin y ∈ s0.entries x
  wf : ∀ l, ∀ e ∈ WL s0 notLit st rest l, e.WF
  delayedValid : ∀ d ∈ st.delayed, (IDX d.1).toNat < s0.vars.toNat

theorem WSInv.init (s0 : Solver) (h : s0.WatchStruct) (notLit : Lit) (cold : Solver) :
    WSInv s0 notLit (PS.init s0 cold) (s0.entries notLit) := by
  have hWL : WL s0 notLit (PS.init s0 cold) (s0.entries notLit) = s0.entries := by
    funext l; unfold WL; by_cases e : l = notLit
    · subst e; simp [PS.init]
    · simp [e, PS.init, delayedFor_nil]
  refine ⟨?_, fun d hd => by simp [PS.init] at hd, fun x y => by rw [hWL], ?_,
    fun d hd => by simp [PS.init] at hd⟩
  · rw [hWL]; exact h.wsa
  · rw [hWL]; intro l; exact parse_wf _

/-- Changing nothing but moving the head entry to the output. -/
theorem WSInv.move {s0 : Solver} {notLit : Lit} {st : PS} {e : WEntry} {rest : List WEntry}
    (h : WSInv s0 notLit st (e :: rest)) (st' : PS) (ho : st'.out = st.out ++ [e])
    (har : st'.arena = st.arena) (hd : st'.delayed = st.delayed) : WSInv s0 notLit st' rest := by
  have hWL : WL s0 notLit st' rest = WL s0 notLit st (e :: rest) := by
    funext l; unfold WL; rw [ho, hd]; simp
  refine ⟨?_, ?_, ?_, ?_, by rw [hd]; exact h.delayedValid⟩
  · rw [hWL, har]; exact h.wsa
  · rw [hd]; exact h.delayedNe
  · rw [hWL]; exact h.bins
  · rw [hWL]; exact h.wf

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem WSA.of_same {a : Arena} {v : UInt32} {E : Lit → List WEntry} (h : WSA a v E)
    (E' : Lit → List WEntry)
    (hcount : ∀ x r, r ∈ a.chain 0 a.sizeWards → a.garbage r = false →
      countRef r (E' x) = countRef r (E x))
    (hbin : ∀ x y, WEntry.bin y ∈ E' x ↔ WEntry.bin y ∈ E x)
    (hlarge : ∀ l b r, WEntry.large b r ∈ E' l → r ∈ a.chain 0 a.sizeWards ∧
      (a.garbage r = false → (l = a.lit r 0 ∨ l = a.lit r 1) ∧ b ∈ a.litsL r)) :
    WSA a v E' := by
  refine ⟨hlarge, ?_, ?_⟩
  · intro r hr hg
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.live r hr hg
    exact ⟨h1, h2, h3, h4, by rw [hcount _ _ hr hg]; exact h5, by rw [hcount _ _ hr hg]; exact h6, h7⟩
  · intro x y hm
    obtain ⟨h1, h2, h3, h4⟩ := h.bin x y ((hbin x y).mp hm)
    exact ⟨(hbin y x).mpr h1, h2, h3, h4⟩

theorem countRef_swap (r' : Ref) (A B : List WEntry) (b b' : Lit) (r : Ref) :
    countRef r' (A ++ [WEntry.large b' r] ++ B) = countRef r' (A ++ WEntry.large b r :: B) := by
  simp [countRef_append, countRef]

/-- Move the head entry `large b r` to the output with a new blocking literal. -/
theorem WSInv.reblock {s0 : Solver} {notLit : Lit} {st : PS} {b : Lit} {r : Ref}
    {rest : List WEntry} (h : WSInv s0 notLit st (.large b r :: rest)) (b' : Lit) (st' : PS)
    (ho : st'.out = st.out ++ [.large b' r]) (har : st'.arena = st.arena)
    (hd : st'.delayed = st.delayed) (hb' : st.arena.garbage r = false → b' ∈ st.arena.litsL r)
    (hwf : b'.toNat < 2 ^ 31) :
    WSInv s0 notLit st' rest := by
  have hne : ∀ l, l ≠ notLit → WL s0 notLit st' rest l = WL s0 notLit st (.large b r :: rest) l := by
    intro l hl; unfold WL; simp [hl, hd]
  have heq : WL s0 notLit st' rest notLit = st.out ++ [.large b' r] ++ rest := by
    unfold WL; simp [ho]
  have heq0 : WL s0 notLit st (.large b r :: rest) notLit = st.out ++ .large b r :: rest := by
    unfold WL; simp
  have hbin : ∀ x y, WEntry.bin y ∈ WL s0 notLit st' rest x ↔
      WEntry.bin y ∈ WL s0 notLit st (.large b r :: rest) x := by
    intro x y
    by_cases hx : x = notLit
    · subst hx; rw [heq, heq0]; simp
    · rw [hne x hx]
  refine ⟨?wsa, by rw [hd]; exact h.delayedNe, fun x y => (hbin x y).trans (h.bins x y), ?wf,
    by rw [hd]; exact h.delayedValid⟩
  case wf =>
    intro l e he
    by_cases hl : l = notLit
    · rw [hl, heq] at he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with (he | rfl) | he
      · exact h.wf notLit e (by rw [heq0]; simp [he])
      · exact ⟨hwf, (h.wf notLit (.large b r) (by rw [heq0]; simp)).2⟩
      · exact h.wf notLit e (by rw [heq0]; simp [he])
    · rw [hne l hl] at he; exact h.wf l e he
  case wsa =>
  rw [har]
  refine h.wsa.of_same _ ?_ hbin ?_
  · intro x r' _ _
    by_cases hx : x = notLit
    · subst hx; rw [heq, heq0, countRef_swap]
    · rw [hne x hx]
  · intro l b'' r'' hm
    by_cases hl : l = notLit
    · rw [hl] at hm ⊢
      rw [heq] at hm
      have hold := h.wsa.refOK notLit b r (by rw [heq0]; simp)
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with (hm | hm) | hm
      · exact h.wsa.refOK _ _ _ (by rw [heq0]; simp [hm])
      · cases hm
        exact ⟨hold.1, fun hg => ⟨(hold.2 hg).1, hb' hg⟩⟩
      · exact h.wsa.refOK _ _ _ (by rw [heq0]; simp [hm])
    · rw [hne l hl] at hm; exact h.wsa.refOK _ _ _ hm

/-- Drop the head entry of a garbage clause. -/
theorem WSInv.dropGarbage {s0 : Solver} {notLit : Lit} {st : PS} {b : Lit} {r : Ref}
    {rest : List WEntry} (h : WSInv s0 notLit st (.large b r :: rest))
    (hg : st.arena.garbage r = true) : WSInv s0 notLit st rest := by
  have hne : ∀ l, l ≠ notLit → WL s0 notLit st rest l = WL s0 notLit st (.large b r :: rest) l := by
    intro l hl; unfold WL; simp [hl]
  have heq : WL s0 notLit st rest notLit = st.out ++ rest := by unfold WL; simp
  have heq0 : WL s0 notLit st (.large b r :: rest) notLit = st.out ++ .large b r :: rest := by
    unfold WL; simp
  have hbin : ∀ x y, WEntry.bin y ∈ WL s0 notLit st rest x ↔
      WEntry.bin y ∈ WL s0 notLit st (.large b r :: rest) x := by
    intro x y
    by_cases hx : x = notLit
    · subst hx; rw [heq, heq0]; simp
    · rw [hne x hx]
  refine ⟨?wsa, h.delayedNe, fun x y => (hbin x y).trans (h.bins x y), ?wf, h.delayedValid⟩
  case wf =>
    intro l e he
    by_cases hl : l = notLit
    · rw [hl, heq] at he
      simp only [List.mem_append] at he
      rcases he with he | he
      · exact h.wf notLit e (by rw [heq0]; simp [he])
      · exact h.wf notLit e (by rw [heq0]; simp [he])
    · rw [hne l hl] at he; exact h.wf l e he
  case wsa =>
  refine h.wsa.of_same _ ?_ hbin ?_
  · intro x r' _ hg'
    by_cases hx : x = notLit
    · subst hx; rw [heq, heq0]
      have : r ≠ r' := by intro e; subst e; rw [hg] at hg'; contradiction
      simp [countRef_append, countRef, this]
    · rw [hne x hx]
  · intro l b'' r'' hm
    by_cases hl : l = notLit
    · rw [hl] at hm ⊢
      rw [heq] at hm
      refine h.wsa.refOK _ _ _ ?_
      rw [heq0]; simp only [List.mem_append, List.mem_cons] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inr hm)
    · rw [hne l hl] at hm; exact h.wsa.refOK _ _ _ hm

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem countRef_append_large_ne (r' r : Ref) (L : List WEntry) (b : Lit) (h : r ≠ r') :
    countRef r' (L ++ [WEntry.large b r]) = countRef r' L := by
  simp [countRef_append, countRef, h]

theorem countRef_drop_ne (r' r : Ref) (A B : List WEntry) (b : Lit) (h : r ≠ r') :
    countRef r' (A ++ B) = countRef r' (A ++ WEntry.large b r :: B) := by
  simp [countRef_append, countRef, h]

theorem WSInv.replace {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {b : Lit} {r : Ref} (H : StepHyp s0 i lit st done rest (.large b r))
    (F : LargeFacts s0 lit st done b r) (h : WSInv s0 (NOT lit) st (.large b r :: rest))
    (hg : st.arena.garbage r = false)
    (R : Nat) (hR2 : 2 ≤ R) (hRs : R < (st.arena.size r).toNat)
    (hnf : vFalse (st.a.values.get! (st.arena.lit r R).toNat) = false) :
    WSInv s0 (NOT lit) { st with arena := st.arena.replaceArena r R (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit) (NOT lit), delayed := st.delayed ++ [(st.arena.lit r R, st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit, r)] } rest := by
  generalize hother : st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit = other
  have hw := F.watch
  rw [hother] at hw
  have hlay := H.run.arena.layout
  obtain ⟨W, hperm, _, hsearch⟩ := replace_writeOK hlay F.chain hR2 hRs other (NOT lit) hw
  obtain ⟨hw0, hw1⟩ := replaced_watches hlay F.chain hR2 hRs other (NOT lit) hw
  generalize hrepl : st.arena.lit r R = repl at hnf hw1 ⊢
  generalize st.arena.replaceArena r R other (NOT lit) = a' at W hperm hw0 hw1 hsearch ⊢
  have hRnf : ¬ (V s0 st).IsFalse repl := by
    rw [isFalse_iff_vFalse]; simp [V_a, hnf]
  have hneR : repl ≠ NOT lit := by
    intro e; rw [e] at hRnf; exact hRnf H.notLitFalse
  have hRlt : R < 2 ^ 32 := by have := UInt32.toNat_lt (st.arena.size r); omega
  have hneo : other ≠ NOT lit := by
    rcases hw with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · rw [← h0, ← h1]; exact F.ne01.symm
    · rw [← h0, ← h1]; exact F.ne01
  -- `repl` is not one of the old watches
  have hRw : repl ≠ st.arena.lit r 0 ∧ repl ≠ st.arena.lit r 1 := by
    have hlen : (st.arena.litsL r).length = (st.arena.size r).toNat := length_litsL _ _
    have g : ∀ k (hk : k < (st.arena.size r).toNat), (st.arena.litsL r)[k]'(by omega) = st.arena.lit r k :=
      fun k hk => getElem_litsL _ _ _ _
    constructor
    · intro e
      rw [← hrepl, ← g R hRs, ← g 0 (by omega)] at e
      have := (List.Nodup.getElem_inj F.nodup).mp e; omega
    · intro e
      rw [← hrepl, ← g R hRs, ← g 1 (by omega)] at e
      have := (List.Nodup.getElem_inj F.nodup).mp e; omega
  have hReo : repl ≠ other := by
    rcases hw with ⟨_, h1⟩ | ⟨_, h0⟩
    · rw [← h1]; exact hRw.2
    · rw [← h0]; exact hRw.1
  -- old abstract lists
  have hW := h.wsa
  have hcount1 : countRef r (WL s0 (NOT lit) st (.large b r :: rest) (NOT lit)) = 1 := by
    have := (hW.live r F.chain hg)
    rcases hw with ⟨h0, _⟩ | ⟨h1, _⟩
    · have h' := this.2.2.2.2.1; rw [h0] at h'; exact h'
    · have h' := this.2.2.2.2.2.1; rw [h1] at h'; exact h'
  have hWLn : WL s0 (NOT lit) st (.large b r :: rest) (NOT lit) = st.out ++ .large b r :: rest := by
    unfold WL; simp
  have hnotin : ∀ b', WEntry.large b' r ∉ st.out ++ rest := by
    rw [hWLn] at hcount1
    intro b' hb'
    have := countRef_pos r _ b' hb'
    simp [countRef_append, countRef] at hcount1 this
    omega
  -- where the entries of `r` can be in the old lists
  have hwhere : ∀ l b', WEntry.large b' r ∈ WL s0 (NOT lit) st (.large b r :: rest) l →
      l = NOT lit ∨ l = other := by
    intro l b' hm
    have := ((hW.refOK l b' r hm).2 hg).1
    rcases hw with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · rw [h0, h1] at this; exact this
    · rw [h0, h1] at this; exact this.symm
  -- the new lists
  have hWL' : ∀ l, WL s0 (NOT lit) { st with arena := a', delayed := st.delayed ++ [(repl, other, r)] } rest l =
      if l = NOT lit then st.out ++ rest
      else if l = repl then WL s0 (NOT lit) st (.large b r :: rest) l ++ [.large other r]
      else WL s0 (NOT lit) st (.large b r :: rest) l := by
    intro l
    unfold WL
    by_cases e1 : l = NOT lit
    · simp [e1]
    · by_cases e2 : l = repl
      · subst e2; simp [e1, delayedFor_append]
      · simp [e1, e2, delayedFor_append, Ne.symm e2]
  have hchain' : a'.chain 0 a'.sizeWards = st.arena.chain 0 st.arena.sizeWards := W.chain
  have hgar : ∀ x ∈ st.arena.chain 0 st.arena.sizeWards, a'.garbage x = st.arena.garbage x := by
    intro x hx; unfold garbage flag; rw [W.word0 x hx]
  have hbinIff : ∀ x y, WEntry.bin y ∈ WL s0 (NOT lit) { st with arena := a', delayed := st.delayed ++ [(repl, other, r)] } rest x ↔
      WEntry.bin y ∈ WL s0 (NOT lit) st (.large b r :: rest) x := by
    intro x y
    rw [hWL']
    by_cases e1 : x = NOT lit
    · rw [ite_eq_left e1, e1, hWLn]; simp
    · rw [ite_eq_right e1]
      by_cases e2 : x = repl
      · rw [ite_eq_left e2]; simp
      · rw [ite_eq_right e2]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun x y => (hbinIff x y).trans (h.bins x y), ?wf, ?dv⟩
  case dv =>
    intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact h.delayedValid d hd
    · have := F.valid repl (by rw [← hrepl]; exact lit_mem_litsL _ _ _ hRs)
      exact this
  case wf =>
    intro l e he
    rw [hWL'] at he
    have hewf := h.wf (NOT lit) (.large b r) (by rw [hWLn]; simp)
    by_cases e1 : l = NOT lit
    · rw [ite_eq_left e1] at he
      refine h.wf (NOT lit) e ?_
      rw [hWLn]; simp only [List.mem_append, List.mem_cons] at he ⊢
      rcases he with he | he
      · exact Or.inl he
      · exact Or.inr (Or.inr he)
    · rw [ite_eq_right e1] at he
      by_cases e2 : l = repl
      · rw [ite_eq_left e2] at he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h.wf l e he
        · refine ⟨?_, hewf.2⟩
          have hv := F.valid other (by
            rcases hw with ⟨_, h1⟩ | ⟨_, h0⟩
            · rw [← h1]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
            · rw [← h0]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega))
          have hb := H.ctx.ws.varsBound
          unfold ValidLit at hv; rw [IDX_toNat] at hv
          exact (by simp only [V] at hv; omega)
      · rw [ite_eq_right e2] at he; exact h.wf l e he
  · -- refOK
    intro l b'' r'' hm
    rw [hWL'] at hm
    have hold : WEntry.large b'' r'' ∈ WL s0 (NOT lit) st (.large b r :: rest) l ∨
        (l = repl ∧ b'' = other ∧ r'' = r) := by
      by_cases e1 : l = NOT lit
      · rw [ite_eq_left e1] at hm; left; rw [e1, hWLn]
        simp only [List.mem_append, List.mem_cons] at hm ⊢
        rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (Or.inr hm)
      · rw [ite_eq_right e1] at hm
        by_cases e2 : l = repl
        · rw [ite_eq_left e2] at hm
          simp only [List.mem_append, List.mem_singleton, WEntry.large.injEq] at hm
          rcases hm with hm | ⟨hb, hr⟩
          · exact Or.inl hm
          · exact Or.inr ⟨e2, hb, hr⟩
        · rw [ite_eq_right e2] at hm; exact Or.inl hm
    rcases hold with hold | ⟨rfl, rfl, rfl⟩
    · obtain ⟨hc, hlv⟩ := hW.refOK _ _ _ hold
      refine ⟨by rw [hchain']; exact hc, fun hg' => ?_⟩
      rw [hgar r'' hc] at hg'
      obtain ⟨hl, hb⟩ := hlv hg'
      by_cases e : r'' = r
      · subst e
        -- an entry of `r` in an old list other than the head: on `other`'s list
        have hl' : l = other := by
          rcases hwhere l b'' hold with e1 | e1
          · exfalso
            rw [ite_eq_left e1] at hm
            exact hnotin b'' hm
          · exact e1
        exact ⟨Or.inl (by rw [hw0, hl']), hperm.mem_iff.mpr hb⟩
      · obtain ⟨hL, _⟩ := W.others r'' hc e
        have h3 := (hW.live r'' hc hg').1
        have hsz : (a'.size r'').toNat = (st.arena.size r'').toNat := by rw [W.size r'' hc]
        rw [lit_eq_of_litsL_eq hL (by omega), lit_eq_of_litsL_eq hL (by omega), hL]
        exact ⟨hl, hb⟩
    · refine ⟨by rw [hchain']; exact F.chain, fun _ => ⟨Or.inr hw1.symm, ?_⟩⟩
      apply hperm.mem_iff.mpr
      rcases hw with ⟨_, h1⟩ | ⟨_, h0⟩
      · rw [← h1]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
      · rw [← h0]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
  · -- live
    intro r'' hc' hg'
    have hc : r'' ∈ st.arena.chain 0 st.arena.sizeWards := by rw [← hchain']; exact hc'
    rw [hgar r'' hc] at hg'
    obtain ⟨h3, hnd, hs2, hslt, hc0, hc1, hval⟩ := hW.live r'' hc hg'
    have hsz : a'.size r'' = st.arena.size r'' := W.size r'' hc
    by_cases e : r'' = r
    · subst e
      refine ⟨by rw [hsz]; exact h3, hperm.nodup_iff.mpr hnd, ?_, ?_, ?_, ?_,
        fun x hx => hval x (hperm.mem_iff.mp hx)⟩
      · rw [hsearch]; simp; omega
      · rw [hsearch, hsz]; simp; omega
      · rw [hw0, hWL', ite_eq_right hneo, ite_eq_right hReo.symm]
        rcases hw with ⟨_, h1⟩ | ⟨_, h0⟩
        · rw [← h1]; exact hc1
        · rw [← h0]; exact hc0
      · rw [hw1, hWL', ite_eq_right hneR, ite_eq_left rfl]
        have h0 : countRef r'' (WL s0 (NOT lit) st (.large b r'' :: rest) repl) = 0 := by
          apply Classical.byContradiction
          intro hpos
          obtain ⟨b', hb'⟩ := countRef_mem r'' (WL s0 (NOT lit) st (.large b r'' :: rest) repl)
            (by omega)
          rcases hwhere repl b' hb' with e1 | e1
          · exact hneR e1
          · exact hReo e1
        rw [countRef_append]; simp [countRef, h0]
    · obtain ⟨hL, hS⟩ := W.others r'' hc e
      have hsz' : (a'.size r'').toNat = (st.arena.size r'').toNat := by rw [hsz]
      have e0 := lit_eq_of_litsL_eq hL (k := 0) (by omega)
      have e1 := lit_eq_of_litsL_eq hL (k := 1) (by omega)
      have hcnt : ∀ x, countRef r'' (WL s0 (NOT lit) { st with arena := a', delayed := st.delayed ++ [(repl, other, r)] } rest x) =
          countRef r'' (WL s0 (NOT lit) st (.large b r :: rest) x) := by
        intro x
        rw [hWL']
        by_cases f1 : x = NOT lit
        · rw [ite_eq_left f1, f1, hWLn]; exact countRef_drop_ne r'' r _ _ b (Ne.symm e)
        · rw [ite_eq_right f1]
          by_cases f2 : x = repl
          · rw [ite_eq_left f2]; exact countRef_append_large_ne r'' r _ other (Ne.symm e)
          · rw [ite_eq_right f2]
      refine ⟨by rw [hsz]; exact h3, by rw [hL]; exact hnd, by rw [hS]; exact hs2,
        by rw [hS, hsz]; exact hslt, by rw [hcnt, e0]; exact hc0, by rw [hcnt, e1]; exact hc1,
        by rw [hL]; exact hval⟩
  · -- bin
    intro x y hm
    obtain ⟨h1, h2, h3, h4⟩ := hW.bin x y ((hbinIff x y).mp hm)
    exact ⟨(hbinIff y x).mpr h1, h2, h3, h4⟩
  · intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact h.delayedNe d hd
    · exact hneR

end Solver
end LeanKissat

namespace LeanKissat
namespace Solver
open Arena

theorem ws_step {s0 : Solver} {i : Nat} {lit : Lit} {st : PS} {done rest : List WEntry}
    {e : WEntry} (H : StepHyp s0 i lit st done rest e) (h : WSInv s0 (NOT lit) st (e :: rest))
    (probing jump : Bool) (lv : UInt32) :
    WSInv s0 (NOT lit) (PS.step probing jump lv (NOT lit) st e) rest := by
  cases e with
  | bin b =>
    unfold PS.step
    simp only
    split
    · exact h.move _ rfl rfl rfl
    split
    · exact h.move _ rfl rfl rfl
    · exact h.move _ rfl rfl rfl
  | large b r =>
    unfold PS.step
    simp only
    by_cases hbt : vTrue (st.a.values.get! b.toNat) = true
    · rw [ite_eq_left hbt]; exact h.move _ rfl rfl rfl
    rw [ite_eq_right hbt]
    have hr0 := (H.ctx.ws.refOK _ _ _ H.mem).1
    have hgeq : st.arena.garbage r = s0.arena.garbage r := by
      unfold garbage flag; rw [H.run.arena.word0 r hr0]
    by_cases hg : st.arena.garbage r = true
    · rw [ite_eq_left hg]; exact h.dropGarbage hg
    rw [ite_eq_right hg]
    have hg' : st.arena.garbage r = false := by simpa using hg
    have F := H.largeFacts (by rw [← hgeq]; exact hg')
    by_cases hot : vTrue (st.a.values.get! (st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit).toNat) = true
    · rw [ite_eq_left hot]
      have hmem : st.arena.lit r 0 ^^^ st.arena.lit r 1 ^^^ NOT lit ∈ st.arena.litsL r := by
        rcases F.watch with ⟨_, h1⟩ | ⟨_, h0⟩
        · rw [← h1]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
        · rw [← h0]; exact lit_mem_litsL _ _ _ (by have := F.size3; omega)
      refine h.reblock _ _ rfl rfl rfl (fun _ => hmem) ?_
      have hv := F.valid _ hmem
      have hb := H.ctx.ws.varsBound
      unfold ValidLit at hv; rw [IDX_toNat] at hv
      simp only [V] at hv; omega
    rw [ite_eq_right hot]
    have SS := search_spec st.arena st.a.values r _ _ F.searched2 F.searchedLt
    simp only at SS
    generalize (if findReplacement st.arena st.a.values r (st.arena.searched r).toNat
        (st.arena.size r).toNat < (st.arena.size r).toNat then
        findReplacement st.arena st.a.values r (st.arena.searched r).toNat (st.arena.size r).toNat
      else if findReplacement st.arena st.a.values r 2 (st.arena.searched r).toNat <
        (st.arena.searched r).toNat then findReplacement st.arena st.a.values r 2 (st.arena.searched r).toNat
      else (st.arena.size r).toNat) = R at SS ⊢
    by_cases hR : R < (st.arena.size r).toNat
    · rw [ite_eq_left hR]; exact h.replace H F hg' R (SS.1 hR).1 hR (SS.1 hR).2
    rw [ite_eq_right hR]
    split
    · exact h.move _ rfl rfl rfl
    · exact h.move _ rfl rfl rfl

theorem WSInv.flush {s0 : Solver} {notLit : Lit} {st : PS} {es : List WEntry}
    (h : WSInv s0 notLit st es) : WSInv s0 notLit { st with out := st.out ++ es } [] := by
  have hWL : WL s0 notLit { st with out := st.out ++ es } [] = WL s0 notLit st es := by
    funext l; unfold WL; simp
  exact ⟨hWL ▸ h.wsa, h.delayedNe, fun x y => by rw [hWL]; exact h.bins x y, by rw [hWL]; exact h.wf,
    h.delayedValid⟩

theorem run_both {s0 : Solver} {i : Nat} {lit : Lit} (hctx : Ctx s0 i lit) (probing jump : Bool)
    {lv : UInt32} (hlv : lv.toNat ≤ s0.level.toNat) :
    ∀ (es : List WEntry) (st : PS) (done : List WEntry), RunInv s0 i (NOT lit) st done →
    WSInv s0 (NOT lit) st es → s0.entries (NOT lit) = done ++ es →
    RunInv s0 i (NOT lit) (PS.run probing jump lv (NOT lit) st es) (done ++ es) ∧
    WSInv s0 (NOT lit) (PS.run probing jump lv (NOT lit) st es) [] := by
  intro es
  induction es with
  | nil => intro st done h hw _; simpa [PS.run] using ⟨h, hw⟩
  | cons e es ih =>
    intro st done h hw hsplit
    by_cases hres : st.res.isSome
    · rw [PS.run_of_res st hres]
      exact ⟨h.extend_conflict hres _ _ rfl rfl rfl rfl, hw.flush⟩
    · have hres' : st.res = none := by simpa using hres
      rw [PS.run_cons_none st hres']
      have H : StepHyp s0 i lit st done es e := ⟨hctx, h, hres', hsplit⟩
      have hstep : RunInv s0 i (NOT lit) (PS.step probing jump lv (NOT lit) st e)
          (done ++ [e]) := by
        cases e with
        | bin b => exact step_bin H probing jump hlv
        | large b r => exact step_large H probing jump lv
      have := ih _ _ hstep (ws_step H hw probing jump lv) (by rw [hsplit]; simp)
      simpa using this

end Solver
end LeanKissat
