import LeanKissat.Proofs.ImportAdd

/-!
# Main theorems

For the options of the `--plain` configuration, `solveCNF` is sound:
* result 20 (UNSAT) implies that `F` is unsatisfiable;
* result 10 (SAT) implies that the reported model satisfies `F`.
-/

namespace LeanKissat
open Std.Sat
open Solver

/-- The options the proofs rely on (all set by `--plain`). -/
structure PlainConfig (o : Options) : Prop where
  plain : PlainOpts o
  jump : o.jumpreasons = 0
  tumble : o.tumble = 0

theorem foldl_max_ge (L : List (Literal Nat)) : ∀ m, m ≤ L.foldl (fun m l => max m (l.1 + 1)) m := by
  induction L with
  | nil => intro m; exact Nat.le_refl _
  | cons x xs ih => intro m; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_mem (L : List (Literal Nat)) : ∀ m, ∀ l ∈ L, l.1 + 1 ≤ L.foldl (fun m l => max m (l.1 + 1)) m := by
  induction L with
  | nil => intro m l hl; simp at hl
  | cons x xs ih =>
    intro m l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge _ _)
    · exact ih _ l hl

theorem foldl_max_le (L : List (Literal Nat)) (B : Nat) : ∀ m, m ≤ B → (∀ l ∈ L, l.1 + 1 ≤ B) →
    L.foldl (fun m l => max m (l.1 + 1)) m ≤ B := by
  induction L with
  | nil => intro m hm _; exact hm
  | cons x xs ih =>
    intro m hm hl
    exact ih _ (Nat.max_le.mpr ⟨hm, hl x (List.mem_cons_self ..)⟩) (fun l h => hl l (List.mem_cons_of_mem _ h))

theorem maxVar_spec (F : CNF Nat) :
    (∀ c ∈ F.clauses.toList, ∀ l ∈ c.literals, l.1 < F.maxVar) ∧
    (CNF.ValidVars F → F.maxVar < 2 ^ 30) := by
  unfold Std.Sat.CNF.maxVar
  simp only [← Array.foldl_toList]
  have hge : ∀ (C : List (CNF.Clause Nat)) m, m ≤ C.foldl (fun m c => c.literals.foldl (fun m l => max m (l.1 + 1)) m) m := by
    intro C; induction C with
    | nil => intro m; exact Nat.le_refl _
    | cons c cs ih => intro m; exact Nat.le_trans (foldl_max_ge _ _) (ih _)
  have hmem : ∀ (C : List (CNF.Clause Nat)) m, ∀ c ∈ C, ∀ l ∈ c.literals,
      l.1 < C.foldl (fun m c => c.literals.foldl (fun m l => max m (l.1 + 1)) m) m := by
    intro C; induction C with
    | nil => intro m c hc; simp at hc
    | cons c cs ih =>
      intro m c' hc' l hl
      rcases List.mem_cons.mp hc' with rfl | hc'
      · have := foldl_max_mem c'.literals m l hl; have := hge cs (c'.literals.foldl (fun m l => max m (l.1 + 1)) m)
        simp only [List.foldl_cons]; omega
      · exact ih _ c' hc' l hl
  have hle : ∀ (C : List (CNF.Clause Nat)) m B, m ≤ B → (∀ c ∈ C, ∀ l ∈ c.literals, l.1 + 1 ≤ B) →
      C.foldl (fun m c => c.literals.foldl (fun m l => max m (l.1 + 1)) m) m ≤ B := by
    intro C; induction C with
    | nil => intro m B hm _; exact hm
    | cons c cs ih =>
      intro m B hm hc
      exact ih _ B (foldl_max_le _ B m hm (hc c (List.mem_cons_self ..))) (fun c' h => hc c' (List.mem_cons_of_mem _ h))
  refine ⟨fun c hc l hl => hmem _ 0 c hc l hl, fun hv => ?_⟩
  have := hle F.clauses.toList 0 EXTERNAL_MAX_VAR (Nat.zero_le _)
    (fun c hc l hl => hv c (by simpa [CNF.Internal.mem_iff] using hc) l hl)
  unfold EXTERNAL_MAX_VAR LD_MAX_VAR at this; simp at this
  have e : F.clauses.foldl (fun m c => c.literals.foldl (fun m l => max m (l.1 + 1)) m) 0 =
      F.clauses.toList.foldl (fun m c => c.literals.foldl (fun m l => max m (l.1 + 1)) m) 0 := by
    rw [Array.foldl_toList]
  omega

/-- The state after adding the clauses `L` (a prefix of the input). -/
def ImpAll (F : CNF Nat) (L : List (CNF.Clause Nat)) (s : Solver) : Prop :=
  (s.inconsistent = true ∧ ¬ ∃ β, PhiF F β) ∨ (Flagged s ∧ s.inconsistent = false) ∨
  (ImpBase F s ∧ ∀ c ∈ L, CovC s c)

theorem importAll (F : CNF Nat) : ∀ (M : List (CNF.Clause Nat)), (∀ c ∈ M, c ∈ F.clauses.toList) →
    ∀ (L : List (CNF.Clause Nat)) (s : Solver), ImpAll F L s → ImpAll F (L ++ M) (M.foldl addClause s) := by
  intro M
  induction M with
  | nil => intro _ L s h; simpa using h
  | cons c cs ih =>
    intro hM L s h
    have hc := hM c (List.mem_cons_self ..)
    have hcs : ∀ c' ∈ cs, c' ∈ F.clauses.toList := fun c' h' => hM c' (List.mem_cons_of_mem _ h')
    have := ih hcs (L ++ [c]) (addClause s c) ?_
    · simpa using this
    rcases h with ⟨hi, hu⟩ | ⟨hf, hi⟩ | ⟨hb, hcov⟩
    · have k := addClause_bad s c (Or.inl hi)
      exact Or.inl ⟨by rw [k.1]; exact hi, hu⟩
    · have k := addClause_bad s c (Or.inr hf)
      refine Or.inr (Or.inl ⟨?_, by rw [k.1]; exact hi⟩)
      obtain ⟨e1, e2, e3, e4⟩ := k
      unfold Flagged at *; rw [e2, e3, e4]; exact hf
    · rcases addClause_spec hb hc with h' | h' | ⟨hb', hm, hcv⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · refine Or.inr (Or.inr ⟨hb', fun c' hc' => ?_⟩)
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact (hcov c' hc').mono hm hb.search.inv.core hb'.search.inv.core
        · simp at hc'; subst hc'; exact hcv

theorem reserved_impBase {F : CNF Nat} {opts : Options} {s : Solver} (hr : Reserved s opts F.maxVar)
    (hc : PlainConfig opts) : ImpBase F s := by
  have hf := hr.fresh
  have hsinv : SInv (PhiF F) s := hf.sinv (by rw [hr.options]; exact hc.jump)
  refine ⟨⟨hsinv, fun d hd => absurd hd (hf.not_inDB d), fun i b _ => by unfold abit abits; simp [hf.aBits],
      hr.clause, fun e => by rw [hr.inconsistent] at e; simp at e, hr.watching, by rw [hr.options]; exact hc.plain,
      hr.imp⟩, hf.level, by rw [hf.propagate, hf.trailL]; rfl, hr.marks, by rw [hr.vars]; exact hr.marksSize,
    hr.cs, hr.ct, hr.csh, ?_, by rw [hr.options]; exact hc.tumble, ?_, hr.inconsistent, ?_⟩
  · intro v hv
    left; have := hr.active v (by rw [← hr.vars]; exact hv)
    unfold isActive varFlags at this
    have e : (UInt32.ofNat v).toNat = v := by have := hf.small; simp; omega
    rw [e] at this; exact this
  · intro c hcF l hl; rw [hr.vars]; exact (maxVar_spec F).1 c hcF l hl
  · obtain ⟨n1, n2, n3⟩ := hr.notFlagged
    intro h; unfold Flagged at h; rw [n1, n2, n3] at h; simp at h

theorem search_flagged {P : Procedures} (hpre : ∀ s, (P.preprocess s).1 = 0 ∧ Flagged (P.preprocess s).2)
    {s : Solver} (hf : Flagged s) (hi : s.inconsistent = false) : (search P s).1 = 0 := by
  unfold search
  rw [if_neg (by simp [hi])]
  have h1 : (if s.options.luckyearly != 0 then s.lucky else (0, s)) = (0, s) := by
    split
    · exact lucky_flagged s hf
    · rfl
  rw [h1]
  dsimp only
  rw [if_neg (by simp)]
  have h2 : (if s.options.preprocess != 0 && s.options.probe != 0 && s.options.preprocessprobe != 0 then
      P.preprocess s else (0, s)).1 = 0 ∧ Flagged (if s.options.preprocess != 0 && s.options.probe != 0 &&
      s.options.preprocessprobe != 0 then P.preprocess s else (0, s)).2 := by
    split
    · exact hpre s
    · exact ⟨rfl, hf⟩
  generalize (if s.options.preprocess != 0 && s.options.probe != 0 && s.options.preprocessprobe != 0 then
      P.preprocess s else (0, s)) = R at h2
  obtain ⟨r, u⟩ := R
  obtain ⟨hr, hu⟩ := h2
  dsimp only at hr hu ⊢
  subst hr
  rw [if_neg (by simp)]
  have h3 : (if u.options.luckylate != 0 then u.lucky else (0, u)) = (0, u) := by
    split
    · exact lucky_flagged u hu
    · rfl
  rw [h3]
  dsimp only
  rw [if_neg (by simp)]
  split
  · rw [searchLoop_flagged P (((startSearch_fm _).trans (classify_fm _)).flagged hu)]
  · rfl

theorem procedures_hyps :
    (∀ s, (procedures.probe s).1 = 0 ∧ Flagged (procedures.probe s).2) ∧
    (∀ s, (procedures.eliminate s).1 = 0 ∧ Flagged (procedures.eliminate s).2) ∧
    (∀ s, (procedures.preprocess s).1 = 0 ∧ Flagged (procedures.preprocess s).2) :=
  ⟨fun s => ⟨rfl, Or.inr (Or.inr rfl)⟩, fun s => ⟨rfl, Or.inr (Or.inr rfl)⟩, fun s => ⟨rfl, Or.inr (Or.inr rfl)⟩⟩

/-- The state handed to `kissat_search` after importing `F`. -/
theorem import_spec {opts : Options} {F : CNF Nat} (hc : PlainConfig opts) (hv : CNF.ValidVars F) :
    ImpAll F F.clauses.toList (F.clauses.foldl addClause ((Solver.init opts).reserve F.maxVar)) := by
  have hn := (maxVar_spec F).2 hv
  have hr := init_reserve_spec opts F.maxVar hn hc.tumble
  have hb := reserved_impBase hr hc
  have := importAll F F.clauses.toList (fun c h => h) [] _ (Or.inr (Or.inr ⟨hb, fun c hc => by simp at hc⟩))
  rw [← Array.foldl_toList]; simpa using this

/-- Soundness of UNSAT answers (`--plain`; assuming the reduce procedure keeps the invariants). -/
theorem solveCNF_unsat {opts : Options} {F : CNF Nat} (hc : PlainConfig opts) (hv : CNF.ValidVars F)
    (hred : ReduceOK (PhiF F) Solver.reduce) : (solveCNF opts F).1 = 20 → F.Unsat := by
  intro h20
  have hF : ∀ c ∈ F.clauses.toList, ∀ l ∈ c.literals, l.1 < 2 ^ 31 := by
    have := (maxVar_spec F).2 hv; intro c hc l hl; have := (maxVar_spec F).1 c hc l hl; omega
  obtain ⟨hp1, hp2, hp3⟩ := procedures_hyps
  unfold solveCNF at h20
  dsimp only at h20
  rcases import_spec hc hv with ⟨_, hu⟩ | ⟨hf, hi⟩ | ⟨hb, _⟩
  · exact unsat_of_phiF hF hu
  · rw [search_flagged hp3 hf hi] at h20; simp at h20
  · exact unsat_of_phiF hF ((kissatSearch_spec (P := procedures) hred hp1 hp2 hp3 hb.search).1 h20)

/-- Soundness of SAT answers (`--plain`; assuming the reduce procedure keeps the invariants). -/
theorem solveCNF_sat {opts : Options} {F : CNF Nat} (hc : PlainConfig opts) (hv : CNF.ValidVars F)
    (hred : ReduceOK (PhiF F) Solver.reduce) : (solveCNF opts F).1 = 10 → F.Sat (modelOf (solveCNF opts F).2) := by
  intro h10
  have hF : ∀ c ∈ F.clauses.toList, ∀ l ∈ c.literals, l.1 < 2 ^ 31 := by
    have := (maxVar_spec F).2 hv; intro c hc l hl; have := (maxVar_spec F).1 c hc l hl; omega
  obtain ⟨hp1, hp2, hp3⟩ := procedures_hyps
  unfold solveCNF at h10 ⊢
  dsimp only at h10 ⊢
  rcases import_spec hc hv with ⟨hi, _⟩ | ⟨hf, hi⟩ | ⟨hb, hcov⟩
  · unfold search at h10; rw [if_pos hi] at h10; simp at h10
  · rw [search_flagged hp3 hf hi] at h10; simp at h10
  · exact sat_final ((kissatSearch_spec (P := procedures) hred hp1 hp2 hp3 hb.search).2 h10) hb.search.inv hcov hF

end LeanKissat
