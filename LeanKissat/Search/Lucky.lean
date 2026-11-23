import LeanKissat.Search.Analyze

/-
Lucky phases (`lucky.c`).
-/
namespace LeanKissat
namespace Solver

/-- Shared large-clause check of `no_all_negative_clauses` / `no_all_positive_clauses`:
  some irredundant large clause has all literals of polarity `neg` (or false). -/
def existsLargeAllPolarity (s : Solver) (negative : Bool) : Bool := Id.run do
  let last := s.lastIrredundant
  for ref in s.arena.clauseRefsFrom 0 do
    if last != INVALID_REF && last < ref then break
    if s.arena.redundant ref then continue
    if s.arena.garbage ref then continue
    let mut ok := false   -- found a literal of the other polarity that is not false
    for i in [0:(s.arena.size ref).toNat] do
      let lit := s.arena.lit ref i
      let wrongSign := if negative then !NEGATED lit else NEGATED lit
      if wrongSign && !vFalse (s.value lit) then
        ok := true
        break
    if !ok then return true
  return false

/-- Port of `no_all_negative_clauses` (lucky.c). -/
def noAllNegativeClauses (s : Solver) : Bool := Id.run do
  if s.existsLargeAllPolarity true then return false
  for i in [0:s.vars.toNat] do
    let idx := UInt32.ofNat i
    if !s.isActive idx then continue
    let notLit := NOT (LIT idx)
    let ws := s.watchesOf notLit
    let mut p := 0
    for _ in [0:ws.size] do
      if p ≥ ws.size then break
      let w := ws.get! p
      if watchIsBinary w then
        let other := watchLit w
        if NEGATED other && s.isActive (IDX other) then return false
        p := p + 1
      else p := p + 2
  return true

/-- Port of `no_all_positive_clauses` (lucky.c). -/
def noAllPositiveClauses (s : Solver) : Bool := Id.run do
  if s.existsLargeAllPolarity false then return false
  for i in [0:s.vars.toNat] do
    let idx := UInt32.ofNat i
    if !s.isActive idx then continue
    let lit := LIT idx
    let ws := s.watchesOf lit
    let mut p := 0
    for _ in [0:ws.size] do
      if p ≥ ws.size then break
      let w := ws.get! p
      if watchIsBinary w then
        let other := watchLit w
        if !NEGATED other && s.isActive (IDX other) then return false
        p := p + 1
      else p := p + 2
  return true

/-- `kissat_internal_assume` with its preconditions checked: the literal is valid and
  unassigned and the trail is fully propagated (C asserts these; the port stops with
  `unknown` if they fail). -/
def luckyAssume (s : Solver) (lit : Lit) : Option Solver :=
  if IDX lit < s.vars && s.value lit == 0 && s.propagate == s.asg.trail.size then
    some (s.internalAssume lit)
  else none

/-- The second polarity after a conflict on a decision level above one. -/
def luckyFlip (s : Solver) (first : Lit) : Option UInt32 × Solver :=
  let s := s.backtrackWithoutUpdatingPhases (s.level - 1)
  match s.luckyAssume (NOT first) with
  | none => (some 0, { s with notPorted := true })
  | some s =>
    match s.probingPropagate none true with
    | (s, none) => (none, s)
    | (s, some _) => (some 0, s.backtrackWithoutUpdatingPhases 0)

/-- Propagating the units learned from a failed literal. -/
def luckyFailedRoot (s : Solver) : Option UInt32 × Solver :=
  match s.probingPropagate none true with
  | (s, some d) =>
    match s.analyze d with
    -- ASSERT (checked): C asserts `inconsistent` after analyzing the root conflict.
    | (r, s) => if r == 20 then (some 20, s) else (some 0, { s with notPorted := true })
  | (s, none) => (none, s)

/-- A failed literal on decision level one. -/
def luckyFailed (s : Solver) (c : CRef) : Option UInt32 × Solver :=
  match s.analyze c with
  | (r, s) =>
    -- `r = 20` means `inconsistent` (C continues and finds the conflict again); a flagged
    -- analysis stops with `unknown`.
    if r == 20 then (some 20, s)
    else if s.overflowed || s.outOfResources || s.notPorted then (some 0, s)
    else s.luckyFailedRoot

/-- The conflict branch of a lucky step. -/
def luckyConflict (s : Solver) (first : Lit) (c : CRef) : Option UInt32 × Solver :=
  if s.level > 1 then s.luckyFlip first else s.luckyFailed c

/-- One step of the four `*_satisfiable` functions for import `eidx`.
  `firstPositive` selects whether `lit` or `NOT lit` is assumed first.
  Returns `some res` to stop with result `res`. -/
def luckyStep (s : Solver) (eidx : Nat) (firstPositive : Bool) : Option UInt32 × Solver :=
  let bits := s.importBits.get! eidx
  if bits &&& ImportBits.imported == 0 then (none, s)
  else if bits &&& ImportBits.eliminated != 0 then (none, s)
  else
  let lit := s.importLit.get! eidx
  let idx := IDX lit
  if !s.isActive idx then (none, s)
  else if s.value lit != 0 then (none, s)
  else
  let first := if firstPositive then lit else NOT lit
  match s.luckyAssume first with
  | none => (some 0, { s with notPorted := true })
  | some s =>
    match s.probingPropagate none true with
    | (s, none) => (none, s)
    | (s, some c) => s.luckyConflict first c

/-- The loop of `forward_*_satisfiable` / `backward_*_satisfiable` (lucky.c) from position `k`. -/
def luckySatLoop (forward firstPositive : Bool) (n : Nat) (s : Solver) (k : Nat) : UInt32 × Solver :=
  -- a flagged state (`unknown`, only after a failed checked assertion) ends the lucky phases
  if s.overflowed || s.outOfResources || s.notPorted then (0, s)
  else if k < n then
    let eidx := if forward then k else n - 1 - k
    match s.luckyStep eidx firstPositive with
    | (some r, s) => (r, s)
    | (none, s) => luckySatLoop forward firstPositive n s (k + 1)
  else (10, s)
termination_by n - k

/-- `forward_*_satisfiable` / `backward_*_satisfiable` (lucky.c). -/
def luckySatisfiable (s : Solver) (forward firstPositive : Bool) : UInt32 × Solver :=
  luckySatLoop forward firstPositive s.importLit.size s 0

/-- Assign the active unassigned variables `i, i+1, ..., n-1` to `positive` and propagate. -/
def luckyAssignLoop (positive : Bool) (n : Nat) (s : Solver) (i : Nat) : Solver :=
  if i < n then
    let idx := UInt32.ofNat i
    if !s.isActive idx then luckyAssignLoop positive n s (i + 1)
    else if s.value (LIT idx) != 0 then luckyAssignLoop positive n s (i + 1)
    else
      match s.luckyAssume (if positive then LIT idx else NOT (LIT idx)) with
      | none => { s with notPorted := true }
      | some s =>
        match s.probingPropagate none true with
        -- DEVIATION: C asserts that no conflict occurs here (the polarity check above
        -- guarantees it). If it ever did, we stop with `unknown` instead of claiming SAT.
        | (s, some _) => { s with notPorted := true }
        | (s, none) => luckyAssignLoop positive n s (i + 1)
  else s
termination_by n - i

/-- Assign all active unassigned variables to `positive` and propagate. -/
def luckyAssignAll (s : Solver) (positive : Bool) : Solver :=
  luckyAssignLoop positive s.vars.toNat s 0

/-- A lucky `SAT` answer: every variable assigned and propagated. -/
@[inline] def luckyComplete (s : Solver) : Bool :=
  s.asg.unassigned == 0 && s.propagate == s.asg.trail.size

/-- The two `*_satisfiable` phases assigning all variables to the same polarity. -/
def luckyAssignPhase (s : Solver) : UInt32 × Solver :=
  let (res, s) :=
    if s.noAllNegativeClauses then
      let s := s.luckyAssignAll true
      ((if s.notPorted then 0 else 10 : UInt32), s)
    else (0, s)
  if res == 0 && !s.notPorted && s.noAllPositiveClauses then
    let s := s.luckyAssignAll false
    ((if s.notPorted then 0 else 10 : UInt32), s)
  else (res, s)

/-- The four `forward/backward_false/true_satisfiable` phases. -/
def luckySatPhases (s : Solver) : UInt32 × Solver :=
  match s.luckySatisfiable true false with
  | (0, s) =>
    match s.luckySatisfiable true true with
    | (0, s) =>
      match s.luckySatisfiable false false with
      | (0, s) => s.luckySatisfiable false true
      | r => r
    | r => r
  | r => r

/-- Port of `kissat_lucky` (lucky.c). -/
def lucky (s : Solver) : UInt32 × Solver :=
  if s.inconsistent then (0, s)
  -- a flagged state (`unknown`) is left alone
  else if s.overflowed || s.outOfResources || s.notPorted then (0, s)
  else if s.options.lucky == 0 then (0, s)
  else
  let s := { s with probing := true }
  match s.luckyAssignPhase with
  | (res, s) =>
    if s.notPorted then (0, { s with probing := false })
    else
    match (if res == 0 then s.luckySatPhases else (res, s)) with
    | (res, s) =>
      -- ASSERT (checked): a lucky assignment is complete and propagated (C claims `SAT`
      -- without checking); otherwise stop with `unknown`.
      if res == 10 && !s.luckyComplete then (0, { s with probing := false, notPorted := true })
      else (res, { s with probing := false })

end Solver
end LeanKissat
