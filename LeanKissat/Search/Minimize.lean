import LeanKissat.Search.Learn

/-
Learned clause minimization (`minimize.c`) and shrinking (`shrink.c`).
-/
namespace LeanKissat
namespace Solver

@[inline] def pushRemovable (s : Solver) (idx : UInt32) : Solver :=
  { (s.setABit idx ABits.removable true) with removable := s.removable.push idx }
@[inline] def pushPoisoned (s : Solver) (idx : UInt32) : Solver :=
  { (s.setABit idx ABits.poisoned true) with poisoned := s.poisoned.push idx }
@[inline] def pushShrinkable (s : Solver) (idx : UInt32) : Solver :=
  { (s.setABit idx ABits.shrinkable true) with shrinkable := s.shrinkable.push idx }
@[inline] def pushAnalyzed (s : Solver) (idx : UInt32) : Solver :=
  { (s.setABit idx ABits.analyzed true) with analyzed := s.analyzed.push idx }

/-- Port of `minimized_index` (minimize.c): `1` removable, `-1` not, `0` unknown. -/
def minimizedIndex (s : Solver) (minimizing : Bool) (idx : UInt32) (depth : Nat) : Int :=
  let level := s.levelIdx idx
  if level == 0 then 1
  else if s.abit idx ABits.removable && depth != 0 then 1
  else if s.reasonIdx idx == DECISION_REASON then -1
  else if s.abit idx ABits.poisoned then -1
  else if (minimizing || depth == 0) && s.frameUsedAt level ≤ 1 then -1
  else 0

/-- Mark `minimize[i..n)` as removable / poisoned. -/
def markMinimizeStack (s : Solver) (res : Bool) (i n : Nat) : Solver :=
  if _h : i < n then
    let idx := s.minimize.get! i
    let s := if res then s.pushRemovable idx else s.pushPoisoned idx
    s.markMinimizeStack res (i + 1) n
  else s
termination_by n - i

/-- Push the variables in `minimize[saved..]` as removable / poisoned and pop them. -/
def finishMinimizeStack (s : Solver) (saved : Nat) (res : Bool) : Solver :=
  let s := s.markMinimizeStack res saved s.minimize.size
  { s with minimize := s.minimize.shrink saved }

mutual

/-- Port of `minimize_literal` (minimize.c). `maxDepth = minimizedepth`. -/
def minimizeLiteral (s : Solver) (minimizing : Bool) (maxDepth : Nat) (lit : Lit)
    (depth : Nat) : Bool × Solver :=
  if h : depth ≥ maxDepth then (false, s) else
  let idx := IDX lit
  let tmp := s.minimizedIndex minimizing idx depth
  if tmp > 0 then (true, s)
  else if tmp < 0 then (false, s)
  else
    let (res, s) :=
      if s.isBinaryReason idx then
        minimizeBinary s minimizing maxDepth (s.reasonIdx idx) depth (by omega)
          (s.vars.toNat + 1)
      else minimizeReference s minimizing maxDepth (s.reasonIdx idx) lit depth (by omega)
    if depth == 0 then (res, s)
    else if !res then (res, s.pushPoisoned idx)
    else if !s.abit idx ABits.removable then (res, s.pushRemovable idx)
    else (res, s)
termination_by (maxDepth + 2 - depth, 2, 0)

/-- Port of `minimize_reference` (minimize.c). -/
def minimizeReference (s : Solver) (minimizing : Bool) (maxDepth : Nat) (ref : Ref)
    (lit : Lit) (depth : Nat) (hd : depth ≤ maxDepth) : Bool × Solver :=
  let notLit := NOT lit
  let s := if s.options.minimizeticks != 0 then INC! s search_ticks else s
  minimizeRefLoop s minimizing maxDepth ref notLit depth hd (s.arena.size ref).toNat 0
termination_by (maxDepth + 2 - depth, 1, 0)

/-- The literal loop of `minimize_reference`. -/
def minimizeRefLoop (s : Solver) (minimizing : Bool) (maxDepth : Nat) (ref : Ref)
    (notLit : Lit) (depth : Nat) (hd : depth ≤ maxDepth) (n i : Nat) : Bool × Solver :=
  if hi : i < n then
    let other := s.arena.lit ref i
    if other == notLit then minimizeRefLoop s minimizing maxDepth ref notLit depth hd n (i + 1)
    else
      let (ok, s) := minimizeLiteral s minimizing maxDepth other (depth + 1)
      if !ok then (false, s)
      else minimizeRefLoop s minimizing maxDepth ref notLit depth hd n (i + 1)
  else (true, s)
termination_by (maxDepth + 2 - depth, 0, n - i)

/-- Port of `minimize_binary` (minimize.c): follow the binary reason chain.
  -- FUEL: bounded by `vars`; reasons are assigned strictly earlier, so the chain
  has at most `vars` elements. Out of fuel counts as not removable (sound). -/
def minimizeBinary (s : Solver) (minimizing : Bool) (maxDepth : Nat) (lit : Lit)
    (depth : Nat) (hd : depth < maxDepth) (fuel : Nat) : Bool × Solver :=
  let saved := s.minimize.size
  let (res, s) := minimizeBinaryChain s minimizing maxDepth lit depth hd fuel
  (res, s.finishMinimizeStack saved res)
termination_by (maxDepth + 2 - depth, 1, fuel + 1)

def minimizeBinaryChain (s : Solver) (minimizing : Bool) (maxDepth : Nat) (next : Lit)
    (depth : Nat) (hd : depth < maxDepth) (fuel : Nat) : Bool × Solver :=
  match fuel with
  | 0 => (false, s)
  | fuel + 1 =>
    let idx := IDX next
    let tmp := s.minimizedIndex minimizing idx 1
    if tmp != 0 then (tmp > 0, s)
    else
      let s := { s with minimize := s.minimize.push idx }
      if !s.isBinaryReason idx then
        minimizeReference s minimizing maxDepth (s.reasonIdx idx) next (depth + 1) (by omega)
      else minimizeBinaryChain s minimizing maxDepth (s.reasonIdx idx) depth hd fuel
termination_by (maxDepth + 2 - depth, 1, fuel)

end

/-- Port of `kissat_minimize_literal` (minimize.c). -/
@[inline] def minimizeLiteralTop (s : Solver) (lit : Lit) (litInClause : Bool) : Bool × Solver :=
  s.minimizeLiteral false s.options.minimizedepth lit (if litInClause then 0 else 1)

/-- Clear bit `b` of the variables `v[i..n)`. -/
def clearBitsUp (s : Solver) (v : U32Vec) (b : UInt8) (i n : Nat) : Solver :=
  if _h : i < n then (s.setABit (v.get! i) b false).clearBitsUp v b (i + 1) n
  else s
termination_by n - i

/-- Clear bit `b` of the variables `v[n-1-i], …, v[0]` for `i` from `k` (in this order). -/
def clearBitsDown (s : Solver) (v : U32Vec) (b : UInt8) (n k : Nat) : Solver :=
  if _h : k < n then (s.setABit (v.get! (n - 1 - k)) b false).clearBitsDown v b n (k + 1)
  else s
termination_by n - k

/-- Port of `kissat_reset_poisoned` (minimize.c). -/
def resetPoisoned (s : Solver) : Solver :=
  let s := s.clearBitsUp s.poisoned ABits.poisoned 0 s.poisoned.size
  { s with poisoned := s.poisoned.clear }

/-- The compaction loop of `compactClause`. -/
def compactLoop (c : U32Vec) (p q : Nat) : U32Vec × Nat :=
  if _h : p < c.size then
    let lit := c.get! p
    if lit != INVALID_LIT then compactLoop (c.set! q lit) (p + 1) (q + 1)
    else compactLoop c (p + 1) q
  else (c, q)
termination_by c.size - p
decreasing_by all_goals simp_all [U32Vec.size_set!]; omega

/-- Remove `INVALID_LIT` entries from `s.clause`. -/
def compactClause (s : Solver) : Solver :=
  let c := s.clause
  let s := { s with clause := .empty }
  let (c, q) := compactLoop c 0 0
  { s with clause := c.shrink q }

/-- Mark the variables of `clause[i..n)` as removable. -/
def markClauseRemovable (s : Solver) (i n : Nat) : Solver :=
  if _h : i < n then (s.pushRemovable (IDX (s.clause.get! i))).markClauseRemovable (i + 1) n
  else s
termination_by n - i

/-- The minimization loop of `kissat_minimize_clause`: `for (p = end; --p > lits;)`, i.e.
  positions `i - 1, …, 1`. -/
def minimizeDown (s : Solver) : Nat → Solver
  | 0 => s
  | 1 => s
  | i + 2 =>
    let lit := s.clause.get! (i + 1)
    let (ok, s') := s.minimizeLiteral true s.options.minimizedepth lit 0
    let s' := if ok then { s' with clause := s'.clause.set! (i + 1) INVALID_LIT } else s'
    minimizeDown s' (i + 1)

/-- Port of `kissat_minimize_clause` (minimize.c). -/
def minimizeClause (s : Solver) : Solver :=
  let n := s.clause.size
  let s := s.markClauseRemovable 0 n
  if s.options.shrink > 2 then s
  else
    let s := (s.minimizeDown n).compactClause
    -- ADD (literals_minimized, ...): METRIC
    s.resetPoisoned

/-! ### `shrink.c` -/

def resetShrinkable (s : Solver) : Solver :=
  let s := s.clearBitsDown s.shrinkable ABits.shrinkable s.shrinkable.size 0
  { s with shrinkable := s.shrinkable.clear }

/-- The loop of `markShrinkableAsRemovable` over `shrinkable[n-1-k], …, shrinkable[0]`. -/
def markShrinkableLoop (s : Solver) (n k : Nat) : Solver :=
  if _h : k < n then
    let idx := s.shrinkable.get! (n - 1 - k)
    let s := s.setABit idx ABits.shrinkable false
    let s := if !s.abit idx ABits.removable then s.pushRemovable idx else s
    s.markShrinkableLoop n (k + 1)
  else s
termination_by n - k

def markShrinkableAsRemovable (s : Solver) : Solver :=
  let s := s.markShrinkableLoop s.shrinkable.size 0
  { s with shrinkable := s.shrinkable.clear }

/-- Port of `shrink_literal` (shrink.c): `0`, `1` or `-1`. -/
def shrinkLiteral (s : Solver) (level : UInt32) (lit : Lit) : Int × Solver :=
  let idx := IDX lit
  let alevel := s.levelIdx idx
  if alevel == 0 then (0, s)
  else if s.abit idx ABits.shrinkable then (0, s)
  else if alevel < level then
    if s.abit idx ABits.removable then (0, s)
    else if s.options.shrink > 2 then
      let (ok, s) := s.minimizeLiteralTop lit false
      if ok then (0, s) else (-1, s)
    else (-1, s)
  else (1, s.pushShrinkable idx)

/-- Replace the literals of `clause[p..e)` by `INVALID_LIT`, counting them. -/
def invalidateBlock (s : Solver) (p e cnt : Nat) : Nat × Solver :=
  if _h : p < e then
    if s.clause.get! p == INVALID_LIT then s.invalidateBlock (p + 1) e cnt
    else ({ s with clause := s.clause.set! p INVALID_LIT } : Solver).invalidateBlock (p + 1) e (cnt + 1)
  else (cnt, s)
termination_by e - p

/-- Port of `shrunken_block` (shrink.c), non-LOGGING build. -/
def shrunkenBlock (s : Solver) (beginBlock endBlock : Nat) (uip : Lit) : Nat × Solver :=
  let notUip := NOT uip
  let (blockShrunken, s) := s.invalidateBlock beginBlock endBlock 0
  let s := { s with clause := s.clause.set! beginBlock notUip }
  let blockShrunken := blockShrunken - 1
  let uidx := IDX uip
  let s := if !s.isAnalyzed uidx then s.pushAnalyzed uidx else s
  (blockShrunken, s.markShrinkableAsRemovable)

/-- The literal loop of `shrink_along_large`. -/
def shrinkLargeLoop (s : Solver) (level : UInt32) (uip : Lit) (ref : Ref) (i n opened : Nat) :
    Nat × Bool × Solver :=
  if _h : i < n then
    let other := s.arena.lit ref i
    if other == uip then s.shrinkLargeLoop level uip ref (i + 1) n opened
    else
      let (tmp, s) := s.shrinkLiteral level other
      if tmp < 0 then (opened, true, s)
      else s.shrinkLargeLoop level uip ref (i + 1) n (if tmp > 0 then opened + 1 else opened)
  else (opened, false, s)
termination_by n - i

/-- Port of `shrink_along_large` (shrink.c). Returns `(open, failed)`. -/
def shrinkAlongLarge (s : Solver) (level : UInt32) (uip : Lit) (ref : Ref) : Nat × Bool × Solver :=
  let s := if s.options.minimizeticks != 0 then INC! s search_ticks else s
  s.shrinkLargeLoop level uip ref 0 (s.arena.size ref).toNat 0

/-- Port of `shrink_along_reason` (shrink.c). -/
def shrinkAlongReason (s : Solver) (level : UInt32) (uip : Lit) (resolveLarge : Bool) :
    Nat × Bool × Solver :=
  let idx := IDX uip
  if s.reasonIdx idx == DECISION_REASON then (0, true, s)  -- checked assertion: never a decision
  else if s.isBinaryReason idx then
    let (tmp, s) := s.shrinkLiteral level (s.reasonIdx idx)
    -- C ignores `tmp < 0` here: a binary reason literal is always on the same level, so
    -- `shrink_literal` cannot fail; failing explicitly keeps the result sound regardless.
    ((if tmp > 0 then 1 else 0), Decidable.decide (tmp < 0), s)
  else if resolveLarge then s.shrinkAlongLarge level uip (s.reasonIdx idx)
  else (0, true, s)

/-- Trail walk of `shrink_block`: find the previous shrinkable trail literal at or
  before position `t`. Returns the literal and the position before it. -/
def findShrinkable (s : Solver) (t : Nat) : Lit × Nat :=
  let lit := s.asg.trail.get! t
  if s.abit (IDX lit) ABits.shrinkable then (lit, t - 1)
  else if h : t = 0 then (lit, 0)
  else findShrinkable s (t - 1)
termination_by t

/-- Main loop of `shrink_block`.
  -- FUEL: bounded by the trail size (each round consumes one trail position). -/
def shrinkBlockLoop (s : Solver) (level : UInt32) (resolveLarge : Bool) (opened t : Nat)
    (fuel : Nat) : Lit × Bool × Solver :=
  match fuel with
  | 0 => (INVALID_LIT, true, s)
  | fuel + 1 =>
    let (uip, t) := s.findShrinkable t
    if opened == 1 then (uip, false, s)
    else
      let (o, failed, s) := s.shrinkAlongReason level uip resolveLarge
      if failed then (uip, true, s)
      else shrinkBlockLoop s level resolveLarge (opened + o - 1) t fuel

/-- `shrink_literal` on the literals of the block `clause[p..e)`. -/
def shrinkBlockLits (s : Solver) (level : UInt32) (p e : Nat) : Solver :=
  if _h : p < e then
    let lit := s.clause.get! p
    let s := if lit == INVALID_LIT then s else (s.shrinkLiteral level lit).2
    s.shrinkBlockLits level (p + 1) e
  else s
termination_by e - p

/-- Every literal of `clause[p..e)` is valid, its variable is assigned on the trail at the
  position recorded in `assigned[idx].trail`, and that position is at most `maxTrail`. -/
def blockPositionsOK (s : Solver) (p e maxTrail : Nat) : Bool :=
  if _h : p < e then
    let lit := s.clause.get! p
    let q := (s.trailIdx (IDX lit)).toNat
    lit != INVALID_LIT && q ≤ maxTrail && q < s.asg.trail.size &&
      IDX (s.asg.trail.get! q) == IDX lit && s.blockPositionsOK (p + 1) e maxTrail
  else true
termination_by e - p

/-- Port of `shrink_block` (shrink.c). -/
def shrinkBlock (s : Solver) (beginBlock endBlock : Nat) (level : UInt32) (maxTrail : Nat) :
    Nat × Solver :=
  let opened := endBlock - beginBlock
  -- checked assertions: the shrinkable stack is empty (`minimize_and_shrink_block`) and every
  -- block literal lies on the trail at or before `maxTrail` (otherwise do not shrink this block)
  if !(Decidable.decide (maxTrail < s.asg.trail.size) && s.shrinkable.size == 0 &&
      s.blockPositionsOK beginBlock endBlock maxTrail)
  then (0, s) else
  let before := s.shrinkable.size
  let s := s.shrinkBlockLits level beginBlock endBlock
  -- checked assertion: every block literal became shrinkable
  if s.shrinkable.size != before + opened then (0, s.resetShrinkable) else
  let resolveLarge := s.options.shrink > 1
  let (uip, failed, s2) := s.shrinkBlockLoop level resolveLarge opened maxTrail (s.asg.trail.size + 1)
  if failed then (0, s2.resetShrinkable)
  else s2.shrunkenBlock beginBlock endBlock uip

/-- Port of `next_block` (shrink.c): returns `(beginBlock, level, maxTrail)`. -/
def nextBlock (s : Solver) (endBlock : Nat) : Nat × UInt32 × Nat := Id.run do
  let mut level := INVALID_LEVEL
  let mut maxTrail := 0
  let mut b := endBlock
  for _ in [0:endBlock] do
    let lit := s.clause.get! (b - 1)
    let idx := IDX lit
    let litLevel := s.levelIdx idx
    if level == INVALID_LEVEL then level := litLevel
    else if litLevel > level then break
    b := b - 1
    let tr := (s.trailIdx idx).toNat
    if tr > maxTrail then maxTrail := tr
  return (b, level, maxTrail)

/-- The literal loop of `minimize_block`. -/
def minimizeBlockLoop (s : Solver) (p e minimized : Nat) : Nat × Solver :=
  if _h : p < e then
    let lit := s.clause.get! p
    let (ok, s) := s.minimizeLiteralTop lit true
    if !ok then s.minimizeBlockLoop (p + 1) e minimized
    else ({ s with clause := s.clause.set! p INVALID_LIT } : Solver).minimizeBlockLoop (p + 1) e (minimized + 1)
  else (minimized, s)
termination_by e - p

/-- Port of `minimize_block` (shrink.c). -/
def minimizeBlock (s : Solver) (beginBlock endBlock : Nat) : Nat × Solver :=
  s.minimizeBlockLoop beginBlock endBlock 0

/-- Port of `minimize_and_shrink_block` (shrink.c). Returns the new end. -/
def minimizeAndShrinkBlock (s : Solver) (endBlock : Nat) : Nat × Solver :=
  let (beginBlock, level, maxTrail) := s.nextBlock endBlock
  let opened := endBlock - beginBlock
  if opened < 2 then (beginBlock, s)
  else
    let (shrunken, s) := s.shrinkBlock beginBlock endBlock level maxTrail
    if shrunken == 0 then
      let (_, s) := s.minimizeBlock beginBlock endBlock
      (beginBlock, s)
    else (beginBlock, s)

/-- Outer loop of `kissat_shrink_clause`. -/
def shrinkClauseLoop (s : Solver) (endBlock : Nat) : Solver :=
  if _h : endBlock = 0 then s
  else
    let (b, s) := s.minimizeAndShrinkBlock endBlock
    if _hb : b < endBlock then shrinkClauseLoop s b
    else s  -- unreachable: `next_block` consumes at least one literal
termination_by endBlock

/-- Port of `kissat_shrink_clause` (shrink.c). -/
def shrinkClause (s : Solver) : Solver :=
  let s := s.shrinkClauseLoop s.clause.size
  let s := s.compactClause
  -- ADD (literals_shrunken / literals_minshrunken): METRIC
  s.resetPoisoned

end Solver
end LeanKissat
