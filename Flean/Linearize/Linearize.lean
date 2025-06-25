import Mathlib.Data.Int.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Term
import Flean.Linearize.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Linearize Tactic

The `linearize` tactic transforms exponential inequalities of the form `a < (b : R)^z`
(where `b` is a natural number base, `z` is an integer exponent, and `R` is a linear ordered field)
into logarithmic form using `Int.log` to make them suitable for `linarith`.

## Usage

```lean
example (a : ℝ) (h : 1 < a) (h2 : a < (2 : ℝ)^100) : a < (2 : ℝ)^200 := by
  linearize at h2  -- transforms to: Int.log 2 a < 100
  linarith

-- Or use linearize! to automatically apply linarith (with omega fallback)
example (a : ℝ) (h : 1 < a) (h2 : a < (2 : ℝ)^100) : a < (2 : ℝ)^200 := by
  linearize! at h2  -- transforms and applies linarith automatically

-- linearize! also supports passing additional lemmas to linarith
example (a : ℝ) (h : 1 < a) (h2 : a < (2 : ℝ)^5) (extra : Int.log 2 a ≥ 2) : Int.log 2 a ≤ 4 := by
  linearize! [extra] at h2  -- passes extra to linarith

-- linearize! will fall back to omega if linarith fails (useful for integer reasoning)
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^5) (extra : Int.log 2 a ≥ 2) :
    Int.log 2 a = 4 ∨ Int.log 2 a = 3 ∨ Int.log 2 a = 2 := by
  linearize! [extra] at h  -- uses omega fallback for disjunctive reasoning

-- Goal linearization for same-base exponential comparisons
example (m n : ℤ) (h : m < n) : (2 : ℝ)^m < (2 : ℝ)^n := by
  linearize  -- automatically reduces to m < n and solves
```
-/

/-
Relevant pieces
def Int.log{R : Type u_1} [Semifield R] [LinearOrder R] [FloorSemiring R] (b : ℕ) (r : R) :
ℤ
The greatest power of b such that b ^ log b r ≤ r.

theorem Int.zpow_log_le_self{R : Type u_1} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
↑b ^ log b r ≤ r

theorem Int.lt_zpow_succ_log_self{R : Type u_1} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} (hb : 1 < b) (r : R) :
r < ↑b ^ (log b r + 1)

theorem Int.log_zpow{R : Type u_1} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} (hb : 1 < b) (z : ℤ) :
log b (↑b ^ z) = z

theorem Int.lt_zpow_iff_log_lt{R : Type u_1} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
r < ↑b ^ x ↔ log b r < x
zpow b and Int.log b (almost) form a Galois connection.

theorem Int.zpow_le_iff_le_log{R : Type u_1} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
↑b ^ x ≤ r ↔ x ≤ log b r
zpow b and Int.log b (almost) form a Galois connection.
-/

namespace Mathlib.Tactic.Linearize

open Lean Elab Meta Tactic Qq Parser.Tactic

initialize registerTraceClass `linearize

/-- Helper to convert an Nat | Int to an Int -/
def asInt (e : Expr) : MetaM Q(ℤ) := do
  if (← inferType e).constName? == .some ``Nat then
    have e : Q(ℕ) := e
    pure q(Int.ofNat $e)
  else
    pure e

/-- Check if an expression represents the literal 1, unwrapping various coercion layers -/
def isLiteralOne (e : Expr) : Bool :=
  e.isConstOf ``One.one ||
  (match e.getAppFnArgs with
   | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit? == some 1
   | (``Int.ofNat, #[n]) =>
     n.rawNatLit? == some 1 || n.isConstOf ``One.one ||
     (match n.getAppFnArgs with
      | (``OfNat.ofNat, #[_, m, _]) => m.rawNatLit? == some 1
      | _ => false)
   | (``Nat.cast, #[_, _, n]) =>
     n.rawNatLit? == some 1 || n.isConstOf ``One.one ||
     (match n.getAppFnArgs with
      | (``OfNat.ofNat, #[_, m, _]) => m.rawNatLit? == some 1
      | _ => false)
   | _ => false)

/-- Check if an expression represents the literal 0, unwrapping various coercion layers -/
def isLiteralZero (e : Expr) : Bool :=
  e.isConstOf ``Zero.zero ||
  (match e.getAppFnArgs with
   | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit? == some 0
   | (``Int.ofNat, #[n]) =>
     n.rawNatLit? == some 0 || n.isConstOf ``Zero.zero ||
     (match n.getAppFnArgs with
      | (``OfNat.ofNat, #[_, m, _]) => m.rawNatLit? == some 0
      | _ => false)
   | (``Nat.cast, #[_, _, n]) =>
     n.rawNatLit? == some 0 || n.isConstOf ``Zero.zero ||
     (match n.getAppFnArgs with
      | (``OfNat.ofNat, #[_, m, _]) => m.rawNatLit? == some 0
      | _ => false)
   | _ => false)

/-- Try to solve an LT side goal of the form `lhs < rhs` -/
def solveLTSideGoal (g : MVarId) (lhs _rhs : Expr) : TacticM (Option MVarId) := do
  -- Save the current goal state
  let savedGoals ← getGoals

  -- Check if lhs is 1
  let isOne := isLiteralOne lhs
  if isOne then
    -- This is a 1 < b goal, try norm_num first
    trace[linearize] "Detected 1 < b pattern, trying norm_num"
    try
      setGoals [g]
      evalTactic (← `(tactic| norm_num))
      let remainingGoals ← getGoals
      setGoals savedGoals
      if remainingGoals.isEmpty then
        return none  -- Goal was solved
      else
        return some g
    catch _ =>
      -- norm_num failed, try linarith
      trace[linearize] "norm_num failed, trying linarith"
      try
        setGoals [g]
        evalTactic (← `(tactic| linarith))
        let remainingGoals ← getGoals
        setGoals savedGoals
        if remainingGoals.isEmpty then
          return none  -- Goal was solved
        else
          return some g
      catch _ =>
        setGoals savedGoals
        trace[linearize] "linarith also failed, keeping as side goal"
        return some g
  else
    -- This is a 0 < a type goal, try assumption first
    trace[linearize] "Detected 0 < a pattern, trying assumption"
    let result ← observing? g.assumption
    match result with
    | some _ => return none  -- Goal was solved
    | none =>
      -- assumption failed, try norm_num first (good for numeric casts like 0 < ↑2)
      trace[linearize] "assumption failed, trying norm_num"
      try
        setGoals [g]
        evalTactic (← `(tactic| norm_num))
        let remainingGoals ← getGoals
        setGoals savedGoals
        if remainingGoals.isEmpty then
          return none  -- Goal was solved
        else
          return some g
      catch _ =>
        -- norm_num failed, try linarith
        trace[linearize] "norm_num failed, trying linarith"
        try
          setGoals [g]
          evalTactic (← `(tactic| linarith))
          let remainingGoals ← getGoals
          setGoals savedGoals
          if remainingGoals.isEmpty then
            return none  -- Goal was solved
          else
            return some g
        catch _ =>
          setGoals savedGoals
          trace[linearize] "linarith also failed, keeping as side goal"
          return some g

/-- Try to solve an LE side goal of the form `lhs ≤ rhs` -/
def solveLESideGoal (g : MVarId) (lhs _rhs : Expr) : TacticM (Option MVarId) := do
  -- Save the current goal state
  let savedGoals ← getGoals

  -- Check if lhs is 1 (for patterns like 1 ≤ b)
  let isOne := isLiteralOne lhs
  if isOne then
    -- This is a 1 ≤ b goal, try norm_num first
    trace[linearize] "Detected 1 ≤ b pattern, trying norm_num"
    try
      setGoals [g]
      evalTactic (← `(tactic| norm_num))
      let remainingGoals ← getGoals
      setGoals savedGoals
      if remainingGoals.isEmpty then
        return none  -- Goal was solved
      else
        return some g
    catch _ =>
      -- norm_num failed, try linarith
      trace[linearize] "norm_num failed, trying linarith"
      try
        setGoals [g]
        evalTactic (← `(tactic| linarith))
        let remainingGoals ← getGoals
        setGoals savedGoals
        if remainingGoals.isEmpty then
          return none  -- Goal was solved
        else
          return some g
      catch _ =>
        setGoals savedGoals
        trace[linearize] "linarith also failed, keeping as side goal"
        return some g
  else
    -- This is a 0 ≤ a type goal, try assumption first
    trace[linearize] "Detected 0 ≤ a pattern, trying assumption"
    let result ← observing? g.assumption
    match result with
    | some _ => return none  -- Goal was solved
    | none =>
      -- assumption failed, try norm_num first (good for numeric casts like 0 ≤ ↑2)
      trace[linearize] "assumption failed, trying norm_num"
      try
        setGoals [g]
        evalTactic (← `(tactic| norm_num))
        let remainingGoals ← getGoals
        setGoals savedGoals
        if remainingGoals.isEmpty then
          return none  -- Goal was solved
        else
          return some g
      catch _ =>
        -- norm_num failed, try linarith
        trace[linearize] "norm_num failed, trying linarith"
        try
          setGoals [g]
          evalTactic (← `(tactic| linarith))
          let remainingGoals ← getGoals
          setGoals savedGoals
          if remainingGoals.isEmpty then
            return none  -- Goal was solved
          else
            return some g
        catch _ =>
          setGoals savedGoals
          trace[linearize] "linarith also failed, keeping as side goal"
          return some g

/-- Try to solve a side goal automatically based on its type -/
def trySolveSideGoal (g : MVarId) : TacticM (Option MVarId) := do
    -- Check if the goal is already assigned
    if ← g.isAssigned then
      trace[linearize] "Goal already solved"
      return none

    -- Get the goal type to determine what kind of side condition it is
    let goalType ← g.getType
    trace[linearize] "Trying to auto-solve side goal: {goalType}"

    -- Debug: print the app function and args
    let (fn, args) := goalType.getAppFnArgs
    trace[linearize] "Goal app function: {fn}, num args: {args.size}"

    -- Dispatch to specialized handlers based on comparison type
    match goalType.getAppFnArgs with
    | (``LT.lt, #[_, _, lhs, rhs]) =>
      solveLTSideGoal g lhs rhs
    | (``LE.le, #[_, _, lhs, rhs]) =>
      solveLESideGoal g lhs rhs
    | (``Ne, #[_, _lhs, _rhs]) =>
      -- This is a ≠ goal, try assumption first
      trace[linearize] "Detected ≠ pattern, trying assumption"
      let result ← observing? g.assumption
      match result with
      | some _ => return none  -- Goal was solved
      | none =>
        -- assumption failed, try norm_num
        trace[linearize] "assumption failed, trying norm_num"
        let savedGoals ← getGoals
        try
          setGoals [g]
          evalTactic (← `(tactic| norm_num))
          let remainingGoals ← getGoals
          setGoals savedGoals
          if remainingGoals.isEmpty then
            return none  -- Goal was solved
          else
            return some g
        catch _ =>
          setGoals savedGoals
          trace[linearize] "norm_num also failed, keeping as side goal"
          return some g
    | _ =>
      -- Unknown goal type, try norm_num as a last resort
      trace[linearize] "Unknown side goal type, trying norm_num"
      let savedGoals ← getGoals
      try
        setGoals [g]
        evalTactic (← `(tactic| norm_num))
        let remainingGoals ← getGoals
        setGoals savedGoals
        if remainingGoals.isEmpty then
          return none  -- Goal was solved
        else
          trace[linearize] "norm_num couldn't solve it, keeping as side goal"
          return some g
      catch _ =>
        setGoals savedGoals
        trace[linearize] "norm_num failed, keeping as side goal"
        return some g



/-- Check if an expression is of the form `(b : R)^z` where `b` is a natural number literal -/
def isNatCastZpow (e : Expr) : MetaM (Option (ℕ × Expr × Expr × Expr)) := do
  trace[linearize] "Checking if zpow: {e}"
  match e.getAppFnArgs with
  | (``HPow.hPow, #[_, _, _, _, base, exponent]) =>
    trace[linearize] "Found HPow.hPow with base: {base}, exponent: {exponent}"
    -- Check if base is a natural number cast
    match base.getAppFnArgs with
    | (``Nat.cast, #[R, _, natExpr]) =>
      trace[linearize] "Found Nat.cast base with natExpr: {natExpr}"
      -- Try to extract the natural number value
      if let some n := natExpr.rawNatLit? then
        trace[linearize] "Found natural number: {n}"
        return some (n, base, exponent, R)
      else
        trace[linearize] "No natural number found"
        return none
    | (``OfNat.ofNat, #[R, natExpr, _]) =>
      trace[linearize] "Found OfNat.ofNat base with natExpr: {natExpr}"
      -- Try to extract the natural number value
      if let some n := natExpr.rawNatLit? then
        trace[linearize] "Found natural number: {n}"
        return some (n, base, exponent, R)
      else
        trace[linearize] "No natural number found"
        return none
    | _ =>
      trace[linearize] "Base is not Nat.cast: {base.getAppFnArgs}"
      return none
  | (``Pow.pow, #[_, _, _, base, exponent]) =>
    trace[linearize] "Found Pow.pow with base: {base}, exponent: {exponent}"
    -- Also handle Pow.pow for natural exponents
    have exponent : Q(ℕ) := exponent
    match base.getAppFnArgs with
    | (``Nat.cast, #[R, _, natExpr]) =>
      trace[linearize] "Found Nat.cast base with natExpr: {natExpr}"
      -- Try to extract the natural number value
      if let some n := natExpr.rawNatLit? then
        trace[linearize] "Found natural number: {n}"
        -- Convert natural exponent to integer
        let instNatCast ← synthInstanceQ q(NatCast ℤ)
        have intExp : Q(ℤ) := q(@Nat.cast ℤ $instNatCast $exponent)
        return some (n, base, intExp, R)
      else
        trace[linearize] "No natural number found"
        return none
    | (``OfNat.ofNat, #[R, natExpr, _]) =>
      trace[linearize] "Found OfNat.ofNat base with natExpr: {natExpr}"
      -- Try to extract the natural number value
      if let some n := natExpr.rawNatLit? then
        trace[linearize] "Found natural number: {n}"
        -- Convert natural exponent to integer
        let instNatCast ← synthInstanceQ q(NatCast ℤ)
        have intExp : Q(ℤ) := q(@Nat.cast ℤ $instNatCast $exponent)
        return some (n, base, intExp, R)
      else
        trace[linearize] "No natural number found"
        return none
    | _ =>
      trace[linearize] "Base is not Nat.cast: {base.getAppFnArgs}"
      return none
  | _ => return none

/-- Check if an expression is a comparison that we can linearize -/
def isLinearizableComparison (e : Expr) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``LT.lt, #[_, _, _, _]) => return true
  | (``LE.le, #[_, _, _, _]) => return true
  | (``GT.gt, #[_, _, _, _]) => return true
  | (``GE.ge, #[_, _, _, _]) => return true
  | (``Eq, #[_, _, _]) => return true
  | _ => return false

/-- Transform a comparison involving zpow to use Int.log -/
def transformZpowComparison (e : Expr) : MetaM (Option Q(Prop)) := do
  trace[linearize] "Transforming comparison: {e}"
  -- Necessary instances for the theorem and side goals
  match e.getAppFnArgs with
  | (``LT.lt, #[_R, _inst, lhs, rhs]) =>
    -- Case: lhs < rhs
    let ⟨_, R, lhs⟩ ← inferTypeQ' lhs
    have rhs : Q($R) := rhs
    trace[linearize] "lt: lhs: {lhs}; R: {R}"

    let _a1 ← synthInstanceQ q(Semifield $R)
    let _a2 ← synthInstanceQ q(LinearOrder $R)
    let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
    let _a4 ← synthInstanceQ q(FloorSemiring $R)

    if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
      if let some (b_lhs, _, exp_lhs, _) ← isNatCastZpow lhs then
        -- Check if both sides have the same base: a^m < a^n � m < n (when 1 < a)
        if b_lhs == b_rhs then
          let intExpLhs ← asInt exp_lhs
          let intExpRhs ← asInt exp_rhs
          pure (some q($intExpLhs < $intExpRhs))
        else
          return none
      else
        -- Skip linearization if lhs is 0 (since Int.log b 0 doesn't make sense)
        if isLiteralZero lhs then
          return none
        -- lhs < (b : R)^exp � Int.log b lhs < exp (when 0 < lhs, 1 < b)
        have b : Q(ℕ) := mkNatLit b_rhs
        have logExpr : Q(ℤ) := q(Int.log $b $lhs)
        let intExp ← asInt exp_rhs
        pure (some q($logExpr < $intExp))
    else if let some (b, _, exp, _) ← isNatCastZpow lhs then
      -- Skip linearization if rhs is 0 (since Int.log b 0 doesn't make sense)
      if isLiteralZero rhs then
        return none
      -- (b : R)^exp < rhs � exp < Int.log b rhs + 1 (when 0 < rhs, 1 < b)
      have b : Q(ℕ) := mkNatLit b
      have plusOne : Q(ℤ) := q(Int.log $b $rhs + 1)
      let intExp ← asInt exp
      pure (some q($intExp < $plusOne))
    else
      return none
  | (``LE.le, #[_R, _inst, lhs, rhs]) =>
    let ⟨_, R, lhs⟩ ← inferTypeQ' lhs
    have rhs : Q($R) := rhs

    trace[linearize] "le: lhs: {lhs}; R: {R}"

    let _a1 ← synthInstanceQ q(Semifield $R)
    let _a2 ← synthInstanceQ q(LinearOrder $R)
    let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
    let _a4 ← synthInstanceQ q(FloorSemiring $R)

    if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
      if let some (b_lhs, _, exp_lhs, _) ← isNatCastZpow lhs then
        -- Check if both sides have the same base: a^m ≤ a^n ↔ m ≤ n (when 1 < a)
        if b_lhs == b_rhs then
          let intExpLhs ← asInt exp_lhs
          let intExpRhs ← asInt exp_rhs
          pure (some q($intExpLhs ≤ $intExpRhs))
        else
          return none
      else
        -- Skip linearization if lhs is 0 (since Int.log b 0 doesn't make sense)
        if isLiteralZero lhs then
          return none
        -- lhs ≤ (b : R)^exp ↔ Int.log b lhs ≤ exp (when 0 < lhs, 1 < b)
        have b : Q(ℕ) := mkNatLit b_rhs
        let intExp ← asInt exp_rhs
        pure (some q(Int.log $b $lhs ≤ $intExp))
    else if let some (b, _, exp, _) ← isNatCastZpow lhs then
      -- Skip linearization if rhs is 0 (since Int.log b 0 doesn't make sense)
      if isLiteralZero rhs then
        return none
      -- (b : R)^exp ≤ rhs ↔ exp ≤ Int.log b rhs (when 0 < rhs, 1 < b)
      have b : Q(ℕ) := mkNatLit b
      let intExp ← asInt exp
      pure (some q($intExp ≤ Int.log $b $rhs))
    else
      return none
  | _ => return none


/-- Find all linearizable hypotheses in the current goal -/
def findLinearizableHyps (g : MVarId) : TacticM (Array FVarId) := do
  g.withContext do
    let lctx ← getLCtx
    let mut fvars : Array FVarId := #[]
    for ldecl in lctx do
      if !ldecl.isImplementationDetail then
        -- Check if this hypothesis can be linearized
        let canLinearize ← try
          let result ← transformZpowComparison ldecl.type
          pure result.isSome
        catch _ =>
          pure false
        if canLinearize then
          fvars := fvars.push ldecl.fvarId
    pure fvars

/-- Linearize LT goals of various patterns involving zpow -/
def linearizeLTGoal (g : MVarId) (lhs rhs : Expr) : TacticM (List MVarId) := do
  trace[linearize] "linearizeLTGoal: lhs={lhs}, rhs={rhs}"
  trace[linearize] "  isLiteralOne(lhs)={isLiteralOne lhs}"
  trace[linearize] "  isLiteralZero(lhs)={isLiteralZero lhs}"

  -- Check for pattern 1 < a^n using one_lt_zpow₀
  if isLiteralOne lhs then
    trace[linearize] "  Pattern: 1 < a^n"
    if let some (b, _, exp, _) ← isNatCastZpow rhs then
      -- Check the type of the exponent to decide between zpow and pow
      let expType ← inferType exp
      if (← isDefEq expType q(ℕ)) then
        -- Natural exponent: use one_lt_pow'
        trace[linearize] "Applying one_lt_pow for base {b}"

        let ⟨_, R, _⟩ ← inferTypeQ' rhs

        have expNat : Q(ℕ) := exp
        have a : Q(ℕ) := mkNatLit b

        -- Need instances for one_lt_pow₀
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(PartialOrder $R)
        let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
        let _inst4 ← synthInstanceQ q(PosMulMono $R)

        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(1 < ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        let hnGoal ← mkFreshExprMVarQ q($expNat ≠ 0) MetavarKind.syntheticOpaque (`hn)

        have thmProof : Q((1 : $R) < ($a : $R) ^ $expNat) := q(one_lt_pow₀ $haGoal $hnGoal)

        -- Apply the theorem to reduce the goal
        g.assign thmProof

        Term.synthesizeSyntheticMVarsUsingDefault

        return [haGoal.mvarId!, hnGoal.mvarId!]
      else
        -- Integer exponent: use one_lt_zpow₀
        trace[linearize] "Applying one_lt_zpow₀ for base {b}"

        let ⟨_, R, _⟩ ← inferTypeQ' rhs

        let expInt : Q(ℤ) ← asInt exp
        have a : Q(ℕ) := mkNatLit b

        -- Need instances for one_lt_zpow₀
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(PartialOrder $R)
        let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
        let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)

        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(1 < ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        let hnGoal ← mkFreshExprMVarQ q(0 < $expInt) MetavarKind.syntheticOpaque (`hn)

        have thmProof : Q((1 : $R) < ($a : $R) ^ $expInt) := q(one_lt_zpow₀ $haGoal $hnGoal)

        -- Apply the theorem to reduce the goal
        g.assign thmProof

        Term.synthesizeSyntheticMVarsUsingDefault

        return [haGoal.mvarId!, hnGoal.mvarId!]
    else
      throwError "linearize: goal linearization for 1 < ... only supports power expressions with natural base"
  -- Check for pattern 0 < a^n using zpow_pos
  else if isLiteralZero lhs then
    trace[linearize] "  Pattern: 0 < a^n"
    if let some (b, _, exp, _) ← isNatCastZpow rhs then
      trace[linearize] "Applying zpow_pos for base {b}"

      let ⟨_, R, _⟩ ← inferTypeQ' rhs

      let exp : Q(ℤ) ← asInt exp
      have a : Q(ℕ) := mkNatLit b

      -- Need instances for zpow_pos
      let _inst1 ← synthInstanceQ q(DivisionRing $R)
      let _inst2 ← synthInstanceQ q(PartialOrder $R)
      let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
      let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)

      assumeInstancesCommute

      let haGoal ← mkFreshExprMVarQ q(0 < ($a : $R)) MetavarKind.syntheticOpaque (`ha)

      have thmProof : Q((0 : $R) < ($a : $R) ^ $exp) := q(zpow_pos $haGoal $exp)

      -- Apply the theorem to reduce the goal
      g.assign thmProof

      Term.synthesizeSyntheticMVarsUsingDefault

      return [haGoal.mvarId!]
    else
      throwError "linearize: goal linearization for 0 < ... only supports zpow expressions"
  else if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
    trace[linearize] "  Pattern: LHS not literal, but RHS is zpow"
    if let some (b_lhs, _, exp_lhs, _) ← isNatCastZpow lhs then
      -- Both sides are zpow with same base: a^m < a^n ↔ m < n (when 1 < a)
      if b_lhs == b_rhs then
        trace[linearize] "Applying zpow_lt_zpow_right₀ for base {b_lhs}"

        let ⟨_, R, _⟩ ← inferTypeQ' lhs

        let exp_lhs : Q(ℤ) ← asInt exp_lhs
        let exp_rhs : Q(ℤ) ← asInt exp_rhs
        have a : Q(ℕ) := mkNatLit b_lhs

        -- Need instances for zpow_lt_zpow_right₀
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(LinearOrder $R)
        let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
        let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)

        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(1 < ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        let hmnGoal ← mkFreshExprMVarQ q($exp_lhs < $exp_rhs) MetavarKind.syntheticOpaque (`hmn)

        have thmProof : Q(($a : $R) ^ $exp_lhs < ($a : $R) ^ $exp_rhs) := q(zpow_lt_zpow_right₀ $haGoal $hmnGoal)

        -- Apply the theorem to reduce the goal
        g.assign thmProof

        Term.synthesizeSyntheticMVarsUsingDefault

        return [haGoal.mvarId!, hmnGoal.mvarId!]
      else
        throwError "linearize: different bases not supported"
    else
      throwError "linearize: goal linearization only supports same-base zpow comparisons"
  else
    trace[linearize] "  Pattern: No pattern matched - final else in linearizeLTGoal"
    throwError "linearize: goal linearization only supports same-base zpow comparisons"

/-- Linearize LE goals of various patterns involving zpow -/
def linearizeLEGoal (g : MVarId) (lhs rhs : Expr) : TacticM (List MVarId) := do
  -- Check for pattern 0 ≤ a^n using zpow_nonneg
  if isLiteralZero lhs then
    if let some (b, _, exp, _) ← isNatCastZpow rhs then
      trace[linearize] "Applying zpow_nonneg for base {b}"

      let ⟨_, R, _⟩ ← inferTypeQ' rhs

      let exp : Q(ℤ) ← asInt exp
      have a : Q(ℕ) := mkNatLit b

      -- Need instances for zpow_nonneg (same as zpow_pos)
      let _inst1 ← synthInstanceQ q(DivisionRing $R)
      let _inst2 ← synthInstanceQ q(PartialOrder $R)
      let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
      let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)

      assumeInstancesCommute

      let haGoal ← mkFreshExprMVarQ q(0 ≤ ($a : $R)) MetavarKind.syntheticOpaque (`ha)

      have thmProof : Q((0 : $R) ≤ ($a : $R) ^ $exp) := q(zpow_nonneg $haGoal $exp)

      -- Apply the theorem to reduce the goal
      g.assign thmProof

      Term.synthesizeSyntheticMVarsUsingDefault

      return [haGoal.mvarId!]
    else
      throwError "linearize: goal linearization for 0 ≤ ... only supports zpow expressions"
  -- Check for pattern 1 ≤ a^n using one_le_zpow₀
  else if isLiteralOne lhs then
    if let some (b, _, exp, _) ← isNatCastZpow rhs then
      -- Check the type of the exponent to decide between zpow and pow
      let expType ← inferType exp
      if (← isDefEq expType q(ℕ)) then
        -- Natural exponent: use one_le_pow₀
        trace[linearize] "Applying one_le_pow₀ for base {b}"

        let ⟨_, R, _⟩ ← inferTypeQ' rhs

        have expNat : Q(ℕ) := exp
        have a : Q(ℕ) := mkNatLit b

        -- Need instances for one_le_pow₀
        -- let _inst1 ← synthInstanceQ q(MonoidWithZero $R)
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(Preorder $R)
        let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
        let _inst4 ← synthInstanceQ q(PosMulMono $R)

        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(1 ≤ ($a : $R)) MetavarKind.syntheticOpaque (`ha)

        have thmProof : Q((1 : $R) ≤ ($a : $R) ^ $expNat) := q(one_le_pow₀ $haGoal)

        -- Apply the theorem to reduce the goal
        g.assign thmProof

        Term.synthesizeSyntheticMVarsUsingDefault

        return [haGoal.mvarId!]
      else
        -- Integer exponent: use one_le_zpow₀
        trace[linearize] "Applying one_le_zpow₀ for base {b}"

        let ⟨_, R, _⟩ ← inferTypeQ' rhs

        let expInt : Q(ℤ) ← asInt exp
        have a : Q(ℕ) := mkNatLit b

        -- Need instances for one_le_zpow₀
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(PartialOrder $R)
        let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
        let _inst4 ← synthInstanceQ q(PosMulReflectLT $R)

        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(1 ≤ ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        let hnGoal ← mkFreshExprMVarQ q(0 ≤ $expInt) MetavarKind.syntheticOpaque (`hn)

        have thmProof : Q((1 : $R) ≤ ($a : $R) ^ $expInt) := q(one_le_zpow₀ $haGoal $hnGoal)

        -- Apply the theorem to reduce the goal
        g.assign thmProof

        Term.synthesizeSyntheticMVarsUsingDefault

        return [haGoal.mvarId!, hnGoal.mvarId!]
    else
      throwError "linearize: goal linearization for 1 ≤ ... only supports power expressions with natural base"
  else if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
    if let some (b_lhs, _, exp_lhs, _) ← isNatCastZpow lhs then
      -- Both sides are zpow with same base: a^m ≤ a^n ↔ m ≤ n (when 1 < a)
      if b_lhs == b_rhs then
        trace[linearize] "Applying zpow_le_zpow_right₀ for base {b_lhs}"

        let ⟨_, R, _⟩ ← inferTypeQ' lhs
        trace[linearize] "R = {R}"

        let exp_lhs : Q(ℤ) ← asInt exp_lhs
        let exp_rhs : Q(ℤ) ← asInt exp_rhs
        have a : Q(ℕ) := mkNatLit b_lhs
        trace[linearize] "exp_lhs={exp_lhs}; exp_rhs={exp_rhs}; a={a}"

        -- Need instances for zpow_le_zpow_right₀
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(LinearOrder $R)
        let _inst3 ← synthInstanceQ q(PosMulReflectLE $R)
        let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)

        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(1 ≤ ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        let hmnGoal ← mkFreshExprMVarQ q($exp_lhs ≤ $exp_rhs) MetavarKind.syntheticOpaque (`hmn)

        have thmProof : Q(($a : $R) ^ $exp_lhs ≤ ($a : $R) ^ $exp_rhs) := q(zpow_le_zpow_right₀ $haGoal $hmnGoal)

        -- Apply the theorem to reduce the goal
        g.assign thmProof

        Term.synthesizeSyntheticMVarsUsingDefault

        return [haGoal.mvarId!, hmnGoal.mvarId!]
      else
        throwError "linearize: different bases not supported"
    else
      throwError "linearize: goal linearization only supports same-base zpow comparisons"
  else
    throwError "linearize: goal linearization only supports same-base zpow comparisons"

/-- Apply linearization to a goal of the form a^m < a^n using zpow_lt_zpow_right₀ -/
def linearizeGoal (g : MVarId) : TacticM (List MVarId) := do
  g.withContext do
    let goalType ← g.getType
    trace[linearize] "=== ENTERING linearizeGoal ==="
    trace[linearize] "Analyzing goal: {goalType}"

    let (fn, args) := goalType.getAppFnArgs
    trace[linearize] "  Goal app function: {fn}"
    trace[linearize] "  Goal app args count: {args.size}"
    trace[linearize] "  Goal app args: {args}"

    -- Manual inspection of the goal structure
    trace[linearize] "  Goal expr kind: {goalType.ctorName}"
    match goalType with
    | .app f a =>
      trace[linearize] "  Goal is app: f={f}, a={a}"
      let (f2, args2) := f.getAppFnArgs
      trace[linearize] "    f app function: {f2}, args: {args2}"
    | .mvar id => trace[linearize] "  Goal is mvar: {id}"
    | .fvar id => trace[linearize] "  Goal is fvar"
    | .const name levels => trace[linearize] "  Goal is const: {name}, levels: {levels}"
    | _ => trace[linearize] "  Goal is other: {goalType.ctorName}"

    -- Try reducing the goal type first
    let goalTypeReduced ← whnf goalType
    trace[linearize] "  Reduced goal: {goalTypeReduced}"
    let (fnReduced, argsReduced) := goalTypeReduced.getAppFnArgs
    trace[linearize] "  Reduced app function: {fnReduced}"
    trace[linearize] "  Reduced app args count: {argsReduced.size}"

    -- Dispatch to specialized handlers based on comparison type
    -- First try the original goal type (works for most cases)
    match goalType.getAppFnArgs with
    | (``LT.lt, #[_, _, lhs, rhs]) =>
      trace[linearize] "  Dispatching to linearizeLTGoal (original 4-arg pattern)"
      linearizeLTGoal g lhs rhs
    | (``LE.le, #[_, _, lhs, rhs]) =>
      trace[linearize] "  Dispatching to linearizeLEGoal (original 4-arg pattern)"
      linearizeLEGoal g lhs rhs
    | _ =>
      -- If original doesn't work, try the reduced version (for mvar cases)
      trace[linearize] "  Original pattern didn't match, trying reduced goal"
      match goalTypeReduced.getAppFnArgs with
      | (``LT.lt, #[_, _, lhs, rhs]) =>
        trace[linearize] "  Dispatching to linearizeLTGoal (reduced 4-arg pattern)"
        linearizeLTGoal g lhs rhs
      | (``LE.le, #[_, _, lhs, rhs]) =>
        trace[linearize] "  Dispatching to linearizeLEGoal (reduced 4-arg pattern)"
        linearizeLEGoal g lhs rhs
      | (fn, #[lhs, rhs]) =>
        -- Check if this is a 2-argument LT or LE pattern
        trace[linearize] "  Checking reduced 2-arg pattern, fn={fn}"
        -- Use the reduced goal type expression to check structure
        if goalTypeReduced.isApp then
          let actualFn := goalTypeReduced.getAppFn
          trace[linearize] "  Actual function from reduced goal: {actualFn}, constName: {actualFn.constName?}"
          trace[linearize] "  Function kind: {actualFn.ctorName}"
          
          -- Check if it's a direct LT.lt or LE.le constant
          if actualFn.constName? == some ``LT.lt then
            trace[linearize] "  Dispatching to linearizeLTGoal (reduced 2-arg LT pattern)"
            linearizeLTGoal g lhs rhs
          else if actualFn.constName? == some ``LE.le then
            trace[linearize] "  Dispatching to linearizeLEGoal (reduced 2-arg LE pattern)"
            linearizeLEGoal g lhs rhs
          else
            -- Check if it's a projection or field that ultimately refers to LT.lt
            -- The structure might be something like `instX.toY.toLT.1` where `.1` is the `<` operator
            match actualFn with
            | .proj typeName idx _ =>
              trace[linearize] "  Function is projection: typeName={typeName}, idx={idx}"
              -- Check if this is a projection from a type that should contain LT
              if typeName == ``LT || typeName.toString.endsWith "LT" then
                trace[linearize] "  Dispatching to linearizeLTGoal (LT projection pattern)"
                linearizeLTGoal g lhs rhs
              else if typeName == ``LE || typeName.toString.endsWith "LE" then
                trace[linearize] "  Dispatching to linearizeLEGoal (LE projection pattern)"
                linearizeLEGoal g lhs rhs
              else
                trace[linearize] "  Projection is not LT/LE: {typeName}"
                throwError "linearize: goal linearization only supports < and ≤ comparisons"
            | _ =>
              trace[linearize] "  Function is not LT/LE: {actualFn.constName?}"
              throwError "linearize: goal linearization only supports < and ≤ comparisons"
        else
          trace[linearize] "  Reduced goal is not an app: {goalTypeReduced}"
          throwError "linearize: goal linearization only supports < and ≤ comparisons"
      | _ =>
        trace[linearize] "  Goal pattern not recognized - wrong number of args"
        trace[linearize] "  Original args count: {args.size}, Reduced args count: {argsReduced.size}"
        throwError "linearize: goal linearization only supports < and ≤ comparisons"

/-- Linearize LT hypotheses of various patterns involving zpow -/
def linearizeLTHyp (h : FVarId) (g : MVarId) (d : LocalDecl) (transformed : Q(Prop)) (lhs rhs : Expr) : TacticM (List MVarId) := do
  if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
    if let some (b_lhs, _, _exp_lhs, _) ← isNatCastZpow lhs then
      -- Both sides are zpow with same base - this should be handled in goal linearization
      if b_lhs == b_rhs then
        throwError "linearize: same-base zpow hypotheses not supported, try applying this to a goal instead"
      else
        throwError "linearize: different bases not supported"
    else
      -- Only RHS is zpow: lhs < b^exp
      let b := b_rhs
      let exp := exp_rhs
      trace[linearize] "Applying Int.lt_zpow_iff_log_lt for base {b}"

      -- Get the type of the LHS, because using the R from LT.lt causes synth instance issues
      -- like failing to find Semifield ℝ
      let ⟨_, R, lhs⟩ ← inferTypeQ' lhs

      let exp : Q(ℤ) ← asInt exp -- this could be an int or nat in the expr
      have b : Q(ℕ) := mkNatLit b

      -- Necessary instances for the theorem and side goals
      let _a1 ← synthInstanceQ q(Semifield $R)
      let _a2 ← synthInstanceQ q(LinearOrder $R)
      let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
      let _a4 ← synthInstanceQ q(FloorSemiring $R)

      assumeInstancesCommute -- undocumented but used everywhere /shrug

      let hbGoal ← mkFreshExprMVarQ q(1 < $b) MetavarKind.syntheticOpaque (`hb)
      let hrGoal ← mkFreshExprMVarQ q(0 < $lhs) MetavarKind.syntheticOpaque (`hr)

      have dType : Q(Prop) := d.type
      have thmType : Q(Prop) := q($dType ↔ $transformed)
      let thmMVar ← mkFreshExprMVarQ thmType MetavarKind.syntheticOpaque `thm

      trace[linearize] "lhs: {lhs}; exp: {exp}; b: {b}; R: {R}"
      have thmProof : Q($lhs < ($b : $R) ^ $exp ↔ Int.log $b $lhs < $exp) := q(Int.lt_zpow_iff_log_lt (R := $R) (x := $exp) (r := $lhs) $hbGoal $hrGoal)
      thmMVar.mvarId!.assign thmProof

      -- let proof ← mkAppM ``Iff.mp #[thmMVar, d.toExpr]
      let dExpr: Q($lhs < ($b : $R) ^ $exp) := d.toExpr
      have proof := q(Iff.mp $thmProof $dExpr)

      let g ← g.clear h
      let (_, g) ← g.note d.userName proof

      Term.synthesizeSyntheticMVarsUsingDefault

      return [g, hbGoal.mvarId!, hrGoal.mvarId!]
  else if let some (b, _, exp, _) ← isNatCastZpow lhs then
    -- (b : R)^exp < rhs ↔ exp < Int.log b rhs + 1 (when 0 < rhs, 1 < b)
    trace[linearize] "Applying zpow_lt pattern for base {b} (b^x < r direction)"

    let ⟨_, R, rhs⟩ ← inferTypeQ' rhs

    let exp : Q(ℤ) ← asInt exp
    have b : Q(ℕ) := mkNatLit b

    -- Necessary instances for the theorem and side goals
    let _a1 ← synthInstanceQ q(Semifield $R)
    let _a2 ← synthInstanceQ q(LinearOrder $R)
    let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
    let _a4 ← synthInstanceQ q(FloorSemiring $R)

    assumeInstancesCommute

    let hbGoal ← mkFreshExprMVarQ q(1 < $b) MetavarKind.syntheticOpaque (`hb)
    let hrGoal ← mkFreshExprMVarQ q(0 < $rhs) MetavarKind.syntheticOpaque (`hr)

    let thmMVar ← mkFreshExprMVar q($exp < Int.log $b $rhs + 1) MetavarKind.syntheticOpaque `thm
    have thmProof : Q(↑$b ^ $exp < $rhs → $exp < Int.log $b $rhs + 1) := q(Mathlib.Tactic.Linearize.zpow_lt_imp_lt_log_succ (R := $R) (b := $b) (n := $exp) (r := $rhs) $hbGoal $hrGoal)
    thmMVar.mvarId!.assign thmProof

    let dExpr : Q(↑$b ^ $exp < $rhs) := d.toExpr
    have proof := q($thmProof $dExpr)

    let g ← g.clear h
    let (_, g) ← g.note d.userName proof

    Term.synthesizeSyntheticMVarsUsingDefault

    return [g, hbGoal.mvarId!, hrGoal.mvarId!]
  else
    throwError "linearize: unsupported zpow expression"

/-- Linearize LE hypotheses of various patterns involving zpow -/
def linearizeLEHyp (h : FVarId) (g : MVarId) (d : LocalDecl) (transformed : Q(Prop)) (lhs rhs : Expr) : TacticM (List MVarId) := do
  if let some (b, _, exp, _) ← isNatCastZpow rhs then
    trace[linearize] "Applying le_zpow_iff_log_le for base {b}"

    let ⟨_, R, lhs⟩ ← inferTypeQ' lhs

    let exp : Q(ℤ) ← asInt exp
    have b : Q(ℕ) := mkNatLit b

    -- Necessary instances for the theorem and side goals
    let _a1 ← synthInstanceQ q(Semifield $R)
    let _a2 ← synthInstanceQ q(LinearOrder $R)
    let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
    let _a4 ← synthInstanceQ q(FloorSemiring $R)

    assumeInstancesCommute

    let hbGoal ← mkFreshExprMVarQ q(1 < $b) MetavarKind.syntheticOpaque (`hb)
    let hrGoal ← mkFreshExprMVarQ q(0 < $lhs) MetavarKind.syntheticOpaque (`hr)

    let thmMVar ← mkFreshExprMVar q(Int.log $b $lhs ≤ $exp) MetavarKind.syntheticOpaque `thm

    have thmProof : Q($lhs ≤ ↑$b ^ $exp → Int.log $b $lhs ≤ $exp) := q(Mathlib.Tactic.Linearize.le_zpow_imp_log_le (R := $R) (b := $b) (n := $exp) (r := $lhs) $hbGoal $hrGoal)
    thmMVar.mvarId!.assign thmProof

    let dExpr : Q($lhs ≤ ↑$b ^ $exp) := d.toExpr
    have proof := q($thmProof $dExpr)

    let g ← g.clear h
    let (_, g) ← g.note d.userName proof

    Term.synthesizeSyntheticMVarsUsingDefault

    return [g, hbGoal.mvarId!, hrGoal.mvarId!]
  else if let some (b, _, exp, _) ← isNatCastZpow lhs then
    trace[linearize] "Applying Int.zpow_le_iff_le_log for base {b} (reverse direction)"

    let ⟨_, R, rhs⟩ ← inferTypeQ' rhs

    let exp : Q(ℤ) ← asInt exp
    have b : Q(ℕ) := mkNatLit b

    -- Necessary instances for the theorem and side goals
    let _a1 ← synthInstanceQ q(Semifield $R)
    let _a2 ← synthInstanceQ q(LinearOrder $R)
    let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
    let _a4 ← synthInstanceQ q(FloorSemiring $R)

    assumeInstancesCommute

    let hbGoal ← mkFreshExprMVarQ q(1 < $b) MetavarKind.syntheticOpaque (`hb)
    let hrGoal ← mkFreshExprMVarQ q(0 < $rhs) MetavarKind.syntheticOpaque (`hr)

    have dType : Q(Prop) := d.type
    have thmType : Q(Prop) := q($dType ↔ $transformed)
    let thmMVar ← mkFreshExprMVarQ thmType MetavarKind.syntheticOpaque `thm

    have thmProof : Q(↑$b ^ $exp ≤ $rhs ↔ $exp ≤ Int.log $b $rhs) := q(Int.zpow_le_iff_le_log (R := $R) (x := $exp) (r := $rhs) $hbGoal $hrGoal)
    thmMVar.mvarId!.assign thmProof

    let dExpr: Q(↑$b ^ $exp ≤ $rhs) := d.toExpr
    have proof := q(Iff.mp $thmProof $dExpr)

    let g ← g.clear h
    let (_, g) ← g.note d.userName proof

    Term.synthesizeSyntheticMVarsUsingDefault

    return [g, hbGoal.mvarId!, hrGoal.mvarId!]
  else
    throwError "linearize: unsupported zpow expression"

/-- Apply linearization to a single hypothesis using the mathlib pattern -/
def linearizeHyp (h : FVarId) (g : MVarId) : TacticM (List MVarId) := do
  g.withContext do
    let d ← h.getDecl
    trace[linearize] "Analyzing hypothesis {d.userName} : {d.type}"

    -- Check if this hypothesis can be linearized
    let transformed? ← try
      transformZpowComparison d.type
    catch _ =>
      pure none
    match transformed? with
    | some transformed => do
      trace[linearize] "Can linearize to: {transformed}"

      -- Dispatch to specialized handlers based on comparison type
      match d.type.getAppFnArgs with
      | (``LT.lt, #[_, _, lhs, rhs]) =>
        linearizeLTHyp h g d transformed lhs rhs
      | (``LE.le, #[_, _, lhs, rhs]) =>
        linearizeLEHyp h g d transformed lhs rhs
      | _ =>
        throwError "linearize: unexpected comparison type"

    | none =>
      throwError "linearize: hypothesis {d.userName} cannot be linearized"

/-- Apply linearization at the specified location -/
def linearizeAtLocation (loc : Location) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    match loc with
    | Location.targets hyps simplifyTarget =>
      -- Get hypothesis FVarIds
      let targetFVars ← hyps.filterMapM fun hyp => do
        let fvarId ← getFVarId hyp
        -- Verify it's linearizable
        let decl ← fvarId.getDecl
        let canLinearize ← try
          let _ ← transformZpowComparison decl.type
          pure true
        catch _ =>
          pure false
        if canLinearize then
          return some fvarId
        else
          throwError "linearize: hypothesis {hyp} cannot be linearized"

      if targetFVars.isEmpty && !simplifyTarget then
        throwError "linearize: no suitable hypotheses found"

      if targetFVars.isEmpty && simplifyTarget then
        -- Only target specified, try goal linearization
        trace[linearize] "Only target specified, trying goal linearization"
        try
          let newGoals ← linearizeGoal g
          let mut remainingSideGoals : List MVarId := []
          for sideGoal in newGoals do
            match ← trySolveSideGoal sideGoal with
            | none =>
              trace[linearize] "Successfully auto-solved side goal"
            | some g =>
              trace[linearize] "Could not auto-solve side goal, keeping it"
              remainingSideGoals := remainingSideGoals.append [g]

          replaceMainGoal remainingSideGoals
          return
        catch e =>
          throwError "linearize: goal linearization failed: {e.toMessageData}"

      -- Apply linearization to hypotheses
      let mut currentGoal := g
      let mut allNewGoals : List MVarId := []

      for fvar in targetFVars do
        let newGoals ← linearizeHyp fvar currentGoal
        match newGoals with
        | mainGoal :: sideGoals =>
          currentGoal := mainGoal
          allNewGoals := allNewGoals ++ sideGoals
        | [] =>
          throwError "linearize: internal error - no goals returned"

      -- If target is also specified, try goal linearization on the remaining goal
      if simplifyTarget then
        try
          let goalNewGoals ← linearizeGoal currentGoal
          allNewGoals := allNewGoals ++ goalNewGoals
          -- If goal linearization succeeded, the goal is solved
          replaceMainGoal allNewGoals
          return
        catch _ =>
          -- Goal linearization failed, continue with hypothesis linearization only
          pure ()

      -- Try to automatically solve side goals
      trace[linearize] "Attempting to auto-solve {allNewGoals.length} side goals"
      let mut remainingSideGoals : List MVarId := []
      for sideGoal in allNewGoals do
        match ← trySolveSideGoal sideGoal with
        | none =>
          trace[linearize] "Successfully auto-solved side goal"
        | some g =>
          trace[linearize] "Could not auto-solve side goal, keeping it"
          remainingSideGoals := remainingSideGoals.append [g]

      -- Set the new goal list
      replaceMainGoal (currentGoal :: remainingSideGoals)

    | Location.wildcard =>
      -- Apply to all suitable hypotheses and the target
      let targetFVars ← findLinearizableHyps g

      if targetFVars.isEmpty then
        -- No hypotheses found, try goal linearization only
        try
          let newGoals ← linearizeGoal g
          let mut remainingSideGoals : List MVarId := []
          for sideGoal in newGoals do
            match ← trySolveSideGoal sideGoal with
            | none =>
              trace[linearize] "Successfully auto-solved side goal"
            | some g =>
              trace[linearize] "Could not auto-solve side goal, keeping it"
              remainingSideGoals := remainingSideGoals.append [g]
          replaceMainGoal remainingSideGoals
        catch e =>
          throwError "linearize: no suitable hypotheses found and goal linearization failed: {e.toMessageData}"
      else
        -- Apply linearization to hypotheses
        let mut currentGoal := g
        let mut allNewGoals : List MVarId := []

        for fvar in targetFVars do
          let newGoals ← linearizeHyp fvar currentGoal
          match newGoals with
          | mainGoal :: sideGoals =>
            currentGoal := mainGoal
            allNewGoals := allNewGoals ++ sideGoals
          | [] =>
            throwError "linearize: internal error - no goals returned"

        -- Also try goal linearization
        let mut goalLinearized := false
        try
          let goalNewGoals ← linearizeGoal currentGoal
          allNewGoals := allNewGoals ++ goalNewGoals
          goalLinearized := true
          -- Goal linearization succeeded, continue to auto-solve side goals
        catch _ =>
          -- Goal linearization failed, continue with hypothesis linearization only
          pure ()

        -- Try to automatically solve side goals
        trace[linearize] "Attempting to auto-solve {allNewGoals.length} side goals"
        let mut remainingSideGoals : List MVarId := []
        for sideGoal in allNewGoals do
          match ← trySolveSideGoal sideGoal with
          | none =>
            trace[linearize] "Successfully auto-solved side goal"
          | some g =>
            trace[linearize] "Could not auto-solve side goal, keeping it"
            remainingSideGoals := remainingSideGoals.append [g]

        -- If goal was linearized, it's been solved, so don't include it
        if goalLinearized then
          replaceMainGoal remainingSideGoals
        else
          replaceMainGoal (currentGoal :: remainingSideGoals)

/-- The linearize tactic syntax -/
syntax (name := linearize) "linearize" (location)? : tactic

/-- Elaboration rule for linearize tactic -/
elab_rules : tactic
  | `(tactic| linearize $[$loc:location]?) => do
    let location := match loc with
    | none => Location.wildcard
    | some loc => expandLocation loc
    linearizeAtLocation location

/-- The linearize! tactic that applies linearize then linarith -/
syntax (name := linearizeBang) "linearize!" (&" only")? (" [" term,* "]")? (location)? : tactic

/-- Elaboration rule for linearize! tactic -/
elab_rules : tactic
  | `(tactic| linearize! $[only%$o]? $[ [ $args,* ] ]? $[$loc:location]?) => do
    let location := match loc with
    | none => Location.wildcard
    | some loc => expandLocation loc
    linearizeAtLocation location
    -- Apply norm_num then linarith to all remaining goals
    let initialGoals ← getGoals
    let mut remainingGoals : List MVarId := []

    for goal in initialGoals do
      if ← goal.isAssigned then
        -- Goal was already solved during linearization
        continue
      else
        try
          setGoals [goal]
          -- First apply norm_num to clean up numerical expressions and casts in hypotheses and goal
          evalTactic (← `(tactic| norm_num at *))
          -- Then apply linarith with the provided arguments
          let linarithCall ← match o, args with
          | some _, some args =>
            `(tactic| linarith only [$args,*])
          | some _, none =>
            `(tactic| linarith only)
          | none, some args =>
            `(tactic| linarith [$args,*])
          | none, none =>
            `(tactic| linarith)
          evalTactic linarithCall
          -- Check if goal was solved
          if ← goal.isAssigned then
            continue  -- Goal was solved, don't add to remaining
          else
            remainingGoals := goal :: remainingGoals
        catch _ =>
          -- If norm_num + linarith fails, try norm_num + omega as a fallback
          try
            setGoals [goal]
            evalTactic (← `(tactic| norm_num at *))
            evalTactic (← `(tactic| omega))
            if ← goal.isAssigned then
              continue  -- Goal was solved by omega
            else
              remainingGoals := goal :: remainingGoals
          catch _ =>
            -- If both linarith and omega fail, keep the goal
            remainingGoals := goal :: remainingGoals

    setGoals remainingGoals.reverse

end Mathlib.Tactic.Linearize
