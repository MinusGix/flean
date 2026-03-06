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

By default, `linearize` acts only on the goal. To target hypotheses, use `linearize at ...`.
To target all hypotheses and the goal, use `linearize at *`.

## Usage

```lean
example (a : ℝ) (h : 1 < a) (h2 : a < (2 : ℝ)^100) : a < (2 : ℝ)^200 := by
  linearize at h2  -- transforms to: Int.log 2 a < 100
  linarith

-- Or use linearize! to automatically apply linarith (with omega fallback)
example (a : ℝ) (h : 1 < a) (h2 : a < (2 : ℝ)^100) : a < (2 : ℝ)^200 := by
  linearize! at h2  -- transforms and applies linarith automatically

-- linearize! also supports passing additional lemmas to linarith
example (a : ℝ) (h : 1 < a) (h2 : a < (2 : ℝ)^5) (extra : Int.log 2 a ≥ 2) :
    Int.log 2 a ≤ 4 := by
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
    -- For nat literals: produce @OfNat.ofNat ℤ n _ (the canonical ℤ literal).
    -- For nat variables: produce @Nat.cast ℤ _ N (matches how omega coerces hyps).
    -- Using the wrong form causes omega proof construction to fail with type mismatches.
    match (e : Expr).getAppFnArgs with
    | (``OfNat.ofNat, #[_, nRaw, _]) =>
      match nRaw.rawNatLit? with
      | some _ =>
        let instType := mkApp2 (mkConst ``OfNat [.zero]) q(ℤ) nRaw
        let inst ← synthInstance instType
        pure (mkApp3 (mkConst ``OfNat.ofNat [.zero]) q(ℤ) nRaw inst)
      | none =>
        let _inst ← synthInstanceQ q(NatCast ℤ)
        pure q(($e : ℤ))
    | _ =>
      let _inst ← synthInstanceQ q(NatCast ℤ)
      pure q(($e : ℤ))
  else
    pure e

def asR {u : Level} (R : Q(Type u)) (e : Expr) (_inst : Q(NatCast $R)) : MetaM Q($R) := do
  let eType ← inferType e
  if eType.isAppOf ``Nat then
    have e : Q(ℕ) := e
    match e with
    | .lit (.natVal n) =>
      -- @OfNat.ofNat ℝ 2 instOfNatAtLeastTwo : ℝ
      let inst : Q(OfNat $R $n) := ← synthInstanceQ (q(OfNat $R $n))
      pure q(@OfNat.ofNat $R $n $inst)
    | _ =>
      throwError "Expected a natural number literal"
  else
    -- TODO: smarter casting
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

/-- Try a sequence of tactics to solve a side goal.
    Tries: assumption → norm_num → omega → linarith, returning `none` if any succeeds. -/
private def trySideGoalTactics (g : MVarId) (skipAssumption : Bool := false) :
    TacticM (Option MVarId) := do
  let savedGoals ← getGoals
  -- Try each tactic: assumption, omega, exact_mod_cast, norm_num, positivity, linarith
  for (name, stx) in [
    ("assumption",      ← `(tactic| assumption)),
    ("omega",           ← `(tactic| omega)),
    ("exact_mod_cast",  ← `(tactic| exact_mod_cast (by omega))),
    ("norm_num",        ← `(tactic| norm_num)),
    ("positivity",      ← `(tactic| positivity)),
    ("linarith",        ← `(tactic| linarith))
  ] do
    if skipAssumption && name == "assumption" then continue
    let saved ← saveState
    try
      setGoals [g]
      evalTactic stx
      if (← getGoals).isEmpty then
        trace[linearize] "Side goal solved by {name}"
        setGoals savedGoals
        return none
      restoreState saved
    catch _ =>
      restoreState saved
  setGoals savedGoals
  trace[linearize] "All side goal tactics failed"
  return some g

/-- Try to solve an LT side goal of the form `lhs < rhs` -/
def solveLTSideGoal (g : MVarId) (lhs _rhs : Expr) : TacticM (Option MVarId) := do
  if isLiteralOne lhs then
    trace[linearize] "Detected 1 < b pattern"
    trySideGoalTactics g (skipAssumption := true)
  else
    trace[linearize] "Detected 0 < a pattern"
    trySideGoalTactics g

/-- Try to solve an LE side goal of the form `lhs ≤ rhs` -/
def solveLESideGoal (g : MVarId) (lhs _rhs : Expr) : TacticM (Option MVarId) := do
  if isLiteralOne lhs then
    trace[linearize] "Detected 1 ≤ b pattern"
    trySideGoalTactics g (skipAssumption := true)
  else
    trace[linearize] "Detected 0 ≤ a pattern"
    trySideGoalTactics g

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
      trace[linearize] "Detected ≠ pattern"
      -- Try zpow_ne_zero (a^n ≠ 0)
      let zpow_solved ← observing? do
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``zpow_ne_zero)
        setGoals gs
        evalTactic (← `(tactic| first | norm_num | assumption))
        let remaining ← getGoals
        if !remaining.isEmpty then throwError "zpow_ne_zero side goals remain"
      if zpow_solved.isSome then
        trace[linearize] "Solved with zpow_ne_zero"
        return none
      -- Try Ne.symm + zpow_ne_zero (0 ≠ a^n)
      let zpow_symm_solved ← observing? do
        let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``Ne.symm)
          | throwError "Ne.symm failed"
        let gs ← g'.apply (← mkConstWithFreshMVarLevels ``zpow_ne_zero)
        setGoals gs
        evalTactic (← `(tactic| first | norm_num | assumption))
        let remaining ← getGoals
        if !remaining.isEmpty then throwError "zpow_ne_zero side goals remain"
      if zpow_symm_solved.isSome then
        trace[linearize] "Solved with Ne.symm + zpow_ne_zero"
        return none
      -- Fall back to generic tactics
      trySideGoalTactics g
    | _ =>
      trace[linearize] "Unknown side goal type"
      trySideGoalTactics g



/-- Unfold local let-bound fvars (from `set`) to their definitions, recursively. -/
partial def unfoldLetFVars (e : Expr) : MetaM Expr := do
  -- First handle the top-level: if it's an fvar with a value, unfold it
  let e ← if e.isFVar then
    let ldecl ← e.fvarId!.getDecl
    if let some val := ldecl.value? then pure val else pure e
  else pure e
  -- Then zeta-reduce any remaining let expressions
  zetaReduce e

/-- Check if an expression is of the form `(b : R)^z` where `b` is a natural number literal -/
def isNatCastZpow (e : Expr) : MetaM (Option (ℕ × Expr × Expr × Expr)) := do
  trace[linearize] "isNatCastZpow checking: {e}"
  trace[linearize] "  Expression kind: {e.ctorName}"

  -- Unfold let bindings (from `set`) and instantiate metavariables
  let e' ← do
    let e ← unfoldLetFVars e
    if e.isMVar then
      trace[linearize] "  Expression is mvar, attempting to instantiate"
      instantiateMVars e
    else
      pure e

  let appInfo := e'.getAppFnArgs
  trace[linearize] "  getAppFnArgs function: {appInfo.1}"
  trace[linearize] "  getAppFnArgs #args: {appInfo.2.size}"
  match appInfo with
  | (``HPow.hPow, #[_, _, _, _, base, exponent]) =>
    trace[linearize] "Found HPow.hPow with base: {base}, exponent: {exponent}"
    -- Check if base is a natural number cast
    let baseAppInfo := base.getAppFnArgs
    trace[linearize] "Base getAppFnArgs: {baseAppInfo}"
    match baseAppInfo with
    | (``Nat.cast, #[R, _, natExpr]) =>
      trace[linearize] "Found Nat.cast base with natExpr: {natExpr}"
      -- Try to extract the natural number value
      if let some n := natExpr.rawNatLit? then
        trace[linearize] "Found natural number: {n}"
        return some (n, base, exponent, R)
      else
        trace[linearize] "No natural number found in Nat.cast"
        return none
    | (``OfNat.ofNat, #[R, natExpr, _]) =>
      trace[linearize] "Found OfNat.ofNat base with natExpr: {natExpr}"
      -- Try to extract the natural number value
      if let some n := natExpr.rawNatLit? then
        trace[linearize] "Found natural number: {n}"
        return some (n, base, exponent, R)
      else
        trace[linearize] "No natural number found in OfNat.ofNat"
        return none
    | (fn, args) =>
      trace[linearize] "Base is not Nat.cast or OfNat.ofNat, fn: {fn}, args: {args}"
      -- Sometimes the base might be wrapped differently, let's try to unfold it
      let baseUnfolded ← whnf base
      trace[linearize] "Trying with unfolded base: {baseUnfolded}"
      match baseUnfolded.getAppFnArgs with
      | (``OfNat.ofNat, #[R, natExpr, _]) =>
        trace[linearize] "Found OfNat.ofNat after unfolding with natExpr: {natExpr}"
        if let some n := natExpr.rawNatLit? then
          trace[linearize] "Found natural number after unfolding: {n}"
          return some (n, base, exponent, R)
        else
          return none
      | _ =>
        -- Check if the unfolded expression is an application ending with a natural literal
        -- This handles cases like `inst.toDivisionRing.toAddGroupWithOne.toNatCast.1 2`
        let rec findNatLit (e : Expr) : Option ℕ :=
          match e with
          | .lit (.natVal n) => some n
          | .app _f a => findNatLit a
          | _ => none

        if let some n := findNatLit baseUnfolded then
          trace[linearize] "Found nat value in unfolded base: {n}"
          if n ≥ 2 then  -- Only handle bases ≥ 2 for logarithms
            -- Need to infer the target type R from the original expression
            let baseType ← inferType base
            return some (n, base, exponent, baseType)
          else
            return none
        else
          trace[linearize] "Still not recognized after unfolding: {baseUnfolded}"
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

/-- Check if an expression is `expectedBase ^ exp` (via HPow or Pow), returning the exponent.
    Uses `isDefEq` to match the base, so it works with arbitrary expressions. -/
def isExprPow (expectedBase : Expr) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← unfoldLetFVars e
  match e.getAppFnArgs with
  | (``HPow.hPow, #[_, _, _, _, base, exponent]) =>
    if (← isDefEq base expectedBase) then
      return some (base, exponent)
    else
      return none
  | (``Pow.pow, #[_, _, _, base, exponent]) =>
    if (← isDefEq base expectedBase) then
      return some (base, exponent)
    else
      return none
  | _ => return none

/-- Linearize a goal of the form `base^m cmp base^n` for an arbitrary base expression.
    Returns side goals for the base condition and exponent comparison. -/
def linearizeBaseGoal (g : MVarId) (baseStx : Expr) : TacticM (List MVarId) := do
  g.withContext do
    let goalType ← g.getType
    match goalType.getAppFnArgs with
    | (``LE.le, #[_, _, lhs, rhs]) =>
      if let some (baseLhs, expLhs) ← isExprPow baseStx lhs then
        if let some (_baseRhs, expRhs) ← isExprPow baseStx rhs then
          let ⟨_, R, _⟩ ← inferTypeQ' lhs
          let expType ← inferType expLhs
          if expType.isConstOf ``Nat then
            -- ℕ exponents: pow_le_pow_right₀
            have expLhs : Q(ℕ) := expLhs
            have expRhs : Q(ℕ) := expRhs
            have baseExpr : Q($R) := baseLhs
            let _inst1 ← synthInstanceQ q(MonoidWithZero $R)
            let _inst2 ← synthInstanceQ q(Preorder $R)
            let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
            let _inst4 ← synthInstanceQ q(PosMulMono $R)
            assumeInstancesCommute
            let haGoal ← mkFreshExprMVarQ q((1 : $R) ≤ $baseExpr) MetavarKind.syntheticOpaque (`ha)
            let hmnGoal ← mkFreshExprMVarQ q($expLhs ≤ $expRhs) MetavarKind.syntheticOpaque (`hmn)
            g.assign q(pow_le_pow_right₀ $haGoal $hmnGoal)
            Term.synthesizeSyntheticMVarsUsingDefault
            return [haGoal.mvarId!, hmnGoal.mvarId!]
          else
            -- ℤ exponents: zpow_le_zpow_right₀
            let expLhs : Q(ℤ) ← asInt expLhs
            let expRhs : Q(ℤ) ← asInt expRhs
            have baseExpr : Q($R) := baseLhs
            let _inst1 ← synthInstanceQ q(DivisionRing $R)
            let _inst2 ← synthInstanceQ q(LinearOrder $R)
            let _inst3 ← synthInstanceQ q(PosMulReflectLE $R)
            let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
            assumeInstancesCommute
            let haGoal ← mkFreshExprMVarQ q((1 : $R) ≤ $baseExpr) MetavarKind.syntheticOpaque (`ha)
            let hmnGoal ← mkFreshExprMVarQ q($expLhs ≤ $expRhs) MetavarKind.syntheticOpaque (`hmn)
            g.assign q(zpow_le_zpow_right₀ $haGoal $hmnGoal)
            Term.synthesizeSyntheticMVarsUsingDefault
            return [haGoal.mvarId!, hmnGoal.mvarId!]
        else throwError "linearize (base := ...): RHS is not a power of the given base"
      else throwError "linearize (base := ...): LHS is not a power of the given base"
    | (``LT.lt, #[_, _, lhs, rhs]) =>
      if let some (baseLhs, expLhs) ← isExprPow baseStx lhs then
        if let some (_baseRhs, expRhs) ← isExprPow baseStx rhs then
          let ⟨_, R, _⟩ ← inferTypeQ' lhs
          let expType ← inferType expLhs
          if expType.isConstOf ``Nat then
            -- ℕ exponents: pow_lt_pow_right₀
            have expLhs : Q(ℕ) := expLhs
            have expRhs : Q(ℕ) := expRhs
            have baseExpr : Q($R) := baseLhs
            let _inst1 ← synthInstanceQ q(MonoidWithZero $R)
            let _inst2 ← synthInstanceQ q(PartialOrder $R)
            let _inst3 ← synthInstanceQ q(PosMulStrictMono $R)
            let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
            assumeInstancesCommute
            let haGoal ← mkFreshExprMVarQ q((1 : $R) < $baseExpr) MetavarKind.syntheticOpaque (`ha)
            let hmnGoal ← mkFreshExprMVarQ q($expLhs < $expRhs) MetavarKind.syntheticOpaque (`hmn)
            g.assign q(pow_lt_pow_right₀ $haGoal $hmnGoal)
            Term.synthesizeSyntheticMVarsUsingDefault
            return [haGoal.mvarId!, hmnGoal.mvarId!]
          else
            -- ℤ exponents: zpow_lt_zpow_right₀
            let expLhs : Q(ℤ) ← asInt expLhs
            let expRhs : Q(ℤ) ← asInt expRhs
            have baseExpr : Q($R) := baseLhs
            let _inst1 ← synthInstanceQ q(DivisionRing $R)
            let _inst2 ← synthInstanceQ q(LinearOrder $R)
            let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
            let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
            assumeInstancesCommute
            let haGoal ← mkFreshExprMVarQ q((1 : $R) < $baseExpr) MetavarKind.syntheticOpaque (`ha)
            let hmnGoal ← mkFreshExprMVarQ q($expLhs < $expRhs) MetavarKind.syntheticOpaque (`hmn)
            g.assign q(zpow_lt_zpow_right₀ $haGoal $hmnGoal)
            Term.synthesizeSyntheticMVarsUsingDefault
            return [haGoal.mvarId!, hmnGoal.mvarId!]
        else throwError "linearize (base := ...): RHS is not a power of the given base"
      else throwError "linearize (base := ...): LHS is not a power of the given base"
    | _ => throwError "linearize (base := ...): goal is not ≤ or <"

/-- Check if an expression is `a / b`, returning (a, b). -/
def isDiv (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← unfoldLetFVars e
  match e.getAppFnArgs with
  | (``HDiv.hDiv, #[_, _, _, _, num, den]) => return some (num, den)
  | _ => return none

/-- Check if an expression is `base^exp` for any recognized base (literal or arbitrary).
    Returns (base, exponent) if it's any kind of power expression. -/
def isAnyPow (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← unfoldLetFVars e
  match e.getAppFnArgs with
  | (``HPow.hPow, #[_, _, _, _, base, exponent]) => return some (base, exponent)
  | (``Pow.pow, #[_, _, _, base, exponent]) => return some (base, exponent)
  | _ => return none

/-- Linearize a goal of the form `c / base^m ≤ c / base^n` (reciprocal monotonicity).
    Reduces to `base^n ≤ base^m` (flipped) + `0 ≤ c` + `0 < base^n`.
    Also handles `<` variant. Uses `apply` to let Lean handle instance resolution. -/
def linearizeRecipGoal (g : MVarId) : TacticM (List MVarId) := do
  g.withContext do
    let goalType ← g.getType
    match goalType.getAppFnArgs with
    | (``LE.le, #[_, _, lhs, rhs]) =>
      let some (numL, denL) ← isDiv lhs | throwError "linearize: LHS is not a division"
      let some (numR, denR) ← isDiv rhs | throwError "linearize: RHS is not a division"
      unless (← isDefEq numL numR) do
        throwError "linearize: numerators don't match in reciprocal pattern"
      let some (baseL, _) ← isAnyPow denL | throwError "linearize: LHS denominator is not a power"
      let some (baseR, _) ← isAnyPow denR | throwError "linearize: RHS denominator is not a power"
      unless (← isDefEq baseL baseR) do
        throwError "linearize: bases don't match in reciprocal pattern"
      -- Apply div_le_div_of_nonneg_left via `apply`, let Lean resolve instances
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``div_le_div_of_nonneg_left)
      return gs
    | (``LT.lt, #[_, _, lhs, rhs]) =>
      let some (numL, denL) ← isDiv lhs | throwError "linearize: LHS is not a division"
      let some (numR, denR) ← isDiv rhs | throwError "linearize: RHS is not a division"
      unless (← isDefEq numL numR) do
        throwError "linearize: numerators don't match in reciprocal pattern"
      let some (baseL, _) ← isAnyPow denL | throwError "linearize: LHS denominator is not a power"
      let some (baseR, _) ← isAnyPow denR | throwError "linearize: RHS denominator is not a power"
      unless (← isDefEq baseL baseR) do
        throwError "linearize: bases don't match in reciprocal pattern"
      -- Apply div_lt_div_of_pos_left via `apply`, let Lean resolve instances
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``div_lt_div_of_pos_left)
      return gs
    | _ => throwError "linearize: reciprocal pattern only supports ≤ and <"

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
        -- Check if both sides have the same base: a^m < a^n  m < n (when 1 < a)
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
        -- lhs < (b : R)^exp  Int.log b lhs < exp (when 0 < lhs, 1 < b)
        have b : Q(ℕ) := mkNatLit b_rhs
        have logExpr : Q(ℤ) := q(Int.log $b $lhs)
        let intExp ← asInt exp_rhs
        pure (some q($logExpr < $intExp))
    else if let some (b, _, exp, _) ← isNatCastZpow lhs then
      -- Skip linearization if rhs is 0 (since Int.log b 0 doesn't make sense)
      if isLiteralZero rhs then
        return none
      -- (b : R)^exp < rhs  exp < Int.log b rhs + 1 (when 0 < rhs, 1 < b)
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
      let expType ← inferType exp
      if (← isDefEq expType q(ℕ)) then
        -- Natural exponent: use pow_pos
        trace[linearize] "Applying pow_pos for base {b}"
        let ⟨_, R, _⟩ ← inferTypeQ' rhs
        have expNat : Q(ℕ) := exp
        have a : Q(ℕ) := mkNatLit b

        -- Need instances for pow_pos
        let _inst1 ← synthInstanceQ q(MonoidWithZero $R)
        let _inst2 ← synthInstanceQ q(PartialOrder $R)
        let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
        let _inst4 ← synthInstanceQ q(PosMulStrictMono $R)
        let _inst5 ← synthInstanceQ q(NatCast $R)

        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(0 < ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        have thmProof : Q((0 : $R) < ($a : $R) ^ $expNat) := q(pow_pos $haGoal $expNat)
        g.assign thmProof
        Term.synthesizeSyntheticMVarsUsingDefault
        return [haGoal.mvarId!]
      else
        -- Integer exponent: use zpow_pos
        trace[linearize] "Applying zpow_pos for base {b}"
        let ⟨_, R, _⟩ ← inferTypeQ' rhs
        let expInt : Q(ℤ) ← asInt exp
        have a : Q(ℕ) := mkNatLit b

        -- Need instances for zpow_pos
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(PartialOrder $R)
        let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
        let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(0 < ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        have thmProof : Q((0 : $R) < ($a : $R) ^ $expInt) := q(zpow_pos $haGoal $expInt)
        g.assign thmProof
        Term.synthesizeSyntheticMVarsUsingDefault
        return [haGoal.mvarId!]
    else
      throwError "linearize: goal linearization for 0 < ... only supports zpow expressions"
  else if let some (b_rhs, base_rhs, exp_rhs, _) ← isNatCastZpow rhs then
    trace[linearize] "  Pattern: LHS not literal, but RHS is zpow"
    if let some (b_lhs, _base_lhs, exp_lhs, _) ← isNatCastZpow lhs then
      -- Both sides are zpow with same base: a^m < a^n ↔ m < n (when 1 < a)
      if b_lhs == b_rhs then
        let ⟨_, R, _⟩ ← inferTypeQ' lhs

        -- Check if exponents are ℕ (pow) or need ℤ casting (zpow)
        let expType_lhs ← inferType exp_lhs
        if expType_lhs.isConstOf ``Nat then do
          -- ℕ exponents: use pow_lt_pow_right₀
          trace[linearize] "Applying pow_lt_pow_right₀ for ℕ exponents, base {b_lhs}"
          have exp_lhs : Q(ℕ) := exp_lhs
          have exp_rhs : Q(ℕ) := exp_rhs
          have baseExpr : Q($R) := base_rhs

          let _inst1 ← synthInstanceQ q(MonoidWithZero $R)
          let _inst2 ← synthInstanceQ q(PartialOrder $R)
          let _inst3 ← synthInstanceQ q(PosMulStrictMono $R)
          let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
          assumeInstancesCommute

          let haGoal ← mkFreshExprMVarQ q((1 : $R) < $baseExpr) MetavarKind.syntheticOpaque (`ha)
          let hmnGoal ← mkFreshExprMVarQ q($exp_lhs < $exp_rhs) MetavarKind.syntheticOpaque (`hmn)
          g.assign q(pow_lt_pow_right₀ $haGoal $hmnGoal)
          Term.synthesizeSyntheticMVarsUsingDefault
          return [haGoal.mvarId!, hmnGoal.mvarId!]
        else
          -- ℤ exponents: use zpow_lt_zpow_right₀
          trace[linearize] "Applying zpow_lt_zpow_right₀ for ℤ exponents, base {b_lhs}"
          let exp_lhs : Q(ℤ) ← asInt exp_lhs
          let exp_rhs : Q(ℤ) ← asInt exp_rhs
          have a : Q(ℕ) := mkNatLit b_lhs

          let _inst1 ← synthInstanceQ q(DivisionRing $R)
          let _inst2 ← synthInstanceQ q(LinearOrder $R)
          let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
          let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
          assumeInstancesCommute

          let haGoal ← mkFreshExprMVarQ q(1 < ($a : $R)) MetavarKind.syntheticOpaque (`ha)
          let hmnGoal ← mkFreshExprMVarQ q($exp_lhs < $exp_rhs) MetavarKind.syntheticOpaque (`hmn)

          have thmProof : Q(($a : $R) ^ $exp_lhs < ($a : $R) ^ $exp_rhs) := q(zpow_lt_zpow_right₀ $haGoal $hmnGoal)
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
  trace[linearize] "linearizeLEGoal: lhs={lhs}, rhs={rhs}"

  -- Check for pattern 0 ≤ a^n using zpow_nonneg
  if isLiteralZero lhs then
    trace[linearize] "  Pattern: 0 ≤ a^n"
    if let some (b, bExpr, exp, _) ← isNatCastZpow rhs then
      let expType ← inferType exp
      if (← isDefEq expType q(ℕ)) then
        -- Natural exponent: use pow_nonneg
        trace[linearize] "Applying pow_nonneg for base {b}"
        let ⟨_, R, _⟩ ← inferTypeQ' rhs
        have expNat : Q(ℕ) := exp
        have a : Q(ℕ) := mkNatLit b

        -- Need instances for pow_nonneg
        let _inst1 ← synthInstanceQ q(MonoidWithZero $R)
        let _inst2 ← synthInstanceQ q(Preorder $R)
        let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
        let _inst4 ← synthInstanceQ q(PosMulMono $R)
        let _inst5 ← synthInstanceQ q(NatCast $R)
        assumeInstancesCommute

        let haGoal ← mkFreshExprMVarQ q(0 ≤ ($a : $R)) MetavarKind.syntheticOpaque (`ha)
        have thmProof : Q((0 : $R) ≤ ($a : $R) ^ $expNat) := q(pow_nonneg $haGoal $expNat)
        g.assign thmProof
        Term.synthesizeSyntheticMVarsUsingDefault
        return [haGoal.mvarId!]
      else
        -- Integer exponent: use zpow_nonneg
        trace[linearize] "Applying zpow_nonneg for base {b}"
        let ⟨_, R, _⟩ ← inferTypeQ' rhs
        let _inst1 ← synthInstanceQ q(GroupWithZero $R)
        let _inst2 ← synthInstanceQ q(PartialOrder $R)
        let _inst3 ← synthInstanceQ q(PosMulReflectLT $R)
        let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
        let _inst5 ← synthInstanceQ q(NatCast $R)
        assumeInstancesCommute


        let expInt : Q(ℤ) ← asInt exp
        -- have a : Q(ℕ) := mkNatLit b
        have bExpr : Q($R) := ← asR R bExpr _inst5

        trace[linearize] "b={b}"
        trace[linearize] "exp={exp}"
        trace[linearize] "R={R}"
        trace[linearize] "expInt={expInt}"
        trace[linearize] "bExpr={bExpr}"

        -- Need instances for zpow_nonneg
        -- let _inst1 ← synthInstanceQ q(DivisionRing $R)
        -- let _inst2 ← synthInstanceQ q(LinearOrder $R)
        -- let _inst3 ← synthInstanceQ q(PosMulReflectLE $R)
        -- let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
        -- [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀]

        let haGoal ← mkFreshExprMVarQ q(0 ≤ $bExpr) MetavarKind.syntheticOpaque (`ha)
        have thmProof : Q(0 ≤ $bExpr ^ $expInt) := q(zpow_nonneg $haGoal $expInt)
        g.assign thmProof
        Term.synthesizeSyntheticMVarsUsingDefault
        return [haGoal.mvarId!]
    else
      throwError "linearize: goal linearization for 0 ≤ ... only supports power expressions"
  -- Check for pattern 1 ≤ a^n using one_le_zpow₀
  else if isLiteralOne lhs then
    if let some (b, bExpr, exp, _) ← isNatCastZpow rhs then
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

        -- Need instances for one_le_zpow₀
        let _inst1 ← synthInstanceQ q(DivisionRing $R)
        let _inst2 ← synthInstanceQ q(PartialOrder $R)
        let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
        let _inst4 ← synthInstanceQ q(PosMulReflectLT $R)
        let _inst5 ← synthInstanceQ q(NatCast $R)
        assumeInstancesCommute

        let expInt : Q(ℤ) ← asInt exp
        -- have a : Q(ℕ) := mkNatLit b
        have bExpr : Q($R) := ← asR R bExpr _inst5


        let haGoal ← mkFreshExprMVarQ q(1 ≤ $bExpr) MetavarKind.syntheticOpaque (`ha)
        let hnGoal ← mkFreshExprMVarQ q(0 ≤ $expInt) MetavarKind.syntheticOpaque (`hn)

        have thmProof : Q((1 : $R) ≤ $bExpr ^ $expInt) := q(one_le_zpow₀ $haGoal $hnGoal)

        -- Apply the theorem to reduce the goal
        g.assign thmProof

        Term.synthesizeSyntheticMVarsUsingDefault

        return [haGoal.mvarId!, hnGoal.mvarId!]
    else
      throwError "linearize: goal linearization for 1 ≤ ... only supports power expressions with natural base"
  else if let some (b_rhs, base_rhs, exp_rhs, _) ← isNatCastZpow rhs then
    if let some (b_lhs, _base_lhs, exp_lhs, _) ← isNatCastZpow lhs then
      -- Both sides are zpow with same base: a^m ≤ a^n ↔ m ≤ n (when 1 ≤ a)
      if b_lhs == b_rhs then
        let ⟨_, R, _⟩ ← inferTypeQ' lhs

        -- Check if exponents are ℕ (pow) or need ℤ casting (zpow)
        let expType_lhs ← inferType exp_lhs
        if expType_lhs.isConstOf ``Nat then do
          -- ℕ exponents: use pow_le_pow_right₀
          trace[linearize] "Applying pow_le_pow_right₀ for ℕ exponents, base {b_lhs}"
          have exp_lhs : Q(ℕ) := exp_lhs
          have exp_rhs : Q(ℕ) := exp_rhs
          have baseExpr : Q($R) := base_rhs

          let _inst1 ← synthInstanceQ q(MonoidWithZero $R)
          let _inst2 ← synthInstanceQ q(Preorder $R)
          let _inst3 ← synthInstanceQ q(ZeroLEOneClass $R)
          let _inst4 ← synthInstanceQ q(PosMulMono $R)
          assumeInstancesCommute

          let haGoal ← mkFreshExprMVarQ q((1 : $R) ≤ $baseExpr) MetavarKind.syntheticOpaque (`ha)
          let hmnGoal ← mkFreshExprMVarQ q($exp_lhs ≤ $exp_rhs) MetavarKind.syntheticOpaque (`hmn)
          g.assign q(pow_le_pow_right₀ $haGoal $hmnGoal)
          Term.synthesizeSyntheticMVarsUsingDefault
          return [haGoal.mvarId!, hmnGoal.mvarId!]
        else
          -- ℤ exponents: use zpow_le_zpow_right₀
          trace[linearize] "Applying zpow_le_zpow_right₀ for ℤ exponents, base {b_lhs}"
          let exp_lhs : Q(ℤ) ← asInt exp_lhs
          let exp_rhs : Q(ℤ) ← asInt exp_rhs
          have a : Q(ℕ) := mkNatLit b_lhs

          let _inst1 ← synthInstanceQ q(DivisionRing $R)
          let _inst2 ← synthInstanceQ q(LinearOrder $R)
          let _inst3 ← synthInstanceQ q(PosMulReflectLE $R)
          let _inst4 ← synthInstanceQ q(ZeroLEOneClass $R)
          assumeInstancesCommute

          let haGoal ← mkFreshExprMVarQ q(1 ≤ ($a : $R)) MetavarKind.syntheticOpaque (`ha)
          let hmnGoal ← mkFreshExprMVarQ q($exp_lhs ≤ $exp_rhs) MetavarKind.syntheticOpaque (`hmn)

          have thmProof : Q(($a : $R) ^ $exp_lhs ≤ ($a : $R) ^ $exp_rhs) := q(zpow_le_zpow_right₀ $haGoal $hmnGoal)
          g.assign thmProof
          Term.synthesizeSyntheticMVarsUsingDefault
          return [haGoal.mvarId!, hmnGoal.mvarId!]
      else
        throwError "linearize: different bases not supported"
    else
      throwError "linearize: goal linearization only supports same-base zpow comparisons"
  else
    throwError "linearize: goal linearization only supports same-base zpow comparisons"

/-- Linearize NE goals of the form `a^n ≠ 0` -/
def linearizeNEGoal (g : MVarId) (lhs rhs : Expr) : TacticM (List MVarId) := do
  trace[linearize] "linearizeNEGoal: lhs={lhs}, rhs={rhs}"

  -- Helper function to handle the core logic of applying zpow_ne_zero
  let handle_zpow_ne_zero (zpow_expr : Expr) (g : MVarId) : TacticM (List MVarId) := do
    if let some (b, _, exp, _) ← isNatCastZpow zpow_expr then
      trace[linearize] "Applying zpow_ne_zero for base {b}"
      let ⟨_, R, _⟩ ← inferTypeQ' zpow_expr
      let exp : Q(ℤ) ← asInt exp
      have a : Q(ℕ) := mkNatLit b

      -- Need instance for zpow_ne_zero
      -- let _inst1 ← synthInstanceQ q(GroupWithZero $R)
      let _inst1 ← synthInstanceQ q(DivisionRing $R)
      let _inst2 ← synthInstanceQ q(LinearOrder $R)
      assumeInstancesCommute

      let haGoal ← mkFreshExprMVarQ q(($a : $R) ≠ 0) MetavarKind.syntheticOpaque (`ha)
      have thmProof : Q(($a : $R) ^ $exp ≠ 0) := q(zpow_ne_zero $exp $haGoal)
      g.assign thmProof
      Term.synthesizeSyntheticMVarsUsingDefault
      return [haGoal.mvarId!]
    else
      throwError "linearize: goal linearization for ... ≠ 0 only supports zpow expressions"

  -- Case 1: a^n ≠ 0
  if isLiteralZero rhs then
    handle_zpow_ne_zero lhs g
  -- Case 2: 0 ≠ a^n
  else if isLiteralZero lhs then
    -- Apply symmetry to turn `0 ≠ a^n` into `a^n ≠ 0`
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``Ne.symm) | throwError "Ne.symm produced more/less than one goal"
    handle_zpow_ne_zero rhs g'
  else
    throwError "linearize: goal linearization for ≠ only supports comparisons with 0"

/-- Try direct power linearization, then reciprocal as fallback -/
def linearizeGoalCore (g : MVarId) : TacticM (List MVarId) := do
  g.withContext do
    let goalType ← instantiateMVars (← g.getType)
    trace[linearize] "=== ENTERING linearizeGoal ==="
    trace[linearize] "Analyzing goal: {goalType}"

    let (fn, args) := goalType.getAppFnArgs
    trace[linearize] "  Goal app function: {fn}"
    trace[linearize] "  Goal app args count: {args.size}"

    -- Try reducing the goal type first
    let goalTypeReduced ← whnf goalType

    -- Dispatch to specialized handlers based on comparison type
    -- First try the original goal type (works for most cases)
    match goalType.getAppFnArgs with
    | (``LT.lt, #[_, _, lhs, rhs]) =>
      linearizeLTGoal g lhs rhs
    | (``LE.le, #[_, _, lhs, rhs]) =>
      linearizeLEGoal g lhs rhs
    | (``Ne, #[_, lhs, rhs]) =>
      linearizeNEGoal g lhs rhs
    | _ =>
      -- If original doesn't work, try the reduced version (for mvar cases)
      trace[linearize] "  Original pattern didn't match, trying reduced goal"
      let (fnReduced, argsReduced) := goalTypeReduced.getAppFnArgs
      trace[linearize] "  Reduced app function: {fnReduced}, args: {argsReduced.size}"
      match goalTypeReduced.getAppFnArgs with
      | (``LT.lt, #[_, _, lhs, rhs]) =>
        linearizeLTGoal g lhs rhs
      | (``LE.le, #[_, _, lhs, rhs]) =>
        linearizeLEGoal g lhs rhs
      | (``Ne, #[_, lhs, rhs]) =>
        linearizeNEGoal g lhs rhs
      | (_, #[lhs, rhs]) =>
        if goalTypeReduced.isApp then
          let actualFn := goalTypeReduced.getAppFn
          if actualFn.constName? == some ``LT.lt then
            linearizeLTGoal g lhs rhs
          else if actualFn.constName? == some ``LE.le then
            linearizeLEGoal g lhs rhs
          else
            match actualFn with
            | .proj typeName _ _ =>
              if typeName == ``LT || typeName.toString.endsWith "LT" then
                linearizeLTGoal g lhs rhs
              else if typeName == ``LE || typeName.toString.endsWith "LE" then
                linearizeLEGoal g lhs rhs
              else
                throwError "linearize: goal not a power comparison"
            | _ => throwError "linearize: goal not a power comparison"
        else throwError "linearize: goal not a power comparison"
      | _ => throwError "linearize: goal not a power comparison"

/-- Try to solve a side goal, including recursive linearization for power comparisons.
    This extends `trySolveSideGoal` with the ability to decompose `base^n ≤ base^m`
    side goals that arise from reciprocal linearization. -/
def trySolveSideGoalDeep (g : MVarId) : TacticM (Option MVarId) := do
  -- First try the basic solver
  match ← trySolveSideGoal g with
  | none => return none
  | some g =>
    -- If basic solver failed, try recursive linearization
    trace[linearize] "trySolveSideGoalDeep: trying linearizeGoalCore on side goal"
    let saved ← saveState
    try
      let subGoals ← linearizeGoalCore g
      -- Try to solve all sub-goals
      for sg in subGoals do
        match ← trySolveSideGoal sg with
        | none => pure ()
        | some _ =>
          restoreState saved
          return some g
      return none
    catch _ =>
      restoreState saved
      return some g

/-- Apply linearization to a goal. Tries direct power patterns first,
    then reciprocal `c / base^m ≤ c / base^n` as fallback.
    For reciprocal, recursively linearizes the `base^n ≤ base^m` side goal. -/
def linearizeGoal (g : MVarId) : TacticM (List MVarId) := do
  try
    linearizeGoalCore g
  catch e₁ =>
    -- Try reciprocal recognition as fallback
    trace[linearize] "Direct power linearization failed, trying reciprocal pattern"
    try
      let sideGoals ← linearizeRecipGoal g
      -- Try to recursively solve side goals (especially power comparisons)
      let mut remaining : List MVarId := []
      for sg in sideGoals do
        match ← trySolveSideGoalDeep sg with
        | none => pure ()
        | some sg' => remaining := remaining ++ [sg']
      return remaining
    catch _ =>
      throw e₁  -- Rethrow the original error if reciprocal also fails

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

/-- Helper: run linearizeBaseGoal and solve side goals, replacing main goal -/
def linearizeBaseAtGoal (baseExpr : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let newGoals ← linearizeBaseGoal g baseExpr
  let mut remainingSideGoals : List MVarId := []
  for sideGoal in newGoals do
    match ← trySolveSideGoal sideGoal with
    | none => pure ()
    | some g => remainingSideGoals := remainingSideGoals ++ [g]
  replaceMainGoal remainingSideGoals

/-- The linearize tactic syntax -/
syntax (name := linearize) "linearize" ("(base" ":=" term ")")? (location)? : tactic

/-- Elaboration rule for linearize tactic -/
elab_rules : tactic
  | `(tactic| linearize $[(base := $base)]? $[$loc:location]?) => do
    if let some baseTerm := base then
      let baseExpr ← Tactic.elabTerm baseTerm none
      linearizeBaseAtGoal baseExpr
    else
      let location := match loc with
      | none => Location.targets #[] true
      | some loc => expandLocation loc
      linearizeAtLocation location

/-- The linearize! tactic that applies linearize then linarith -/
syntax (name := linearizeBang) "linearize!" ("(base" ":=" term ")")? (&" only")? (" [" term,* "]")? (location)? : tactic

/-- Elaboration rule for linearize! tactic -/
elab_rules : tactic
  | `(tactic| linearize! $[(base := $base)]? $[only%$o]? $[ [ $args,* ] ]? $[$loc:location]?) => do
    if let some baseTerm := base then
      let baseExpr ← Tactic.elabTerm baseTerm none
      linearizeBaseAtGoal baseExpr
    else
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
