import Mathlib.Data.Int.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.TryThis

/-!
# Linearize Tactic

The `linearize` tactic transforms exponential inequalities of the form `a < (b : R)^z`
(where `b` is a natural number base, `z` is an integer exponent, and `R` is a linear ordered field)
into logarithmic form using `Int.log` to make them suitable for `linarith`.

## Usage

```lean
example (a : ℝ) (h : 1 < a) (h2 : a < (2 : ℝ)^100) : a < (2 : ℝ)^200 := by
  linearize h2  -- transforms to: Int.log 2 a < 100
  linarith
```
-/

namespace Mathlib.Tactic.Linearize

open Lean Elab Meta Tactic Qq

initialize registerTraceClass `linearize

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
    match base.getAppFnArgs with
    | (``Nat.cast, #[R, _, natExpr]) =>
      trace[linearize] "Found Nat.cast base with natExpr: {natExpr}"
      -- Try to extract the natural number value
      if let some n := natExpr.rawNatLit? then
        trace[linearize] "Found natural number: {n}"
        -- Convert natural exponent to integer
        let instNatCast ← synthInstance (mkApp (mkConst ``NatCast []) (mkConst ``Int))
        let intExp ← mkAppM ``Nat.cast #[mkConst ``Int, instNatCast, exponent]
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
        let instNatCast ← synthInstance (mkApp (mkConst ``NatCast []) (mkConst ``Int))
        let intExp ← mkAppM ``Nat.cast #[mkConst ``Int, instNatCast, exponent]
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
def transformZpowComparison (e : Expr) : MetaM (Option Expr) := do
  trace[linearize] "Transforming comparison: {e}"
  match e.getAppFnArgs with
  | (``LT.lt, #[_R, _inst, lhs, rhs]) =>
    -- Case: lhs < rhs
    if let some (b, base, exp, _) ← isNatCastZpow rhs then
      -- lhs < (b : R)^exp � Int.log b lhs < exp (when 0 < lhs, 1 < b)
      let logExpr ← mkAppM ``Int.log #[mkNatLit b, lhs]
      -- Convert exponent to integer if it's a natural number
      let expType ← inferType exp
      let intExp ← if expType.isConstOf ``Nat then
        mkAppM ``Int.ofNat #[exp]
      else
        pure exp
      mkAppM ``LT.lt #[logExpr, intExp]
    else if let some (b, base, exp, _) ← isNatCastZpow lhs then
      -- (b : R)^exp < rhs � exp < Int.log b rhs + 1 (when 0 < rhs, 1 < b)
      let logExpr ← mkAppM ``Int.log #[mkNatLit b, rhs]
      let plusOne ← mkAppM ``HAdd.hAdd #[logExpr, mkIntLit 1]
      -- Convert exponent to integer if it's a natural number
      let expType ← inferType exp
      let intExp ← if expType.isConstOf ``Nat then
        mkAppM ``Int.ofNat #[exp]
      else
        pure exp
      mkAppM ``LT.lt #[intExp, plusOne]
    else
      return none
  | (``LE.le, #[_R, _inst, lhs, rhs]) =>
    -- Similar for d
    if let some (b, base, exp, _) ← isNatCastZpow rhs then
      -- lhs d (b : R)^exp � Int.log b lhs d exp (when 0 < lhs, 1 < b)
      let logExpr ← mkAppM ``Int.log #[mkNatLit b, lhs]
      -- Convert exponent to integer if it's a natural number
      let expType ← inferType exp
      let intExp ← if expType.isConstOf ``Nat then
        mkAppM ``Int.ofNat #[exp]
      else
        pure exp
      mkAppM ``LE.le #[logExpr, intExp]
    else if let some (b, base, exp, _) ← isNatCastZpow lhs then
      -- (b : R)^exp d rhs � exp d Int.log b rhs (when 0 < rhs, 1 < b)
      let logExpr ← mkAppM ``Int.log #[mkNatLit b, rhs]
      -- Convert exponent to integer if it's a natural number
      let expType ← inferType exp
      let intExp ← if expType.isConstOf ``Nat then
        mkAppM ``Int.ofNat #[exp]
      else
        pure exp
      mkAppM ``LE.le #[intExp, logExpr]
    else
      return none
  | _ => return none

/-- Generate a proof that the transformed comparison follows from the original -/
def proveTransformation (original transformed : Expr) : MetaM (Expr × Array Expr) := do
  -- Construct proper proofs using Int.log theorems and return side condition metavariables
  match original.getAppFnArgs, transformed.getAppFnArgs with
  | (``LT.lt, #[R, _, lhs, rhs]), (``LT.lt, #[_, _, logExpr, intExp]) =>
    -- Case: lhs < rhs became Int.log b lhs < intExp  
    -- We need to prove: lhs < b^z → Int.log b lhs < intExp
    if let some (b, base_expr, exp_expr, _) ← isNatCastZpow rhs then
      trace[linearize] "Constructing LT proof for base {b}"
      
      -- Create fresh metavariables for side conditions
      let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
      let zero ← mkAppOptM ``OfNat.ofNat #[R, mkNatLit 0, none]
      let hrType ← mkAppM ``LT.lt #[zero, lhs]
      
      let hbMVar ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque `h_1_lt_b
      let hrMVar ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque `h_0_lt_lhs
      
      -- The proof should directly produce the linearized result
      -- We want: given h_orig : lhs < (b:R)^z, produce: Int.log b lhs < z
      -- This comes from: (Int.lt_zpow_iff_log_lt hb hr).mpr h_orig
      let proof ← do
        trace[linearize] "Building linearization proof for: {original} → {transformed}"
        
        -- Create the proof term: (Int.lt_zpow_iff_log_lt hbMVar hrMVar).mpr
        -- Infer the universe level from the type R
        let lhsType ← inferType lhs
        let rLevel ← match ← inferType lhsType with
          | Expr.sort level => pure level
          | _ => pure levelZero  -- fallback
        let iff_thm := mkAppN (mkConst ``Int.lt_zpow_iff_log_lt [rLevel]) #[hbMVar, hrMVar]
        pure (mkAppN (mkConst ``Iff.mpr) #[iff_thm])
      
      return (proof, #[hbMVar, hrMVar])
    else
      let proof ← mkSorry transformed false
      return (proof, #[])
      
  | (``LE.le, #[R, _, lhs, rhs]), (``LE.le, #[_, _, logExpr, intExp]) =>
    -- Case: lhs ≤ rhs became Int.log b lhs ≤ intExp
    if let some (b, base_expr, exp_expr, _) ← isNatCastZpow rhs then
      trace[linearize] "Constructing LE proof for base {b}"
      
      -- Create fresh metavariables for side conditions
      let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
      let zero ← mkAppOptM ``OfNat.ofNat #[R, mkNatLit 0, none]
      let hrType ← mkAppM ``LT.lt #[zero, lhs]
      
      let hbMVar ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque `h_1_lt_b
      let hrMVar ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque `h_0_lt_lhs
      
      -- The proof should directly produce the linearized result  
      let proof ← do
        trace[linearize] "Building linearization proof for: {original} → {transformed}"
        
        -- Create the proof term: (Int.zpow_le_iff_le_log hbMVar hrMVar).mp
        -- Infer the universe level from the type R
        let lhsType ← inferType lhs
        let rLevel ← match ← inferType lhsType with
          | Expr.sort level => pure level
          | _ => pure levelZero  -- fallback
        let iff_thm := mkAppN (mkConst ``Int.zpow_le_iff_le_log [rLevel]) #[hbMVar, hrMVar]
        pure (mkAppN (mkConst ``Iff.mp) #[iff_thm])
      
      return (proof, #[hbMVar, hrMVar])
    else
      let proof ← mkSorry transformed false
      return (proof, #[])
      
  | _, _ =>
    trace[linearize] "Unknown transformation pattern"
    let proof ← mkSorry transformed false
    return (proof, #[])

/-- Apply linearize transformation to a single hypothesis or goal -/
def linearizeHypothesis (hyp : Expr) : TacticM (Option (Expr × Expr × Array Expr)) := do
  let hypType ← inferType hyp
  trace[linearize] "Checking hypothesis type: {hypType}"
  if let some transformed ← transformZpowComparison hypType then
    trace[linearize] "Transformed to: {transformed}"
    let (proof, sideConds) ← proveTransformation hypType transformed
    return some (transformed, proof, sideConds)
  else
    trace[linearize] "No transformation found"
    return none

/-- Main linearize tactic implementation -/
def linearizeTacticCore (targets : Array Expr) : TacticM Unit := do
  -- If no targets specified, try to linearize all hypotheses
  let actualTargets ← if targets.isEmpty then
    let lctx ← getLCtx
    lctx.foldlM (fun acc ldecl =>
      if ldecl.isImplementationDetail then return acc
      else return acc.push ldecl.toExpr) #[]
  else
    pure targets

  let mut newHyps : Array (Expr × Expr × Expr) := #[]  -- (original, transformed, proof)
  let mut allSideConds : Array Expr := #[]

  -- Try to transform each target
  for target in actualTargets do
    if let some (transformed, proof, sideConds) ← linearizeHypothesis target then
      newHyps := newHyps.push (target, transformed, proof)
      allSideConds := allSideConds ++ sideConds

  -- Add the new hypotheses and side condition goals
  liftMetaTactic fun goal => do
    let mut currentGoal := goal
    
    -- Add linearized hypotheses, replacing the originals
    for (origTarget, transformed, proof) in newHyps do
      -- Get the original hypothesis name
      let lctx ← getLCtx
      let origName := match origTarget with
        | Expr.fvar id => 
          match lctx.find? id with
          | some ldecl => ldecl.userName
          | none => `h_linearized
        | _ => `h_linearized
      
      -- Apply the proof to the original hypothesis to get the linearized version
      -- proof is: Iff.mpr (Int.lt_zpow_iff_log_lt hb hr) : original → transformed
      -- origTarget is: h : original  
      -- We want: h_linearized : transformed
      let linearizedProof := mkApp proof origTarget
      
      -- Add the linearized hypothesis and clear the original
      let goalWithAssertion ← MVarId.assert currentGoal origName transformed linearizedProof
      -- Introduce the asserted hypothesis into the context
      let (_, newGoal) ← MVarId.intro goalWithAssertion origName
      -- Try to clear the original hypothesis if it's an fvar
      let finalGoal ← match origTarget with
        | Expr.fvar originalId => 
          try
            MVarId.clear newGoal originalId
          catch _ => 
            pure newGoal  -- If we can't clear it, just continue
        | _ => pure newGoal
      currentGoal := finalGoal
    
    -- Add side condition goals
    let sideCondGoals := allSideConds.map (fun expr => expr.mvarId!)
    
    -- Return main goal plus all side condition goals
    return (#[currentGoal] ++ sideCondGoals).toList

  -- Suggest trying linarith
  if !newHyps.isEmpty then
    Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) "linarith"

/-- The linearize tactic syntax -/
syntax (name := linearize) "linearize" (ppSpace colGt term)* : tactic

/-- Elaboration rule for linearize tactic -/
elab_rules : tactic
  | `(tactic| linearize $[$targets]*) => do
    let targetExprs ← targets.mapM (fun t => elabTerm t none)
    linearizeTacticCore targetExprs

end Mathlib.Tactic.Linearize
