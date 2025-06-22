import Mathlib.Data.Int.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.TryThis
import Lean.Elab.Tactic.Basic
import Lean.Elab.Term

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
    if let some (b, _, exp, _) ← isNatCastZpow rhs then
      -- lhs < (b : R)^exp � Int.log b lhs < exp (when 0 < lhs, 1 < b)
      let logExpr ← mkAppM ``Int.log #[mkNatLit b, lhs]
      -- Convert exponent to integer if it's a natural number
      let expType ← inferType exp
      let intExp ← if expType.isConstOf ``Nat then
        mkAppM ``Int.ofNat #[exp]
      else
        pure exp
      mkAppM ``LT.lt #[logExpr, intExp]
    else if let some (b, _, exp, _) ← isNatCastZpow lhs then
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
    if let some (b, _, exp, _) ← isNatCastZpow rhs then
      -- lhs d (b : R)^exp � Int.log b lhs d exp (when 0 < lhs, 1 < b)
      let logExpr ← mkAppM ``Int.log #[mkNatLit b, lhs]
      -- Convert exponent to integer if it's a natural number
      let expType ← inferType exp
      let intExp ← if expType.isConstOf ``Nat then
        mkAppM ``Int.ofNat #[exp]
      else
        pure exp
      mkAppM ``LE.le #[logExpr, intExp]
    else if let some (b, _, exp, _) ← isNatCastZpow lhs then
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

def mkNatLit' (ty : Expr) (n : Nat) : MetaM Expr := do
  let level ← getLevel ty
  let r := mkRawNatLit n
  pure (mkApp3 (mkConst ``OfNat.ofNat [level]) ty r (mkApp (mkConst ``instOfNatNat) r))

/-- Apply linearization to a single hypothesis using the mathlib pattern -/
def linearizeHyp (h : FVarId) (g : MVarId) : TacticM (List MVarId) := do
  g.withContext do
    let d ← h.getDecl
    trace[linearize] "Analyzing hypothesis {d.userName} : {d.type}"

    -- Check if this hypothesis can be linearized
    match ← transformZpowComparison d.type with
    | some transformed => do
      trace[linearize] "Can linearize to: {transformed}"

      -- Apply the appropriate theorem based on the comparison type
      match d.type.getAppFnArgs with
      | (``LT.lt, #[R, _, lhs, rhs]) =>
        if let some (b, _, exp, _) ← isNatCastZpow rhs then
          trace[linearize] "Applying Int.lt_zpow_iff_log_lt for base {b}"
          -- Create goals for the side conditions
          let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
          trace[linearize] "hbType: {hbType}"
          let rType ← inferType R -- Type u
          let level := rType.sortLevel!
          -- let level ← getLevel R
          let zero ← Expr.ofNat R 0
          trace[linearize] "level: {level}"
          let ltInst ← synthInstance (← mkAppM ``LT #[R])
          trace[linearize] "ltInst: {ltInst}"
          let hrType ← mkAppOptM' (mkConst ``LT.lt [levelZero]) #[some R, some ltInst, some zero, some lhs]
          -- let hrType ← mkAppOptM ``LT.lt #[some R, some ltInst, some zero, some lhs]
          -- let hrType ← mkAppM ``LT.lt #[zero, lhs]
          trace[linearize] "hrType: {hrType}"

          let hbGoal ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque (`hb)
          let hrGoal ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque (`hr)
          trace[linearize] "hbGoal: {hbGoal}"
          trace[linearize] "hrGoal: {hrGoal}"

          -- Apply: (Int.lt_zpow_iff_log_lt hb hr).mpr h
          -- Construct the iff theorem using unification to handle implicits
          let thmType ← mkAppM ``Iff #[d.type, transformed]
          let thmMVar ← mkFreshExprMVar thmType MetavarKind.syntheticOpaque `thm

          trace[linearize] "thmType: {thmType}"
          trace[linearize] "thmMVar: {thmMVar}"

          -- Create the theorem term and unify
          -- let ltZpowThm ← mkConstWithFreshMVarLevels ``Int.lt_zpow_iff_log_lt
          -- let ltZpowThm ← mkConstWithLevelParams ``Int.lt_zpow_iff_log_lt
          -- let thmApp ← mkAppM ``Int.lt_zpow_iff_log_lt #[hbGoal, hrGoal]
          -- let thmApp ← mkAppM' ltZpowThm #[hbGoal, hrGoal]
          -- let ltZpowThm ← mkConstWithFreshMVarLevels ``Int.lt_zpow_iff_log_lt
          -- let ltZpowThm := mkConst ``Int.lt_zpow_iff_log_lt [level]
          -- [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
          -- let semifieldInst ← synthInstance (← mkAppM ``Semifield #[R])
          -- let linearOrderInst ← synthInstance (← mkAppM ``LinearOrder #[R])
          -- let isStrictORingInst ← synthInstance (← mkAppM ``IsStrictOrderedRing #[R])
          -- let floorSemiringInst ← synthInstance (← mkAppM ``FloorSemiring #[R])
          -- let thmApp := mkApp2 ltZpowThm hbGoal hrGoal
          let r ← R.toSyntax
          let hbs ← hbGoal.toSyntax
          let hrs ← hrGoal.toSyntax
          let lhsS ← lhs.toSyntax
          let expS ← exp.toSyntax
          let thmProof ← Term.elabTerm (← `(Int.lt_zpow_iff_log_lt (R := $r) (x := $expS) (r := $lhsS) $hbs $hrs)) (some thmType)
          -- let thmApp ← mkAppM' ltZpowThm #[R, semifieldInst, linearOrderInst, isStrictORingInst, floorSemiringInst]
          -- trace[linearize] "thmApp: {thmApp}"
          thmMVar.mvarId!.assign thmProof

          -- trace[linearize] "ltZpowThm: {ltZpowThm}"

          let proof ← mkAppM ``Iff.mp #[thmMVar, d.toExpr]
          trace[linearize] "proof: {proof}"

          -- Replace the old hypothesis with the linearized version
          let g ← g.clear h
          let (_, g) ← g.note d.userName proof

          Term.synthesizeSyntheticMVarsUsingDefault

          -- Return main goal followed by side condition goals
          return [g, hbGoal.mvarId!, hrGoal.mvarId!]
        else if let some (_, _, _, _) ← isNatCastZpow lhs then
          -- For b^x < r, this is harder to handle directly with Int.log
          -- Let's skip this case for now and focus on the main use case
          throwError "linearize: b^x < r direction not yet implemented (use r < b^x form instead)"
        else
          throwError "linearize: unsupported zpow expression"

      | (``LE.le, #[R, _, lhs, rhs]) =>
        if let some (b, _, _, _) ← isNatCastZpow rhs then
          trace[linearize] "Applying Int.zpow_le_iff_le_log for base {b}"
          -- Create goals for the side conditions
          let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
          let zero ← mkFreshExprMVar R
          -- let zeroGoal ← mkFreshExprMVar (← mkAppM ``Eq #[zero, mkNatLit 0])
          let hrType ← mkAppOptM ``LT.lt #[none, none, zero, lhs]

          let hbGoal ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque (`hb)
          let hrGoal ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque (`hr)

          -- Apply: (Int.zpow_le_iff_le_log hb hr).mp h
          let thmType ← mkAppM ``Iff #[d.type, transformed]
          let thmMVar ← mkFreshExprMVar thmType

          let zpowLeThm ← mkConstWithFreshMVarLevels ``Int.zpow_le_iff_le_log
          let thmApp ← mkAppM' zpowLeThm #[hbGoal, hrGoal]
          thmMVar.mvarId!.assign thmApp

          let proof ← mkAppM ``Iff.mp #[thmMVar, d.toExpr]

          -- Replace the old hypothesis with the linearized version
          let g ← g.clear h
          let (_, g) ← g.note d.userName proof

          return [g, hbGoal.mvarId!, hrGoal.mvarId!]
        else if let some (b, _, _, _) ← isNatCastZpow lhs then
          trace[linearize] "Applying Int.zpow_le_iff_le_log for base {b}"
          -- Case: (b : R)^exp ≤ rhs → exp ≤ Int.log b rhs
          let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
          let zero ← mkFreshExprMVar R
          let zeroGoal ← mkFreshExprMVar (← mkAppM ``Eq #[zero, mkNatLit 0])
          let hrType ← mkAppM ``LT.lt #[zero, rhs]

          let hbGoal ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque (`hb)
          let hrGoal ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque (`hr)

          -- For b^x ≤ r, we can use Int.zpow_le_iff_le_log: b^x ≤ r ↔ x ≤ Int.log b r
          let thmType ← mkAppM ``Iff #[d.type, transformed]
          let thmMVar ← mkFreshExprMVar thmType

          let zpowLeThm ← mkConstWithFreshMVarLevels ``Int.zpow_le_iff_le_log
          let thmApp ← mkAppM' zpowLeThm #[hbGoal, hrGoal]
          thmMVar.mvarId!.assign thmApp

          let proof ← mkAppM ``Iff.mp #[thmMVar, d.toExpr]

          -- Replace the old hypothesis with the linearized version
          let g ← g.clear h
          let (_, g) ← g.note d.userName proof

          return [g, hbGoal.mvarId!, hrGoal.mvarId!]
        else
          throwError "linearize: unsupported zpow expression"

      | _ =>
        throwError "linearize: unexpected comparison type"

    | none =>
      throwError "linearize: hypothesis {d.userName} cannot be linearized"

/-- Main linearize tactic implementation using mathlib patterns -/
def linearizeTacticCore (targets : Array Expr) : TacticM Unit := do
  -- Get the main goal
  let g ← getMainGoal

  -- Get target hypotheses
  let targetFVars ← if targets.isEmpty then
    -- If no targets specified, get all suitable hypotheses
    let lctx ← getLCtx
    let mut fvars : Array FVarId := #[]
    for ldecl in lctx do
      if !ldecl.isImplementationDetail then
        -- Check if this hypothesis can be linearized
        if (← transformZpowComparison ldecl.type).isSome then
          fvars := fvars.push ldecl.fvarId
    pure fvars
  else
    -- Convert target expressions to FVarIds
    targets.filterMapM fun target => do
      match target with
      | Expr.fvar id => pure (some id)
      | _ => pure none

  if targetFVars.isEmpty then
    throwError "linearize: no suitable hypotheses found"

  -- Apply linearization to each target hypothesis
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

  -- Set the new goal list: main goal followed by all side condition goals
  replaceMainGoal (currentGoal :: allNewGoals)

  -- Suggest trying linarith
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) "linarith"

/-- The linearize tactic syntax -/
syntax (name := linearize) "linearize" (ppSpace colGt term)* : tactic

/-- Elaboration rule for linearize tactic -/
elab_rules : tactic
  | `(tactic| linearize $[$targets]*) => do
    let targetExprs ← targets.mapM (fun t => elabTerm t none)
    linearizeTacticCore targetExprs

end Mathlib.Tactic.Linearize
