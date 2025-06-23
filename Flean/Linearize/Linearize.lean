import Mathlib.Data.Int.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.TryThis
import Lean.Elab.Tactic.Basic
import Lean.Elab.Term
import Flean.Linearize.Lemmas

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
          let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
          trace[linearize] "hbType: {hbType}"
          let rType ← inferType R -- Type u
          let level := rType.sortLevel!

          let zero ← Expr.ofNat R 0
          let ltInst ← synthInstance (← mkAppM ``LT #[R])
          let hrType ← mkAppOptM' (mkConst ``LT.lt [levelZero]) #[some R, some ltInst, some zero, some lhs]

          trace[linearize] "hrType: {hrType}"

          let hbGoal ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque (`hb)
          let hrGoal ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque (`hr)

          let thmType ← mkAppM ``Iff #[d.type, transformed]
          let thmMVar ← mkFreshExprMVar thmType MetavarKind.syntheticOpaque `thm

          let r ← R.toSyntax
          let hbs ← hbGoal.toSyntax
          let hrs ← hrGoal.toSyntax
          let lhsS ← lhs.toSyntax
          let expS ← exp.toSyntax
          let thmProof ← Term.elabTerm (← `(Int.lt_zpow_iff_log_lt (R := $r) (x := $expS) (r := $lhsS) $hbs $hrs)) (some thmType)
          thmMVar.mvarId!.assign thmProof

          let proof ← mkAppM ``Iff.mp #[thmMVar, d.toExpr]

          let g ← g.clear h
          let (_, g) ← g.note d.userName proof

          Term.synthesizeSyntheticMVarsUsingDefault

          return [g, hbGoal.mvarId!, hrGoal.mvarId!]
        else if let some (b, _, exp, _) ← isNatCastZpow lhs then
          -- (b : R)^exp < rhs ↔ exp < Int.log b rhs + 1 (when 0 < rhs, 1 < b)
          trace[linearize] "Applying zpow_lt pattern for base {b} (b^x < r direction)"
          let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
          trace[linearize] "hbType: {hbType}"

          let zero ← Expr.ofNat R 0
          let ltInst ← synthInstance (← mkAppM ``LT #[R])
          let hrType ← mkAppOptM' (mkConst ``LT.lt [levelZero]) #[some R, some ltInst, some zero, some rhs]

          trace[linearize] "hrType: {hrType}"

          let hbGoal ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque (`hb)
          let hrGoal ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque (`hr)

          let logExpr ← mkAppM ``Int.log #[mkNatLit b, rhs]
          let plusOne ← mkAppM ``HAdd.hAdd #[logExpr, mkIntLit 1]
          -- Convert exponent to integer if it's a natural number
          let expType ← inferType exp
          let intExp ← if expType.isConstOf ``Nat then
            mkAppM ``Int.ofNat #[exp]
          else
            pure exp
          let targetComparison ← mkAppM ``LT.lt #[intExp, plusOne]

          let thmType ← mkArrow d.type targetComparison
          let thmMVar ← mkFreshExprMVar thmType MetavarKind.syntheticOpaque `thm

          let r ← R.toSyntax
          let hbs ← hbGoal.toSyntax
          let hrs ← hrGoal.toSyntax
          let rhsS ← rhs.toSyntax
          let expS ← exp.toSyntax
          let bSyntax ← (mkNatLit b).toSyntax
          let thmProof ← Term.elabTerm (← `(Mathlib.Tactic.Linearize.zpow_lt_imp_lt_log_succ (R := $r) (b := $bSyntax) (n := $expS) (r := $rhsS) $hbs $hrs)) (some thmType)
          thmMVar.mvarId!.assign thmProof

          let proof ← mkAppM' thmMVar #[d.toExpr]

          let g ← g.clear h
          let (_, g) ← g.note d.userName proof

          Term.synthesizeSyntheticMVarsUsingDefault

          return [g, hbGoal.mvarId!, hrGoal.mvarId!]
        else
          throwError "linearize: unsupported zpow expression"

      | (``LE.le, #[R, _, lhs, rhs]) =>
        if let some (b, _, exp, _) ← isNatCastZpow rhs then
          trace[linearize] "Applying le_zpow_iff_log_le for base {b}"
          let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
          let zero ← Expr.ofNat R 0
          let ltInst ← synthInstance (← mkAppM ``LT #[R])
          let hrType ← mkAppOptM' (mkConst ``LT.lt [levelZero]) #[some R, some ltInst, some zero, some lhs]

          let hbGoal ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque (`hb)
          let hrGoal ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque (`hr)

          let thmType ← mkArrow d.type transformed
          let thmMVar ← mkFreshExprMVar thmType MetavarKind.syntheticOpaque `thm

          let r ← R.toSyntax
          let hbs ← hbGoal.toSyntax
          let hrs ← hrGoal.toSyntax
          let lhsS ← lhs.toSyntax
          let expS ← exp.toSyntax
          let bSyntax ← (mkNatLit b).toSyntax
          let thmProof ← Term.elabTerm (← `(Mathlib.Tactic.Linearize.le_zpow_imp_log_le (R := $r) (b := $bSyntax) (n := $expS) (r := $lhsS) $hbs $hrs)) (some thmType)
          thmMVar.mvarId!.assign thmProof

          let proof ← mkAppM' thmMVar #[d.toExpr]

          let g ← g.clear h
          let (_, g) ← g.note d.userName proof

          Term.synthesizeSyntheticMVarsUsingDefault

          return [g, hbGoal.mvarId!, hrGoal.mvarId!]
        else if let some (b, _, exp, _) ← isNatCastZpow lhs then
          trace[linearize] "Applying Int.zpow_le_iff_le_log for base {b} (reverse direction)"
          let hbType ← mkAppM ``LT.lt #[mkNatLit 1, mkNatLit b]
          trace[linearize] "hbType: {hbType}"

          let zero ← Expr.ofNat R 0
          let ltInst ← synthInstance (← mkAppM ``LT #[R])
          let hrType ← mkAppOptM' (mkConst ``LT.lt [levelZero]) #[some R, some ltInst, some zero, some rhs]

          trace[linearize] "hrType: {hrType}"

          let hbGoal ← mkFreshExprMVar hbType MetavarKind.syntheticOpaque (`hb)
          let hrGoal ← mkFreshExprMVar hrType MetavarKind.syntheticOpaque (`hr)

          let thmType ← mkAppM ``Iff #[d.type, transformed]
          let thmMVar ← mkFreshExprMVar thmType MetavarKind.syntheticOpaque `thm

          let r ← R.toSyntax
          let hbs ← hbGoal.toSyntax
          let hrs ← hrGoal.toSyntax
          let rhsS ← rhs.toSyntax
          let expS ← exp.toSyntax
          let thmProof ← Term.elabTerm (← `(Int.zpow_le_iff_le_log (R := $r) (x := $expS) (r := $rhsS) $hbs $hrs)) (some thmType)
          thmMVar.mvarId!.assign thmProof

          let proof ← mkAppM ``Iff.mp #[thmMVar, d.toExpr]

          let g ← g.clear h
          let (_, g) ← g.note d.userName proof

          Term.synthesizeSyntheticMVarsUsingDefault

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
