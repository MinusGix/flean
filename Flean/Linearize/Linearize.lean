import Mathlib.Data.Int.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Basic
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

/-- Helper to convert an Nat | Int to an Int -/
def asInt (e : Expr) : MetaM Q(ℤ) := do
  if (← inferType e).constName? == .some ``Nat then
    have e : Q(ℕ) := e
    pure q(Int.ofNat $e)
  else
    pure e

/-- Try to solve a side goal automatically based on its type -/
def trySolveSideGoal (g : MVarId) : TacticM (Option MVarId) := do
  try
    -- Check if the goal is already assigned
    if ← g.isAssigned then
      trace[linearize] "Goal already solved"
      return none

    -- Get the goal type to determine what kind of side condition it is
    let goalType ← g.getType
    trace[linearize] "Trying to auto-solve side goal: {goalType}"

    -- Save the current goal state
    let savedGoals ← getGoals

    -- Check if it's a 1 < b type goal (where b is a natural number)
    match goalType.getAppFnArgs with
    | (``LT.lt, #[_, _, lhs, rhs]) =>
      -- Check if lhs is 1
      let isOne := lhs.isConstOf ``One.one ||
        (match lhs.getAppFnArgs with
         | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit? == some 1
         | _ => false)

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
          -- assumption failed, try linarith
          trace[linearize] "assumption failed, trying linarith"
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
    | (``LE.le, #[_, _, lhs, rhs]) =>
      -- Check if lhs is 1 (for patterns like 1 ≤ b)
      let isOne := lhs.isConstOf ``One.one ||
        (match lhs.getAppFnArgs with
         | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit? == some 1
         | _ => false)

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
          -- assumption failed, try linarith
          trace[linearize] "assumption failed, trying linarith"
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
    | _ =>
      -- Unknown goal type, keep it as is
      trace[linearize] "Unknown side goal type, keeping as is"
      return some g
  catch e =>
    trace[linearize] "Error in trySolveSideGoal: {e.toMessageData}"
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
          have a : Q(ℕ) := mkNatLit b_lhs
          let intExpLhs ← asInt exp_lhs
          let intExpRhs ← asInt exp_rhs
          pure (some q($intExpLhs < $intExpRhs))
        else
          return none
      else
        -- lhs < (b : R)^exp � Int.log b lhs < exp (when 0 < lhs, 1 < b)
        have b : Q(ℕ) := mkNatLit b_rhs
        have logExpr : Q(ℤ) := q(Int.log $b $lhs)
        let intExp ← asInt exp_rhs
        pure (some q($logExpr < $intExp))
    else if let some (b, _, exp, _) ← isNatCastZpow lhs then
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
        -- lhs ≤ (b : R)^exp ↔ Int.log b lhs ≤ exp (when 0 < lhs, 1 < b)
        have b : Q(ℕ) := mkNatLit b_rhs
        let intExp ← asInt exp_rhs
        pure (some q(Int.log $b $lhs ≤ $intExp))
    else if let some (b, _, exp, _) ← isNatCastZpow lhs then
      -- (b : R)^exp ≤ rhs ↔ exp ≤ Int.log b rhs (when 0 < rhs, 1 < b)
      have b : Q(ℕ) := mkNatLit b
      let intExp ← asInt exp
      pure (some q($intExp ≤ Int.log $b $rhs))
    else
      return none
  | _ => return none


/-- Apply linearization to a goal of the form a^m < a^n using zpow_lt_zpow_right₀ -/
def linearizeGoal (g : MVarId) : TacticM (List MVarId) := do
  g.withContext do
    let goalType ← g.getType
    trace[linearize] "Analyzing goal: {goalType}"

    -- Check if this goal can be linearized using zpow comparison
    match goalType.getAppFnArgs with
    | (``LT.lt, #[_, _, lhs, rhs]) =>
      if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
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
        throwError "linearize: goal linearization only supports same-base zpow comparisons"
    | (``LE.le, #[_, _, lhs, rhs]) =>
      if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
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
    | _ =>
      throwError "linearize: goal linearization only supports < and ≤ comparisons"

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

      -- Apply the appropriate theorem based on the comparison type
      match d.type.getAppFnArgs with
      | (``LT.lt, #[_, _, lhs, rhs]) =>
        if let some (b_rhs, _, exp_rhs, _) ← isNatCastZpow rhs then
          if let some (b_lhs, _, exp_lhs, _) ← isNatCastZpow lhs then
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

      | (``LE.le, #[_, _, lhs, rhs]) =>
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
    trace[linearize] "targets are empty, trying to get all suitable hypotheses"
    -- If no targets specified, get all suitable hypotheses
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
  else
    -- Convert target expressions to FVarIds
    trace[linearize] "targets={targets}"
    targets.filterMapM fun target => do
      match target with
      | Expr.fvar id => pure (some id)
      | _ => pure none

  if targetFVars.isEmpty then
    -- No suitable hypotheses found, try goal linearization
    trace[linearize] "No suitable hypotheses found, trying goal linearization"
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
      throwError "linearize: no suitable hypotheses found and goal linearization failed: {e.toMessageData}"

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

  -- Try to automatically solve side goals
  trace[linearize] "Attempting to auto-solve {allNewGoals.length} side goals"
  let mut remainingSideGoals : List MVarId := []
  for sideGoal in allNewGoals do
    match ← trySolveSideGoal sideGoal with
    | none =>
      trace[linearize] "Successfully auto-solved side goal"
      -- Goal was solved, don't add it to remaining goals
    | some g =>
      trace[linearize] "Could not auto-solve side goal, keeping it"
      remainingSideGoals := remainingSideGoals.append [g]

  -- Set the new goal list: main goal followed by remaining side condition goals
  replaceMainGoal (currentGoal :: remainingSideGoals)

/-- The linearize tactic syntax -/
syntax (name := linearize) "linearize" (ppSpace colGt term)* : tactic

/-- Elaboration rule for linearize tactic -/
elab_rules : tactic
  | `(tactic| linearize $[$targets]*) => do
    trace[linearize] "pretargets={targets}"
    let g ← getMainGoal
    let targetExprs ← g.withContext do
      targets.mapM (fun t => elabTerm t none)
    linearizeTacticCore targetExprs

end Mathlib.Tactic.Linearize
