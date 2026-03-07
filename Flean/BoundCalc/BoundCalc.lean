/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Flean.Linearize.Linearize

/-!
# BoundCalc tactic

`bound_calc` automates monotonicity reasoning for products, divisions, and powers.

## Phase 1 (gcongr dispatch)
Calls `gcongr` to decompose the goal structurally, then dispatches subgoals
with a chain of standard tactics.

## Phase 3 (factor matching)
For goals where LHS and RHS have different syntactic groupings (e.g.,
`6 * D * den * num ≤ 3 * ab^2 * 2^L`), the tactic:
1. Extracts flat factor lists from both sides
2. Scans hypotheses for `≤`/`<` bounds
3. Finds a partition of factors covered by hypothesis groups
4. Constructs a proof via `mul_le_mul` chains + `linarith`

See `BoundCalc/Design.md` for the full design and `BoundCalc/TestCases.lean` for examples.
-/

open Lean Elab Meta Tactic

namespace BoundCalc

/-! ### Factor extraction -/

/-- Extract a flat list of multiplicative factors from an expression.
    `a * b * c` → `[a, b, c]`. Non-`*` subexpressions are treated as atomic. -/
partial def extractMulFactors (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, lhs, rhs]) =>
    extractMulFactors lhs ++ extractMulFactors rhs
  | _ => #[e]

/-! ### Bound hypothesis representation -/

/-- A hypothesis that states `∏ lhsFactors ≤ ∏ rhsFactors` (or `<`). -/
structure BoundHyp where
  lhsFactors : Array Expr
  rhsFactors : Array Expr
  proof      : Expr
  isStrict   : Bool
  deriving Inhabited

/-! ### Hypothesis scanning -/

/-- Check if an expression is `a ≤ b` and return `(a, b, isStrict=false)`. -/
def matchLE? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) => some (a, b)
  | _ => none

/-- Check if an expression is `a < b` and return `(a, b)`. -/
def matchLT? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => some (a, b)
  | _ => none

/-- Scan the local context for hypotheses of the form `X ≤ Y` or `X < Y`.
    Returns an array of `BoundHyp` with extracted factor lists. -/
def scanBoundHyps (ctx : LocalContext) : Array BoundHyp := Id.run do
  let mut hyps : Array BoundHyp := #[]
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let ty := decl.type
    if let some (a, b) := matchLE? ty then
      hyps := hyps.push {
        lhsFactors := extractMulFactors a
        rhsFactors := extractMulFactors b
        proof := decl.toExpr
        isStrict := false
      }
    else if let some (a, b) := matchLT? ty then
      hyps := hyps.push {
        lhsFactors := extractMulFactors a
        rhsFactors := extractMulFactors b
        proof := decl.toExpr
        isStrict := true
      }
  return hyps

/-! ### Multiset operations (using `isDefEq` for factor comparison) -/

/-- Try to remove one element from `arr` that is definitionally equal to `target`.
    Returns `some remaining` on success, `none` on failure. -/
def removeDefEq (arr : Array Expr) (target : Expr) : MetaM (Option (Array Expr)) := do
  for h : i in [:arr.size] do
    if ← withNewMCtxDepth (isDefEq arr[i] target) then
      return some (arr.eraseIdx i)
  return none

/-- Check if `sub` is a sub-multiset of `arr` (using `isDefEq`).
    Returns `some remaining` (the elements of `arr` not matched) on success. -/
def multisetRemoveAll (arr sub : Array Expr) : MetaM (Option (Array Expr)) := do
  let mut remaining := arr
  for elem in sub do
    match ← removeDefEq remaining elem with
    | some r => remaining := r
    | none => return none
  return some remaining

/-! ### Factor matching algorithm -/

/-- Build a product expression from an array of factors. -/
def buildProduct (factors : Array Expr) : MetaM Expr := do
  if factors.isEmpty then throwError "buildProduct: empty factor list"
  let mut result := factors[0]!
  for i in [1:factors.size] do
    result ← mkAppM ``HMul.hMul #[result, factors[i]!]
  return result

/-- Result of a successful factor matching: a list of hypothesis applications
    that together prove `∏ lhsFactors ≤ ∏ rhsFactors` (or `<` if strict). -/
structure MatchResult where
  /-- Ordered list of (lhsFactorGroup, rhsFactorGroup, proof, isStrict) -/
  groups : Array (Array Expr × Array Expr × Expr × Bool)

/-- Try to close a goal using a tactic. Returns true only if the goal is fully assigned.
    Suppresses error messages and catches all exceptions. -/
def tryTacticOnGoal (goal : MVarId) (tacStx : TSyntax `tactic) : MetaM Bool := do
  try
    let remaining ← goal.withContext do
      Elab.Term.TermElabM.run' (ctx := { errToSorry := false }) do
        Elab.Tactic.run goal (Elab.Tactic.evalTactic tacStx)
    if remaining.isEmpty then
      return ← goal.isAssigned
    return false
  catch _ => return false

/-- Create a fresh metavar with the current local context (so tactics can see hypotheses). -/
def mkFreshExprMVarInCtx (ty : Expr) (name : Name) : MetaM Expr := do
  mkFreshExprMVarAt (← getLCtx) (← getLocalInstances) ty MetavarKind.syntheticOpaque name

/-- Save and restore both Core and Meta state for backtracking. -/
def withFullBacktrack {α : Type} (action : MetaM (Option α)) : MetaM (Option α) := do
  let coreState ← Core.saveState
  let metaState ← get
  match ← action with
  | some result => return some result
  | none =>
    set metaState
    coreState.restore
    return none

/-- Try to synthesize a proof of `lhs ≤ rhs` for a single factor pair.
    Tries: reflexivity, then omega/norm_num/linearize for decidable bounds. -/
def trySynthesizeSingleBound (lhs rhs : Expr) : MetaM (Option Expr) := do
  -- 1. Reflexive: l ≡ r definitionally
  let isEq ← withNewMCtxDepth (isDefEq lhs rhs)
  if isEq then
    try
      return some (← mkAppM ``le_refl #[lhs])
    catch _ => pure ()
  -- 2. Try specific lemma applications for common patterns
  let ty ← mkAppM ``LE.le #[lhs, rhs]
  for lemmaStx in #["exact Nat.one_le_two_pow", "exact Nat.one_le_pow _ _ (by omega)"] do
    let result ← withNewMCtxDepth do
      let mvar ← mkFreshExprMVarInCtx ty `_bc_tmp
      let stx ← match lemmaStx with
        | "exact Nat.one_le_two_pow" =>
          `(tactic| exact Nat.one_le_two_pow)
        | _ =>
          `(tactic| exact Nat.one_le_pow _ _ (by omega))
      if ← tryTacticOnGoal mvar.mvarId! stx then
        return some mvar
      return none
    if result.isSome then return result
  -- 3. Try decidable tactics (omega, norm_num, linearize) on a temporary goal.
  --    These are safe: they either close the goal completely or fail without side effects.
  --    We skip positivity/linarith as they can log errors that leak.
  for tacName in #["omega", "norm_num", "linearize"] do
    let result ← withNewMCtxDepth do
      let mvar ← mkFreshExprMVarInCtx ty `_bc_tmp
      let stx ← match tacName with
        | "omega" => `(tactic| omega)
        | "norm_num" => `(tactic| (norm_num; done))
        | _ => `(tactic| linearize)
      if ← tryTacticOnGoal mvar.mvarId! stx then
        return some mvar
      return none
    if result.isSome then return result
  return none

/-- Try to synthesize a proof of `∏ lhs ≤ ∏ rhs` for product expressions.
    Builds the product expressions and tries the same tactics as single bounds. -/
def trySynthesizeProductBound (lhs rhs : Array Expr) : MetaM (Option Expr) := do
  let lhsExpr ← buildProduct lhs
  let rhsExpr ← buildProduct rhs
  let ty ← mkAppM ``LE.le #[lhsExpr, rhsExpr]
  for tacName in #["omega", "norm_num", "linarith"] do
    let result ← withNewMCtxDepth do
      let mvar ← mkFreshExprMVarInCtx ty `_bc_tmp
      let stx ← match tacName with
        | "omega" => `(tactic| omega)
        | "norm_num" => `(tactic| (norm_num; done))
        | _ => `(tactic| linarith)
      if ← tryTacticOnGoal mvar.mvarId! stx then
        return some mvar
      return none
    if result.isSome then return result
  return none

/-- Try to find a hypothesis that exactly covers the given factor lists (no synthesis).
    Returns `(proof, isStrict)`. -/
def findHypMatch (lhs rhs : Array Expr) (hyps : Array BoundHyp) :
    MetaM (Option (Expr × Bool)) := do
  for h in hyps do
    if h.lhsFactors.size != lhs.size then continue
    if h.rhsFactors.size != rhs.size then continue
    match ← multisetRemoveAll lhs h.lhsFactors with
    | some #[] =>
      match ← multisetRemoveAll rhs h.rhsFactors with
      | some #[] => return some (h.proof, h.isStrict)
      | _ => continue
    | _ => continue
  return none

/-- Try to find a hypothesis or synthesized bound that covers the given factor lists.
    Returns `(proof, isStrict)`. -/
def findSingleMatch (lhs rhs : Array Expr) (hyps : Array BoundHyp)
    (allowSynthesis : Bool) : MetaM (Option (Expr × Bool)) := do
  -- 1. Check context hypotheses
  if let some result ← findHypMatch lhs rhs hyps then
    return some result
  -- 2. For single factors, try synthesizing a bound (always non-strict)
  if allowSynthesis && lhs.size == 1 && rhs.size == 1 then
    if let some proof ← trySynthesizeSingleBound lhs[0]! rhs[0]! then
      return some (proof, false)
  return none

/-- Generate all ways to split an array into two non-empty parts.
    Returns pairs `(left, right)` where `left ++ right` is a permutation of `arr`.
    We enumerate by choosing a subset of indices for the left part. -/
def binaryPartitions (arr : Array Expr) : Array (Array Expr × Array Expr) := Id.run do
  if arr.size ≤ 1 then return #[]
  let n := arr.size
  -- Enumerate non-empty proper subsets via bitmask
  let mut result : Array (Array Expr × Array Expr) := #[]
  -- We use bitmasks from 1 to 2^n - 2 (non-empty, non-full)
  let total := 1 <<< n
  for mask in [1:total - 1] do
    let mut left : Array Expr := #[]
    let mut right : Array Expr := #[]
    for h : i in [:n] do
      if mask &&& (1 <<< i) != 0 then
        left := left.push arr[i]
      else
        right := right.push arr[i]
    -- Only include if both parts are non-empty (guaranteed by mask range)
    result := result.push (left, right)
  return result

/-- Core recursive matching algorithm.
    Tries to partition `lhsFactors` and `rhsFactors` into groups,
    each covered by a hypothesis from `hyps`.
    `allowSynthesis` enables synthesized bounds (reflexive, norm_num, linearize).
    `depth` limits recursion. -/
partial def findMatching (lhsFactors rhsFactors : Array Expr)
    (hyps : Array BoundHyp) (allowSynthesis : Bool := false)
    (depth : Nat := 8) : MetaM (Option MatchResult) := do
  if depth == 0 then return none

  -- Base case: try a single hypothesis (+ optional synthesis)
  if let some (proof, isStrict) ← findSingleMatch lhsFactors rhsFactors hyps allowSynthesis then
    return some { groups := #[(lhsFactors, rhsFactors, proof, isStrict)] }

  -- Recursive case: try all binary partitions of LHS
  let lhsParts := binaryPartitions lhsFactors
  for (lhsLeft, lhsRight) in lhsParts do
    let rhsParts := binaryPartitions rhsFactors
    for (rhsLeft, rhsRight) in rhsParts do
      if let some matchLeft ← findMatching lhsLeft rhsLeft hyps allowSynthesis (depth - 1) then
        if let some matchRight ← findMatching lhsRight rhsRight hyps allowSynthesis (depth - 1) then
          return some { groups := matchLeft.groups ++ matchRight.groups }
  return none

/-! ### Proof construction -/

/-- The dispatch tactic chain for closing side goals (nonnegativity etc.) -/
def dispatchSideGoalSyntax : TSyntax `tactic :=
  Unhygienic.run `(tactic|
    first
      | positivity
      | assumption
      | linarith
      | omega
      | (norm_num; done)
  )

/-- Wrap a proof expression syntax with `le_of_lt` if it's strict and we need `≤`. -/
def weakenIfStrict (proofStx : TSyntax `term) (isStrict : Bool) :
    CoreM (TSyntax `term) := do
  if isStrict then
    `(le_of_lt $proofStx)
  else
    return proofStx

/-- Build a `have` statement for one step of the mul chain.
    `goalStrict`: whether we need the result to be `<`.
    `leftStrict`/`rightStrict`: whether the left/right proofs are `<`.
    For a `<` result, we need at least one strict input.
    `mul_lt_mul : a < b → c ≤ d → 0 < c → 0 ≤ b → a * c < b * d`
    `mul_lt_mul' : a ≤ b → c < d → 0 ≤ c → 0 < b → a * c < b * d`
    `mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d` -/
def mkMulChainStep (name : Name) (leftProof rightProof : TSyntax `term)
    (leftStrict rightStrict goalStrict : Bool) :
    CoreM (TSyntax `tactic) := do
  let dispatch := dispatchSideGoalSyntax
  if goalStrict then
    if leftStrict then
      -- mul_lt_mul : a < b → c ≤ d → 0 < c → 0 ≤ b → a * c < b * d
      let rp ← weakenIfStrict rightProof rightStrict
      `(tactic|
        have $(mkIdent name) := mul_lt_mul $leftProof $rp
          (by $(⟨dispatch.raw⟩)) (by $(⟨dispatch.raw⟩)))
    else if rightStrict then
      -- mul_lt_mul' : a ≤ b → c < d → 0 ≤ c → 0 < b → a * c < b * d
      `(tactic|
        have $(mkIdent name) := mul_lt_mul' $leftProof $rightProof
          (by $(⟨dispatch.raw⟩)) (by $(⟨dispatch.raw⟩)))
    else
      -- Both non-strict but goal is strict — shouldn't happen (caller ensures at least one strict)
      -- Fall back to mul_le_mul (will fail at linarith step)
      `(tactic|
        have $(mkIdent name) := mul_le_mul $leftProof $rightProof
          (by $(⟨dispatch.raw⟩)) (by $(⟨dispatch.raw⟩)))
  else
    -- Goal is ≤: weaken any strict proofs
    let lp ← weakenIfStrict leftProof leftStrict
    let rp ← weakenIfStrict rightProof rightStrict
    `(tactic|
      have $(mkIdent name) := mul_le_mul $lp $rp
        (by $(⟨dispatch.raw⟩)) (by $(⟨dispatch.raw⟩)))

/-- Try to close the main goal using the factor matching algorithm.
    The goal should be of the form `LHS ≤ RHS` or `LHS < RHS` where both sides are products. -/
def closeByFactorMatching (goal : MVarId) : TacticM (Option (List MVarId)) := do
  goal.withContext do
    let target ← goal.getType
    -- Extract LHS and RHS from ≤ or < goal
    let (lhs, rhs, goalStrict) ← match matchLE? target with
      | some (a, b) => pure (a, b, false)
      | none => match matchLT? target with
        | some (a, b) => pure (a, b, true)
        | none => return none

    let lhsFactors := extractMulFactors lhs
    let rhsFactors := extractMulFactors rhs

    -- Only use factor matching for multi-factor products
    if lhsFactors.size ≤ 1 && rhsFactors.size ≤ 1 then return none

    -- Scan hypotheses
    let ctx ← getLCtx
    let hyps := scanBoundHyps ctx

    -- Try to find a matching: first hypothesis-only, then with synthesis
    let some matching ← (do
      if let some m ← findMatching lhsFactors rhsFactors hyps false then
        return some m
      findMatching lhsFactors rhsFactors hyps true
        : TacticM (Option MatchResult)) | return none

    -- For strict goals, verify at least one group is strict
    let hasStrict := matching.groups.any fun (_, _, _, s) => s
    if goalStrict && !hasStrict then return none

    -- Build the proof using `have` chain + `linarith`
    if matching.groups.size == 0 then return none

    if matching.groups.size == 1 then
      -- Single group: the hypothesis directly proves the goal (up to ring rewriting)
      let (_, _, proof, isStrict) := matching.groups[0]!
      -- For ≤ goal with strict proof, weaken first
      let effectiveProof ← if !goalStrict && isStrict then
        try mkAppM ``le_of_lt #[proof] catch _ => pure proof
      else pure proof
      -- Try: the proof might directly close the goal
      try
        goal.assign effectiveProof
        return some []
      catch _ => pure ()
      -- Try linarith with the proof as a hint
      try
        let stx ← `(tactic| linarith [$(← Term.exprToSyntax effectiveProof)])
        let goals ← evalTacticAt stx goal
        return some goals
      catch _ => return none

    -- Multiple groups: build mul chain
    -- Decide which step gets the strict lemma (for < goals)
    -- Strategy: use strict at the first step that has a strict input
    try
      let mut currentGoal := goal

      -- Build proof syntax array with strictness info
      let mut proofExprs : Array (TSyntax `term × Bool) := #[]
      for (_, _, proof, isStrict) in matching.groups do
        proofExprs := proofExprs.push (← Term.exprToSyntax proof, isStrict)

      -- For < goals, find which step will use the strict lemma
      -- We "spend" strictness at the first opportunity
      let mut strictSpent := !goalStrict  -- if goal is ≤, consider strict already "spent"

      let (firstProof, firstStrict) := proofExprs[0]!
      let (secondProof, secondStrict) := proofExprs[1]!

      let haveName := Name.mkSimple s!"h_bc_1"
      -- Determine if this step should produce a strict result
      let stepStrict := !strictSpent && (firstStrict || secondStrict)
      let haveStx ← mkMulChainStep haveName firstProof secondProof
        firstStrict secondStrict stepStrict
      if stepStrict then strictSpent := true

      let goals ← evalTacticAt haveStx currentGoal
      if goals.isEmpty then return some []
      currentGoal := List.head! goals
      let mut prevName := haveName
      let mut prevStrict := stepStrict

      -- Chain remaining groups
      for i in [2:matching.groups.size] do
        let (nextProof, nextStrict) := proofExprs[i]!
        let chainName := Name.mkSimple s!"h_bc_{i}"
        let prevIdent := mkIdent prevName

        let stepStrict := !strictSpent && (prevStrict || nextStrict)
        let haveStx ← mkMulChainStep chainName (⟨prevIdent.raw⟩) nextProof
          prevStrict nextStrict stepStrict
        if stepStrict then strictSpent := true

        let goals ← evalTacticAt haveStx currentGoal
        if goals.isEmpty then return some []
        currentGoal := List.head! goals
        prevName := chainName
        prevStrict := stepStrict

      -- Now close with linarith, providing the chain result as hint
      let finalIdent := mkIdent prevName
      let linarithStx ← `(tactic| linarith [$finalIdent])
      let goals ← evalTacticAt linarithStx currentGoal
      return some goals
    catch _ => return none

end BoundCalc

/-- `bound_calc` automates monotonicity reasoning for products.

**Phase 1:** Decomposes via `gcongr`, dispatches subgoals with standard tactics.
**Phase 3:** For regrouped products, uses factor matching to find hypothesis
combinations and constructs `mul_le_mul` chains. -/
elab "bound_calc" : tactic => do
  let goal ← getMainGoal

  -- Phase 1: gcongr + dispatch chain (fast, no metavar creation)
  try
    evalTactic (← `(tactic|
      gcongr <;> first
        | assumption
        | exact le_refl _
        | positivity
        | omega
        | (norm_num; done)
        | linarith
        | (first | linearize | fail "linearize failed")
        | exact Nat.one_le_two_pow
        | exact Nat.one_le_pow _ _ (by omega)
    ))
    return
  catch _ => pure ()

  -- Phase 3: Factor matching (handles regrouped products)
  -- Save state so any metavars created during synthesis are cleaned up on failure
  let phase3State ← saveState
  try
    if let some remainingGoals ← BoundCalc.closeByFactorMatching goal then
      replaceMainGoal remainingGoals
      return
  catch _ => pure ()
  restoreState phase3State

  -- nlinarith fallback
  try
    evalTactic (← `(tactic| nlinarith))
    return
  catch _ => pure ()

  -- Phase 1b: gcongr decomposition + partial dispatch (P4 support)
  -- Decomposes the goal via gcongr, auto-closes nonneg/positivity subgoals,
  -- leaves the remaining bound subgoals for the user to fill in.
  -- We re-focus on the original goal to work around any leaked metavars from Phase 3.
  try
    setGoals [goal]
    evalTactic (← `(tactic|
      gcongr <;> first
        | assumption
        | exact le_refl _
        | positivity
        | omega
        | (norm_num; done)
        | linarith
        | (first | linearize | fail "linearize failed")
        | exact Nat.one_le_two_pow
        | exact Nat.one_le_pow _ _ (by omega)
        | skip
    ))
    return
  catch _ => pure ()

  throwError "bound_calc: could not close the goal"
