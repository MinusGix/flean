# Lean 4 Metaprogramming Reference: Theorem Construction and Application

This document provides a comprehensive reference for common patterns in Lean 4 metaprogramming, specifically focused on constructing and applying theorems in tactics. It includes both standard Lean 4 metaprogramming patterns and their Qq (typed quotation) alternatives.

## Table of Contents
1. [Setup and Imports](#setup-and-imports)
2. [Basic Expression Construction](#basic-expression-construction)
3. [Metavariable Management](#metavariable-management)
4. [Type Class Instance Synthesis](#type-class-instance-synthesis)
5. [Theorem Application Patterns](#theorem-application-patterns)
6. [Goal Manipulation](#goal-manipulation)
7. [Common Pitfalls and Solutions](#common-pitfalls-and-solutions)
8. [Qq-Specific Patterns](#qq-specific-patterns)

## Setup and Imports

### Standard Metaprogramming
```lean
import Lean.Elab.Tactic.Basic
import Lean.Elab.Term

open Lean Elab Meta Tactic
```

### With Qq (Typed Quotations)
```lean
import Lean.Elab.Tactic.Basic
import Lean.Elab.Term
import Qq

open Lean Elab Meta Tactic Qq
```

**Key differences with Qq:**
- Types are declared with `Q(...)` syntax
- Expressions are written with `q(...)` syntax
- Provides compile-time type checking for metaprogramming

## Basic Expression Construction

### Creating Constants and Applications

#### Standard Approach
```lean
-- Basic constant creation
let myConst := mkConst ``Nat.add
let myConstWithLevels ← mkConstWithFreshMVarLevels ``List.map

-- Simple applications
let natAddExpr ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]
let listMapExpr ← mkAppM ``List.map #[f, list]

-- Manual application (more control)
let app := mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3)
```

#### Qq Approach
```lean
-- Simple expressions with type checking
have two : Q(ℕ) := q(2)
have three : Q(ℕ) := q(3)
have natAddExpr : Q(ℕ) := q($two + $three)

-- Function application
have f : Q(α → β) := ...
have x : Q(α) := ...
have applied : Q(β) := q($f $x)

-- More complex expressions
have listExpr : Q(List ℕ) := q([1, 2, 3])
```

### Literal Construction

#### Standard Approach
```lean
-- Numeric literals
let natLit := mkNatLit 42
let intLit := mkIntLit (-5)

-- String literals
let strLit := mkStrLit "hello"

-- Type applications
let natType := mkConst ``Nat
let listNatType ← mkAppM ``List #[natType]
```

#### Qq Approach
```lean
-- Numeric literals with type
have natLit : Q(ℕ) := q(42)
have intLit : Q(ℤ) := q(-5)

-- String literals
have strLit : Q(String) := q("hello")

-- Type expressions
have natType : Q(Type) := q(ℕ)
have listNatType : Q(Type) := q(List ℕ)

-- Working with variables
let n : ℕ := 42
have nExpr : Q(ℕ) := q($n)
```

### Building Complex Types

#### Standard Approach
```lean
-- Function types
let funType ← mkArrow domainType codomainType

-- Dependent function types (Pi types)
let piType ← mkForallFVars #[x, y] bodyType

-- Product types
let prodType ← mkAppM ``Prod #[typeA, typeB]
```

#### Qq Approach
```lean
-- Function types
have α : Q(Type) := ...
have β : Q(Type) := ...
have funType : Q(Type) := q($α → $β)

-- Product types
have prodType : Q(Type) := q($α × $β)

-- Working with generic types
variable {R : Q(Type)}
have listType : Q(Type) := q(List $R)
```

## Metavariable Management

### Creating Metavariables

#### Standard Approach
```lean
-- Basic metavariable creation
let mvar ← mkFreshExprMVar someType MetavarKind.syntheticOpaque `name

-- Different metavariable kinds:
-- - MetavarKind.syntheticOpaque: For proof obligations
-- - MetavarKind.natural: For implicit arguments
-- - MetavarKind.synthetic: For placeholders

-- Creating multiple related metavariables
let mvars ← Array.mapM (fun ty => mkFreshExprMVar ty MetavarKind.syntheticOpaque `name) types
```

#### Qq Approach
```lean
-- Creating typed metavariables
have hbGoal ← mkFreshExprMVarQ q(1 < $b) MetavarKind.syntheticOpaque (`hb)
have hrGoal ← mkFreshExprMVarQ q(0 < $lhs) MetavarKind.syntheticOpaque (`hr)

-- Creating metavariables with complex types
have thmType : Q(Prop) := q($dType ↔ $transformed)
let thmMVar ← mkFreshExprMVarQ thmType MetavarKind.syntheticOpaque `thm

-- Working with typed proof obligations
have proof ← mkFreshExprMVarQ q($lhs ≤ $rhs) MetavarKind.syntheticOpaque `proof
```

### Assigning Metavariables

#### Standard Approach
```lean
-- Direct assignment
mvar.mvarId!.assign someExpr

-- Conditional assignment
if ← mvar.mvarId!.isAssigned then
  -- already assigned
else
  mvar.mvarId!.assign someExpr

-- Check assignment status
let isAssigned ← mvar.mvarId!.isAssigned
let assignment? ← mvar.mvarId!.getAssignment?
```

#### Qq Approach
```lean
-- Typed assignment
have thmProof : Q($lhs < ↑$b ^ $exp ↔ Int.log $b $lhs < $exp) := 
  q(Int.lt_zpow_iff_log_lt (R := $R) (x := $exp) (r := $lhs) $hbGoal $hrGoal)
thmMVar.mvarId!.assign thmProof

-- Assignment with type preservation
have proof : Q(Prop) := ...
mvar.mvarId!.assign proof

-- Note: Assignment is the same, but type safety is maintained
```

### Working with Metavariable Goals

#### Standard Approach
```lean
-- Convert expression metavar to goal
let goal := mvar.mvarId!

-- Apply tactics to specific metavariables
goal.withContext do
  -- work in the context of this goal
  someComputation

-- Get metavariable information
let mvarlDecl ← goal.getDecl
let goalType ← goal.getType
let localContext ← goal.getLCtx
```

#### Qq Approach
```lean
-- Same goal handling, but with typed expressions
let goal := mvar.mvarId!

-- Working within goal context with typed expressions
goal.withContext do
  -- inferTypeQ to get properly typed expressions
  let ⟨_, R, lhs⟩ ← inferTypeQ' lhs
  have rhs : Q($R) := rhs
  -- work with typed expressions

-- Creating and returning typed subgoals
return [g, hbGoal.mvarId!, hrGoal.mvarId!]
```

## Type Class Instance Synthesis

### Basic Instance Synthesis

#### Standard Approach
```lean
-- Synthesize instance for a type class
let addInst ← synthInstance (← mkAppM ``Add #[natType])
let ltInst ← synthInstance (← mkAppM ``LT #[realType])

-- Use synthesized instances
let addExpr ← mkAppOptM ``HAdd.hAdd #[none, none, some addInst, a, b]
```

#### Qq Approach
```lean
-- Synthesize instances with typed expressions
let _a1 ← synthInstanceQ q(Semifield $R)
let _a2 ← synthInstanceQ q(LinearOrder $R)
let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
let _a4 ← synthInstanceQ q(FloorSemiring $R)

-- Direct synthesis for specific types
let instNatCast ← synthInstanceQ q(NatCast ℤ)

-- Using assumeInstancesCommute for complex instance hierarchies
assumeInstancesCommute
```

### Working with Type Class Constraints

#### Standard Approach
```lean
-- Building expressions that depend on type class instances
-- Pattern: let the system infer instances automatically
let expr ← mkAppM ``LT.lt #[a, b]  -- System finds LT instance

-- Manual instance passing when needed
let ltInstance ← synthInstance (← mkAppM ``LT #[R])
let expr ← mkAppOptM ``LT.lt #[some R, some ltInstance, some a, some b]
```

#### Qq Approach
```lean
-- Type class instances are often inferred automatically in q(...)
have a : Q($R) := ...
have b : Q($R) := ...
have expr : Q(Prop) := q($a < $b)  -- LT instance inferred

-- Explicit instance synthesis when needed
let inst ← synthInstanceQ q(LT $R)

-- Working with polymorphic functions
have intExp : Q(ℤ) := q(@Nat.cast ℤ $instNatCast $exponent)
```

### Common Type Class Patterns

#### Standard Approach
```lean
-- Numeric type classes
let hasAdd ← synthInstance (← mkAppM ``Add #[typ])
let hasLT ← synthInstance (← mkAppM ``LT #[typ])
let hasLE ← synthInstance (← mkAppM ``LE #[typ])

-- Algebraic structures
let semigroup ← synthInstance (← mkAppM ``Semigroup #[typ])
let group ← synthInstance (← mkAppM ``Group #[typ])
let ring ← synthInstance (← mkAppM ``Ring #[typ])
let field ← synthInstance (← mkAppM ``Field #[typ])

-- Order structures
let preorder ← synthInstance (← mkAppM ``Preorder #[typ])
let partialOrder ← synthInstance (← mkAppM ``PartialOrder #[typ])
let linearOrder ← synthInstance (← mkAppM ``LinearOrder #[typ])
```

#### Qq Approach
```lean
-- Numeric type classes
have R : Q(Type) := ...
let hasAdd ← synthInstanceQ q(Add $R)
let hasLT ← synthInstanceQ q(LT $R)
let hasLE ← synthInstanceQ q(LE $R)

-- Algebraic structures
let semigroup ← synthInstanceQ q(Semigroup $R)
let group ← synthInstanceQ q(Group $R)
let ring ← synthInstanceQ q(Ring $R)
let field ← synthInstanceQ q(Field $R)

-- Order structures
let preorder ← synthInstanceQ q(Preorder $R)
let partialOrder ← synthInstanceQ q(PartialOrder $R)
let linearOrder ← synthInstanceQ q(LinearOrder $R)

-- Complex instance requirements
let _a1 ← synthInstanceQ q(Semifield $R)
let _a2 ← synthInstanceQ q(LinearOrder $R)
let _a3 ← synthInstanceQ q(IsStrictOrderedRing $R)
let _a4 ← synthInstanceQ q(FloorSemiring $R)
```

## Theorem Application Patterns

### Direct Theorem Application

#### Standard Approach
```lean
-- Simple theorem application
let theorem ← mkConstWithFreshMVarLevels ``Nat.add_comm
let proof ← mkAppM ``Nat.add_comm #[a, b]

-- Theorem with multiple arguments
let theorem ← mkConstWithFreshMVarLevels ``Int.lt_zpow_iff_log_lt
let proof ← mkAppM ``Int.lt_zpow_iff_log_lt #[R, x, n, hb, hr]
```

#### Qq Approach
```lean
-- Direct theorem application with typed expressions
have a : Q(ℕ) := ...
have b : Q(ℕ) := ...
have proof : Q($a + $b = $b + $a) := q(Nat.add_comm $a $b)

-- Complex theorem application
have thmProof : Q($lhs < ↑$b ^ $exp ↔ Int.log $b $lhs < $exp) := 
  q(Int.lt_zpow_iff_log_lt (R := $R) (x := $exp) (r := $lhs) $hbGoal $hrGoal)

-- Named arguments for clarity
have proof : Q(↑$b ^ $exp < $rhs → $exp < Int.log $b $rhs + 1) := 
  q(Mathlib.Tactic.Linearize.zpow_lt_imp_lt_log_succ (R := $R) (b := $b) (n := $exp) (r := $rhs) $hbGoal $hrGoal)
```

### Applying Theorems with Metavariable Arguments

#### Standard Approach
```lean
-- Create metavariables for unknown arguments
let sideCond1 ← mkFreshExprMVar type1 MetavarKind.syntheticOpaque `h1
let sideCond2 ← mkFreshExprMVar type2 MetavarKind.syntheticOpaque `h2

-- Apply theorem with metavariables
let proof ← mkAppM ``my_theorem #[knownArg1, sideCond1, knownArg2, sideCond2]

-- Return the metavariables as subgoals
return [mainGoal, sideCond1.mvarId!, sideCond2.mvarId!]
```

#### Qq Approach
```lean
-- Create typed metavariables for side conditions
let hbGoal ← mkFreshExprMVarQ q(1 < $b) MetavarKind.syntheticOpaque (`hb)
let hrGoal ← mkFreshExprMVarQ q(0 < $lhs) MetavarKind.syntheticOpaque (`hr)

-- Apply theorem with metavariables
have thmProof : Q($lhs < ↑$b ^ $exp ↔ Int.log $b $lhs < $exp) := 
  q(Int.lt_zpow_iff_log_lt (R := $R) (x := $exp) (r := $lhs) $hbGoal $hrGoal)

-- Assign and return subgoals
thmMVar.mvarId!.assign thmProof
return [g, hbGoal.mvarId!, hrGoal.mvarId!]
```

### Equivalence and Implication Application

#### Standard Approach
```lean
-- Applying iff theorems
let iffThm ← mkAppM ``some_iff_theorem #[args...]
let forwardProof ← mkAppM ``Iff.mp #[iffThm, originalHyp]
let backwardProof ← mkAppM ``Iff.mpr #[iffThm, transformedHyp]

-- Applying implication theorems
let impThm ← mkAppM ``some_imp_theorem #[args...]
let proof ← mkAppM impThm #[originalHyp]
```

#### Qq Approach
```lean
-- Applying iff theorems with typed expressions
have iffThm : Q($P ↔ $Q) := q(some_iff_theorem ...)
have originalHyp : Q($P) := ...
have forwardProof : Q($Q) := q(Iff.mp $iffThm $originalHyp)

-- Direct iff application
let dExpr : Q($lhs < ↑$b ^ $exp) := d.toExpr
have proof := q(Iff.mp $thmProof $dExpr)

-- Implication application
have impThm : Q($P → $Q) := q(some_imp_theorem ...)
have proof : Q($Q) := q($impThm $originalHyp)
```

### Building Proof Terms Incrementally

#### Standard Approach
```lean
-- Step-by-step proof construction
let step1 ← mkAppM ``theorem1 #[arg1, arg2]
let step2 ← mkAppM ``theorem2 #[step1, arg3]
let finalProof ← mkAppM ``theorem3 #[step2, arg4]

-- Function composition style
let composed ← mkAppM ``Function.comp #[f, g]
let appliedComposed ← mkAppM composed #[x]
```

#### Qq Approach
```lean
-- Step-by-step with typed expressions
have step1 : Q($P) := q(theorem1 $arg1 $arg2)
have step2 : Q($Q) := q(theorem2 $step1 $arg3)
have finalProof : Q($R) := q(theorem3 $step2 $arg4)

-- Function composition with types
have f : Q(α → β) := ...
have g : Q(β → γ) := ...
have composed : Q(α → γ) := q(Function.comp $g $f)
have x : Q(α) := ...
have appliedComposed : Q(γ) := q($composed $x)

-- Building complex proofs
have dType : Q(Prop) := d.type
have thmType : Q(Prop) := q($dType ↔ $transformed)
let thmMVar ← mkFreshExprMVarQ thmType MetavarKind.syntheticOpaque `thm
```

## Goal Manipulation

### Goal State Management

```lean
-- Get current goals
let goals ← getGoals

-- Set goals
setGoals [goal1, goal2, goal3]

-- Replace main goal
replaceMainGoal newGoals

-- Work with specific goal
goal.withContext do
  -- computations in goal's context
  someWork
```

### Hypothesis Management

```lean
-- Add new hypothesis
let (fvarId, newGoal) ← goal.note userName proofExpr

-- Clear hypothesis
let newGoal ← goal.clear fvarId

-- Substitute hypothesis
let newGoal ← goal.replace fvarId newProofExpr

-- Get hypothesis declaration
let decl ← fvarId.getDecl
let hypType := decl.type
let hypName := decl.userName
```

### Goal Transformation

```lean
-- Apply tactic to goal
let newGoals ← goal.apply tacticExpr

-- Change goal target
let newGoal ← goal.change newTarget

-- Assert new fact
let newGoal ← goal.assert userName newType newProof

-- Define new value
let newGoal ← goal.define userName newType newValue
```

## Common Pitfalls and Solutions

### Level Management

```lean
-- Problem: Level mismatches
-- Solution: Use mkConstWithFreshMVarLevels for polymorphic constants
let polyConst ← mkConstWithFreshMVarLevels ``List.map

-- Problem: Manual level construction
-- Solution: Let Lean infer levels when possible
let expr ← mkAppM ``somePolymorphicFn #[args]  -- Lean infers levels
```

### Type Inference Issues

```lean
-- Problem: Type not inferred correctly
-- Solution: Provide explicit type annotations
let typedExpr ← mkAppM ``someFunction #[arg] >>= fun e => 
  ensureHasType expectedType e

-- Problem: Instance synthesis failure
-- Solution: Synthesize instances explicitly
let inst ← synthInstance targetClass
let expr ← mkAppOptM ``function #[some inst, otherArgs...]
```

### Context Management

```lean
-- Problem: Working outside goal context
-- Solution: Always work within goal context for local computations
goal.withContext do
  let localDecl ← localVar.fvarId!.getDecl
  -- work with local declarations

-- Problem: Metavariable assignment outside context
-- Solution: Assign metavariables in their own context
mvar.mvarId!.withContext do
  mvar.mvarId!.assign value
```

### Performance Considerations

```lean
-- Efficient: Batch operations
let mvars ← Array.mapM createMVar types
let proofs ← mvars.mapM buildProof

-- Inefficient: Repeated small operations in loops
-- Prefer bulk operations when possible

-- Efficient: Use mkAppM when possible (handles instance synthesis)
let expr ← mkAppM ``function #[args]

-- Less efficient: Manual instance synthesis for every call
let inst ← synthInstance ...
let expr ← mkApp ... inst ...
```

### Debugging Patterns

```lean
-- Trace expression structure
trace[debug] "Expression: {expr}"
trace[debug] "Type: {← inferType expr}"

-- Check metavariable status
trace[debug] "MVar assigned: {← mvar.mvarId!.isAssigned}"

-- Inspect goal state
trace[debug] "Goals: {← getGoals}"
trace[debug] "Local context: {← getLCtx}"
```

## Qq-Specific Patterns

### Type Inference with inferTypeQ

```lean
-- Get the type of an expression and extract components
let ⟨_, R, lhs⟩ ← inferTypeQ' lhs
have rhs : Q($R) := rhs

-- This is crucial when synthInstanceQ fails due to type mismatches
-- Example: Using R from LT.lt can cause issues, so we get it from the expression itself
```

### Type Casting and Redeclaration

```lean
-- Casting by redeclaration (not checked at compile time!)
have e : Expr := someExpr
have e : Q(ℕ) := e  -- Cast to typed expression

-- Converting between Nat and Int
have n : Q(ℕ) := q(5)
have i : Q(ℤ) := q(Int.ofNat $n)

-- Working with different power notations
have exp : Q(ℕ) := ...
have intExp : Q(ℤ) := q(@Nat.cast ℤ $instNatCast $exp)
```

### Using `have` instead of `let`

```lean
-- Prefer `have` for Qq expressions
have x : Q(ℤ) := q(blah)  -- Good: doesn't keep originating info

-- Avoid `let` with Qq
let x : Q(ℤ) := q(blah)   -- Can cause weird issues with Qq
```

### Working with Natural Number Literals

```lean
-- Creating natural number literals
have b : Q(ℕ) := mkNatLit 42

-- Pattern matching on literals
if let some n := natExpr.rawNatLit? then
  have b : Q(ℕ) := mkNatLit n
  -- use b
```

### Handling Powers (zpow vs pow)

```lean
-- zpow is used with integers and generic R
have pow1 : Q($R) := q((2 : $R)^($n : ℤ))

-- pow is used with natural numbers
have pow2 : Q(ℕ) := q(2^($n : ℕ))

-- Converting between them
have natPow : Q(ℕ) := ...
have intPow : Q(ℤ) := q(Int.ofNat $natPow)
```

### Common Qq Pitfalls and Solutions

#### synthInstanceQ Failures
```lean
-- Problem: synthInstanceQ fails with unclear types
-- Solution: Use inferTypeQ to get proper type
let ⟨_, R, expr⟩ ← inferTypeQ' expr
let inst ← synthInstanceQ q(Semifield $R)
```

#### Type Mismatches in q(...)
```lean
-- Problem: Type mismatch in quotation
-- Solution: Ensure all subexpressions have correct types
have a : Q($R) := ...  -- NOT just Expr
have b : Q($R) := ...
have sum : Q($R) := q($a + $b)
```

#### Assignment Context Issues
```lean
-- Always assign metavariables in their context
mvar.mvarId!.withContext do
  have proof : Q($P) := ...
  mvar.mvarId!.assign proof
```

## Best Practices Summary

### Standard Metaprogramming
1. **Use `mkAppM` whenever possible** - it handles implicit arguments and instance synthesis
2. **Create metavariables for unknown arguments** - let the tactic system handle proof obligations
3. **Work within goal contexts** - use `goal.withContext` for local operations
4. **Synthesize instances explicitly when needed** - but let `mkAppM` handle it when possible
5. **Use `mkConstWithFreshMVarLevels`** for polymorphic constants

### Qq-Specific Best Practices
1. **Use `have` instead of `let`** for Qq expressions to avoid originating info issues
2. **Use `inferTypeQ'` when synthInstanceQ fails** to get proper type references
3. **Be explicit about types in q(...)** - especially for numeric literals
4. **Prefer typed expressions throughout** - provides compile-time checking
5. **Remember casting is unchecked** - be careful when redeclaring types
6. **Use `assumeInstancesCommute`** when dealing with complex instance hierarchies

### General Best Practices
1. **Trace liberally during development** - understanding what expressions you're building is crucial
2. **Handle errors gracefully** - metaprogramming operations can fail
3. **Prefer batch operations** - they're more efficient than many small operations
4. **Test incrementally** - build and test small pieces before combining