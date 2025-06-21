# Linearize Tactic Design Document

## Overview
The `linearize` tactic transforms exponential inequalities of the form `a < (b : R)^z` (where `b` is a natural number base, `z` is an integer exponent, and `R` is a linear ordered field) into logarithmic form using `Int.log` to make them suitable for `linarith`.

## Motivation
Lean's `linarith` tactic is effective at solving linear arithmetic goals, but it cannot handle exponential expressions directly. By converting exponential inequalities to logarithmic form, we can leverage `linarith`'s capabilities for a broader class of problems.

## Key Components

### 1. Core Function: Int.log
- **`Int.log`** (from `Mathlib.Data.Int.Log`): Integer logarithm for fields
  - Definition: `Int.log b r` = greatest `k` such that `(b : R)^k ≤ r`
  - Works for any linear ordered field with floor semiring (ℝ, ℚ, etc.)
  - Handles both positive and negative values appropriately
  - Returns 0 for `r ≤ 0` or `b ≤ 1`

### 2. Key Theorems for Transformation

Core inequalities:
- `Int.zpow_log_le_self`: `(b : R) ^ (Int.log b r) ≤ r` when `0 < r` and `1 < b`
- `Int.lt_zpow_succ_log_self`: `r < (b : R) ^ (Int.log b r + 1)` when `1 < b`
- `Int.log_zpow`: `Int.log b ((b : R) ^ z) = z` when `1 < b`
- `Int.log_mono_right`: `Int.log b` is monotone for positive arguments

These theorems give us the key relationships:
- If `a < (b : R)^z` and `0 < a`, then `Int.log b a < z`
- If `(b : R)^z < a` and `0 < a`, then `z < Int.log b a + 1`
- Similar relationships hold for `≤`, `≥`, `>`

### 3. Tactic Implementation Pattern

Based on mathlib tactics, the implementation should follow this pattern:

```lean
syntax (name := linearize) "linearize" (ppSpace colGt term)* : tactic

elab_rules : tactic
  | `(tactic| linearize $[$targets]*) => do
    -- Implementation here
```

### 4. Core Algorithm

1. **Parse targets**: Extract expressions to transform (or use all hypotheses and goal if none specified)

2. **Identify exponential patterns**: Find subexpressions of the form `(b : R)^z` where:
   - `b` is a natural number constant (typically 2, 10, etc.)
   - `z` is an integer expression (using `zpow`)
   - `R` is a linear ordered field

3. **Transform inequalities**:
   - `a < (b : R)^z` → `Int.log b a < z` (when `0 < a`, `1 < b`)
   - `(b : R)^z < a` → `z < Int.log b a + 1` (when `0 < a`, `1 < b`)
   - `a ≤ (b : R)^z` → `Int.log b a ≤ z` (when `0 < a`, `1 < b`)
   - `(b : R)^z ≤ a` → `z ≤ Int.log b a` (when `0 < a`, `1 < b`)
   - For equality: `a = (b : R)^z` → `a = (b : R)^z ∧ Int.log b a = z` (when `0 < a`, `1 < b`)

4. **Handle edge cases**:
   - Non-positive values: `Int.log` returns 0 for `r ≤ 0`, may need to add positivity hypotheses
   - Base ≤ 1: Skip transformation or report error
   - Mixed positive/negative: May need case analysis

5. **Generate proofs**: For each transformation, construct a proof using the appropriate theorem from `Int.log`

### 5. Helper Functions Needed

```lean
-- Check if expression is of form (b : R)^z using zpow, where b is a nat cast
def isNatCastZpow (e : Expr) : MetaM (Option (ℕ × Expr × Expr × Expr))

-- Transform a comparison involving zpow expressions
def transformZpowComparison (e : Expr) : MetaM (Option (Expr × Expr))

-- Generate proof of transformation using Int.log theorems
def proveZpowTransformation (original transformed : Expr) : MetaM Expr

-- Check if we can apply linearize to a zpow expression  
def canLinearizeZpow (e : Expr) : MetaM Bool

-- Note: isNatCastZpow should return (b : ℕ, base_expr : Expr, exponent : Expr, field_type : Expr)
-- where base_expr is the full (b : R) expression
```

### 6. Integration with linarith

After transformation, the tactic should:
1. Add the transformed inequalities as new hypotheses
2. Optionally call `linarith` to solve the goal
3. Clean up temporary hypotheses if needed

## Example Usage

```lean
example (a : ℝ) (h : 1 < a) (h2 : a < 2^100) : a < 2^200 := by
  linearize h2  -- transforms to: Int.log 2 a < 100
  -- Now linarith can handle it
  linarith

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) 
    (h1 : 2^10 ≤ x) (h2 : x < 2^20) (h3 : 2^15 ≤ y) : 2^9 < x * y := by
  linearize h1 h2 h3
  -- Transforms to: 10 ≤ Int.log 2 x, Int.log 2 x < 20, 15 ≤ Int.log 2 y
  -- Then using log_mul: Int.log 2 (x * y) = Int.log 2 x + Int.log 2 y
  linarith
```

## Implementation Steps

1. Create basic syntax and elaboration rules
2. Implement pattern matching for exponential expressions
3. Add transformation logic for each comparison type
4. Implement proof generation using appropriate theorems
5. Add edge case handling
6. Test with various examples
7. Add optimization for common patterns
8. Document usage and limitations

## Potential Extensions

1. Support for more general exponential expressions (not just integer exponents)
2. Automatic detection of which hypotheses to transform
3. Integration with other tactics beyond linarith
4. Support for logarithms with non-integer bases
5. Handling of more complex expressions involving products and quotients