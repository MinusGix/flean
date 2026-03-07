# BoundCalc Tactic — Design Document

## Motivation

Floating-point termination proofs and error analyses frequently involve bounding products:

```
a * b ≤ c * d    (given a ≤ c and b ≤ d, with appropriate sign conditions)
```

Currently each such step requires manually invoking `mul_le_mul` with 4 arguments
(two bounds + two positivity proofs), or `mul_le_mul_of_nonneg_right/left` with 2.
This is the most common source of proof verbosity after power monotonicity (which
`linearize` now handles).

## What exists

### `gcongr`
Mathlib's `gcongr` tactic decomposes monotonicity goals structurally:
- `a * b ≤ c * d` → subgoals `a ≤ c` and `b ≤ d` (matched by unification)
- Handles nested products, one-sided, strict, ℕ/ℝ/ℚ
- Dispatches nonnegativity via `positivity`
- **Limitation:** requires LHS and RHS to have the same syntactic factor structure

### `nlinarith`
Nonlinear arithmetic — multiplies pairs of hypotheses to generate degree-2 terms:
- Handles 2-factor regrouped products: `6*D*den*num ≤ 3*ab²*2^L` ✓
- **Limitation:** degree-2 only, fails on 3+ factor products

### `polyrith`
Shut down (relied on external service). Not available.

## Algorithm

### Overview

Given a goal `LHS ≤ RHS` (or `<`) where both sides are products:

1. **Fast path:** Try `gcongr` dispatch (Phase 1, already implemented)
2. **Medium path:** Try `nlinarith` (handles 2-factor regrouping for free)
3. **Full path:** Factor matching algorithm (described below)

### Step 1: Factor extraction

Walk each side's Expr tree, splitting on `HMul.hMul`, to get flat factor lists.
Treat non-`*` subexpressions as atomic (including `2^L`, `ab^2`, etc.).

```
6 * D * den * num  →  [6, D, den, num]
3 * ab^2 * 2^L     →  [3, ab^2, 2^L]
```

Don't use `ring_nf` on the whole expression — it would expand powers and lose
structure. Factor extraction is purely syntactic tree-walking.

### Step 2: Hypothesis scanning

Scan the local context for hypotheses of the form `X ≤ Y` or `X < Y`.
For each, extract factors of both sides:

```
h6D : 6 * D ≤ 3 * 2^L   →  BoundHyp([6, D], [3, 2^L], h6D, nonstrict)
hdp : den * num ≤ ab^2   →  BoundHyp([den, num], [ab^2], hdp, nonstrict)
```

Also synthesize trivial bounds:
- Reflexive: `x ≤ x` for any factor appearing on both sides
- Constant: `457 ≤ 500` checkable by `norm_num`/`omega`
- Power: `2^e1 ≤ 2^e2` checkable by `linearize`

### Step 3: Factor matching (the core algorithm)

Find a way to partition LHS factors and RHS factors into matched groups,
where each group pair is covered by a hypothesis (or trivial bound).

**Formally:** Given `LHS_factors = [l₁, ..., lₘ]` and `RHS_factors = [r₁, ..., rₙ]`,
find sets of bounds `{(L₁, R₁, h₁), ..., (Lₖ, Rₖ, hₖ)}` such that:
- Each `Lᵢ` is a subset of LHS_factors, each `Rᵢ` is a subset of RHS_factors
- The `Lᵢ` partition LHS_factors, the `Rᵢ` partition RHS_factors
- Each `hᵢ` proves `∏Lᵢ ≤ ∏Rᵢ` (or is verifiable as such)

**Search strategy:** Recursive binary decomposition.

```
match(lhs_factors, rhs_factors):
  -- Base: check if a single hypothesis covers everything
  for h in hypotheses:
    if h.lhs_factors == lhs_factors && h.rhs_factors == rhs_factors:
      return h

  -- Recursive: split into two groups
  for (lhs_left, lhs_right) in binary_partitions(lhs_factors):
    for (rhs_left, rhs_right) in binary_partitions(rhs_factors):
      if match(lhs_left, rhs_left) && match(lhs_right, rhs_right):
        return combine(...)
```

With 2-4 factors per side, the number of binary partitions is tiny:
- 2 factors: 1 way to split
- 3 factors: 3 ways
- 4 factors: 7 ways

Factor comparison uses `isDefEq` (up to definitional equality). For factors
that don't match definitionally but are equal by `ring`, we'd need a ring
check — but in practice, our factors are atomic expressions that match exactly
or not at all.

### Step 4: Proof construction

Once a matching is found, construct a `calc` proof:

```lean
calc LHS
    = (∏L₁) * (∏L₂) * ... := by ring
  _ ≤ (∏R₁) * (∏R₂) * ... := by
      apply mul_le_mul h₁ (mul_le_mul h₂ h₃ ...) (by positivity) (by positivity)
  _ = RHS := by ring
```

The two `ring` steps handle regrouping. The middle step chains `mul_le_mul`
applications. Nonnegativity goals are dispatched by `positivity`.

### Step 5: Nonnegativity

Each `mul_le_mul` application requires showing the RHS of one bound and
the LHS of the other are nonneg. Dispatch chain:
`positivity | assumption | linarith | omega | norm_num`

## Execution order

`bound_calc` tries approaches in order of increasing cost:

1. **`gcongr` dispatch** (Phase 1) — microseconds, handles aligned products
2. **`nlinarith`** — milliseconds, handles 2-factor regrouping
3. **Factor matching** (Phase 3) — milliseconds, handles arbitrary regrouping

If all fail, leave the goal for the user.

## Syntax

```lean
-- Basic: try all approaches automatically
bound_calc

-- With hint hypotheses (Phase 3 can prioritize these in matching)
bound_calc [h1, h2, h3]
```

## Scope decisions

**In scope:**
- `a * b ≤ c * d` and variants with ≤, <, nested products
- Factor regrouping via `ring`
- Nonnegativity dispatch via `positivity` / `linarith`
- Integration with `linearize` for power factor subgoals
- ℝ, ℚ, ℕ, ℤ domains

**Out of scope (for now):**
- Division: `a/b ≤ c/d` (anti-monotone in denominator, different lemmas)
  Could add later by rewriting `a/b` as `a * b⁻¹` and handling `inv_le_inv`
- Chain composition (Phase 4): multi-step `calc` chains through intermediate products
  The user writes the `calc` structure; `bound_calc` closes each step
- Sum bounds: `a + b ≤ c + d` (already handled by `linarith` / `gcongr`)

## Implementation status

1. ✅ Phase 1: `gcongr` + dispatch chain (done, ~15 lines)
2. ✅ Factor extraction: walk Expr tree, split on `*` (~30 lines)
3. ✅ Hypothesis scanning: scan context for `≤`/`<` hypotheses, extract factors (~40 lines)
4. ✅ Factor matching: recursive binary partition search (~80 lines)
5. ✅ Proof construction: `mul_le_mul` chain + `linarith` (~70 lines)
6. ✅ Integration: Phase 3 → Phase 1 → nlinarith fallback (~20 lines)
7. 🔄 Test on codebase patterns, iterate

Total: ~250 lines of metaprogramming.

## Roadmap (next improvements)

### R1: Synthesized trivial bounds (HIGH)
Factor matching currently only uses context hypotheses. Add synthesis of:
- **Reflexive:** `x ≤ x` for any factor appearing on both sides
- **Constant:** `457 ≤ 500` checkable by `norm_num`/`omega`
- **Power:** `2^e₁ ≤ 2^e₂` checkable by `linearize`

This removes the need for users to explicitly state obvious factor bounds.

**Codebase motivation:** OddInterval.lean has `Nat.mul_le_mul_left _ hd_le` where
one factor is bounded by hypothesis and the other factor is identical on both sides.
LogTermination.lean has `457 * ab^3 * 2^ab ≤ 500 * ab^3 * 2^ab`.

### R2: Extensible dispatch chain (MEDIUM) ✅ DONE
Added lemma-based dispatch for power bounds:
- `Nat.one_le_two_pow` → handles `1 ≤ 2^n`
- `Nat.one_le_pow _ _ (by omega)` → handles `1 ≤ m^n` for concrete `m ≥ 1`

Added to both Phase 1 gcongr dispatch and Phase 3 synthesis.
Unblocked P1.6 and NP.6 test cases.

Long-term: `@[bound_calc_dispatch]` attribute for external lemma registration.

### R3: Strict inequality support in factor matching (MEDIUM) ✅ DONE
Factor matching now handles both `≤` and `<` goals:
- `<` hypotheses tracked with `isStrict = true` through matching
- For `≤` goals with `<` hypotheses: wraps with `le_of_lt`
- For `<` goals: uses `mul_lt_mul` (left-strict) or `mul_lt_mul'` (right-strict)
- Strictness "spent" at first opportunity in multi-group chains

**Note:** `mul_lt_mul` needs `0 < c` (not just `0 ≤ c`) for the second factor.
Unblocked SI.3, SI.4, P1.7, plus new SI.6/SI.7/SI.8 tests.

### R4: Division support (LOW)
Rewrite `a / b` as `a * b⁻¹` and handle `inv_le_inv` for the inverted factor.
Or recognize `div_le_div_of_nonneg_right` patterns directly.

**Codebase motivation:** RoundNormal.lean has `div_le_div_of_nonneg_right` inside
`mul_le_mul_of_nonneg_right` patterns.

### R5: Calc step integration (LOW)
Most `mul_le_mul` calls live inside `calc` blocks. Could `bound_calc` close
individual calc steps? It already can — the user writes the calc structure,
`bound_calc` closes each `_ ≤ _` step. No special support needed beyond
making the tactic robust enough.

## Open questions

- **Hint syntax:** `bound_calc [h1, h2]` to guide matching, or just auto-search?
- **Timeout:** Factor matching is exponential in theory but tiny in practice (≤4 factors).
  Depth limit of 8 is the current safety valve.
- **Partial coverage:** If matching covers only some factors, should we leave
  subgoals for the remaining ones? Or require full coverage? Full coverage is simpler.
