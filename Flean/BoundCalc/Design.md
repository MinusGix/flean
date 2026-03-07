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

## What exists: `gcongr`

Mathlib's `gcongr` tactic handles the structural decomposition well:

**What it handles (tested):**
- `a * b ≤ c * d` with hypotheses `a ≤ c`, `b ≤ d` — finds bounds by unification
- Nested products: `a * b * c ≤ A * B * C` — recurses automatically
- One-sided: `a * b ≤ c * b` — recognizes `b = b`, only needs `a ≤ c`
- Strict one-sided: `a * b < c * b` — handles `<` on the varying factor
- Natural numbers: works for `ℕ` products too
- Dispatches nonnegativity side goals via `positivity`

**Where it falls short:**
- Subgoals beyond `positivity`: when side goals need `omega`, `norm_num`,
  `linearize`, or domain-specific lemmas (e.g., `1 ≤ 2^ab`), gcongr leaves
  them unsolved
- Needs fully stated goal (both LHS and RHS known) — can't synthesize the RHS
- No ring normalization — if factors are grouped differently on LHS vs RHS, fails
- No transitivity chaining through intermediate products

**Bottom line:** `gcongr` already covers Phase 1's structural decomposition.
The real gap is in the subgoal dispatch and the more advanced phases.

## Feature phases

### Phase 1: `gcongr` + rich subgoal dispatch
`bound_calc` = `gcongr` followed by a subgoal dispatch chain:
`assumption | exact le_refl _ | positivity | omega | norm_num | linearize | linarith`

This is essentially a one-line macro but covers the actual gap: gcongr
leaves subgoals that need omega/linearize, and users currently write out
the full `mul_le_mul h1 h2 (by positivity) (by positivity)` instead.

**Estimated coverage:** ~20 sites where `mul_le_mul` is called explicitly.

**Implementation:** Trivial — literally `gcongr <;> ...`. Could be a macro.

### Phase 2: Factor matching with hypothesis search
Given `a * b ≤ ?_` (unknown RHS), decompose the LHS into factors, search the
context for upper bounds on each factor, and synthesize the RHS as the product
of those bounds.

```lean
-- Context has: h1 : den ≤ ab, h2 : num ≤ ab
-- Goal: den * num ≤ ?_
-- bound_calc finds h1, h2, produces: den * num ≤ ab * ab
```

**Replaces:** Manual `calc` steps that restructure products just to apply bounds.

### Phase 3: Ring normalization + factor group matching
Handle goals where LHS and RHS have different factor groupings:

```lean
-- Goal: 6 * D * den * num ≤ 3 * 2^L * ab^2
-- After ring normalization: (6*D) * (den*num) vs (3*2^L) * ab^2
-- Match: 6*D ≤ 3*2^L (from h6D) and den*num ≤ ab^2 (from hdp_le)
```

Requires `ring`-normalizing both sides, then matching factor groups against
available hypotheses. Significantly harder than Phase 1-2.

### Phase 4: Chain composition
Compose multiple `≤` steps:

```lean
-- bound_calc [h6D, hdp_le, h3ab2]
-- Automatically chains: 6D·den·num ≤ 3·2^L·ab² ≤ 2^ab·2^L = 2^(ab+L)
```

## Interaction with existing tactics

| Pattern | Current | With bound_calc |
|---------|---------|-----------------|
| `a * b ≤ c * d` (hyps available) | `mul_le_mul h1 h2 (by positivity) (by positivity)` | `by bound_calc` |
| `a * b ≤ c * d` (needs omega) | `gcongr` then manual omega | `by bound_calc` |
| `a * b ≤ c * b` | `mul_le_mul_of_nonneg_right h1 (by positivity)` | `by bound_calc` |
| `a * b < c * d` | `mul_lt_mul h1 h2 (by positivity) (by positivity)` | `by bound_calc` |
| `a / b ≤ c / d` | `div_le_div_of_nonneg_...` | Phase 3+ |
| `a ^ n ≤ b ^ n` | `linearize` handles this | Not needed |
| Regrouped products | Manual `calc` + `ring` | Phase 3+ |

## Implementation plan

1. Phase 1 as macro: `gcongr <;> first | assumption | ...` — test on codebase
2. If Phase 1 covers most sites, evaluate whether Phase 2+ is worth the complexity
3. Phase 2 requires metaprogramming (factor decomposition, context search)
4. Phase 3+ is research-level

## Open questions

- Name: `bound_calc` vs `mono` vs `bound` vs `product_bound`?
  - `mono` is intuitive but might conflict with Mathlib's `@[mono]` attribute
  - `bound_calc` suggests calculation, Phase 1 is more structural
  - `gcongr!` as an enhanced version? Precedent with `linearize!`
- Should it be a standalone tactic or extension to `linearize`/`gcongr`?
- Should `div_le_div` patterns be in scope? (many in LogTermination)
- How to handle mixed `*` and `^` in the same expression?
