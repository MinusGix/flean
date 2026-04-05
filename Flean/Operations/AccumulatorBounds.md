# Hierarchical Accumulator Error Bounds — Design Document

## Context

The library has a generic error bound framework for accumulator algorithms
(algorithms that fold `next = f(acc, input)` over a list). The framework
lives in `AffineFoldInstances.lean` and currently provides:

- **Exact decomposition**: `final + hornerPoly(errors, 0, x) = exact`
- **Per-index bound**: `|hornerPoly(errors, 0, x)| ≤ weightedErrorSum |x| errors`
- **Weighted error sum collapse**: `weightedErrorSum κ errors ≤ ((1+α)^n - 1) · P`
- **Master composition**: `accumulator_error_bound` (one-line final theorem)

Instantiated for Horner (κ=|x|, α=(1+η)²-1), HornerFMA (κ=|x|, α=η),
DotProduct (κ=1, α=(1+η)²-1), DotProductFMA (κ=1, α=η).

### The problem

The framework gives `((1+η)^{2n}-1)` for two-operation algorithms (mul+add),
but manual proofs achieve `((1+η)^n-1)` by tracking the two errors separately.
The root cause: the current model uses a single `α` for both the error bound
and magnitude growth, conflating two distinct quantities.


## The structural insight: triangular 2D recurrence

Every accumulator error analysis has the same hidden structure: a **triangular**
2D recurrence. The state is `(mag_k, bound_k)` where `mag_k = |acc_k|` is the
FP accumulator magnitude and `bound_k` is the running error bound:

```
[mag_{k+1}  ]   [(1+β_acc)·κ,      (1+β_off)  ] [mag_k ]   
[bound_{k+1}] ≤ [α_acc·κ,          κ           ] [bound_k]
                                                             
                 + offset injection terms
```

Key properties of this matrix:

1. **Triangularity**: magnitude evolves independently of the error bound.
   Error depends on magnitude, not vice versa. This means we never need
   full eigendecomposition — the eigenvalues are just the diagonal entries.

2. **Composition IS matrix multiplication**: if algorithm A has step matrix
   `M_A` and B has `M_B`, the composed system is `M_B^m · M_A^n`. Triangular
   times triangular stays triangular.

3. **The output is naturally two terms**: the two components of `M^n · v₀`
   give separate growth rates for the init-inherited term and the
   offset-injected term. Collapsing to one term loses information.

4. **The gauge/norm choice is the matrix norm**: our existing `AffineFold`
   gauge framework is choosing which norm to measure `M^n` in. Spectral
   radius gives tight asymptotics, operator norm gives concrete finite-n bounds.

This also predicts what should be easy and what should be hard:
- **Easy**: single affine map per step (Horner, dot product, Clenshaw, summation).
  The matrix is constant across steps.
- **Hard**: variable-coefficient recurrences, adaptive methods. Need per-step
  matrices and `‖M_n · M_{n-1} · ... · M_1‖` — genuinely harder.
- **Interesting**: algorithms where `κ < 1` (Newton iteration). Both eigenvalues
  are < 1, so geometric sums converge, giving *contraction* bounds from the
  same framework.


## `geomBound`: the fundamental quantity

### Definition

```lean
/-- Accumulated geometric bound: `α · Σ_{k=0}^{n-1} (1+β)^k`.
    The natural quantity arising from n steps with error rate α
    and magnitude growth rate β. -/
noncomputable def geomBound (α β : R) (n : ℕ) : R :=
  α * (Finset.range n).sum (fun k => (1 + β) ^ k)
```

### Core API

```lean
-- Structural
geomBound_zero     : geomBound α β 0 = 0
geomBound_succ     : geomBound α β (n+1) = geomBound α β n + α · (1+β)^n
geomBound_one      : geomBound α β 1 = α

-- Closed forms
geomBound_uniform  : geomBound α α n = (1+α)^n - 1                    -- bridge to current
geomBound_eq_div   : 0 < β → geomBound α β n = (α/β) · ((1+β)^n - 1) -- classical form
geomBound_zero_β   : geomBound α 0 n = n · α                          -- no growth

-- Monotonicity
geomBound_mono_α   : α₁ ≤ α₂ → geomBound α₁ β n ≤ geomBound α₂ β n
geomBound_mono_β   : 0 ≤ α → β₁ ≤ β₂ → geomBound α β₁ n ≤ geomBound α β₂ n
geomBound_mono_n   : 0 ≤ α → 0 ≤ β → n ≤ m → geomBound α β n ≤ geomBound α β m

-- Positivity
geomBound_nonneg   : 0 ≤ α → 0 ≤ β → 0 ≤ geomBound α β n

-- Composition (the key structural lemma)
geomBound_add      : geomBound α β (m + n) =
                       geomBound α β m · (1+β)^n + geomBound α β n

-- Power identity (used in inductive proofs)
geomBound_step     : (1+β)^n · α + geomBound α β n = geomBound α β (n+1)
```

### Why `geomBound` earns its definition

1. **`geomBound_uniform`** is the bridge: the current framework's `((1+α)^n - 1)`
   is literally `geomBound α α n`. All existing theorems can be restated.

2. **`geomBound_add`** makes composition a one-liner. Currently composing two
   algorithms requires manually expanding `(1+α)^m · (1+α)^n` identities.
   With `geomBound`, just apply the composition lemma.

3. **Division-free**: avoids `α/β` in the core development. The `_eq_div`
   lemma is available when you want the classical form, but proofs work
   inductively via `_succ` and `_step` without ever dividing.

4. **Handles β=0 uniformly**: `geomBound α 0 n = n·α` falls out from
   the definition without a special case.


## The four-parameter model (`AccumStep`)

### Structure

```lean
/-- A triangular step model for accumulator error analysis.
    Parameters for the 2D recurrence on (magnitude, error). -/
structure AccumStep (R : Type*) where
  κ      : R   -- propagation rate (|x| for Horner, 1 for dot product)
  α_acc  : R   -- error rate on accumulator component: |e_k| involves α_acc · κ · |acc_k|
  α_off  : R   -- error rate on offset component:      |e_k| involves α_off · |offset_k|
  β      : R   -- magnitude growth rate: |acc_{k+1}| ≤ (1+β) · M_k
```

Note: β is a single parameter, not split into β_acc/β_off. In practice,
the magnitude bound is always of the form `|next| ≤ (1+β) · (κ·|acc| + |offset|)`
(possibly with different coefficients on acc vs offset, but the framework
absorbs the difference by taking the max). This keeps the model at four
parameters without loss for any algorithm we've encountered.

Actually, looking at the DotProduct case more carefully:

```
|next_k| ≤ (1+η)·|acc_k| + (1+η)²·|xy_k|
```

This is NOT `(1+β)·(|acc| + |xy|)` for any single β. It's `(1+η)·|acc| + (1+η)²·|offset|`.
The coefficients on acc and offset are different. To fit the framework, we either:

(a) Take β = (1+η)²-1 (max), losing the tight acc growth → exponent 2n (current)
(b) Use inflated offsets: offset' = (1+η)·|xy|, then (1+η)·(|acc| + offset') works → β = η
(c) Allow β_acc ≠ β_off in the framework

Option (b) is elegant and keeps the framework simple. Option (c) is the "true" four-parameter
model. Let's support both:

```lean
/-- Full four-parameter step model. -/
structure AccumStepFull (R : Type*) where
  κ      : R
  α_acc  : R   -- error rate on acc:    |e_k| ≤ α_acc · κ · mag_k + α_off · off_k
  α_off  : R   -- error rate on offset
  β_acc  : R   -- magnitude growth on acc: |next| ≤ (1+β_acc) · κ · mag_k + (1+β_off) · off_k
  β_off  : R   -- magnitude growth on offset
```

### Per-step hypotheses

Given `AccumStepFull s`:
```
|error_k| ≤ s.α_acc · s.κ · mag_k + s.α_off · offset_k

mag_{k+1} ≤ (1 + s.β_acc) · s.κ · mag_k + (1 + s.β_off) · offset_k
```

### Two-term output

The bound has **two terms** with different growth rates:

```
|final - exact| ≤ A(n) · |init| + Σ_k B(n-k) · |offset_k|
```

where:
- `A(n)` = init-inherited error (grows as `(1+β_acc)^n` scaled by α_acc)
- `B(j)` = offset-injected error at distance j (involves both α_acc, α_off, and both β's)

For the triangular system, working through the recurrence:

```
A(n) = geomBound α_acc β_acc n · κ^n

B(j) = α_off · (1 + β_acc)^j · κ^j  +  α_acc · (contribution from offset flowing through acc)
```

This gets complicated in the fully general case. The clean path is:

### Recommended: two-level approach

**Level A**: The `AccumStepFull` theorem with two-term output. Proved once.
This is the most general and captures the exact structure.

**Level B**: Wrappers that simplify to one-term output for common cases:
- `uniform` (1 param): `α_acc = α_off = β_acc = β_off = α`
- `split_αβ` (2 params): `α_acc = α_off = α`, `β_acc = β_off = β`
- `inflated` (2 params + offset transform): `α_acc = β_acc = β`, offsets pre-multiplied
- `full` (4 params): two-term output


## Instantiation table

| Algorithm     | κ    | α_acc | α_off    | β_acc | β_off    | Exponent | Constant |
|---------------|------|-------|----------|-------|----------|----------|----------|
| Horner        | \|x\|| η     | (1+η)²-1| η     | (1+η)²-1| 2n       | 1        |
| HornerFMA     | \|x\|| η     | η        | η     | η        | n        | 1        |
| DotProduct    | 1    | η     | (1+η)²-1| η     | (1+η)²-1| n        | ≈1 (two-term) |
| DotProductFMA | 1    | η     | η        | η     | η        | n        | 1        |

For DotProduct with the full model: the init term grows as `(1+η)^n` (exponent n,
from β_acc = η), and each offset term gets its own factor. The two-term output
matches the manual proof's `((1+η)^n-1)·|init| + ((1+η)^{n+1}-1)·Σ|xy|`.

For Horner: α_acc = η (the add error on acc) but α_off = (1+η)²-1 (the mul error
inflates the coefficient). Since the offset in Horner IS the polynomial coefficient
(which doesn't grow), the large α_off just means each coefficient's contribution
is amplified by (1+η)²-1 ≈ 2η instead of η. The exponent stays 2n because
β_off = (1+η)²-1 as well — the magnitude genuinely grows at this rate due to
the multiplication.

**Key observation**: Horner *cannot* improve beyond 2n exponent in this framework.
The multiplication genuinely amplifies both the acc and the offset by (1+η). The
2n exponent is real — it reflects that each step has two roundings. Only FMA
(single rounding) achieves n. The DotProduct case is special because κ=1: the
"multiplication" (x_k · y_k) doesn't multiply the *accumulator*, so the acc
growth is only η (from the add), even though the offset growth is (1+η)²-1.


## Implementation plan

### Part 1: `geomBound` definition + API (~80 lines)

**File**: `AffineFoldInstances.lean` or a new `GeomBound.lean`

New file is probably cleaner since `geomBound` is pure algebra (no FP, no traces).

```lean
-- Flean/Operations/GeomBound.lean
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GeomBound

variable {R : Type*} [LinearOrderedField R]

noncomputable def geomBound (α β : R) (n : ℕ) : R :=
  α * (Finset.range n).sum (fun k => (1 + β) ^ k)

-- Core API (~15 theorems, see list above)
-- All pure algebra, should be straightforward for Codex

end GeomBound
```

**Codex task**: Define `geomBound` and prove the full API listed above.
Particularly important: `geomBound_uniform`, `geomBound_add`, `geomBound_step`.

### Part 2: Core four-parameter theorem (~120 lines)

**File**: `AffineFoldInstances.lean` (new section)

The inductive proof mirrors `weightedErrorSum_le_of_relative_errors` but with
the split parameters. The key algebraic step uses `geomBound_step` instead of
the manual power identity.

```lean
/-- Four-parameter accumulator error bound.
    Two-term output: separate bounds for init-inherited and offset-injected error. -/
theorem weightedErrorSum_le_of_general_step
    (κ α_acc α_off β_acc β_off : R)
    (hκ : 0 ≤ κ) (hα_acc : 0 ≤ α_acc) (hα_off : 0 ≤ α_off)
    (hβ_acc : 0 ≤ β_acc) (hβ_off : 0 ≤ β_off)
    (errors offsets : List R) (mags : ℕ → R)
    (hlen : errors.length = offsets.length)
    (hoffsets : ∀ c ∈ offsets, 0 ≤ c)
    (hmags_nn : ∀ k, 0 ≤ mags k)
    (herr : ∀ k (hk : k < errors.length),
        |errors[k]| ≤ α_acc * κ * mags k + α_off * offsets[k]'(by omega))
    (hrecur : ∀ k (hk : k < errors.length),
        mags (k + 1) ≤ (1 + β_acc) * κ * mags k + (1 + β_off) * offsets[k]'(by omega)) :
    weightedErrorSum κ errors ≤
      geomBound α_acc β_acc errors.length * κ ^ errors.length * mags 0 +
      hornerPoly (offsets.map (fun c => geomBound_offset_coeff α_acc α_off β_acc β_off c ...)) 0 κ
```

**Note**: The exact shape of the offset term needs working out. The offset
contribution at step k, propagated through n-k remaining steps, is:

```
κ^{n-1-k} · (α_off · offset_k + α_acc · (accumulated offset-to-acc contribution))
```

This may simplify to:
```
weightedErrorSum κ errors ≤
    geomBound α_acc β_acc n · κ^n · init +
    Σ_k  (α_off · (1+β_acc)^{?} + α_acc · ...) · κ^{n-1-k} · offset_k
```

The exact closed form for the offset term depends on whether `β_acc = β_off`.
When they're equal (common case), the offset term collapses cleanly.

**Alternative (simpler)**: State the theorem with a **single** upper bound
that dominates both terms:

```lean
    weightedErrorSum κ errors ≤
      geomBound (max α_acc α_off) (max β_acc β_off) errors.length *
        hornerPoly offsets (mags 0) κ
```

This loses some tightness but is dramatically simpler to prove and state.
The tight two-term version can be a separate theorem.

**Codex task**: Prove the single-bound version first (easier induction),
then attempt the two-term version.

### Part 3: Wrappers (~40 lines)

```lean
-- Current API: special case α_acc = α_off = β_acc = β_off = α
theorem weightedErrorSum_le_of_relative_errors' :=
  -- apply general, show geomBound α α n = (1+α)^n - 1

-- Split-α: α_acc = α_off = α, β_acc = β_off = β  
theorem weightedErrorSum_le_of_split_errors :=
  -- apply general, simplify

-- Inflated offset: convenience for two-operation algorithms
theorem weightedErrorSum_le_of_inflated_offsets :=
  -- apply current with transformed offsets
```

### Part 4: Re-derive existing bounds (~50 lines)

Show each existing algorithm bound follows from the new framework.
This is validation — the proofs should be short applications of wrappers.

### Part 5: DotProduct tight bound (~30 lines)

Instantiate the four-parameter model for DotProduct:
- `α_acc = η, α_off = (1+η)²-1, β_acc = η, β_off = (1+η)²-1`
- Two-term output: `((1+η)^n-1)·|init| + ((1+η)^{n+1}-1)·Σ|xy|`
- Matches manual proof exactly (or within a negligible factor)


## Composition with `geomBound`

The `geomBound_add` lemma makes algorithm composition clean:

```
geomBound α β (m + n) = geomBound α β m · (1+β)^n + geomBound α β n
```

**Interpretation**: The error from a composed A→B pipeline (m steps of A, then
n steps of B, same parameters) is:
- A's error `geomBound α β m`, propagated through B's n steps: `· (1+β)^n`
- Plus B's own error: `+ geomBound α β n`

For **different** parameters (A uses `α_A, β_A`; B uses `α_B, β_B`):
```
total_error ≤ geomBound α_A β_A m · (1+β_B)^n · (κ_B/κ_A)^n + geomBound α_B β_B n
```

This is the A→B composition theorem. The `(κ_B/κ_A)^n` factor handles
propagation rate changes between algorithms.


## Open questions

1. **Should `geomBound` go in its own file?** It's pure algebra with no FP
   dependency. A standalone file makes it reusable and keeps imports clean.
   Recommendation: yes, `Flean/Operations/GeomBound.lean`.

2. **Two-term vs one-term output for the core theorem?** The two-term version
   is tighter but harder to state. Options:
   - Prove two-term, derive one-term as corollary (cleanest, more work)
   - Prove one-term with `max`, add two-term later if needed (pragmatic)
   Recommendation: one-term with `max` first. Two-term is an optimization.

3. **Replace existing `((1+α)^n - 1)` with `geomBound` everywhere?** This
   would unify the notation but touch many files. Options:
   - Keep both, with a bridge lemma `geomBound_uniform`
   - Gradually migrate as files are touched
   Recommendation: bridge lemma, gradual migration.

4. **Mathlib linear algebra connection?** The triangular structure could be
   formalized as `Matrix (Fin 2) (Fin 2) R` with `upperTriangular` proofs.
   Pros: gets Mathlib's matrix norm and spectral theory. Cons: coercion
   pain, `Fin` indexing overhead for a 2×2 system. The 2×2 case is simple
   enough to inline. Save the matrix connection for when we generalize to
   higher-order jets (k×k triangular systems).
   Recommendation: don't use Mathlib matrices for 2×2. Note the connection
   for future k-jet generalization.


## Codex work breakdown

### Batch 1: `geomBound` (independent, pure algebra)
- **Input**: definition + API signatures from Part 1 above
- **Expected difficulty**: straightforward, mostly `Finset.sum` manipulation
- **Key lemmas to stress-test**: `geomBound_uniform`, `geomBound_add`

### Batch 2: Core four-parameter theorem (depends on Batch 1)
- **Input**: theorem statement + proof sketch from Part 2
- **Expected difficulty**: moderate — the induction is similar to the existing
  `weightedErrorSum_le_of_relative_errors` but with more bookkeeping
- **Fallback**: if the two-term version is too hard, start with one-term `max`

### Batch 3: Wrappers + re-derivation (depends on Batch 2)
- **Input**: wrapper signatures + existing algorithm parameters
- **Expected difficulty**: easy — short applications of the core theorem
- **Validation**: each wrapper should reproduce the existing bound exactly

### Batch 4: DotProduct tight bound (depends on Batch 3)
- **Input**: per-step bounds from `dp_step_combined_error` + framework API
- **Expected difficulty**: easy if framework is working
- **Validation**: compare with manual `dp_error_bound` — should match or be
  within (1+η) factor
