# Backward Error Framework — Design Document

## Motivation

The codebase has extensive **forward error** bounds: `|computed - exact| ≤ bound`.
Backward error flips the perspective: the computed result IS the exact answer to a
slightly perturbed problem. This cleanly separates algorithm quality (backward error)
from problem sensitivity (condition number).

**Existing infrastructure to build on:**
- `Gauge` in AffineFold.lean — nonneg, sub-additive function on state types
- `error_distributable` in KahanSum.lean — distributes total error onto per-input perturbations
- `backward_from_forward` in KahanSum.lean — lifts forward bounds to backward form
- `affineFold_exact_decomposition` — `computed + error_fold = exact_fold` pattern
- `kahan_weak_backward_error` — one complete backward error theorem

## Core Idea

A **perturbation gauge** measures how far a perturbed input is from the original.
A **backward error result** says: the computed output equals `f(x')` for some
perturbed `x'` that is close to `x` under the gauge.

The key abstraction levels:

```
PerturbationGauge   — measures input perturbation size
BackwardResult      — strict: computed = f(x'), gauge(x, x') ≤ ε
MixedResult         — general: computed = f(x') + residual
Composition         — compose via pullback/lifting
```

## Structures

### PerturbationGauge

Generalizes the existing `Gauge`. The existing `Gauge` measures `|state|`; a
`PerturbationGauge` measures `|perturbation relative to original|`.

```lean
/-- A perturbation gauge measures how far x' is from x.
    Parameterized so that componentwise, normwise, and weighted
    backward error are all instances. -/
structure PerturbationGauge (X : Type*) (R : Type*) where
  /-- Size of perturbation from x to x'. -/
  dist : X → X → R
  /-- Non-negative. -/
  nonneg : ∀ x x', 0 ≤ dist x x'
  /-- Zero perturbation has zero size. -/
  self : ∀ x, dist x x = 0
```

Key instances:

```lean
/-- Componentwise relative: max_i |x'_i - x_i| / |x_i|.
    For List/Vector inputs. -/
def componentwiseRelGauge : PerturbationGauge (Fin n → R) R where
  dist x x' := Finset.sup' Finset.univ ⟨0, ...⟩
    (fun i => if x i = 0 then 0 else |x' i - x i| / |x i|)

/-- Normwise relative: ‖x' - x‖ / ‖x‖. -/
def normwiseRelGauge (norm : (Fin n → R) → R) : PerturbationGauge (Fin n → R) R where
  dist x x' := if norm x = 0 then 0 else norm (x' - x) / norm x

/-- Weighted: max_i |x'_i - x_i| / w_i for given weights w. -/
def weightedGauge (w : Fin n → R) : PerturbationGauge (Fin n → R) R where
  dist x x' := Finset.sup' Finset.univ ⟨0, ...⟩
    (fun i => if w i = 0 then 0 else |x' i - x i| / w i)
```

Componentwise = `weightedGauge (fun i => |x i|)`.
Normwise = `weightedGauge (fun _ => ‖x‖)`.

### BackwardResult (strict)

```lean
/-- Strict backward error: computed = f(x') for some x' near x.
    Constructive — provides the actual perturbed input. -/
structure BackwardResult {X Y R : Type*}
    (G : PerturbationGauge X R)
    (f : X → Y) (x : X) (computed : Y) where
  /-- The perturbed input. -/
  x' : X
  /-- Exactness: computed result equals f applied to perturbed input. -/
  exact : f x' = computed
  /-- Backward error bound. -/
  eps : R
  /-- The perturbation is bounded. -/
  bound : G.dist x x' ≤ eps
```

### MixedResult (backward + forward residual)

Many algorithms naturally give "nearby input + small residual" rather than
exact backward error. The AffineFold decompositions have exactly this shape:
`computed + error_fold = exact_fold`, i.e., `computed = exact_fold - error_fold`.

```lean
/-- Mixed backward-forward error:
    computed = f(x') + residual, with both perturbation and residual bounded.

    This is the natural form for compensated algorithms where exact backward
    attribution isn't available, and for composition where strict backward
    error may not compose cleanly. -/
structure MixedResult {X Y R : Type*}
    (G_in : PerturbationGauge X R)
    (G_out : Gauge Y R)  -- reuse existing Gauge for output residual
    (f : X → Y) (x : X) (computed : Y) where
  /-- The perturbed input. -/
  x' : X
  /-- The residual. -/
  residual : Y
  /-- Decomposition: computed = f(x') + residual. -/
  decomp : computed = f x' + residual
  /-- Backward error bound on input perturbation. -/
  eps_back : R
  back_bound : G_in.dist x x' ≤ eps_back
  /-- Forward error bound on residual. -/
  eps_fwd : R
  fwd_bound : G_out.val residual ≤ eps_fwd
```

A `BackwardResult` embeds into `MixedResult` with `residual = 0, eps_fwd = 0`.

### Condition Number

```lean
/-- Condition number of f at x, measured by input gauge G_in and output gauge G_out.
    κ(f, x) = sup { G_out(f(x') - f(x)) / G_in(x, x') : x' ≠ x } -/
def conditionNumber (G_in : PerturbationGauge X R) (G_out : Gauge Y R)
    (f : X → Y) (x : X) : R := ...
    -- For practical use: provide concrete values per algorithm rather than
    -- computing the sup. The key theorem is the bridge:
```

The fundamental relation (stated as a theorem, not requiring computation of the sup):

```lean
/-- Forward error ≤ condition number × backward error (first-order).
    For a BackwardResult with bound ε, the forward error is bounded by
    κ · ε + O(ε²). -/
theorem forward_le_cond_mul_backward ...
```

## Composition

### The Pullback/Lifting Interface

The core composition challenge: if A computes `f(x)` with backward error `ε_A`,
and B computes `g(y)` with backward error `ε_B`, what is the backward error of
B(A(x)) for `g(f(x))`?

The answer requires a **pullback**: can perturbations of `f(x)` be realized as
perturbations of `x`?

```lean
/-- A perturbation lift for f: perturbations of f(x) in G_Y can be pulled back
    to perturbations of x in G_X, with amplification factor Λ.

    For linear f, Λ is the condition number.
    For affine f (our AffineFold), Λ comes from the linear part. -/
structure PerturbationLift {X Y R : Type*}
    (G_X : PerturbationGauge X R)
    (G_Y : PerturbationGauge Y R)
    (f : X → Y) (x : X) where
  /-- Amplification factor. -/
  Λ : R
  /-- The lift: given y' near f(x), produce x' near x with f(x') = y'. -/
  lift : (y' : Y) → G_Y.dist (f x) y' ≤ eps →
         { x' : X // f x' = y' ∧ G_X.dist x x' ≤ Λ * eps }
```

For **linear functions**, the lift is always constructible (right inverse).
For **AffineFold** computations, the affine structure gives the lift.
For **nonlinear** functions, the lift may be existential (implicit function theorem).

### Composition Theorem

```lean
/-- Composition of backward-stable algorithms.
    If A is backward stable for f (error ε_A), B is backward stable for g (error ε_B),
    and f has a perturbation lift with factor Λ, then B∘A is backward stable for g∘f
    with error ε_A + Λ·ε_B (first-order). -/
theorem BackwardResult.compose
    (hA : BackwardResult G_X f x (A x))
    (hB : BackwardResult G_Y g (f x) (B (A x)))
    (lift : PerturbationLift G_X G_Y f x) :
    BackwardResult G_X (g ∘ f) x (B (A x)) where
  ...
```

When no lift exists, the composition naturally gives a `MixedResult` instead:

```lean
/-- Composition without lift: produces mixed backward-forward result. -/
theorem MixedResult.compose_no_lift
    (hA : BackwardResult G_X f x (A x))
    (hB : BackwardResult G_Y g (f x) (B (A x))) :
    MixedResult G_X G_Y_out (g ∘ f) x (B (A x)) where
  ...
```

## Connection to Existing Infrastructure

### AffineFold → MixedResult

Every `affineFold_exact_decomposition` immediately gives a `MixedResult`:

```
computed + affineFold L errors 0 = affineFold L vs s
```

Rewrite as:
```
computed = affineFold L vs s - affineFold L errors 0
        = f(x) + (-affineFold L errors 0)
```

So: `x' = x` (no input perturbation!), `residual = -affineFold L errors 0`,
and `eps_fwd` comes from the gauge bounds (`affineFold_gauge_per_index`).

This is a degenerate mixed result (zero backward, all forward). The interesting
case comes when we *choose* to attribute some error backward.

### error_distributable → BackwardResult

For **linear** `f(x) = Σ aᵢxᵢ`, the existing `error_distributable` converts:
```
|E| ≤ ε · Σ|aᵢxᵢ|
```
into constructive per-component perturbations `μᵢ` with `|μᵢ| ≤ ε`.

This gives a `BackwardResult` with componentwise relative gauge:
```
f(x') = computed, where x'_i = (1 + μ_i) · x_i
```

The existing `backward_from_forward` in KahanSum is exactly this bridge.

### Gauge reuse

The existing `Gauge` (AffineFold.lean) measures output/state size.
`PerturbationGauge` measures input perturbation size. They're different concepts
but share the sub-additive structure. We could make `PerturbationGauge` extend
or contain a `Gauge`, but keeping them separate is cleaner since `PerturbationGauge`
takes two arguments (original + perturbed) while `Gauge` takes one.

## Implementation Plan

### Phase 1: Core definitions + linear backward error
**File: `BackwardError.lean`**

1. `PerturbationGauge` structure
2. `BackwardResult` and `MixedResult` structures
3. `BackwardResult.ofMixed` (embed strict into mixed)
4. `MixedResult.ofBackward` (embed backward into mixed with zero residual)
5. Generalize `error_distributable` → `BackwardResult` for linear functions
6. `componentwiseRelGauge` instance

### Phase 2: Instances for existing algorithms
**File: `BackwardError.lean` or per-algorithm files**

7. Summation backward error (new, from existing forward bounds)
8. Dot product backward error (new, bilinear → constructive in each slot)
9. Lift `kahan_weak_backward_error` to use new framework (shows compatibility)

### Phase 3: Composition + condition numbers
10. `PerturbationLift` structure
11. `BackwardResult.compose` theorem
12. `MixedResult.compose_no_lift` theorem
13. Condition number definition + forward ≤ cond × backward bridge

### Phase 4: AffineFold integration
14. Generic `affineFold_mixed_result` from exact decomposition + gauge bounds
15. Horner/Clenshaw/JetHorner as `MixedResult` instances (automatic from AffineFold)
16. Show that for coefficient perturbation (not point perturbation),
    Horner gives a `BackwardResult` via the affine structure

## Design Decisions

**Constructive by default**: `BackwardResult` and `MixedResult` carry the actual
perturbed input `x'`, not just `∃ x', ...`. This matches the existing
`error_distributable` approach and is more useful for composition.

**Mixed as coequal**: Not an afterthought. Many compositions naturally produce
mixed results, and trying to force everything into strict backward form leads
to artificial complexity.

**Gauge-parameterized**: One theorem covers componentwise, normwise, and weighted
cases. The gauge choice is made at instantiation, not in the theorem.

**Separate from Gauge**: `PerturbationGauge` is not a subtype of `Gauge`.
They measure different things (distance vs. size). The output residual in
`MixedResult` uses the existing `Gauge`.

**Phase 1 is self-contained**: Even without composition (Phase 3), having
`BackwardResult` for summation/dot product/Horner is immediately useful — it's
the standard way these results are stated in numerical analysis textbooks.

## Phase 1+2 Status — DONE

~550 lines, fully sorry-free. All items completed:
- `PerturbationGauge`, `uniformGauge`, `trivialGauge`
- `BackwardResult`, `MixedResult`, `BackwardResult.toMixed`
- `error_distributable`, `backwardResult_of_forward_sum_bound`,
  `backwardResult_of_forward_bilinear_bound`, `backwardResult_of_forward_fin_bound`
- `componentwiseCondNumber`, `forward_le_cond_mul_backward`,
  `forward_rel_le_cond_mul_backward`
- `dp_backward_error`, `dp_backward_error_gamma`
- `backward_compose_one_round` (scalar composition)
- `hornerPoly_eq_fin_sum`, `hornerPoly_abs_eq_fin_sum`, `abs_horner_sum_eq`
- `horner_backward_error` (coefficient perturbation form)

## Known Debt (ordered by priority)

### D1. `error_distributable` duplication — DONE
KahanSum.lean imports BackwardErrorCore and uses the framework's
`backwardResult_of_forward_sum_bound`. Old duplicates removed.

### D2. `MixedResult` residual gauge — DONE
`MixedResult` now takes `G_out : AffineFold.Gauge Y R` parameter and has
`residual_bound : G_out.val residual ≤ eps_fwd`. `Gauge` gained a `symmetric`
field (`val (-s) = val s`). `BackwardResult.toMixed` takes an output gauge.

### D3. AffineFold → MixedResult bridge — DONE
`MixedResult.ofAffineFold` + `MixedResult.ofAffineFoldGauge` in
BackwardErrorCore.lean. Given `computed + error_fold = exact`, produces
`MixedResult` with zero backward error and gauge-bounded residual.
Also added `weightedGaugeSum_nonneg` to AffineFold.lean.

### D4. Condition number ↔ BackwardResult bridge — DONE (summation)
`componentwiseRelGauge_component_bound` extracts per-component bounds.
`forward_from_sum_backward` and `forward_rel_from_sum_backward` connect
`BackwardResult` to forward error and condition number for summation.
General `f` still needs partial derivatives / Jacobian framework.

### D5. Gauge hierarchy — partially done
`componentwiseRelGauge` added (max_i |x'_i - x_i|/|x_i|). Still missing:
normwise gauge, weighted gauge, `PerturbationMetric` (triangle inequality).

### D6. Full gauge-based composition
`PerturbationLift` + `BackwardResult.compose` require triangle inequality
on `PerturbationGauge`. Need `PerturbationMetric` structure extending gauge.

### D7. Port `kahan_weak_backward_error` to framework — DONE
`kahan_backward_result` in KahanSum.lean returns `BackwardResult` with
`componentwiseRelGauge`. Uses `backwardResult_struct_of_forward_fin_bound`
bridge from BackwardErrorCore.lean.

## Future Directions

### F1. Gauge = seminorm design note
Adding `symmetric` to `Gauge` makes it a seminorm (nonneg, zero, triangle,
symmetric). This is the right abstraction for error analysis gauges. If we
ever need asymmetric gauges, a separate structure would be needed — but this
is unlikely for numerical error analysis where all gauges are norm-like.

### F2. AffineFold backward attribution (non-degenerate MixedResult)
`MixedResult.ofAffineFold` always produces `x' = x` (zero backward, all
forward). The interesting case: *redistribute* some forward error backward
onto the coefficients. For Horner `p(x) = Σ cᵢxⁱ`, this would give
"perturbed coefficients `c'ᵢ = (1+μᵢ)cᵢ` + smaller residual" — the standard
backward error interpretation.

The bridge would combine `ofAffineFold` with `error_distributable`:
1. Start with degenerate MixedResult (all-forward residual)
2. Use `error_distributable` on the residual to produce per-coefficient `μᵢ`
3. Attribute those perturbations backward, leaving a smaller (higher-order) residual

This is the natural next step for AffineFold integration after D4.

### F3. `componentwiseRelGauge` requires `n > 0`
The `Finset.sup'` in `componentwiseRelGauge` needs `Finset.univ.Nonempty`,
forcing `0 < n`. The `n = 0` case is trivially correct (empty sum = empty sum)
but can't be expressed with this gauge. Callers must carry the `0 < xs.length`
hypothesis. Could add a `componentwiseRelGauge₀` with a special `n = 0` case,
but probably not worth the complexity.

### F4. Condition number bridge (extends D4)
Connecting `componentwiseCondNumber` to `BackwardResult` closes the loop:
**backward error × condition number = forward error bound**.

For summation: `κ = Σ|xᵢ| / |Σxᵢ|`, already defined.
For Horner: `κ = Σ|cᵢxⁱ| / |p(x)|` — the classical result that Horner
evaluation is backward stable with this condition number.

The theorem shape:
```
theorem forward_from_backward_result (br : BackwardResult G f x computed) :
    |computed - f x| ≤ componentwiseCondNumber ... * br.eps * |f x|
```
This is the standard "rule of thumb" from Higham Ch. 1.
