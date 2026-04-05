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

## Phase 1 Status — DONE

Phase 1 delivered (377 lines, sorry-free). Items completed:
- `PerturbationGauge`, `uniformGauge`, `trivialGauge`
- `BackwardResult`, `MixedResult`, `BackwardResult.toMixed`
- `error_distributable`, `backwardResult_of_forward_sum_bound`,
  `backwardResult_of_forward_bilinear_bound`
- `componentwiseCondNumber`, `forward_le_cond_mul_backward`,
  `forward_rel_le_cond_mul_backward`
- `dp_backward_error`, `dp_backward_error_gamma`

## Known Debt / Phase 2+ Notes

### D1. `error_distributable` duplication
KahanSum.lean has its own `error_distributable` + `backward_from_forward`.
BackwardError.lean has generalized versions. Eventually KahanSum should import
BackwardError and delegate. Not urgent — existing code works.

### D2. `MixedResult` missing residual gauge
The design proposed using AffineFold's `Gauge` to measure the residual, but
the current `MixedResult` has a bare `fwd_bound : R` with no formal connection
to `|residual|`. Needs a `residual_bound : gauge.val residual ≤ fwd_bound`
field or similar. Important for Phase 4 (AffineFold integration).

### D3. Horner backward error linking lemma
Horner's forward bound uses `hornerPoly(|coeffs|, 0, |x|)` (weighted by `|cᵢ|·|x|^i`).
To get coefficient backward error, need `result = Σ(1+μᵢ)·cᵢ·x^i`, distributing
proportional to `|cᵢ·x^i|`. The `error_distributable` machinery handles the
distribution, but a linking lemma `hornerPoly → Fin-indexed sum` is missing.

### D4. Condition number section disconnected
`componentwiseCondNumber` is defined but not connected to `BackwardResult`.
The full bridge (given `BackwardResult` with bound `ε`, derive forward relative
error `ε·κ`) works for summation via `forward_rel_le_cond_mul_backward` but
not for general `f`. Generalizing needs partial derivatives / Jacobian framework.

### D6. `hornerPoly_eq_fin_sum` — 1 sorry
The Fin-indexed linking lemma `hornerPoly cs 0 x = Σ cs[i]·x^{n-1-i}` has 1 sorry
in the cons case: need to show `Σ (c::cs)[succ i]·x^{...} = Σ cs[i]·x^{...}` after
`Fin.sum_univ_succ`. The helper `hornerPoly_acc_eq` is proved. The sorry is pure
`List.get`/`Fin.succ`/`Nat` subtraction arithmetic.

### D5. Gauge hierarchy minimal
Only `uniformGauge` and `trivialGauge` exist. No componentwise relative gauge
(which divides by `|xᵢ|`) — `Finset.sup'` with division-by-zero handling was
fragile. The actual backward error theorems (`dp_backward_error`) don't use
gauges at all; they directly state `|μᵢ| ≤ ε`. Gauges become important for
composition (Phase 3), where perturbation tracking through pipelines is needed.
