# Tag Framework — Phase 2 Design

**Status**: IN PROGRESS (started 2026-04-20).

**Chosen target**: Candidate B — LayerNorm as a new tagged ML primitive.

This doc captures (1) the candidate analysis that led to choosing B,
(2) the LayerNorm design, and (3) the implementation plan.  Running
log; updated as work lands.

---

## 1. Candidate analysis (2026-04-20)

Phase 2's session prompt offered four candidates (A–D).  Key observation
during analysis: Phase 1's `fpSoftmax_bound_of_separated` already
delivers the canonical softmax tail elimination that Candidate A names.
The four candidates decompose as:

### Candidate A — Softmax `subnormalConst` tail elimination

**Phase 1 already delivers the uniform case.**
`Flean/Tags/SoftmaxBounded.lean :: fpSoftmax_bound_of_separated` takes
`IsBoundedRange I xs` + log-bound on `I.lo` + separation +
`εsum ≤ 1/4`, and produces the clean softmax bound (no `sc` tail,
factor-1 not factor-2).  The `quot_isNormalRange` bridge closes the
full loop.

**What's genuinely new in Candidate A**: the **partitioned** variant.
A subset `S ⊆ Fin n` designates "possibly subnormal" indices; the tag
holds on `i ∉ S`; per-index bound branches.  Framework novelty: shows
tags composing with `Finset` subsetting over a vector with a shared
global quantity (the denom).  Scope ~500 lines (core softmax re-proof
with per-index case split).

Raw numeric tightening beyond Phase 1: modest — saves `sc` tail on
`i ∉ S`, keeps it on `i ∈ S`.  Real payoff is the framework pattern.

### Candidate B — LayerNorm as new tagged ML primitive (chosen)

Build FP-rounded LayerNorm (mean, variance, normalize by
`(x − μ) / √(σ² + ε)`), prove a per-component error bound using the
tag framework throughout.

**Why chosen**: tests whether the framework handles a *fresh* workload
end-to-end rather than sharpening a known bound.  This is the strongest
signal about framework durability — "new primitives drop in" is the
load-bearing claim for users.

Scope ~500–800 lines estimated.  Greenfield → more up-front design,
but each piece is tractable (existing `FpSumBound` adapters, existing
sqrt/div semantics).

### Candidate C — Horner with `IsNonneg` coefficient tag

Rewrite `horner_error_bound`'s RHS from `γ · P(|coeffs|, |init|, |x|)`
to `(γ/(1-γ)) · final.toVal` under `IsNonneg` inputs.  Real utility win
(observable bound in terms of computed value), but framework signal is
low — doesn't introduce a new tag pattern.  Scope ~250–350 lines.

### Candidate D — Kahan/Neumaier with `IsNonneg`

Ruled out: the Kahan/Neumaier bounds are already tight
(`2η + nη²` or `n·η·((1+η)^{n+1}−1)`) and don't admit a clean first-
order-only tightening under nonneg inputs — the `nη²` term isn't from
cancellation per se.

### Ranking (elegance + framework utility at acceptable scope)

1. **B (LayerNorm)** — most new surface area, best signal about framework
   durability, fresh ML primitive.
2. **A-partitioned** — framework-novel pattern (per-index tags), but
   numeric payoff over Phase 1 is incremental.
3. **C** — cleanest narrow win, but framework-statement is thin.
4. **D** — ruled out (no real tightening).

**Chose B** per user direction "fine with larger work, matter of
elegance and utility" — B scores highest on utility (new primitive the
framework can claim to handle).

---

## 2. LayerNorm design

### 2.1 Mathematical definition

Standard LayerNorm per-vector:

```
μ      := (1/n) Σ_j x_j
σ²     := (1/n) Σ_j (x_j − μ)²
y_i    := γ_i · (x_i − μ) / √(σ² + eps) + β_i
```

where `eps > 0` is a numerical-stability constant.

### 2.2 Scope simplifications

Deliberate narrowings to keep scope manageable:

- **γ = 1, β = 0**: pure normalization.  Affine scale/shift can be
  added later as a one-line follow-up once the core bound exists —
  it's a trivial `fpMul` + `fpAdd` composition.
- **All-normal-range regime**: per-step `isNormalRange` hypotheses
  threaded explicitly, parallel to `horner_error_bound`'s
  `AllNormalRange`.  Subnormal tolerance is Phase-3 work.
- **`eps` supplied as a `FiniteFp`** with the user-visible invariant
  `isNormalRange eps.toVal` (or similar explicit lower bound).  This
  keeps `σ² + eps` bounded below even if `σ² = 0`.
- **Input shape**: `xs : Fin n → FiniteFp`.  Tag: `IsBoundedRange I xs`
  with explicit `I : FpInterval ℝ`.

### 2.3 Operations threaded

Per-step:

1. **Mean sum**: `Σ x_j`.  User supplies `FpSum.FpSumBound xs ℝ`.
2. **Mean divide**: `Σ / n`.  Multiply-by-`1/n`-as-FP equivalent, or
   explicit `fpDivFinite`.
3. **Shift**: per-i, `x_i − μ̂`  (`fpSubFinite`).
4. **Square**: per-i, `(x_i − μ̂)²`  (`fpMulFinite`).
5. **Variance sum**: `Σ (x_j − μ̂)²`.  User supplies second
   `FpSum.FpSumBound` adapter.
6. **Variance divide**: `Σ / n`.
7. **Eps add**: `σ̂² + eps`  (`fpAddFinite`).
8. **Sqrt**: `√(σ̂² + eps)`  (`fpSqrtFinite`).
9. **Normalize divide**: per-i, `(x_i − μ̂) / √(σ̂² + eps)`
   (`fpDivFinite`).

No FMA in the initial deliverable (could be retrofitted).

### 2.4 Output structure

Bundle the mean, variance, sqrt, and per-component results:

```lean
structure FpLayerNormResult {n : ℕ} (xs : Fin n → FiniteFp) where
  mean     : FiniteFp
  shifted  : Fin n → FiniteFp       -- x_i − mean
  sqDiffs  : Fin n → FiniteFp       -- (x_i − mean)²
  var      : FiniteFp               -- Σ sqDiffs / n
  varPlusEps : FiniteFp
  stddev   : FiniteFp               -- √(var + eps)
  result   : Fin n → FiniteFp
```

### 2.5 Error bound shape

Per-component target:

```
|(result i).toVal − layerNorm xs i| ≤ Cε · |x_i − μ| / √(σ² + eps) + …
```

Where `Cε` is a polynomial in `η` and the summation-adapter relative
errors.  Exact shape depends on how the per-op errors compose; the
analysis is parallel in style to Horner's `((1+η)^{2n}−1)` but with
division and sqrt steps making it messier.

### 2.6 What the tag dematerializes

Primary tag: `IsBoundedRange I xs` with `0 < I.hi − I.lo` (enough
spread for nonzero variance; no trivial-`σ²` case).

Under the tag, several preconditions auto-discharge:

- **Normal range on `x_i`**: direct from tag.
- **Normal range on `x_i − μ`**: use `IsBoundedRange` propagation
  through `fpSubFinite` — need to add this (mirror of `fpAdd`).
- **Normal range on `(x_i − μ)²`**: propagation through `fpMulFinite`
  (exists).
- **Normal range on `σ² + eps`**: lower bound from `eps`, upper from
  `Σ sqDiffs / n` + tag.
- **Normal range on the quotient**: separation-style argument similar
  to `quot_isNormalRange`.

The final delivery: a theorem taking `IsBoundedRange I xs` + the
`FpSumBound` adapters + eps witness + separation hypothesis (for the
normalize divide), producing the per-component bound automatically.

---

## 3. Implementation plan

Staged so each stage commits sorry-free; if session budget runs out,
we ship what landed.

### Stage 1: Pure-math + FP definitions

New file: `Flean/Operations/LayerNorm.lean`.

- `layerNormMean`, `layerNormVar`, `layerNorm` (pure math).
- `fpLayerNormMean`, `fpLayerNormVar`, `fpLayerNorm` (uses `FpSumBound`
  for both sums, takes `eps : FiniteFp` as parameter).
- Basic properties: mean is linear, variance nonneg, shift invariance.

### Stage 2: Mean + shift step error bound

- Bound `|mean.toVal − μ| ≤ εM` using `FpSumBound.relErr` + `fpDiv`.
- Bound `|shifted_i − (x_i − μ)|` using `fpSubFinite` error.

### Stage 3: Square + variance-sum + variance-divide

- Bound `|sqDiffs_i − (x_i − μ)²|`.
- Bound `|var.toVal − σ²|`.

### Stage 4: sqrt + eps-add step

- Bound `|stddev.toVal − √(σ² + eps)|`.

### Stage 5: Per-component normalize divide

- Bound `|result_i − y_i|`.  Ties everything together.

### Stage 6: Tag-specialized wrapper

New file: `Flean/Tags/LayerNorm.lean`.

- Wrapper taking `IsBoundedRange I xs` + separation-style hypothesis,
  discharging all normal-range preconditions automatically.

### Stage 7: Demos + update aggregator

- Demo: concrete LayerNorm with `FpSumBound.ofNaive` for both sums.
- Update `Flean/Tags.lean` aggregator.
- Update `.claude/notes/tag-framework-phase1-design.md` §6 noting
  Phase 2 landed.

---

## 4. Open questions / risks

- **Sqrt error bound infrastructure**: `fpSqrtFinite_correct` gives
  `fpSqrtFinite = round(√(a.toVal))`, but no standalone
  "sqrt rounding error bound" theorem exists.  Derivable from
  `round_preserves_abs_error_normal` applied to `√(·)` as the exact
  value — should be a direct use, not new infrastructure.
- **Variance can be zero** if all `x_i` equal.  Handled by `eps > 0`;
  need to guard against `σ² = 0 + eps` hitting sqrt's zero branch.
- **Division by sqrt can underflow** in extreme regimes.  Separation
  hypothesis on `I.hi − I.lo` vs. `eps` should prevent this; analogous
  to softmax's separation.
- **No `fpSubFinite` tag propagation yet**: need
  `IsBoundedRange.fpSub` (parallel to `.fpAdd`) — small addition,
  mirrors the existing pattern.

---

## 5. Commit cadence

One commit per stage that builds.  Stage 1 (definitions) alone can
commit before any bound lands — the definitions are self-contained.
