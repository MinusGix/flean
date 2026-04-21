# Tag Framework — Phase 2 Design

**Status**: ALL STAGES LANDED (2026-04-20).  Stages 1–6, follow-up
tag-tightening push (cascaded + fully-tagged end-to-end bounds), and
Stage 7 (concrete `FpSum.FpSumBound.ofNaive` demo with both sums)
all green.  Full Flean build: 2809 jobs, sorry-free.

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

---

## 6. What actually landed (2026-04-20 close)

### Files added
- `Flean/Operations/LayerNorm.lean` (~560 lines, sorry-free).
- `Flean/Tags/LayerNorm.lean` (~100 lines, sorry-free).

### Theorems delivered

**Pure-math**: `mean`, `variance`, `layerNorm` + `variance_nonneg`,
`variance_plus_eps_pos`, `sqrt_var_plus_eps_pos`, `sum_shift_eq_zero`.

**Per-step FP error bounds** (normal-range regime, all sorry-free):
1. `fpMean_error_bound` — division step after `FpSumBound` adapter.
2. `fpShift_error_bound` — `fpSubFinite` per-component step.
3. `fpSqDiff_step_error_bound` — `fpMulFinite` squaring step.
4. `fpVar_step_error_bound` — variance divide (thin wrapper of
   `fpMean_error_bound`).
5. `fpVarPlusEps_step_error_bound` — `fpAddFinite` eps-add step.
6. `fpStddev_step_error_bound` — `fpSqrtFinite` step.
7. `fpNormalize_step_error_bound` — final per-component divide.

**End-to-end composition**:
- `fpLayerNorm_composition_bound` — triangle-inequality composition
  of the three main error terms (shift, stddev, final divide) into
  a forward-error bound.
- `fpLayerNorm_end_to_end_error_bound` — `layerNorm`-tied wrapper.

**Tag wrapper**:
- `fpLayerNorm_tagged_bound` — `IsBoundedRange`-aware end-to-end.
- `fpLayerNorm_input_abs_le` — tag magnitude corollary.

### What the tag currently delivers

`IsBoundedRange I xs` exposes `|xs_i| ≤ I.maxMag`, available to
downstream bounds via `.toVal_abs_le`.  The tag is carried through
the wrapper but does not yet automatically discharge normal-range
preconditions on every per-step theorem — that's Phase 3 work
requiring:
- `IsBoundedRange.fpSub` propagation lemma (mirror of existing
  `IsBoundedRange.fpAdd`).
- Lower-bound magnitude reasoning for products and sums
  (`(x_i − μ̂)²` needs `|x_i − μ̂| ≥ 2^(min_exp/2)`, i.e. a
  separation hypothesis on spread of `xs` vs. `μ̂`).
- A `separation`-style hypothesis analogous to softmax's
  `4·n·2^min_exp ≤ exp(I.lo − I.hi)`, tailored to LayerNorm's
  quotient regime.

### Stage 7 landed

- **Concrete demo**: `fpLayerNorm_naiveSum_demo` in
  `Flean/Tags/LayerNorm.lean` (§Demo section).  Threads two
  `FpSum.NaiveSum` traces (mean sum and variance sum) through the
  `FpSumBound.ofNaive` adapter, materialises concrete `δ_shift` and
  `δ_var` from the resulting `relErr` values, and closes via
  `fpLayerNorm_fully_tagged_end_to_end_bound`.  ~120 lines.
- **Demo scope caveat**: the variance-side approximation
  `|Σ sqDiffs_j/n − variance(xs.toVal)| ≤ δ_sqDiffs_approx` is taken
  as a user hypothesis, not derived from the squaring witnesses.
  Deriving it is a straightforward but bulky `|a² − b²| = |a − b|·|a + b|`
  composition across `n` indices; left to callers and documented in
  the theorem docstring.  The `_h_sqDiffs` witnesses are kept in the
  signature as documentation but consumed with a leading underscore.

### Signal about framework durability

Positive:
- Seven new per-step error-bound theorems, all following the same
  `round_witness + round_preserves_abs_error_normal` template —
  confirms that the Phase 1 meta-lemma kernel scales to a new
  workload.
- `FpSumBound` adapter slotted in cleanly — no modifications needed
  to `Flean/Operations/FpSum.lean`.
- Composition via triangle inequality over three main error terms —
  clean, each per-step δ appears explicitly in the final bound.

Neutral:
- The tag currently plays a minor role in the Phase 2 delivery
  (magnitude corollary only).  Broader tag automation needs
  infrastructure additions flagged above.  This matches the pattern
  in Phase 1 where `SoftmaxBounded.lean` bridges landed incrementally.

Negative:
- Struct elaboration with many `FpSumBound`-valued fields hit
  `whnf` heartbeat limits; had to flatten to unbundled hypotheses.
  Worth investigating whether `FpSumBound` reducibility annotations
  would help future bundle structs.

---

## 7. Follow-up push: tag tightening at the end-to-end level

After the Stage-1-through-6 close, the honest critique was that the
tag was carrying through the final wrapper without *dematerializing*
any term — i.e., Phase 2's core ethos wasn't demonstrated for
LayerNorm.  A same-day follow-up pushed on this, landing three
additional commits.

### Framework additions (cross-cutting)

- `FpInterval.neg` / `fpSubN` / `fpSub` + scoped `⊟` notation
  (`Flean/Tags/FpInterval.lean`).  Subtraction defined as
  `fpAdd · (neg ·)` to reuse the existing add slack analysis.
- `IsBoundedRange.neg`, `IsBoundedRange.fpSub`,
  `IsBoundedRange.fpSub_unified`
  (`Flean/Tags/BoundedRangePropagate.lean`) — propagation through
  `fpSubFinite` via negation + add-propagation.  Closes the
  framework gap flagged in §4 as a prerequisite for LayerNorm
  tag automation.

### Per-step tag-tightened bounds

New theorems in `Flean/Tags/LayerNorm.lean`:

1. `varPlusEps_normal_of_eps_normal` — `IsNormal eps` + `0 ≤ var` →
   `2^min_exp ≤ |var + eps|`.  Uses `IsNormal.add_nonneg`.
2. `fpVarPlusEps_tagged_step_error_bound` — wraps the eps-add
   per-step bound, discharges normal-range from the tag.
3. `sqrtVarPlusEps_normal_of_tagged` — `IsNormal varPlusEps` +
   `min_exp ≤ 0` → sqrt-side normal-range.  Uses
   `Real.sqrt_le_sqrt` + `Real.sqrt_sq`.  The `min_exp ≤ 0`
   side condition holds for all standard formats (fp16/32/64/etc.)
   but is explicit to stay format-agnostic.
4. `fpStddev_tagged_step_error_bound` — wraps the sqrt per-step
   bound, discharges normal-range from the tag pair.

### Cascaded composition theorem

`fpStddev_cascaded_tagged_bound` — composes the eps-add + sqrt
tag-tightened bounds with a sqrt-Lipschitz step to bound
`|stddev − √(σ² + eps)|` directly from `|var − σ²| ≤ δ_var` + the
tag hypotheses.

Supporting private lemma: `sqrt_sub_sqrt_le_of_lb` — if `c ≤ a` and
`c ≤ b` with `c > 0`, then `|√a − √b| ≤ |a − b| / (2·√c)`.  Proved
via `(√a − √b)·(√a + √b) = a − b` and denominator substitution.

Result shape:
```
|stddev − √(σ² + eps)| ≤
    η · √varPlusEps
  + (η · (var + eps) + δ_var) / (2 · √(2^min_exp))
```

Three tag-discharged preconditions collapse into one cleanly-stated
bound; the variance-side error `δ_var` stays as the one
user-supplied upstream quantity.

### Fully-tagged end-to-end theorem

`fpLayerNorm_fully_tagged_end_to_end_bound` — final user-facing
wrapper.  Takes:
- Tags: `IsNormal eps.toVal`, `IsNormal varPlusEps.toVal`,
  `min_exp ≤ 0`.
- Framework hypotheses: `0 < n`, `0 < stddev.toVal`,
  `0 ≤ var.toVal`.
- Upstream δ's: `δ_var`, `δ_shift`, `δ_final`.
- FP rounding witnesses for eps-add and sqrt.

Produces: a forward-error bound on `|result_i − layerNorm xs eps i|`
where `eps = eps_fp.toVal`, with the `δ_stddev` field of the earlier
end-to-end bound now auto-composed internally.

### Final scorecard (preconditions dematerialized)

| Per-step precondition | Untagged | Tagged |
|---|---|---|
| eps-add normal-range | manual | ✓ tag |
| sqrt-side normal-range | manual | ✓ tag pair + min_exp |
| sqrt-Lipschitz denom lower bound | manual | ✓ tag pair |
| `δ_stddev` composition | manual | ✓ cascaded |
| mean-div normal-range | manual | still manual |
| shift normal-range | manual | still manual |
| square normal-range | manual | still manual |
| variance-div normal-range | manual | still manual |
| normalize normal-range | manual | still manual |

**4 of 9 preconditions + 1 upstream-derived quantity** are now
automatic under the tag pair.  The 5 that remain are tied to
LayerNorm's `(x_i − μ)` factor, which can be arbitrarily small
for inputs close to the mean — no input-side tag can rule that out
without strong input-spread assumptions (stronger than
`IsBoundedRange`).  This is a property of LayerNorm's math, not a
framework gap; softmax's cleaner tightening story relied on
`exp(x) > 0` providing a natural magnitude floor that
subtraction-based primitives lack.

### What this follow-up validates

Positive about the framework:
- Tag pairs (`IsNormal eps` + `IsNormal varPlusEps`) compose
  cleanly to discharge multiple preconditions at once.
- Cascaded tag-tightened theorems are practical to write:
  ~150 lines for the sqrt composition, using standard mathlib
  `Real.sqrt_*` + algebraic identity on `(√a − √b)(√a + √b)`.
- Fully-tagged end-to-end wrapper reuses the prior unbundled
  theorem (`fpLayerNorm_end_to_end_error_bound`) verbatim by
  just substituting the cascaded δ_stddev — no re-proving.

Honest about the limits:
- The five manual preconditions are a structural limitation,
  not a future deliverable.  LayerNorm will always need
  spread/non-collapse assumptions for the small-difference steps.
  Honest framing in future documentation should lead with this.
- The tag-discharge ratio (4/9) is a meaningful Phase 2 win but
  not complete automation.  Softmax's bridge is richer because
  its primitives have friendlier magnitude behavior.

### Final footprint

- `Flean/Operations/LayerNorm.lean`: 560 lines, 7 per-step theorems
  + 2 composition theorems, all sorry-free.
- `Flean/Tags/LayerNorm.lean`: ~470 lines, 7+ tag-related theorems
  covering per-step tightening, cascaded composition, and
  fully-tagged end-to-end.
- `Flean/Tags/FpInterval.lean` / `Flean/Tags/BoundedRangePropagate.lean`:
  small additions (neg + fpSub propagation).
- Full Flean build: 2809 jobs green, sorry-free.
- Commit chain (8 Phase 2 commits):
  `9f6b384` Stage 1 — pure-math + scope plan
  `512f0c8` Stage 2 — mean + shift error bounds
  `e2cb5ee` Stages 3–5 — per-step bounds + end-to-end
  `2c73269` Stage 6 — IsBoundedRange tagged wrapper
  `ab91218` tag tightening — eps-add + sqrt preconditions
  `5caae4f` cascaded tag-tightening — composed stddev bound
  `4eac832` fully-tagged end-to-end bound
  Stage 7 — concrete `FpSumBound.ofNaive` demo (both sums)
