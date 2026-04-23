# MLP Capstone — Iteration Backlog

**Status**: live working list, 2026-04-22.  Captures observations
from the first MLP capstone (`Flean/Operations/MLP.lean`,
checkpoints `b8d363c` + `e66c67f`) plus user feedback.

Companion docs:
- `strategic-directions.md` — high-level ranking.
- `tag-framework-backlog.md` — tag-side iteration log.
- `tag-framework-patterns.md` — pattern guide.

---

## Items (M-series)

Letter codes:
- ✅ landed
- 🟢 agreed, ready to implement
- 🟡 agreed, needs design discussion
- ⚪ noted, low priority / shrug
- 🔵 documentation update

### M1: `HasAbsBound` vs `IsBoundedRange` for input-side tags ⚪🔵

**Finding**: capstone used `HasAbsBound 1` despite "pixel values in
`[0, 1]`" framing.  The signed (`0 ≤ x`) info was thrown away — the
deterministic magnitude analysis only needed `|x| ≤ 1`.

**User direction**: keep `IsBoundedRange` available; we want to
eventually exploit cancellation statistics where the signed info
matters.

**Action**: pattern guide update only — note that for *deterministic
worst-case* magnitude analyses, `HasAbsBound` is the right default;
`IsBoundedRange` is reserved for cases that exploit signs (softmax
separation, normal-range bridges, future statistical analyses).

### M2: Lipschitz as a framework notion ✅ **SHIPPED 2026-04-22**

`Flean/Operations/Lipschitz.lean` (168 lines, foundational, no
`FloatFormat`/rounding deps).

* `LipschitzMax K f` — per-output Lipschitz on vector functions.
* `LipschitzScalar K f` — scalar version (for activations / M10).
* Composition primitives: `.id_id`, `.const`, `.weaken`, `.comp`,
  `.compScalar` for cross-composition (scalar applied component-wise
  to vector function).

In `MLP.lean`:
* `Layer.forward_lipschitz` — Lipschitz constant `n_in · wMax`.
* `MLP2.forward_lipschitz` — composed via `LipschitzMax.comp`.

Refactor: `MLP2FpResult.forward_error_bound` now uses
`Layer.forward_lipschitz` instead of the (deleted) private
`Layer.forward_perturbation` helper.  Composition via the framework
rather than manual triangle.

**Decision**: custom `LipschitzMax` chosen over Mathlib's
`LipschitzWith`.  Rationale: Mathlib's version requires `PiLp ⊤`
metric instances on `Fin n → R` and `ℝ≥0∞`-valued constants;
heavy plumbing without payoff for our forward-error use case.
A `LipschitzMax → LipschitzWith` bridge is feasible if a future
consumer wants Mathlib API.

**Scope clarification**: per-FP-op Lipschitz is **not** part of
this framework — rounding is discontinuous and isn't Lipschitz in
the usual sense.  FP error bounds stay with the
`round_preserves_*` family.

**Finding**: `Layer.realForward_perturbation` proved that layer 2
amplifies an input δ by at most `n_in · wMax · δ` — i.e., layer 2 is
Lipschitz in its input with constant `n_in · wMax`.  This was the
composition glue for the 2-layer error bound.  Every linear primitive
has a Lipschitz constant; chaining them is how forward errors
propagate through layer stacks.

**User direction**: definitely do this.

**Design discussion**: see §"Lipschitz design notes" below.

**Scope estimate**: ~200–400 lines depending on how rich the
abstraction.

### M3: `LayerBounded` naming ⚪

**Finding**: reads as "the layer is bounded" but means "the layer's
parameters are bounded."

**User direction**: rename to `BoundedParams` (or similar).

**Action**: small rename; bundle with another commit.

### M4: Composable hypothesis bundling 🟡

**Finding**: `MLP2FpResult.forward_error_bound` takes ~10 explicit
arguments.  3-layer MLP would have ~15+.  A struct that bundles
parameters + hypotheses + FP results would collapse call sites.

**User direction**: ideally something more *naturally composable*
than just a struct.

**Design discussion**: see §"Composability design notes" below.

### M5: Derive parameter nonneg accessors 🟢

**Finding**: explicit `0 ≤ wMax`, `0 ≤ bMax` hypotheses accumulate.
These follow from `LayerBounded` + nonempty witness.

**User direction**: yeah.

**Action**: add `BoundedParams.wMax_nn` / `bMax_nn` accessors.
Possibly require `0 < n_out` (or similar) as a struct field.

### M6: Bundle bridges underused at multi-layer level ⚪

**Finding**: I unfolded magnitude bounds manually in MLP rather than
using `FpSumBound.hasAbsBound_of_isBoundedRange`.  The bundle bridges
assume you already *have* the bundle; for multi-layer structures
that iterate bundles, the bridge API is awkward.

**User direction**: unfortunate.

**Action**: possibly add `FpMatVecBound.hasAbsBound_of_per_entry`
that takes per-entry tags on both matrix and vector.  Lower priority
unless multi-layer code keeps unfolding manually.

### M7: Rename `LayerBounded` → `BoundedParams` ⚪

(See M3 — same item, just splitting "rename" from "naming
discussion".)

### M8: Concrete runnable demo + helper lemmas 🟢

**Finding**: shipped theorems but no `example` instantiation.

**User direction**: helper lemmas to ease demo construction would
be valuable.

**Action**: ship a concrete `example MLP2 16 8 4` (or similar) +
a small set of helper lemmas (e.g., `mkBoundedParams`,
`mkLayerFpResult`, `concreteForwardBound`).  ~100 lines total.

### M9: `Finset.sum_sub_distrib` friction ⚪

**Finding**: couldn't apply it to `(Σ + b) - (Σ' + b)` directly;
needed a `ring`-based intermediate.  Recurring Lean ergonomics
gotcha.

**Action**: not a fix — note in patterns doc as a known recipe.

### M10: ReLU + activation framework ✅ (2026-04-22)

**Shipped**: `Flean/Operations/Activation.lean` (117 lines) +
`Flean/Operations/MLP/LayerActivated.lean` (213 lines) +
`LipschitzScalar.errorAmplification` in `Lipschitz.lean` (19 lines).

`Activation R` struct presumes Lipschitz (matches recommendation in
"Activation design notes" below).  `Activation.relu` ships as the
canonical instance; `Activation.identity` as baseline.
`ActivatedLayer R n_in n_out` bundles `Layer` + `Activation R`;
`ActivatedLayer.forward_lipschitz` derives the composed Lipschitz
constant via `LipschitzMax.compScalar`.

FP integration via `ActivationFpResult σ xs` slack-soundness witness
(per-index `|result_i.toVal - σ(xs_i.toVal)| ≤ slack`), parameterized
over the FP implementation.  `ActivatedLayerFpResult.forward_error_bound`
composes layer error with activation slack via the new
`LipschitzScalar.errorAmplification` primitive — proof body 3 lines.

**Deferred follow-ups**: concrete FP ReLU constructor (needs FiniteFp
sign-comparison machinery), M11 CE-on-top integration.
See [m10-activation-framework.md] memory.

**Activated 2-layer MLP follow-up ✅ (2026-04-23)**:
`Flean/Operations/MLP/ActivatedMLP2.lean` (~287 lines, sorry-free).
Ships `ActivatedMLP2`, bounded-params tag, real/FP magnitude bounds,
whole-model Lipschitz, FP error bound via `errorAmplification` on the
second *activated* layer's Lipschitz constant `σ₂.K · n_hidden · w2Max`,
and a ReLU-on-ReLU demo at shape (4 → 3 → 2).  Also added
`ActivatedLayerFpResult.outputBound` + `toVal_abs_le` + `outputBound_nn`
to `LayerActivated.lean` (needed so layer 2 can accept a magnitude
tag on layer 1's activated output).  Error-bound proof body mirrors
the linear `MLP2.forward_error_bound` modulo the amplification constant.

### M11: CE loss layer integration ✅ (2026-04-23)

**Shipped**: `Flean/Operations/MLP/MLPCrossEntropy.lean` (~244 lines,
sorry-free) + helper lemmas in `LogSumExp.lean` (~50 lines) and
`CrossEntropy.lean` (~60 lines).

Helpers:
* `LogSumExp.logsumexp_monotone` — coordinatewise monotonicity.
* `LogSumExp.logsumexp_lipschitz` — 1-Lipschitz in L∞ (via
  monotonicity + `logsumexp_shift_eq`).
* `CrossEntropy.crossEntropy_lipschitz_logits` — CE is L∞-Lipschitz
  in logits with constant `2 · Σ|y_i|`.  Proof decomposes
  `CE(y, x) = -Σ y_i x_i + (Σ y_i) · LSE(x)` and bounds each piece.

Composition:
* `MLPCrossEntropy.compose_error_bound` — abstract (any forward-error
  witness + any CE-vs-FP-logit bound).
* `MLP2FpResult.crossEntropy_error_bound` — linear 2-layer
  specialization.
* `ActivatedMLP2FpResult.crossEntropy_error_bound` — activated
  2-layer specialization.
* `MLP2FpResult.crossEntropy_error_bound_of_res` — variant consuming
  a `FpCrossEntropyResult` bundle.

End-to-end bound shape:

```
|loss.toVal − CE(y, M.forward(x_real))|
  ≤ ce_err + 2 · Σ|y_i| · mlp_err
```

where `ce_err` is the CE pipeline's bound (`FpCrossEntropyResult.error_bound`)
and `mlp_err` is the MLP's per-index forward error
(`MLP2FpResult.errorBound` or `ActivatedMLP2FpResult.errorBound`).

### M12: `realForward` naming 🔵

**Finding**: the function is R-valued, not ℝ-valued — "real" is
confusing.

**User direction**: rename to indicate the abstract field; "this
is the underlying mathematical notion the FP mimics."

**Discussion**: candidates: `forward` (drop the prefix), `eval`,
`exact`, `unrounded`, `groundTruth`, `mathForward`.  See
§"Naming discussion" below.

---

## Lipschitz design notes (for M2)

The shape: every linear primitive (`fpAdd`, `fpDotProduct`,
`fpMatVec`, `Layer`, `MLP2`) is Lipschitz in each of its arguments
under FP perturbations of those arguments.

### Possible APIs

**Option A — pointwise-Lipschitz lemmas, no abstraction**:

```lean
theorem Layer.realForward_perturbation : ∀ ε, |x j - x' j| ≤ ε →
    |L.realForward x i - L.realForward x' i| ≤ (n_in · wMax) · ε
```

What we have already.  Each primitive ships its own.  Multi-layer
composition writes the chain manually.

**Option B — `LipschitzIn` typeclass**:

```lean
class LipschitzIn (f : (α → R) → β → R) (k : R) where
  perturbation_bound : ∀ x x' i δ, (∀ j, |x j - x' j| ≤ δ) →
    |f x i - f x' i| ≤ k · δ
```

Each primitive registers its Lipschitz constant as an instance.
Composition is mechanical via instance resolution.  Risk: typeclass
inference perf as the registry grows.

**Option C — `LipschitzOp` record, explicitly composed**:

```lean
structure LipschitzOp (f : ...) where
  lipschitz : R
  perturbation_bound : ...
```

Records compose via a `compose` operation that multiplies constants.
Explicit, composes cleanly, no typeclass synthesis cost.

### Recommendation

**Option C** seems best:
- Avoids the typeclass perf trap (Phase 1 design rejection).
- Matches the existing "named records of bounds" pattern
  (`FpSumBound`, `FpDotProductBound`, etc.).
- Composition explicit — `op2.compose op1` makes the chain visible.

**Open**: is Lipschitz a tag category (the "regime" or new
"contraction" category) or just a separate algorithm-level concept?
Probably the latter — Lipschitz is about the *operation*, not the
*value*.

---

## Composability design notes (for M4)

The user wants the multi-layer hypothesis bundling to be *naturally
composable*, not just a struct dump.

### What "composable" might mean here

**Option A — n-layer MLP via `Vector` of layers**:

```lean
structure MLPN (n : ℕ) (dims : Fin (n+1) → ℕ) where
  layers : ∀ i : Fin n, Layer (dims i.castSucc) (dims i.succ)
```

with `realForward`, `LayerFpResult`-chain, etc. defined inductively.
Hypothesis lists then collapse into "all layers are bounded by
some matching `wMax_i` / `bMax_i`."  Still long but indexable.

**Option B — inductive composition: 1-layer → n-layer via `Sequential`**:

```lean
structure Sequential (Hd : Layer α β) (Tl : MLPN _) ...
```

Builds n-layer from atoms, gets n-layer bounds via induction.  Most
elegant but most refactoring.

**Option C — bundle struct per layer, fold over them**:

Each layer carries its own `LayerInstance` (params + bounds + FP
result + hypotheses).  `MLP2Instance` is just `(LayerInstance, LayerInstance,
input_link)`.  N-layer is a list of `LayerInstance`s with chained
input-output links.

### Recommendation

**Option C** is the most pragmatic — composes the struct naturally,
doesn't require inductive proofs over a `Vector`-indexed type
(which has its own ergonomics issues).  Each layer's instance is a
unit; multi-layer is a chain.

**Open**: should `LayerInstance` carry the *theorems* (proofs that
`outputBound`, `errorBound` apply) or just the *data* (params + FP
witness)?  If the former, n-layer composition is an inductive proof.
If the latter, the proof is at the use site.

Pragmatic answer: data only.  Proofs at the use site, but uniform
because the structure is uniform.

---

## Activation design notes (for M10)

### Should `Activation` presume Lipschitz?

**Yes — for the practical 99% case**:
- ReLU: 1-Lipschitz
- LeakyReLU: max(1, |negative_slope|)-Lipschitz
- Sigmoid: 1/4-Lipschitz
- Tanh: 1-Lipschitz
- GeLU: ~1.13-Lipschitz
- Swish/SiLU: ~1.1-Lipschitz
- Softplus: 1-Lipschitz

All standard ML activations are Lipschitz with small constants.

**No — for full generality**:
- Polynomial activations (rare but exist) can be non-Lipschitz.
- Future tag-based reasoning might want non-Lipschitz support
  (e.g., probability-aware tightening).

### Recommendation

**Yes, presume Lipschitz**, but make the constant a parameter:

```lean
structure Activation where
  apply : ℝ → ℝ
  lipschitz : ℝ
  apply_lipschitz : ∀ a b, |apply a - apply b| ≤ lipschitz · |a - b|
```

For ReLU, `lipschitz = 1`.  Dosent constrain non-Lipschitz futures
(could add `ActivationGeneral` later).

This couples cleanly with M2: a `Layer` with activation `σ` has
Lipschitz constant `n_in · wMax · σ.lipschitz` in its input.

---

## Naming discussion (for M12)

The function `Layer.realForward x : Fin n_out → R` is R-valued, not
ℝ-valued.  Confusing because R might be ℚ in the codebase.

### Candidates

| Name | Pros | Cons |
|---|---|---|
| `forward` | Short, describes the operation. | Generic — could be confused with `fpForward`. |
| `eval` | Standard math idiom. | Too generic. |
| `exact` | Conveys "no rounding." | Overloaded with the FP `exact` (vs `sticky`) terminology. |
| `unrounded` | Accurate, descriptive. | Verbose. |
| `mathForward` | Descriptive, distinct. | Ugly. |
| `groundTruth` | ML-friendly. | Loaded — sounds like training data. |
| `forwardR` | Indicates R-valued. | Hungarian-style; not Lean-idiomatic. |

### Recommendation

**`forward`** for the R-valued version, **`fpForward`** for an
explicit FP version when needed.  The `LayerFpResult` already names
its FP result `result` — keep that.

Resolves with: `Layer.forward` (math), `LayerFpResult.result` (FP).
Symmetric: `MLP2.forward` (math), `MLP2FpResult.layer2.result` (FP).

---

## Ranking

Rough priority order (user's call):

1. **M2 Lipschitz** — biggest framework idea; needs design before
   coding.
2. **M11 CE integration** — completes the end-to-end story.
3. **M10 Activation** — makes capstone realistic.
4. **M4 Composability** — n-layer-friendly bundling.
5. **M8 Concrete demo + helpers** — runnable artifact + ergonomics.
6. **M5 Parameter nonneg accessors** — small win.
7. **M3 / M7 Rename `LayerBounded` → `BoundedParams`** — bikeshed.
8. **M12 `realForward` rename** — bikeshed-adjacent.
9. **M1 / M6 / M9** — documentation updates only.
