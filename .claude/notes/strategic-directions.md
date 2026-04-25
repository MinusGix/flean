# Flean — Strategic Directions

**Status**: living document.  Captures the high-level review of where
the project stands and what next moves are valuable, surfaced
2026-04-22 after the tag-framework E-series + T-M3 + IsProb + lattice
cleanup batch.

**Companion docs**:
- `tag-framework-backlog.md` — live iteration log for tag work.
- `tag-framework-patterns.md` — pattern guide / teaching artifact.
- `tag-framework-boundedrange-audit.md` — E6 use-site audit.
- `directions.md` — older project-wide directions list.

---

## Stocktake (2026-04-22)

What's in hand:

* **ML primitives arc**: softmax + LSE + CE + log — all concrete,
  all composable, all sorry-free.
* **Tag framework**: 5 categories (algebraic / structural / regime /
  witness / partitioned), populated generator lattice, bundle
  bridges (FpSum, FpDot, FpSumCompensated), pattern guide,
  forward-compat attributes.
* **Meta-lemma kernel**: round_preserves_* family, unified
  round-witness helpers, RModeLaws bundle.
* **Custom tactics**: `linearize`, `bound_calc`, `zpow_norm`.
* **Layer of abstraction over algorithms**: `FpSumBound`,
  `FpDotProductBound`, `FpMatVecBound`, `FpSumBoundCompensated`,
  `FpDotProductBoundCompensated`, all instantiable from concrete
  algorithms.
* **Backward error framework**: shipped, but underused (no concrete
  `PerturbationLift` instances).

What's missing at the strategic level:

1. **No end-to-end showcase.** Every piece composes in theory; no
   demonstration over a realistic workload.
2. **No tag-framework integration tests.** Signature regressions are
   discovered only when downstream demos break.
3. **Several deferred completions** (T-S1, partitioned-softmax
   downstream, letI→def, PerturbationLift instances, mixed-precision
   bridge).
4. **Backward-error framework underused** — composition track
   shipped without concrete lifts.

---

## Ranked recommendations

### Tier 1: Stress-test the stack

#### R1: End-to-end verified forward-pass capstone

**Pick**: 2-layer MLP with constrained input (e.g., normalized
pixels in `[0, 1]`), bounded weights, one-hot target, CE loss.

**Why**:
- Validates the whole stack against a real composition, not a toy.
- Exposes friction we can't see in isolation (signature ergonomics,
  tag composition, bundle wiring).
- Produces a teachable showcase artifact.
- Forces the design conversation: *how painful is it to actually
  write the full hypothesis list?*

**Scope**: ~500–800 lines.

**Status**: in progress (2026-04-22).

#### R2: Tag-framework integration test suite (T-D6)

A focused `Flean/Tags/TestCases.lean` (parallel to
`BoundCalc/TestCases.lean`) that smoke-tests the propagation/
generator/bridge signatures.  Catches regressions cheaply.

**Scope**: ~200 lines.  Pairs naturally with R1 — when the capstone
stresses signatures, the tests keep them honest.

### Tier 2: Framework completions

#### R3: Partitioned softmax downstream

The ~200–300 lines deferred in T-M3.  Re-prove softmax with
per-index case split on `IsBoundedRangeOn` membership, producing
differently-tight coefficients on `i ∈ S` vs `i ∉ S`.  Makes
`IsBoundedRangeOn` a fully first-class tag with a real consumer.

**Scope**: ~250 lines.

**When**: only worth doing if a real workload asks for heterogeneous
per-index tagging.

#### R4: T-S1 — LSE/CE tail elimination under separation

Softmax has `fpSoftmax_bound_of_separated` (drops `subnormalConst`
tail under `IsBoundedRange` + separation).  LSE and CE don't have
analogs.  Mechanical extension.

**Scope**: ~300 lines.

#### R5: Concrete `PerturbationLift` instances

Backward-error framework has `BackwardResult.compose` shipped but no
concrete lift instances.  Ship Horner / weighted-sum lift (Λ =
condition number) to unlock real usage.

**Scope**: ~200–300 lines.

### Tier 3: New primitives / capabilities

#### R6: Mixed-precision bridge — **SHIPPED 2026-04-23 + extended 2026-04-25**

Formalize FP16/BF16 → FP32 accumulation errors.  Bridges
StorageFormats ↔ Operations.  ~950 lines across six files, sorry-free.

Shipped pieces:
- `ToFp.lean` — exact widening `StorageFp sf → FiniteFp ff_wide`
  via `FitsInNormal`; 9 concrete instances.
- `FromFpBound.lean` — generalized `fromFp_widen_val_eq_round` capstone
  (handles the wider-than-`sf.toFloatFormat` case) + normal/unified
  narrowing error bounds.
- `MixedPrecision.lean` — triangle-inequality composition for
  compute-in-wide / store-in-narrow.
- `Quantization.lean` — concrete η_sf and subnormalConst_sf for
  E4M3/E5M2/E3M2/E2M3/E2M1.
- `NarrowingContext.lean` — bundle of typeclasses + format-validity
  proofs; replaces ~7 `@`-form args per theorem with one struct.
  `ofRNE` constructor synthesizes from `[UseRoundingPolicy RNE]`.
- `MixedPrecisionDemo.lean` — concrete E3M2 demo evaluating the
  bound to `(1/8)·|target| + (9/8)·ε_wide + 1/32`.

Follow-ups carried over as separate items: see R6.1–R6.5 below.

#### R6.1: Tag-framework bridge for StorageFormats — **next**

Bridge `Flean/Tags/` propositions through the widen/narrow pipeline.
Concretely:

- `IsBoundedRange.toFiniteFpWiden`: widening preserves any interval
  bound (trivial since widening is exact, but needs the tag-flavored
  signature so consumers can chain).
- `HasAbsBound.fromFp_narrow`: narrowing tightens to
  `(1 + η_sf)·c + subnormalConst_sf`.  Mirrors the existing
  `round_preserves_abs_bound_*` meta-lemmas.
- `IsNonneg`/`IsZero`/etc. preservation through the pipeline (cheap;
  same shape as `IsBoundedRange`).
- A `BundleAbsBound`-style bridge: given an `FpSumBound`/`FpDotProductBound`
  in `ff_wide` plus narrowing, derive a `HasAbsBound` on the narrowed
  storage output.

**Why it pays off**: any client already using the tag framework
inherits quantization-aware bounds for free.  Best ROI of the R6
follow-ups — small, additive, immediately useful.

**Scope**: ~150 lines.

#### R6.2: `WideContext` bundle + concrete `mixedFpMul`/`mixedFpAdd`

Build:
- `WideContext R ff_wide` parallel to `NarrowingContext`, bundling
  the wide-format typeclasses (`RMode`/`RModeExec`/etc. for ff_wide).
- `mixedFpMul (sf : StorageFormat) (ff_wide : FloatFormat) :
  StorageFp sf → StorageFp sf → StorageFp sf` defined as
  `narrow ∘ fpMul ∘ widen×widen`, with a packaged error bound.
- Same for `mixedFpAdd`, possibly `mixedFpFMA`.

Turns the abstract Phase 4 composition theorem into shipped concrete
primitives.  Surfaces the dual-typeclass plumbing that motivates the
`WideContext` bundle.

**Scope**: ~200–300 lines.  Sequenced after R6.1 (so the wide+narrow
ops can use tag-framework bounds directly).

#### R6.3: E4M3 narrowing (NaN-reserve precondition)

The current narrowing chain requires
`sf.maxManFieldAtMaxExp ≥ 2^sf.manBits - 1`.  E4M3 reserves one
mantissa pattern at maxExp for NaN, so it has 6 < 7 and fails this
hypothesis.  E4M3 is the dominant FP8 format in production ML
(Hopper/Blackwell, Meta training), so a parallel proof path that
accounts for the reserved pattern is high-value.

Open question: what does `fromFp` currently do when the rounded result
lands on the NaN-reserved pattern?  Saturate?  Produce NaN?  This
informs whether the fix is a precondition relaxation, a separate
overflow case, or deeper.

**Scope**: ~200–400 lines depending on the answer to the open question.

#### R6.4: E5M2 → Binary16 subnormal-tolerant widening

`FitsInNormal` requires `ff.min_exp ≤ 1 - bias_sf - manBits_sf`,
which fails for `E5M2 → Binary16` (the only practical pair that
doesn't fit).  Would need a `toFiniteFpWiden_subnormal` variant that
allows the widened result to land in `ff_wide`'s subnormal range.

Less practical than R6.3 (E5M2 gradients are normally accumulated in
FP32, not FP16), but completes the format-pair lattice.

**Scope**: ~100–150 lines.

#### R6.5: Quantized linear layer (flagship demo)

Compose R6.1 + R6.2 + R6.3 into an `ActivatedLayer`-style demo with
FP8 storage and FP32 compute.  Analogous to `MLP/Layer.lean` but with
mixed precision: weights stored as E4M3, activations stored as E4M3,
matmul accumulated in Binary32, narrowed back to E4M3.

Closes the loop with the MLP work — the natural next "milestone"
after R6.1/R6.2 land.

**Scope**: ~500+ lines; depends on R6.1, R6.2, R6.3.

#### R7: Newton-Horner concrete instantiation

The accumulator/Newton stack lacks a concrete numerical
demonstration.  Compute explicit convergence radii for binary32/64
on a specific polynomial.  Different arc from the ML/tag work; good
variety.

**Scope**: ~300 lines.

#### R8: New tags — `IsQuantized`, `HasRangeBound`, `IsSterbenzSameSign`

Each only worth shipping when a concrete consumer asks.

### Tier 4: Long-term / architectural

#### R9: Tag inference engine

Below threshold per the design note (~15 tags / 5+ chained).  Can
prototype when usage pattern emerges.  Attribute infrastructure
already in place.

#### R10: `letI` → `def` refactor (E3)

Deferred until a fifth wrapper hits the `simp only [← hX_def]` pain.

---

## Decision-shaping questions

These influence which tier to push next:

### Q1: Does the framework pay off yet?

The ML primitives are fully concrete with or without the tag layer.
The tag framework adds tighter bounds and cleaner specializations
— but has anyone hit a pain point that the tag framework actually
solves?

If yes → invest in framework ergonomics + new tags.
If no → maybe the framework is complete enough; further tag work is
diminishing returns until a consumer demands it.

### Q2: Audience — "me building primitives" or "external researcher reading"?

The capstone (R1) looks very different in each case.

- *Builder audience*: focus on primitive reuse patterns, terse
  composition, library-like API.
- *Reader audience*: focus on narrative, result clarity, motivating
  examples.

The current shipped code leans builder.  R1 forces a decision.

### Q3: Widening or deepening?

- **Widen**: more primitives, tags, ML capabilities (R6, R7, R8).
- **Deepen**: better abstractions, cleaner APIs, automation (R2,
  R5, R9, R10).

Both are valid; the backlog has both.  Resource allocation
question.

---

## Current pick (2026-04-22)

**R1 — end-to-end MLP forward-pass capstone**.

Reasoning: it's the single move that stress-tests everything at
once, gives a demonstrable artifact, and surfaces ergonomic friction
that informs all subsequent infrastructure work.  Aligns with Q1
("does the framework pay off?") by forcing real composition.

Subarchitecture: 2-layer MLP, constrained-input (pixel-style
`[0, 1]` magnitude), bounded weights/biases, one-hot target, CE
loss.  Every layer composes a `FpDotProduct` row, an `fpAddFinite`
bias, and (optionally) an activation.  Final loss via existing CE
machinery.

If R1 lands cleanly: do **R2 (test suite)** as the natural
follow-up (test what we just stressed).  If R1 hits major friction:
the friction itself becomes the next deliverable
(`letI→def`, tighter signatures, new bundle wrappers, etc.).

## Current pick (2026-04-25)

R1 (MLP capstone) and R6 (mixed-precision bridge + NarrowingContext)
both shipped.  Sequencing:

1. **R6.1 — tag-framework bridge for StorageFormats** (current pick).
   Smallest scope, biggest immediate utility, unlocks the
   "quantization-as-typed-tag" framing.
2. **R6.2 — `WideContext` + concrete `mixedFpMul`/`mixedFpAdd`** (next).
   Turns the abstract composition into shipped primitives.

The `NarrowingContext` pattern (one-context-per-FloatFormat-scope) is
generalizable — any time a Flean theorem needs typeclass instances at
a non-ambient `FloatFormat`, the same bundle pattern applies.  Worth
keeping in mind as a "promote to standard pattern" candidate after a
second use site (`WideContext` in R6.2 is the second use site).
