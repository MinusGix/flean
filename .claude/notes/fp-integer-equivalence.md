# FP ↔ Integer Equivalence

Tracking doc for the area: proving FP operations (and compositions) are
*equivalent* to simpler integer / bitwise operations, possibly with a small
correction term. Distinct from forward/backward error work — that bounds
`|fp - real|`; this proves `fp = some_simpler_thing` (or `fp ≈ some_simpler_thing`
within an explicit ε).

## Motivation

The CPU's integer pipeline is faster, wider, and more energy-efficient than its
FP pipeline on most modern hardware. If we can prove "this FP computation
equals this integer computation under conditions C", we unlock:

- **Soft-float emulation** — running unquantized NN inference on integer SIMD
  instructions (AVX-512 VNNI, ARM NEON, etc.).
- **Compile-time simplification** — `fpMul x (2^k)` → exponent bump, no FP op.
- **Exact bit-level reasoning** for low-bit FP formats (E4M3, E5M2) — the
  state space is small enough to enumerate.

## Standing preferences

1. **Exactness preferred** over approximation. When approximation is the only
   option (Quake invsqrt, fast-`expf`), it's acceptable but should come with a
   tight quantitative `|fp_op x - simpler_op x| ≤ ε` bound — "basically accurate"
   should be made *trivially* easy to invoke.
2. **Inputs assumed finite, non-NaN by default**. Theorems shouldn't require
   that hypothesis when not actually needed; but special-case carve-outs (e.g.,
   the result is normal) are fine.
3. **Normal vs subnormal**: pragmatic — special-case normal-only theorems are
   useful, but don't *always* assume normal. Subnormal-tolerant variants are
   first-class follow-ups when worth proving.
4. **De-emphasize quantization**. Already heavily explored externally
   (TFLite, ONNX, INT8 matmul). Often broken in subtle ways. We may revisit
   INT8 matmul later, but the *core logic* simplifications below have less
   external coverage and more research value per proof.

## Existing infrastructure (already in Flean)

- **`Flean/Encoding/Basic.lean`** — `FloatBits`, `FloatBitsTriple`, accessors
  (`sign`, `exponent`, `significand`), classifiers (`isFinite`, `isNormal`,
  `isSubnormal`, `isNaN`, `isInfinite`, `isZero`).
- **`Flean/Encoding/Conversion.lean`** — `FloatBits ↔ Fp` round-trip.
- **`Flean/Encoding/BitSize.lean`**, **`Encoding/Quotient.lean`** — bit-level
  utilities, NaN-payload quotient.
- **`Flean/StorageFormats/`** — concrete formats (E4M3, E5M2, E3M2, Binary16,
  Binary32, Binary64). Round-trip proofs.
- **Tag framework** (`Flean/Tags/`) — `IsBoundedRange`, `HasAbsBound`, etc.
  Useful for "input is in [a, b]" preconditions.
- **Subnormal-tolerant operations** — Softmax core lemma, fpAddFinite, etc.
  The pattern (split on subnormal vs normal) is well-trodden.
- **`notNegZero`**, `isZero_iff` — handle the −0 edge case for ReLU-like ops.

## What's missing (the gap this area fills)

- Theorems linking `Fp`/`FiniteFp` operations to `FloatBits` operations.
  Currently there's `bits ↔ Fp` round-trip, but few "FP-op X equals bit-op Y"
  results. That's the bridge we need to build.
- An `EquivalentOn S f g` / `CloseEquivalentOn S f g ε` framework that lets
  equivalences compose like Lipschitz/error bounds do.
- A pattern-matching tactic for recognizing simplifiable FP subexpressions.

## Roadmap by phase

Roughly ordered easy → hard. Each phase should be self-contained and shippable.

### Phase 1 — Trivial bit-level (single-op, exact)

Fastest wins; building blocks for everything later.

- [ ] **`fpNeg_eq_bit_xor`**: `bits (fpNeg x) = (bits x) XOR sign_mask`. One bit
  flip; no rounding; the only edge case is NaN payload preservation (skip if
  inputs assumed non-NaN).
- [ ] **`fpAbs_eq_bit_mask`**: `bits (fpAbs x) = (bits x) AND (NOT sign_mask)`.
- [ ] **`fpMul_pow2_eq_exponent_add`**: `bits (fpMul x (encode_pow2 k)) =
      bit_increment_exponent (bits x) k`, under "result is normal" hypothesis.
  - [ ] Subnormal-tolerant variant — entry/exit cases via existing infrastructure.
- [ ] **`fpDiv_pow2_eq_exponent_sub`** — symmetric.
- [ ] **`fpCopySign`**: extract sign of one, replace sign of another.

### Phase 2 — Comparison and ordering

Same-sign comparisons reduce to integer comparisons on the bit pattern. This
unlocks integer-pipeline argmax/max/min, useful for softmax/attention.

- [ ] **`fpLt_same_sign_eq_intLt_bits`** — both inputs non-negative (or both
  non-positive) → bit comparison preserves order.
- [ ] **`fpMax_same_sign_eq_intMax_bits`** + symmetric for `fpMin`.
- [ ] **`fpArgmax_nonneg_eq_intArgmax_bits`** — vector argmax for nonneg inputs
  is integer argmax of bit patterns. Important for softmax stability.
- [ ] Mixed-sign case as a small case split (or a separate "general but with
  sign-bit twiddle" theorem).

### Phase 3 — ReLU and friends

ReLU is the most-used activation by far. If we can prove it's a single masked
select on bits, that's a huge win for inference simplification.

- [ ] **`relu_eq_masked_select`**: `bits (relu x) = (bits x) AND mask_from_sign(x)`,
  where `mask_from_sign` is `0 if sign bit set, all-ones otherwise`. Care for
  −0 (use `notNegZero`-style carve-out or define `relu` to map −0 to +0).
- [ ] **`leakyRelu_pow2_decomp`**: with leak `2^{-k}`, the negative branch is
  pure exponent decrement. Composes with Phase 1's `fpMul_pow2_eq_exponent_add`.
- [ ] **`hardSigmoid_eq_clamp_int`**: hard-sigmoid is a clamp; for finite
  inputs, the clamp can be done on bit patterns via Phase 2's comparison
  primitives.
- [ ] **`hardTanh_eq_clamp_int`** — similar.

### Phase 4 — Equivalence framework

Once we have a critical mass of bit-level theorems, package them as an algebra.

- [ ] Define `EquivalentOn (S : Set X) (f g : X → Y)` — pointwise equality on
  a subset. Composition rules (transitivity, congruence under op).
- [ ] Define `CloseEquivalentOn S f g ε` — within ε. Composition: `ε`s add (with
  Lipschitz multiplier when chaining through a Lipschitz function — reuses the
  existing Lipschitz framework).
- [ ] Bridge tags → equivalence: `IsBoundedRange I xs → EquivalentOn ... fp_op
  bit_op` for ops where the bit equivalence holds on the range.
- [ ] **Pattern-matching tactic** — recognize FP subexpressions matching known
  templates (Phase 1–3), instantiate the equivalence.

### Phase 5 — Numerical tricks (approximate, not exact)

Famous bit-level FP tricks. Each becomes "this FP function ≈ this bit-op chain"
with explicit ε.

- [ ] **Fast inverse square root** (Quake 3 trick). `1/√x ≈ (magic - bits(x) >> 1)`
  + Newton iteration. The bit-twiddle is the initial estimate; one Newton step
  gives ~1.5 decimal digits, two gives ~3. Can chain with our existing Newton
  infrastructure.
- [ ] **Soft-`log2`**: `log2 x ≈ exponent_extract(x) + poly(mantissa)`. Exponent
  extraction is a single bit op; the polynomial correction is FP. Common
  building block for `logf` libraries.
- [ ] **Soft-`exp`**: split into `2^k · y` where `k = floor(x · log2 e)`,
  `y ∈ [1, 2)`. Inject `k` into exponent via bit op; compute `y` via
  polynomial. Used in `expf` / `expm1f` libraries.

### Phase 6 — Layer-level fusion (flagship example)

The big payoff: take a small NN subsection and prove it equals a much simpler
integer-op expression. Picks up everything from Phases 1–4.

- [ ] **Binary-weight ReLU layer (XNOR-Net style)**: `ReLU(W * x + b)` with
  `W ∈ {−1, +1}^{m×n}`. Multiplication = sign flip (Phase 1); ReLU = masked
  select (Phase 3). Whole layer becomes XNOR + popcount + mask, an integer-op
  expression.
- [ ] **Affine fusion**: consecutive linear layers `A · (B · x + b₁) + b₂ =
      (A · B) · x + (A · b₁ + b₂)`. True mathematically; FP version requires
  error tracking from the existing framework.
- [ ] **Power-of-2 weight rewrite**: detect that a weight is a power of 2,
  rewrite the multiplication as a shift. Useful in pruning / quantization-aware
  training scenarios.

## Catalog of specific theorem ideas

(Pulled out for cross-reference; all are listed under their phase above.)

| Name | What | Phase |
|---|---|---|
| `fpNeg_eq_bit_xor` | `bits ∘ fpNeg = bit_xor sign_mask` | 1 |
| `fpAbs_eq_bit_mask` | `bits ∘ fpAbs = bit_and ¬sign_mask` | 1 |
| `fpMul_pow2_eq_exponent_add` | `×2^k = exponent + k` (normal carve-out) | 1 |
| `fpLt_same_sign_eq_intLt_bits` | same-sign FP `<` = int `<` on bits | 2 |
| `relu_eq_masked_select` | ReLU as a single bit mask | 3 |
| `leakyRelu_pow2_decomp` | leak = `2^{-k}` becomes exponent dec | 3 |
| `EquivalentOn` / `CloseEquivalentOn` | composition framework | 4 |
| Quake invsqrt approx bound | bit twiddle + Newton step | 5 |
| Soft-`log2` / Soft-`exp` | exponent extract + poly | 5 |
| Binary-weight ReLU layer = XNOR + popcount | flagship | 6 |

## Open design questions

- **Where do bit-op theorems live?** Probably under `Flean/Encoding/BitOps.lean`
  or a new `Flean/IntegerEquivalence/` directory. Decide once we have ~5
  theorems and see if they cluster.
- **`EquivalentOn` typeclass vs proposition vs structure?** Lean idioms vary.
  The Lipschitz framework chose `structure`; we probably want the same for
  consistency, but `Prop` is simpler if no extra fields are needed.
- **Tactic ergonomics**: where in the user's workflow does the "recognize this
  FP expression as equivalent to this bit-op expression" call happen? Inside a
  proof, or as a preprocessing pass that rewrites the goal? The former composes
  with everything else; the latter is more reusable.
- **NaN handling carve-outs**: how aggressively to assume `¬isNaN`. Probably
  default to "all inputs finite non-NaN" as standing hypothesis (matches
  `FiniteFp` already), revisit if a specific theorem benefits from supporting
  NaN.

## Out of scope (and why)

- **Full IEEE 754 NaN-propagation semantics** — most ML deployments don't
  care; carve out finite-non-NaN as default.
- **Quantized inference (INT8 matmul, sub-8-bit weights)** — well-trodden
  externally, often subtly broken, and orthogonal to "core logic"
  simplifications. May revisit later for a specific high-leverage piece (e.g.,
  proving a specific INT8 kernel matches its FP reference within quantization
  error), but not the priority.
- **Logic-gate-level simplification (FPGA / custom ASIC targets)** —
  fascinating but only matters if you control silicon. Integer-op level is the
  practical sweet spot.
- **Hardware-specific instruction modeling (AVX-512, AMX, NEON)** — not in
  the math layer. The integer-op equivalences we prove become *targets* for
  these instructions, but the binding is downstream of the math.

## Where to start

Highest value-per-difficulty concrete first proof: **`fpMul_pow2_eq_exponent_add`**
under "result is normal". Reasons:

1. Building block for *every* power-of-2 weight rewrite.
2. Exercises the bridge between `FiniteFp` and `Encoding/`'s bit-level ops —
   currently mostly absent on top of the encoding scaffolding.
3. Same proof shape generalizes: `fpNeg`, `fpAbs`, ReLU all decompose into
   "sign/exponent tinkering" with the same skeleton.
4. Clean version (no subnormal entry/exit) is small; subnormal-tolerant is the
   natural follow-up using existing infrastructure.

After that: **same-sign FP-compare ↔ integer-compare** unlocks integer-pipeline
argmax/max/min, directly useful for inference (softmax stability, attention,
top-k).

Then enough primitives to attempt a small **binary-weight ReLU layer end-to-end**
as flagship — stresses every primitive (sign flip, masked select, integer
popcount) and produces a result that's both correct and *visibly* a major
simplification over the FP version.

## Additional ideas / backlog

Items not on the original 6-phase roadmap, in rough order of "natural to add
once the surrounding infrastructure exists":

### Bit-pattern classifiers (Phase 1.5)
Each of these is a single bit-pattern test that decides an `Fp` predicate.
Together they cover the IEEE 754 `fpClassify` enum.

- [ ] **`isNaN_eq_bit_test`** — `f.isNaN ↔ b.isExponentAllOnes ∧ ¬b.isTSignificandZero`
  (already a fact in `Encoding/Basic.lean`; surface as a bridge `Fp.isNaN ↔ ...`).
- [ ] **`isInfinite_eq_bit_test`** — symmetric to above.
- [ ] **`isFinite_eq_bit_test`**, **`isNormal_eq_bit_test`**,
      **`isSubnormal_eq_bit_test`**, **`isZero_eq_bit_test`** — same idea.
- [ ] **`fpClassify`** as a single ADT of these, with the tag computed from
  `(b.toBitsTriple.exponent.isZero, b.toBitsTriple.exponent.isAllOnes,
  b.toBitsTriple.significand.isZero)` (8 cases collapse to 5).
- [ ] **`isPowerOfTwo`** — bit-pattern: trailing significand all zero, exponent
  in normal range. Useful for compile-time mul-by-pow2 rewrites at *runtime*.

### `nextUp` / `nextDown` / `nextAfter` (Phase 1.6)
IEEE 754 §5.3.1: `nextUp x` is the smallest representable value greater than `x`.
At the bit level, this is *integer increment* on the bit pattern (with sign-magnitude
care: if positive, increment; if negative, decrement). Strong "integer pipeline"
application — these are used in interval arithmetic, error analysis, and
adversarial ML to compute exact ULP-level perturbations.

- [ ] **`nextUp_eq_bit_increment`** for positive `f`; symmetric for negative.
- [ ] **Sign-magnitude integer increment** as a bit-level operation, with the
  zero-crossing case (smallest positive subnormal vs smallest negative subnormal).
- [ ] **`fpUlp_eq_pow2`** — ULP at `f` is `2^(e - prec + 1)` for normal `f`,
  representable directly as a bit pattern. Connects `Flean/Ulp.lean` to bit ops.

### Total ordering ↔ signed-magnitude integer comparison (Phase 2.5)
IEEE 754 §5.10: `totalOrder` on FP corresponds *exactly* to signed-magnitude
integer comparison on the bit pattern (with NaN ordering convention). This is
the strongest "FP comparison = integer comparison" theorem available, stronger
than the same-sign carve-out. Hardware-relevant: no FP comparator needed for
total-order checks.

- [ ] **`totalOrder_eq_intCmp_signMagnitude`** — full theorem. Likely needs a
  "view bits as signed-magnitude integer" helper at the `BitVec` level.

### Format conversions (Phase 1.7 or Phase 4 add-on)
Bit-level statement of widening/narrowing between FP formats. Already partially
covered by `StorageFormats/MixedPrecision.lean` at the value level; the bit-level
version states "widening = pad significand with zeros, rebias exponent".

- [ ] **`widen_bits_eq_pad`** — Binary16 → Binary32 widening at the bit level.
- [ ] **`narrow_bits_eq_round_truncate`** — Binary32 → Binary16 narrowing
  (involves rounding, so the bit-level statement has an `RModeNearest` carve-out).

### Comparison-derived ops (Phase 2.5)
Beyond max/min, IEEE 754 / hardware exposes:

- [ ] **`fpClamp_eq_bit_clamp`** — `clamp x lo hi`. Composes `fpMax` and `fpMin`,
  so derives directly from Phase 2.
- [ ] **`fpSign_eq_bit_test`** — `sign x ∈ {-1, 0, +1}` from bit pattern.
- [ ] **`fpAbsCompare`** — compare by magnitude only, ignoring sign.

### Activation function family (Phase 3+)
Beyond ReLU/leaky ReLU/hardSigmoid/hardTanh:

- [ ] **`prelu`** — parametric ReLU with FP slope; reduces to Phase 3 if slope
  is a power of 2.
- [ ] **`elu`** — uses `expm1`; relates to Phase 5 soft-`exp`.
- [ ] **`swish`** / **`silu`** — `x * sigmoid(x)`. Bit-level equivalences
  through approximate sigmoid + multiplication.
- [ ] **`gelu` approximate variants** — tanh-based approximation has a Horner
  polynomial that could be expressed via Phase 5 building blocks.
- [ ] **Quantized activations**: bit-bucketing into a lookup-table is a *direct*
  integer-op statement of an approximate activation. Could unlock practical
  inference speedups.

### Numerical recipes (Phase 5 expansions)
Beyond Quake invsqrt and soft-log/exp:

- [ ] **Reciprocal initial estimate** — `1/x ≈ magic - bits(x)` (similar magic
  constant logic). Used in software-divide implementations.
- [ ] **`expm1` near-zero fast path** — bit-level detection of "x close to 0"
  triggers a Taylor approximation via Phase 5 polynomial.
- [ ] **`log1p` near-one fast path** — symmetric.
- [ ] **`pow(x, y)` via `exp(y · log(x))`** — composition of soft-exp and
  soft-log. Big composition demo.
- [ ] **`sqrt` Newton refinement** with Quake invsqrt as initial estimate.

### Layer/architecture flagships (Phase 6 expansions)
Beyond the binary-weight ReLU layer:

- [ ] **Quantized linear layer (INT8)** — partially deferred per "out of scope".
  Could revisit as a *targeted* proof showing INT8 kernel ↔ FP reference within
  quantization error.
- [ ] **Attention head**: `softmax(QK^T / √d) · V`. Composes Phase 2 (argmax for
  stability) + Phase 5 (soft-exp) + matmul. Very visible payoff for transformer
  inference.
- [ ] **Convolution layer with binary/ternary weights** — natural extension of
  binary-weight ReLU layer to 2D.
- [ ] **MoE routing**: top-k argmax via Phase 2 + linear combo of expert outputs.
  Argmax dominates MoE compute, so a Phase 2-based proof captures real value.
- [ ] **Embedding lookup**: pure indexing — but interesting bit-level statement
  about how embeddings are encoded. Probably out of scope (table indexing isn't
  FP arithmetic).

### Tactic / framework backlog (Phase 4 expansions)
Beyond `EquivalentOn` and pattern-matching:

- [ ] **`bit_equiv` tactic** — given `Fp` expression, find equivalent bit-op
  expression. Starts simple (single-op rewrites) and grows to handle composition.
- [ ] **`bit_simplify` simp set** — `@[bit_simp]` attribute on every theorem of
  the form `Fp_op ↔ bit_op`, then `simp only [bit_simp]` rewrites entire FP
  expressions in one pass.
- [ ] **Reflection / decision procedure** for low-bit FP formats (E4M3, E5M2):
  enumerate all bit patterns, mechanically check FP-op = bit-op equivalence.
- [ ] **`BitEquivalent` typeclass** — distinct from `EquivalentOn`, captures
  "FP op `f` and bit op `g` agree on all non-NaN inputs". Composes via instances.

### Bit-level libm intrinsics (Phase 1.8)
The traditional libm bit-twiddle functions are direct bit operations with
specifications already covered by IEEE 754. Each is a small, focused proof.

- [ ] **`frexp`** (`x → (m, e)` such that `x = m * 2^e`, `m ∈ [0.5, 1)`). Bit
  level: split at the exponent boundary. The "exponent" output is the biased
  exponent minus a constant.
- [ ] **`ldexp x k`** (= `x * 2^k`). Already done as `fpMul_pow2_eq_exponent_add`,
  but the libm `ldexp` is the standard external-facing name; surface a
  `ldexp_eq_setBiasedExponent` corollary for downstream codegen.
- [ ] **`signbit x`** — single bit extract. Trivial after `signFlip` / `setSign`.
- [ ] **`fdim x y`** = `max(x - y, 0)`. Decomposes via `fpSub` + Phase 3 ReLU.
- [ ] **`scalbln`** / **`scalbn`** — close cousins of `ldexp`; same bit-level
  story.
- [ ] **`logb`** / **`ilogb`** — extract biased exponent (subtract bias);
  already there via `Fp.logB_exact` in `Operations/LogBScaleB.lean`. Surface
  as a bit-level corollary.

### Round-to-integer family (Phase 1.9 or new phase)
For finite FP that fits in the integer range, rounding to integer can be
implemented as a bit-level shift + masking operation.

- [ ] **`trunc`** (toward zero): clear bits below the integer-binade boundary.
- [ ] **`floor`** / **`ceil`**: trunc with sign-aware adjustment.
- [ ] **`round_to_nearest_int`**: round-to-nearest-even applied to the integer
  binade. The "round bit + sticky" rule is bit-level extraction.
- [ ] **`fpModf`**: `(integer_part, fractional_part)` decomposition. Bit-level
  splits the significand at the integer-binade boundary.
- [ ] **`fpFmod`** (`x mod y`): more involved, but for `y` a power of 2, it's
  a low-bit mask.

### FP equality and ordering shortcuts (Phase 2.7)
Beyond `<`, the ordering primitives have bit-level versions.

- [ ] **`fpEq_iff_bit_eq` (modulo NaN)**: `x = y` (Fp `=`) iff `bits x = bits y`,
  with the carve-out that NaN doesn't equal anything. The bit-level
  formulation is `b₁ = b₂ ∨ (b₁.isZero ∧ b₂.isZero)` (handle ±0 collapse).
- [ ] **`fpNeq` via bit XOR**: `x ≠ y` iff bits differ (modulo ±0 and NaN).
- [ ] **`fpUnordered`**: NaN check shortcut. Single bit test.

### Constant detection / compile-time recognizers (Phase 1.5 extension)
Recognize specific FP values via their bit pattern. Useful for compile-time
specialization (e.g., recognize `f * 1.0` and elide).

- [ ] **`isOne_iff_bit`**: `f = 1` iff `b.toBitsTriple = (false, bias, 0)`.
- [ ] **`isMinusOne_iff_bit`**: same but `(true, bias, 0)`.
- [ ] **`isInteger_iff_bit_low_zero`**: `f ∈ ℤ` for finite `f` iff its
  trailing significand bits below the integer-binade boundary are zero.
- [ ] **`isHalfInteger_iff_bit`**: `f ∈ ℤ + 1/2`. Similar bit-level test.

### Single-rounding FMA at the bit level (Phase 5 flagship)
The IEEE 754 fused multiply-add `FMA(a, b, c) = round(a·b + c)` with single
rounding is *the* canonical hardware FP op that doesn't decompose into simpler
FP ops without losing precision.

- [ ] **`fpFMA_eq_bit_pattern`**: bit-level recipe that matches single-rounding
  FMA. Probably involves wide intermediate (2× precision) addition + final
  rounding. Could become a major framework theorem; the proof is non-trivial
  but well-trodden in the verified-FP literature.

### Stochastic rounding (Phase 5 expansion)
Modern ML training uses stochastic rounding for low-precision training.

- [ ] **`stochasticRound_eq_bit_recipe`**: SR can be implemented as
  "deterministic round-down + add a random bit at the rounding position".
  Bit-level statement: `SR(x, r) = trunc(x) + (if r < frac(x) then 1 ULP else 0)`.
- [ ] **Unbiasedness**: prove `E[SR(x, U)] = x` over uniform `U` — useful for
  ML training convergence proofs.

### Verified soft-FP library (Phase 6 flagship)
Take the union of bit-equivalence theorems shipped in earlier phases and
package as a *complete* soft-FP library: every IEEE 754 FP op implemented at
the integer level with a bit-equivalence theorem.

- [ ] **`SoftFp` namespace**: parallel to `Fp` but every op is a function on
  `FloatBits` rather than `Fp`. Each `SoftFp.fpAdd`, `SoftFp.fpMul`, etc.
  computes via integer ops only.
- [ ] **Equivalence theorem family**: `ofBits (SoftFp.fpAdd b₁ b₂) = fpAdd
  (ofBits b₁) (ofBits b₂)` for each op (with NaN/normal/sub carve-outs).
- [ ] **Decoupled execution**: a downstream consumer wanting "FP from
  integer pipeline" can use `SoftFp` directly + the equivalence theorems for
  correctness.

### bit_decide tactic for low-bit formats (Phase 4 expansion)
Low-bit FP formats (E4M3, E5M2, FP4) have ≤256 bit patterns. Mechanical
verification of FP-op = bit-op equivalence is tractable.

- [ ] **`bit_decide` tactic**: takes a goal of the form
  `∀ b₁ b₂ : FloatBits, P b₁ b₂` (where `b` is over a low-bit format), and
  closes by exhaustive enumeration. Uses Lean's `Decidable` instance machinery.
- [ ] **Pre-baked verification suite**: run `bit_decide` for every shipped
  bit-equivalence theorem on E4M3 / E5M2 to confirm correctness against
  hardware-style ground truth.

### Bit-level magic constants (Phase 5 expansion)
Famous magic constants that show up in bit hacks; proven correct against
their intended approximations.

- [ ] **`quakeInverseSqrtMagic`**: the `0x5f3759df` constant, with the
  approximation theorem `|invsqrt_approx x - 1/√x| ≤ ε`.
- [ ] **`exp2Magic`** / **`log2Magic`**: similar magic constants for soft-exp /
  soft-log fast paths.

### Reproducibility / determinism via bit equivalences (Phase 5+ expansion)
Bit-level equivalences can ground reproducibility claims.

- [ ] **Order-independent sum criterion**: bit-level test on input range that
  guarantees `sum(perm(xs))` is order-independent. (Roughly: all values fit
  in a single binade at the accumulator's precision.)
- [ ] **Cross-platform bit-equivalence**: prove that a specific algorithm
  produces bit-identical results across IEEE 754 conformant hardware (no
  fused ops, no extended precision, no FTZ).

### Hardware-pipeline metadata (low priority)
Tag theorems with metadata about which integer-pipeline instruction implements
them. Not affecting math, but useful for downstream codegen/SIMD targeting.

- [ ] **`@[hw_target ...]` attribute** on each bit-equivalence theorem,
  recording AVX-512 / NEON / RVV instruction names and rough latency.
- [ ] **Latency-aware fusion**: prefer chains of bit-ops with low cumulative
  latency over slightly shorter FP chains.

## Implementation status (live)

(Updated as implementations land. See `MEMORY.md` and
`memory/fp-integer-equivalence.md` for full provenance.)

- ✅ **Phase 1, sign-bit ops** — `Flean/IntegerEquivalence/Basic.lean` (sign
  flip ↔ neg, sign clear ↔ fpAbs, copySign bridge), via `setSign` / `withSign`
  workhorses.
- ✅ **Phase 1, fpMul ↔ exponent shift** — `Flean/Operations/MulPow2.lean`
  (`fpMul_pow2_normal_eq` structural form) + `Flean/IntegerEquivalence/MulPow2.lean`
  (`setBiasedExponent` workhorse + `ofBits_setBiasedExponent_eq_fpMul_pow2`
  bridge), under "input + result both normal" carve-out.
- ✅ **Phase 2.5, total ordering ↔ signed-magnitude bit comparison** (finite
  case) — `Flean/IntegerEquivalence/TotalOrder.lean`. `Fp.totalOrderBitLt` def
  + bridge `ofBits_lt_iff_totalOrderBitLt_of_finite`. Composes Phase 2
  sub-tolerant for same-sign with direct sign-decided cross-sign cases.
  Distinguishes `-0 < +0` correctly. Extension to ∞ is mechanical (sign decides;
  bit-magnitude is naturally maximal for ±∞).
- ✅ **Phase 1.5, bit-pattern classifiers** —
  `Flean/IntegerEquivalence/Classify.lean`. Bridges `Fp.isNaN/isInfinite/isFinite`
  to bit-level tests via `ofBits`. Plus FiniteFp-level decoded predicates
  (`isNormal`, `isSubnormal`, `isZero`, IEEE-strict subnormal) and
  `FiniteFp.isPositivePowerOfTwo` with its bit-level characterization (T = 0 and
  bit-normal exponent).
- ✅ **Phase 2, same-sign comparison ↔ unsigned bit comparison** (FULLY SHIPPED) —
  `Flean/IntegerEquivalence/Compare.lean`. Four bridges all sorry-free:
  - `ofBits_lt_iff_b_toNat_lt_of_normal_nonneg` (non-negative, normal-only)
  - `ofBits_lt_iff_b_toNat_gt_of_normal_nonpos` (non-positive, normal-only)
  - `ofBits_lt_iff_b_toNat_lt_of_finite_nonneg` (non-negative, sub-tolerant)
  - `ofBits_lt_iff_b_toNat_gt_of_finite_nonpos` (non-positive, sub-tolerant)
  Cross-sign / total ordering remains as a Phase 2.5 candidate.
