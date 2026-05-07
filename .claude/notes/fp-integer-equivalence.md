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
