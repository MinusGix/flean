# Flean

Formal verification of IEEE 754 floating-point arithmetic in [Lean 4](https://lean-lang.org/).

## Overview

Flean is a Lean 4 library that formalizes floating-point number formats, all five IEEE 754 rounding modes, arithmetic operations, and their error bounds. The mathematical treatment follows the *Handbook of Floating-Point Arithmetic* by Jean-Michel Muller et al.

The library is generic over the number type (`R`), aiming to effectively work with any linearly ordered field (reals, rationals, etc.) rather than fixing a specific representation. The library aims to be computable, so that it can in principle be used as a (likely slow) software floating point implementation.

Separately, the library aims to formalize GPU floating point formats as well, to better talk about their error bounds and behavior. Though, we avoid formalizing base-10 (or arbitrary base) floating point due to relative obscurity.

## What's Proved

The entire library is **sorry-free** — all results are verified by Lean's proof checker. ~47k lines across 112 files.

### Rounding — all 5 IEEE 754 modes

Each mode (`roundDown`, `roundUp`, `roundTowardZero`, `roundNearestTiesToEven`, `roundNearestTiesAwayFromZero`) has:

- **Correctness** via `roundIntSig_correct` — the core rounding algorithm produces the right result
- **Relative error bounds** — `≤ 2^(1-prec)` for directed modes, `≤ 2^(-prec)` for nearest modes
- **Idempotence** — rounding an already-representable value is a no-op
- **Monotonicity** — `x ≤ y → round(x) ≤ round(y)` for all modes
- **Negation symmetry** — `roundDown(-x) = -roundUp(x)` and vice versa
- **Bracket property** — `roundDown(x) ≤ roundNearest(x) ≤ roundUp(x)`

### Arithmetic operations

| Operation | Correctness | Commutativity |
|-----------|------------|---------------|
| Addition (`fpAdd`) | `fpAddFinite_correct` | `fpAdd_comm` |
| Subtraction (`fpSub`) | `fpSubFinite_correct` | — |
| Multiplication (`fpMul`) | `fpMulFinite_correct` | `fpMul_comm` |
| Division (`fpDiv`) | `fpDivFinite_correct` | — |
| Square root (`fpSqrt`) | `fpSqrtFinite_correct` | — |
| Fused multiply-add (`fpFMA`) | `fpFMAFinite_correct` | `fpFMA_comm_ab` |

Each correctness theorem states: the operation's result equals the rounding mode applied to the exact mathematical result. Division and square root use a shared sticky-bit technique (`sticky_roundIntSig_eq_round`).

### Error-free transformations

- **Fast2Sum** — `fast2Sum_pos_exact`: `a + b = s + e` exactly when `|a| ≥ |b|`
- **TwoSum** — `twoSum_exact`: `a + b = s + e` for arbitrary signs (6-op variant in `TwoSum6Op.lean`)
- **TwoProduct** — `twoProduct_exact`: `a * b = p + e` using FMA
- **Sterbenz lemma** — subtraction is exact when `y/2 ≤ x ≤ 2y`
- **Veltkamp splitting** — `veltkampSplit_exact`: `a_hi + a_lo = a` exactly

### Algorithm error analysis

- **Kahan compensated summation** — Higham's Theorem 4.3: `|ŝₙ - Σxᵢ| ≤ (2η + nη²)·Σ|xᵢ|` (`kahan_higham_bound`). Two independent proof approaches (~1085 lines).

### Verified computation

- **Exp** — Correctly-rounded `exp(x)` via Taylor series + Padé-based irrationality gap termination argument. 5 files, sorry-free.
- **Log** — Correctly-rounded `log(x)` via alternating series bounds + MVT irrationality gap. 5 files, sorry-free.

### IEEE 754-2019 operations

- **Min/Max** — `fpMin`, `fpMax` with basic theorems
- **LogB/ScaleB** — `fpLogB`, `fpScaleB` (§5.3.3)
- **RoundToIntegral** — `fpRoundToIntegral` (§5.9)
- **Predecessor/Successor** — distance properties

### Storage formats (GPU/ML)

Concrete format definitions (E4M3, E5M2, E3M2, E2M3, E2M1, E8M0) with:

- **`fromFp` correctness** — conversion computes the correctly-rounded value (`fromFp_val_eq_round`)
- **Overflow handling** — saturation, infinity, and NaN overflow behaviors proved correct
- **Round-trip** — structural `roundtrip_general` via bitvector extensionality
- **Concrete values** — `one`, `maxFinite`, `minPos` with `toVal` proofs

### Encoding

- **Bit-level encoding/decoding** — `toBits_ofBits` + `ofBits_toBits` round-trip, sorry-free
- **Common constants** — verified without `native_decide`

### Additional

- **ULP/UFP** — unit in last/first place definitions and error bounds
- **Odd interval theorem** — `round_eq_on_odd_interval`, key lemma for division correctness

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager).

```
lake build
```

## Project Structure

```
Flean/
├── FloatFormat.lean         Floating-point format definitions (precision, exponent range)
├── Defs.lean                Core types: Fp, FiniteFp
├── ToVal.lean               Conversion to real/rational values
├── Order.lean               Ordering and comparison
├── CommonConstants.lean     Standard constants (largest finite, smallest subnormal)
├── Rounding/
│   ├── RoundDown.lean       Round toward -∞
│   ├── RoundUp.lean         Round toward +∞
│   ├── RoundTowardZero.lean
│   ├── RoundNearest.lean    Ties-to-even and ties-away-from-zero
│   ├── RelativeErrorBounds.lean
│   ├── Idempotence.lean
│   ├── OddInterval.lean     Odd interval analysis for division
│   ├── ModeClass.lean       RMode/RModeGrid/RModeSplit typeclasses
│   └── ...                  Neighbor/, GridInstance, PolicyInstances
├── Operations/
│   ├── Add.lean             fpAdd with correctness and commutativity
│   ├── Sub.lean             fpSub via fpAdd with negation
│   ├── Mul.lean             fpMul with correctness and commutativity
│   ├── Div.lean             fpDiv with odd interval correctness proof
│   ├── Sqrt.lean            fpSqrt with sticky-bit correctness
│   ├── FMA.lean             Fused multiply-add
│   ├── Fast2Sum.lean        Error-free transformation (ordered inputs)
│   ├── TwoSum.lean          Error-free transformation (arbitrary signs)
│   ├── TwoProduct.lean      Error-free transformation for multiplication
│   ├── VeltkampSplit.lean   Veltkamp splitting exactness
│   ├── Sterbenz.lean        Sterbenz lemma
│   ├── KahanSum.lean        Kahan compensated summation error analysis
│   ├── Exp*.lean            Verified exp computation (5 files)
│   ├── Log*.lean            Verified log computation (5 files)
│   ├── MinMax.lean          IEEE 754-2019 min/max
│   ├── LogBScaleB.lean      logB and scaleB operations
│   ├── RoundToIntegral.lean roundToIntegral operation
│   └── RoundIntSig.lean     Core rounding-via-integer-significand algorithm
├── StorageFormats/           GPU/ML float formats (E4M3, E5M2, etc.)
│   ├── Defs.lean            Format definitions and StorageFp type
│   ├── Conversion.lean      StorageFp ↔ FiniteFp conversion
│   ├── FromFp.lean          Fp → StorageFp conversion
│   ├── FromFpCorrect.lean   fromFp correctness (correctly-rounded value)
│   ├── Extensionality.lean  General round-trip theorem
│   └── RoundRNEVerify.lean  RNE policy verification
├── Encoding/                 Bit-level representations and conversions
├── Linearize/                Custom linearize tactic (~356 sites)
├── BoundCalc/                Custom bound_calc tactic (~144 sites)
├── ZpowNorm/                 Custom zpow_norm tactic (46 sites)
├── NumberTheory/             Padé approximants, irrationality bounds for exp
├── ENNRat/                   Extended nonnegative rationals
└── ERat/                     Extended rationals
```

## AI Assistance

Substantial portions of this library were developed with [Claude](https://claude.ai/) (Anthropic) via [Claude Code](https://docs.anthropic.com/en/docs/claude-code). This includes proof development, refactoring, and exploration of proof strategies.

The initial start of the library was myself writing proofs slowly and carefully, however Claude is substantially faster at sketching out the logic and automatically verifying. Though I read over what it has written, and verify for seeming correctness, there could of course be holes. However, I systematically avoid the usual downfalls (obscured `sorry`s, `native_decide`, overly Weird metaprogramming), and, practically floating point arithmetic is a lot more pinned down and thus there's a lot less room or incentive for there to be large holes.

## References

- Jean-Michel Muller, Nicolas Brisebarre, Florent de Dinechin, Claude-Pierre Jeannerod, Vincent Lefevre, Guillaume Melquiond, Nathalie Revol, Damien Stehle, Serge Torres. *Handbook of Floating-Point Arithmetic*. Birkhauser, 2nd edition, 2018.
- Nicholas J. Higham. *Accuracy and Stability of Numerical Algorithms*. SIAM, 2nd edition, 2002.
- IEEE 754-2019. *IEEE Standard for Floating-Point Arithmetic*.
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — the mathematical library for Lean 4.

## License

Dual-licensed under [MIT](LICENSE-MIT) and [Apache 2.0](LICENSE-APACHE).
