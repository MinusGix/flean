# Flean

Formal verification of IEEE 754 floating-point arithmetic in [Lean 4](https://lean-lang.org/).

## Overview

Flean is a Lean 4 library that formalizes floating-point number formats, all five IEEE 754 rounding modes, arithmetic operations, and their error bounds. The mathematical treatment follows the *Handbook of Floating-Point Arithmetic* by Jean-Michel Muller et al.

The library is generic over the number type (`R`), aiming to effectively work with any linearly ordered field (reals, rationals, etc.) rather than fixing a specific representation. The library aims to be computable, so that it can in principle be used as a (likely slow) software floating point implementation.

Separately, the library aims to formalize GPU floating point formats as well, to better talk about their error bounds and behavior. Though, we avoid formalizing base-10 (or arbitrary base) floating point due to relative obscurity.

## What's Proved

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

Each correctness theorem states: the operation's result equals the rounding mode applied to the exact mathematical result.

### Division — odd interval theorem

`round_eq_on_odd_interval` proves that any rounding mode is constant on intervals `((n-1)*E, (n+1)*E)` where `n` is odd and large enough. This is the key lemma for division correctness, establishing that rounding commutes with the division algorithm's approximation.

### Additional

- **Encoding/decoding** — bit-level floating-point representations and conversions
- **ULP** — unit in last place definitions and error bounds

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager).

```
lake build
```

## Project Structure

```
Flean/
├── FloatFormat.lean       Floating-point format definitions (precision, exponent range)
├── Defs.lean              Core types: Fp, FiniteFp
├── ToVal.lean             Conversion to real/rational values
├── Order.lean             Ordering and comparison
├── CommonConstants.lean   Standard constants (largest finite, smallest subnormal)
├── Rounding/
│   ├── RoundDown.lean     Round toward -∞
│   ├── RoundUp.lean       Round toward +∞
│   ├── RoundTowardZero.lean
│   ├── RoundNearest.lean  Ties-to-even and ties-away-from-zero
│   ├── RelativeErrorBounds.lean
│   ├── Idempotence.lean
│   └── OddInterval.lean   Odd interval analysis for division
├── Operations/
│   ├── Add.lean           fpAdd with correctness and commutativity
│   ├── Sub.lean           fpSub via fpAdd with negation
│   ├── Mul.lean           fpMul with correctness and commutativity
│   ├── Div.lean           fpDiv with odd interval correctness proof
│   └── RoundIntSig.lean   Core rounding-via-integer-significand algorithm
├── Encoding/              Bit-level representations and conversions
├── Linearize/             Custom tactic for FP inequality automation
├── ENNRat/                Extended nonnegative rationals
└── ERat/                  Extended rationals
```

## AI Assistance

Substantial portions of this library were developed with [Claude](https://claude.ai/) (Anthropic) via [Claude Code](https://docs.anthropic.com/en/docs/claude-code). This includes proof development, refactoring, and exploration of proof strategies.

The initial start of the library was myself writing proofs slowly and carefully, however Claude is substantially faster at sketching out the logic and automatically verifying. Though I read over what it has written, and verify for seeming correctness, there could of course be holes. However, I systematically avoid the usual downfalls (obscured `sorry`s, `native_decide`, overly Weird metaprogramming), and, practically floating point arithmetic is a lot more pinned down and thus there's a lot less room or incentive for there to be large holes.

## References

- Jean-Michel Muller, Nicolas Brisebarre, Florent de Dinechin, Claude-Pierre Jeannerod, Vincent Lefevre, Guillaume Melquiond, Nathalie Revol, Damien Stehle, Serge Torres. *Handbook of Floating-Point Arithmetic*. Birkhauser, 2nd edition, 2018.
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — the mathematical library for Lean 4.

## License

Dual-licensed under [MIT](LICENSE-MIT) and [Apache 2.0](LICENSE-APACHE).
