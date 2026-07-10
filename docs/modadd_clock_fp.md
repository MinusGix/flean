# Floating-point modular-addition clock

The modular-addition thread now has two layers:

- `Flean/Operations/ModAddClock.lean` is the exact real-valued specification.
- `Flean/Operations/ModAddClockFp.lean` is the tensor and floating-point realization interface.

## Exact specification and robustness

For a prime modulus `p` and a duplicate-free nonzero frequency bank `K`, the correct class has score
`|K|`. Every wrong class has score at most `|K| cos(2π/p)`. Consequently,

```text
|K| (1 - cos(2π/p)) ≤ margin(K)
                    and
          8 |K|/p² ≤ margin(K).
```

The second bound is deliberately algebraic. A concrete floating-point error certificate can compare
against it without requiring a verified numerical evaluation of `cos`.

The exact clock is translation-invariant: its logits depend on `s-c`, not `s` and `c` separately.
Its ideal margin is therefore independent of the input sum. Partial accuracy enters through learned
or rounded weights and input-dependent floating-point errors, not through sparsity alone. The
pointwise perturbation API reflects this by allowing error radii to vary with input and class.

## Tensor representation

`FrequencyBank p n` stores an injective map `Fin n → ZMod p` with no zero frequency. Its feature
vector has dimension `2n`:

```text
feature(x) = [cos(k₀x), ..., cos(kₙ₋₁x), sin(k₀x), ..., sin(kₙ₋₁x)].
```

The readout row for class `c` is `feature(c)`. The theorem `feature_dot_eq_clockLogit` proves

```text
dot(feature(s), feature(c)) = clockLogit(K, s, c).
```

The proof accounts for canonical `ZMod` representatives: the real phases for `s-c` and for the
difference of the two lifted phases can differ by an integer multiple of `2π`.

## Floating-point realization

`FpClockTables` contains actual `FiniteFp` data:

- `input s`: the stored or computed Fourier feature for sum `s`;
- `readout c`: the stored readout row for class `c`;
- coordinate-wise approximation bounds for both tables.

`FpClockExecution` contains an `FpMatVecBound` for each sum. It does not force an accumulation
algorithm: sequential FMA, pairwise, or compensated dot products can all populate the same
interface.

For every sum `s` and class `c`, `logit_error_le` proves

```text
|computedLogit(s,c) - clockLogit(K,s,c)|
  ≤ arithmeticError(s,c) + quantizationError(s,c).
```

The arithmetic term comes directly from `FpMatVecBound`. The quantization term is

```text
2n · (readoutErr(c) · (1 + inputErr(s)) + inputErr(s)).
```

This accounts for the product of two perturbed Fourier coordinates, whose exact magnitudes are at
most one.

Two failure certificates are available:

- `CertifiedBadInputs` uses the exact ideal margin.
- `AlgebraicBadInputs` replaces it with the lower bound `8n/p²`.

In both cases the actual decoder failure set is proved to be a subset of the certified set.

## Next concrete experiment

The next step is data rather than another abstraction:

1. choose a concrete prime modulus and frequency list;
2. round its cosine/sine table into Binary32;
3. construct row-wise FMA or pairwise `FpDotProductBound`s and assemble an `FpMatVecBound`;
4. evaluate the algebraic bad-input predicate;
5. repeat with BF16 and compare which inputs lose their margin.

After that, replace the assumed recovered sum feature with the actual rounded computation from the
separate embeddings of `a` and `b`. That will add the upstream trig-combination error to
`inputErr`; the readout and failure-set proofs remain unchanged.
