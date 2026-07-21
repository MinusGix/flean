# Floating-point modular-addition clock

The modular-addition thread now has two layers:

- `Flean/Operations/ModAddClock.lean` is the exact real-valued specification.
- `Flean/Operations/ModAddClockFp.lean` is the tensor and floating-point realization interface.
- `Flean/Operations/ModAddClockBinary32.lean` supplies canonical Binary32 RNE tables, including the
  full nonzero frequency bank for `p=113`.
- `Flean/Operations/ModAddClockBinary32EndToEnd.lean` constructs the sum feature from separate
  inputs, executes a sequential Binary32 FMA readout, and proves accuracy one for `p=113`.

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

## Binary32 tables

`Flean.ModAddClock.Binary32.round` is the actual finite result of rounding a real coordinate in
Binary32 with round-to-nearest, ties-to-even. The construction proves that every coordinate is
finite and that

```text
|round(x) - x| ≤ 2⁻²⁴|x| + 2⁻¹⁵⁰
               ≤ 2⁻²⁴ + 2⁻¹⁵⁰       when |x| ≤ 1.
```

`Binary32.tables B` applies this rounding operation to every coordinate of a frequency bank.
`Binary32.fullBank113` enumerates residues `1,...,112`, and `Binary32.fullTables113` is therefore a
`113 × 224` table: 112 cosine entries followed by 112 sine entries for each residue.

The table is a verified mathematical Binary32 table rather than a checked-in decimal approximation:
`Real.sin` and `Real.cos` are noncomputable, so the entries are exposed as canonical rounded
`FiniteFp` values with proofs, not evaluated host-language bit patterns. A future export/import path
can attach literal bit patterns to these values using interval certificates without changing the
clock interface.

For the full bank, the file also proves

```text
896 / 12769 ≤ margin
```

and reduces the table quantization contribution to

```text
224 · (tableError · (1 + tableError) + tableError).
```

## End-to-end separate-input theorem

`Binary32.composedFeature fullBank113 a b` constructs the Fourier feature of `a+b` from the stored
features of `a` and `b`. Each coordinate uses the cosine/sine addition identities, one rounded
product, and one rounded FMA. `Binary32.dotFold` then evaluates the 224-coordinate readout using a
right-associated sequence of fused multiply-adds.

The proof tracks table error, feature-composition error, and sequential-FMA error separately. Their
sum remains below half the certified full-bank margin, yielding

```text
Binary32.endToEndAccuracy113_eq_one :
  accuracy Binary32.endToEndLogit113 = 1
```

This theorem receives `a` and `b` separately; it does not assume an oracle-provided feature of
`a+b`.

## Next concrete experiment

The mathematical Binary32 execution path is now certified. Remaining experiments concern concrete
data export and alternate formats or accumulation strategies:

1. export literal Binary32 bit patterns and certify them against the canonical rounded values;
2. compare sequential FMA with pairwise or compensated accumulation;
3. repeat the construction with BF16 and identify which inputs, if any, lose their margin.
