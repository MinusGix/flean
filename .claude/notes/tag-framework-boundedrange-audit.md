# `IsBoundedRange` Use-Site Audit (E6)

**Question**: what fraction of `IsBoundedRange` consumers use the
signed `lo`/`hi` info versus just the magnitude `maxMag` projection?
If the answer is "mostly magnitude", `IsBoundedRange` would be
over-engineered for those sites and we should recommend `HasAbsBound`
as the default.

**Verdict** (2026-04-22): **mixed, framework is not over-engineered**.
Keep both tags.  Internal propagation is signed; consumer APIs are
split between signed (Softmax, normal-range bridges) and magnitude
(LayerNorm, bundle bridges).

---

## Methodology

Counted occurrences of `.lo` / `.hi` (signed access) vs `.maxMag` /
`.toVal_abs_le` / `.toHasAbsBound` (magnitude access) in each
`IsBoundedRange`-consuming file under `Flean/Tags/`.  Excluded
`BoundedRangePropagate.lean` and `FpInterval.lean` as internal
implementation.

## Counts

| File | Signed (`.lo`/`.hi`) | Magnitude (`.maxMag` / `.toVal_abs_le`) | Interpretation |
|---|---|---|---|
| `Bridges/ToIsNormalRange.lean` | 43 | 0 | **Heavily signed**. `exp_isNormalRange_of_bounded` needs `lo`/`hi` separately for log-bound analysis. |
| `SoftmaxBounded.lean` | 8 | 0 | **Signed-dominant**. Separation constant `exp(I.lo − I.hi)`, log-bound conditions on `I.lo`/`I.hi`. |
| `LayerNorm.lean` | 1 | 5 | **Magnitude-dominant**. Uses `maxMag` for the input-magnitude corollary. |

Scalar site (`AbsBound.lean` / `AbsBoundPropagate.lean`):
uses `IsBoundedRange → HasAbsBound` via `toHasAbsBound` (bridge use,
counts as magnitude-side).

Bundle bridges (`BundleAbsBound.lean`, T-M4):
three theorems call `IsBoundedRange → HasAbsBound` via
`toHasAbsBound` + `maxMag`.  Magnitude-only.

## Analysis

### Signed-side consumers

`SoftmaxBounded.lean` and `Bridges/ToIsNormalRange.lean` genuinely
need the signed interval.  Specifically:

- **`exp_isNormalRange_of_bounded`**: needs `I.lo` to lower-bound
  `exp(x)` (so it stays above `2^min_exp`) and `I.hi` to upper-bound
  `exp(x)` (so it stays below `2^(max_exp+1)`).  `maxMag` alone wouldn't
  work — both sides of the interval constrain the output range.
- **`fpSoftmax_bound_of_separated`**: separation constant
  `4·n·2^min_exp ≤ exp(I.lo − I.hi)` encodes the *spread* of the
  interval.  `maxMag` loses this information (two intervals with the
  same `maxMag` can have very different spreads).

### Magnitude-side consumers

`LayerNorm.lean` and the bundle bridges use only `maxMag`.  These
sites could reasonably take `HasAbsBound` directly and skip the
`IsBoundedRange` → `HasAbsBound` bridge.

However, the bridge is only one line (`IsBoundedRange.toHasAbsBound`),
and `IsBoundedRange` is a more convenient input-side tag for users
who naturally have interval information (e.g. "my input is bounded
logits in `[-10, 10]`").  Forcing callers to compute `maxMag` and
pass `HasAbsBound` is less ergonomic.

### Bundle bridges

The bundle bridges `FpSumBound.hasAbsBound_of_isBoundedRange` and
similar accept `IsBoundedRange` and immediately project via
`toHasAbsBound` + `maxMag`.  This is **idiomatic** — they can be
called from either `IsBoundedRange` sources or, via
`HasAbsBound.toIsBoundedRange` + singleton, from `HasAbsBound`
sources.

## Recommendation

**No refactor.**  Both tags serve distinct roles:

- **`IsBoundedRange`** — signed interval.  Use when the consumer
  needs `lo`/`hi` separately (spread, asymmetric bounds, normal-range
  conditions).  Natural input-side tag for logits and inputs with
  known sign info.
- **`HasAbsBound`** — scalar magnitude.  Use when the consumer only
  needs `|x| ≤ c`.  Simpler algebra for propagation (see T-M1).

**What to consider adding** (low priority, orthogonal to this audit):

1. An `IsAsymmetricBound c_lo c_hi x` tag for the case where the
   caller has `-c_lo ≤ x.toVal ≤ c_hi` but the two bounds differ.
   Currently subsumed by `IsBoundedRange`; might deserve a thinner
   tag when a concrete consumer asks.
2. A `HasSignKnown x (sign : Bool)` tag — sometimes consumers only
   need the sign, not magnitude.  Trivial to define; defer until
   demand appears.

## Related backlog items

- E4 (bundle `magBound`): orthogonal to this audit, but removes the
  last bit of bare `(1 + relErr) · n · c` duplication.
- T-M2 `IsProb`: a candidate asymmetric-range tag if it lands.
- E6 closes with "no action required".
