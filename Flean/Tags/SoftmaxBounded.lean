import Flean.Operations.Softmax
import Flean.Tags.BoundedRange
import Flean.Tags.Bridges.ToIsNormalRange

/-!
# Consumer Wrapper: Bounded-Input Softmax Bound

**Status**: Phase 1 bridge-consumer file. Post-reorganization per
design doc §3.3, the `IsBoundedRange` tag lives in
`Flean/Tags/BoundedRange.lean`, the bridges
`IsBoundedRange.exp_isNormalRange` and `quot_isNormalRange` live in
`Flean/Tags/Bridges/ToIsNormalRange.lean`, and this file contains
only the downstream wrapper theorems.

## What this file delivers

- `fpSoftmax_bound_of_bounded` — user supplies `IsBoundedRange I xs`
  + log-bound conditions on `I.lo`, `I.hi` + the remaining softmax
  hypotheses (denominator closeness, non-zero significand,
  quotient-in-normal-range, finiteness of division); the clean
  `fpSoftmaxOf_error_bound` (no `subnormalConst` tail) applies via
  the exp-bridge, without the user ever writing
  `isNormalRange (exp ·)` by hand.

- `fpSoftmax_bound_of_separated` — lighter companion that also
  discharges `h_quot_nr` via `IsBoundedRange.quot_isNormalRange`,
  trading it for a `h_separation : 4·n·2^min_exp ≤ exp(I.lo − I.hi)`
  hypothesis and an `εsum ≤ 1/4` bound on the denom-closeness error.
  Summation-based denoms (Kahan's `2η + nη²`, Neumaier, …) plug in
  directly as long as their `εsum` stays below `1/4`.
-/

set_option autoImplicit false

namespace Flean.Tags

open Softmax

variable [FloatFormat]
variable [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

/-- **Composition**: bounded-input tag + log-bound conditions on `lo, hi`
+ remaining softmax hypotheses → clean softmax bound. The tag
discharges `h_exp_nr` via the `exp_isNormalRange` bridge; `h_quot_nr`
stays manual pending the locked `quot_isNormalRange` bridge (design
doc §3.3). -/
theorem fpSoftmax_bound_of_bounded
    {n : ℕ} (hn : 0 < n) {I : FpInterval ℝ}
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (hxs : IsBoundedRange (R := ℝ) I xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ I.lo)
    (hhi : I.hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_δ_lt : (η : ℝ) + εsum * (1 + (η : ℝ)) < 1)
    (hd_m : denom.m ≠ 0)
    (h_quot_nr : ∀ i, isNormalRange (((exps i).toVal : ℝ) / denom.toVal))
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i := by
  have h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)) :=
    hxs.exp_isNormalRange hlo hhi
  exact fpSoftmaxOf_error_bound hn xs exps denom result εsum h_exp h_exp_nr
    h_denom_close h_εsum_nn h_δ_lt hd_m h_quot_nr h_result i

/-- **Lighter composition**: bounded-input tag + log-bound conditions
+ separation condition + remaining softmax hypotheses → clean softmax
bound.  Both `h_exp_nr` (via `exp_isNormalRange`) and `h_quot_nr`
(via `quot_isNormalRange`) are discharged automatically.

The `εsum ≤ 1/4` bound captures any practical summation-based denom
error: single fp-add (`εsum = η`), Kahan (`εsum = 2η + nη²`), Neumaier,
etc. — plugs in directly as long as it stays below `1/4`.

Input-side requirements beyond `_of_bounded`:
- separation witness `4·n·2^min_exp ≤ exp(I.lo − I.hi)` preventing
  softmax underflow,
- explicit `0 < denom.toVal` (to ratio meaningfully),
- explicit `εsum ≤ 1/4` on the denom-closeness error. -/
theorem fpSoftmax_bound_of_separated
    {n : ℕ} (hn : 0 < n) {I : FpInterval ℝ}
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (hxs : IsBoundedRange (R := ℝ) I xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ I.lo)
    (hhi : I.hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (h_separation : 4 * (n : ℝ) * (2 : ℝ) ^ (FloatFormat.min_exp : ℤ) ≤
                    Real.exp (I.lo - I.hi))
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum) (h_εsum_le : εsum ≤ 1/4)
    (hd_pos : 0 < (denom.toVal : ℝ))
    (h_δ_lt : (η : ℝ) + εsum * (1 + (η : ℝ)) < 1)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i := by
  have h_quot_nr : ∀ i, isNormalRange (((exps i).toVal : ℝ) / denom.toVal) :=
    fun i =>
      hxs.quot_isNormalRange hn hlo hhi h_exp h_εsum_nn h_εsum_le
        h_denom_close hd_pos h_separation i
  exact fpSoftmax_bound_of_bounded hn xs exps denom result εsum
    hxs hlo hhi h_exp h_denom_close h_εsum_nn h_δ_lt hd_m h_quot_nr h_result i

end Flean.Tags
