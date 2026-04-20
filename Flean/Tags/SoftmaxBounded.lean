import Flean.Operations.Softmax
import Flean.Tags.BoundedRange
import Flean.Tags.Bridges.ToIsNormalRange

/-!
# Consumer Wrapper: Bounded-Input Softmax Bound

**Status**: Phase 1 bridge-consumer file. Post-reorganization per
design doc §3.3, the `IsBoundedRange` tag lives in
`Flean/Tags/BoundedRange.lean`, the bridge
`IsBoundedRange.exp_isNormalRange` lives in
`Flean/Tags/Bridges/ToIsNormalRange.lean`, and this file contains
only the downstream wrapper theorem.

## What this file delivers

`fpSoftmax_bound_of_bounded` — user supplies `IsBoundedRange lo hi xs`
+ log-bound conditions on `lo, hi` + the remaining softmax hypotheses
(denominator closeness, non-zero significand, quotient-in-normal-range,
finiteness of division); the clean
`fpSoftmaxOf_error_bound` (no `subnormalConst` tail) applies via the
exp-bridge, without the user ever writing `isNormalRange (exp ·)` by
hand.

## Deferred

The `h_quot_nr` precondition remains a manual hypothesis. Its bridge
(`IsBoundedRange.quot_isNormalRange`) has a locked signature in the
design doc §3.3; once a focused FP-error-analysis session proves it,
this wrapper gets a lighter companion that consumes only the bounded-
input tag plus the separation condition.
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
    {n : ℕ} (hn : 0 < n) {lo hi : ℝ}
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (hxs : IsBoundedRange (R := ℝ) lo hi xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ lo)
    (hhi : hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
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

end Flean.Tags
