import Flean.Operations.Softmax
import Flean.Util

/-!
# Phase 0+ / Phase 1 Application: Bounded Input Tag → Clean Softmax Bound

**Status**: Phase 1 bridge-library entry point, demonstrating the
tag-to-hypothesis pattern against a real downstream consumer
(`fpSoftmaxOf_error_bound` in `Softmax.lean`).

## What this pilot tests

`Softmax.lean` already has TWO tracks:

1. **Clean track** (`fpSoftmaxOf_error_bound`): takes `h_exp_nr` and
   `h_quot_nr` as hypotheses, yields the purely-multiplicative bound.

2. **Subnormal-tolerant track** (`fpSoftmaxOf_error_bound_subnormal_tight`):
   drops the normal-range hypotheses, pays with a `+ subnormalConst` tail.

This file bridges clean-track preconditions to a natural input tag
(bounded-range on `xs`). User workflow: "my inputs are bounded" →
`h_exp_nr` auto-derived → (with Phase 2 work, also `h_quot_nr`) →
clean bound applies.

## Design (post Phase 1 design doc §§1.8, 3.4)

* Tag `IsBoundedRange (R := R) lo hi xs` — R-parametric per §1.8.
* Bridge `IsBoundedRange.exp_isNormalRange` — ℝ-specific (uses
  `Real.exp`); discharges `h_exp_nr`.
* Parametric propagation (`IsBoundedRange.fpAdd`, `.fpMul`) and the
  `quot_isNormalRange` bridge have their **intended signatures** recorded
  in the design doc (§3.3, §3.4) as code blocks awaiting a focused
  FP-error-analysis session. They are **not** stubbed here with `sorry`
  — the library maintains its sorry-free invariant.

## Design doc cross-references

* §1.8 — all tags R-parametric.
* §1.4 — parametric propagation signatures live in design doc only
  (not committed to library with `sorry`).
* §3.3 — bridges organized by target hypothesis; current file houses
  the `ToIsNormalRange` exp-bridge. Reorganization into
  `Flean/Tags/Bridges/` is a future Phase 1 implementation task.
* §3.4 — parametric `IsBoundedRange.fpAdd` signature in design doc
  only, will land here (or in a sibling file) when the focused
  session proves it.
-/

set_option autoImplicit false

namespace Flean.Tags

open Softmax

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag (R-parametric, per §1.8) -/

/-- `IsBoundedRange (R := R) lo hi xs` asserts each entry of
`xs : Fin n → FiniteFp` satisfies `lo ≤ (xs i).toVal ≤ hi`, measured
in `R`. Closed interval.

Per design doc §1.8, all tags parameterize over `R`; bridges into
ℝ-specific hypotheses (like `isNormalRange (Real.exp ·)`) specialize
the tag to `R := ℝ` at the call site. -/
structure IsBoundedRange {n : ℕ} (lo hi : R) (xs : Fin n → FiniteFp) : Prop where
  /-- Pointwise lower bound. -/
  lower : ∀ i, lo ≤ ((xs i).toVal : R)
  /-- Pointwise upper bound. -/
  upper : ∀ i, ((xs i).toVal : R) ≤ hi

/-! ## Bridge: bounded input → exp in normal range (ℝ-specific) -/

/-- **Bridge theorem**: if `xs` lies in `[lo, hi]` (measured in ℝ) with
`lo ≥ min_exp · log 2` and `hi < (max_exp+1) · log 2`, then
`Real.exp ((xs i).toVal)` is in the normal range for all `i`.

This discharges the `h_exp_nr` precondition of `fpSoftmaxOf_error_bound`
from an input tag automatically. -/
theorem IsBoundedRange.exp_isNormalRange
    {n : ℕ} {lo hi : ℝ} {xs : Fin n → FiniteFp}
    (h : IsBoundedRange (R := ℝ) lo hi xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ lo)
    (hhi : hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (i : Fin n) : isNormalRange (Real.exp ((xs i).toVal : ℝ)) := by
  refine ⟨?_, ?_⟩
  · have hy_ge : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ ((xs i).toVal : ℝ) :=
      le_trans hlo (h.lower i)
    have hexp_step : Real.exp ((FloatFormat.min_exp : ℝ) * Real.log 2) ≤
                     Real.exp ((xs i).toVal : ℝ) :=
      Real.exp_le_exp_of_le hy_ge
    rwa [exp_int_mul_log2] at hexp_step
  · have hy_lt : ((xs i).toVal : ℝ) <
                 ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2 :=
      lt_of_le_of_lt (h.upper i) hhi
    have hexp_step : Real.exp ((xs i).toVal : ℝ) <
                     Real.exp (((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2) :=
      Real.exp_strictMono hy_lt
    rwa [exp_int_mul_log2] at hexp_step

/-! ## Downstream wrapper

With `exp_isNormalRange` complete and `h_quot_nr` still manual (pending
a focused session — signature recorded in the design doc), the wrapper
consumes the bounded-input tag + log-bound conditions on `lo, hi` +
`h_quot_nr` as an explicit hypothesis. -/

variable [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

/-- **Composition**: bounded-input tag + log-bound conditions + remaining
softmax hypotheses → clean softmax bound. The tag discharges `h_exp_nr`
via the `exp_isNormalRange` bridge; `h_quot_nr` stays manual pending
the Phase 2 quot bridge. -/
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
