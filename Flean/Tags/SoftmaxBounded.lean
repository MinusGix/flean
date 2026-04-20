import Flean.Operations.Softmax
import Flean.Util

/-!
# Phase 0+ Application: Bounded Input Tag → Clean Softmax Bound

**Status**: Phase 0 → Phase 1 validation experiment. Tests whether the
tag-framework pattern survives contact with a real downstream consumer
(`fpSoftmaxOf_error_bound` in `Softmax.lean`).

## What this pilot tests

`Softmax.lean` already has TWO tracks:

1. **Clean track** (`fpSoftmaxOf_error_bound`, line 922): takes
   `h_exp_nr : ∀ i, isNormalRange (exp xs_i)` as a hypothesis, yields
   the purely-multiplicative bound
   `|(result i).toVal - softmax(x) i| ≤ softmaxErrorCoeff · softmax(x) i`
   with NO `subnormalConst` tail.

2. **Subnormal-tolerant track** (`fpSoftmaxOf_error_bound_subnormal_tight`,
   line 1512): drops the `h_exp_nr` precondition, pays with a
   `+ subnormalConst` additive tail.

The `IsNormal` tightening story from Phase 0 (`Flean/Tags/Normal.lean`)
would, in the strongest form, let track 2's conclusion reduce to track
1's — but that requires re-proving the core bound under IsNormal, which
is invasive Phase-2 work.

This pilot takes a different and equally useful approach: **show that
a natural INPUT tag (bounded-range on `xs`) automatically supplies the
`h_exp_nr` precondition that the clean track requires**.

The user workflow becomes: "my inputs are bounded" (stated as one tag)
→ `isNormalRange (exp xs_i)` follows automatically → clean softmax
bound applies. No manual `isNormalRange` plumbing per call site.

## Design

* Tag: `IsBoundedRange lo hi xs` on a vector, closed `[lo, hi]`.
* Bridge: the tag plus `lo ≥ min_exp · log 2` and `hi < (max_exp+1) · log 2`
  implies `isNormalRange (exp xs_i)` for all `i`. Uses `exp_int_mul_log2`
  (already in `Flean/Util.lean`) and `Real.exp_le_exp`/`exp_strictMono`.
* Downstream demo: a corollary that packages the bridge + existing
  `fpSoftmaxOf_error_bound` into one call, so the user supplies only
  the tag and the remaining softmax hypotheses.

## Validation findings

* The natural input tag (`IsBoundedRange`) exists *below* the softmax
  preconditions and cleanly generates them via a single bridge theorem.
  The pattern *does* survive contact with real code.
* The `h_quot_nr` precondition (quotient is in normal range) is NOT
  derivable from `IsBoundedRange` alone — it depends on `denom`, which
  is a computed quantity. This is an orthogonal tag-threading problem
  for Phase 1 to address.
* `FloatFormat.max_exp + 1` in `isNormalRange` shows up as a cast issue
  (ℤ → ℝ inside zpow / exp arguments). `exp_int_mul_log2` handled this
  cleanly — suggests the Flean codebase already has the cast plumbing
  tag framework design would need.
-/

set_option autoImplicit false

namespace Flean.Tags

open Softmax

variable [FloatFormat]

/-! ## The tag -/

/-- `IsBoundedRange lo hi xs` asserts each entry of `xs : Fin n → FiniteFp`
satisfies `lo ≤ (xs i).toVal ≤ hi`, measured in ℝ. Closed interval. -/
structure IsBoundedRange {n : ℕ} (lo hi : ℝ) (xs : Fin n → FiniteFp) : Prop where
  /-- Pointwise lower bound. -/
  lower : ∀ i, lo ≤ ((xs i).toVal : ℝ)
  /-- Pointwise upper bound. -/
  upper : ∀ i, ((xs i).toVal : ℝ) ≤ hi

/-! ## Bridge: bounded input → exp in normal range -/

/-- **Bridge theorem**: if `xs` lies in `[lo, hi]` with `lo` high enough
and `hi` low enough (in terms of `log 2 · min_exp` / `log 2 · (max_exp+1)`),
then `exp ((xs i).toVal)` is in the normal range for all `i`. This
discharges the `h_exp_nr` precondition of `fpSoftmaxOf_error_bound`
automatically from an input tag. -/
theorem IsBoundedRange.exp_isNormalRange
    {n : ℕ} {lo hi : ℝ} {xs : Fin n → FiniteFp}
    (h : IsBoundedRange lo hi xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ lo)
    (hhi : hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (i : Fin n) : isNormalRange (Real.exp ((xs i).toVal : ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- Lower: 2^min_exp ≤ exp(xs_i)
    have hy_ge : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ ((xs i).toVal : ℝ) :=
      le_trans hlo (h.lower i)
    have hexp_step : Real.exp ((FloatFormat.min_exp : ℝ) * Real.log 2) ≤
                     Real.exp ((xs i).toVal : ℝ) :=
      Real.exp_le_exp_of_le hy_ge
    rwa [exp_int_mul_log2] at hexp_step
  · -- Upper: exp(xs_i) < 2^(max_exp + 1)
    have hy_lt : ((xs i).toVal : ℝ) <
                 ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2 :=
      lt_of_le_of_lt (h.upper i) hhi
    have hexp_step : Real.exp ((xs i).toVal : ℝ) <
                     Real.exp (((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2) :=
      Real.exp_strictMono hy_lt
    rwa [exp_int_mul_log2] at hexp_step

/-! ## Downstream demo: bounded input → clean softmax bound

This section shows how `IsBoundedRange` feeds the existing
`fpSoftmaxOf_error_bound` (clean / no `subnormalConst` variant) without
the caller having to prove `h_exp_nr` by hand. -/

variable [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

/-- **Composition demo**: given a bounded-input tag and the remaining
softmax hypotheses (denominator closeness, non-zero significand,
quotient-in-normal-range), the clean softmax bound applies. The
bounded-input tag plus the bound conditions on `lo, hi` discharge
`h_exp_nr` automatically.

This is the end-to-end "tag threads through softmax proof via bridge"
demonstration that validates Phase 0. -/
theorem fpSoftmax_bound_of_bounded
    {n : ℕ} (hn : 0 < n) {lo hi : ℝ}
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (hxs : IsBoundedRange lo hi xs)
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
  -- Derive `h_exp_nr` from the tag + bridge, then delegate.
  have h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)) :=
    hxs.exp_isNormalRange hlo hhi
  exact fpSoftmaxOf_error_bound hn xs exps denom result εsum h_exp h_exp_nr
    h_denom_close h_εsum_nn h_δ_lt hd_m h_quot_nr h_result i

end Flean.Tags
