import Flean.Tags.Sterbenz
import Flean.Operations.LogSumExp
import Flean.Operations.CrossEntropy
import Flean.Operations.Softmax

/-! # Vector-level Sterbenz shift tag

Phase 2 tag-tightening extension: the `h_shift_exact` hypothesis in
`LogSumExp`, `CrossEntropy`, and `Softmax` requires that subtracting
the pivot (`fpMax xs hn`) from every input is exact, which the caller
must establish separately (typically by invoking the Sterbenz lemma on
each index).

This file packages that argument as a first-class tag:

* `SterbenzShiftResult xs c` bundles a witness `xs'` together with
  the per-index `fpSubFinite` and `.toVal` identities.
* `sterbenzShift_of` constructs one from
  `∀ i, Flean.Tags.IsSterbenz (xs i) c` via
  `fpSubFinite_exact_of_sterbenz`.
* `fpLogSumExp_sterbenzShift_error_bound` and
  `fpCrossEntropy_sterbenzShift_error_bound` are tag-specialized
  wrappers that consume the tag and dispatch to the existing
  end-to-end theorems.

The wrappers demonstrate a fourth kind of tag-specialization beyond
the Phase 0 trichotomy (structural isolation / additive-tail
elimination / exactness): **precondition discharge** — the tag
doesn't tighten the bound, but absorbs a structural hypothesis that
would otherwise fall to the caller.
-/

set_option autoImplicit false

namespace Flean.Tags

open Finset BigOperators

variable [FloatFormat] [RModeExec]

/-! ## Core extraction: `∀ i, IsSterbenz (xs i) c` → exact shift -/

/-- Per-index exact-shift witness.

Carries the shifted vector `xs'` together with the proofs that
`fpSubFinite (xs i) c = Fp.finite (xs' i)` (FP semantics) and
`(xs' j).toVal = (xs j).toVal - c.toVal` (real semantics). -/
structure SterbenzShiftResult {n : ℕ}
    (xs : Fin n → FiniteFp) (c : FiniteFp) where
  /-- The shifted vector. -/
  xs' : Fin n → FiniteFp
  /-- FP-level correctness: each `xs'` is `fpSubFinite (xs i) c`. -/
  h_sub : ∀ i, fpSubFinite (xs i) c = Fp.finite (xs' i)
  /-- Real-level exactness: the shift incurs no rounding error. -/
  h_exact : ∀ j, ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - (c.toVal : ℝ)

/-- **Constructor**: from a vector-level Sterbenz tag, extract the exact-shift
witness.  Each `xs' i` is the unique finite float whose `.toVal` equals
the difference `(xs i).toVal - c.toVal`, guaranteed by
`fpSubFinite_exact_of_sterbenz`.

`Classical.choose` is used per index; the result is `noncomputable`. -/
noncomputable def sterbenzShift_of
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeIdem ℝ]
    {n : ℕ} (xs : Fin n → FiniteFp) (c : FiniteFp)
    (h : ∀ i, Flean.Tags.IsSterbenz (R := ℝ) (xs i) c) :
    SterbenzShiftResult xs c :=
  let per_i : ∀ i, ∃ f : FiniteFp,
      fpSubFinite (xs i) c = Fp.finite f ∧
        ((f.toVal : ℝ) = (xs i).toVal - c.toVal) :=
    fun i => Flean.Tags.fpSubFinite_exact_of_sterbenz (R := ℝ) (h i)
  { xs' := fun i => Classical.choose (per_i i)
    h_sub := fun i => (Classical.choose_spec (per_i i)).1
    h_exact := fun j => (Classical.choose_spec (per_i j)).2 }

end Flean.Tags

/-! ## Tag-specialized LSE wrapper -/

namespace LogSumExp

open Finset BigOperators Softmax Flean.Tags

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeSticky ℝ] [RModeNearest ℝ] [RModeConj ℝ] [RModeIdem ℝ]
  [ExpApprox] [ExpApproxSound]

variable {n : ℕ}

/-- **Tag-specialized LSE end-to-end bound**.

When every input is in the Sterbenz regime w.r.t. the FP max, the
exact-shift hypothesis is discharged automatically by the tag.  The
caller supplies fewer arguments; the bound itself is the same as
`fpLogSumExp_end_to_end_error_bound`. -/
theorem fpLogSumExp_sterbenzShift_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (h_sterb : ∀ i, IsSterbenz (R := ℝ) (xs i) (fpMax xs hn))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i,
      fpExpFinite ((sterbenzShift_of xs (fpMax xs hn) h_sterb).xs' i) =
        Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (h_margin : LogSumExp.epsilonSum sum < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst)
    (result : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0) :
    |((result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * LogSumExp.dLog sum + logSubConst) +
      Softmax.subnormalConst := by
  set shift := sterbenzShift_of xs (fpMax xs hn) h_sterb
  exact fpLogSumExp_end_to_end_error_bound hn xs shift.xs' shift.h_exact
    exps h_exp sum h_margin logResult η_log h_η_log_nn
    logSubConst h_logSub_nn h_log_close result h_final_add h_final_ne

end LogSumExp

/-! ## Tag-specialized cross-entropy wrapper -/

namespace CrossEntropy

open Finset BigOperators LogSumExp Softmax Flean.Tags

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeSticky ℝ] [RModeNearest ℝ] [RModeConj ℝ] [RModeIdem ℝ]
  [ExpApprox] [ExpApproxSound]

variable {n : ℕ}

/-- **Tag-specialized cross-entropy end-to-end bound**.

Same structural move as `fpLogSumExp_sterbenzShift_error_bound`: the
vector Sterbenz tag discharges `h_shift_exact`.  Outer shift
(the per-index `r_i = round(xs_i - lse)` step inside CE) is *not*
covered by this tag — that's a separate subtraction against `lse`
which lives outside the logitspivot regime. -/
theorem fpCrossEntropy_sterbenzShift_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (ys : Fin n → FiniteFp)
    (h_sterb : ∀ i, IsSterbenz (R := ℝ) (xs i) (fpMax xs hn))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i,
      fpExpFinite ((sterbenzShift_of xs (fpMax xs hn) h_sterb).xs' i) =
        Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (h_margin : LogSumExp.epsilonSum sum < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst)
    (lse : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite lse)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0)
    (r : Fin n → FiniteFp)
    (h_shift_close : ∀ i,
      |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - (lse.toVal : ℝ))| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst)
    (dp : FpDotProduct.FpDotProductBound ys r ℝ) :
    |(((- dp.result).toVal : ℝ)) -
        crossEntropy (fun i => ((ys i).toVal : ℝ))
                     (fun i => ((xs i).toVal : ℝ))| ≤
      dp.relErr * ∑ i, |((ys i).toVal : ℝ) * ((r i).toVal : ℝ)| +
      ∑ i, |((ys i).toVal : ℝ)| *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst +
          deltaLSE xs hn sum η_log logSubConst) := by
  set shift := sterbenzShift_of xs (fpMax xs hn) h_sterb
  exact fpCrossEntropy_end_to_end_error_bound hn xs ys
    shift.xs' shift.h_exact exps h_exp sum h_margin
    logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close
    lse h_final_add h_final_ne
    r h_shift_close dp

end CrossEntropy

/-! ## Tag-specialized softmax wrapper -/

namespace Softmax

open Finset BigOperators Flean.Tags

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeSticky ℝ] [RModeNearest ℝ] [RModeConj ℝ] [RModeIdem ℝ]
  [ExpApprox] [ExpApproxSound]

variable {n : ℕ}

/-- **Tag-specialized softmax end-to-end bound**.

Parallel to `fpLogSumExp_sterbenzShift_error_bound` and
`fpCrossEntropy_sterbenzShift_error_bound`.  When every input is in
the Sterbenz regime w.r.t. `fpMax xs hn`, the exact-shift hypothesis
is discharged automatically by the tag.  Bound shape unchanged from
`fpSoftmax_end_to_end_error_bound`. -/
theorem fpSoftmax_sterbenzShift_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (h_sterb : ∀ i, IsSterbenz (R := ℝ) (xs i) (fpMax xs hn))
    (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i,
      fpExpFinite ((sterbenzShift_of xs (fpMax xs hn) h_sterb).xs' i) =
        Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_margin_ind : (1 + εsum) * (n : ℝ) * subnormalConst <
                     1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ))) +
        (1 + εsum) * (n : ℝ) * subnormalConst) /
       ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
        (1 + εsum) * (n : ℝ) * subnormalConst)) *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      (1 + (1 + (η : ℝ)) /
        ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
         (1 + εsum) * (n : ℝ) * subnormalConst)) * subnormalConst := by
  set shift := sterbenzShift_of xs (fpMax xs hn) h_sterb
  exact fpSoftmax_end_to_end_error_bound hn xs shift.xs' shift.h_exact
    exps denom result εsum h_exp h_denom_close h_εsum_nn
    h_margin_ind hd_m h_result i

end Softmax
