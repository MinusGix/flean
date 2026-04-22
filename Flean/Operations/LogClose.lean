import Flean.Operations.Log
import Flean.Operations.Softmax
import Flean.Operations.LogSumExp
import Flean.Operations.CrossEntropy

/-! # Bridge: `fpLogFinite` correctness → `h_log_close` shape

`LogSumExp` and `CrossEntropy` take an abstract `h_log_close` witness
for the log step (a consequence of the absence of a concrete
`fpLogFinite` when those files were written).  Now that `Log.lean` and
`LogAdapter.lean` provide a concrete `fpLogFinite`, this file supplies a
bridge:

  `fpLogFinite a = Fp.finite logResult` (under `0 < a.toVal`)
  →  `|logResult.toVal - Real.log a.toVal| ≤ η · |Real.log a.toVal| + subnormalConst`

which is exactly the shape LSE's `h_log_close` wants (with `η_log = η`,
`logSubConst = Softmax.subnormalConst`).

A concrete LSE demo (`fpLogSumExp_concrete_error_bound`) then plugs this
into `fpLogSumExp_end_to_end_error_bound`, eliminating the last abstract
hypothesis in the LSE pipeline.
-/

namespace Log

open Finset BigOperators

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeSticky ℝ] [RModeZero ℝ] [RModeNearest ℝ] [RModeConj ℝ]
  [LogApprox] [LogApproxSound]

/-- **Bridge lemma**: `fpLogFinite`'s correctness and sign-symmetric rounding
combine to give the `h_log_close` shape used by `LogSumExp` / `CrossEntropy`.

Valid on any strictly positive input.  Zero-log (`a.toVal = 1`) is handled
by the `v = 0` case, where both sides of the bound collapse to `0 ≤ subnormalConst`. -/
theorem fpLogFinite_close
    (a : FiniteFp) (h_pos : 0 < (a.toVal : ℝ))
    (logResult : FiniteFp)
    (h_eq : fpLogFinite a = Fp.finite logResult) :
    |((logResult.toVal : ℝ)) - Real.log (a.toVal : ℝ)| ≤
      (η : ℝ) * |Real.log (a.toVal : ℝ)| + Softmax.subnormalConst := by
  have h_correct : fpLogFinite a = ○(Real.log (a.toVal : ℝ)) :=
    fpLogFinite_correct a h_pos
  have h_round_eq : ○(Real.log (a.toVal : ℝ)) = Fp.finite logResult := by
    rw [← h_correct]; exact h_eq
  set v : ℝ := Real.log (a.toVal : ℝ) with hv_def
  by_cases hv : v = 0
  · -- v = 0: logResult must be 0.
    rw [hv] at h_round_eq
    rw [RModeZero.round_zero (R := ℝ)] at h_round_eq
    have h_log_eq : (0 : FiniteFp) = logResult := by
      injection h_round_eq
    rw [hv, ← h_log_eq]
    simp only [FiniteFp.toVal_zero, sub_zero, abs_zero, mul_zero, zero_add]
    exact Softmax.subnormalConst_nn
  · rcases lt_or_gt_of_ne hv with hv_neg | hv_pos
    · -- v < 0: conjugate to positive via RModeConj.
      have hneg_pos : 0 < -v := by linarith
      have h_round_neg : ○(-v) = Fp.finite (-logResult) := by
        rw [RModeConj.round_neg v hv, h_round_eq, Fp.neg_finite]
      have h_round_err_neg : |(-v) - ((-logResult).toVal : ℝ)| ≤ Fp.ulp (-v) / 2 :=
        RModeNearest_abs_error_le_ulp_half_pos (-v) hneg_pos (-logResult) h_round_neg
      have hulp_neg := Softmax.ulp_half_le_unified (-v) hneg_pos
      rw [FiniteFp.toVal_neg_eq_neg] at h_round_err_neg
      have h_eq_abs :
          |(-v) - (-(logResult.toVal : ℝ))| = |((logResult.toVal : ℝ)) - v| := by
        rw [show (-v) - (-(logResult.toVal : ℝ)) =
              ((logResult.toVal : ℝ)) - v from by ring]
      rw [h_eq_abs] at h_round_err_neg
      have habs_v : |v| = -v := abs_of_neg hv_neg
      rw [habs_v]; linarith
    · -- v > 0: direct.
      have h_round_err : |v - (logResult.toVal : ℝ)| ≤ Fp.ulp v / 2 :=
        RModeNearest_abs_error_le_ulp_half_pos v hv_pos logResult h_round_eq
      have hulp := Softmax.ulp_half_le_unified v hv_pos
      have habs_v : |v| = v := abs_of_pos hv_pos
      have h_sym : |v - (logResult.toVal : ℝ)| = |((logResult.toVal : ℝ)) - v| :=
        abs_sub_comm _ _
      rw [h_sym] at h_round_err
      rw [habs_v]; linarith

end Log

/-! ## LSE with concrete log witness

Supplies the abstract `h_log_close` hypothesis in
`fpLogSumExp_end_to_end_error_bound` by appealing to `fpLogFinite_close`.
The resulting theorem has no abstract log-rounding parameters: the log
step is the concrete `fpLogFinite(sum.result)`. -/

namespace LogSumExp

open Finset BigOperators Softmax

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeSticky ℝ] [RModeZero ℝ] [RModeNearest ℝ] [RModeConj ℝ]
  [ExpApprox] [ExpApproxSound] [LogApprox] [LogApproxSound]

variable {n : ℕ}

/-- **End-to-end LSE with concrete log**.

Same shape as `fpLogSumExp_end_to_end_error_bound` but with the log step
supplied by `fpLogFinite`: the caller only needs `0 < sum.result.toVal`
(positivity is automatic from `S' ≥ 1`) and a finite witness
`fpLogFinite sum.result = Fp.finite logResult`.  The resulting bound
uses `η_log = η` and `logSubConst = Softmax.subnormalConst`. -/
theorem fpLogSumExp_concrete_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp) (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (h_sum_pos : (0 : ℝ) < (sum.result.toVal : ℝ))
    (h_margin :
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp)
    (h_logFinite : fpLogFinite sum.result = Fp.finite logResult)
    (result : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0) :
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    |((result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        ((η : ℝ) *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + (η : ℝ)) * D_log + Softmax.subnormalConst) +
      Softmax.subnormalConst := by
  have h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        (η : ℝ) * |Real.log ((sum.result.toVal : ℝ))| + Softmax.subnormalConst :=
    Log.fpLogFinite_close sum.result h_sum_pos logResult h_logFinite
  exact fpLogSumExp_end_to_end_error_bound hn xs xs' h_shift_exact exps h_exp
    sum h_margin logResult (η : ℝ) (by positivity) Softmax.subnormalConst
    Softmax.subnormalConst_nn h_log_close result h_final_add h_final_ne

end LogSumExp

/-! ## Cross-entropy with concrete log witness

Same idea as `fpLogSumExp_concrete_error_bound`: drop the abstract log
hypothesis from `fpCrossEntropy_end_to_end_error_bound` by appealing
to `fpLogFinite_close`. -/

namespace CrossEntropy

open Finset BigOperators LogSumExp Softmax

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeSticky ℝ] [RModeZero ℝ] [RModeNearest ℝ] [RModeConj ℝ]
  [ExpApprox] [ExpApproxSound] [LogApprox] [LogApproxSound]

variable {n : ℕ}

/-- **End-to-end cross-entropy with concrete log**.

Composes `fpCrossEntropy_end_to_end_error_bound` with `fpLogFinite_close`,
specializing `η_log = η` and `logSubConst = Softmax.subnormalConst`.
The caller supplies `0 < sum.result.toVal` and a finite-witness
`fpLogFinite sum.result = Fp.finite lse`; the abstract log hypothesis
vanishes. -/
theorem fpCrossEntropy_concrete_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (ys : Fin n → FiniteFp)
    (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (h_sum_pos : (0 : ℝ) < (sum.result.toVal : ℝ))
    (h_margin :
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp)
    (h_logFinite : fpLogFinite sum.result = Fp.finite logResult)
    (lse : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite lse)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0)
    (r : Fin n → FiniteFp)
    (h_shift_close : ∀ i,
      |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - (lse.toVal : ℝ))| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst)
    (dp : FpDotProduct.FpDotProductBound ys r ℝ) :
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    letI Δ_LSE : ℝ :=
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        ((η : ℝ) *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + (η : ℝ)) * D_log + Softmax.subnormalConst) +
      Softmax.subnormalConst
    |(((- dp.result).toVal : ℝ)) -
        crossEntropy (fun i => ((ys i).toVal : ℝ))
                     (fun i => ((xs i).toVal : ℝ))| ≤
      dp.relErr * ∑ i, |((ys i).toVal : ℝ) * ((r i).toVal : ℝ)| +
      ∑ i, |((ys i).toVal : ℝ)| *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst + Δ_LSE) := by
  have h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        (η : ℝ) * |Real.log ((sum.result.toVal : ℝ))| + Softmax.subnormalConst :=
    Log.fpLogFinite_close sum.result h_sum_pos logResult h_logFinite
  exact fpCrossEntropy_end_to_end_error_bound hn xs ys
    xs' h_shift_exact exps h_exp sum h_margin
    logResult (η : ℝ) (by positivity) Softmax.subnormalConst
    Softmax.subnormalConst_nn h_log_close
    lse h_final_add h_final_ne
    r h_shift_close dp

end CrossEntropy
