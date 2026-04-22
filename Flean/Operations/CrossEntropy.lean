import Flean.Operations.LogSumExp
import Flean.Operations.FpDotProduct

/-!
# Cross-Entropy Loss: Verified End-to-End Error Bound

The classification cross-entropy loss:

  `CE(y, x) = -Σ_i y_i · (x_i - logsumexp(x)) = -Σ_i y_i · log_softmax(x)_i`

is the standard ML classifier objective. `x : Fin n → ℝ` are *logits*, `y` is
the target distribution (usually a probability vector or a one-hot encoding).

The FP implementation composes:

1. `lse : FiniteFp` from the `LogSumExp` end-to-end pipeline.
2. `r_i := round(x_i - lse)`, the log-probability vector.
3. `s  := fpDotProduct(y, r)`.
4. `loss := -s`.

This file provides the composed forward error bound on
`|loss.toVal - CE(y, x)|`, taking:

* the full LSE pipeline (matching `fpLogSumExp_end_to_end_error_bound`);
* the per-index shift-rounding bound as an abstract hypothesis
  (mirroring the abstract `h_log_close` in LSE);
* an `FpDotProductBound` witness for the `Σ y_i · r_i` step.

## Main results

* `crossEntropy`, `crossEntropy_shift_eq`, `crossEntropy_nonneg` — real-valued setup
* `fpCrossEntropy_end_to_end_error_bound` — the main composition theorem
* `FpCrossEntropyResult` + `.error_bound` — bundled form
* `fpCrossEntropy_naiveSum_error_bound` — demo using `FpSumBound.ofNaive` and
  `FpDotProductBound.ofDotProductFMA`

## Design notes

The shift step is kept abstract via `h_shift_close` rather than requiring
`fpSubFinite (xs i) lse = Fp.finite (r i)` with a nonzero side condition per
index.  This matches the abstract `h_log_close` in LSE, avoids a pile of
nonzero side conditions, and naturally handles the zero case
(`r_i = 0` when `xs i = lse`).  The rounding bound
`η · |xs_i - lse| + Softmax.subnormalConst` that the caller would derive
from `fpSubFinite_correct` + `Softmax.ulp_half_le_unified` is simply passed
in directly.
-/

set_option autoImplicit false

namespace CrossEntropy

open Finset BigOperators LogSumExp Softmax

variable {n : ℕ}

/-! ## Real-Valued Setup -/

/-- Cross-entropy of a target distribution `y` against logits `x`:
`CE(y, x) = -Σ_i y_i · (x_i - logsumexp x)`. No sign or simplex constraint on
`y` is imposed; under nonneg `y` with `Σ y = 1` this is the standard loss. -/
noncomputable def crossEntropy (y x : Fin n → ℝ) : ℝ :=
  -∑ i, y i * (x i - logsumexp x)

/-- Cross-entropy is shift-invariant: adding a constant to every logit leaves
the loss unchanged.  Mirrors softmax's shift-invariance and is the reason the
subtract-max trick is safe in the LSE pipeline. -/
theorem crossEntropy_shift_eq (y x : Fin n → ℝ) (c : ℝ) (hn : 0 < n) :
    crossEntropy y (Softmax.shift x c) = crossEntropy y x := by
  unfold crossEntropy
  have h_lse := logsumexp_shift_eq x c hn
  have h_per : ∀ i,
      (Softmax.shift x c) i - logsumexp (Softmax.shift x c) =
        x i - logsumexp x := by
    intro i
    simp only [Softmax.shift, h_lse]
    ring
  simp only [h_per]

/-- Under nonneg `y`, every term `y_i · (x_i - LSE)` is nonpositive (since
`x_i ≤ LSE`), so `CE ≥ 0`. -/
theorem crossEntropy_nonneg (y x : Fin n → ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    0 ≤ crossEntropy y x := by
  unfold crossEntropy
  rw [neg_nonneg]
  refine Finset.sum_nonpos (fun i _ => ?_)
  have h_le : x i ≤ logsumexp x := logsumexp_ge x i
  have h_diff : x i - logsumexp x ≤ 0 := by linarith
  exact mul_nonpos_iff.mpr (Or.inl ⟨hy i, h_diff⟩)

/-! ## End-to-End FP Cross-Entropy Error Bound

The pipeline is `xs → lse → r → s → loss`, composed from the LSE pipeline
(steps 1–4) plus a per-index shift, one dot product, and a final sign flip.

The bound composes additively:

* `dp.relErr · Σ|y_i · r_i.toVal|` from the dot-product step.
* `Σ|y_i| · (η · |xs_i - lse.toVal| + Softmax.subnormalConst)` from the
  per-index shift rounding.
* `(Σ|y_i|) · Δ_LSE` from propagating the LSE error uniformly through the
  shift (since `r_exact_i - (xs_i - lse.toVal) = lse.toVal - LSE`, a
  constant across `i`).

Folded into a single weighted sum:
```
|loss.toVal - CE(y, x)| ≤
    dp.relErr · Σ|y_i · r_i.toVal|
  + Σ|y_i| · (η · |xs_i - lse.toVal| + Softmax.subnormalConst + Δ_LSE)
```
-/

section EndToEnd

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

/-- **End-to-end cross-entropy error bound**.

Given the full LSE pipeline (producing `lse : FiniteFp`), an abstract
shift-rounding witness `h_shift_close` (`|r_i - (xs_i - lse)| ≤ η·|xs_i - lse|
+ subnormalConst`, as the caller would derive from `fpSubFinite_correct` + the
`RModeNearest` half-ulp bound), and an `FpDotProductBound ys r` witness for
the inner product, this produces a forward bound on
`|loss.toVal - crossEntropy y x|` where `loss := -dp.result`.

`Δ_LSE` denotes the LSE end-to-end bound in its standard
`η·|LSE| + (1+η)·(η_log·(LSE-c) + (1+η_log)·D_log + logSubConst) + subnormalConst`
form; it propagates uniformly through the shift. -/
theorem fpCrossEntropy_end_to_end_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (ys : Fin n → FiniteFp)
    -- LSE pipeline ----------------------------------------------------
    (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (h_margin :
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst)
    (lse : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite lse)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0)
    -- Shift step ------------------------------------------------------
    (r : Fin n → FiniteFp)
    (h_shift_close : ∀ i,
      |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - (lse.toVal : ℝ))| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst)
    -- Dot product -----------------------------------------------------
    (dp : FpDotProduct.FpDotProductBound ys r ℝ) :
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    letI Δ_LSE : ℝ :=
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst
    |(((- dp.result).toVal : ℝ)) -
        crossEntropy (fun i => ((ys i).toVal : ℝ))
                     (fun i => ((xs i).toVal : ℝ))| ≤
      dp.relErr * ∑ i, |((ys i).toVal : ℝ) * ((r i).toVal : ℝ)| +
      ∑ i, |((ys i).toVal : ℝ)| *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst + Δ_LSE) := by
  -- Abbreviations.
  set c : ℝ := ((fpMax xs hn).toVal : ℝ)
  set L : ℝ := (lse.toVal : ℝ) with hL_def
  set LSE : ℝ := logsumexp (fun j => ((xs j).toVal : ℝ)) with hLSE_def
  set ε_sum : ℝ :=
    ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
      (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst with hε_def
  set D_log : ℝ := ε_sum / (1 - ε_sum) with hDlog_def
  set Δ_LSE : ℝ :=
    (η : ℝ) * |LSE| +
    (1 + (η : ℝ)) *
      (η_log * (LSE - c) + (1 + η_log) * D_log + logSubConst) +
    Softmax.subnormalConst with hΔ_def
  -- Step 1: the LSE end-to-end error bound.
  have h_lse_close : |L - LSE| ≤ Δ_LSE := by
    simpa [hL_def, hLSE_def, hΔ_def, hε_def, hDlog_def] using
      fpLogSumExp_end_to_end_error_bound hn xs xs' h_shift_exact exps h_exp
        sum h_margin logResult η_log h_η_log_nn logSubConst h_logSub_nn
        h_log_close lse h_final_add h_final_ne
  have hΔ_nn : 0 ≤ Δ_LSE := le_trans (abs_nonneg _) h_lse_close
  have hη_nn : (0 : ℝ) ≤ (η : ℝ) := by positivity
  have hsc_nn : (0 : ℝ) ≤ Softmax.subnormalConst := Softmax.subnormalConst_nn
  -- Step 2: bundle the per-index error on `r_i`:
  --   |r_i - (x_i - LSE)| ≤ η·|x_i - L| + subnormalConst + Δ_LSE
  have h_r_close : ∀ i,
      |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE)| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - L| + Softmax.subnormalConst + Δ_LSE := by
    intro i
    have h1 := h_shift_close i
    -- The gap between (x_i - L) and (x_i - LSE) is (LSE - L), bounded by Δ_LSE.
    have h_tri : |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE)| ≤
        |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - L)| +
        |(((xs i).toVal : ℝ) - L) - (((xs i).toVal : ℝ) - LSE)| := by
      have hreq :
          ((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE) =
            (((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - L)) +
            ((((xs i).toVal : ℝ) - L) - (((xs i).toVal : ℝ) - LSE)) := by ring
      rw [hreq]; exact abs_add_le _ _
    have h2 : |(((xs i).toVal : ℝ) - L) - (((xs i).toVal : ℝ) - LSE)| =
        |L - LSE| := by
      have : (((xs i).toVal : ℝ) - L) - (((xs i).toVal : ℝ) - LSE) =
          -(L - LSE) := by ring
      rw [this, abs_neg]
    calc |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE)|
        ≤ _ := h_tri
      _ = |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - L)| + |L - LSE| := by rw [h2]
      _ ≤ ((η : ℝ) * |((xs i).toVal : ℝ) - L| + Softmax.subnormalConst)
            + Δ_LSE := by linarith
      _ = (η : ℝ) * |((xs i).toVal : ℝ) - L| + Softmax.subnormalConst + Δ_LSE :=
          by ring
  -- Step 3: the dot product bound.
  have h_dp := dp.h_bound
  -- Step 4: bound |Σ y_i · r_i - Σ y_i · (x_i - LSE)| by Σ |y_i| · (per-index r close).
  have h_sum_close :
      |(∑ i, ((ys i).toVal : ℝ) * ((r i).toVal : ℝ)) -
        (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))| ≤
        ∑ i, |((ys i).toVal : ℝ)| *
          ((η : ℝ) * |((xs i).toVal : ℝ) - L| +
            Softmax.subnormalConst + Δ_LSE) := by
    have h_sub :
        (∑ i, ((ys i).toVal : ℝ) * ((r i).toVal : ℝ)) -
          (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE)) =
        ∑ i, ((ys i).toVal : ℝ) *
          (((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [h_sub]
    calc |∑ i, ((ys i).toVal : ℝ) *
              (((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE))|
        ≤ ∑ i, |((ys i).toVal : ℝ) *
              (((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |((ys i).toVal : ℝ)| *
              |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - LSE)| := by
          apply Finset.sum_congr rfl
          intro i _; rw [abs_mul]
      _ ≤ ∑ i, |((ys i).toVal : ℝ)| *
              ((η : ℝ) * |((xs i).toVal : ℝ) - L| +
                Softmax.subnormalConst + Δ_LSE) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact mul_le_mul_of_nonneg_left (h_r_close i) (abs_nonneg _)
  -- Step 5: triangle on |dp.result - Σ y·(x - LSE)|.
  have h_main :
      |((dp.result.toVal : ℝ)) -
          (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))| ≤
        dp.relErr * ∑ i, |((ys i).toVal : ℝ) * ((r i).toVal : ℝ)| +
        ∑ i, |((ys i).toVal : ℝ)| *
          ((η : ℝ) * |((xs i).toVal : ℝ) - L| +
            Softmax.subnormalConst + Δ_LSE) := by
    have h_tri :
        |((dp.result.toVal : ℝ)) -
            (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))| ≤
        |((dp.result.toVal : ℝ)) -
            (∑ i, ((ys i).toVal : ℝ) * ((r i).toVal : ℝ))| +
        |(∑ i, ((ys i).toVal : ℝ) * ((r i).toVal : ℝ)) -
            (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))| := by
      have hreq :
          ((dp.result.toVal : ℝ)) -
              (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE)) =
          (((dp.result.toVal : ℝ)) -
              (∑ i, ((ys i).toVal : ℝ) * ((r i).toVal : ℝ))) +
          ((∑ i, ((ys i).toVal : ℝ) * ((r i).toVal : ℝ)) -
              (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))) := by ring
      rw [hreq]; exact abs_add_le _ _
    linarith [h_dp, h_sum_close]
  -- Step 6: negate to get the `loss = -dp.result` statement; CE = -Σ y·(x - LSE).
  have h_loss_toVal : ((- dp.result).toVal : ℝ) = -(dp.result.toVal : ℝ) :=
    FiniteFp.toVal_neg_eq_neg (R := ℝ) dp.result
  have h_CE_eq :
      crossEntropy (fun i => ((ys i).toVal : ℝ))
                   (fun i => ((xs i).toVal : ℝ)) =
      -(∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE)) := by
    simp only [crossEntropy, hLSE_def]
  rw [h_loss_toVal, h_CE_eq]
  have h_eq_abs :
      |(-(dp.result.toVal : ℝ)) -
          (-(∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE)))| =
      |((dp.result.toVal : ℝ)) -
          (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))| := by
    rw [show (-(dp.result.toVal : ℝ)) -
            (-(∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))) =
          -(((dp.result.toVal : ℝ)) -
            (∑ i, ((ys i).toVal : ℝ) * (((xs i).toVal : ℝ) - LSE))) from by ring,
        abs_neg]
  rw [h_eq_abs]
  exact h_main

end EndToEnd

/-! ## Bundle

`FpCrossEntropyResult` collects the full pipeline (LSE + shift + dot product)
into a single structure, exposing `.error_bound`.  Parallels
`FpLogSumExpResult`. -/

section Bundle

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

/-- Complete cross-entropy pipeline witness, ready to produce an error bound. -/
structure FpCrossEntropyResult
    (xs : Fin n → FiniteFp) (ys : Fin n → FiniteFp) (hn : 0 < n) where
  /-- Shifted inputs `xs' i = xs i - fpMax xs hn`. -/
  xs' : Fin n → FiniteFp
  /-- The shift is exact (e.g. under Sterbenz). -/
  h_shift_exact : ∀ j,
    ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ)
  /-- FP exp results on shifted inputs. -/
  exps : Fin n → FiniteFp
  /-- Correctness of the FP exp step. -/
  h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i)
  /-- FP summation witness (any algorithm) for the LSE inner sum. -/
  sum : FpSum.FpSumBound exps ℝ
  /-- Combined sum-error margin; ensures log is well-defined. -/
  h_margin :
    ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
      (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1
  /-- Abstract FP log result. -/
  logResult : FiniteFp
  /-- Multiplicative log-rounding coefficient. -/
  η_log : ℝ
  /-- Nonnegativity of `η_log`. -/
  η_log_nn : 0 ≤ η_log
  /-- Additive (subnormal) tail of the log step. -/
  logSubConst : ℝ
  /-- Nonnegativity of `logSubConst`. -/
  logSubConst_nn : 0 ≤ logSubConst
  /-- Log-rounding proximity bound. -/
  h_log_close :
    |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
      η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst
  /-- Computed `lse : FiniteFp`. -/
  lse : FiniteFp
  /-- Final `fpAdd(max, logResult) = lse` witness. -/
  h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite lse
  /-- Final-add nonzero side condition (handled sign-symmetrically). -/
  h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0
  /-- Log-probability vector `r_i = round(xs_i - lse)`. -/
  r : Fin n → FiniteFp
  /-- Shift-step proximity bound. -/
  h_shift_close : ∀ i,
    |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - (lse.toVal : ℝ))| ≤
      (η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
        Softmax.subnormalConst
  /-- Dot-product witness for `Σ y_i · r_i`. -/
  dp : FpDotProduct.FpDotProductBound ys r ℝ

namespace FpCrossEntropyResult

/-- The computed FP loss `= -dp.result`. -/
def loss {xs : Fin n → FiniteFp} {ys : Fin n → FiniteFp} {hn : 0 < n}
    (ρ : FpCrossEntropyResult xs ys hn) : FiniteFp :=
  - ρ.dp.result

/-- The main error bound, stated as a bundle method. -/
theorem error_bound
    {xs : Fin n → FiniteFp} {ys : Fin n → FiniteFp} {hn : 0 < n}
    (ρ : FpCrossEntropyResult xs ys hn) :
    letI ε_sum : ℝ :=
      ((η : ℝ) + ρ.sum.relErr * (1 + (η : ℝ))) +
        (1 + ρ.sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    letI Δ_LSE : ℝ :=
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (ρ.η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + ρ.η_log) * D_log + ρ.logSubConst) +
      Softmax.subnormalConst
    |((ρ.loss.toVal : ℝ)) -
        crossEntropy (fun i => ((ys i).toVal : ℝ))
                     (fun i => ((xs i).toVal : ℝ))| ≤
      ρ.dp.relErr * ∑ i, |((ys i).toVal : ℝ) * ((ρ.r i).toVal : ℝ)| +
      ∑ i, |((ys i).toVal : ℝ)| *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (ρ.lse.toVal : ℝ)| +
          Softmax.subnormalConst + Δ_LSE) := by
  simpa [FpCrossEntropyResult.loss] using
    fpCrossEntropy_end_to_end_error_bound hn xs ys
      ρ.xs' ρ.h_shift_exact ρ.exps ρ.h_exp ρ.sum ρ.h_margin
      ρ.logResult ρ.η_log ρ.η_log_nn ρ.logSubConst ρ.logSubConst_nn
      ρ.h_log_close ρ.lse ρ.h_final_add ρ.h_final_ne
      ρ.r ρ.h_shift_close ρ.dp

end FpCrossEntropyResult

end Bundle

/-! ## Concrete Adapters (Demos)

Plug specific summation and dot-product adapters into the end-to-end
theorem.  Each demo specialises
`fpCrossEntropy_end_to_end_error_bound` to a concrete algorithm choice
for the LSE inner sum (NaiveSum / Kahan) and the outer dot product
(`ofDotProduct` / `ofDotProductFMA`). -/

section Demo

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

/-- **NaiveSum + FMA dot product demo**.

* Inner sum (LSE): `FpSum.FpSumBound.ofNaive` over `List.ofFn exps`.
* Outer dot: `FpDotProduct.FpDotProductBound.ofDotProductFMA`.

The outer FMA adapter does not require `RModeIdem`, so this works with the
ambient LSE typeclasses.  The resulting `dp.relErr = (1+η)^n - 1`. -/
theorem fpCrossEntropy_naiveSum_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (ys : Fin n → FiniteFp)
    -- LSE pipeline (NaiveSum)
    (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    {sumResult : FiniteFp}
    (trace : FpSum.NaiveSum (List.ofFn exps) sumResult)
    (hnr : trace.AllNormalRange (R := ℝ))
    (h_margin :
      letI sum := FpSum.FpSumBound.ofNaive exps trace hnr
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sumResult.toVal : ℝ))| ≤
        η_log * |Real.log ((sumResult.toVal : ℝ))| + logSubConst)
    (lse : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite lse)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0)
    -- Shift step (abstract per-index rounding)
    (r : Fin n → FiniteFp)
    (h_shift_close : ∀ i,
      |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - (lse.toVal : ℝ))| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst)
    -- Dot product (FMA)
    {dpInit dpResult : FiniteFp}
    (dpTrace : DotProductFMA.FMADPTrace
        (List.ofFn (fun i => (ys i, r i))) dpInit dpResult)
    (hdp_init : dpInit.toVal (R := ℝ) = 0)
    (hdp_nr : dpTrace.AllNormalRange (R := ℝ)) :
    letI sum := FpSum.FpSumBound.ofNaive exps trace hnr
    letI dp := FpDotProduct.FpDotProductBound.ofDotProductFMA
        (R := ℝ) ys r dpTrace hdp_init hdp_nr
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    letI Δ_LSE : ℝ :=
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst
    |(((- dp.result).toVal : ℝ)) -
        crossEntropy (fun i => ((ys i).toVal : ℝ))
                     (fun i => ((xs i).toVal : ℝ))| ≤
      dp.relErr * ∑ i, |((ys i).toVal : ℝ) * ((r i).toVal : ℝ)| +
      ∑ i, |((ys i).toVal : ℝ)| *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst + Δ_LSE) := by
  set sum := FpSum.FpSumBound.ofNaive exps trace hnr with hsum_def
  set dp := FpDotProduct.FpDotProductBound.ofDotProductFMA
      (R := ℝ) ys r dpTrace hdp_init hdp_nr with hdp_def
  have h_log_close' :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst := by
    simpa [hsum_def, FpSum.FpSumBound.ofNaive, FpSum.FpSumBound.ofPairwise]
      using h_log_close
  exact fpCrossEntropy_end_to_end_error_bound hn xs ys
    xs' h_shift_exact exps h_exp sum h_margin
    logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close'
    lse h_final_add h_final_ne
    r h_shift_close dp

end Demo

end CrossEntropy
