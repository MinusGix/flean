import Flean.ToVal
import Flean.Operations.CrossEntropy

/-!
# Tag: `IsOneHot`

R-parametric tag asserting a vector `y : Fin n → FiniteFp` is a
one-hot encoding: exactly one index carries `1`, every other index
carries `0`.  The classical setup for ML classification targets.

## The tag

`IsOneHot j y` takes an explicit hot index `j : Fin n` as a parameter
(mirroring `IsBoundedRange`'s `FpInterval` parameter — tags that
carry data the user needs to name in statements take that data as a
parameter rather than existentially quantifying it).

## What it resolves

Under `IsOneHot j y`, real-valued sums collapse to a single-index
evaluation:

* `Σ y_i · f i = f j`
* `Σ |y_i · f i| = |f j|`
* `Σ |y_i| = 1`

Applied to the cross-entropy bound, the general
`dp.relErr · Σ|y_i · r_i| + Σ|y_i| · (η·|x_i - lse| + tail)`
collapses to
`dp.relErr · |r_j| + (η·|x_j - lse| + tail)`
— the standard ML classifier loss form.

## Specialization shape

This is a **structural isolation** pattern (Phase 0 finding 1): the
tag doesn't tighten magnitude per se, but collapses the RHS sum into a
single term.  For one-hot targets — the common ML case — this is an
order-of-magnitude tighter bound.
-/

set_option autoImplicit false

namespace Flean.Tags

open Finset BigOperators

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## The tag -/

/-- `IsOneHot (R := R) j y` asserts `y` is one-hot at index `j`:
`(y j).toVal = 1` and `(y i).toVal = 0` for every `i ≠ j`.

R-parametric per design doc §1.8.  The hot-index is an explicit
parameter (as with `IsBoundedRange`'s interval). -/
structure IsOneHot {n : ℕ} (j : Fin n) (y : Fin n → FiniteFp) : Prop where
  /-- The hot index carries value `1`. -/
  hot : ((y j).toVal : R) = 1
  /-- Every other index carries value `0`. -/
  cold : ∀ i, i ≠ j → ((y i).toVal : R) = 0

/-! ## Basic sum-collapse lemmas -/

omit [IsStrictOrderedRing R] in
/-- Under `IsOneHot j y`, the weighted sum `Σ y_i · f i` collapses to the
hot-index evaluation `f j`.  The fundamental algebraic fact underlying
every one-hot specialization. -/
theorem IsOneHot.sum_eq {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) (f : Fin n → R) :
    ∑ i, ((y i).toVal : R) * f i = f j := by
  rw [Finset.sum_eq_single j]
  · rw [h.hot, one_mul]
  · intro i _ hij
    rw [h.cold i hij, zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ j) hmem

/-- Magnitude sum-collapse: `Σ |y_i · f i| = |f j|`. -/
theorem IsOneHot.sum_abs_eq {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) (f : Fin n → R) :
    ∑ i, |((y i).toVal : R) * f i| = |f j| := by
  rw [Finset.sum_eq_single j]
  · rw [h.hot, one_mul]
  · intro i _ hij
    rw [h.cold i hij, zero_mul, abs_zero]
  · intro hmem; exact absurd (Finset.mem_univ j) hmem

/-- `Σ |y_i| = 1` — the total mass of a one-hot vector. -/
theorem IsOneHot.sum_abs_eq_one {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) :
    ∑ i, |((y i).toVal : R)| = 1 := by
  rw [Finset.sum_eq_single j]
  · rw [h.hot, abs_one]
  · intro i _ hij
    rw [h.cold i hij, abs_zero]
  · intro hmem; exact absurd (Finset.mem_univ j) hmem

/-- Per-index weighted-sum collapse.  For a function `g : Fin n → R`,
`Σ |y_i| · g i = g j`. -/
theorem IsOneHot.weighted_sum_eq {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) (g : Fin n → R) :
    ∑ i, |((y i).toVal : R)| * g i = g j := by
  rw [Finset.sum_eq_single j]
  · rw [h.hot, abs_one, one_mul]
  · intro i _ hij
    rw [h.cold i hij, abs_zero, zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ j) hmem

/-! ## Sanity properties -/

/-- Under `IsOneHot j y`, every entry is non-negative (either `1` or `0`). -/
theorem IsOneHot.toVal_nonneg {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) (i : Fin n) :
    (0 : R) ≤ ((y i).toVal : R) := by
  by_cases hij : i = j
  · rw [hij, h.hot]; exact zero_le_one
  · rw [h.cold i hij]

/-- Under `IsOneHot j y`, every entry is bounded by `1`. -/
theorem IsOneHot.toVal_le_one {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) (i : Fin n) :
    ((y i).toVal : R) ≤ 1 := by
  by_cases hij : i = j
  · rw [hij, h.hot]
  · rw [h.cold i hij]; exact zero_le_one

end Flean.Tags

/-! ## Tag-specialized cross-entropy bound

`fpCrossEntropy_oneHot_error_bound` specializes
`fpCrossEntropy_end_to_end_error_bound` by folding the one-hot tag's
sum-collapse lemmas into the output bound.  The two summations
(`Σ|y_i·r_i|` and `Σ|y_i|·…`) reduce to single-index evaluations at
`j`. -/

namespace CrossEntropy

open Finset BigOperators LogSumExp Softmax Flean.Tags

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

variable {n : ℕ}

/-- **One-hot cross-entropy error bound**.

Under `IsOneHot j ys`, the general CE error bound collapses to a
single-index form: the dot-product bound contributes `dp.relErr ·
|r_j.toVal|` (instead of `Σ|y_i · r_i|`) and the shift-propagation
contributes only the `i = j` term.

This is the standard ML classifier-loss regime — CE on a one-hot
target — and it gives a dramatically tighter bound than the general
dense-`y` case. -/
theorem fpCrossEntropy_oneHot_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (ys : Fin n → FiniteFp)
    (j : Fin n)
    (h_onehot : IsOneHot (R := ℝ) j ys)
    (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ k,
      ((xs' k).toVal : ℝ) = ((xs k).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
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
      (η : ℝ) * |logsumexp (fun k => ((xs k).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun k => ((xs k).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst
    |(((- dp.result).toVal : ℝ)) -
        crossEntropy (fun i => ((ys i).toVal : ℝ))
                     (fun i => ((xs i).toVal : ℝ))| ≤
      dp.relErr * |((r j).toVal : ℝ)| +
      ((η : ℝ) * |((xs j).toVal : ℝ) - (lse.toVal : ℝ)| +
        Softmax.subnormalConst + Δ_LSE) := by
  -- Freeze the iterated `letI` bindings so the collapse lemmas have
  -- concrete terms to rewrite.
  set ε_sum : ℝ :=
    ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
      (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst with hε_def
  set D_log : ℝ := ε_sum / (1 - ε_sum) with hDlog_def
  set Δ_LSE : ℝ :=
    (η : ℝ) * |logsumexp (fun k => ((xs k).toVal : ℝ))| +
    (1 + (η : ℝ)) *
      (η_log *
          (logsumexp (fun k => ((xs k).toVal : ℝ)) -
            ((fpMax xs hn).toVal : ℝ)) +
        (1 + η_log) * D_log + logSubConst) +
    Softmax.subnormalConst with hΔ_def
  have h_gen := fpCrossEntropy_end_to_end_error_bound hn xs ys
    xs' h_shift_exact exps h_exp sum h_margin
    logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close
    lse h_final_add h_final_ne
    r h_shift_close dp
  simp only [← hε_def, ← hDlog_def, ← hΔ_def] at h_gen
  rw [h_onehot.sum_abs_eq (fun i => ((r i).toVal : ℝ))] at h_gen
  rw [h_onehot.weighted_sum_eq
      (fun i => (η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
        Softmax.subnormalConst + Δ_LSE)] at h_gen
  exact h_gen

end CrossEntropy
