import Flean.Operations.Activations.Sigmoid
import Flean.Operations.Activations.SigmoidFp
import Flean.Operations.KahanSum
import Flean.Operations.MLP.LayerActivated

/-!
# Closeness Bound for `fpSigmoidFinite`

Proves that the FP sigmoid kernel `fpSigmoidFinite x` is close to the
math reference `Real.sigmoid x.toVal`, with an explicit slack bound
expressed in terms of `η = 2^(-prec)` and the input.

## Result

Under finite-path witnesses (the three intermediate FP operations don't
overflow / NaN) plus standard normal-range hypotheses for the rounding
error bounds, we have:

```
|r.toVal - Real.sigmoid x.toVal| ≤ η·(2 + (2+η)·exp(-x.toVal)) / (1 - η)
```

This is the natural composition of:
* `fpExpFinite_correct + standard_error_additive`: `|e − exp(−x)| ≤ η·exp(−x)`
* `fpAdd_error_or_zero`:                          `|d − (1 + e)| ≤ η·|1 + e|`
* `fpDiv_error_or_zero`:                          `|r − 1/d| ≤ η·|1/d|`

plus the triangle:
```
|r − 1/(1+er)| ≤ |r − 1/d| + |1/d − 1/(1+er)|
              ≤ η/d + |er − e + 1+e − d| / (d · (1+er))
```

The denominator-stability factor `(1 − η)` enters because `d ≥ (1−η)·(1+e)`
rather than `≥ 1` exactly.

## Practical use

The slack expression `fpSigmoidFinite_slack xr = η·(2+(2+η)·exp(−xr))/(1−η)`
is tightest at moderate `xr` (where `exp(−xr)` is bounded). For very
negative `xr` it grows like `exp(−xr)`, making the bound vacuous; users
should constrain inputs to a reasonable domain.
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeNearest ℝ] [RModeSticky ℝ] [ExpApprox] [ExpApproxSound]

set_option linter.unusedSectionVars false in
private lemma local_hη_lt_one : (η : ℝ) < 1 := by
  simp only [FloatFormat.hEps_def]
  have hp := FloatFormat.prec_pos
  have hneg : -(FloatFormat.prec : ℤ) < 0 := by omega
  have h1 : (1 : ℝ) < 2 := by norm_num
  calc (2 : ℝ) ^ (-(FloatFormat.prec : ℤ))
      < (2 : ℝ) ^ (0 : ℤ) := zpow_lt_zpow_right₀ h1 hneg
    _ = 1 := zpow_zero _

/-- Slack expression for `fpSigmoidFinite x` versus `Real.sigmoid x.toVal`.

Composed of three η-rounding contributions plus the denominator-stability
factor `1/(1−η)`:
* `2η`: from `fpDiv` (≤ η, since `1/d ≤ 1/(1−η)`) plus the constant offset;
* `η·(2+η)·exp(−xr)`: scaling with the size of the exponential.

The `(1−η)` denominator reflects that `d_fp ≥ (1−η)·(1+e_fp)` after
add-rounding rather than `d_fp ≥ 1` exactly. -/
noncomputable def fpSigmoidFinite_slack (xr : ℝ) : ℝ :=
  η * (2 + (2 + η) * Real.exp (-xr)) / (1 - η)

theorem fpSigmoidFinite_slack_nn (xr : ℝ) :
    0 ≤ fpSigmoidFinite_slack xr := by
  unfold fpSigmoidFinite_slack
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hη_lt : (η : ℝ) < 1 := local_hη_lt_one
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have h2 : (0 : ℝ) ≤ Real.exp (-xr) := (Real.exp_pos _).le
  have h3 : (0 : ℝ) ≤ 2 + η := by linarith
  have hnum_nn : (0 : ℝ) ≤ η * (2 + (2 + η) * Real.exp (-xr)) := by positivity
  exact div_nonneg hnum_nn h1.le

/-- **Closeness lemma**: when the FP sigmoid pipeline produces a finite
result via finite intermediates, that result is within
`fpSigmoidFinite_slack` of the math sigmoid. -/
theorem fpSigmoidFinite_close (x : FiniteFp) {e d r : FiniteFp}
    (he : fpExpFinite (-x) = Fp.finite e)
    (hd : fpAddFinite (1 : FiniteFp) e = Fp.finite d)
    (hr : fpDivFinite (1 : FiniteFp) d = Fp.finite r)
    (her_normal : isNormalRange (Real.exp (-(x.toVal : ℝ))))
    (h_d_normal : isNormalRange ((1 : ℝ) + (e.toVal : ℝ)) ∨
                  ((1 : ℝ) + (e.toVal : ℝ) = 0))
    (h_r_normal : isNormalRange ((1 : ℝ) / (d.toVal : ℝ)) ∨
                  ((1 : ℝ) / (d.toVal : ℝ) = 0))
    (hd_m_ne : d.m ≠ 0) :
    |((r.toVal : ℝ)) - Real.sigmoid (x.toVal : ℝ)| ≤
      fpSigmoidFinite_slack (x.toVal : ℝ) := by
  -- Set up abbreviations.
  set xr : ℝ := (x.toVal : ℝ) with hxr_def
  set er : ℝ := Real.exp (-xr) with her_def
  set e_fp : ℝ := (e.toVal : ℝ) with he_fp_def
  set d_fp : ℝ := (d.toVal : ℝ) with hd_fp_def
  set r_fp : ℝ := (r.toVal : ℝ) with hr_fp_def
  -- Real-side facts.
  have her_pos : 0 < er := Real.exp_pos _
  have her_nn : 0 ≤ er := her_pos.le
  -- η bounds.
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hη_lt : (η : ℝ) < 1 := local_hη_lt_one
  have h_one_minus_η_pos : (0 : ℝ) < 1 - η := by linarith
  -- Step 1: |e_fp − er| ≤ η · er.
  have h_neg_x_toVal : ((-x).toVal : ℝ) = -xr := by
    rw [hxr_def]; exact FiniteFp.toVal_neg_eq_neg x
  have h_exp_eq_round : fpExpFinite (-x) = ○er := by
    rw [fpExpFinite_correct (-x), h_neg_x_toVal]
  have h_round_e : ○er = Fp.finite e := h_exp_eq_round ▸ he
  have h_e_close_abs : |e_fp - er| ≤ η * |er| :=
    KahanSum.standard_error_additive (R := ℝ) er her_normal e h_round_e
  have h_er_abs : |er| = er := abs_of_nonneg her_nn
  have h_e_close : |e_fp - er| ≤ η * er := by rw [h_er_abs] at h_e_close_abs; exact h_e_close_abs
  -- e_fp positivity / range.
  have h_e_diff_le := abs_le.mp h_e_close
  have h_e_fp_lo : (1 - η) * er ≤ e_fp := by linarith [h_e_diff_le.1]
  have h_e_fp_hi : e_fp ≤ (1 + η) * er := by linarith [h_e_diff_le.2]
  have h_e_fp_nn : 0 ≤ e_fp := by
    have : 0 ≤ (1 - η) * er := mul_nonneg (by linarith) her_nn
    linarith
  have h_one_plus_e_fp_pos : 0 < 1 + e_fp := by linarith
  have h_one_plus_e_fp_nn : 0 ≤ 1 + e_fp := h_one_plus_e_fp_pos.le
  have h_one_plus_e_fp_abs : |1 + e_fp| = 1 + e_fp := abs_of_nonneg h_one_plus_e_fp_nn
  -- Step 2: |d_fp − (1 + e_fp)| ≤ η · |1 + e_fp|  =  η · (1 + e_fp).
  have h_one_toVal : ((1 : FiniteFp).toVal : ℝ) = 1 := FiniteFp.toVal_one
  -- Bridge the user-facing `(1 : ℝ) + e_fp` form to the `(1 : FiniteFp).toVal + e.toVal` form.
  have h_d_normal' : isNormalRange (((1 : FiniteFp).toVal : ℝ) + (e.toVal : ℝ)) ∨
                     (((1 : FiniteFp).toVal : ℝ) + (e.toVal : ℝ) = 0) := by
    rw [h_one_toVal]; exact h_d_normal
  have h_d_close_raw := KahanSum.fpAdd_error_or_zero (R := ℝ) (1 : FiniteFp) e d hd h_d_normal'
  rw [h_one_toVal] at h_d_close_raw
  have h_d_close : |d_fp - (1 + e_fp)| ≤ η * (1 + e_fp) := by
    rw [h_one_plus_e_fp_abs] at h_d_close_raw
    exact h_d_close_raw
  -- d_fp positivity / range.
  have h_d_diff_le := abs_le.mp h_d_close
  have h_d_fp_lo : (1 - η) * (1 + e_fp) ≤ d_fp := by linarith [h_d_diff_le.1]
  have h_d_fp_hi : d_fp ≤ (1 + η) * (1 + e_fp) := by linarith [h_d_diff_le.2]
  have h_d_fp_pos : 0 < d_fp := by
    have h1 : 0 < (1 - η) * (1 + e_fp) := mul_pos h_one_minus_η_pos h_one_plus_e_fp_pos
    linarith
  have h_d_fp_ge_one_minus_η : 1 - η ≤ d_fp := by
    have : (1 - η) * 1 ≤ (1 - η) * (1 + e_fp) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- Step 3: |r_fp − 1/d_fp| ≤ η · |1/d_fp| = η / d_fp.
  -- Lean elaborates `(1 : FiniteFp) / d : Fp` as `Fp.finite 1 / Fp.finite d` (using
  -- `HDiv Fp Fp Fp`) when the FiniteFp/FiniteFp instance isn't picked first, so we
  -- bridge via `fpDiv_finite_finite`.
  have hr_form : Fp.finite (1 : FiniteFp) / Fp.finite d = Fp.finite r := by
    rw [fpDiv_finite_finite (1 : FiniteFp) d hd_m_ne]; exact hr
  have h_r_normal' : isNormalRange (((1 : FiniteFp).toVal : ℝ) / (d.toVal : ℝ)) ∨
                     (((1 : FiniteFp).toVal : ℝ) / (d.toVal : ℝ) = 0) := by
    rw [h_one_toVal]; exact h_r_normal
  have h_r_close_raw := KahanSum.fpDiv_error_or_zero (R := ℝ) (1 : FiniteFp) d r
    hd_m_ne hr_form h_r_normal'
  rw [h_one_toVal] at h_r_close_raw
  -- h_r_close_raw : |r_fp - 1/d_fp| ≤ η * |1/d_fp|
  have h_one_over_d_pos : 0 < 1 / d_fp := one_div_pos.mpr h_d_fp_pos
  have h_one_over_d_abs : |1 / d_fp| = 1 / d_fp := abs_of_pos h_one_over_d_pos
  have h_r_close : |r_fp - 1 / d_fp| ≤ η * (1 / d_fp) := by
    rw [h_one_over_d_abs] at h_r_close_raw; exact h_r_close_raw
  -- d_real := 1 + er.
  have h_d_real_pos : (0 : ℝ) < 1 + er := by linarith
  -- |1/d_fp − 1/(1+er)| bound via |d_real - d_fp| / (d_fp · (1+er)).
  -- |d_real − d_fp| ≤ |er − e_fp| + |(1 + e_fp) − d_fp| ≤ η·er + η·(1+e_fp).
  have h_dr_diff : |(1 + er) - d_fp| ≤ η * er + η * (1 + e_fp) := by
    have h_split : (1 + er) - d_fp = (er - e_fp) + ((1 + e_fp) - d_fp) := by ring
    have h_t1 : |er - e_fp| ≤ η * er := by
      rw [abs_sub_comm]; exact h_e_close
    have h_t2 : |(1 + e_fp) - d_fp| ≤ η * (1 + e_fp) := by
      rw [abs_sub_comm]; exact h_d_close
    calc |(1 + er) - d_fp|
        = |(er - e_fp) + ((1 + e_fp) - d_fp)| := by rw [h_split]
      _ ≤ |er - e_fp| + |(1 + e_fp) - d_fp| := abs_add_le _ _
      _ ≤ η * er + η * (1 + e_fp) := by linarith
  -- Bound the cross term |1/d_fp − 1/(1+er)|.
  have h_cross : |(1 / d_fp) - (1 / (1 + er))| ≤
      (η * er + η * (1 + e_fp)) / (d_fp * (1 + er)) := by
    have h_id : 1 / d_fp - 1 / (1 + er) = ((1 + er) - d_fp) / (d_fp * (1 + er)) := by
      field_simp
    have h_prod_pos : 0 < d_fp * (1 + er) := mul_pos h_d_fp_pos h_d_real_pos
    rw [h_id, abs_div, abs_of_pos h_prod_pos]
    exact div_le_div_of_nonneg_right h_dr_diff h_prod_pos.le
  -- Lower bound the product: d_fp · (1+er) ≥ (1−η)·1 = 1−η.
  have h_prod_lb : 1 - η ≤ d_fp * (1 + er) := by
    calc 1 - η = (1 - η) * 1 := by ring
      _ ≤ d_fp * 1 := mul_le_mul_of_nonneg_right h_d_fp_ge_one_minus_η (by norm_num)
      _ ≤ d_fp * (1 + er) :=
          mul_le_mul_of_nonneg_left (by linarith) h_d_fp_pos.le
  have h_prod_pos : 0 < d_fp * (1 + er) := mul_pos h_d_fp_pos h_d_real_pos
  -- Loosen the cross bound by replacing the denominator with its lower bound.
  have h_dr_num_nn : 0 ≤ η * er + η * (1 + e_fp) := by
    have := mul_nonneg hη_nn her_nn
    have := mul_nonneg hη_nn h_one_plus_e_fp_nn
    linarith
  have h_cross_loosened : |(1 / d_fp) - (1 / (1 + er))| ≤
      (η * er + η * (1 + e_fp)) / (1 - η) := by
    calc |(1 / d_fp) - (1 / (1 + er))|
        ≤ (η * er + η * (1 + e_fp)) / (d_fp * (1 + er)) := h_cross
      _ ≤ (η * er + η * (1 + e_fp)) / (1 - η) :=
          div_le_div_of_nonneg_left h_dr_num_nn h_one_minus_η_pos h_prod_lb
  -- Bound |1/d_fp| ≤ 1/(1-η).
  have h_inv_d_lb : 1 / d_fp ≤ 1 / (1 - η) :=
    one_div_le_one_div_of_le h_one_minus_η_pos h_d_fp_ge_one_minus_η
  have h_step3_loosened : |r_fp - 1 / d_fp| ≤ η * (1 / (1 - η)) := by
    calc |r_fp - 1 / d_fp|
        ≤ η * (1 / d_fp) := h_r_close
      _ ≤ η * (1 / (1 - η)) := mul_le_mul_of_nonneg_left h_inv_d_lb hη_nn
  -- Real.sigmoid xr = 1/(1+er).
  have h_sigmoid_eq : Real.sigmoid xr = 1 / (1 + er) := by
    rw [Real.sigmoid_def, ← her_def, one_div]
  -- Triangle on |r_fp - sigmoid(xr)|.
  have h_tri : |r_fp - Real.sigmoid xr| ≤
      η * (1 / (1 - η)) + (η * er + η * (1 + e_fp)) / (1 - η) := by
    rw [h_sigmoid_eq]
    calc |r_fp - 1 / (1 + er)|
        = |(r_fp - 1 / d_fp) + (1 / d_fp - 1 / (1 + er))| := by ring_nf
      _ ≤ |r_fp - 1 / d_fp| + |1 / d_fp - 1 / (1 + er)| := abs_add_le _ _
      _ ≤ η * (1 / (1 - η)) + (η * er + η * (1 + e_fp)) / (1 - η) := by
          linarith [h_step3_loosened, h_cross_loosened]
  -- Algebraic simplification: combine into the slack formula.
  -- slack = η·(2 + (2+η)·er)/(1-η)
  -- LHS bound = η/(1-η) + (η·er + η·(1+e_fp))/(1-η)
  --           = (η + η·er + η·(1+e_fp))/(1-η)
  --           = η·(2 + er + e_fp)/(1-η)
  -- e_fp ≤ (1+η)·er, so 2 + er + e_fp ≤ 2 + er + (1+η)·er = 2 + (2+η)·er.
  have h_combine_num : η * (1 / (1 - η)) + (η * er + η * (1 + e_fp)) / (1 - η) =
      η * (2 + er + e_fp) / (1 - η) := by
    field_simp
    ring
  rw [h_combine_num] at h_tri
  -- Final monotonicity: e_fp ≤ (1+η)·er ⟹ 2 + er + e_fp ≤ 2 + (2+η)·er.
  have h_sum_le : 2 + er + e_fp ≤ 2 + (2 + η) * er := by
    have : er + e_fp ≤ er + (1 + η) * er := by linarith [h_e_fp_hi]
    have : er + e_fp ≤ (2 + η) * er := by linarith
    linarith
  have h_num_le : η * (2 + er + e_fp) ≤ η * (2 + (2 + η) * er) :=
    mul_le_mul_of_nonneg_left h_sum_le hη_nn
  have h_div_mono : η * (2 + er + e_fp) / (1 - η) ≤
      η * (2 + (2 + η) * er) / (1 - η) :=
    div_le_div_of_nonneg_right h_num_le h_one_minus_η_pos.le
  -- Conclude.
  unfold fpSigmoidFinite_slack
  exact le_trans h_tri h_div_mono

/-! ## Per-input witness bundle and `ActivationFpResult` constructor

The closeness lemma is conditional on three FP intermediate witnesses
(exp finite, add finite, div finite) plus normal-range hypotheses. We
package these per-input into `SigmoidFpWitness`, then ship a
constructor that lifts a vector of per-input witnesses into an
`MLP.ActivationFpResult` paired with `Activation.sigmoid`. -/

/-- Per-input finite-path witness for the FP sigmoid pipeline. -/
structure SigmoidFpWitness (x : FiniteFp) where
  /-- Rounded `exp(-x)`. -/
  e : FiniteFp
  /-- Rounded `1 + e`. -/
  d : FiniteFp
  /-- Rounded `1 / d`, the FP sigmoid result. -/
  r : FiniteFp
  /-- exp step landed in finite range. -/
  he : fpExpFinite (-x) = Fp.finite e
  /-- add step landed in finite range. -/
  hd : fpAddFinite (1 : FiniteFp) e = Fp.finite d
  /-- div step landed in finite range. -/
  hr : fpDivFinite (1 : FiniteFp) d = Fp.finite r

/-- Bundle constructor for the FP sigmoid: given per-input witnesses
plus normal-range hypotheses and a uniform slack bound, produce an
`MLP.ActivationFpResult` for `Activation.sigmoid`. -/
noncomputable def MLP.ActivationFpResult.ofSigmoidWitnesses {n : ℕ}
    (xs : Fin n → FiniteFp)
    (w : ∀ i, SigmoidFpWitness (xs i))
    (slack : ℝ) (slack_nn : 0 ≤ slack)
    (her_nr : ∀ i, isNormalRange (Real.exp (-((xs i).toVal : ℝ))))
    (h_d_nr : ∀ i, isNormalRange ((1 : ℝ) + ((w i).e.toVal : ℝ)) ∨
                   ((1 : ℝ) + ((w i).e.toVal : ℝ) = 0))
    (h_r_nr : ∀ i, isNormalRange ((1 : ℝ) / ((w i).d.toVal : ℝ)) ∨
                   ((1 : ℝ) / ((w i).d.toVal : ℝ) = 0))
    (h_d_m_ne : ∀ i, (w i).d.m ≠ 0)
    (h_slack : ∀ i, fpSigmoidFinite_slack ((xs i).toVal : ℝ) ≤ slack) :
    MLP.ActivationFpResult (R := ℝ) Flean.Activation.sigmoid xs where
  result := fun i => (w i).r
  slack := slack
  slack_nn := slack_nn
  h_close := fun i => by
    have h := fpSigmoidFinite_close (xs i) (w i).he (w i).hd (w i).hr
                (her_nr i) (h_d_nr i) (h_r_nr i) (h_d_m_ne i)
    have hs := h_slack i
    -- `Activation.sigmoid.apply x = Real.sigmoid x` definitionally.
    show |(((w i).r.toVal) : ℝ) - Flean.Activation.sigmoid.apply ((xs i).toVal : ℝ)| ≤ slack
    rw [Flean.Activation.sigmoid_apply]
    linarith

/-! ## ActivatedLayer integration

Plumbs `ofSigmoidWitnesses` into `MLP.ActivatedLayerFpResult` so the
sigmoid kernel is consumable by the activated-layer error-bound stack. -/

section LayerIntegration

variable [RModeConj ℝ] [RModeZero ℝ]

/-- Bundle constructor: lift a linear `LayerFpResult` plus per-i sigmoid
witnesses on its outputs to an `ActivatedLayerFpResult` for the
sigmoid-activated layer `⟨L, Flean.Activation.sigmoid⟩`. -/
noncomputable def MLP.ActivatedLayerFpResult.ofSigmoidLinear {n_in n_out : ℕ}
    {L : MLP.Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (linear : MLP.LayerFpResult L x ℝ)
    (w : ∀ i, SigmoidFpWitness (linear.result i))
    (slack : ℝ) (slack_nn : 0 ≤ slack)
    (her_nr : ∀ i, isNormalRange (Real.exp (-((linear.result i).toVal : ℝ))))
    (h_d_nr : ∀ i, isNormalRange ((1 : ℝ) + ((w i).e.toVal : ℝ)) ∨
                   ((1 : ℝ) + ((w i).e.toVal : ℝ) = 0))
    (h_r_nr : ∀ i, isNormalRange ((1 : ℝ) / ((w i).d.toVal : ℝ)) ∨
                   ((1 : ℝ) / ((w i).d.toVal : ℝ) = 0))
    (h_d_m_ne : ∀ i, (w i).d.m ≠ 0)
    (h_slack : ∀ i, fpSigmoidFinite_slack ((linear.result i).toVal : ℝ) ≤ slack) :
    MLP.ActivatedLayerFpResult
      ({ layer := L, activation := Flean.Activation.sigmoid } :
        MLP.ActivatedLayer ℝ n_in n_out) x where
  linear := linear
  activated := MLP.ActivationFpResult.ofSigmoidWitnesses
    linear.result w slack slack_nn her_nr h_d_nr h_r_nr h_d_m_ne h_slack

/-- **Demo**: forward error bound for an activated layer using sigmoid as
the activation, constructed via `ActivatedLayerFpResult.ofSigmoidLinear`.
Specializes the general activated bound at `K = 1/4`:

```
|fp_result_i − σ(W·x + b)_i| ≤ slack + (1/4) · linear.errorBound
```

Threads the linear-stage error and the per-input sigmoid kernel slack
through `LipschitzScalar.errorAmplification`. -/
theorem MLP.ActivatedLayerFpResult.forward_error_bound_sigmoid_demo
    {n_in n_out : ℕ}
    {L : MLP.Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (linear : MLP.LayerFpResult L x ℝ)
    (w : ∀ i, SigmoidFpWitness (linear.result i))
    (slack : ℝ) (slack_nn : 0 ≤ slack)
    (her_nr : ∀ i, isNormalRange (Real.exp (-((linear.result i).toVal : ℝ))))
    (h_d_nr : ∀ i, isNormalRange ((1 : ℝ) + ((w i).e.toVal : ℝ)) ∨
                   ((1 : ℝ) + ((w i).e.toVal : ℝ) = 0))
    (h_r_nr : ∀ i, isNormalRange ((1 : ℝ) / ((w i).d.toVal : ℝ)) ∨
                   ((1 : ℝ) / ((w i).d.toVal : ℝ) = 0))
    (h_d_m_ne : ∀ i, (w i).d.m ≠ 0)
    (h_slack : ∀ i, fpSigmoidFinite_slack ((linear.result i).toVal : ℝ) ≤ slack)
    {wMax bMax : ℝ} (hL : MLP.BoundedParams (R := ℝ) L wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : ℝ} (hx : ∀ j, Flean.Tags.HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    let LA : MLP.ActivatedLayer ℝ n_in n_out :=
      { layer := L, activation := Flean.Activation.sigmoid }
    let res : MLP.ActivatedLayerFpResult LA x :=
      MLP.ActivatedLayerFpResult.ofSigmoidLinear linear w slack
        slack_nn her_nr h_d_nr h_r_nr h_d_m_ne h_slack
    |((res.activated.result i).toVal : ℝ) -
        LA.forward (fun j => ((x j).toVal : ℝ)) i| ≤
      slack + (1 / 4 : ℝ) * linear.errorBound wMax xMax bMax := by
  intro LA res
  have h := res.forward_error_bound hL hwMax_nn hx hxMax_nn i
  -- `res.errorBound` unfolds to
  -- `res.activated.slack + LA.activation.K * res.linear.errorBound`,
  -- and structure projections + `Activation.sigmoid.K = 1/4` make this
  -- defeq to the demo bound.
  exact h

end LayerIntegration

end Flean
