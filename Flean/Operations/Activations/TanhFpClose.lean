import Flean.Operations.Activations.Tanh
import Flean.Operations.Activations.TanhFp
import Flean.Operations.Activations.SigmoidFpClose
import Flean.Operations.MLP.LayerActivated

/-!
# Closeness Bound for `fpTanhFinite`

Composes the forward-sigmoid closeness (`fpSigmoidFinite_close`) with
the four FP rounding steps in the `tanh = 2σ(2x) − 1` pipeline:
input doubling, inner sigmoid, output doubling, output `−1`.

## Slack expression

```
tanh_slack(xr, tx_real) :=
  2·η·(2+η)·(1 + σ_slack(tx_real))   -- output doubling + sub
  + η                                 -- constant from the −1 step
  + 2·σ_slack(tx_real)                -- forward sigmoid (factor 2 from outer doubling)
  + η·|xr|                            -- σ Lipschitz at input shift
```

where `σ_slack := fpSigmoidFinite_slack` and `tx_real := (tx).toVal`
is the FP intermediate `x + x` (= 2x rounded).

The slack depends on the FP doubled value `tx_real` rather than `2·xr`
directly because the inner sigmoid is fed the rounded value. Bundles
that need a uniform slack across multiple inputs supply an upper bound
covering all per-input slacks.
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeNearest ℝ] [RModeSticky ℝ] [ExpApprox] [ExpApproxSound]

set_option linter.unusedSectionVars false in
private lemma local_hη_lt_one_tanh : (η : ℝ) < 1 := by
  simp only [FloatFormat.hEps_def]
  have hp := FloatFormat.prec_pos
  have hneg : -(FloatFormat.prec : ℤ) < 0 := by omega
  have h1 : (1 : ℝ) < 2 := by norm_num
  calc (2 : ℝ) ^ (-(FloatFormat.prec : ℤ))
      < (2 : ℝ) ^ (0 : ℤ) := zpow_lt_zpow_right₀ h1 hneg
    _ = 1 := zpow_zero _

/-- Slack expression for `fpTanhFinite` against `Real.tanh`.

Parameters:
* `xr` — the original input value `x.toVal`.
* `tx_real` — the FP intermediate `x + x`'s `toVal` (close to `2·xr`
  but not exactly).

Decomposition:
* `2·η·(2+η)·(1 + σ_slack(tx_real))` — combined output-doubling and
  sub-1 rounding errors, amplified by `|tsx − 1|` bound.
* `η` — constant from `|tsx − 1| ≤ ... + 1`.
* `2·σ_slack(tx_real)` — forward sigmoid error, scaled by 2 from outer doubling.
* `η·|xr|` — σ Lipschitz K=1/4 applied to `|tx_real − 2xr| ≤ 2η|xr|`,
  scaled by 2 from outer doubling. -/
noncomputable def fpTanhFinite_slack_at (xr tx_real : ℝ) : ℝ :=
  let σs := fpSigmoidFinite_slack tx_real
  2 * η * (2 + η) * (1 + σs) + η + 2 * σs + η * |xr|

theorem fpTanhFinite_slack_at_nn (xr tx_real : ℝ) :
    0 ≤ fpTanhFinite_slack_at xr tx_real := by
  unfold fpTanhFinite_slack_at
  have hη_nn : (0 : ℝ) ≤ η[ℝ] := by positivity
  have hσs_nn : 0 ≤ fpSigmoidFinite_slack tx_real :=
    fpSigmoidFinite_slack_nn tx_real
  have h_xr_abs : 0 ≤ |xr| := abs_nonneg _
  positivity

/-- **Closeness lemma for the FP tanh kernel.** -/
theorem fpTanhFinite_close (x : FiniteFp)
    {tx : FiniteFp}
    (hdbl1 : fpAddFinite x x = Fp.finite tx)
    {e d sx : FiniteFp}
    (he : fpExpFinite (-tx) = Fp.finite e)
    (hd : fpAddFinite (1 : FiniteFp) e = Fp.finite d)
    (hsig : fpDivFinite (1 : FiniteFp) d = Fp.finite sx)
    {tsx r : FiniteFp}
    (hdbl2 : fpAddFinite sx sx = Fp.finite tsx)
    (hsub : fpSubFinite tsx (1 : FiniteFp) = Fp.finite r)
    (h_dbl1_nr : isNormalRange ((x.toVal : ℝ) + (x.toVal : ℝ)) ∨
                 ((x.toVal : ℝ) + (x.toVal : ℝ) = 0))
    (her_normal : isNormalRange (Real.exp (-((tx.toVal : ℝ)))))
    (h_d_normal : isNormalRange ((1 : ℝ) + (e.toVal : ℝ)) ∨
                  ((1 : ℝ) + (e.toVal : ℝ) = 0))
    (h_r_normal : isNormalRange ((1 : ℝ) / (d.toVal : ℝ)) ∨
                  ((1 : ℝ) / (d.toVal : ℝ) = 0))
    (hd_m_ne : d.m ≠ 0)
    (h_dbl2_nr : isNormalRange ((sx.toVal : ℝ) + (sx.toVal : ℝ)) ∨
                 ((sx.toVal : ℝ) + (sx.toVal : ℝ) = 0))
    (h_sub_nr : isNormalRange ((tsx.toVal : ℝ) - (1 : ℝ)) ∨
                ((tsx.toVal : ℝ) - (1 : ℝ) = 0)) :
    |((r.toVal : ℝ)) - Real.tanh (x.toVal : ℝ)| ≤
      fpTanhFinite_slack_at (x.toVal : ℝ) (tx.toVal : ℝ) := by
  -- Setup
  set xr : ℝ := (x.toVal : ℝ) with hxr_def
  set tx_real : ℝ := (tx.toVal : ℝ) with htx_def
  set sx_fp : ℝ := (sx.toVal : ℝ) with hsx_def
  set tsx_fp : ℝ := (tsx.toVal : ℝ) with htsx_def
  set r_fp : ℝ := (r.toVal : ℝ) with hr_def
  set σs : ℝ := fpSigmoidFinite_slack tx_real with hσs_def
  -- η bounds
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hη_lt : (η : ℝ) < 1 := local_hη_lt_one_tanh
  have hσs_nn : 0 ≤ σs := fpSigmoidFinite_slack_nn tx_real
  -- Step 1: |tx_real - 2xr| ≤ η · |2xr|, hence ≤ 2η · |xr|.
  have h_dbl1_close := KahanSum.fpAdd_error_or_zero (R := ℝ) x x tx hdbl1 h_dbl1_nr
  -- h_dbl1_close : |tx.toVal - (x.toVal + x.toVal)| ≤ η · |x.toVal + x.toVal|
  have h_2xr_eq : (x.toVal : ℝ) + (x.toVal : ℝ) = 2 * xr := by rw [hxr_def]; ring
  rw [h_2xr_eq] at h_dbl1_close
  have h_tx_close : |tx_real - 2 * xr| ≤ η * |2 * xr| := h_dbl1_close
  have h_2_xr_abs : |2 * xr| = 2 * |xr| := by rw [abs_mul]; simp
  rw [h_2_xr_abs] at h_tx_close
  have h_tx_to_2xr : |tx_real - 2 * xr| ≤ 2 * η * |xr| := by linarith
  -- Step 2 (forward sigmoid): |sx_fp - σ(tx_real)| ≤ σs.
  have h_sig_close := fpSigmoidFinite_close tx he hd hsig her_normal h_d_normal h_r_normal hd_m_ne
  rw [← htx_def, ← hsx_def, ← hσs_def] at h_sig_close
  -- h_sig_close : |sx_fp - Real.sigmoid tx_real| ≤ σs
  -- Step 2b: |σ(tx_real) - σ(2xr)| ≤ (1/4) · |tx_real - 2xr| via σ-Lipschitz.
  have h_sig_lip := _root_.Flean.Real.sigmoid_lipschitz_quarter.bound tx_real (2 * xr)
  -- h_sig_lip : |σ(tx_real) - σ(2xr)| ≤ (1/4) · |tx_real - 2xr|
  -- Combining: |sx_fp - σ(2xr)| ≤ σs + (1/4) · |tx_real - 2xr|.
  have h_sx_to_sigma2xr : |sx_fp - Real.sigmoid (2 * xr)| ≤
      σs + (1 / 4) * |tx_real - 2 * xr| := by
    calc |sx_fp - Real.sigmoid (2 * xr)|
        = |(sx_fp - Real.sigmoid tx_real) + (Real.sigmoid tx_real - Real.sigmoid (2 * xr))| := by
          ring_nf
      _ ≤ |sx_fp - Real.sigmoid tx_real| + |Real.sigmoid tx_real - Real.sigmoid (2 * xr)| :=
          abs_add_le _ _
      _ ≤ σs + (1 / 4) * |tx_real - 2 * xr| := by linarith
  -- Step 3: |tsx_fp - 2 sx_fp| ≤ η · |2 sx_fp|.
  have h_dbl2_close := KahanSum.fpAdd_error_or_zero (R := ℝ) sx sx tsx hdbl2 h_dbl2_nr
  have h_2sx_eq : (sx.toVal : ℝ) + (sx.toVal : ℝ) = 2 * sx_fp := by rw [hsx_def]; ring
  rw [h_2sx_eq] at h_dbl2_close
  have h_tsx_close : |tsx_fp - 2 * sx_fp| ≤ η * |2 * sx_fp| := h_dbl2_close
  -- Step 4: |r_fp - (tsx_fp - 1)| ≤ η · |tsx_fp - 1|.
  have h_one_toVal : ((1 : FiniteFp).toVal : ℝ) = 1 := FiniteFp.toVal_one
  have h_sub_nr' : isNormalRange ((tsx.toVal : ℝ) - ((1 : FiniteFp).toVal : ℝ)) ∨
                   ((tsx.toVal : ℝ) - ((1 : FiniteFp).toVal : ℝ) = 0) := by
    rw [h_one_toVal]; exact h_sub_nr
  have h_sub_close := KahanSum.fpSub_error_or_zero (R := ℝ) tsx (1 : FiniteFp) r hsub h_sub_nr'
  rw [h_one_toVal] at h_sub_close
  -- h_sub_close : |r.toVal - (tsx.toVal - 1)| ≤ η · |tsx.toVal - 1|
  have h_r_close : |r_fp - (tsx_fp - 1)| ≤ η * |tsx_fp - 1| := h_sub_close
  -- Bound |sx_fp| ≤ 1 + σs (since σ ∈ (0,1)).
  have h_sigma_abs_le : ∀ y : ℝ, |Real.sigmoid y| ≤ 1 := by
    intro y
    rw [abs_of_pos (Real.sigmoid_pos y)]
    exact Real.sigmoid_le_one y
  have h_sx_abs : |sx_fp| ≤ 1 + σs := by
    calc |sx_fp|
        = |sx_fp - Real.sigmoid tx_real + Real.sigmoid tx_real| := by ring_nf
      _ ≤ |sx_fp - Real.sigmoid tx_real| + |Real.sigmoid tx_real| := abs_add_le _ _
      _ ≤ σs + 1 := by linarith [h_sigma_abs_le tx_real]
      _ = 1 + σs := by ring
  -- |2 · sx_fp| = 2 · |sx_fp| ≤ 2(1 + σs).
  have h_2sx_abs_le : |2 * sx_fp| ≤ 2 * (1 + σs) := by
    rw [abs_mul]; simp; linarith [h_sx_abs]
  -- |tsx_fp| ≤ |2sx_fp| + |tsx_fp - 2sx_fp| ≤ 2(1+σs) + η · 2(1+σs) = 2(1+η)(1+σs).
  have h_tsx_abs : |tsx_fp| ≤ 2 * (1 + η) * (1 + σs) := by
    have h1 := abs_add_le tsx_fp (-(2 * sx_fp))
    -- Wait that's not quite right. Let me redo.
    have h2 : |tsx_fp| ≤ |2 * sx_fp| + |tsx_fp - 2 * sx_fp| := by
      calc |tsx_fp| = |2 * sx_fp + (tsx_fp - 2 * sx_fp)| := by ring_nf
        _ ≤ |2 * sx_fp| + |tsx_fp - 2 * sx_fp| := abs_add_le _ _
    have h3 : η * |2 * sx_fp| ≤ η * (2 * (1 + σs)) :=
      mul_le_mul_of_nonneg_left h_2sx_abs_le hη_nn
    have h4 : |tsx_fp - 2 * sx_fp| ≤ η * (2 * (1 + σs)) := le_trans h_tsx_close h3
    have h5 : |tsx_fp| ≤ 2 * (1 + σs) + η * (2 * (1 + σs)) := by linarith [h_2sx_abs_le, h4]
    have h6 : 2 * (1 + σs) + η * (2 * (1 + σs)) = 2 * (1 + η) * (1 + σs) := by ring
    linarith
  -- |tsx_fp - 1| ≤ |tsx_fp| + 1 ≤ 2(1+η)(1+σs) + 1.
  have h_tsx_minus_one_abs : |tsx_fp - 1| ≤ 2 * (1 + η) * (1 + σs) + 1 := by
    calc |tsx_fp - 1|
        ≤ |tsx_fp| + |(1 : ℝ)| := by
            have := abs_add_le tsx_fp (-(1 : ℝ))
            calc |tsx_fp - 1| = |tsx_fp + -(1 : ℝ)| := by ring_nf
              _ ≤ |tsx_fp| + |-(1 : ℝ)| := abs_add_le _ _
              _ = |tsx_fp| + |(1 : ℝ)| := by rw [abs_neg]
      _ = |tsx_fp| + 1 := by simp
      _ ≤ 2 * (1 + η) * (1 + σs) + 1 := by linarith
  -- Now assemble the final triangle.
  -- |r_fp - tanh(xr)| = |r_fp - (2σ(2xr) - 1)|
  --                  ≤ |r_fp - (tsx_fp - 1)| + |(tsx_fp - 1) - (2σ(2xr) - 1)|
  --                  = |r_fp - (tsx_fp - 1)| + |tsx_fp - 2σ(2xr)|
  -- |tsx_fp - 2σ(2xr)| ≤ |tsx_fp - 2sx_fp| + 2|sx_fp - σ(2xr)|
  --                   ≤ η · |2sx_fp| + 2(σs + (1/4)|tx_real - 2xr|)
  --                   ≤ η · 2(1+σs) + 2σs + (1/2)·|tx_real - 2xr|
  --                   ≤ 2η(1+σs) + 2σs + (1/2) · 2η|xr|
  --                   = 2η(1+σs) + 2σs + η|xr|
  have h_tsx_to_2sigma : |tsx_fp - 2 * Real.sigmoid (2 * xr)| ≤
      η * (2 * (1 + σs)) + 2 * σs + η * |xr| := by
    have h_split : tsx_fp - 2 * Real.sigmoid (2 * xr) =
        (tsx_fp - 2 * sx_fp) + 2 * (sx_fp - Real.sigmoid (2 * xr)) := by ring
    calc |tsx_fp - 2 * Real.sigmoid (2 * xr)|
        = |(tsx_fp - 2 * sx_fp) + 2 * (sx_fp - Real.sigmoid (2 * xr))| := by rw [h_split]
      _ ≤ |tsx_fp - 2 * sx_fp| + |2 * (sx_fp - Real.sigmoid (2 * xr))| := abs_add_le _ _
      _ = |tsx_fp - 2 * sx_fp| + 2 * |sx_fp - Real.sigmoid (2 * xr)| := by
            rw [abs_mul]; simp
      _ ≤ η * |2 * sx_fp| + 2 * (σs + (1 / 4) * |tx_real - 2 * xr|) := by linarith
      _ ≤ η * (2 * (1 + σs)) + 2 * (σs + (1 / 4) * (2 * η * |xr|)) := by
          have h_a : η * |2 * sx_fp| ≤ η * (2 * (1 + σs)) :=
            mul_le_mul_of_nonneg_left h_2sx_abs_le hη_nn
          have h_b : (1 / 4) * |tx_real - 2 * xr| ≤ (1 / 4) * (2 * η * |xr|) :=
            mul_le_mul_of_nonneg_left h_tx_to_2xr (by norm_num)
          linarith
      _ = η * (2 * (1 + σs)) + 2 * σs + η * |xr| := by ring
  -- tanh(xr) = 2σ(2xr) - 1
  have h_tanh_eq : Real.tanh xr = 2 * Real.sigmoid (2 * xr) - 1 :=
    Real.tanh_eq_two_sigmoid_sub_one xr
  -- Final triangle
  have h_final : |r_fp - Real.tanh xr| ≤
      η * |tsx_fp - 1| + (η * (2 * (1 + σs)) + 2 * σs + η * |xr|) := by
    rw [h_tanh_eq]
    have h_split : r_fp - (2 * Real.sigmoid (2 * xr) - 1) =
        (r_fp - (tsx_fp - 1)) + (tsx_fp - 2 * Real.sigmoid (2 * xr)) := by ring
    calc |r_fp - (2 * Real.sigmoid (2 * xr) - 1)|
        = |(r_fp - (tsx_fp - 1)) + (tsx_fp - 2 * Real.sigmoid (2 * xr))| := by rw [h_split]
      _ ≤ |r_fp - (tsx_fp - 1)| + |tsx_fp - 2 * Real.sigmoid (2 * xr)| := abs_add_le _ _
      _ ≤ η * |tsx_fp - 1| + (η * (2 * (1 + σs)) + 2 * σs + η * |xr|) := by linarith
  -- Bound η · |tsx_fp - 1| ≤ η · (2(1+η)(1+σs) + 1).
  have h_step4_loose : η * |tsx_fp - 1| ≤ η * (2 * (1 + η) * (1 + σs) + 1) :=
    mul_le_mul_of_nonneg_left h_tsx_minus_one_abs hη_nn
  -- Algebraic combine: η · (2(1+η)(1+σs) + 1) + (η · 2(1+σs) + 2σs + η|xr|)
  --                  = 2η(1+σs)·[(1+η) + 1] + η + 2σs + η|xr|
  --                  = 2η(2+η)(1+σs) + η + 2σs + η|xr|
  -- which matches `fpTanhFinite_slack_at xr tx_real`.
  have h_combine : η * (2 * (1 + η) * (1 + σs) + 1) +
                   (η * (2 * (1 + σs)) + 2 * σs + η * |xr|) =
                   2 * η * (2 + η) * (1 + σs) + η + 2 * σs + η * |xr| := by ring
  -- Conclude
  show |r_fp - Real.tanh xr| ≤ fpTanhFinite_slack_at xr tx_real
  unfold fpTanhFinite_slack_at
  rw [← hσs_def]
  show |r_fp - Real.tanh xr| ≤ 2 * η * (2 + η) * (1 + σs) + η + 2 * σs + η * |xr|
  rw [← h_combine]
  linarith [h_final, h_step4_loose]

/-! ## Per-input witness bundle and `ActivationFpResult` constructor -/

/-- Per-input finite-path witness for the FP tanh pipeline.
Bundles the four step witnesses + a `SigmoidFpWitness` for the inner sigmoid. -/
structure TanhFpWitness (x : FiniteFp) where
  /-- Rounded `2x`. -/
  tx : FiniteFp
  /-- Rounded `2x` step witness. -/
  hdbl1 : fpAddFinite x x = Fp.finite tx
  /-- Inner forward sigmoid witness on the doubled input. -/
  sig : SigmoidFpWitness tx
  /-- Rounded `2 · sig.r`. -/
  tsx : FiniteFp
  /-- Output doubling step witness. -/
  hdbl2 : fpAddFinite sig.r sig.r = Fp.finite tsx
  /-- Final result (rounded `tsx − 1`). -/
  r : FiniteFp
  /-- Final sub step witness. -/
  hsub : fpSubFinite tsx (1 : FiniteFp) = Fp.finite r

/-- Bundle constructor for the FP tanh: per-input witnesses + uniform
slack bound, returns `MLP.ActivationFpResult Activation.tanh xs`. -/
noncomputable def MLP.ActivationFpResult.ofTanhWitnesses {n : ℕ}
    (xs : Fin n → FiniteFp)
    (w : ∀ i, TanhFpWitness (xs i))
    (slack : ℝ) (slack_nn : 0 ≤ slack)
    (h_dbl1_nr : ∀ i, isNormalRange (((xs i).toVal : ℝ) + ((xs i).toVal : ℝ)) ∨
                      (((xs i).toVal : ℝ) + ((xs i).toVal : ℝ) = 0))
    (her_nr : ∀ i, isNormalRange (Real.exp (-(((w i).tx).toVal : ℝ))))
    (h_d_nr : ∀ i, isNormalRange ((1 : ℝ) + ((w i).sig.e.toVal : ℝ)) ∨
                   ((1 : ℝ) + ((w i).sig.e.toVal : ℝ) = 0))
    (h_r_nr : ∀ i, isNormalRange ((1 : ℝ) / ((w i).sig.d.toVal : ℝ)) ∨
                   ((1 : ℝ) / ((w i).sig.d.toVal : ℝ) = 0))
    (h_d_m_ne : ∀ i, (w i).sig.d.m ≠ 0)
    (h_dbl2_nr : ∀ i, isNormalRange (((w i).sig.r.toVal : ℝ) + ((w i).sig.r.toVal : ℝ)) ∨
                      (((w i).sig.r.toVal : ℝ) + ((w i).sig.r.toVal : ℝ) = 0))
    (h_sub_nr : ∀ i, isNormalRange (((w i).tsx.toVal : ℝ) - (1 : ℝ)) ∨
                     (((w i).tsx.toVal : ℝ) - (1 : ℝ) = 0))
    (h_slack : ∀ i, fpTanhFinite_slack_at ((xs i).toVal : ℝ) (((w i).tx).toVal : ℝ) ≤ slack) :
    MLP.ActivationFpResult (R := ℝ) Flean.Activation.tanh xs where
  result := fun i => (w i).r
  slack := slack
  slack_nn := slack_nn
  h_close := fun i => by
    have h := fpTanhFinite_close (xs i)
                (w i).hdbl1
                (w i).sig.he (w i).sig.hd (w i).sig.hr
                (w i).hdbl2
                (w i).hsub
                (h_dbl1_nr i) (her_nr i) (h_d_nr i) (h_r_nr i) (h_d_m_ne i)
                (h_dbl2_nr i) (h_sub_nr i)
    have hs := h_slack i
    show |(((w i).r.toVal) : ℝ) - Flean.Activation.tanh.apply ((xs i).toVal : ℝ)| ≤ slack
    rw [Flean.Activation.tanh_apply]
    linarith

end Flean
