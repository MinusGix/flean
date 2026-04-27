import Flean.Operations.Activations.Tanh
import Flean.Operations.Activations.TanhFp
import Flean.Operations.Activations.TanhFpClose
import Flean.Operations.Mul
import Flean.Operations.Sub

/-!
# Floating-Point Tanh Derivative

`tanh'(x) = 1 − tanh²(x)`. FP implementation:

```
fpTanhDerivFinite x = fpSub 1 (fpMul (fpTanh x) (fpTanh x))
```

Composes with the existing `fpTanhFinite` + closeness, plus two extra
FP rounding steps (mul + sub).

## Slack expression

Let `T := fpTanhFinite_slack_at xr tx_real` (forward tanh slack). Then:

```
tanh_deriv_slack(xr, tx_real) := η + η·(2+η)·(1+T)² + (2+T)·T
```

Decomposition mirrors the sigmoid derivative:
* `(2+T)·T` — propagation of forward tanh slack into both factors of `t²`.
* `η·(2+η)·(1+T)²` — combined `fpMul` (η·|t²|) and `fpSub` (η·|1 − t²|)
  rounding errors, amplified by the worst-case magnitude `(1+η)(1+T)²`.
* `η` — constant from `|1 − sq_fp|` bound.
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RModeExec] [ExpApprox]

/-! ## FP definitions -/

/-- Floating-point tanh derivative kernel for finite inputs.

Computes `1 − tanh²(x)` via:
1. `t := fpTanhFinite x`
2. `sq := fpMul t t`
3. `r := fpSub 1 sq` -/
noncomputable def fpTanhDerivFinite (x : FiniteFp) : Fp :=
  match fpTanhFinite x with
  | .NaN => .NaN
  | .infinite s => .infinite s
  | .finite t =>
      match fpMulFinite t t with
      | .NaN => .NaN
      | .infinite s => .infinite s
      | .finite sq => fpSubFinite (1 : FiniteFp) sq

/-- IEEE-style FP tanh derivative `Fp → Fp`. -/
noncomputable def fpTanhDeriv (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .finite 0  -- tanh'(+∞) = 0
  | .infinite true => .finite 0   -- tanh'(−∞) = 0
  | .finite a => fpTanhDerivFinite a

@[simp] theorem fpTanhDeriv_finite (a : FiniteFp) :
    fpTanhDeriv (Fp.finite a) = fpTanhDerivFinite a := rfl

@[simp] theorem fpTanhDeriv_nan : fpTanhDeriv Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpTanhDeriv_pos_inf :
    fpTanhDeriv (Fp.infinite false) = Fp.finite 0 := rfl

@[simp] theorem fpTanhDeriv_neg_inf :
    fpTanhDeriv (Fp.infinite true) = Fp.finite 0 := rfl

/-! ## Result-shape -/

/-- Finite-path reduction. -/
theorem fpTanhDerivFinite_eq_sub_of_finite (x : FiniteFp) {t sq : FiniteFp}
    (htanh : fpTanhFinite x = Fp.finite t)
    (hmul : fpMulFinite t t = Fp.finite sq) :
    fpTanhDerivFinite x = fpSubFinite (1 : FiniteFp) sq := by
  unfold fpTanhDerivFinite
  rw [htanh]
  simp only
  rw [hmul]

/-! ## Closeness lemma -/

section Close

variable [RMode ℝ] [RoundIntSigMSound ℝ] [RModeNearest ℝ] [RModeSticky ℝ]
  [ExpApproxSound]

set_option linter.unusedSectionVars false in
/-- Bound: `|Real.tanh x| ≤ 1`, derived from `tanh = 2σ(2x) − 1` and σ ∈ (0,1). -/
private lemma abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [Real.tanh_eq_two_sigmoid_sub_one]
  have h1 := Real.sigmoid_pos (2 * x)
  have h2 := Real.sigmoid_le_one (2 * x)
  rw [abs_le]; constructor <;> linarith

set_option linter.unusedSectionVars false in
private lemma local_hη_lt_one_deriv : (η : ℝ) < 1 := by
  simp only [FloatFormat.hEps_def]
  have hp := FloatFormat.prec_pos
  have hneg : -(FloatFormat.prec : ℤ) < 0 := by omega
  have h1 : (1 : ℝ) < 2 := by norm_num
  calc (2 : ℝ) ^ (-(FloatFormat.prec : ℤ))
      < (2 : ℝ) ^ (0 : ℤ) := zpow_lt_zpow_right₀ h1 hneg
    _ = 1 := zpow_zero _

/-- Slack expression for `fpTanhDerivFinite` against `1 − Real.tanh² xr`. -/
noncomputable def fpTanhDerivFinite_slack_at (xr tx_real : ℝ) : ℝ :=
  let T := fpTanhFinite_slack_at xr tx_real
  η + η * (2 + η) * (1 + T) ^ 2 + (2 + T) * T

theorem fpTanhDerivFinite_slack_at_nn (xr tx_real : ℝ) :
    0 ≤ fpTanhDerivFinite_slack_at xr tx_real := by
  unfold fpTanhDerivFinite_slack_at
  have hη_nn : (0 : ℝ) ≤ η[ℝ] := by positivity
  have hT_nn : 0 ≤ fpTanhFinite_slack_at xr tx_real :=
    fpTanhFinite_slack_at_nn xr tx_real
  have h1 : 0 ≤ (1 + fpTanhFinite_slack_at xr tx_real) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 2 + η[ℝ] := by linarith
  have h3 : 0 ≤ 2 + fpTanhFinite_slack_at xr tx_real := by linarith
  positivity

/-- **Closeness lemma for the FP tanh derivative.** -/
theorem fpTanhDerivFinite_close (x : FiniteFp)
    {tx : FiniteFp}
    (hdbl1 : fpAddFinite x x = Fp.finite tx)
    {e d sx : FiniteFp}
    (he : fpExpFinite (-tx) = Fp.finite e)
    (hd : fpAddFinite (1 : FiniteFp) e = Fp.finite d)
    (hsig : fpDivFinite (1 : FiniteFp) d = Fp.finite sx)
    {tsx t : FiniteFp}
    (hdbl2 : fpAddFinite sx sx = Fp.finite tsx)
    (htanh_sub : fpSubFinite tsx (1 : FiniteFp) = Fp.finite t)
    {sq r : FiniteFp}
    (hmul : fpMulFinite t t = Fp.finite sq)
    (hsub : fpSubFinite (1 : FiniteFp) sq = Fp.finite r)
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
    (h_tanh_sub_nr : isNormalRange ((tsx.toVal : ℝ) - (1 : ℝ)) ∨
                     ((tsx.toVal : ℝ) - (1 : ℝ) = 0))
    (h_mul_nr : isNormalRange ((t.toVal : ℝ) * (t.toVal : ℝ)) ∨
                ((t.toVal : ℝ) * (t.toVal : ℝ) = 0))
    (h_sub_nr : isNormalRange ((1 : ℝ) - (sq.toVal : ℝ)) ∨
                ((1 : ℝ) - (sq.toVal : ℝ) = 0)) :
    |((r.toVal : ℝ)) - (1 - Real.tanh (x.toVal : ℝ) ^ 2)| ≤
      fpTanhDerivFinite_slack_at (x.toVal : ℝ) (tx.toVal : ℝ) := by
  -- Setup
  set xr : ℝ := (x.toVal : ℝ) with hxr_def
  set tx_real : ℝ := (tx.toVal : ℝ) with htx_def
  set t_fp : ℝ := (t.toVal : ℝ) with ht_def
  set sq_fp : ℝ := (sq.toVal : ℝ) with hsq_def
  set r_fp : ℝ := (r.toVal : ℝ) with hr_def
  set T : ℝ := fpTanhFinite_slack_at xr tx_real with hT_def
  -- η bounds
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hη_lt : (η : ℝ) < 1 := local_hη_lt_one_deriv
  have hT_nn : 0 ≤ T := fpTanhFinite_slack_at_nn xr tx_real
  -- Forward tanh closeness: |t_fp − tanh(xr)| ≤ T.
  have h_tanh_close := fpTanhFinite_close x hdbl1 he hd hsig hdbl2 htanh_sub
                        h_dbl1_nr her_normal h_d_normal h_r_normal hd_m_ne
                        h_dbl2_nr h_tanh_sub_nr
  rw [← hxr_def, ← htx_def, ← ht_def, ← hT_def] at h_tanh_close
  -- |tanh(xr)| ≤ 1
  have h_tanh_abs_le : |Real.tanh xr| ≤ 1 := abs_tanh_le_one xr
  -- |t_fp| ≤ 1 + T
  have h_t_fp_abs : |t_fp| ≤ 1 + T := by
    calc |t_fp| = |t_fp - Real.tanh xr + Real.tanh xr| := by ring_nf
      _ ≤ |t_fp - Real.tanh xr| + |Real.tanh xr| := abs_add_le _ _
      _ ≤ T + 1 := by linarith
      _ = 1 + T := by ring
  have h_t_fp_sq_abs : t_fp ^ 2 ≤ (1 + T) ^ 2 := by
    rcases abs_le.mp h_t_fp_abs with ⟨h1, h2⟩
    nlinarith [hT_nn, h1, h2]
  -- Step: mul closeness |sq_fp - t_fp²| ≤ η · t_fp²
  have h_t_sq_eq : (t.toVal : ℝ) * (t.toVal : ℝ) = t_fp ^ 2 := by
    rw [ht_def]; ring
  have h_mul_nr' : isNormalRange (t_fp ^ 2) ∨ (t_fp ^ 2 = 0) := by
    rw [← h_t_sq_eq]; exact h_mul_nr
  have h_mul_close := KahanSum.fpMul_error_or_zero (R := ℝ) t t sq hmul h_mul_nr
  rw [h_t_sq_eq] at h_mul_close
  rw [← hsq_def] at h_mul_close
  -- h_mul_close : |sq_fp - t_fp ^ 2| ≤ η · |t_fp ^ 2|
  have h_t_sq_nn : 0 ≤ t_fp ^ 2 := sq_nonneg _
  have h_t_sq_abs : |t_fp ^ 2| = t_fp ^ 2 := abs_of_nonneg h_t_sq_nn
  rw [h_t_sq_abs] at h_mul_close
  -- |sq_fp| ≤ (1 + η)(1 + T)²
  have h_sq_abs : |sq_fp| ≤ (1 + η) * (1 + T) ^ 2 := by
    calc |sq_fp| = |sq_fp - t_fp ^ 2 + t_fp ^ 2| := by ring_nf
      _ ≤ |sq_fp - t_fp ^ 2| + |t_fp ^ 2| := abs_add_le _ _
      _ ≤ η * t_fp ^ 2 + t_fp ^ 2 := by linarith [h_t_sq_abs]
      _ = (1 + η) * t_fp ^ 2 := by ring
      _ ≤ (1 + η) * (1 + T) ^ 2 := by
          have h1η_nn : (0 : ℝ) ≤ 1 + η := by linarith
          exact mul_le_mul_of_nonneg_left h_t_fp_sq_abs h1η_nn
  -- |1 - sq_fp| ≤ 1 + |sq_fp| ≤ 1 + (1+η)(1+T)²
  have h_one_minus_sq_abs : |1 - sq_fp| ≤ 1 + (1 + η) * (1 + T) ^ 2 := by
    calc |1 - sq_fp| = |1 + (-sq_fp)| := by ring_nf
      _ ≤ |(1 : ℝ)| + |-sq_fp| := abs_add_le _ _
      _ = 1 + |sq_fp| := by rw [abs_neg]; simp
      _ ≤ 1 + (1 + η) * (1 + T) ^ 2 := by linarith
  -- Step: sub closeness |r_fp - (1 - sq_fp)| ≤ η · |1 - sq_fp|
  have h_one_toVal : ((1 : FiniteFp).toVal : ℝ) = 1 := FiniteFp.toVal_one
  have h_sub_nr' : isNormalRange (((1 : FiniteFp).toVal : ℝ) - (sq.toVal : ℝ)) ∨
                   (((1 : FiniteFp).toVal : ℝ) - (sq.toVal : ℝ) = 0) := by
    rw [h_one_toVal]; exact h_sub_nr
  have h_sub_close := KahanSum.fpSub_error_or_zero (R := ℝ) (1 : FiniteFp) sq r hsub h_sub_nr'
  rw [h_one_toVal] at h_sub_close
  -- h_sub_close : |r.toVal - (1 - sq.toVal)| ≤ η · |1 - sq.toVal|
  have h_r_close : |r_fp - (1 - sq_fp)| ≤ η * |1 - sq_fp| := h_sub_close
  -- |tanh²(xr) - sq_fp| split:
  -- |tanh²(xr) - sq_fp| ≤ |tanh²(xr) - t_fp²| + |t_fp² - sq_fp|
  -- |tanh² - t²| = |tanh + t| · |tanh - t| ≤ (|tanh| + |t|) · T ≤ (1 + (1+T)) · T = (2+T)·T
  -- |t² - sq| ≤ η · t² ≤ η · (1+T)²
  have h_tanh_sq_to_sq : |Real.tanh xr ^ 2 - sq_fp| ≤ (2 + T) * T + η * (1 + T) ^ 2 := by
    have h_split : Real.tanh xr ^ 2 - sq_fp =
        (Real.tanh xr ^ 2 - t_fp ^ 2) + (t_fp ^ 2 - sq_fp) := by ring
    have h_sq_diff : Real.tanh xr ^ 2 - t_fp ^ 2 =
        (Real.tanh xr + t_fp) * (Real.tanh xr - t_fp) := by ring
    have h_abs_sq_diff : |Real.tanh xr ^ 2 - t_fp ^ 2| ≤ (2 + T) * T := by
      rw [h_sq_diff, abs_mul]
      have h_factor1 : |Real.tanh xr + t_fp| ≤ 2 + T := by
        calc |Real.tanh xr + t_fp|
            ≤ |Real.tanh xr| + |t_fp| := abs_add_le _ _
          _ ≤ 1 + (1 + T) := by linarith
          _ = 2 + T := by ring
      have h_factor2 : |Real.tanh xr - t_fp| ≤ T := by
        rw [abs_sub_comm]; exact h_tanh_close
      have h_factor1_nn : 0 ≤ |Real.tanh xr + t_fp| := abs_nonneg _
      have h_2T_nn : 0 ≤ 2 + T := by linarith
      exact mul_le_mul h_factor1 h_factor2 (abs_nonneg _) h_2T_nn
    have h_abs_t_minus_sq : |t_fp ^ 2 - sq_fp| ≤ η * (1 + T) ^ 2 := by
      rw [show (t_fp ^ 2 - sq_fp) = -(sq_fp - t_fp ^ 2) from by ring, abs_neg]
      calc |sq_fp - t_fp ^ 2|
          ≤ η * t_fp ^ 2 := h_mul_close
        _ ≤ η * (1 + T) ^ 2 := mul_le_mul_of_nonneg_left h_t_fp_sq_abs hη_nn
    calc |Real.tanh xr ^ 2 - sq_fp|
        = |(Real.tanh xr ^ 2 - t_fp ^ 2) + (t_fp ^ 2 - sq_fp)| := by rw [h_split]
      _ ≤ |Real.tanh xr ^ 2 - t_fp ^ 2| + |t_fp ^ 2 - sq_fp| := abs_add_le _ _
      _ ≤ (2 + T) * T + η * (1 + T) ^ 2 := by linarith
  -- Final triangle: |r_fp - (1 - tanh²(xr))| ≤ |r_fp - (1 - sq_fp)| + |sq_fp - tanh²(xr)|
  have h_final_tri : |r_fp - (1 - Real.tanh xr ^ 2)| ≤
      η * (1 + (1 + η) * (1 + T) ^ 2) + ((2 + T) * T + η * (1 + T) ^ 2) := by
    have h_split : r_fp - (1 - Real.tanh xr ^ 2) =
        (r_fp - (1 - sq_fp)) + (Real.tanh xr ^ 2 - sq_fp) := by ring
    calc |r_fp - (1 - Real.tanh xr ^ 2)|
        = |(r_fp - (1 - sq_fp)) + (Real.tanh xr ^ 2 - sq_fp)| := by rw [h_split]
      _ ≤ |r_fp - (1 - sq_fp)| + |Real.tanh xr ^ 2 - sq_fp| := abs_add_le _ _
      _ ≤ η * |1 - sq_fp| + ((2 + T) * T + η * (1 + T) ^ 2) := by linarith
      _ ≤ η * (1 + (1 + η) * (1 + T) ^ 2) + ((2 + T) * T + η * (1 + T) ^ 2) := by
          have := mul_le_mul_of_nonneg_left h_one_minus_sq_abs hη_nn
          linarith
  -- Algebraic combine: η + η(1+η)(1+T)² + (2+T)T + η(1+T)²
  --                  = η + η(1+T)²·[(1+η) + 1] + (2+T)T
  --                  = η + η(2+η)(1+T)² + (2+T)T
  have h_combine : η * (1 + (1 + η) * (1 + T) ^ 2) +
                   ((2 + T) * T + η * (1 + T) ^ 2) =
                   η + η * (2 + η) * (1 + T) ^ 2 + (2 + T) * T := by ring
  rw [h_combine] at h_final_tri
  show |r_fp - (1 - Real.tanh xr ^ 2)| ≤ fpTanhDerivFinite_slack_at xr tx_real
  unfold fpTanhDerivFinite_slack_at
  rw [← hT_def]
  exact h_final_tri

/-! ## Per-input witness bundle and result struct -/

/-- Per-input finite-path witness for the FP tanh derivative pipeline. -/
structure TanhDerivFpWitness (x : FiniteFp) where
  /-- Forward tanh witness. -/
  tanh : TanhFpWitness x
  /-- Rounded `t · t`. -/
  sq : FiniteFp
  /-- Final result `1 − sq`. -/
  r' : FiniteFp
  /-- Mul step witness. -/
  hmul : fpMulFinite tanh.r tanh.r = Fp.finite sq
  /-- Sub step witness. -/
  hsub : fpSubFinite (1 : FiniteFp) sq = Fp.finite r'

/-- Bundle of FP tanh derivative results paired with a uniform slack
witness against `1 − Real.tanh² (xs i .toVal)`. -/
structure TanhDerivResult {n : ℕ} (xs : Fin n → FiniteFp) where
  /-- FP derivative output per index. -/
  result : Fin n → FiniteFp
  /-- Uniform slack against `1 − tanh²(xs i .toVal)`. -/
  slack : ℝ
  /-- Slack is nonneg. -/
  slack_nn : 0 ≤ slack
  /-- Per-index closeness. -/
  h_close : ∀ i, |(((result i).toVal) : ℝ) -
    (1 - Real.tanh ((xs i).toVal : ℝ) ^ 2)| ≤ slack

/-- Bundle constructor for the FP tanh derivative. -/
noncomputable def TanhDerivResult.ofWitnesses {n : ℕ}
    (xs : Fin n → FiniteFp)
    (w : ∀ i, TanhDerivFpWitness (xs i))
    (slack : ℝ) (slack_nn : 0 ≤ slack)
    (h_dbl1_nr : ∀ i, isNormalRange (((xs i).toVal : ℝ) + ((xs i).toVal : ℝ)) ∨
                      (((xs i).toVal : ℝ) + ((xs i).toVal : ℝ) = 0))
    (her_nr : ∀ i, isNormalRange (Real.exp (-(((w i).tanh.tx).toVal : ℝ))))
    (h_d_nr : ∀ i, isNormalRange ((1 : ℝ) + ((w i).tanh.sig.e.toVal : ℝ)) ∨
                   ((1 : ℝ) + ((w i).tanh.sig.e.toVal : ℝ) = 0))
    (h_r_nr : ∀ i, isNormalRange ((1 : ℝ) / ((w i).tanh.sig.d.toVal : ℝ)) ∨
                   ((1 : ℝ) / ((w i).tanh.sig.d.toVal : ℝ) = 0))
    (h_d_m_ne : ∀ i, (w i).tanh.sig.d.m ≠ 0)
    (h_dbl2_nr : ∀ i, isNormalRange (((w i).tanh.sig.r.toVal : ℝ) + ((w i).tanh.sig.r.toVal : ℝ)) ∨
                      (((w i).tanh.sig.r.toVal : ℝ) + ((w i).tanh.sig.r.toVal : ℝ) = 0))
    (h_tanh_sub_nr : ∀ i, isNormalRange (((w i).tanh.tsx.toVal : ℝ) - (1 : ℝ)) ∨
                          (((w i).tanh.tsx.toVal : ℝ) - (1 : ℝ) = 0))
    (h_mul_nr : ∀ i, isNormalRange (((w i).tanh.r.toVal : ℝ) * ((w i).tanh.r.toVal : ℝ)) ∨
                     (((w i).tanh.r.toVal : ℝ) * ((w i).tanh.r.toVal : ℝ) = 0))
    (h_sub_nr : ∀ i, isNormalRange ((1 : ℝ) - ((w i).sq.toVal : ℝ)) ∨
                     ((1 : ℝ) - ((w i).sq.toVal : ℝ) = 0))
    (h_slack : ∀ i, fpTanhDerivFinite_slack_at ((xs i).toVal : ℝ) (((w i).tanh.tx).toVal : ℝ) ≤ slack) :
    TanhDerivResult xs where
  result := fun i => (w i).r'
  slack := slack
  slack_nn := slack_nn
  h_close := fun i => by
    have h := fpTanhDerivFinite_close (xs i)
                (w i).tanh.hdbl1
                (w i).tanh.sig.he (w i).tanh.sig.hd (w i).tanh.sig.hr
                (w i).tanh.hdbl2 (w i).tanh.hsub
                (w i).hmul (w i).hsub
                (h_dbl1_nr i) (her_nr i) (h_d_nr i) (h_r_nr i) (h_d_m_ne i)
                (h_dbl2_nr i) (h_tanh_sub_nr i)
                (h_mul_nr i) (h_sub_nr i)
    have hs := h_slack i
    linarith

end Close

end Flean
