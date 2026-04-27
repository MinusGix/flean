import Flean.Operations.Activations.Sigmoid
import Flean.Operations.Activations.SigmoidFp
import Flean.Operations.Activations.SigmoidFpClose
import Flean.Operations.Mul
import Flean.Operations.Sub

/-!
# Floating-Point Sigmoid Derivative

FP-arithmetic implementation of `σ'(x) = σ(x)·(1 − σ(x))` paired with
the math reference `fun x ↦ Real.sigmoid x * (1 - Real.sigmoid x)`.

## Composition

Building on `fpSigmoidFinite` (from `SigmoidFp.lean`), we add two FP
primitive ops:

```
sigmoid_deriv_fp(x) = fpMul (sigmoid_fp x) (fpSub 1 (sigmoid_fp x))
```

i.e. multiply the forward sigmoid value by `1 − sigmoid_fp x`.

## Result-shape and closeness

* `fpSigmoidDerivFinite_eq_mul_of_finite` — finite-path reduction.
* `fpSigmoidDerivFinite_slack` — slack expression composing the
  forward sigmoid slack with `fpSub` and `fpMul` per-op η errors.
* `fpSigmoidDerivFinite_close` — full closeness lemma against
  `Real.sigmoid x * (1 − Real.sigmoid x)`.

## Why we factor this way

This file does not redefine sigmoid as `Activation ℝ` for σ' (that
would require a separate Lipschitz proof against σ''). The deliverable
shape that Wisp needs is the FP function plus a closeness witness
against the math derivative; both are shipped as standalone theorems
here. Downstream consumers can wrap σ' as an `Activation ℝ` later if
desired (`|σ''| ≤ 1/4` gives Lipschitz K = 1/4).
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RModeExec] [ExpApprox]

/-! ## FP definitions -/

/-- Floating-point sigmoid derivative kernel for finite inputs.

Computes `σ(x)·(1 − σ(x))` via:
1. `sx := fpSigmoidFinite x` (might be NaN/∞ if exp overflows; if so, propagate).
2. `c := fpSubFinite 1 sx`.
3. `r' := fpMulFinite sx c`.

When `sigma_fp x = Fp.finite 0` (the `exp` overflow short-circuit),
`c = 1`, `r' = 0` — matching the math limit `σ'(−∞) = 0`. -/
noncomputable def fpSigmoidDerivFinite (x : FiniteFp) : Fp :=
  match fpSigmoidFinite x with
  | .NaN => .NaN
  | .infinite s => .infinite s
  | .finite sx =>
      match fpSubFinite (1 : FiniteFp) sx with
      | .NaN => .NaN
      | .infinite s => .infinite s
      | .finite c => fpMulFinite sx c

/-- IEEE-style FP sigmoid derivative `Fp → Fp` with full propagation.

* `NaN ↦ NaN`
* `+∞ ↦ Fp.finite 0` (σ'(+∞) = 0)
* `−∞ ↦ Fp.finite 0` (σ'(−∞) = 0)
* finite ↦ `fpSigmoidDerivFinite` -/
noncomputable def fpSigmoidDeriv (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .finite 0
  | .infinite true => .finite 0
  | .finite a => fpSigmoidDerivFinite a

@[simp] theorem fpSigmoidDeriv_finite (a : FiniteFp) :
    fpSigmoidDeriv (Fp.finite a) = fpSigmoidDerivFinite a := rfl

@[simp] theorem fpSigmoidDeriv_nan :
    fpSigmoidDeriv Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpSigmoidDeriv_pos_inf :
    fpSigmoidDeriv (Fp.infinite false) = Fp.finite 0 := rfl

@[simp] theorem fpSigmoidDeriv_neg_inf :
    fpSigmoidDeriv (Fp.infinite true) = Fp.finite 0 := rfl

/-! ## Result-shape -/

/-- Finite-path reduction: when all three intermediate steps land in
finite range, the result is `fpMulFinite sx c`. -/
theorem fpSigmoidDerivFinite_eq_mul_of_finite (x : FiniteFp) {sx c : FiniteFp}
    (hsig : fpSigmoidFinite x = Fp.finite sx)
    (hsub : fpSubFinite (1 : FiniteFp) sx = Fp.finite c) :
    fpSigmoidDerivFinite x = fpMulFinite sx c := by
  unfold fpSigmoidDerivFinite
  rw [hsig]
  simp only
  rw [hsub]

/-- NaN propagation through the forward sigmoid. -/
theorem fpSigmoidDerivFinite_of_sigmoid_nan (x : FiniteFp)
    (h : fpSigmoidFinite x = Fp.NaN) :
    fpSigmoidDerivFinite x = Fp.NaN := by
  unfold fpSigmoidDerivFinite
  rw [h]

/-! ## Closeness lemma -/

section Close

variable [RMode ℝ] [RoundIntSigMSound ℝ] [RModeNearest ℝ] [RModeSticky ℝ]
  [ExpApproxSound]

set_option linter.unusedSectionVars false in
private lemma local_hη_lt_one' : (η : ℝ) < 1 := by
  simp only [FloatFormat.hEps_def]
  have hp := FloatFormat.prec_pos
  have hneg : -(FloatFormat.prec : ℤ) < 0 := by omega
  have h1 : (1 : ℝ) < 2 := by norm_num
  calc (2 : ℝ) ^ (-(FloatFormat.prec : ℤ))
      < (2 : ℝ) ^ (0 : ℤ) := zpow_lt_zpow_right₀ h1 hneg
    _ = 1 := zpow_zero _

/-- Slack expression for `fpSigmoidDerivFinite` against
`Real.sigmoid x · (1 − Real.sigmoid x)`. Composes forward-sigmoid slack
(`σ_slack := fpSigmoidFinite_slack`) with `fpSub` + `fpMul` η-rounding.

Decomposition:
* `η · (2 + η) · (1 + σs)²` — the rounding errors of `fpSub` and `fpMul`,
  amplified by the worst-case magnitude `(1 + σs) · (1 + η)·(1 + σs)`
  of the FP product `s_fp · c_fp`.
* `σs · (2 + σs)` — propagation of the forward sigmoid slack into both
  factors of `σ' = σ · (1 − σ)`. -/
noncomputable def fpSigmoidDerivFinite_slack (xr : ℝ) : ℝ :=
  let σs := fpSigmoidFinite_slack xr
  η * (2 + η) * (1 + σs)^2 + σs * (2 + σs)

theorem fpSigmoidDerivFinite_slack_nn (xr : ℝ) :
    0 ≤ fpSigmoidDerivFinite_slack xr := by
  unfold fpSigmoidDerivFinite_slack
  have hη_nn : (0 : ℝ) ≤ η[ℝ] := by positivity
  have hσs_nn : 0 ≤ fpSigmoidFinite_slack xr := fpSigmoidFinite_slack_nn xr
  have h1 : 0 ≤ (1 + fpSigmoidFinite_slack xr)^2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ 2 + fpSigmoidFinite_slack xr := by linarith
  positivity

/-- **Closeness lemma for the FP sigmoid derivative.**

Given finite-path witnesses for the forward sigmoid (`he, hd, hr`) plus
forward normal-range hypotheses (those needed by
`fpSigmoidFinite_close`), and the additional `fpSub` + `fpMul` step
witnesses + their normal-range conditions, the FP derivative is within
`fpSigmoidDerivFinite_slack` of the math derivative
`Real.sigmoid xr · (1 − Real.sigmoid xr)`. -/
theorem fpSigmoidDerivFinite_close (x : FiniteFp)
    {e d sx : FiniteFp}
    (he : fpExpFinite (-x) = Fp.finite e)
    (hd : fpAddFinite (1 : FiniteFp) e = Fp.finite d)
    (hsig : fpDivFinite (1 : FiniteFp) d = Fp.finite sx)
    {c r' : FiniteFp}
    (hsub : fpSubFinite (1 : FiniteFp) sx = Fp.finite c)
    (hmul : fpMulFinite sx c = Fp.finite r')
    (her_normal : isNormalRange (Real.exp (-(x.toVal : ℝ))))
    (h_d_normal : isNormalRange ((1 : ℝ) + (e.toVal : ℝ)) ∨
                  ((1 : ℝ) + (e.toVal : ℝ) = 0))
    (h_r_normal : isNormalRange ((1 : ℝ) / (d.toVal : ℝ)) ∨
                  ((1 : ℝ) / (d.toVal : ℝ) = 0))
    (hd_m_ne : d.m ≠ 0)
    (h_sub_normal : isNormalRange ((1 : ℝ) - (sx.toVal : ℝ)) ∨
                    ((1 : ℝ) - (sx.toVal : ℝ) = 0))
    (h_mul_normal : isNormalRange ((sx.toVal : ℝ) * (c.toVal : ℝ)) ∨
                    ((sx.toVal : ℝ) * (c.toVal : ℝ) = 0)) :
    |((r'.toVal : ℝ)) - Real.sigmoid (x.toVal : ℝ) *
        (1 - Real.sigmoid (x.toVal : ℝ))| ≤
      fpSigmoidDerivFinite_slack (x.toVal : ℝ) := by
  -- Setup
  set xr : ℝ := (x.toVal : ℝ) with hxr_def
  set sr : ℝ := Real.sigmoid xr with hsr_def
  set s_fp : ℝ := (sx.toVal : ℝ) with hs_fp_def
  set c_fp : ℝ := (c.toVal : ℝ) with hc_fp_def
  set p_fp : ℝ := (r'.toVal : ℝ) with hp_fp_def
  set σs : ℝ := fpSigmoidFinite_slack xr with hσs_def
  -- η bounds
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hη_lt : (η : ℝ) < 1 := local_hη_lt_one'
  have hσs_nn : 0 ≤ σs := fpSigmoidFinite_slack_nn xr
  -- Real-side facts
  have hsr_pos : 0 < sr := Real.sigmoid_pos xr
  have hsr_le_one : sr ≤ 1 := Real.sigmoid_le_one xr
  have hone_minus_sr_nn : 0 ≤ 1 - sr := by linarith
  have hone_minus_sr_le_one : 1 - sr ≤ 1 := by linarith
  -- Forward sigmoid closeness: |s_fp - sr| ≤ σs.
  have h_sig_close : |s_fp - sr| ≤ σs := by
    have h := fpSigmoidFinite_close x he hd hsig her_normal h_d_normal h_r_normal hd_m_ne
    rw [← hxr_def, ← hsr_def, ← hσs_def] at h
    have hexpand : fpSigmoidFinite x = Fp.finite sx := by
      rw [fpSigmoidFinite_eq_div_of_finite x he hd]; exact hsig
    -- The closeness lemma gives `|sx.toVal - Real.sigmoid xr| ≤ σs` modulo `Fp.finite r := sx`
    -- via `fpSigmoidFinite_eq_div_of_finite`. Rewrite: in `h`, `r` was `sx`.
    -- Actually `fpSigmoidFinite_close` was stated with arbitrary `r`; here `r := sx`.
    exact h
  -- Bounds on s_fp and 1 - s_fp
  have h_diff_le := abs_le.mp h_sig_close
  have h_s_fp_lo : sr - σs ≤ s_fp := by linarith [h_diff_le.1]
  have h_s_fp_hi : s_fp ≤ sr + σs := by linarith [h_diff_le.2]
  have h_s_fp_nn : -σs ≤ s_fp := by linarith [h_s_fp_lo]
  have h_s_fp_le : s_fp ≤ 1 + σs := by linarith [h_s_fp_hi]
  have h_abs_s_fp : |s_fp| ≤ 1 + σs := by
    rw [abs_le]; constructor <;> linarith
  have h_one_minus_s_fp_lo : -σs ≤ 1 - s_fp := by linarith [h_s_fp_le]
  have h_one_minus_s_fp_hi : 1 - s_fp ≤ 1 + σs := by linarith [h_s_fp_lo]
  have h_abs_one_minus_s_fp : |1 - s_fp| ≤ 1 + σs := by
    rw [abs_le]; constructor <;> linarith
  -- fpSub closeness: |c_fp - (1 - s_fp)| ≤ η · |1 - s_fp|
  have h_one_toVal : ((1 : FiniteFp).toVal : ℝ) = 1 := FiniteFp.toVal_one
  have h_sub_normal' : isNormalRange (((1 : FiniteFp).toVal : ℝ) - (sx.toVal : ℝ)) ∨
                       (((1 : FiniteFp).toVal : ℝ) - (sx.toVal : ℝ) = 0) := by
    rw [h_one_toVal]; exact h_sub_normal
  have h_sub_close_raw := KahanSum.fpSub_error_or_zero (R := ℝ) (1 : FiniteFp) sx c hsub h_sub_normal'
  rw [h_one_toVal] at h_sub_close_raw
  have h_sub_close : |c_fp - (1 - s_fp)| ≤ η * |1 - s_fp| := h_sub_close_raw
  have h_sub_close' : |c_fp - (1 - s_fp)| ≤ η * (1 + σs) := by
    calc |c_fp - (1 - s_fp)|
        ≤ η * |1 - s_fp| := h_sub_close
      _ ≤ η * (1 + σs) := mul_le_mul_of_nonneg_left h_abs_one_minus_s_fp hη_nn
  -- Bound on c_fp
  have h_c_diff_le := abs_le.mp h_sub_close'
  have h_c_fp_lo : (1 - s_fp) - η * (1 + σs) ≤ c_fp := by linarith [h_c_diff_le.1]
  have h_c_fp_hi : c_fp ≤ (1 - s_fp) + η * (1 + σs) := by linarith [h_c_diff_le.2]
  have h_abs_c_fp : |c_fp| ≤ (1 + σs) + η * (1 + σs) := by
    rw [abs_le]; constructor
    · linarith [h_c_fp_lo, h_one_minus_s_fp_lo]
    · linarith [h_c_fp_hi, h_one_minus_s_fp_hi]
  have h_abs_c_fp' : |c_fp| ≤ (1 + η) * (1 + σs) := by
    have : (1 + σs) + η * (1 + σs) = (1 + η) * (1 + σs) := by ring
    linarith [h_abs_c_fp]
  -- fpMul closeness: |p_fp - s_fp · c_fp| ≤ η · |s_fp · c_fp|
  have h_mul_close_raw := KahanSum.fpMul_error_or_zero (R := ℝ) sx c r' hmul h_mul_normal
  -- h_mul_close_raw : |r'.toVal - sx.toVal * c.toVal| ≤ η * |sx.toVal * c.toVal|
  have h_mul_close : |p_fp - s_fp * c_fp| ≤ η * |s_fp * c_fp| := h_mul_close_raw
  have h_abs_mul : |s_fp * c_fp| ≤ (1 + σs) * ((1 + η) * (1 + σs)) := by
    rw [abs_mul]
    exact mul_le_mul h_abs_s_fp h_abs_c_fp' (abs_nonneg _) (by linarith [hσs_nn])
  have h_mul_close' : |p_fp - s_fp * c_fp| ≤ η * ((1 + σs) * ((1 + η) * (1 + σs))) :=
    le_trans h_mul_close (mul_le_mul_of_nonneg_left h_abs_mul hη_nn)
  -- Now bound |s_fp · c_fp - sr · (1 - sr)|.
  -- s_fp · c_fp - sr · (1 - sr)
  --  = s_fp · (c_fp - (1 - sr)) + (s_fp - sr) · (1 - sr)
  -- |s_fp · (c_fp - (1 - sr))| ≤ |s_fp| · (|c_fp - (1 - s_fp)| + |s_fp - sr|)
  --                            ≤ (1 + σs) · (η · (1 + σs) + σs)
  -- |(s_fp - sr) · (1 - sr)| ≤ σs · 1 = σs
  have h_c_to_real : |c_fp - (1 - sr)| ≤ η * (1 + σs) + σs := by
    have h_split : c_fp - (1 - sr) = (c_fp - (1 - s_fp)) - (s_fp - sr) := by ring
    rw [h_split, sub_eq_add_neg]
    calc |(c_fp - (1 - s_fp)) + -(s_fp - sr)|
        ≤ |c_fp - (1 - s_fp)| + |-(s_fp - sr)| := abs_add_le _ _
      _ = |c_fp - (1 - s_fp)| + |s_fp - sr| := by rw [abs_neg]
      _ ≤ η * (1 + σs) + σs := by linarith [h_sub_close', h_sig_close]
  have h_inner1 : |s_fp * (c_fp - (1 - sr))| ≤ (1 + σs) * (η * (1 + σs) + σs) := by
    rw [abs_mul]
    exact mul_le_mul h_abs_s_fp h_c_to_real (abs_nonneg _) (by linarith [hσs_nn])
  have h_inner2 : |(s_fp - sr) * (1 - sr)| ≤ σs * 1 := by
    rw [abs_mul, abs_of_nonneg hone_minus_sr_nn]
    exact mul_le_mul h_sig_close hone_minus_sr_le_one hone_minus_sr_nn hσs_nn
  have h_sc_minus_p_real : |s_fp * c_fp - sr * (1 - sr)| ≤
      (1 + σs) * (η * (1 + σs) + σs) + σs := by
    have h_split : s_fp * c_fp - sr * (1 - sr) =
        s_fp * (c_fp - (1 - sr)) + (s_fp - sr) * (1 - sr) := by ring
    rw [h_split]
    calc |s_fp * (c_fp - (1 - sr)) + (s_fp - sr) * (1 - sr)|
        ≤ |s_fp * (c_fp - (1 - sr))| + |(s_fp - sr) * (1 - sr)| := abs_add_le _ _
      _ ≤ (1 + σs) * (η * (1 + σs) + σs) + σs * 1 := by linarith
      _ = (1 + σs) * (η * (1 + σs) + σs) + σs := by ring
  -- Triangle on |p_fp - sr · (1 - sr)|.
  have h_tri : |p_fp - sr * (1 - sr)| ≤
      η * ((1 + σs) * ((1 + η) * (1 + σs))) +
      ((1 + σs) * (η * (1 + σs) + σs) + σs) := by
    have h_split : p_fp - sr * (1 - sr) = (p_fp - s_fp * c_fp) + (s_fp * c_fp - sr * (1 - sr)) := by
      ring
    rw [h_split]
    calc |(p_fp - s_fp * c_fp) + (s_fp * c_fp - sr * (1 - sr))|
        ≤ |p_fp - s_fp * c_fp| + |s_fp * c_fp - sr * (1 - sr)| := abs_add_le _ _
      _ ≤ η * ((1 + σs) * ((1 + η) * (1 + σs))) + ((1 + σs) * (η * (1 + σs) + σs) + σs) := by
          linarith
  -- Algebraic step: show the natural composed bound equals the slack.
  -- η · (1+σs)² · (1+η) + (1+σs) · (η · (1+σs) + σs) + σs
  --   = η · (2+η) · (1+σs)² + σs · (2+σs)
  -- which matches `fpSigmoidDerivFinite_slack xr`.
  have h_eq : η * ((1 + σs) * ((1 + η) * (1 + σs))) +
              ((1 + σs) * (η * (1 + σs) + σs) + σs) =
              η * (2 + η) * (1 + σs) ^ 2 + σs * (2 + σs) := by ring
  rw [h_eq] at h_tri
  -- Translate `Real.sigmoid xr * (1 - Real.sigmoid xr)` to `sr * (1 - sr)` form,
  -- and unfold the `let σs := ...` in the slack definition.
  show |p_fp - Real.sigmoid xr * (1 - Real.sigmoid xr)| ≤
       fpSigmoidDerivFinite_slack xr
  rw [← hsr_def]
  unfold fpSigmoidDerivFinite_slack
  show |p_fp - sr * (1 - sr)| ≤
       η * (2 + η) * (1 + fpSigmoidFinite_slack xr) ^ 2 +
       fpSigmoidFinite_slack xr * (2 + fpSigmoidFinite_slack xr)
  rw [← hσs_def]
  exact h_tri

/-! ## Per-input witness bundle and result struct

Mirrors `SigmoidFpWitness` / `MLP.ActivationFpResult.ofSigmoidWitnesses`
from `SigmoidFpClose.lean`. We don't reuse `MLP.ActivationFpResult`
directly here because that requires `Activation ℝ` for the derivative
function (which would need its own Lipschitz proof against `σ''`); the
deliverable Wisp needs is a `(result, slack, h_close)` bundle, which
`SigmoidDerivResult` gives directly. -/

/-- Per-input finite-path witness for the FP sigmoid derivative pipeline.
Extends `SigmoidFpWitness` with the additional `fpSub` + `fpMul` step
witnesses. -/
structure SigmoidDerivFpWitness (x : FiniteFp) where
  /-- Forward sigmoid witness (provides `e, d, sx` and their finite-path proofs). -/
  sig : SigmoidFpWitness x
  /-- Rounded `1 − sx`. -/
  c : FiniteFp
  /-- Rounded `sx · (1 − sx)`, the FP derivative result. -/
  r' : FiniteFp
  /-- sub step landed in finite range. -/
  hsub : fpSubFinite (1 : FiniteFp) sig.r = Fp.finite c
  /-- mul step landed in finite range. -/
  hmul : fpMulFinite sig.r c = Fp.finite r'

/-- Bundle of per-index FP sigmoid derivative results plus a uniform
slack witness against `σ'(xs i .toVal)`.

Parallels `MLP.ActivationFpResult` for the math sigmoid; we don't lift to
that struct because doing so would require packaging
`fun x ↦ Real.sigmoid x * (1 - Real.sigmoid x)` as a `Flean.Activation ℝ`
with its own Lipschitz proof. Downstream consumers that want this lift
can construct the `Activation ℝ` separately and re-package. -/
structure SigmoidDerivResult {n : ℕ} (xs : Fin n → FiniteFp) where
  /-- FP derivative output per index. -/
  result : Fin n → FiniteFp
  /-- Uniform slack against `σ'(xs i .toVal)`. -/
  slack : ℝ
  /-- Slack is nonneg. -/
  slack_nn : 0 ≤ slack
  /-- Per-index closeness against the math derivative. -/
  h_close : ∀ i, |(((result i).toVal) : ℝ) -
    (Real.sigmoid ((xs i).toVal : ℝ) *
     (1 - Real.sigmoid ((xs i).toVal : ℝ)))| ≤ slack

/-- Bundle constructor for the FP sigmoid derivative: given per-input
witnesses + uniform slack bound, produce a `SigmoidDerivResult`. -/
noncomputable def SigmoidDerivResult.ofWitnesses {n : ℕ}
    (xs : Fin n → FiniteFp)
    (w : ∀ i, SigmoidDerivFpWitness (xs i))
    (slack : ℝ) (slack_nn : 0 ≤ slack)
    (her_nr : ∀ i, isNormalRange (Real.exp (-((xs i).toVal : ℝ))))
    (h_d_nr : ∀ i, isNormalRange ((1 : ℝ) + ((w i).sig.e.toVal : ℝ)) ∨
                   ((1 : ℝ) + ((w i).sig.e.toVal : ℝ) = 0))
    (h_r_nr : ∀ i, isNormalRange ((1 : ℝ) / ((w i).sig.d.toVal : ℝ)) ∨
                   ((1 : ℝ) / ((w i).sig.d.toVal : ℝ) = 0))
    (h_d_m_ne : ∀ i, (w i).sig.d.m ≠ 0)
    (h_sub_nr : ∀ i, isNormalRange ((1 : ℝ) - ((w i).sig.r.toVal : ℝ)) ∨
                     ((1 : ℝ) - ((w i).sig.r.toVal : ℝ) = 0))
    (h_mul_nr : ∀ i, isNormalRange (((w i).sig.r.toVal : ℝ) * ((w i).c.toVal : ℝ)) ∨
                     (((w i).sig.r.toVal : ℝ) * ((w i).c.toVal : ℝ) = 0))
    (h_slack : ∀ i, fpSigmoidDerivFinite_slack ((xs i).toVal : ℝ) ≤ slack) :
    SigmoidDerivResult xs where
  result := fun i => (w i).r'
  slack := slack
  slack_nn := slack_nn
  h_close := fun i => by
    have h := fpSigmoidDerivFinite_close (xs i)
                (w i).sig.he (w i).sig.hd (w i).sig.hr
                (w i).hsub (w i).hmul
                (her_nr i) (h_d_nr i) (h_r_nr i) (h_d_m_ne i)
                (h_sub_nr i) (h_mul_nr i)
    have hs := h_slack i
    linarith

end Close

end Flean
