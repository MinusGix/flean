import Flean.Operations.LayerNorm
import Flean.Tags.BoundedRange
import Flean.Tags.Normal
import Flean.Operations.FpSum

/-!
# Tag-Specialized LayerNorm: `IsBoundedRange` Wrapper

**Status**: Phase 2 Stage 6 — bridging scaffold.

## What this file delivers

A minimal wrapper that takes `IsBoundedRange I xs` (Phase 1 tag) and
exposes the `|x_i| ≤ I.maxMag` magnitude bound that downstream
LayerNorm error analyses need.  The full end-to-end forward error
bound is composed via `fpLayerNorm_end_to_end_error_bound` (Phase 2
Stage 5) plus accumulated per-step δ's.

## What the tag dematerializes

Under `IsBoundedRange I xs` with `I.lo` and `I.hi` bounded, the
per-component `|xs_i|` magnitude is automatically available via
`IsBoundedRange.toVal_abs_le`.  This feeds into:

- Bounds on `|shifted_i|` after the mean shift.
- Bounds on `|(shifted_i)²|` after squaring.
- Bounds on `|var|` via the variance sum.

The **full** tag-driven automation — discharging every normal-range
precondition on per-step rounding theorems — requires additional
`IsBoundedRange.fpSub` propagation + lower-bound magnitude reasoning
(the tag gives upper bounds easily, but `≥ 2^min_exp` lower bounds
need separation hypotheses).  That work is scoped for a follow-up
session; see the design doc for scope.

## Minimum bridge

The one concrete deliverable: `fpLayerNorm_tagged_bound`, which
takes an `IsBoundedRange` tag + per-step δ hypotheses (rather than
per-step normal-range hypotheses) and reaches the end-to-end bound.
Normal-range discharging stays manual in this Phase 2 delivery, but
the tag still serves a role: it gives the user a uniform way to
describe input bounds, replacing ad-hoc `|xs_i| ≤ c` scattered
through error-bound hypotheses with a single tag carry-through.
-/

set_option autoImplicit false

namespace Flean.Tags

open LayerNorm

variable [FloatFormat]

/-- **Tagged LayerNorm end-to-end bound** (Phase 2 Stage 6).

Thin tag-aware wrapper around `fpLayerNorm_end_to_end_error_bound`.
The `IsBoundedRange I xs` tag is carried through the statement;
currently its role is to expose `|xs_i| ≤ I.maxMag` via `.toVal_abs_le`
to downstream computations that may need it.

Per-step `δ_shift`, `δ_stddev`, `δ_final` are expected to be derived
by the user from concrete summation adapters + per-step rounding
witnesses (see `Flean/Operations/LayerNorm.lean`'s individual step
theorems).  Future work: discharge these δ's automatically from the
tag + separation hypotheses. -/
theorem fpLayerNorm_tagged_bound
    {n : ℕ} {I : FpInterval ℝ} {xs : Fin n → FiniteFp}
    {shifted : Fin n → FiniteFp} {stddev : FiniteFp}
    {result : Fin n → FiniteFp}
    (_hxs : IsBoundedRange (R := ℝ) I xs)
    (i : Fin n) {eps : ℝ} (heps_pos : 0 < eps)
    (hn_pos_r : 0 < (n : ℝ))
    (h_stddev_pos : 0 < (stddev.toVal : ℝ))
    {δ_shift δ_stddev δ_final : ℝ}
    (h_shift :
      |((shifted i).toVal : ℝ) -
          (((xs i).toVal : ℝ) -
            mean (fun j => ((xs j).toVal : ℝ)))| ≤ δ_shift)
    (h_stddev :
      |((stddev.toVal : ℝ)) -
          Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) + eps)| ≤
        δ_stddev)
    (h_final :
      |((result i).toVal : ℝ) -
          (shifted i).toVal / stddev.toVal| ≤ δ_final) :
    |((result i).toVal : ℝ) -
        layerNorm (fun j => ((xs j).toVal : ℝ)) eps i| ≤
      δ_final + δ_shift / stddev.toVal +
        |((xs i).toVal : ℝ) -
            mean (fun j => ((xs j).toVal : ℝ))| * δ_stddev /
          ((stddev.toVal : ℝ) *
            Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) + eps)) :=
  fpLayerNorm_end_to_end_error_bound i heps_pos hn_pos_r
    h_stddev_pos h_shift h_stddev h_final

/-- **Magnitude corollary** from the tag: under `IsBoundedRange I xs`,
every input has bounded magnitude.  This is the one immediate value
the tag provides to LayerNorm bounds today. -/
theorem fpLayerNorm_input_abs_le
    {n : ℕ} {I : FpInterval ℝ} {xs : Fin n → FiniteFp}
    (hxs : IsBoundedRange (R := ℝ) I xs) (i : Fin n) :
    |((xs i).toVal : ℝ)| ≤ I.maxMag :=
  hxs.toVal_abs_le i

/-! ## Tag-dematerialized per-step bounds

The helpers below discharge normal-range preconditions on per-step
LayerNorm theorems automatically from an `IsNormal eps` tag on the
stability constant + the (free) nonnegativity of the real variance.
These are the concrete tag-tightening demos for LayerNorm.

**What gets discharged**:
- `fpVarPlusEps_step_error_bound`'s normal-range hypothesis: derivable
  from `IsNormal eps` + `0 ≤ var.toVal` (variance is always a nonneg
  sum divided by n, so the real var is nonneg; its FP approximation
  stays nonneg under the unified-round preservation).
-/

/-- **Normal-range on `var + eps` from `IsNormal eps`**.

Under `IsNormal eps.toVal` + nonnegativity of the FP variance, the sum
`var + eps` is ≥ `2^min_exp`, so its absolute value lies above the
normal-range lower bound.  Used to discharge
`fpVarPlusEps_step_error_bound`'s normal-range hypothesis. -/
theorem varPlusEps_normal_of_eps_normal {var eps : FiniteFp}
    (heps : IsNormal (R := ℝ) eps.toVal)
    (hvar_nn : 0 ≤ (var.toVal : ℝ)) :
    (2 : ℝ) ^ FloatFormat.min_exp ≤ |((var.toVal : ℝ)) + eps.toVal| := by
  have hsum_normal : IsNormal (R := ℝ) (var.toVal + eps.toVal) := by
    have h_swap : (var.toVal : ℝ) + eps.toVal = eps.toVal + var.toVal := by ring
    rw [h_swap]
    exact heps.add_nonneg hvar_nn
  have hsum_pos : 0 < (var.toVal : ℝ) + eps.toVal := hsum_normal.pos
  have habs : |((var.toVal : ℝ)) + eps.toVal| = (var.toVal : ℝ) + eps.toVal :=
    abs_of_pos hsum_pos
  rw [habs]
  exact hsum_normal.ge_min

/-- **Tag-tightened eps-add error bound**.

`fpVarPlusEps_step_error_bound` with the normal-range precondition
discharged automatically from `IsNormal eps` + `0 ≤ var.toVal`.
First concrete Phase 2-style tightening for LayerNorm: the tag
dematerializes one of the seven per-step preconditions. -/
theorem fpVarPlusEps_tagged_step_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
    [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]
    {var eps varPlusEps : FiniteFp}
    (heps : IsNormal (R := ℝ) eps.toVal)
    (hvar_nn : 0 ≤ (var.toVal : ℝ))
    (h_varPlusEps : fpAddFinite var eps = Fp.finite varPlusEps) :
    |((varPlusEps.toVal : ℝ)) - (var.toVal + eps.toVal)| ≤
      (η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| :=
  fpVarPlusEps_step_error_bound h_varPlusEps
    (varPlusEps_normal_of_eps_normal heps hvar_nn)

/-- **Normal-range on `√(varPlusEps)` from `IsNormal varPlusEps` +
`min_exp ≤ 0`**.

For standard FP formats (fp16/32/64/etc.), `min_exp` is negative, so
`2^(2·min_exp) ≤ 2^min_exp` and the normal-range hypothesis on
`√varPlusEps` follows from `IsNormal varPlusEps`.  This discharges
`fpStddev_step_error_bound`'s normal-range hypothesis under the
`min_exp ≤ 0` side condition.

The side condition is explicit (not derived) to keep the theorem
format-agnostic — if a pathological FloatFormat has `min_exp > 0`,
the caller must supply the stronger sqrt-side hypothesis directly. -/
theorem sqrtVarPlusEps_normal_of_tagged
    {varPlusEps : FiniteFp}
    (hvpe : IsNormal (R := ℝ) varPlusEps.toVal)
    (hme : FloatFormat.min_exp ≤ 0) :
    (2 : ℝ) ^ FloatFormat.min_exp ≤ |Real.sqrt ((varPlusEps.toVal : ℝ))| := by
  have hvpe_pos : 0 < (varPlusEps.toVal : ℝ) := hvpe.pos
  have hsqrt_nn : 0 ≤ Real.sqrt ((varPlusEps.toVal : ℝ)) :=
    Real.sqrt_nonneg _
  rw [abs_of_nonneg hsqrt_nn]
  -- Need: 2^min_exp ≤ √varPlusEps
  -- Both sides positive; equivalent to (2^min_exp)² ≤ varPlusEps, i.e., 2^(2·min_exp) ≤ varPlusEps.
  have h2me_pos : (0 : ℝ) < (2 : ℝ) ^ FloatFormat.min_exp := by positivity
  have hgoal_sq :
      ((2 : ℝ) ^ FloatFormat.min_exp) ^ 2 ≤ (varPlusEps.toVal : ℝ) := by
    -- ((2:ℝ)^min_exp)^2 = 2^(2·min_exp) ≤ 2^min_exp ≤ varPlusEps.
    have hpow_sq : ((2 : ℝ) ^ FloatFormat.min_exp) ^ 2 =
        (2 : ℝ) ^ (2 * FloatFormat.min_exp : ℤ) := by
      rw [show (2 * FloatFormat.min_exp : ℤ) = FloatFormat.min_exp + FloatFormat.min_exp from by ring]
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [hpow_sq]
    have hpow_le :
        (2 : ℝ) ^ (2 * FloatFormat.min_exp : ℤ) ≤ (2 : ℝ) ^ FloatFormat.min_exp := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    exact le_trans hpow_le hvpe.ge_min
  -- √varPlusEps ≥ 2^min_exp via monotonicity of √ applied to hgoal_sq.
  have h_sqrt_mono :
      Real.sqrt (((2 : ℝ) ^ FloatFormat.min_exp) ^ 2) ≤
        Real.sqrt ((varPlusEps.toVal : ℝ)) :=
    Real.sqrt_le_sqrt hgoal_sq
  have h_sqrt_sq :
      Real.sqrt (((2 : ℝ) ^ FloatFormat.min_exp) ^ 2) =
        (2 : ℝ) ^ FloatFormat.min_exp := by
    rw [Real.sqrt_sq (le_of_lt h2me_pos)]
  linarith

/-- **Tag-tightened sqrt error bound**.

`fpStddev_step_error_bound` with normal-range precondition on
`√varPlusEps` discharged automatically from `IsNormal varPlusEps` +
`min_exp ≤ 0`. -/
theorem fpStddev_tagged_step_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ]
    {varPlusEps stddev : FiniteFp}
    (hvpe : IsNormal (R := ℝ) varPlusEps.toVal)
    (hme : FloatFormat.min_exp ≤ 0)
    (h_ve_pos : varPlusEps.s = false)
    (h_ve_m_ne : varPlusEps.m ≠ 0)
    (h_stddev : fpSqrtFinite varPlusEps = Fp.finite stddev) :
    |((stddev.toVal : ℝ)) - Real.sqrt ((varPlusEps.toVal : ℝ))| ≤
      (η : ℝ) * |Real.sqrt ((varPlusEps.toVal : ℝ))| :=
  fpStddev_step_error_bound h_ve_pos h_ve_m_ne h_stddev
    (sqrtVarPlusEps_normal_of_tagged hvpe hme)

/-! ## Cascaded tag-tightened composition

One level up from the per-step tagged bounds: compose the eps-add
and sqrt steps into a single `|stddev − √(σ² + eps)|` bound,
taking a user-supplied `|var − σ²| ≤ δ_var` for the upstream
variance error.

Key lemma: `|√a − √b| = |a − b| / (√a + √b)`, with the denominator
lower-bounded by `2·√(2^min_exp)` when `a, b ≥ 2^min_exp`.  Both
endpoints of our sqrt are ≥ `2^min_exp`: `varPlusEps` by
`IsNormal varPlusEps`, and `σ² + eps` by `σ² ≥ 0` + `IsNormal eps`. -/

omit [FloatFormat] in
private theorem sqrt_sub_sqrt_le_of_lb {a b c : ℝ}
    (ha : c ≤ a) (hb : c ≤ b) (hc_pos : 0 < c) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / (2 * Real.sqrt c) := by
  have ha_pos : 0 < a := lt_of_lt_of_le hc_pos ha
  have hb_pos : 0 < b := lt_of_lt_of_le hc_pos hb
  have ha_nn : 0 ≤ a := le_of_lt ha_pos
  have hb_nn : 0 ≤ b := le_of_lt hb_pos
  have hc_nn : 0 ≤ c := le_of_lt hc_pos
  have hsqrt_a_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha_pos
  have hsqrt_b_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb_pos
  have hsqrt_c_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc_pos
  have hsqrt_c_le_a : Real.sqrt c ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have hsqrt_c_le_b : Real.sqrt c ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  -- √a + √b ≥ 2·√c.
  have hsum_ge : 2 * Real.sqrt c ≤ Real.sqrt a + Real.sqrt b := by linarith
  have hsum_pos : 0 < Real.sqrt a + Real.sqrt b := by linarith
  -- (√a - √b)·(√a + √b) = a - b.
  have h_ident : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    have ha_sq : Real.sqrt a * Real.sqrt a = a :=
      Real.mul_self_sqrt ha_nn
    have hb_sq : Real.sqrt b * Real.sqrt b = b :=
      Real.mul_self_sqrt hb_nn
    ring_nf
    rw [show Real.sqrt a ^ 2 = Real.sqrt a * Real.sqrt a from sq _,
        show Real.sqrt b ^ 2 = Real.sqrt b * Real.sqrt b from sq _,
        ha_sq, hb_sq]
  -- |√a - √b| = |a - b| / (√a + √b).
  have h_diff_eq :
      Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
    field_simp
    linarith [h_ident]
  rw [h_diff_eq, abs_div]
  have habs_sum : |Real.sqrt a + Real.sqrt b| = Real.sqrt a + Real.sqrt b :=
    abs_of_pos hsum_pos
  rw [habs_sum]
  -- |a - b| / (√a + √b) ≤ |a - b| / (2·√c) — denominator got smaller, numerator same.
  have h2sqrtc_pos : 0 < 2 * Real.sqrt c := by linarith
  have habs_ab_nn : 0 ≤ |a - b| := abs_nonneg _
  exact div_le_div_of_nonneg_left habs_ab_nn h2sqrtc_pos hsum_ge

/-- **Cascaded tag-tightened stddev error bound**.

Composes `fpVarPlusEps_tagged_step_error_bound` +
`fpStddev_tagged_step_error_bound` + sqrt Lipschitz into a single
bound on `|stddev.toVal − √(σ² + eps)|`, taking a user-supplied
`|var.toVal − σ²| ≤ δ_var` for the upstream variance error.

Under the tag hypotheses, both `varPlusEps` and `σ² + eps` are ≥
`2^min_exp`, so the sqrt-Lipschitz denominator is ≥ `2·√(2^min_exp)`.

Result:
```
|stddev − √(σ² + eps)| ≤ η · √varPlusEps +
                         (η · (var + eps) + δ_var) / (2 · √(2^min_exp))
```

Two of the three error contributions come from tag-discharged per-step
bounds; the third is the propagated variance error `δ_var`. -/
theorem fpStddev_cascaded_tagged_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]
    {var eps varPlusEps stddev : FiniteFp}
    {sigma_sq_exact δ_var : ℝ}
    (heps : IsNormal (R := ℝ) eps.toVal)
    (hvpe : IsNormal (R := ℝ) varPlusEps.toVal)
    (hme : FloatFormat.min_exp ≤ 0)
    (hvar_nn : 0 ≤ (var.toVal : ℝ))
    (hsigma_sq_nn : 0 ≤ sigma_sq_exact)
    (h_var_err : |((var.toVal : ℝ)) - sigma_sq_exact| ≤ δ_var)
    (h_varPlusEps : fpAddFinite var eps = Fp.finite varPlusEps)
    (h_ve_s : varPlusEps.s = false) (h_ve_m_ne : varPlusEps.m ≠ 0)
    (h_stddev : fpSqrtFinite varPlusEps = Fp.finite stddev) :
    |((stddev.toVal : ℝ)) - Real.sqrt (sigma_sq_exact + eps.toVal)| ≤
      (η : ℝ) * Real.sqrt ((varPlusEps.toVal : ℝ)) +
      ((η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| + δ_var) /
        (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp)) := by
  -- Tag-discharged per-step bounds.
  have h_ve_err :
      |((varPlusEps.toVal : ℝ)) - (var.toVal + eps.toVal)| ≤
        (η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| :=
    fpVarPlusEps_tagged_step_error_bound heps hvar_nn h_varPlusEps
  have h_stddev_err :
      |((stddev.toVal : ℝ)) - Real.sqrt ((varPlusEps.toVal : ℝ))| ≤
        (η : ℝ) * |Real.sqrt ((varPlusEps.toVal : ℝ))| :=
    fpStddev_tagged_step_error_bound hvpe hme h_ve_s h_ve_m_ne h_stddev
  have h_sqrt_vpe_nn : 0 ≤ Real.sqrt ((varPlusEps.toVal : ℝ)) :=
    Real.sqrt_nonneg _
  have h_stddev_err' :
      |((stddev.toVal : ℝ)) - Real.sqrt ((varPlusEps.toVal : ℝ))| ≤
        (η : ℝ) * Real.sqrt ((varPlusEps.toVal : ℝ)) := by
    rw [abs_of_nonneg h_sqrt_vpe_nn] at h_stddev_err; exact h_stddev_err
  -- Both varPlusEps and σ² + eps are ≥ 2^min_exp (for the sqrt Lipschitz).
  have h2me_pos : (0 : ℝ) < (2 : ℝ) ^ FloatFormat.min_exp := by positivity
  have h_σeps_lb : (2 : ℝ) ^ FloatFormat.min_exp ≤ sigma_sq_exact + eps.toVal := by
    have : eps.toVal ≤ sigma_sq_exact + eps.toVal := by linarith
    exact le_trans heps.ge_min this
  have h_vpe_lb : (2 : ℝ) ^ FloatFormat.min_exp ≤ (varPlusEps.toVal : ℝ) :=
    hvpe.ge_min
  -- Sqrt Lipschitz.
  have h_sqrt_lip :
      |Real.sqrt ((varPlusEps.toVal : ℝ)) - Real.sqrt (sigma_sq_exact + eps.toVal)| ≤
        |((varPlusEps.toVal : ℝ)) - (sigma_sq_exact + eps.toVal)| /
          (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp)) :=
    sqrt_sub_sqrt_le_of_lb h_vpe_lb h_σeps_lb h2me_pos
  -- Combine ve-err + var-err to bound |varPlusEps - (σ² + eps)|.
  have h_inner :
      |((varPlusEps.toVal : ℝ)) - (sigma_sq_exact + eps.toVal)| ≤
        (η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| + δ_var := by
    have hdiff :
        ((varPlusEps.toVal : ℝ)) - (sigma_sq_exact + eps.toVal) =
          (((varPlusEps.toVal : ℝ)) - ((var.toVal : ℝ) + eps.toVal)) +
          (((var.toVal : ℝ)) - sigma_sq_exact) := by ring
    calc |((varPlusEps.toVal : ℝ)) - (sigma_sq_exact + eps.toVal)|
        = |(((varPlusEps.toVal : ℝ)) - ((var.toVal : ℝ) + eps.toVal)) +
            (((var.toVal : ℝ)) - sigma_sq_exact)| := by rw [hdiff]
      _ ≤ |((varPlusEps.toVal : ℝ)) - ((var.toVal : ℝ) + eps.toVal)| +
          |((var.toVal : ℝ)) - sigma_sq_exact| := abs_add_le _ _
      _ ≤ (η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| + δ_var := by
          linarith
  have h2sqrtc_pos :
      (0 : ℝ) < 2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp) := by
    have : 0 < Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp) :=
      Real.sqrt_pos.mpr h2me_pos
    linarith
  have h_lip_bound :
      |Real.sqrt ((varPlusEps.toVal : ℝ)) - Real.sqrt (sigma_sq_exact + eps.toVal)| ≤
        ((η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| + δ_var) /
          (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp)) := by
    calc |Real.sqrt ((varPlusEps.toVal : ℝ)) -
            Real.sqrt (sigma_sq_exact + eps.toVal)|
        ≤ |((varPlusEps.toVal : ℝ)) - (sigma_sq_exact + eps.toVal)| /
            (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp)) := h_sqrt_lip
      _ ≤ ((η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| + δ_var) /
            (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp)) :=
          div_le_div_of_nonneg_right h_inner (le_of_lt h2sqrtc_pos)
  -- Triangle inequality: |stddev − √(σ² + eps)| ≤ |stddev − √vpe| + |√vpe − √(σ² + eps)|.
  have htri :
      |((stddev.toVal : ℝ)) - Real.sqrt (sigma_sq_exact + eps.toVal)| ≤
        |((stddev.toVal : ℝ)) - Real.sqrt ((varPlusEps.toVal : ℝ))| +
        |Real.sqrt ((varPlusEps.toVal : ℝ)) - Real.sqrt (sigma_sq_exact + eps.toVal)| :=
    abs_sub_le _ _ _
  linarith

/-! ## Fully-tagged end-to-end LayerNorm bound

Glues the cascaded stddev bound into
`fpLayerNorm_end_to_end_error_bound` so the user no longer supplies
`δ_stddev` — that's computed internally from the tag pair + upstream
`δ_var`.  This is the most-tag-tightened LayerNorm forward-error
bound the current framework delivers.

What the user supplies:
- Tag hypotheses: `IsNormal eps.toVal`, `IsNormal varPlusEps.toVal`,
  `min_exp ≤ 0`.
- Framework hypotheses: `0 < n`, `0 < stddev.toVal`, `0 ≤ var.toVal`.
- Upstream δ's: `δ_var` (variance chain), `δ_shift` (shift chain),
  `δ_final` (final divide).
- FP rounding witnesses for eps-add, sqrt (the ones whose
  normal-range hypotheses the tags discharge).

What the user no longer supplies:
- `δ_stddev` — derived via `fpStddev_cascaded_tagged_bound`.
- eps-add normal-range hypothesis.
- sqrt-side normal-range hypothesis.
- sqrt-Lipschitz denominator lower bound.

Before/after: Phase 1-era bound would require all three discharged
preconditions manually, plus the user would need `δ_stddev` as a
derived quantity.  Phase 2 cascaded form: three preconditions gone,
`δ_stddev` auto-composed. -/
theorem fpLayerNorm_fully_tagged_end_to_end_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]
    {n : ℕ} {xs : Fin n → FiniteFp}
    {var varPlusEps stddev eps_fp : FiniteFp}
    {shifted : Fin n → FiniteFp}
    {result : Fin n → FiniteFp}
    (i : Fin n)
    (heps : IsNormal (R := ℝ) eps_fp.toVal)
    (hvpe : IsNormal (R := ℝ) varPlusEps.toVal)
    (hme : FloatFormat.min_exp ≤ 0)
    (hn_pos_r : 0 < (n : ℝ))
    (h_stddev_pos : 0 < (stddev.toVal : ℝ))
    (hvar_nn : 0 ≤ (var.toVal : ℝ))
    {δ_var δ_shift δ_final : ℝ}
    (h_var_err :
      |((var.toVal : ℝ)) -
          variance (fun j => ((xs j).toVal : ℝ))| ≤ δ_var)
    (h_shift :
      |((shifted i).toVal : ℝ) -
          (((xs i).toVal : ℝ) -
            mean (fun j => ((xs j).toVal : ℝ)))| ≤ δ_shift)
    (h_final :
      |((result i).toVal : ℝ) -
          (shifted i).toVal / stddev.toVal| ≤ δ_final)
    (h_varPlusEps : fpAddFinite var eps_fp = Fp.finite varPlusEps)
    (h_ve_s : varPlusEps.s = false)
    (h_ve_m_ne : varPlusEps.m ≠ 0)
    (h_stddev_witness : fpSqrtFinite varPlusEps = Fp.finite stddev) :
    |((result i).toVal : ℝ) -
        layerNorm (fun j => ((xs j).toVal : ℝ)) eps_fp.toVal i| ≤
      δ_final + δ_shift / stddev.toVal +
        |((xs i).toVal : ℝ) -
            LayerNorm.mean (fun j => ((xs j).toVal : ℝ))| *
        ((η : ℝ) * Real.sqrt ((varPlusEps.toVal : ℝ)) +
          ((η : ℝ) * |((var.toVal : ℝ)) + eps_fp.toVal| + δ_var) /
            (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp))) /
          ((stddev.toVal : ℝ) *
            Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) +
                       eps_fp.toVal)) := by
  have hsigma_sq_nn :
      0 ≤ variance (fun j => ((xs j).toVal : ℝ)) :=
    variance_nonneg _ (le_of_lt hn_pos_r)
  have heps_pos : 0 < (eps_fp.toVal : ℝ) := heps.pos
  -- Cascaded stddev bound via the tag.
  have h_stddev_bound :
      |((stddev.toVal : ℝ)) -
          Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) +
                     eps_fp.toVal)| ≤
        (η : ℝ) * Real.sqrt ((varPlusEps.toVal : ℝ)) +
        ((η : ℝ) * |((var.toVal : ℝ)) + eps_fp.toVal| + δ_var) /
          (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp)) :=
    fpStddev_cascaded_tagged_bound heps hvpe hme hvar_nn hsigma_sq_nn
      h_var_err h_varPlusEps h_ve_s h_ve_m_ne h_stddev_witness
  -- Plug into the pre-existing end-to-end theorem.
  exact fpLayerNorm_end_to_end_error_bound i heps_pos hn_pos_r
    h_stddev_pos h_shift h_stddev_bound h_final

/-! ## Concrete adapter: LayerNorm with `NaiveSum` on both sums

Stage 7 demo.  Shows the framework wires together when both the mean
sum and the variance sum are supplied as `FpSum.NaiveSum` traces: the
`FpSum.FpSumBound.ofNaive` adapter threads each trace into the
per-step error bounds, and the whole chain composes via
`fpLayerNorm_fully_tagged_end_to_end_bound`.

The variance-side approximation `|Σ sqDiffs_j / n − variance(xs.toVal)|`
is supplied as a user hypothesis `h_sqDiffs_approx`.  Deriving it from
the per-index squaring error `|sqDiffs_j − shifted_j²|` + the shift
error `|shifted_j − (xs_j − μ)|` is a mechanical but bulky composition
(involving `|a² − b²| = |a − b|·|a + b|` across `n` indices) that we
leave to callers; see the docstring for the expected shape. -/

section Demo

open FpSum

/-- **LayerNorm demo: both sums via `NaiveSum`** (Stage 7).

Instantiates `fpLayerNorm_fully_tagged_end_to_end_bound` using
`FpSumBound.ofNaive` for the mean sum (over `xs`) and the variance
sum (over the squared-difference vector `sqDiffs`).  The per-step
rounding chain is supplied directly; the only "glue" the demo pulls
out of the NaiveSum adapter is the summation relative-error
coefficient `(1+η)^{n-1} − 1`.

**Caller supplies**:

- Two `NaiveSum` traces (mean and variance sums), with
  `AllNormalRange` predicates.
- Tag hypotheses discharged by the fully-tagged framework:
  `IsNormal eps_fp.toVal`, `IsNormal varPlusEps.toVal`, `min_exp ≤ 0`.
- FP-rounding witnesses + remaining normal-range preconditions for
  mean-div, shift, and normalize-div (the tag does not discharge
  these — see the scorecard in the Phase 2 design doc).
- `h_sqDiffs_approx`: a bound on how close the sum of `sqDiffs` is to
  the true variance.  In practice, derived from
  `fpSqDiff_step_error_bound` + shift-error composition across the
  `n` indices; not automated in this demo.

**Produces**: the same end-to-end forward-error bound that
`fpLayerNorm_fully_tagged_end_to_end_bound` produces, with
`δ_var`, `δ_shift`, `δ_final` materialised from the concrete adapters. -/
theorem fpLayerNorm_naiveSum_demo
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]
    {n : ℕ} {xs : Fin n → FiniteFp}
    {meanFp var varPlusEps stddev eps_fp nFp : FiniteFp}
    {sumMeanResult sumVarResult : FiniteFp}
    {shifted sqDiffs result : Fin n → FiniteFp}
    (i : Fin n)
    (hn_pos : 0 < n)
    -- Tag hypotheses
    (heps : IsNormal (R := ℝ) eps_fp.toVal)
    (hvpe : IsNormal (R := ℝ) varPlusEps.toVal)
    (hme : FloatFormat.min_exp ≤ 0)
    -- FP-representation of `n`
    (hNFp_toVal : (nFp.toVal : ℝ) = (n : ℝ))
    (hNFp_m_ne : nFp.m ≠ 0)
    -- NaiveSum traces
    (tμ : NaiveSum (List.ofFn xs) sumMeanResult)
    (hnr_μ : tμ.AllNormalRange (R := ℝ))
    (tσ : NaiveSum (List.ofFn sqDiffs) sumVarResult)
    (hnr_σ : tσ.AllNormalRange (R := ℝ))
    -- Mean step
    (h_mean : fpDivFinite sumMeanResult nFp = Fp.finite meanFp)
    (h_quot_ne_μ : (sumMeanResult.toVal : ℝ) / nFp.toVal ≠ 0)
    (h_quot_normal_μ :
      (2 : ℝ) ^ FloatFormat.min_exp ≤
        |(sumMeanResult.toVal : ℝ) / nFp.toVal|)
    -- Shift step (for index i)
    (h_shifted : ∀ j, fpSubFinite (xs j) meanFp = Fp.finite (shifted j))
    (h_shift_normal :
      (2 : ℝ) ^ FloatFormat.min_exp ≤ |((xs i).toVal : ℝ) - meanFp.toVal|)
    -- Squaring step.  The witnesses live in the signature as
    -- documentation — consumers need them to derive the upstream
    -- `h_sqDiffs_approx` hypothesis — but the demo body proves its
    -- bound without opening the squaring chain, so the parameter is
    -- named with a leading underscore to suppress the unused-variable
    -- linter.
    (_h_sqDiffs : ∀ j,
      fpMulFinite (shifted j) (shifted j) = Fp.finite (sqDiffs j))
    -- Variance divide step
    (h_var : fpDivFinite sumVarResult nFp = Fp.finite var)
    (h_quot_ne_σ : (sumVarResult.toVal : ℝ) / nFp.toVal ≠ 0)
    (h_quot_normal_σ :
      (2 : ℝ) ^ FloatFormat.min_exp ≤
        |(sumVarResult.toVal : ℝ) / nFp.toVal|)
    -- Bound on `|Σ sqDiffs_j/n − variance(xs.toVal)|` (user-supplied;
    -- see the module docstring).
    {δ_sqDiffs_approx : ℝ}
    (h_sqDiffs_approx :
      |(∑ j, ((sqDiffs j).toVal : ℝ)) / (n : ℝ) -
          variance (fun j => ((xs j).toVal : ℝ))| ≤ δ_sqDiffs_approx)
    -- Eps-add + sqrt steps (tag discharges these preconditions)
    (h_varPlusEps : fpAddFinite var eps_fp = Fp.finite varPlusEps)
    (h_ve_s : varPlusEps.s = false)
    (h_ve_m_ne : varPlusEps.m ≠ 0)
    (h_stddev_witness : fpSqrtFinite varPlusEps = Fp.finite stddev)
    -- Nonnegativity of the FP variance (user-supplied; e.g., via
    -- monotonicity of rounding on the nonneg variance sum).
    (hvar_nn : 0 ≤ (var.toVal : ℝ))
    -- Normalize step (per-index divide)
    (h_stddev_m_ne : stddev.m ≠ 0)
    (h_stddev_pos : 0 < (stddev.toVal : ℝ))
    (h_result : ∀ j, fpDivFinite (shifted j) stddev = Fp.finite (result j))
    (h_quot_ne_n : ((shifted i).toVal : ℝ) / stddev.toVal ≠ 0)
    (h_quot_normal_n :
      (2 : ℝ) ^ FloatFormat.min_exp ≤
        |((shifted i).toVal : ℝ) / stddev.toVal|) :
    -- Concrete δ's built from the two NaiveSum adapters.
    letI μSum := FpSumBound.ofNaive (R := ℝ) xs tμ hnr_μ
    letI σSum := FpSumBound.ofNaive (R := ℝ) sqDiffs tσ hnr_σ
    letI δ_shift :=
      (η : ℝ) * |((xs i).toVal : ℝ) - meanFp.toVal| +
        ((η : ℝ) * |(sumMeanResult.toVal : ℝ) / nFp.toVal| +
          μSum.relErr * (∑ j, |((xs j).toVal : ℝ)|) / (n : ℝ))
    letI δ_var :=
      ((η : ℝ) * |(sumVarResult.toVal : ℝ) / nFp.toVal| +
        σSum.relErr * (∑ j, |((sqDiffs j).toVal : ℝ)|) / (n : ℝ)) +
        δ_sqDiffs_approx
    letI δ_final :=
      (η : ℝ) * |((shifted i).toVal : ℝ) / stddev.toVal|
    |((result i).toVal : ℝ) -
        layerNorm (fun j => ((xs j).toVal : ℝ)) eps_fp.toVal i| ≤
      δ_final + δ_shift / stddev.toVal +
        |((xs i).toVal : ℝ) -
            LayerNorm.mean (fun j => ((xs j).toVal : ℝ))| *
        ((η : ℝ) * Real.sqrt ((varPlusEps.toVal : ℝ)) +
          ((η : ℝ) * |((var.toVal : ℝ)) + eps_fp.toVal| + δ_var) /
            (2 * Real.sqrt ((2 : ℝ) ^ FloatFormat.min_exp))) /
          ((stddev.toVal : ℝ) *
            Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) +
                       eps_fp.toVal)) := by
  -- Build the two FpSumBound adapters from the NaiveSum traces.
  set μSum := FpSumBound.ofNaive (R := ℝ) xs tμ hnr_μ with hμSum_def
  set σSum := FpSumBound.ofNaive (R := ℝ) sqDiffs tσ hnr_σ with hσSum_def
  -- μSum.result = sumMeanResult and σSum.result = sumVarResult (by defn).
  have hμSum_result : μSum.result = sumMeanResult := rfl
  have hσSum_result : σSum.result = sumVarResult := rfl
  -- Mean error bound (from the mean NaiveSum adapter).
  have h_mean_err :
      |(meanFp.toVal : ℝ) - (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ)| ≤
        (η : ℝ) * |(μSum.result.toVal : ℝ) / nFp.toVal| +
        μSum.relErr * (∑ j, |((xs j).toVal : ℝ)|) / (n : ℝ) := by
    have := fpMean_error_bound hn_pos μSum hNFp_toVal hNFp_m_ne
      (mean := meanFp)
    rw [hμSum_result] at this
    exact this h_mean h_quot_ne_μ h_quot_normal_μ
  -- Shift error bound (composes the shift step with the mean error).
  have h_shift :
      |((shifted i).toVal : ℝ) -
          (((xs i).toVal : ℝ) -
            LayerNorm.mean (fun j => ((xs j).toVal : ℝ)))| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - meanFp.toVal| +
          ((η : ℝ) * |(sumMeanResult.toVal : ℝ) / nFp.toVal| +
            μSum.relErr * (∑ j, |((xs j).toVal : ℝ)|) / (n : ℝ)) := by
    have h_step :=
      fpShift_error_bound (xs := xs) (mean := meanFp) shifted
        h_shifted i h_shift_normal
    -- mean (toVal ∘ xs) = (∑ xs.toVal)/n by definition; unfold to match.
    have h_mean_unfold :
        LayerNorm.mean (fun j => ((xs j).toVal : ℝ)) =
          (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ) := rfl
    rw [h_mean_unfold]
    rw [hμSum_result] at h_mean_err
    linarith
  -- Variance-sum divide error (from the variance NaiveSum adapter).
  have h_var_sum_err :
      |(var.toVal : ℝ) - (∑ j, ((sqDiffs j).toVal : ℝ)) / (n : ℝ)| ≤
        (η : ℝ) * |(σSum.result.toVal : ℝ) / nFp.toVal| +
        σSum.relErr * (∑ j, |((sqDiffs j).toVal : ℝ)|) / (n : ℝ) := by
    have := fpVar_step_error_bound hn_pos σSum hNFp_toVal hNFp_m_ne
      (var := var)
    rw [hσSum_result] at this
    exact this h_var h_quot_ne_σ h_quot_normal_σ
  -- Variance error (composes the divide error with the approximation hypothesis).
  have h_var_err :
      |(var.toVal : ℝ) -
          variance (fun j => ((xs j).toVal : ℝ))| ≤
        ((η : ℝ) * |(sumVarResult.toVal : ℝ) / nFp.toVal| +
          σSum.relErr * (∑ j, |((sqDiffs j).toVal : ℝ)|) / (n : ℝ)) +
          δ_sqDiffs_approx := by
    have htri :
        |(var.toVal : ℝ) -
            variance (fun j => ((xs j).toVal : ℝ))| ≤
          |(var.toVal : ℝ) -
              (∑ j, ((sqDiffs j).toVal : ℝ)) / (n : ℝ)| +
            |(∑ j, ((sqDiffs j).toVal : ℝ)) / (n : ℝ) -
              variance (fun j => ((xs j).toVal : ℝ))| :=
      abs_sub_le _ _ _
    rw [hσSum_result] at h_var_sum_err
    linarith
  -- Normalize-step error (final divide at index i).
  have h_final :
      |((result i).toVal : ℝ) -
          (shifted i).toVal / stddev.toVal| ≤
        (η : ℝ) * |((shifted i).toVal : ℝ) / stddev.toVal| :=
    fpNormalize_step_error_bound h_stddev_m_ne h_result i
      h_quot_ne_n h_quot_normal_n
  -- Plumbing: apply the fully-tagged end-to-end theorem.
  have hn_pos_r : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  exact fpLayerNorm_fully_tagged_end_to_end_bound (xs := xs)
    (var := var) (varPlusEps := varPlusEps) (stddev := stddev)
    (eps_fp := eps_fp) (shifted := shifted) (result := result)
    i heps hvpe hme hn_pos_r h_stddev_pos hvar_nn h_var_err h_shift
    h_final h_varPlusEps h_ve_s h_ve_m_ne h_stddev_witness

end Demo

end Flean.Tags
