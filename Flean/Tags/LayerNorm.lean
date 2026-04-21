import Flean.Operations.LayerNorm
import Flean.Tags.BoundedRange
import Flean.Tags.Normal

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

end Flean.Tags
