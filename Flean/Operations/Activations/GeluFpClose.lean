import Flean.Operations.Activations.Gelu
import Flean.Operations.Activations.GeluFp
import Flean.Operations.Activations.TanhFpClose
import Flean.Operations.KahanSum

/-!
# Closeness Bound for FP GeLU (tanh approximation)

Composes the gelu pipeline error analysis with the inner tanh
closeness (`fpTanhFinite_close`).

## Strategy: modular closeness

Rather than derive a tight closed-form slack from `(xr, αr, cr, hr, η)`
alone (which requires several hundred lines of magnitude tracking
through 9 FP ops), this file ships a *modular* closeness theorem:

* The user supplies per-step closeness witnesses `ε_*` for each FP
  intermediate (typically derived from `KahanSum.fpMul_error_or_zero`
  applied to the witness bundle).
* The user supplies magnitude bounds `M_hx`, `M_opt` for the final-step
  factors.
* We discharge the final triangle inequality.

The output slack is:

```
ε_total := η · (M_hx · M_opt) + ε_hx · M_opt + |hr · xr| · ε_opt + ε_hx · ε_opt
```

This is the standard "two-factor product error" bound applied to the
final `r = hx · opt` step. The user's `ε_opt` itself absorbs the
upstream error chain (8 prior steps + tanh closeness).
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeNearest ℝ] [RModeSticky ℝ] [ExpApprox] [ExpApproxSound]

/-- Modular final-step closeness for `fpGeluFinite_with`.

Given:
* `ε_hx` — closeness of the FP `half · x` against `hr · xr`.
* `ε_opt` — closeness of the FP `1 + tanh(u)` against the math
  `1 + tanh(c · (x + α·x³))` (this absorbs all 8 prior steps + tanh).
* `M_hx`, `M_opt` — magnitude bounds on the final-step FP factors.
* `h_r_close_step` — the final FP rounding step bound.

We deliver `|r_fp − gelu_real| ≤ ε_total` where `ε_total` is the
two-factor product-error formula above. -/
theorem fpGeluFinite_with_close_modular
    (half α c x : FiniteFp) (w : GeluFpWitness half α c x)
    (ε_hx : ℝ) (h_hx_close : |((w.hx.toVal : ℝ)) -
        (half.toVal : ℝ) * (x.toVal : ℝ)| ≤ ε_hx)
    (ε_opt : ℝ) (h_opt_close : |((w.opt.toVal : ℝ)) -
        (1 + Real.tanh ((c.toVal : ℝ) * ((x.toVal : ℝ) +
          (α.toVal : ℝ) * ((x.toVal : ℝ) * (x.toVal : ℝ) * (x.toVal : ℝ)))))| ≤ ε_opt)
    (h_r_close_step : |((w.r.toVal : ℝ)) -
        (w.hx.toVal : ℝ) * (w.opt.toVal : ℝ)| ≤
        η * |(w.hx.toVal : ℝ) * (w.opt.toVal : ℝ)|)
    (M_hx : ℝ) (h_M_hx : |((w.hx.toVal : ℝ))| ≤ M_hx) (h_M_hx_nn : 0 ≤ M_hx)
    (M_opt : ℝ) (h_M_opt : |((w.opt.toVal : ℝ))| ≤ M_opt) (h_M_opt_nn : 0 ≤ M_opt) :
    |((w.r.toVal : ℝ)) - Real.geluTanhApprox (half.toVal : ℝ) (c.toVal : ℝ)
        (α.toVal : ℝ) (x.toVal : ℝ)| ≤
      η * (M_hx * M_opt) + ε_hx * M_opt +
      |((half.toVal : ℝ)) * (x.toVal : ℝ)| * ε_opt + ε_hx * ε_opt := by
  set xr : ℝ := (x.toVal : ℝ)
  set hr : ℝ := (half.toVal : ℝ)
  set αr : ℝ := (α.toVal : ℝ)
  set cr : ℝ := (c.toVal : ℝ)
  set hx_fp : ℝ := (w.hx.toVal : ℝ)
  set opt_fp : ℝ := (w.opt.toVal : ℝ)
  set r_fp : ℝ := (w.r.toVal : ℝ)
  set hx_r : ℝ := hr * xr
  set opt_r : ℝ := 1 + Real.tanh (cr * (xr + αr * (xr * xr * xr)))
  -- Triangle decomposition
  have h_split :
      r_fp - hx_r * opt_r =
      (r_fp - hx_fp * opt_fp) + (hx_fp * opt_fp - hx_r * opt_r) := by ring
  have h_diff_factor :
      hx_fp * opt_fp - hx_r * opt_r =
      (hx_fp - hx_r) * opt_fp + hx_r * (opt_fp - opt_r) := by ring
  have h_hx_close' : |hx_fp - hx_r| ≤ ε_hx := h_hx_close
  have h_opt_close' : |opt_fp - opt_r| ≤ ε_opt := h_opt_close
  -- |hx_fp · opt_fp − hx_r · opt_r| ≤ ε_hx · M_opt + |hx_r| · ε_opt
  have h_cross_bound :
      |hx_fp * opt_fp - hx_r * opt_r| ≤ ε_hx * M_opt + |hx_r| * ε_opt := by
    rw [h_diff_factor]
    have h1 : |hx_fp - hx_r| * |opt_fp| ≤ ε_hx * M_opt :=
      mul_le_mul h_hx_close' h_M_opt (abs_nonneg _)
        (le_trans (abs_nonneg _) h_hx_close')
    have h2 : |hx_r| * |opt_fp - opt_r| ≤ |hx_r| * ε_opt :=
      mul_le_mul_of_nonneg_left h_opt_close' (abs_nonneg _)
    calc |(hx_fp - hx_r) * opt_fp + hx_r * (opt_fp - opt_r)|
        ≤ |(hx_fp - hx_r) * opt_fp| + |hx_r * (opt_fp - opt_r)| := abs_add_le _ _
      _ = |hx_fp - hx_r| * |opt_fp| + |hx_r| * |opt_fp - opt_r| := by
            rw [abs_mul, abs_mul]
      _ ≤ ε_hx * M_opt + |hx_r| * ε_opt := by linarith
  -- Final-step rounding |r_fp − hx_fp · opt_fp| ≤ η · M_hx · M_opt
  have h_hx_fp_opt_fp_abs : |hx_fp * opt_fp| ≤ M_hx * M_opt := by
    rw [abs_mul]
    exact mul_le_mul h_M_hx h_M_opt (abs_nonneg _) h_M_hx_nn
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have h_step_loose : |r_fp - hx_fp * opt_fp| ≤ η * (M_hx * M_opt) :=
    le_trans h_r_close_step (mul_le_mul_of_nonneg_left h_hx_fp_opt_fp_abs hη_nn)
  -- |hx_r| = |hr · xr|
  have h_hx_r_abs : |hx_r| = |hr * xr| := by simp [hx_r]
  -- Note: ε_hx · ε_opt is dropped on the LHS but kept as a slack-loosener.
  have h_eps_nn : 0 ≤ ε_hx * ε_opt :=
    mul_nonneg (le_trans (abs_nonneg _) h_hx_close')
               (le_trans (abs_nonneg _) h_opt_close')
  -- gelu_real factored
  have h_gelu_eq :
      Real.geluTanhApprox hr cr αr xr = hx_r * opt_r := by
    unfold Real.geluTanhApprox
    show hr * xr * (1 + Real.tanh (cr * (xr + αr * xr ^ 3))) = hx_r * opt_r
    have h_pow : (xr : ℝ) ^ 3 = xr * xr * xr := by ring
    rw [h_pow]
  rw [h_gelu_eq]
  calc |r_fp - hx_r * opt_r|
      = |(r_fp - hx_fp * opt_fp) + (hx_fp * opt_fp - hx_r * opt_r)| := by rw [h_split]
    _ ≤ |r_fp - hx_fp * opt_fp| + |hx_fp * opt_fp - hx_r * opt_r| := abs_add_le _ _
    _ ≤ η * (M_hx * M_opt) + (ε_hx * M_opt + |hx_r| * ε_opt) := by linarith
    _ = η * (M_hx * M_opt) + ε_hx * M_opt + |hx_r| * ε_opt := by ring
    _ ≤ η * (M_hx * M_opt) + ε_hx * M_opt + |hr * xr| * ε_opt + ε_hx * ε_opt := by
          rw [← h_hx_r_abs]; linarith

/-! ## Discussion

The closeness lemma above is "modular": it consumes a `(ε_hx, ε_opt)`
pair plus magnitude bounds and produces the final-step triangle.

The tight closed-form lemma below derives the modular theorem's inputs
mechanically from `(xr, αr, cr, hr)` and per-step normal-range
hypotheses, threading magnitudes and rounding slacks through all
9 FP ops (5 mul + 2 add + tanh + final mul). -/

/-! ## Tight (non-modular) closeness

Derives `(ε_hx, ε_opt, M_hx, M_opt)` from input bounds + per-step
normal-range hypotheses, then dispatches to
`fpGeluFinite_with_close_modular`.

The chain follows the 9-step pipeline:
```
1. x²       2. x³       3. αx³      4. inner = x + αx³
5. u = c·inner          6. t = tanh(u)
7. opt = 1 + t          8. hx = half · x       9. r = hx · opt
```
At each step, magnitudes propagate as `M_next ≤ (1+η)·M_prev_bound`
(rounding amplifies by at most `1+η`); errors propagate as
`ε_next ≤ η·|exact_next| + (Lipschitz constant)·ε_prev`.

For step 6 (tanh), we use `fpTanhFinite_close` and the 1-Lipschitz
property of `Real.tanh` to bound
`|t_fp - tanh(c·(x+α·x³))| ≤ tanh_slack(u_fp_real, tx_real) + |u_fp_real - c·(x+α·x³)|`.
-/

/-- Polynomial-chain magnitude: bound on `|x³_fp|` given `|x| ≤ B`. -/
noncomputable def M_x_cu (B : ℝ) : ℝ := (1 + η) ^ 2 * B ^ 3

/-- Polynomial-chain error: bound on `|x³_fp - x³|` given `|x| ≤ B`. -/
noncomputable def ε_x_cu (B : ℝ) : ℝ := η * (2 + η) * B ^ 3

/-- Polynomial-chain magnitude: bound on `|αx³_fp|`. -/
noncomputable def M_ax_cu (B Bα : ℝ) : ℝ := (1 + η) ^ 3 * Bα * B ^ 3

/-- Polynomial-chain error: bound on `|αx³_fp - α·x³|`. -/
noncomputable def ε_ax_cu (B Bα : ℝ) : ℝ :=
  η * (1 + η) ^ 2 * Bα * B ^ 3 + Bα * ε_x_cu B

/-- Polynomial-chain magnitude: bound on `|inner_fp|` where
`inner_fp = round(x + αx³_fp)`. -/
noncomputable def M_inner (B Bα : ℝ) : ℝ := (1 + η) * (B + M_ax_cu B Bα)

/-- Polynomial-chain error: bound on `|inner_fp - (x + α·x³)|`. -/
noncomputable def ε_inner (B Bα : ℝ) : ℝ :=
  η * (B + M_ax_cu B Bα) + ε_ax_cu B Bα

/-- Polynomial-chain magnitude: bound on `|u_fp|` where `u_fp = round(c·inner_fp)`. -/
noncomputable def M_u (B Bα Bc : ℝ) : ℝ := (1 + η) * Bc * M_inner B Bα

/-- Polynomial-chain error: bound on `|u_fp - c·(x+α·x³)|`. -/
noncomputable def ε_u (B Bα Bc : ℝ) : ℝ :=
  η * Bc * M_inner B Bα + Bc * ε_inner B Bα

/-- Tight closed-form slack expression for `fpGeluFinite_with`.

Parameters:
* `B`, `Bh`, `Bα`, `Bc` — magnitude bounds on `x`, `half`, `α`, `c`.
* `tx_real`, `u_fp_real` — FP intermediates needed to pinpoint the
  inner tanh's slack.

Decomposition: final-mul rounding `η·M_hx·M_opt` plus the cross terms
from the modular theorem, with `M_hx`, `M_opt`, `ε_hx`, `ε_opt`
expanded from the polynomial chain.

Defined inline (no `let` bindings) so that downstream callers can match
the bound by `rfl` against the algebraic form `η · M_hx · M_opt + ε_hx
· M_opt + Bh · B · ε_opt + ε_hx · ε_opt` produced by the modular
theorem. -/
noncomputable def fpGeluFinite_slack_at
    (B Bh Bα Bc tx_real u_fp_real : ℝ) : ℝ :=
  -- Final-mul rounding term: η · M_hx · M_opt
  (η : ℝ) *
    ((1 + η) * Bh * B *
      ((1 + η) * (1 + (1 + fpTanhFinite_slack_at u_fp_real tx_real)))) +
  -- ε_hx · M_opt cross term
  (η : ℝ) * (Bh * B) *
    ((1 + η) * (1 + (1 + fpTanhFinite_slack_at u_fp_real tx_real))) +
  -- |hr · xr| · ε_opt cross term (loosened to Bh · B)
  Bh * B *
    ((η : ℝ) * (1 + (1 + fpTanhFinite_slack_at u_fp_real tx_real)) +
      (fpTanhFinite_slack_at u_fp_real tx_real + ε_u B Bα Bc)) +
  -- ε_hx · ε_opt cross term
  (η : ℝ) * (Bh * B) *
    ((η : ℝ) * (1 + (1 + fpTanhFinite_slack_at u_fp_real tx_real)) +
      (fpTanhFinite_slack_at u_fp_real tx_real + ε_u B Bα Bc))

/-- The slack is non-negative when input bounds are non-negative. -/
theorem fpGeluFinite_slack_at_nn
    {B Bh Bα Bc tx_real u_fp_real : ℝ}
    (hB : 0 ≤ B) (hBh : 0 ≤ Bh) (hBα : 0 ≤ Bα) (hBc : 0 ≤ Bc) :
    0 ≤ fpGeluFinite_slack_at B Bh Bα Bc tx_real u_fp_real := by
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hts_nn : 0 ≤ fpTanhFinite_slack_at u_fp_real tx_real :=
    fpTanhFinite_slack_at_nn u_fp_real tx_real
  have hMxc_nn : 0 ≤ M_x_cu B := by show 0 ≤ (1 + (η : ℝ))^2 * B^3; positivity
  have hεxc_nn : 0 ≤ ε_x_cu B := by
    show 0 ≤ (η : ℝ) * (2 + η) * B^3; positivity
  have hMaxc_nn : 0 ≤ M_ax_cu B Bα := by
    show 0 ≤ (1 + (η : ℝ))^3 * Bα * B^3; positivity
  have hεaxc_nn : 0 ≤ ε_ax_cu B Bα := by
    show 0 ≤ (η : ℝ) * (1 + η)^2 * Bα * B^3 + Bα * ε_x_cu B; positivity
  have hMinner_nn : 0 ≤ M_inner B Bα := by
    show 0 ≤ (1 + (η : ℝ)) * (B + M_ax_cu B Bα); positivity
  have hεinner_nn : 0 ≤ ε_inner B Bα := by
    show 0 ≤ (η : ℝ) * (B + M_ax_cu B Bα) + ε_ax_cu B Bα; positivity
  have hεu_nn : 0 ≤ ε_u B Bα Bc := by
    show 0 ≤ (η : ℝ) * Bc * M_inner B Bα + Bc * ε_inner B Bα; positivity
  unfold fpGeluFinite_slack_at
  positivity

/-- **Tight closeness lemma for the FP gelu kernel.**

Derives `(ε_hx, ε_opt, M_hx, M_opt)` from `(B, Bh, Bα, Bc)` plus per-step
normal-range hypotheses, then composes
`fpGeluFinite_with_close_modular` with the polynomial-chain derivations.

Hypothesis bundle is split into:
* Input magnitude bounds: `|x.toVal| ≤ B`, `|half.toVal| ≤ Bh`, etc.
* 7 polynomial-chain normal-range-or-zero hypotheses (one per FP op
  before tanh + the final-mul, the inner-add, and the half·x mul).
* The standard 6 normal-range hypotheses for the inner tanh
  (`fpTanhFinite_close`'s preconditions).
-/
theorem fpGeluFinite_close
    (half α c x : FiniteFp) (w : GeluFpWitness half α c x)
    -- Magnitude bounds on inputs
    {B Bh Bα Bc : ℝ}
    (hB : |((x.toVal : ℝ))| ≤ B) (hB_nn : 0 ≤ B)
    (hBh : |((half.toVal : ℝ))| ≤ Bh) (hBh_nn : 0 ≤ Bh)
    (hBα : |((α.toVal : ℝ))| ≤ Bα) (hBα_nn : 0 ≤ Bα)
    (hBc : |((c.toVal : ℝ))| ≤ Bc) (hBc_nn : 0 ≤ Bc)
    -- Polynomial-chain normal-range-or-zero hypotheses
    (h_sq_nr : isNormalRange ((x.toVal : ℝ) * (x.toVal : ℝ)) ∨
               (x.toVal : ℝ) * (x.toVal : ℝ) = 0)
    (h_cu_nr : isNormalRange ((w.x_sq.toVal : ℝ) * (x.toVal : ℝ)) ∨
               (w.x_sq.toVal : ℝ) * (x.toVal : ℝ) = 0)
    (h_ax_cu_nr : isNormalRange ((α.toVal : ℝ) * (w.x_cu.toVal : ℝ)) ∨
                  (α.toVal : ℝ) * (w.x_cu.toVal : ℝ) = 0)
    (h_inner_nr : isNormalRange ((x.toVal : ℝ) + (w.ax_cu.toVal : ℝ)) ∨
                  (x.toVal : ℝ) + (w.ax_cu.toVal : ℝ) = 0)
    (h_u_nr : isNormalRange ((c.toVal : ℝ) * (w.inner.toVal : ℝ)) ∨
              (c.toVal : ℝ) * (w.inner.toVal : ℝ) = 0)
    (h_opt_nr : isNormalRange ((1 : ℝ) + (w.tanh_w.r.toVal : ℝ)) ∨
                (1 : ℝ) + (w.tanh_w.r.toVal : ℝ) = 0)
    (h_hx_nr : isNormalRange ((half.toVal : ℝ) * (x.toVal : ℝ)) ∨
               (half.toVal : ℝ) * (x.toVal : ℝ) = 0)
    (h_r_nr : isNormalRange ((w.hx.toVal : ℝ) * (w.opt.toVal : ℝ)) ∨
              (w.hx.toVal : ℝ) * (w.opt.toVal : ℝ) = 0)
    -- Tanh's normal-range hypotheses (preconditions of fpTanhFinite_close)
    (h_dbl1_nr : isNormalRange ((w.u.toVal : ℝ) + (w.u.toVal : ℝ)) ∨
                 (w.u.toVal : ℝ) + (w.u.toVal : ℝ) = 0)
    (her_normal : isNormalRange (Real.exp (-((w.tanh_w.tx.toVal : ℝ)))))
    (h_d_normal : isNormalRange ((1 : ℝ) + (w.tanh_w.sig.e.toVal : ℝ)) ∨
                  ((1 : ℝ) + (w.tanh_w.sig.e.toVal : ℝ) = 0))
    (h_sig_r_normal : isNormalRange ((1 : ℝ) / (w.tanh_w.sig.d.toVal : ℝ)) ∨
                      ((1 : ℝ) / (w.tanh_w.sig.d.toVal : ℝ) = 0))
    (hd_m_ne : w.tanh_w.sig.d.m ≠ 0)
    (h_dbl2_nr : isNormalRange ((w.tanh_w.sig.r.toVal : ℝ) + (w.tanh_w.sig.r.toVal : ℝ)) ∨
                 ((w.tanh_w.sig.r.toVal : ℝ) + (w.tanh_w.sig.r.toVal : ℝ) = 0))
    (h_sub_nr : isNormalRange ((w.tanh_w.tsx.toVal : ℝ) - (1 : ℝ)) ∨
                ((w.tanh_w.tsx.toVal : ℝ) - (1 : ℝ) = 0)) :
    |((w.r.toVal : ℝ)) - Real.geluTanhApprox (half.toVal : ℝ) (c.toVal : ℝ)
        (α.toVal : ℝ) (x.toVal : ℝ)| ≤
      fpGeluFinite_slack_at B Bh Bα Bc
        (w.tanh_w.tx.toVal : ℝ) (w.u.toVal : ℝ) := by
  -- Setup abbreviations
  set xr : ℝ := (x.toVal : ℝ) with hxr_def
  set hr : ℝ := (half.toVal : ℝ) with hhr_def
  set αr : ℝ := (α.toVal : ℝ) with hαr_def
  set cr : ℝ := (c.toVal : ℝ) with hcr_def
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have h1η_nn : (0 : ℝ) ≤ 1 + η := by linarith
  -- Step 1: x²
  have h_sq_close := KahanSum.fpMul_error_or_zero (R := ℝ) x x w.x_sq w.h_sq h_sq_nr
  have h_sq_xr : (x.toVal : ℝ) * (x.toVal : ℝ) = xr * xr := by rw [hxr_def]
  rw [h_sq_xr] at h_sq_close
  have h_xr_sq_abs : |xr * xr| ≤ B * B := by
    rw [abs_mul]; exact mul_le_mul hB hB (abs_nonneg _) hB_nn
  have h_x_sq_close : |(w.x_sq.toVal : ℝ) - xr * xr| ≤ η * (B * B) := by
    refine le_trans h_sq_close ?_
    exact mul_le_mul_of_nonneg_left h_xr_sq_abs hη_nn
  have h_x_sq_mag : |(w.x_sq.toVal : ℝ)| ≤ (1 + η) * (B * B) := by
    have h1 : |(w.x_sq.toVal : ℝ)| ≤ |(w.x_sq.toVal : ℝ) - xr * xr| + |xr * xr| := by
      have := abs_add_le ((w.x_sq.toVal : ℝ) - xr * xr) (xr * xr)
      have hrw : (w.x_sq.toVal : ℝ) - xr * xr + (xr * xr) = (w.x_sq.toVal : ℝ) := by ring
      linarith [abs_add_le ((w.x_sq.toVal : ℝ) - xr * xr) (xr * xr),
                show |(w.x_sq.toVal : ℝ) - xr * xr + xr * xr| = |(w.x_sq.toVal : ℝ)| from
                  by rw [hrw]]
    calc |(w.x_sq.toVal : ℝ)|
        ≤ |(w.x_sq.toVal : ℝ) - xr * xr| + |xr * xr| := h1
      _ ≤ η * (B * B) + B * B := by linarith
      _ = (1 + η) * (B * B) := by ring
  -- Step 2: x³ = x_sq · x
  have h_cu_close := KahanSum.fpMul_error_or_zero (R := ℝ) w.x_sq x w.x_cu w.h_cu h_cu_nr
  -- |x_cu_fp - x_sq_fp · xr| ≤ η · |x_sq_fp · xr|
  -- Compose: |x_cu_fp - xr³| ≤ |x_cu_fp - x_sq_fp · xr| + |x_sq_fp · xr - xr · xr · xr|
  have hB3_nn : 0 ≤ B^3 := by positivity
  have hBpow_eq : B * B * B = B ^ 3 := by ring
  have h_xsq_xr_mag : |(w.x_sq.toVal : ℝ) * xr| ≤ (1 + η) * B^3 := by
    rw [abs_mul]
    have hxr_abs : |xr| ≤ B := hB
    calc |(w.x_sq.toVal : ℝ)| * |xr|
        ≤ (1 + η) * (B * B) * B := by
          apply mul_le_mul h_x_sq_mag hxr_abs (abs_nonneg _)
          exact mul_nonneg h1η_nn (mul_nonneg hB_nn hB_nn)
      _ = (1 + η) * B^3 := by rw [← hBpow_eq]; ring
  have h_x_cu_step_loose : |(w.x_cu.toVal : ℝ) - (w.x_sq.toVal : ℝ) * xr| ≤
      η * ((1 + η) * B^3) :=
    le_trans h_cu_close (mul_le_mul_of_nonneg_left h_xsq_xr_mag hη_nn)
  have h_xsq_to_xr2 : |(w.x_sq.toVal : ℝ) * xr - xr * xr * xr| ≤ η * B^3 := by
    have h1 : (w.x_sq.toVal : ℝ) * xr - xr * xr * xr =
        ((w.x_sq.toVal : ℝ) - xr * xr) * xr := by ring
    rw [h1, abs_mul]
    have h2 : |(w.x_sq.toVal : ℝ) - xr * xr| * |xr| ≤ η * (B * B) * B :=
      mul_le_mul h_x_sq_close hB (abs_nonneg _)
        (mul_nonneg hη_nn (mul_nonneg hB_nn hB_nn))
    rw [← hBpow_eq]; linarith
  have h_x_cu_close : |(w.x_cu.toVal : ℝ) - xr * xr * xr| ≤ η * (2 + η) * B^3 := by
    have h_split : (w.x_cu.toVal : ℝ) - xr * xr * xr =
        ((w.x_cu.toVal : ℝ) - (w.x_sq.toVal : ℝ) * xr) +
          ((w.x_sq.toVal : ℝ) * xr - xr * xr * xr) := by ring
    calc |(w.x_cu.toVal : ℝ) - xr * xr * xr|
        = |((w.x_cu.toVal : ℝ) - (w.x_sq.toVal : ℝ) * xr) +
            ((w.x_sq.toVal : ℝ) * xr - xr * xr * xr)| := by rw [h_split]
      _ ≤ |(w.x_cu.toVal : ℝ) - (w.x_sq.toVal : ℝ) * xr| +
            |(w.x_sq.toVal : ℝ) * xr - xr * xr * xr| := abs_add_le _ _
      _ ≤ η * ((1 + η) * B^3) + η * B^3 := by linarith
      _ = η * (2 + η) * B^3 := by ring
  have h_x_cu_eq_ε : η * (2 + η) * B^3 = ε_x_cu B := by unfold ε_x_cu; rfl
  have h_x_cu_close' : |(w.x_cu.toVal : ℝ) - xr * xr * xr| ≤ ε_x_cu B := by
    rw [← h_x_cu_eq_ε]; exact h_x_cu_close
  have h_x_cu_mag : |(w.x_cu.toVal : ℝ)| ≤ M_x_cu B := by
    have h_xr3_abs : |xr * xr * xr| ≤ B^3 := by
      have habs : |xr * xr * xr| = |xr| * |xr| * |xr| := by rw [abs_mul, abs_mul]
      rw [habs]
      have h := mul_le_mul (mul_le_mul hB hB (abs_nonneg _) hB_nn) hB
        (abs_nonneg _) (mul_nonneg hB_nn hB_nn)
      rw [hBpow_eq] at h; exact h
    have h_sum :
        |(w.x_cu.toVal : ℝ)| ≤
          |(w.x_cu.toVal : ℝ) - xr * xr * xr| + |xr * xr * xr| := by
      have hadd := abs_add_le ((w.x_cu.toVal : ℝ) - xr * xr * xr) (xr * xr * xr)
      have hrw : (w.x_cu.toVal : ℝ) - xr * xr * xr + xr * xr * xr =
          (w.x_cu.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |(w.x_cu.toVal : ℝ)| ≤ (1 + (η : ℝ)) ^ 2 * B^3
    have h_expand : (1 + (η : ℝ)) ^ 2 * B^3 = (η * (2 + η) + 1) * B^3 := by ring
    rw [h_expand]
    nlinarith [h_sum, h_x_cu_close, h_xr3_abs, hη_nn, hB3_nn]
  -- Step 3: αx³ = α · x_cu
  have h_ax_cu_close := KahanSum.fpMul_error_or_zero (R := ℝ) α w.x_cu w.ax_cu
    w.h_ax_cu h_ax_cu_nr
  -- |ax_cu_fp - αr · x_cu_fp| ≤ η · |αr · x_cu_fp|
  have h_α_xcu_mag : |αr * (w.x_cu.toVal : ℝ)| ≤ Bα * M_x_cu B := by
    rw [abs_mul]
    exact mul_le_mul hBα h_x_cu_mag (abs_nonneg _) hBα_nn
  have h_ax_cu_step : |(w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ)| ≤
      η * (Bα * M_x_cu B) := by
    refine le_trans h_ax_cu_close ?_
    exact mul_le_mul_of_nonneg_left h_α_xcu_mag hη_nn
  have h_α_diff : |αr * (w.x_cu.toVal : ℝ) - αr * (xr * xr * xr)| ≤
      Bα * ε_x_cu B := by
    have h1 : αr * (w.x_cu.toVal : ℝ) - αr * (xr * xr * xr) =
        αr * ((w.x_cu.toVal : ℝ) - xr * xr * xr) := by ring
    rw [h1, abs_mul]
    exact mul_le_mul hBα h_x_cu_close' (abs_nonneg _) hBα_nn
  have h_ax_cu_close' : |(w.ax_cu.toVal : ℝ) - αr * (xr * xr * xr)| ≤
      ε_ax_cu B Bα := by
    have h_split : (w.ax_cu.toVal : ℝ) - αr * (xr * xr * xr) =
        ((w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ)) +
          (αr * (w.x_cu.toVal : ℝ) - αr * (xr * xr * xr)) := by ring
    have hε_eq :
        ε_ax_cu B Bα = (η : ℝ) * (1 + η) ^ 2 * Bα * B ^ 3 + Bα * ε_x_cu B := rfl
    have hM_eq : M_x_cu B = (1 + (η : ℝ)) ^ 2 * B ^ 3 := rfl
    rw [hε_eq]
    calc |(w.ax_cu.toVal : ℝ) - αr * (xr * xr * xr)|
        = |((w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ)) +
            (αr * (w.x_cu.toVal : ℝ) - αr * (xr * xr * xr))| := by rw [h_split]
      _ ≤ |(w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ)| +
            |αr * (w.x_cu.toVal : ℝ) - αr * (xr * xr * xr)| := abs_add_le _ _
      _ ≤ η * (Bα * M_x_cu B) + Bα * ε_x_cu B := by linarith
      _ = (η : ℝ) * (1 + η) ^ 2 * Bα * B ^ 3 + Bα * ε_x_cu B := by
            rw [hM_eq]; ring
  have h_ax_cu_mag : |(w.ax_cu.toVal : ℝ)| ≤ M_ax_cu B Bα := by
    have h_axcu_exact : |αr * (w.x_cu.toVal : ℝ)| ≤ Bα * M_x_cu B := h_α_xcu_mag
    have h_sum :
        |(w.ax_cu.toVal : ℝ)| ≤
          |(w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ)| +
            |αr * (w.x_cu.toVal : ℝ)| := by
      have := abs_add_le ((w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ))
        (αr * (w.x_cu.toVal : ℝ))
      have hrw : (w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ) +
          αr * (w.x_cu.toVal : ℝ) = (w.ax_cu.toVal : ℝ) := by ring
      rw [hrw] at this; exact this
    show |(w.ax_cu.toVal : ℝ)| ≤ (1 + (η : ℝ)) ^ 3 * Bα * B ^ 3
    have hM_eq : M_x_cu B = (1 + (η : ℝ)) ^ 2 * B ^ 3 := rfl
    calc |(w.ax_cu.toVal : ℝ)|
        ≤ |(w.ax_cu.toVal : ℝ) - αr * (w.x_cu.toVal : ℝ)| +
            |αr * (w.x_cu.toVal : ℝ)| := h_sum
      _ ≤ η * (Bα * M_x_cu B) + Bα * M_x_cu B := by linarith
      _ = (1 + η) * (Bα * M_x_cu B) := by ring
      _ = (1 + η) * Bα * ((1 + η) ^ 2 * B^3) := by rw [hM_eq]; ring
      _ = (1 + η) ^ 3 * Bα * B^3 := by ring
  -- Step 4: inner = x + ax_cu
  have h_inner_close := KahanSum.fpAdd_error_or_zero (R := ℝ) x w.ax_cu w.inner
    w.h_inner h_inner_nr
  have h_x_axcu_mag : |xr + (w.ax_cu.toVal : ℝ)| ≤ B + M_ax_cu B Bα := by
    have := abs_add_le xr ((w.ax_cu.toVal : ℝ))
    linarith
  have h_inner_step : |(w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ))| ≤
      η * (B + M_ax_cu B Bα) := by
    refine le_trans h_inner_close ?_
    exact mul_le_mul_of_nonneg_left h_x_axcu_mag hη_nn
  have h_inner_close' : |(w.inner.toVal : ℝ) - (xr + αr * (xr * xr * xr))| ≤
      ε_inner B Bα := by
    have h_split : (w.inner.toVal : ℝ) - (xr + αr * (xr * xr * xr)) =
        ((w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ))) +
          ((w.ax_cu.toVal : ℝ) - αr * (xr * xr * xr)) := by ring
    show |(w.inner.toVal : ℝ) - (xr + αr * (xr * xr * xr))| ≤
      (η : ℝ) * (B + M_ax_cu B Bα) + ε_ax_cu B Bα
    calc |(w.inner.toVal : ℝ) - (xr + αr * (xr * xr * xr))|
        = |((w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ))) +
            ((w.ax_cu.toVal : ℝ) - αr * (xr * xr * xr))| := by rw [h_split]
      _ ≤ |(w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ))| +
            |(w.ax_cu.toVal : ℝ) - αr * (xr * xr * xr)| := abs_add_le _ _
      _ ≤ (η : ℝ) * (B + M_ax_cu B Bα) + ε_ax_cu B Bα := by linarith
  have h_inner_mag : |(w.inner.toVal : ℝ)| ≤ M_inner B Bα := by
    have h_sum :
        |(w.inner.toVal : ℝ)| ≤
          |(w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ))| +
            |xr + (w.ax_cu.toVal : ℝ)| := by
      have := abs_add_le ((w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ)))
        (xr + (w.ax_cu.toVal : ℝ))
      have hrw : (w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ)) +
          (xr + (w.ax_cu.toVal : ℝ)) = (w.inner.toVal : ℝ) := by ring
      rw [hrw] at this; exact this
    unfold M_inner
    calc |(w.inner.toVal : ℝ)|
        ≤ |(w.inner.toVal : ℝ) - (xr + (w.ax_cu.toVal : ℝ))| +
            |xr + (w.ax_cu.toVal : ℝ)| := h_sum
      _ ≤ η * (B + M_ax_cu B Bα) + (B + M_ax_cu B Bα) := by linarith
      _ = (1 + η) * (B + M_ax_cu B Bα) := by ring
  -- Step 5: u = c · inner
  have h_u_close := KahanSum.fpMul_error_or_zero (R := ℝ) c w.inner w.u w.h_u h_u_nr
  have h_c_inner_mag : |cr * (w.inner.toVal : ℝ)| ≤ Bc * M_inner B Bα := by
    rw [abs_mul]
    exact mul_le_mul hBc h_inner_mag (abs_nonneg _) hBc_nn
  have h_u_step : |(w.u.toVal : ℝ) - cr * (w.inner.toVal : ℝ)| ≤
      η * (Bc * M_inner B Bα) := by
    refine le_trans h_u_close ?_
    exact mul_le_mul_of_nonneg_left h_c_inner_mag hη_nn
  have h_c_diff : |cr * (w.inner.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr))| ≤
      Bc * ε_inner B Bα := by
    have h1 : cr * (w.inner.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr)) =
        cr * ((w.inner.toVal : ℝ) - (xr + αr * (xr * xr * xr))) := by ring
    rw [h1, abs_mul]
    exact mul_le_mul hBc h_inner_close' (abs_nonneg _) hBc_nn
  have h_u_close' : |(w.u.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr))| ≤
      ε_u B Bα Bc := by
    have h_split : (w.u.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr)) =
        ((w.u.toVal : ℝ) - cr * (w.inner.toVal : ℝ)) +
          (cr * (w.inner.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr))) := by ring
    have hε_eq : ε_u B Bα Bc = (η : ℝ) * Bc * M_inner B Bα + Bc * ε_inner B Bα := rfl
    rw [hε_eq]
    calc |(w.u.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr))|
        = |((w.u.toVal : ℝ) - cr * (w.inner.toVal : ℝ)) +
            (cr * (w.inner.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr)))| := by rw [h_split]
      _ ≤ |(w.u.toVal : ℝ) - cr * (w.inner.toVal : ℝ)| +
            |cr * (w.inner.toVal : ℝ) - cr * (xr + αr * (xr * xr * xr))| := abs_add_le _ _
      _ ≤ (η : ℝ) * Bc * M_inner B Bα + Bc * ε_inner B Bα := by linarith
  -- Step 6: t = tanh(u). Use fpTanhFinite_close + tanh's 1-Lipschitz.
  -- Derive tx + sigmoid witnesses
  have h_tanh_close := fpTanhFinite_close w.u w.tanh_w.hdbl1
    w.tanh_w.sig.he w.tanh_w.sig.hd w.tanh_w.sig.hr
    w.tanh_w.hdbl2 w.tanh_w.hsub
    h_dbl1_nr her_normal h_d_normal h_sig_r_normal hd_m_ne h_dbl2_nr h_sub_nr
  -- h_tanh_close : |tanh_w.r.toVal - Real.tanh w.u.toVal| ≤ tanh_slack
  set tanh_slack : ℝ :=
    fpTanhFinite_slack_at (w.u.toVal : ℝ) (w.tanh_w.tx.toVal : ℝ) with htanh_slack_def
  have h_tanh_slack_nn : 0 ≤ tanh_slack :=
    fpTanhFinite_slack_at_nn (w.u.toVal : ℝ) (w.tanh_w.tx.toVal : ℝ)
  -- 1-Lipschitz: |tanh(u_fp) - tanh(c·(...))| ≤ |u_fp - c·(...)|
  have h_tanh_lip : |Real.tanh ((w.u.toVal : ℝ)) -
      Real.tanh (cr * (xr + αr * (xr * xr * xr)))| ≤
      |((w.u.toVal : ℝ)) - cr * (xr + αr * (xr * xr * xr))| := by
    have := _root_.Flean.Real.tanh_lipschitz_one.bound (w.u.toVal : ℝ)
      (cr * (xr + αr * (xr * xr * xr)))
    linarith
  -- Combine: |t_fp - tanh(c·(...))| ≤ tanh_slack + ε_u
  have h_t_close : |((w.tanh_w.r.toVal : ℝ)) -
      Real.tanh (cr * (xr + αr * (xr * xr * xr)))| ≤ tanh_slack + ε_u B Bα Bc := by
    have h_split : ((w.tanh_w.r.toVal : ℝ)) -
        Real.tanh (cr * (xr + αr * (xr * xr * xr))) =
      (((w.tanh_w.r.toVal : ℝ)) - Real.tanh ((w.u.toVal : ℝ))) +
        (Real.tanh ((w.u.toVal : ℝ)) - Real.tanh (cr * (xr + αr * (xr * xr * xr)))) := by ring
    calc |((w.tanh_w.r.toVal : ℝ)) - Real.tanh (cr * (xr + αr * (xr * xr * xr)))|
        = |(((w.tanh_w.r.toVal : ℝ)) - Real.tanh ((w.u.toVal : ℝ))) +
            (Real.tanh ((w.u.toVal : ℝ)) -
              Real.tanh (cr * (xr + αr * (xr * xr * xr))))| := by rw [h_split]
      _ ≤ |((w.tanh_w.r.toVal : ℝ)) - Real.tanh ((w.u.toVal : ℝ))| +
            |Real.tanh ((w.u.toVal : ℝ)) -
              Real.tanh (cr * (xr + αr * (xr * xr * xr)))| := abs_add_le _ _
      _ ≤ tanh_slack + ε_u B Bα Bc := by linarith
  -- |t_fp| ≤ 1 + tanh_slack since |tanh(u_fp)| ≤ 1
  have h_t_mag : |((w.tanh_w.r.toVal : ℝ))| ≤ 1 + tanh_slack := by
    -- |tanh u| ≤ 1: derive from `tanh = 2σ(2u) - 1` and `0 < σ < 1`.
    have h_tanh_abs : |Real.tanh ((w.u.toVal : ℝ))| ≤ 1 := by
      rw [_root_.Real.tanh_eq_two_sigmoid_sub_one]
      have hsp : 0 < _root_.Real.sigmoid (2 * (w.u.toVal : ℝ)) :=
        _root_.Real.sigmoid_pos _
      have hsl : _root_.Real.sigmoid (2 * (w.u.toVal : ℝ)) ≤ 1 :=
        _root_.Real.sigmoid_le_one _
      rw [abs_le]; constructor <;> linarith
    have h_close_via_u : |((w.tanh_w.r.toVal : ℝ)) - Real.tanh ((w.u.toVal : ℝ))| ≤
        tanh_slack := h_tanh_close
    calc |((w.tanh_w.r.toVal : ℝ))|
        = |(((w.tanh_w.r.toVal : ℝ)) - Real.tanh ((w.u.toVal : ℝ))) +
            Real.tanh ((w.u.toVal : ℝ))| := by ring_nf
      _ ≤ |((w.tanh_w.r.toVal : ℝ)) - Real.tanh ((w.u.toVal : ℝ))| +
            |Real.tanh ((w.u.toVal : ℝ))| := abs_add_le _ _
      _ ≤ tanh_slack + 1 := by linarith
      _ = 1 + tanh_slack := by ring
  -- Step 7: opt = round(1 + t)
  have h_one_toVal : ((1 : FiniteFp).toVal : ℝ) = 1 := FiniteFp.toVal_one
  -- Restate normality with explicit `(1 : FiniteFp).toVal` for the error_or_zero API.
  have h_opt_nr' :
      isNormalRange (((1 : FiniteFp).toVal : ℝ) + (w.tanh_w.r.toVal : ℝ)) ∨
        ((1 : FiniteFp).toVal : ℝ) + (w.tanh_w.r.toVal : ℝ) = 0 := by
    rw [h_one_toVal]; exact h_opt_nr
  have h_opt_close := KahanSum.fpAdd_error_or_zero (R := ℝ) (1 : FiniteFp) w.tanh_w.r
    w.opt w.h_opt h_opt_nr'
  rw [h_one_toVal] at h_opt_close
  have h_one_plus_t_mag : |1 + ((w.tanh_w.r.toVal : ℝ))| ≤ 1 + (1 + tanh_slack) := by
    have := abs_add_le (1 : ℝ) ((w.tanh_w.r.toVal : ℝ))
    have h1 : |(1 : ℝ)| = 1 := abs_one
    linarith
  have h_opt_step : |(w.opt.toVal : ℝ) - (1 + (w.tanh_w.r.toVal : ℝ))| ≤
      η * (1 + (1 + tanh_slack)) := by
    refine le_trans h_opt_close ?_
    exact mul_le_mul_of_nonneg_left h_one_plus_t_mag hη_nn
  -- Combine to ε_opt
  have h_opt_close_final : |((w.opt.toVal : ℝ)) -
      (1 + Real.tanh (cr * (xr + αr * (xr * xr * xr))))| ≤
      η * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc) := by
    have h_split : ((w.opt.toVal : ℝ)) -
        (1 + Real.tanh (cr * (xr + αr * (xr * xr * xr)))) =
      ((w.opt.toVal : ℝ) - (1 + ((w.tanh_w.r.toVal : ℝ)))) +
        ((((w.tanh_w.r.toVal : ℝ))) -
          Real.tanh (cr * (xr + αr * (xr * xr * xr)))) := by ring
    calc |((w.opt.toVal : ℝ)) - (1 + Real.tanh (cr * (xr + αr * (xr * xr * xr))))|
        = |((w.opt.toVal : ℝ) - (1 + ((w.tanh_w.r.toVal : ℝ)))) +
            ((((w.tanh_w.r.toVal : ℝ))) -
              Real.tanh (cr * (xr + αr * (xr * xr * xr))))| := by rw [h_split]
      _ ≤ |((w.opt.toVal : ℝ)) - (1 + ((w.tanh_w.r.toVal : ℝ)))| +
            |(((w.tanh_w.r.toVal : ℝ))) -
              Real.tanh (cr * (xr + αr * (xr * xr * xr)))| := abs_add_le _ _
      _ ≤ η * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc) := by linarith
  -- |opt_fp| ≤ (1+η) · (1 + (1+tanh_slack))
  have h_opt_mag : |((w.opt.toVal : ℝ))| ≤ (1 + η) * (1 + (1 + tanh_slack)) := by
    have h_sum :
        |(w.opt.toVal : ℝ)| ≤
          |(w.opt.toVal : ℝ) - (1 + ((w.tanh_w.r.toVal : ℝ)))| +
            |1 + ((w.tanh_w.r.toVal : ℝ))| := by
      have := abs_add_le ((w.opt.toVal : ℝ) - (1 + ((w.tanh_w.r.toVal : ℝ))))
        (1 + ((w.tanh_w.r.toVal : ℝ)))
      have hrw : (w.opt.toVal : ℝ) - (1 + ((w.tanh_w.r.toVal : ℝ))) +
          (1 + ((w.tanh_w.r.toVal : ℝ))) = (w.opt.toVal : ℝ) := by ring
      rw [hrw] at this; exact this
    calc |((w.opt.toVal : ℝ))|
        ≤ |((w.opt.toVal : ℝ)) - (1 + ((w.tanh_w.r.toVal : ℝ)))| +
            |1 + ((w.tanh_w.r.toVal : ℝ))| := h_sum
      _ ≤ η * (1 + (1 + tanh_slack)) + (1 + (1 + tanh_slack)) := by linarith
      _ = (1 + η) * (1 + (1 + tanh_slack)) := by ring
  -- Step 8: hx = half · x
  have h_hx_close := KahanSum.fpMul_error_or_zero (R := ℝ) half x w.hx w.h_hx h_hx_nr
  have h_hr_xr_mag : |hr * xr| ≤ Bh * B := by
    rw [abs_mul]
    exact mul_le_mul hBh hB (abs_nonneg _) hBh_nn
  have h_hx_step : |(w.hx.toVal : ℝ) - hr * xr| ≤ η * (Bh * B) := by
    refine le_trans h_hx_close ?_
    exact mul_le_mul_of_nonneg_left h_hr_xr_mag hη_nn
  have h_hx_mag : |((w.hx.toVal : ℝ))| ≤ (1 + η) * Bh * B := by
    have h_sum :
        |(w.hx.toVal : ℝ)| ≤ |(w.hx.toVal : ℝ) - hr * xr| + |hr * xr| := by
      have := abs_add_le ((w.hx.toVal : ℝ) - hr * xr) (hr * xr)
      have hrw : (w.hx.toVal : ℝ) - hr * xr + hr * xr = (w.hx.toVal : ℝ) := by ring
      rw [hrw] at this; exact this
    calc |(w.hx.toVal : ℝ)|
        ≤ |(w.hx.toVal : ℝ) - hr * xr| + |hr * xr| := h_sum
      _ ≤ η * (Bh * B) + Bh * B := by linarith
      _ = (1 + η) * Bh * B := by ring
  -- Step 9: r = hx · opt — final step rounding error.
  have h_r_close_step_eq := KahanSum.fpMul_error_or_zero (R := ℝ) w.hx w.opt w.r
    w.h_r h_r_nr
  -- Apply the modular theorem
  have h_modular := fpGeluFinite_with_close_modular half α c x w
    ((η : ℝ) * (Bh * B)) h_hx_step
    ((η : ℝ) * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc))
      h_opt_close_final
    h_r_close_step_eq
    ((1 + η) * Bh * B) h_hx_mag (by positivity)
    ((1 + η) * (1 + (1 + tanh_slack)))
    h_opt_mag (by
      have := h_tanh_slack_nn
      positivity)
  -- The modular theorem produces:
  --   η · ((1+η)·Bh·B · (1+η)·(1+(1+tanh_slack))) + ...
  --     + |hr · xr| · ε_opt + (η·Bh·B) · ε_opt
  -- Loosen `|hr · xr|` to `Bh · B`.
  have hMxc_nn : 0 ≤ M_x_cu B := by show 0 ≤ (1 + (η : ℝ))^2 * B^3; positivity
  have hεxc_nn : 0 ≤ ε_x_cu B := by show 0 ≤ (η : ℝ) * (2 + η) * B^3; positivity
  have hMaxc_nn : 0 ≤ M_ax_cu B Bα := by
    show 0 ≤ (1 + (η : ℝ))^3 * Bα * B^3; positivity
  have hεaxc_nn : 0 ≤ ε_ax_cu B Bα := by
    show 0 ≤ (η : ℝ) * (1 + η)^2 * Bα * B^3 + Bα * ε_x_cu B; positivity
  have hMinner_nn : 0 ≤ M_inner B Bα := by
    show 0 ≤ (1 + (η : ℝ)) * (B + M_ax_cu B Bα); positivity
  have hεinner_nn : 0 ≤ ε_inner B Bα := by
    show 0 ≤ (η : ℝ) * (B + M_ax_cu B Bα) + ε_ax_cu B Bα; positivity
  have hεu_nn : 0 ≤ ε_u B Bα Bc := by
    show 0 ≤ (η : ℝ) * Bc * M_inner B Bα + Bc * ε_inner B Bα; positivity
  have h_ε_opt_v_nn :
      0 ≤ (η : ℝ) * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc) := by
    have h_ts := h_tanh_slack_nn
    have h1 : 0 ≤ 1 + (1 + tanh_slack) := by linarith
    have hη_step : 0 ≤ (η : ℝ) * (1 + (1 + tanh_slack)) := mul_nonneg hη_nn h1
    linarith
  have h_swap : |hr * xr| *
      ((η : ℝ) * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc)) ≤
      Bh * B *
      ((η : ℝ) * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc)) :=
    mul_le_mul_of_nonneg_right h_hr_xr_mag h_ε_opt_v_nn
  -- Now bound the modular result using the loose `Bh · B`, then identify with
  -- `fpGeluFinite_slack_at` (the `let`-let bindings unfold definitionally).
  show |((w.r.toVal : ℝ)) - Real.geluTanhApprox hr cr αr xr| ≤
      fpGeluFinite_slack_at B Bh Bα Bc (w.tanh_w.tx.toVal : ℝ) (w.u.toVal : ℝ)
  show |((w.r.toVal : ℝ)) - Real.geluTanhApprox hr cr αr xr| ≤
      (η : ℝ) * ((1 + η) * Bh * B * ((1 + η) * (1 + (1 + tanh_slack)))) +
        (η : ℝ) * (Bh * B) * ((1 + η) * (1 + (1 + tanh_slack))) +
        Bh * B *
          ((η : ℝ) * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc)) +
        (η : ℝ) * (Bh * B) *
          ((η : ℝ) * (1 + (1 + tanh_slack)) + (tanh_slack + ε_u B Bα Bc))
  linarith [h_modular]

end Flean
