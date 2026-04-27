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
pair plus magnitude bounds and produces the final-step triangle. In
practice, downstream consumers derive `ε_hx` directly from
`KahanSum.fpMul_error_or_zero` applied to `w.h_hx`, and derive `ε_opt`
by chaining 8 step lemmas plus `fpTanhFinite_close`. The full chain is
mechanical but lengthy.

Tight closed-form slack from `(xr, αr, cr, hr, η)` alone is left as a
future tightening: ~400 LOC of magnitude tracking through 9 ops, not
strictly needed for Wisp's per-element backward bridge prototype which
just needs *a* slack witness. -/

end Flean
