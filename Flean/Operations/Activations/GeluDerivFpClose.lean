import Flean.Operations.Activations.GeluDerivFp
import Flean.Operations.Activations.GeluFpClose
import Flean.Operations.KahanSum

/-!
# Closeness Bound for FP GeLU Derivative (tanh approximation)

Composes the gelu forward intermediates (`GeluFpIntermediates` from
`GeluFpClose`) with the 9 derivative-only FP steps (10–18) of
`fpGeluDerivFinite_with`, against the math reference
`Real.geluTanhApprox_deriv`.

## Pipeline (as in `GeluDerivFp.lean`)

```
1–8: forward gelu chain (provides x_sq, x_cu, ax_cu, inner, u, t, opt, hx)
10:  sq = t · t                  (squared tanh)
11:  sech_sq = 1 − sq             (1 − tanh²(u))
12:  half_opt = half · opt        (= half · (1 + tanh(u)))
13:  three_a_xsq = three_α · x²  (caller supplies three_α ≈ 3·α)
14:  one_plus_3axsq = 1 + three_a_xsq
15:  up = c · one_plus_3axsq      (= u'(x) ≈ c·(1 + 3α·x²))
16:  hxd = hx · sech_sq           (= half · x · (1 − tanh²(u)))
17:  hxdu = hxd · up
18:  r = half_opt + hxdu          (final result)
```

## Slack expression

The slack is a layered cascade of cross-product / triangle bounds.
Each derivative-only step contributes a `(1+η)`-magnification of the
prior magnitudes plus a triangle-inequality coupling to the math
reference.  The forward bounds (`tanh_slack`, `ε_u`, `M_x_sq`, etc.)
plug in directly from `GeluFpIntermediates`.
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeNearest ℝ] [RModeSticky ℝ] [ExpApprox] [ExpApproxSound]

/-! ## Slack expression and component bounds -/

/-! ## Forward closed-form magnitude/error helpers

Named noncomputable defs for the closed-form forward bounds (matching
`GeluFpIntermediates`'s fields in their explicit RHS form).  Using
named defs (rather than inline `let`s in the slack expression) lets
the closeness proof's `set`-bound abbreviations match by `rfl`. -/

/-- Forward-magnitude bound on `|t_fp| = |w.tanh_w.r.toVal|`. -/
noncomputable def gelu_M_t (tx_real u_fp_real : ℝ) : ℝ :=
  1 + fpTanhFinite_slack_at u_fp_real tx_real

/-- Forward-magnitude bound on `|opt_fp|`. -/
noncomputable def gelu_M_opt (tx_real u_fp_real : ℝ) : ℝ :=
  (1 + (η : ℝ)) * (1 + gelu_M_t tx_real u_fp_real)

/-- Forward-magnitude bound on `|hx_fp|`. -/
noncomputable def gelu_M_hx (B Bh : ℝ) : ℝ := (1 + (η : ℝ)) * Bh * B

/-- Forward-magnitude bound on `|x_sq_fp|`. -/
noncomputable def gelu_M_x_sq (B : ℝ) : ℝ := (1 + (η : ℝ)) * (B * B)

/-- Forward-error bound on `|t_fp − tanh(c·(x+α·x³))|`. -/
noncomputable def gelu_ε_t (B Bα Bc tx_real u_fp_real : ℝ) : ℝ :=
  fpTanhFinite_slack_at u_fp_real tx_real + ε_u B Bα Bc

/-- Forward-error bound on `|opt_fp − (1 + tanh(c·(x+α·x³)))|`. -/
noncomputable def gelu_ε_opt (B Bα Bc tx_real u_fp_real : ℝ) : ℝ :=
  (η : ℝ) * (1 + gelu_M_t tx_real u_fp_real) + gelu_ε_t B Bα Bc tx_real u_fp_real

/-- Forward-error bound on `|hx_fp − half·x|`. -/
noncomputable def gelu_ε_hx (B Bh : ℝ) : ℝ := (η : ℝ) * (Bh * B)

/-- Forward-error bound on `|x_sq_fp − x²|`. -/
noncomputable def gelu_ε_x_sq (B : ℝ) : ℝ := (η : ℝ) * (B * B)

/-! ### Derivative-only step bounds (steps 10–17) -/

/-- Closeness of `sq_fp` against `tanh²(c·(x+α·x³))`. -/
noncomputable def gelu_ε_sq (B Bα Bc tx_real u_fp_real : ℝ) : ℝ :=
  let M_t := gelu_M_t tx_real u_fp_real
  let ε_t := gelu_ε_t B Bα Bc tx_real u_fp_real
  (η : ℝ) * M_t * M_t + ε_t * (M_t + 1)

/-- Magnitude of `sq_fp`. -/
noncomputable def gelu_M_sq (tx_real u_fp_real : ℝ) : ℝ :=
  (1 + (η : ℝ)) * gelu_M_t tx_real u_fp_real * gelu_M_t tx_real u_fp_real

/-- Closeness of `sech_sq_fp` against `1 − tanh²(c·(x+α·x³))`. -/
noncomputable def gelu_ε_sech_sq (B Bα Bc tx_real u_fp_real : ℝ) : ℝ :=
  (η : ℝ) * (1 + gelu_M_sq tx_real u_fp_real) +
    gelu_ε_sq B Bα Bc tx_real u_fp_real

/-- Magnitude of `sech_sq_fp`. -/
noncomputable def gelu_M_sech_sq (tx_real u_fp_real : ℝ) : ℝ :=
  (1 + (η : ℝ)) * (1 + gelu_M_sq tx_real u_fp_real)

/-- Closeness of `half_opt_fp` against `half · (1 + tanh(c·(x+α·x³)))`. -/
noncomputable def gelu_ε_half_opt (B Bh Bα Bc tx_real u_fp_real : ℝ) : ℝ :=
  (η : ℝ) * Bh * gelu_M_opt tx_real u_fp_real +
    Bh * gelu_ε_opt B Bα Bc tx_real u_fp_real

/-- Magnitude of `half_opt_fp`. -/
noncomputable def gelu_M_half_opt (Bh tx_real u_fp_real : ℝ) : ℝ :=
  (1 + (η : ℝ)) * Bh * gelu_M_opt tx_real u_fp_real

/-- Closeness of `three_a_xsq_fp` against `3·α · x²`. -/
noncomputable def gelu_ε_three_a_xsq (B B3α ε_3α : ℝ) : ℝ :=
  (η : ℝ) * B3α * gelu_M_x_sq B + B3α * gelu_ε_x_sq B + ε_3α * (B * B)

/-- Magnitude of `three_a_xsq_fp`. -/
noncomputable def gelu_M_three_a_xsq (B B3α : ℝ) : ℝ :=
  (1 + (η : ℝ)) * B3α * gelu_M_x_sq B

/-- Closeness of `one_plus_3axsq_fp` against `1 + 3·α · x²`. -/
noncomputable def gelu_ε_one_plus (B B3α ε_3α : ℝ) : ℝ :=
  (η : ℝ) * (1 + gelu_M_three_a_xsq B B3α) +
    gelu_ε_three_a_xsq B B3α ε_3α

/-- Magnitude of `one_plus_3axsq_fp`. -/
noncomputable def gelu_M_one_plus (B B3α : ℝ) : ℝ :=
  (1 + (η : ℝ)) * (1 + gelu_M_three_a_xsq B B3α)

/-- Closeness of `up_fp` against `c · (1 + 3·α · x²)`. -/
noncomputable def gelu_ε_up (B B3α Bc ε_3α : ℝ) : ℝ :=
  (η : ℝ) * Bc * gelu_M_one_plus B B3α + Bc * gelu_ε_one_plus B B3α ε_3α

/-- Magnitude of `up_fp`. -/
noncomputable def gelu_M_up (B B3α Bc : ℝ) : ℝ :=
  (1 + (η : ℝ)) * Bc * gelu_M_one_plus B B3α

/-- Closeness of `hxd_fp` against `half · x · (1 − tanh²)`. -/
noncomputable def gelu_ε_hxd (B Bh Bα Bc tx_real u_fp_real : ℝ) : ℝ :=
  (η : ℝ) * gelu_M_hx B Bh * gelu_M_sech_sq tx_real u_fp_real +
    gelu_ε_hx B Bh * gelu_M_sech_sq tx_real u_fp_real +
    Bh * B * gelu_ε_sech_sq B Bα Bc tx_real u_fp_real

/-- Magnitude of `hxd_fp`. -/
noncomputable def gelu_M_hxd (B Bh tx_real u_fp_real : ℝ) : ℝ :=
  (1 + (η : ℝ)) * gelu_M_hx B Bh * gelu_M_sech_sq tx_real u_fp_real

/-- Closeness of `hxdu_fp` against `half · x · (1 − tanh²) · u'`. -/
noncomputable def gelu_ε_hxdu (B Bh Bα B3α Bc ε_3α tx_real u_fp_real : ℝ) : ℝ :=
  (η : ℝ) * gelu_M_hxd B Bh tx_real u_fp_real *
      gelu_M_up B B3α Bc +
    gelu_ε_hxd B Bh Bα Bc tx_real u_fp_real * gelu_M_up B B3α Bc +
    Bh * B * gelu_ε_up B B3α Bc ε_3α

/-- Magnitude of `hxdu_fp`. -/
noncomputable def gelu_M_hxdu (B Bh B3α Bc tx_real u_fp_real : ℝ) : ℝ :=
  (1 + (η : ℝ)) * gelu_M_hxd B Bh tx_real u_fp_real *
    gelu_M_up B B3α Bc

/-- Tight closed-form slack expression for `fpGeluDerivFinite_with`.

Bounds `|r_fp − geluTanhApprox_deriv| ≤ this`.  Final-add rounding
plus the two cross-term closeness contributions (`half_opt` and
`hxdu`) against the math reference. -/
noncomputable def fpGeluDerivFinite_slack_at
    (B Bh Bα B3α Bc ε_3α tx_real u_fp_real : ℝ) : ℝ :=
  (η : ℝ) * (gelu_M_half_opt Bh tx_real u_fp_real +
      gelu_M_hxdu B Bh B3α Bc tx_real u_fp_real) +
    gelu_ε_half_opt B Bh Bα Bc tx_real u_fp_real +
    gelu_ε_hxdu B Bh Bα B3α Bc ε_3α tx_real u_fp_real

/-! ## Closeness lemma -/

set_option maxHeartbeats 1600000 in
/-- **Tight closeness lemma for the FP gelu derivative kernel.**

Composes `fpGeluFinite_close_intermediates` (forward intermediates)
with 9 new step rounding witnesses + a layered cross-product
decomposition for the derivative-only chain (steps 10–18) plus a
final triangle against `Real.geluTanhApprox_deriv`. -/
theorem fpGeluDerivFinite_close
    (half α three_α c x : FiniteFp)
    (w : GeluDerivFpWitness half α three_α c x)
    -- Magnitude bounds on inputs
    {B Bh Bα B3α Bc ε_3α : ℝ}
    (hB : |((x.toVal : ℝ))| ≤ B) (hB_nn : 0 ≤ B)
    (hBh : |((half.toVal : ℝ))| ≤ Bh) (hBh_nn : 0 ≤ Bh)
    (hBα : |((α.toVal : ℝ))| ≤ Bα) (hBα_nn : 0 ≤ Bα)
    (hB3α : |((three_α.toVal : ℝ))| ≤ B3α) (hB3α_nn : 0 ≤ B3α)
    (hBc : |((c.toVal : ℝ))| ≤ Bc) (hBc_nn : 0 ≤ Bc)
    (h_ε3α : |((three_α.toVal : ℝ)) - 3 * (α.toVal : ℝ)| ≤ ε_3α)
    (h_ε3α_nn : 0 ≤ ε_3α)
    -- Forward polynomial-chain normal-range hypotheses (steps 1–8)
    (h_sq_nr : isNormalRange ((x.toVal : ℝ) * (x.toVal : ℝ)) ∨
               (x.toVal : ℝ) * (x.toVal : ℝ) = 0)
    (h_cu_nr : isNormalRange ((w.fwd.x_sq.toVal : ℝ) * (x.toVal : ℝ)) ∨
               (w.fwd.x_sq.toVal : ℝ) * (x.toVal : ℝ) = 0)
    (h_ax_cu_nr : isNormalRange ((α.toVal : ℝ) * (w.fwd.x_cu.toVal : ℝ)) ∨
                  (α.toVal : ℝ) * (w.fwd.x_cu.toVal : ℝ) = 0)
    (h_inner_nr : isNormalRange ((x.toVal : ℝ) + (w.fwd.ax_cu.toVal : ℝ)) ∨
                  (x.toVal : ℝ) + (w.fwd.ax_cu.toVal : ℝ) = 0)
    (h_u_nr : isNormalRange ((c.toVal : ℝ) * (w.fwd.inner.toVal : ℝ)) ∨
              (c.toVal : ℝ) * (w.fwd.inner.toVal : ℝ) = 0)
    (h_opt_nr : isNormalRange ((1 : ℝ) + (w.fwd.tanh_w.r.toVal : ℝ)) ∨
                (1 : ℝ) + (w.fwd.tanh_w.r.toVal : ℝ) = 0)
    (h_hx_nr : isNormalRange ((half.toVal : ℝ) * (x.toVal : ℝ)) ∨
               (half.toVal : ℝ) * (x.toVal : ℝ) = 0)
    -- Tanh's normal-range hypotheses
    (h_dbl1_nr : isNormalRange ((w.fwd.u.toVal : ℝ) + (w.fwd.u.toVal : ℝ)) ∨
                 (w.fwd.u.toVal : ℝ) + (w.fwd.u.toVal : ℝ) = 0)
    (her_normal : isNormalRange (Real.exp (-((w.fwd.tanh_w.tx.toVal : ℝ)))))
    (h_d_normal : isNormalRange ((1 : ℝ) + (w.fwd.tanh_w.sig.e.toVal : ℝ)) ∨
                  ((1 : ℝ) + (w.fwd.tanh_w.sig.e.toVal : ℝ) = 0))
    (h_sig_r_normal : isNormalRange ((1 : ℝ) / (w.fwd.tanh_w.sig.d.toVal : ℝ)) ∨
                      ((1 : ℝ) / (w.fwd.tanh_w.sig.d.toVal : ℝ) = 0))
    (hd_m_ne : w.fwd.tanh_w.sig.d.m ≠ 0)
    (h_dbl2_nr : isNormalRange
                  ((w.fwd.tanh_w.sig.r.toVal : ℝ) + (w.fwd.tanh_w.sig.r.toVal : ℝ)) ∨
                 ((w.fwd.tanh_w.sig.r.toVal : ℝ) + (w.fwd.tanh_w.sig.r.toVal : ℝ) = 0))
    (h_sub_nr : isNormalRange ((w.fwd.tanh_w.tsx.toVal : ℝ) - (1 : ℝ)) ∨
                ((w.fwd.tanh_w.tsx.toVal : ℝ) - (1 : ℝ) = 0))
    -- Derivative-only step normal-range hypotheses (steps 10–18)
    (h_sq_d_nr : isNormalRange
                  ((w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ)) ∨
                 (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ) = 0)
    (h_sech_sq_nr : isNormalRange ((1 : ℝ) - (w.sq.toVal : ℝ)) ∨
                    (1 : ℝ) - (w.sq.toVal : ℝ) = 0)
    (h_half_opt_nr : isNormalRange ((half.toVal : ℝ) * (w.fwd.opt.toVal : ℝ)) ∨
                     (half.toVal : ℝ) * (w.fwd.opt.toVal : ℝ) = 0)
    (h_three_a_xsq_nr : isNormalRange
                        ((three_α.toVal : ℝ) * (w.fwd.x_sq.toVal : ℝ)) ∨
                       (three_α.toVal : ℝ) * (w.fwd.x_sq.toVal : ℝ) = 0)
    (h_one_plus_nr : isNormalRange ((1 : ℝ) + (w.three_a_xsq.toVal : ℝ)) ∨
                     (1 : ℝ) + (w.three_a_xsq.toVal : ℝ) = 0)
    (h_up_nr : isNormalRange ((c.toVal : ℝ) * (w.one_plus_3axsq.toVal : ℝ)) ∨
               (c.toVal : ℝ) * (w.one_plus_3axsq.toVal : ℝ) = 0)
    (h_hxd_nr : isNormalRange ((w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)) ∨
                (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ) = 0)
    (h_hxdu_nr : isNormalRange ((w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)) ∨
                 (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ) = 0)
    (h_r_nr : isNormalRange ((w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ)) ∨
              (w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ) = 0) :
    |((w.r.toVal : ℝ)) - Real.geluTanhApprox_deriv (half.toVal : ℝ)
        (c.toVal : ℝ) (α.toVal : ℝ) (x.toVal : ℝ)| ≤
      fpGeluDerivFinite_slack_at B Bh Bα B3α Bc ε_3α
        (w.fwd.tanh_w.tx.toVal : ℝ) (w.fwd.u.toVal : ℝ) := by
  -- Pull forward intermediates struct.
  let inter := fpGeluFinite_close_intermediates half α c x w.fwd
    hB hB_nn hBh hBh_nn hBα hBα_nn hBc hBc_nn h_sq_nr h_cu_nr h_ax_cu_nr
    h_inner_nr h_u_nr h_opt_nr h_hx_nr h_dbl1_nr her_normal h_d_normal
    h_sig_r_normal hd_m_ne h_dbl2_nr h_sub_nr
  -- Setup short names for ℝ-valued projections.
  set xr : ℝ := (x.toVal : ℝ) with hxr_def
  set hr : ℝ := (half.toVal : ℝ) with hhr_def
  set αr : ℝ := (α.toVal : ℝ) with hαr_def
  set t3αr : ℝ := (three_α.toVal : ℝ) with ht3αr_def
  set cr : ℝ := (c.toVal : ℝ) with hcr_def
  -- η bounds
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have h1η_nn : (0 : ℝ) ≤ 1 + η := by linarith
  -- Tanh slack abbrevs.
  set tanh_slack : ℝ :=
    fpTanhFinite_slack_at (w.fwd.u.toVal : ℝ) (w.fwd.tanh_w.tx.toVal : ℝ)
    with htanh_slack_def
  have h_tanh_slack_nn : 0 ≤ tanh_slack :=
    fpTanhFinite_slack_at_nn (w.fwd.u.toVal : ℝ) (w.fwd.tanh_w.tx.toVal : ℝ)
  -- Forward closed-form magnitudes (read from struct, lifted to lets).
  set M_t : ℝ := 1 + tanh_slack with hM_t_def
  set M_opt : ℝ := (1 + η) * (1 + M_t) with hM_opt_def
  set M_hx : ℝ := (1 + η) * Bh * B with hM_hx_def
  set M_x_sq : ℝ := (1 + η) * (B * B) with hM_x_sq_def
  set ε_t : ℝ := tanh_slack + ε_u B Bα Bc with hε_t_def
  set ε_opt : ℝ := (η : ℝ) * (1 + M_t) + ε_t with hε_opt_def
  set ε_hx : ℝ := (η : ℝ) * (Bh * B) with hε_hx_def
  set ε_x_sq : ℝ := (η : ℝ) * (B * B) with hε_x_sq_def
  have hM_t_nn : 0 ≤ M_t := by show 0 ≤ 1 + tanh_slack; linarith
  have hM_opt_nn : 0 ≤ M_opt := by
    show 0 ≤ (1 + η) * (1 + M_t); positivity
  have hM_hx_nn : 0 ≤ M_hx := by
    show 0 ≤ (1 + η) * Bh * B; positivity
  have hM_x_sq_nn : 0 ≤ M_x_sq := by
    show 0 ≤ (1 + η) * (B * B); positivity
  have hε_t_nn : 0 ≤ ε_t := by
    show 0 ≤ tanh_slack + ε_u B Bα Bc
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
    linarith
  have hε_opt_nn : 0 ≤ ε_opt := by
    show 0 ≤ (η : ℝ) * (1 + M_t) + ε_t
    have h1 : 0 ≤ 1 + M_t := by linarith
    have hηM : 0 ≤ (η : ℝ) * (1 + M_t) := mul_nonneg hη_nn h1
    linarith
  have hε_hx_nn : 0 ≤ ε_hx := by
    show 0 ≤ (η : ℝ) * (Bh * B); positivity
  have hε_x_sq_nn : 0 ≤ ε_x_sq := by
    show 0 ≤ (η : ℝ) * (B * B); positivity
  -- Pull forward intermediate ε's and M's from the struct.
  -- inter.hε_t  : |t_fp - tanh(c·(x+α·x³))| ≤ tanh_slack + ε_u B Bα Bc = ε_t
  -- inter.hε_opt: ≤ ε_opt
  -- inter.hε_hx : ≤ ε_hx (form: |hx_fp - half·x| ≤ η·(Bh·B))
  -- inter.hε_x_sq: |x_sq_fp - x²| ≤ η·(B·B) = ε_x_sq
  -- inter.hM_t  : |t_fp| ≤ M_t
  -- inter.hM_opt: |opt_fp| ≤ M_opt
  -- inter.hM_hx : |hx_fp| ≤ M_hx
  -- inter.hM_x_sq: |x_sq_fp| ≤ M_x_sq
  -- (We re-bind via show/have to make types match nicely.)
  have h_ε_t : |((w.fwd.tanh_w.r.toVal : ℝ)) -
      Real.tanh (geluPolyArg αr cr xr)| ≤ ε_t := inter.hε_t
  have h_M_t : |((w.fwd.tanh_w.r.toVal : ℝ))| ≤ M_t := inter.hM_t
  have h_ε_opt : |((w.fwd.opt.toVal : ℝ)) -
      (1 + Real.tanh (geluPolyArg αr cr xr))| ≤ ε_opt := inter.hε_opt
  have h_M_opt : |((w.fwd.opt.toVal : ℝ))| ≤ M_opt := inter.hM_opt
  have h_ε_hx : |((w.fwd.hx.toVal : ℝ)) - hr * xr| ≤ ε_hx := inter.hε_hx
  have h_M_hx : |((w.fwd.hx.toVal : ℝ))| ≤ M_hx := inter.hM_hx
  have h_ε_x_sq : |((w.fwd.x_sq.toVal : ℝ)) - xr * xr| ≤ ε_x_sq := inter.hε_x_sq
  have h_M_x_sq : |((w.fwd.x_sq.toVal : ℝ))| ≤ M_x_sq := inter.hM_x_sq
  -- |tanh(u_real)| ≤ 1 (from tanh = 2σ(2u) − 1 + 0 < σ < 1).
  have h_tanh_abs_le_one : |Real.tanh (geluPolyArg αr cr xr)| ≤ 1 := by
    rw [_root_.Real.tanh_eq_two_sigmoid_sub_one]
    have hsp := _root_.Real.sigmoid_pos (2 * geluPolyArg αr cr xr)
    have hsl := _root_.Real.sigmoid_le_one (2 * geluPolyArg αr cr xr)
    rw [abs_le]; constructor <;> linarith
  -- Step 10: sq = t · t. ε_step = η · |t·t|, then add tanh² coupling.
  have h_sq_step :=
    KahanSum.fpMul_error_or_zero (R := ℝ) w.fwd.tanh_w.r w.fwd.tanh_w.r w.sq w.hsq
      h_sq_d_nr
  have h_t2_abs : |((w.fwd.tanh_w.r.toVal : ℝ)) * (w.fwd.tanh_w.r.toVal : ℝ)| ≤
      M_t * M_t := by
    rw [abs_mul]; exact mul_le_mul h_M_t h_M_t (abs_nonneg _) hM_t_nn
  -- |sq_fp - t²| ≤ η · M_t²
  have h_sq_close_t2 : |((w.sq.toVal : ℝ)) -
      (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ)| ≤
      (η : ℝ) * (M_t * M_t) := by
    refine le_trans h_sq_step ?_
    exact mul_le_mul_of_nonneg_left h_t2_abs hη_nn
  -- |t² - tanh²(u)| ≤ ε_t · (M_t + 1) (factor: |t-tanh(u)|·|t+tanh(u)|).
  have h_t2_minus_tanh2 :
      |((w.fwd.tanh_w.r.toVal : ℝ)) * (w.fwd.tanh_w.r.toVal : ℝ) -
        Real.tanh (geluPolyArg αr cr xr) ^ 2| ≤
      ε_t * (M_t + 1) := by
    have h_factor : ((w.fwd.tanh_w.r.toVal : ℝ)) * (w.fwd.tanh_w.r.toVal : ℝ) -
        Real.tanh (geluPolyArg αr cr xr) ^ 2 =
      ((w.fwd.tanh_w.r.toVal : ℝ) - Real.tanh (geluPolyArg αr cr xr)) *
        ((w.fwd.tanh_w.r.toVal : ℝ) + Real.tanh (geluPolyArg αr cr xr)) := by
      ring
    rw [h_factor, abs_mul]
    have h_sum_abs : |((w.fwd.tanh_w.r.toVal : ℝ)) +
        Real.tanh (geluPolyArg αr cr xr)| ≤ M_t + 1 := by
      calc |((w.fwd.tanh_w.r.toVal : ℝ)) +
          Real.tanh (geluPolyArg αr cr xr)|
          ≤ |((w.fwd.tanh_w.r.toVal : ℝ))| +
              |Real.tanh (geluPolyArg αr cr xr)| := abs_add_le _ _
        _ ≤ M_t + 1 := by linarith
    have h_diff_abs : |((w.fwd.tanh_w.r.toVal : ℝ)) -
        Real.tanh (geluPolyArg αr cr xr)| ≤ ε_t := h_ε_t
    exact mul_le_mul h_diff_abs h_sum_abs (abs_nonneg _) hε_t_nn
  -- Combine: |sq_fp - tanh²(u)| ≤ η·M_t² + ε_t·(M_t+1) =: ε_sq_real
  set ε_sq_real : ℝ := (η : ℝ) * (M_t * M_t) + ε_t * (M_t + 1)
    with hε_sq_real_def
  have h_ε_sq_real : |((w.sq.toVal : ℝ)) -
      Real.tanh (geluPolyArg αr cr xr) ^ 2| ≤ ε_sq_real := by
    have h_split : ((w.sq.toVal : ℝ)) -
        Real.tanh (geluPolyArg αr cr xr) ^ 2 =
      (((w.sq.toVal : ℝ)) -
        (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ)) +
      ((w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ) -
        Real.tanh (geluPolyArg αr cr xr) ^ 2) := by ring
    show |((w.sq.toVal : ℝ)) - Real.tanh (geluPolyArg αr cr xr) ^ 2| ≤
      (η : ℝ) * (M_t * M_t) + ε_t * (M_t + 1)
    calc |((w.sq.toVal : ℝ)) - Real.tanh (geluPolyArg αr cr xr) ^ 2|
        = |(((w.sq.toVal : ℝ)) -
            (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ)) +
          ((w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ) -
            Real.tanh (geluPolyArg αr cr xr) ^ 2)| := by rw [h_split]
      _ ≤ |((w.sq.toVal : ℝ)) -
            (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ)| +
          |((w.fwd.tanh_w.r.toVal : ℝ)) * (w.fwd.tanh_w.r.toVal : ℝ) -
            Real.tanh (geluPolyArg αr cr xr) ^ 2| := abs_add_le _ _
      _ ≤ (η : ℝ) * (M_t * M_t) + ε_t * (M_t + 1) := by linarith
  set M_sq : ℝ := (1 + η) * M_t * M_t with hM_sq_def
  have hM_sq_nn : 0 ≤ M_sq := by show 0 ≤ (1 + η) * M_t * M_t; positivity
  have h_M_sq : |((w.sq.toVal : ℝ))| ≤ M_sq := by
    have h_sum :
        |((w.sq.toVal : ℝ))| ≤
          |((w.sq.toVal : ℝ)) -
            (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ)| +
          |((w.fwd.tanh_w.r.toVal : ℝ)) * (w.fwd.tanh_w.r.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.sq.toVal : ℝ)) -
          (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ))
        ((w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ))
      have hrw : ((w.sq.toVal : ℝ)) -
          (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ) +
          (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ) =
          ((w.sq.toVal : ℝ)) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.sq.toVal : ℝ))| ≤ (1 + η) * M_t * M_t
    calc |((w.sq.toVal : ℝ))|
        ≤ |((w.sq.toVal : ℝ)) -
            (w.fwd.tanh_w.r.toVal : ℝ) * (w.fwd.tanh_w.r.toVal : ℝ)| +
          |((w.fwd.tanh_w.r.toVal : ℝ)) * (w.fwd.tanh_w.r.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (M_t * M_t) + M_t * M_t := by linarith
      _ = (1 + η) * M_t * M_t := by ring
  -- Step 11: sech_sq = 1 - sq.
  have h_one_toVal : ((1 : FiniteFp).toVal : ℝ) = 1 := FiniteFp.toVal_one
  have h_sech_sq_nr' :
      isNormalRange (((1 : FiniteFp).toVal : ℝ) - (w.sq.toVal : ℝ)) ∨
        ((1 : FiniteFp).toVal : ℝ) - (w.sq.toVal : ℝ) = 0 := by
    rw [h_one_toVal]; exact h_sech_sq_nr
  have h_sech_step :=
    KahanSum.fpSub_error_or_zero (R := ℝ) (1 : FiniteFp) w.sq w.sech_sq
      w.hsech_sq h_sech_sq_nr'
  rw [h_one_toVal] at h_sech_step
  -- |sech_sq_fp - (1 - sq_fp)| ≤ η · |1 - sq_fp| ≤ η · (1 + M_sq)
  have h_one_minus_sq_abs : |1 - ((w.sq.toVal : ℝ))| ≤ 1 + M_sq := by
    have hadd := abs_add_le (1 : ℝ) (-((w.sq.toVal : ℝ)))
    have h1 : |(1 : ℝ)| = 1 := abs_one
    have hneg : |-((w.sq.toVal : ℝ))| = |((w.sq.toVal : ℝ))| := abs_neg _
    have hrw : |1 - (w.sq.toVal : ℝ)| = |1 + (-(w.sq.toVal : ℝ))| := by ring_nf
    rw [hrw]
    calc |1 + (-(w.sq.toVal : ℝ))|
        ≤ |(1 : ℝ)| + |-((w.sq.toVal : ℝ))| := abs_add_le _ _
      _ = 1 + |((w.sq.toVal : ℝ))| := by rw [h1, hneg]
      _ ≤ 1 + M_sq := by linarith
  have h_sech_step_loose : |((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ))| ≤
      (η : ℝ) * (1 + M_sq) := by
    refine le_trans h_sech_step ?_
    exact mul_le_mul_of_nonneg_left h_one_minus_sq_abs hη_nn
  set ε_sech_sq_real : ℝ := (η : ℝ) * (1 + M_sq) + ε_sq_real
    with hε_sech_sq_real_def
  -- Closeness vs (1 - tanh²(u))
  have h_ε_sech_sq_real : |((w.sech_sq.toVal : ℝ)) -
      (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| ≤ ε_sech_sq_real := by
    have h_split : ((w.sech_sq.toVal : ℝ)) -
        (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) =
      (((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ))) +
      ((1 - (w.sq.toVal : ℝ)) -
        (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) := by ring
    have h_inner_eq : (1 - (w.sq.toVal : ℝ)) -
        (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) =
      Real.tanh (geluPolyArg αr cr xr) ^ 2 - (w.sq.toVal : ℝ) := by ring
    have h_inner_abs : |(1 - (w.sq.toVal : ℝ)) -
        (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| ≤ ε_sq_real := by
      rw [h_inner_eq]
      have h_neg : Real.tanh (geluPolyArg αr cr xr) ^ 2 - (w.sq.toVal : ℝ) =
          -((w.sq.toVal : ℝ) - Real.tanh (geluPolyArg αr cr xr) ^ 2) := by
        ring
      rw [h_neg, abs_neg]
      exact h_ε_sq_real
    show |((w.sech_sq.toVal : ℝ)) -
        (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| ≤
      (η : ℝ) * (1 + M_sq) + ε_sq_real
    calc |((w.sech_sq.toVal : ℝ)) -
            (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)|
        = |(((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ))) +
            ((1 - (w.sq.toVal : ℝ)) -
              (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2))| := by
            rw [h_split]
      _ ≤ |((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ))| +
          |(1 - (w.sq.toVal : ℝ)) -
            (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| :=
            abs_add_le _ _
      _ ≤ (η : ℝ) * (1 + M_sq) + ε_sq_real := by linarith
  set M_sech_sq : ℝ := (1 + η) * (1 + M_sq) with hM_sech_sq_def
  have hM_sech_sq_nn : 0 ≤ M_sech_sq := by
    show 0 ≤ (1 + η) * (1 + M_sq); positivity
  have h_M_sech_sq : |((w.sech_sq.toVal : ℝ))| ≤ M_sech_sq := by
    have h_sum :
        |((w.sech_sq.toVal : ℝ))| ≤
          |((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ))| +
          |1 - (w.sq.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ)))
        (1 - (w.sq.toVal : ℝ))
      have hrw : ((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ)) +
          (1 - (w.sq.toVal : ℝ)) = (w.sech_sq.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.sech_sq.toVal : ℝ))| ≤ (1 + η) * (1 + M_sq)
    calc |((w.sech_sq.toVal : ℝ))|
        ≤ |((w.sech_sq.toVal : ℝ)) - (1 - (w.sq.toVal : ℝ))| +
          |1 - (w.sq.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (1 + M_sq) + (1 + M_sq) := by linarith
      _ = (1 + η) * (1 + M_sq) := by ring
  -- Step 12: half_opt = half · opt.
  have h_half_opt_step :=
    KahanSum.fpMul_error_or_zero (R := ℝ) half w.fwd.opt w.half_opt
      w.hhalf_opt h_half_opt_nr
  have h_half_opt_abs : |hr * ((w.fwd.opt.toVal : ℝ))| ≤ Bh * M_opt := by
    rw [abs_mul]; exact mul_le_mul hBh h_M_opt (abs_nonneg _) hBh_nn
  have h_half_opt_step_loose :
      |((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ)| ≤
      (η : ℝ) * (Bh * M_opt) := by
    refine le_trans h_half_opt_step ?_
    exact mul_le_mul_of_nonneg_left h_half_opt_abs hη_nn
  set ε_half_opt_real : ℝ := (η : ℝ) * Bh * M_opt + Bh * ε_opt
    with hε_half_opt_real_def
  -- Closeness vs half · (1 + tanh(u))
  have h_ε_half_opt_real : |((w.half_opt.toVal : ℝ)) -
      hr * (1 + Real.tanh (geluPolyArg αr cr xr))| ≤ ε_half_opt_real := by
    have h_split : ((w.half_opt.toVal : ℝ)) -
        hr * (1 + Real.tanh (geluPolyArg αr cr xr)) =
      (((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ)) +
      (hr * (w.fwd.opt.toVal : ℝ) -
        hr * (1 + Real.tanh (geluPolyArg αr cr xr))) := by ring
    have h_diff_chain :
        |hr * ((w.fwd.opt.toVal : ℝ)) -
          hr * (1 + Real.tanh (geluPolyArg αr cr xr))| ≤ Bh * ε_opt := by
      have h1 : hr * ((w.fwd.opt.toVal : ℝ)) -
          hr * (1 + Real.tanh (geluPolyArg αr cr xr)) =
        hr * (((w.fwd.opt.toVal : ℝ)) -
          (1 + Real.tanh (geluPolyArg αr cr xr))) := by ring
      rw [h1, abs_mul]
      exact mul_le_mul hBh h_ε_opt (abs_nonneg _) hBh_nn
    show |((w.half_opt.toVal : ℝ)) -
        hr * (1 + Real.tanh (geluPolyArg αr cr xr))| ≤
      (η : ℝ) * Bh * M_opt + Bh * ε_opt
    calc |((w.half_opt.toVal : ℝ)) -
            hr * (1 + Real.tanh (geluPolyArg αr cr xr))|
        = |(((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ)) +
            (hr * (w.fwd.opt.toVal : ℝ) -
              hr * (1 + Real.tanh (geluPolyArg αr cr xr)))| := by rw [h_split]
      _ ≤ |((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ)| +
          |hr * (w.fwd.opt.toVal : ℝ) -
            hr * (1 + Real.tanh (geluPolyArg αr cr xr))| := abs_add_le _ _
      _ ≤ (η : ℝ) * (Bh * M_opt) + Bh * ε_opt := by linarith
      _ = (η : ℝ) * Bh * M_opt + Bh * ε_opt := by ring
  set M_half_opt : ℝ := (1 + η) * Bh * M_opt with hM_half_opt_def
  have hM_half_opt_nn : 0 ≤ M_half_opt := by
    show 0 ≤ (1 + η) * Bh * M_opt; positivity
  have h_M_half_opt : |((w.half_opt.toVal : ℝ))| ≤ M_half_opt := by
    have h_sum : |((w.half_opt.toVal : ℝ))| ≤
        |((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ)| +
        |hr * (w.fwd.opt.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ))
        (hr * (w.fwd.opt.toVal : ℝ))
      have hrw : ((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ) +
          hr * (w.fwd.opt.toVal : ℝ) = (w.half_opt.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.half_opt.toVal : ℝ))| ≤ (1 + η) * Bh * M_opt
    calc |((w.half_opt.toVal : ℝ))|
        ≤ |((w.half_opt.toVal : ℝ)) - hr * (w.fwd.opt.toVal : ℝ)| +
          |hr * (w.fwd.opt.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (Bh * M_opt) + Bh * M_opt := by linarith
      _ = (1 + η) * Bh * M_opt := by ring
  -- Step 13: three_a_xsq = three_α · x_sq.
  have h_three_a_step :=
    KahanSum.fpMul_error_or_zero (R := ℝ) three_α w.fwd.x_sq w.three_a_xsq
      w.hthree_a_xsq h_three_a_xsq_nr
  have h_three_a_abs : |t3αr * ((w.fwd.x_sq.toVal : ℝ))| ≤ B3α * M_x_sq := by
    rw [abs_mul]
    exact mul_le_mul hB3α h_M_x_sq (abs_nonneg _) hB3α_nn
  have h_three_a_step_loose :
      |((w.three_a_xsq.toVal : ℝ)) - t3αr * (w.fwd.x_sq.toVal : ℝ)| ≤
      (η : ℝ) * (B3α * M_x_sq) := by
    refine le_trans h_three_a_step ?_
    exact mul_le_mul_of_nonneg_left h_three_a_abs hη_nn
  -- Closeness against 3α · x²:
  -- |three_α·x_sq_fp - 3α·x²| ≤ |three_α·x_sq_fp - three_α·x²| + |three_α·x² - 3α·x²|
  --                          ≤ B3α · ε_x_sq + ε_3α · B²
  have h_xr2_abs : |xr * xr| ≤ B * B := by
    rw [abs_mul]; exact mul_le_mul hB hB (abs_nonneg _) hB_nn
  have h_inner_diff_3a :
      |t3αr * ((w.fwd.x_sq.toVal : ℝ)) - 3 * αr * (xr * xr)| ≤
      B3α * ε_x_sq + ε_3α * (B * B) := by
    have h_split : t3αr * ((w.fwd.x_sq.toVal : ℝ)) - 3 * αr * (xr * xr) =
        t3αr * (((w.fwd.x_sq.toVal : ℝ)) - xr * xr) +
        (t3αr - 3 * αr) * (xr * xr) := by ring
    have h_a : |t3αr * (((w.fwd.x_sq.toVal : ℝ)) - xr * xr)| ≤ B3α * ε_x_sq := by
      rw [abs_mul]; exact mul_le_mul hB3α h_ε_x_sq (abs_nonneg _) hB3α_nn
    have h_b : |(t3αr - 3 * αr) * (xr * xr)| ≤ ε_3α * (B * B) := by
      rw [abs_mul]
      exact mul_le_mul h_ε3α h_xr2_abs (abs_nonneg _) h_ε3α_nn
    calc |t3αr * ((w.fwd.x_sq.toVal : ℝ)) - 3 * αr * (xr * xr)|
        = |t3αr * (((w.fwd.x_sq.toVal : ℝ)) - xr * xr) +
            (t3αr - 3 * αr) * (xr * xr)| := by rw [h_split]
      _ ≤ |t3αr * (((w.fwd.x_sq.toVal : ℝ)) - xr * xr)| +
          |(t3αr - 3 * αr) * (xr * xr)| := abs_add_le _ _
      _ ≤ B3α * ε_x_sq + ε_3α * (B * B) := by linarith
  set ε_three_a_xsq_real : ℝ :=
    (η : ℝ) * B3α * M_x_sq + B3α * ε_x_sq + ε_3α * (B * B)
    with hε_three_a_real_def
  have h_ε_three_a_real : |((w.three_a_xsq.toVal : ℝ)) -
      3 * αr * (xr * xr)| ≤ ε_three_a_xsq_real := by
    have h_split : ((w.three_a_xsq.toVal : ℝ)) - 3 * αr * (xr * xr) =
      (((w.three_a_xsq.toVal : ℝ)) - t3αr * (w.fwd.x_sq.toVal : ℝ)) +
      (t3αr * ((w.fwd.x_sq.toVal : ℝ)) - 3 * αr * (xr * xr)) := by ring
    show |((w.three_a_xsq.toVal : ℝ)) - 3 * αr * (xr * xr)| ≤
      (η : ℝ) * B3α * M_x_sq + B3α * ε_x_sq + ε_3α * (B * B)
    calc |((w.three_a_xsq.toVal : ℝ)) - 3 * αr * (xr * xr)|
        = |(((w.three_a_xsq.toVal : ℝ)) - t3αr * (w.fwd.x_sq.toVal : ℝ)) +
            (t3αr * ((w.fwd.x_sq.toVal : ℝ)) - 3 * αr * (xr * xr))| := by
            rw [h_split]
      _ ≤ |((w.three_a_xsq.toVal : ℝ)) - t3αr * (w.fwd.x_sq.toVal : ℝ)| +
          |t3αr * ((w.fwd.x_sq.toVal : ℝ)) - 3 * αr * (xr * xr)| :=
            abs_add_le _ _
      _ ≤ (η : ℝ) * (B3α * M_x_sq) +
          (B3α * ε_x_sq + ε_3α * (B * B)) := by linarith
      _ = (η : ℝ) * B3α * M_x_sq + B3α * ε_x_sq + ε_3α * (B * B) := by ring
  set M_three_a_xsq : ℝ := (1 + η) * B3α * M_x_sq with hM_three_a_def
  have hM_three_a_nn : 0 ≤ M_three_a_xsq := by
    show 0 ≤ (1 + η) * B3α * M_x_sq; positivity
  have h_M_three_a : |((w.three_a_xsq.toVal : ℝ))| ≤ M_three_a_xsq := by
    have h_sum : |((w.three_a_xsq.toVal : ℝ))| ≤
        |((w.three_a_xsq.toVal : ℝ)) - t3αr * (w.fwd.x_sq.toVal : ℝ)| +
        |t3αr * (w.fwd.x_sq.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.three_a_xsq.toVal : ℝ)) - t3αr * (w.fwd.x_sq.toVal : ℝ))
        (t3αr * (w.fwd.x_sq.toVal : ℝ))
      have hrw : ((w.three_a_xsq.toVal : ℝ)) -
          t3αr * (w.fwd.x_sq.toVal : ℝ) +
          t3αr * (w.fwd.x_sq.toVal : ℝ) =
          (w.three_a_xsq.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.three_a_xsq.toVal : ℝ))| ≤ (1 + η) * B3α * M_x_sq
    calc |((w.three_a_xsq.toVal : ℝ))|
        ≤ |((w.three_a_xsq.toVal : ℝ)) - t3αr * (w.fwd.x_sq.toVal : ℝ)| +
          |t3αr * (w.fwd.x_sq.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (B3α * M_x_sq) + B3α * M_x_sq := by linarith
      _ = (1 + η) * B3α * M_x_sq := by ring
  -- Step 14: one_plus_3axsq = 1 + three_a_xsq.
  have h_one_plus_nr' :
      isNormalRange (((1 : FiniteFp).toVal : ℝ) + (w.three_a_xsq.toVal : ℝ)) ∨
        ((1 : FiniteFp).toVal : ℝ) + (w.three_a_xsq.toVal : ℝ) = 0 := by
    rw [h_one_toVal]; exact h_one_plus_nr
  have h_one_plus_step :=
    KahanSum.fpAdd_error_or_zero (R := ℝ) (1 : FiniteFp) w.three_a_xsq
      w.one_plus_3axsq w.hone_plus h_one_plus_nr'
  rw [h_one_toVal] at h_one_plus_step
  have h_one_plus_3a_abs : |1 + ((w.three_a_xsq.toVal : ℝ))| ≤
      1 + M_three_a_xsq := by
    have hadd := abs_add_le (1 : ℝ) ((w.three_a_xsq.toVal : ℝ))
    have h1 : |(1 : ℝ)| = 1 := abs_one
    linarith
  have h_one_plus_step_loose :
      |((w.one_plus_3axsq.toVal : ℝ)) - (1 + (w.three_a_xsq.toVal : ℝ))| ≤
      (η : ℝ) * (1 + M_three_a_xsq) := by
    refine le_trans h_one_plus_step ?_
    exact mul_le_mul_of_nonneg_left h_one_plus_3a_abs hη_nn
  set ε_one_plus_real : ℝ :=
    (η : ℝ) * (1 + M_three_a_xsq) + ε_three_a_xsq_real
    with hε_one_plus_real_def
  have h_ε_one_plus_real : |((w.one_plus_3axsq.toVal : ℝ)) -
      (1 + 3 * αr * (xr * xr))| ≤ ε_one_plus_real := by
    have h_split : ((w.one_plus_3axsq.toVal : ℝ)) - (1 + 3 * αr * (xr * xr)) =
      (((w.one_plus_3axsq.toVal : ℝ)) - (1 + (w.three_a_xsq.toVal : ℝ))) +
      (((w.three_a_xsq.toVal : ℝ)) - 3 * αr * (xr * xr)) := by ring
    show |((w.one_plus_3axsq.toVal : ℝ)) - (1 + 3 * αr * (xr * xr))| ≤
      (η : ℝ) * (1 + M_three_a_xsq) + ε_three_a_xsq_real
    calc |((w.one_plus_3axsq.toVal : ℝ)) - (1 + 3 * αr * (xr * xr))|
        = |(((w.one_plus_3axsq.toVal : ℝ)) -
            (1 + (w.three_a_xsq.toVal : ℝ))) +
          (((w.three_a_xsq.toVal : ℝ)) - 3 * αr * (xr * xr))| := by rw [h_split]
      _ ≤ |((w.one_plus_3axsq.toVal : ℝ)) -
            (1 + (w.three_a_xsq.toVal : ℝ))| +
          |((w.three_a_xsq.toVal : ℝ)) - 3 * αr * (xr * xr)| := abs_add_le _ _
      _ ≤ (η : ℝ) * (1 + M_three_a_xsq) + ε_three_a_xsq_real := by linarith
  set M_one_plus : ℝ := (1 + η) * (1 + M_three_a_xsq) with hM_one_plus_def
  have hM_one_plus_nn : 0 ≤ M_one_plus := by
    show 0 ≤ (1 + η) * (1 + M_three_a_xsq); positivity
  have h_M_one_plus : |((w.one_plus_3axsq.toVal : ℝ))| ≤ M_one_plus := by
    have h_sum : |((w.one_plus_3axsq.toVal : ℝ))| ≤
        |((w.one_plus_3axsq.toVal : ℝ)) - (1 + (w.three_a_xsq.toVal : ℝ))| +
        |1 + (w.three_a_xsq.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.one_plus_3axsq.toVal : ℝ)) - (1 + (w.three_a_xsq.toVal : ℝ)))
        (1 + (w.three_a_xsq.toVal : ℝ))
      have hrw : ((w.one_plus_3axsq.toVal : ℝ)) -
          (1 + (w.three_a_xsq.toVal : ℝ)) +
          (1 + (w.three_a_xsq.toVal : ℝ)) =
          (w.one_plus_3axsq.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.one_plus_3axsq.toVal : ℝ))| ≤ (1 + η) * (1 + M_three_a_xsq)
    calc |((w.one_plus_3axsq.toVal : ℝ))|
        ≤ |((w.one_plus_3axsq.toVal : ℝ)) -
            (1 + (w.three_a_xsq.toVal : ℝ))| +
          |1 + (w.three_a_xsq.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (1 + M_three_a_xsq) +
          (1 + M_three_a_xsq) := by linarith
      _ = (1 + η) * (1 + M_three_a_xsq) := by ring
  -- Step 15: up = c · one_plus_3axsq.
  have h_up_step :=
    KahanSum.fpMul_error_or_zero (R := ℝ) c w.one_plus_3axsq w.up
      w.hup h_up_nr
  have h_c_one_plus_abs : |cr * ((w.one_plus_3axsq.toVal : ℝ))| ≤
      Bc * M_one_plus := by
    rw [abs_mul]; exact mul_le_mul hBc h_M_one_plus (abs_nonneg _) hBc_nn
  have h_up_step_loose :
      |((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ)| ≤
      (η : ℝ) * (Bc * M_one_plus) := by
    refine le_trans h_up_step ?_
    exact mul_le_mul_of_nonneg_left h_c_one_plus_abs hη_nn
  set ε_up_real : ℝ := (η : ℝ) * Bc * M_one_plus + Bc * ε_one_plus_real
    with hε_up_real_def
  have h_ε_up_real : |((w.up.toVal : ℝ)) -
      cr * (1 + 3 * αr * (xr * xr))| ≤ ε_up_real := by
    have h_split : ((w.up.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr)) =
      (((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ)) +
      (cr * ((w.one_plus_3axsq.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr)))
        := by ring
    have h_diff_chain : |cr * ((w.one_plus_3axsq.toVal : ℝ)) -
        cr * (1 + 3 * αr * (xr * xr))| ≤ Bc * ε_one_plus_real := by
      have h1 : cr * ((w.one_plus_3axsq.toVal : ℝ)) -
          cr * (1 + 3 * αr * (xr * xr)) =
        cr * (((w.one_plus_3axsq.toVal : ℝ)) - (1 + 3 * αr * (xr * xr))) := by
          ring
      rw [h1, abs_mul]
      exact mul_le_mul hBc h_ε_one_plus_real (abs_nonneg _) hBc_nn
    show |((w.up.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr))| ≤
      (η : ℝ) * Bc * M_one_plus + Bc * ε_one_plus_real
    calc |((w.up.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr))|
        = |(((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ)) +
            (cr * ((w.one_plus_3axsq.toVal : ℝ)) -
              cr * (1 + 3 * αr * (xr * xr)))| := by rw [h_split]
      _ ≤ |((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ)| +
          |cr * ((w.one_plus_3axsq.toVal : ℝ)) -
            cr * (1 + 3 * αr * (xr * xr))| := abs_add_le _ _
      _ ≤ (η : ℝ) * (Bc * M_one_plus) + Bc * ε_one_plus_real := by linarith
      _ = (η : ℝ) * Bc * M_one_plus + Bc * ε_one_plus_real := by ring
  set M_up : ℝ := (1 + η) * Bc * M_one_plus with hM_up_def
  have hM_up_nn : 0 ≤ M_up := by
    show 0 ≤ (1 + η) * Bc * M_one_plus; positivity
  have h_M_up : |((w.up.toVal : ℝ))| ≤ M_up := by
    have h_sum : |((w.up.toVal : ℝ))| ≤
        |((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ)| +
        |cr * (w.one_plus_3axsq.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ))
        (cr * (w.one_plus_3axsq.toVal : ℝ))
      have hrw : ((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ) +
          cr * (w.one_plus_3axsq.toVal : ℝ) = (w.up.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.up.toVal : ℝ))| ≤ (1 + η) * Bc * M_one_plus
    calc |((w.up.toVal : ℝ))|
        ≤ |((w.up.toVal : ℝ)) - cr * (w.one_plus_3axsq.toVal : ℝ)| +
          |cr * (w.one_plus_3axsq.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (Bc * M_one_plus) + Bc * M_one_plus := by linarith
      _ = (1 + η) * Bc * M_one_plus := by ring
  -- Step 16: hxd = hx · sech_sq.
  have h_hxd_step :=
    KahanSum.fpMul_error_or_zero (R := ℝ) w.fwd.hx w.sech_sq w.hxd
      w.hhxd h_hxd_nr
  have h_hxd_abs :
      |((w.fwd.hx.toVal : ℝ)) * (w.sech_sq.toVal : ℝ)| ≤ M_hx * M_sech_sq := by
    rw [abs_mul]; exact mul_le_mul h_M_hx h_M_sech_sq (abs_nonneg _) hM_hx_nn
  have h_hxd_step_loose :
      |((w.hxd.toVal : ℝ)) - (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)| ≤
      (η : ℝ) * (M_hx * M_sech_sq) := by
    refine le_trans h_hxd_step ?_
    exact mul_le_mul_of_nonneg_left h_hxd_abs hη_nn
  -- Bound on |hx_real · sech²|: |hx_real · sech²| ≤ Bh · B (since |sech²| ≤ 1)
  have h_sech2_le_one :
      |1 - Real.tanh (geluPolyArg αr cr xr) ^ 2| ≤ 1 := by
    have h1 : 0 ≤ Real.tanh (geluPolyArg αr cr xr) ^ 2 := sq_nonneg _
    have h2 : Real.tanh (geluPolyArg αr cr xr) ^ 2 ≤ 1 := by
      have h_abs := h_tanh_abs_le_one
      have h_sq_abs :
          |Real.tanh (geluPolyArg αr cr xr)| ^ 2 =
            Real.tanh (geluPolyArg αr cr xr) ^ 2 := sq_abs _
      have h_pow :
          |Real.tanh (geluPolyArg αr cr xr)| ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h_abs 2
      have h_one_sq : (1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h_sq_abs, h_one_sq] at h_pow
      exact h_pow
    rw [abs_le]; constructor <;> linarith
  have h_hx_real_sech2_abs :
      |hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| ≤ Bh * B := by
    rw [abs_mul]
    have h_hr_xr_abs : |hr * xr| ≤ Bh * B := by
      rw [abs_mul]; exact mul_le_mul hBh hB (abs_nonneg _) hBh_nn
    have h_BhB_nn : 0 ≤ Bh * B := mul_nonneg hBh_nn hB_nn
    calc |hr * xr| * |1 - Real.tanh (geluPolyArg αr cr xr) ^ 2|
        ≤ Bh * B * 1 :=
          mul_le_mul h_hr_xr_abs h_sech2_le_one (abs_nonneg _) h_BhB_nn
      _ = Bh * B := by ring
  -- Cross-product bound for step 16.
  have h_cross_hxd : |((w.fwd.hx.toVal : ℝ)) * (w.sech_sq.toVal : ℝ) -
      hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| ≤
      ε_hx * M_sech_sq + Bh * B * ε_sech_sq_real := by
    have h_split :
        ((w.fwd.hx.toVal : ℝ)) * (w.sech_sq.toVal : ℝ) -
          hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) =
        (((w.fwd.hx.toVal : ℝ)) - hr * xr) * (w.sech_sq.toVal : ℝ) +
        (hr * xr) * (((w.sech_sq.toVal : ℝ)) -
          (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) := by ring
    have h_a : |(((w.fwd.hx.toVal : ℝ)) - hr * xr) * (w.sech_sq.toVal : ℝ)| ≤
        ε_hx * M_sech_sq := by
      rw [abs_mul]
      exact mul_le_mul h_ε_hx h_M_sech_sq (abs_nonneg _) hε_hx_nn
    have h_b : |(hr * xr) * (((w.sech_sq.toVal : ℝ)) -
        (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2))| ≤
        Bh * B * ε_sech_sq_real := by
      rw [abs_mul]
      have h_hr_xr_abs : |hr * xr| ≤ Bh * B := by
        rw [abs_mul]; exact mul_le_mul hBh hB (abs_nonneg _) hBh_nn
      have h_BhB_nn : 0 ≤ Bh * B := mul_nonneg hBh_nn hB_nn
      exact mul_le_mul h_hr_xr_abs h_ε_sech_sq_real (abs_nonneg _) h_BhB_nn
    calc |((w.fwd.hx.toVal : ℝ)) * (w.sech_sq.toVal : ℝ) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)|
        = |(((w.fwd.hx.toVal : ℝ)) - hr * xr) * (w.sech_sq.toVal : ℝ) +
            (hr * xr) * (((w.sech_sq.toVal : ℝ)) -
              (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2))| := by rw [h_split]
      _ ≤ |(((w.fwd.hx.toVal : ℝ)) - hr * xr) * (w.sech_sq.toVal : ℝ)| +
          |(hr * xr) * (((w.sech_sq.toVal : ℝ)) -
            (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2))| := abs_add_le _ _
      _ ≤ ε_hx * M_sech_sq + Bh * B * ε_sech_sq_real := by linarith
  set ε_hxd_real : ℝ :=
    (η : ℝ) * M_hx * M_sech_sq + ε_hx * M_sech_sq + Bh * B * ε_sech_sq_real
    with hε_hxd_real_def
  have h_ε_hxd_real : |((w.hxd.toVal : ℝ)) -
      hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| ≤
      ε_hxd_real := by
    have h_split : ((w.hxd.toVal : ℝ)) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) =
      (((w.hxd.toVal : ℝ)) - (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)) +
      (((w.fwd.hx.toVal : ℝ)) * (w.sech_sq.toVal : ℝ) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) := by ring
    show |((w.hxd.toVal : ℝ)) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| ≤
      (η : ℝ) * M_hx * M_sech_sq + ε_hx * M_sech_sq + Bh * B * ε_sech_sq_real
    calc |((w.hxd.toVal : ℝ)) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)|
        = |(((w.hxd.toVal : ℝ)) -
            (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)) +
          (((w.fwd.hx.toVal : ℝ)) * (w.sech_sq.toVal : ℝ) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2))| := by
            rw [h_split]
      _ ≤ |((w.hxd.toVal : ℝ)) -
            (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)| +
          |((w.fwd.hx.toVal : ℝ)) * (w.sech_sq.toVal : ℝ) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)| :=
            abs_add_le _ _
      _ ≤ (η : ℝ) * (M_hx * M_sech_sq) +
          (ε_hx * M_sech_sq + Bh * B * ε_sech_sq_real) := by linarith
      _ = (η : ℝ) * M_hx * M_sech_sq + ε_hx * M_sech_sq +
          Bh * B * ε_sech_sq_real := by ring
  set M_hxd : ℝ := (1 + η) * M_hx * M_sech_sq with hM_hxd_def
  have hM_hxd_nn : 0 ≤ M_hxd := by
    show 0 ≤ (1 + η) * M_hx * M_sech_sq; positivity
  have h_M_hxd : |((w.hxd.toVal : ℝ))| ≤ M_hxd := by
    have h_sum : |((w.hxd.toVal : ℝ))| ≤
        |((w.hxd.toVal : ℝ)) - (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)| +
        |(w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.hxd.toVal : ℝ)) - (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ))
        ((w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ))
      have hrw : ((w.hxd.toVal : ℝ)) -
          (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ) +
          (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ) =
          (w.hxd.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.hxd.toVal : ℝ))| ≤ (1 + η) * M_hx * M_sech_sq
    calc |((w.hxd.toVal : ℝ))|
        ≤ |((w.hxd.toVal : ℝ)) -
            (w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)| +
          |(w.fwd.hx.toVal : ℝ) * (w.sech_sq.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (M_hx * M_sech_sq) + M_hx * M_sech_sq := by linarith
      _ = (1 + η) * M_hx * M_sech_sq := by ring
  -- Step 17: hxdu = hxd · up.
  have h_hxdu_step :=
    KahanSum.fpMul_error_or_zero (R := ℝ) w.hxd w.up w.hxdu w.hhxdu h_hxdu_nr
  have h_hxdu_abs : |((w.hxd.toVal : ℝ)) * (w.up.toVal : ℝ)| ≤ M_hxd * M_up := by
    rw [abs_mul]; exact mul_le_mul h_M_hxd h_M_up (abs_nonneg _) hM_hxd_nn
  have h_hxdu_step_loose :
      |((w.hxdu.toVal : ℝ)) - (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)| ≤
      (η : ℝ) * (M_hxd * M_up) := by
    refine le_trans h_hxdu_step ?_
    exact mul_le_mul_of_nonneg_left h_hxdu_abs hη_nn
  -- Cross-product bound for step 17.
  -- |hxd · up - (hr·xr·sech²)·u'_real| ≤ ε_hxd_real · M_up + |hr·xr·sech²| · ε_up_real
  have h_cross_hxdu :
      |((w.hxd.toVal : ℝ)) * (w.up.toVal : ℝ) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
          (cr * (1 + 3 * αr * (xr * xr)))| ≤
      ε_hxd_real * M_up + Bh * B * ε_up_real := by
    have h_split :
        ((w.hxd.toVal : ℝ)) * (w.up.toVal : ℝ) -
          hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
            (cr * (1 + 3 * αr * (xr * xr))) =
        (((w.hxd.toVal : ℝ)) -
          hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
            (w.up.toVal : ℝ) +
        (hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
          (((w.up.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr))) := by ring
    have hε_hxd_real_nn : 0 ≤ ε_hxd_real := by
      show 0 ≤ (η : ℝ) * M_hx * M_sech_sq + ε_hx * M_sech_sq +
        Bh * B * ε_sech_sq_real
      have hε_sq_real_nn : 0 ≤ ε_sq_real := by
        show 0 ≤ (η : ℝ) * (M_t * M_t) + ε_t * (M_t + 1)
        have hM_t2_nn : 0 ≤ M_t * M_t := mul_nonneg hM_t_nn hM_t_nn
        have hM_t1_nn : 0 ≤ M_t + 1 := by linarith
        have h1 : 0 ≤ (η : ℝ) * (M_t * M_t) := mul_nonneg hη_nn hM_t2_nn
        have h2 : 0 ≤ ε_t * (M_t + 1) := mul_nonneg hε_t_nn hM_t1_nn
        linarith
      have hε_sech_sq_real_nn : 0 ≤ ε_sech_sq_real := by
        show 0 ≤ (η : ℝ) * (1 + M_sq) + ε_sq_real
        have h1 : 0 ≤ 1 + M_sq := by linarith
        have h2 : 0 ≤ (η : ℝ) * (1 + M_sq) := mul_nonneg hη_nn h1
        linarith
      have hBhB_nn : 0 ≤ Bh * B := mul_nonneg hBh_nn hB_nn
      have h1 : 0 ≤ (η : ℝ) * M_hx * M_sech_sq := by
        have := mul_nonneg hM_hx_nn hM_sech_sq_nn
        positivity
      have h2 : 0 ≤ ε_hx * M_sech_sq := mul_nonneg hε_hx_nn hM_sech_sq_nn
      have h3 : 0 ≤ Bh * B * ε_sech_sq_real :=
        mul_nonneg hBhB_nn hε_sech_sq_real_nn
      linarith
    have h_a : |(((w.hxd.toVal : ℝ)) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
          (w.up.toVal : ℝ)| ≤ ε_hxd_real * M_up := by
      rw [abs_mul]
      exact mul_le_mul h_ε_hxd_real h_M_up (abs_nonneg _) hε_hxd_real_nn
    have h_b : |(hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
        (((w.up.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr)))| ≤
        Bh * B * ε_up_real := by
      rw [abs_mul]
      have hBhB_nn : 0 ≤ Bh * B := mul_nonneg hBh_nn hB_nn
      exact mul_le_mul h_hx_real_sech2_abs h_ε_up_real (abs_nonneg _) hBhB_nn
    calc |((w.hxd.toVal : ℝ)) * (w.up.toVal : ℝ) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
              (cr * (1 + 3 * αr * (xr * xr)))|
        = |(((w.hxd.toVal : ℝ)) -
              hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
            (w.up.toVal : ℝ) +
          (hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
            (((w.up.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr)))| := by
            rw [h_split]
      _ ≤ |(((w.hxd.toVal : ℝ)) -
              hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
            (w.up.toVal : ℝ)| +
          |(hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2)) *
            (((w.up.toVal : ℝ)) - cr * (1 + 3 * αr * (xr * xr)))| :=
            abs_add_le _ _
      _ ≤ ε_hxd_real * M_up + Bh * B * ε_up_real := by linarith
  set ε_hxdu_real : ℝ :=
    (η : ℝ) * M_hxd * M_up + ε_hxd_real * M_up + Bh * B * ε_up_real
    with hε_hxdu_real_def
  have h_ε_hxdu_real : |((w.hxdu.toVal : ℝ)) -
      hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
        (cr * (1 + 3 * αr * (xr * xr)))| ≤ ε_hxdu_real := by
    have h_split : ((w.hxdu.toVal : ℝ)) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
          (cr * (1 + 3 * αr * (xr * xr))) =
      (((w.hxdu.toVal : ℝ)) - (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)) +
      (((w.hxd.toVal : ℝ)) * (w.up.toVal : ℝ) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
          (cr * (1 + 3 * αr * (xr * xr)))) := by ring
    show |((w.hxdu.toVal : ℝ)) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
          (cr * (1 + 3 * αr * (xr * xr)))| ≤
      (η : ℝ) * M_hxd * M_up + ε_hxd_real * M_up + Bh * B * ε_up_real
    calc |((w.hxdu.toVal : ℝ)) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
              (cr * (1 + 3 * αr * (xr * xr)))|
        = |(((w.hxdu.toVal : ℝ)) -
              (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)) +
          (((w.hxd.toVal : ℝ)) * (w.up.toVal : ℝ) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
              (cr * (1 + 3 * αr * (xr * xr))))| := by rw [h_split]
      _ ≤ |((w.hxdu.toVal : ℝ)) -
            (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)| +
          |((w.hxd.toVal : ℝ)) * (w.up.toVal : ℝ) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
              (cr * (1 + 3 * αr * (xr * xr)))| := abs_add_le _ _
      _ ≤ (η : ℝ) * (M_hxd * M_up) +
          (ε_hxd_real * M_up + Bh * B * ε_up_real) := by linarith
      _ = (η : ℝ) * M_hxd * M_up + ε_hxd_real * M_up +
          Bh * B * ε_up_real := by ring
  set M_hxdu : ℝ := (1 + η) * M_hxd * M_up with hM_hxdu_def
  have hM_hxdu_nn : 0 ≤ M_hxdu := by
    show 0 ≤ (1 + η) * M_hxd * M_up; positivity
  have h_M_hxdu : |((w.hxdu.toVal : ℝ))| ≤ M_hxdu := by
    have h_sum : |((w.hxdu.toVal : ℝ))| ≤
        |((w.hxdu.toVal : ℝ)) - (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)| +
        |(w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)| := by
      have hadd := abs_add_le
        (((w.hxdu.toVal : ℝ)) - (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ))
        ((w.hxd.toVal : ℝ) * (w.up.toVal : ℝ))
      have hrw : ((w.hxdu.toVal : ℝ)) -
          (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ) +
          (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ) = (w.hxdu.toVal : ℝ) := by ring
      rw [hrw] at hadd; exact hadd
    show |((w.hxdu.toVal : ℝ))| ≤ (1 + η) * M_hxd * M_up
    calc |((w.hxdu.toVal : ℝ))|
        ≤ |((w.hxdu.toVal : ℝ)) -
            (w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)| +
          |(w.hxd.toVal : ℝ) * (w.up.toVal : ℝ)| := h_sum
      _ ≤ (η : ℝ) * (M_hxd * M_up) + M_hxd * M_up := by linarith
      _ = (1 + η) * M_hxd * M_up := by ring
  -- Step 18: r = half_opt + hxdu.
  have h_r_step :=
    KahanSum.fpAdd_error_or_zero (R := ℝ) w.half_opt w.hxdu w.r w.hr h_r_nr
  have h_half_opt_plus_hxdu_abs :
      |((w.half_opt.toVal : ℝ)) + (w.hxdu.toVal : ℝ)| ≤
      M_half_opt + M_hxdu := by
    have hadd := abs_add_le ((w.half_opt.toVal : ℝ)) ((w.hxdu.toVal : ℝ))
    linarith
  have h_r_step_loose : |((w.r.toVal : ℝ)) -
      ((w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ))| ≤
      (η : ℝ) * (M_half_opt + M_hxdu) := by
    refine le_trans h_r_step ?_
    exact mul_le_mul_of_nonneg_left h_half_opt_plus_hxdu_abs hη_nn
  -- Final triangle.
  -- geluTanhApprox_deriv hr cr αr xr =
  --   hr · (1 + tanh(geluPolyArg αr cr xr)) +
  --   hr · xr · (1 − tanh²(geluPolyArg αr cr xr)) · (cr · (1 + 3·α·x²))
  have h_gelu_eq :
      Real.geluTanhApprox_deriv hr cr αr xr =
        hr * (1 + Real.tanh (geluPolyArg αr cr xr)) +
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
          (cr * (1 + 3 * αr * (xr * xr))) := by
    unfold Real.geluTanhApprox_deriv
    have h_pow : (xr : ℝ) ^ 3 = xr * xr * xr := by ring
    have h_pow2 : (xr : ℝ) ^ 2 = xr * xr := by ring
    show hr * (1 + Real.tanh (cr * (xr + αr * xr ^ 3))) +
        hr * xr * (1 - Real.tanh (cr * (xr + αr * xr ^ 3)) ^ 2) *
          (cr * (1 + 3 * αr * xr ^ 2)) =
      hr * (1 + Real.tanh (geluPolyArg αr cr xr)) +
      hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
        (cr * (1 + 3 * αr * (xr * xr)))
    rw [h_pow, h_pow2]
    rfl
  rw [h_gelu_eq]
  -- |r_fp - (half_opt_real + hxdu_real)| ≤ step + ε_half_opt + ε_hxdu
  have h_final_tri : |((w.r.toVal : ℝ)) -
      (hr * (1 + Real.tanh (geluPolyArg αr cr xr)) +
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
          (cr * (1 + 3 * αr * (xr * xr))))| ≤
      (η : ℝ) * (M_half_opt + M_hxdu) +
      ε_half_opt_real + ε_hxdu_real := by
    have h_split : ((w.r.toVal : ℝ)) -
        (hr * (1 + Real.tanh (geluPolyArg αr cr xr)) +
          hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
            (cr * (1 + 3 * αr * (xr * xr)))) =
      (((w.r.toVal : ℝ)) -
        ((w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ))) +
      (((w.half_opt.toVal : ℝ)) -
        hr * (1 + Real.tanh (geluPolyArg αr cr xr))) +
      (((w.hxdu.toVal : ℝ)) -
        hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
          (cr * (1 + 3 * αr * (xr * xr)))) := by ring
    calc |((w.r.toVal : ℝ)) -
            (hr * (1 + Real.tanh (geluPolyArg αr cr xr)) +
              hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
                (cr * (1 + 3 * αr * (xr * xr))))|
        = |(((w.r.toVal : ℝ)) -
              ((w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ))) +
          (((w.half_opt.toVal : ℝ)) -
            hr * (1 + Real.tanh (geluPolyArg αr cr xr))) +
          (((w.hxdu.toVal : ℝ)) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
              (cr * (1 + 3 * αr * (xr * xr))))| := by rw [h_split]
      _ ≤ |(((w.r.toVal : ℝ)) -
              ((w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ))) +
          (((w.half_opt.toVal : ℝ)) -
            hr * (1 + Real.tanh (geluPolyArg αr cr xr)))| +
          |((w.hxdu.toVal : ℝ)) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
              (cr * (1 + 3 * αr * (xr * xr)))| := abs_add_le _ _
      _ ≤ (|((w.r.toVal : ℝ)) -
              ((w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ))| +
            |((w.half_opt.toVal : ℝ)) -
              hr * (1 + Real.tanh (geluPolyArg αr cr xr))|) +
          |((w.hxdu.toVal : ℝ)) -
            hr * xr * (1 - Real.tanh (geluPolyArg αr cr xr) ^ 2) *
              (cr * (1 + 3 * αr * (xr * xr)))| := by
            have habs := abs_add_le
              (((w.r.toVal : ℝ)) -
                ((w.half_opt.toVal : ℝ) + (w.hxdu.toVal : ℝ)))
              (((w.half_opt.toVal : ℝ)) -
                hr * (1 + Real.tanh (geluPolyArg αr cr xr)))
            linarith
      _ ≤ (η : ℝ) * (M_half_opt + M_hxdu) +
          ε_half_opt_real + ε_hxdu_real := by linarith
  -- The slack-at unfolds (via the named gelu_M_*/gelu_ε_* helpers) to the
  -- same expression that h_final_tri bounds.  The proof's `set`-bound
  -- vars match by construction; `linarith` closes the remaining identity.
  have h_slack_eq : fpGeluDerivFinite_slack_at B Bh Bα B3α Bc ε_3α
      (w.fwd.tanh_w.tx.toVal : ℝ) (w.fwd.u.toVal : ℝ) =
      (η : ℝ) * (M_half_opt + M_hxdu) + ε_half_opt_real + ε_hxdu_real := by
    simp only [fpGeluDerivFinite_slack_at, gelu_M_half_opt, gelu_M_hxdu,
      gelu_ε_half_opt, gelu_ε_hxdu, gelu_M_t, gelu_M_opt, gelu_M_hx,
      gelu_M_x_sq, gelu_ε_t, gelu_ε_opt, gelu_ε_hx, gelu_ε_x_sq, gelu_ε_sq,
      gelu_M_sq, gelu_ε_sech_sq, gelu_M_sech_sq, gelu_ε_three_a_xsq,
      gelu_M_three_a_xsq, gelu_ε_one_plus, gelu_M_one_plus, gelu_ε_up,
      gelu_M_up, gelu_ε_hxd, gelu_M_hxd]
    ring
  rw [h_slack_eq]
  exact h_final_tri

end Flean
