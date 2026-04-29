import Flean.Operations.Activations.Gelu
import Flean.Operations.Activation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz constant for the parametric tanh-form GeLU

Ships `Flean.Activation.geluTanhWith half c α : Activation ℝ` (under
`0 ≤ α`) with Lipschitz constant `K = 5 · |half|`.

The bound is intentionally loose — for the standard parameters
`half = 1/2`, `c = √(2/π)`, `α ≈ 0.045`, the true global Lipschitz
constant of GeLU is ≈ 1.131, attained near `x ≈ 0.97`.  Our `K = 5/2`
is ~2.2× the tight constant; in exchange the proof is parametric in
`(half, c, α)` and follows from one saturation inequality plus a
single algebraic ratio bound.

## Main results

* `Real.abs_mul_one_sub_tanh_sq_le_one`:
  `|y · (1 - (Real.tanh y)²)| ≤ 1`.  The "saturation" inequality —
  while `|tanh' y| = |1 - tanh²y|` is bounded by 1, the *weighted*
  bound by `|y|` still doesn't blow up because `1 - tanh²y` decays
  exponentially in `|y|`.
* `Real.hasDerivAt_tanh`: `(Real.tanh)' y = 1 - (Real.tanh y)²`,
  derived from `tanh = sinh/cosh` plus the identity `cosh² − sinh² = 1`.
* `Real.hasDerivAt_geluTanhApprox`: derivative formula for the
  parametric tanh-form GeLU, matching `Real.geluTanhApprox_deriv`.
* `Real.abs_geluTanhApprox_deriv_le`: `|gelu'(x)| ≤ 5 · |half|` under
  `0 ≤ α` (no constraint on `c`).
* `Flean.Real.geluTanhApprox_lipschitz`: `LipschitzScalar (5·|half|)
  (Real.geluTanhApprox half c α)` (flean shape).
* `Flean.Activation.geluTanhWith`: bundled `Activation ℝ`.

## Why the bound is `5 · |half|`

The derivative decomposes as

```
gelu'(x) = half·(1 + tanh u(x)) + half·x·(1 − tanh²u(x))·u'(x)
```

with `u(x) = c·(x + α·x³)` and `u'(x) = c·(1 + 3α·x²)`.  Using:

* `|1 + tanh u| ≤ 2` (since `|tanh| ≤ 1`),
* `|x·(1 − tanh²u)·u'| ≤ 3` (combining `|u·(1−tanh²u)| ≤ 1` with
  `|x·u'/u| = (1+3α·x²)/(1+α·x²) ≤ 3` for `α ≥ 0`),

we get `|gelu'(x)| ≤ |half|·(2 + 3) = 5·|half|`.

The `(1+3α·x²)/(1+α·x²) ≤ 3` step needs `α ≥ 0`; otherwise the
denominator can vanish and the cubic factor argument fails.
-/

set_option autoImplicit false

namespace Real

/-! ## Saturation inequality `|y·(1 − tanh²y)| ≤ 1` -/

/-- Algebraic identity: `1 − tanh²y = 4 / (exp y + exp(−y))²`.

Proof routes through the difference-of-squares decomposition of
`(eʸ + e⁻ʸ)² − (eʸ − e⁻ʸ)² = 4·eʸ·e⁻ʸ = 4`. -/
lemma one_sub_tanh_sq_eq (y : ℝ) :
    1 - (Real.tanh y)^2 = 4 / (Real.exp y + Real.exp (-y))^2 := by
  have h_pos : 0 < Real.exp y + Real.exp (-y) := by positivity
  have h_ne : Real.exp y + Real.exp (-y) ≠ 0 := h_pos.ne'
  have h_mul : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [Real.tanh_eq, div_pow]
  have h_id :
      (1 : ℝ) -
        (Real.exp y - Real.exp (-y))^2 / (Real.exp y + Real.exp (-y))^2 =
      ((Real.exp y + Real.exp (-y))^2 - (Real.exp y - Real.exp (-y))^2) /
        (Real.exp y + Real.exp (-y))^2 := by
    field_simp
  rw [h_id]
  congr 1
  nlinarith [h_mul]

/-- A consequence of `one_sub_tanh_sq_eq`: `(Real.tanh y)² ≤ 1`. -/
lemma tanh_sq_le_one (y : ℝ) : (Real.tanh y)^2 ≤ 1 := by
  have h := Real.one_sub_tanh_sq_eq y
  have h_pos : 0 < (Real.exp y + Real.exp (-y))^2 := by positivity
  have h_div_nn : 0 ≤ 4 / (Real.exp y + Real.exp (-y))^2 := by positivity
  linarith

/-- Saturation inequality: `|y · (1 − tanh²y)| ≤ 1` for all `y : ℝ`.

The function `f(y) = y·(1−tanh²y)` is bounded uniformly even though
the factor `|y|` is unbounded — the `1−tanh²y` factor decays
exponentially fast in `|y|`.  Numerically `sup |f| ≈ 0.447`; this
loose `1` is what we actually use for the GeLU Lipschitz bound. -/
lemma abs_mul_one_sub_tanh_sq_le_one (y : ℝ) :
    |y * (1 - (Real.tanh y)^2)| ≤ 1 := by
  -- Reduce to y ≥ 0 by symmetry (tanh is odd, so 1−tanh²y is even).
  suffices h : ∀ z : ℝ, 0 ≤ z → z * (1 - (Real.tanh z)^2) ≤ 1 by
    have h_one_minus_sq_nn : ∀ z, 0 ≤ 1 - (Real.tanh z)^2 := fun z => by
      linarith [Real.tanh_sq_le_one z]
    rcases le_total 0 y with hy | hy
    · have h_nn : 0 ≤ y * (1 - (Real.tanh y)^2) :=
        mul_nonneg hy (h_one_minus_sq_nn y)
      rw [abs_of_nonneg h_nn]; exact h y hy
    · have h_neg_y_nn : 0 ≤ -y := by linarith
      have h_eq : (Real.tanh (-y))^2 = (Real.tanh y)^2 := by
        rw [Real.tanh_neg]; ring
      have h_abs_eq :
          |y * (1 - (Real.tanh y)^2)| = |(-y) * (1 - (Real.tanh (-y))^2)| := by
        rw [h_eq, neg_mul, abs_neg]
      rw [h_abs_eq]
      have h_nn : 0 ≤ (-y) * (1 - (Real.tanh (-y))^2) :=
        mul_nonneg h_neg_y_nn (h_one_minus_sq_nn (-y))
      rw [abs_of_nonneg h_nn]
      exact h (-y) h_neg_y_nn
  -- Main inequality: for z ≥ 0, z·(1 − tanh²z) ≤ 1.
  intro z hz
  have h_pos_e : 0 < Real.exp z + Real.exp (-z) := by positivity
  have h_sq_pos : 0 < (Real.exp z + Real.exp (-z))^2 := pow_pos h_pos_e 2
  rw [Real.one_sub_tanh_sq_eq]
  rw [show z * (4 / (Real.exp z + Real.exp (-z))^2) =
        (4 * z) / (Real.exp z + Real.exp (-z))^2 from by ring]
  rw [div_le_one h_sq_pos]
  -- Now: 4z ≤ (exp z + exp(-z))^2.  Chain (e^z+e^(-z))² ≥ e^(2z) ≥ 1+2z+2z² ≥ 4z.
  have h_exp_pos : 0 < Real.exp z := Real.exp_pos _
  have h_exp_neg_nn : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  have h_step1 : Real.exp (2 * z) ≤ (Real.exp z + Real.exp (-z))^2 := by
    have h_sq_eq : (Real.exp z + Real.exp (-z))^2 =
        Real.exp z ^ 2 + 2 * (Real.exp z * Real.exp (-z)) + Real.exp (-z) ^ 2 := by
      ring
    have h_exp2_eq : Real.exp (2 * z) = Real.exp z ^ 2 := by
      rw [show (2 : ℝ) * z = z + z from by ring, Real.exp_add]; ring
    rw [h_sq_eq, h_exp2_eq]
    nlinarith [mul_nonneg h_exp_pos.le h_exp_neg_nn, sq_nonneg (Real.exp (-z))]
  have h_step2 : 1 + 2 * z + 2 * z^2 ≤ Real.exp (2 * z) := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 * z by linarith)
    have h_eq : (2 * z)^2 / 2 = 2 * z^2 := by ring
    linarith [h_eq.symm ▸ h]
  have h_step3 : 4 * z ≤ 1 + 2 * z + 2 * z^2 := by
    nlinarith [sq_nonneg (2 * z - 1)]
  linarith

/-! ## Derivative of `Real.tanh`

Mathlib has `Real.hasDerivAt_sinh` / `Real.hasDerivAt_cosh`; we derive
`Real.tanh` from the quotient and rewrite the resulting derivative
`(cosh² − sinh²)/cosh² = 1/cosh² = 1 − tanh²`. -/

/-- `Real.tanh` is differentiable everywhere with derivative
`1 − (Real.tanh y)²`. -/
theorem hasDerivAt_tanh (y : ℝ) :
    HasDerivAt Real.tanh (1 - (Real.tanh y)^2) y := by
  have h_cosh_pos : 0 < Real.cosh y := Real.cosh_pos y
  have h_cosh_ne : Real.cosh y ≠ 0 := h_cosh_pos.ne'
  have h_div := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) h_cosh_ne
  -- h_div :
  --   HasDerivAt (Real.sinh / Real.cosh)
  --     ((Real.cosh y · Real.cosh y − Real.sinh y · Real.sinh y) / (Real.cosh y)²) y
  have h_eq_fun : (Real.sinh / Real.cosh : ℝ → ℝ) = Real.tanh := by
    funext z
    show Real.sinh z / Real.cosh z = Real.tanh z
    rw [Real.tanh_eq_sinh_div_cosh]
  rw [h_eq_fun] at h_div
  -- Rewrite the derivative value to `1 - tanh²y`.
  have h_cs := Real.cosh_sq_sub_sinh_sq y
  have h_cosh_sq_ne : (Real.cosh y)^2 ≠ 0 := pow_ne_zero _ h_cosh_ne
  have h_eq_val :
      (Real.cosh y * Real.cosh y - Real.sinh y * Real.sinh y) / (Real.cosh y)^2
        = 1 - (Real.tanh y)^2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
  rw [← h_eq_val]
  exact h_div

end Real

/-! ## Derivative of `Real.geluTanhApprox`

Builds the explicit derivative formula via product/chain rules, matching
the `Real.geluTanhApprox_deriv` definition shipped in `Gelu.lean`. -/

namespace Real

/-- Derivative formula for the parametric tanh-form GeLU. -/
theorem hasDerivAt_geluTanhApprox (half c α x : ℝ) :
    HasDerivAt (fun y => Real.geluTanhApprox half c α y)
      (Real.geluTanhApprox_deriv half c α x) x := by
  -- Inner: u(x) = c · (x + α · x³).  Polynomial.
  have h_u : HasDerivAt (fun z => c * (z + α * z^3)) (c * (1 + 3 * α * x^2)) x := by
    have h_id : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
    have h_cube : HasDerivAt (fun z : ℝ => z^3) ((3 : ℕ) * x^(3 - 1)) x :=
      hasDerivAt_pow 3 x
    have h_cube' : HasDerivAt (fun z : ℝ => z^3) (3 * x^2) x := by
      have h_eq : ((3 : ℕ) : ℝ) * x^(3 - 1 : ℕ) = 3 * x^2 := by norm_num
      rw [← h_eq]; exact_mod_cast h_cube
    have h_alpha_cube : HasDerivAt (fun z : ℝ => α * z^3) (α * (3 * x^2)) x :=
      h_cube'.const_mul α
    have h_sum : HasDerivAt (fun z : ℝ => z + α * z^3) (1 + α * (3 * x^2)) x :=
      h_id.add h_alpha_cube
    have h_scaled : HasDerivAt (fun z => c * (z + α * z^3))
        (c * (1 + α * (3 * x^2))) x :=
      h_sum.const_mul c
    convert h_scaled using 1
    ring
  -- tanh ∘ u
  have h_tanh_u :
      HasDerivAt (fun z => Real.tanh (c * (z + α * z^3)))
        ((1 - (Real.tanh (c * (x + α * x^3)))^2) * (c * (1 + 3 * α * x^2))) x :=
    (Real.hasDerivAt_tanh _).comp x h_u
  -- 1 + tanh ∘ u
  have h_one_plus_tanh_u := h_tanh_u.const_add (1 : ℝ)
  -- half · z, derivative half
  have h_half_x : HasDerivAt (fun z : ℝ => half * z) half x := by
    have := (hasDerivAt_id x).const_mul half
    convert this using 1; ring
  -- half · z · (1 + tanh u(z)) — product rule
  have h_prod := h_half_x.mul h_one_plus_tanh_u
  -- Match function shapes and value shape.
  have h_fun_eq :
      (fun y => half * y * ((fun w => 1 + Real.tanh (c * (w + α * w^3))) y)) =
      fun y => Real.geluTanhApprox half c α y := by
    funext z
    show half * z * (1 + Real.tanh (c * (z + α * z^3))) =
         Real.geluTanhApprox half c α z
    rfl
  rw [← h_fun_eq]
  convert h_prod using 1
  unfold Real.geluTanhApprox_deriv
  ring

/-! ## Magnitude bound on the derivative -/

/-- Bound on the derivative of the parametric tanh-form GeLU:
`|gelu'(x)| ≤ 5 · |half|` whenever `0 ≤ α`.

The bound decomposes as `2·|half|` (from `|1 + tanh u| ≤ 2`) plus
`3·|half|` (from `|x·(1−tanh²u)·u'| ≤ 3`, combining the saturation
inequality with the algebraic ratio `(1+3α·x²)/(1+α·x²) ≤ 3`). -/
theorem abs_geluTanhApprox_deriv_le {half c α : ℝ} (h_α_nn : 0 ≤ α) (x : ℝ) :
    |Real.geluTanhApprox_deriv half c α x| ≤ 5 * |half| := by
  unfold Real.geluTanhApprox_deriv
  set u : ℝ := c * (x + α * x^3) with h_u_def
  set up : ℝ := c * (1 + 3 * α * x^2) with h_up_def
  -- Preliminary positivity facts.
  have h_alpha_xsq_nn : 0 ≤ α * x^2 := mul_nonneg h_α_nn (sq_nonneg _)
  have h_one_plus_alpha_pos : 0 < 1 + α * x^2 := by linarith
  have h_one_plus_3alpha_pos : 0 < 1 + 3 * α * x^2 := by nlinarith
  have h_tanh_sq_le := Real.tanh_sq_le_one u
  have h_sech_nn : 0 ≤ 1 - (Real.tanh u)^2 := by linarith
  -- Bound on |1 + tanh u|: at most 2.
  have h_abs_tanh : |Real.tanh u| ≤ 1 := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt h_tanh_sq_le
  have h_one_plus_tanh_abs : |1 + Real.tanh u| ≤ 2 := by
    have h_lo : -1 ≤ Real.tanh u := neg_le_of_abs_le h_abs_tanh
    have h_hi : Real.tanh u ≤ 1 := le_of_abs_le h_abs_tanh
    have h_nn : 0 ≤ 1 + Real.tanh u := by linarith
    rw [abs_of_nonneg h_nn]; linarith
  -- Bound on first term: |half · (1 + tanh u)| ≤ 2 · |half|.
  have h_term1 : |half * (1 + Real.tanh u)| ≤ 2 * |half| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h_one_plus_tanh_abs (abs_nonneg _)
  -- Bound on second term: |half · x · (1 − tanh²u) · up| ≤ 3 · |half|.
  -- Strategy: show |x · (1 − tanh²u) · up| ≤ 3, then multiply by |half|.
  have h_x_factor : |x * (1 - (Real.tanh u)^2) * up| ≤ 3 := by
    -- Algebraic identity: (1+α·x²) · x · up = u · (1+3α·x²)
    have h_key :
        (1 + α * x^2) * (x * (1 - (Real.tanh u)^2) * up) =
        u * (1 - (Real.tanh u)^2) * (1 + 3 * α * x^2) := by
      show (1 + α * x^2) * (x * (1 - (Real.tanh u)^2) * (c * (1 + 3*α*x^2))) =
           (c * (x + α*x^3)) * (1 - (Real.tanh u)^2) * (1 + 3*α*x^2)
      ring
    -- Take absolute values: (1+α·x²) · |x·(1−tanh²u)·up| = |u·(1−tanh²u)| · (1+3α·x²)
    have h_abs_key :
        (1 + α * x^2) * |x * (1 - (Real.tanh u)^2) * up| =
        |u * (1 - (Real.tanh u)^2)| * (1 + 3 * α * x^2) := by
      have h_lhs :
          |(1 + α * x^2) * (x * (1 - (Real.tanh u)^2) * up)| =
          (1 + α * x^2) * |x * (1 - (Real.tanh u)^2) * up| := by
        rw [abs_mul, abs_of_pos h_one_plus_alpha_pos]
      have h_rhs :
          |u * (1 - (Real.tanh u)^2) * (1 + 3 * α * x^2)| =
          |u * (1 - (Real.tanh u)^2)| * (1 + 3 * α * x^2) := by
        rw [abs_mul, abs_of_pos h_one_plus_3alpha_pos]
      have h_abs_eq :
          |(1 + α * x^2) * (x * (1 - (Real.tanh u)^2) * up)| =
          |u * (1 - (Real.tanh u)^2) * (1 + 3 * α * x^2)| := by
        rw [h_key]
      rw [h_lhs] at h_abs_eq
      rw [h_rhs] at h_abs_eq
      exact h_abs_eq
    -- Saturation: |u·(1−tanh²u)| ≤ 1
    have h_sat := Real.abs_mul_one_sub_tanh_sq_le_one u
    -- (1+α·x²) · |x·(1−tanh²u)·up| ≤ 1 · (1+3α·x²) ≤ 3 · (1+α·x²)
    have h_chain : (1 + α * x^2) * |x * (1 - (Real.tanh u)^2) * up| ≤
        3 * (1 + α * x^2) := by
      rw [h_abs_key]
      have h1 : |u * (1 - (Real.tanh u)^2)| * (1 + 3 * α * x^2) ≤
                1 * (1 + 3 * α * x^2) :=
        mul_le_mul_of_nonneg_right h_sat (le_of_lt h_one_plus_3alpha_pos)
      have h2 : 1 * (1 + 3 * α * x^2) ≤ 3 * (1 + α * x^2) := by nlinarith
      linarith
    -- Divide both sides by (1+α·x²) > 0
    nlinarith [h_chain, h_one_plus_alpha_pos]
  have h_term2 : |half * x * (1 - (Real.tanh u)^2) * up| ≤ 3 * |half| := by
    rw [show half * x * (1 - (Real.tanh u)^2) * up =
          half * (x * (1 - (Real.tanh u)^2) * up) from by ring,
        abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h_x_factor (abs_nonneg _)
  -- Combine via triangle inequality.
  have h_triangle :
      |half * (1 + Real.tanh u) + half * x * (1 - (Real.tanh u)^2) * up| ≤
      |half * (1 + Real.tanh u)| + |half * x * (1 - (Real.tanh u)^2) * up| :=
    abs_add_le _ _
  linarith

end Real

/-! ## Lipschitz instance and bundled `Activation`

Conclude via mathlib's MVT that `Real.geluTanhApprox half c α` is
`(5·|half|)`-Lipschitz, then bundle as `Flean.Activation ℝ`. -/

namespace Flean

open Flean.Lipschitz

/-- **`Real.geluTanhApprox` is `(5·|half|)`-Lipschitz on ℝ** under
`0 ≤ α`, derived via Mathlib's MVT
(`Convex.norm_image_sub_le_of_norm_deriv_le`) with the derivative
bound `Real.abs_geluTanhApprox_deriv_le`. -/
theorem Real.geluTanhApprox_lipschitz {half c α : ℝ} (h_α_nn : 0 ≤ α) :
    LipschitzScalar (R := ℝ) (5 * |half|) (Real.geluTanhApprox half c α) where
  K_nn := by positivity
  bound := by
    intro a b
    have h_diff : ∀ x ∈ (Set.univ : Set ℝ),
        DifferentiableAt ℝ (fun y => Real.geluTanhApprox half c α y) x :=
      fun x _ => (Real.hasDerivAt_geluTanhApprox half c α x).differentiableAt
    have h_bnd : ∀ x ∈ (Set.univ : Set ℝ),
        ‖deriv (fun y => Real.geluTanhApprox half c α y) x‖ ≤ 5 * |half| := by
      intro x _
      rw [Real.norm_eq_abs, (Real.hasDerivAt_geluTanhApprox half c α x).deriv]
      exact Real.abs_geluTanhApprox_deriv_le h_α_nn x
    have key := convex_univ.norm_image_sub_le_of_norm_deriv_le
      h_diff h_bnd (Set.mem_univ b) (Set.mem_univ a)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at key

/-- The parametric tanh-form GeLU activation, bundled as
`Flean.Activation ℝ` with Lipschitz constant `5·|half|`.

Inputs:
* `half`, `c` arbitrary scalars (`half ≈ 1/2`, `c ≈ √(2/π)` for the
  standard parameters).
* `α` a non-negativity-constrained scalar (`α ≈ 0.044715` for the
  standard parameters).

The `5·|half|` Lipschitz constant is loose; for standard parameters
it gives `K = 5/2 = 2.5` versus the tight value of ~1.131.  See module
docstring for the proof outline and why we accept the looseness. -/
noncomputable def Activation.geluTanhWith (half c α : ℝ) (h_α_nn : 0 ≤ α) :
    Activation ℝ where
  apply := Real.geluTanhApprox half c α
  K := 5 * |half|
  lipschitz := _root_.Flean.Real.geluTanhApprox_lipschitz h_α_nn

@[simp] lemma Activation.geluTanhWith_apply
    (half c α : ℝ) (h_α_nn : 0 ≤ α) (x : ℝ) :
    (Activation.geluTanhWith half c α h_α_nn).apply x =
      Real.geluTanhApprox half c α x := rfl

@[simp] lemma Activation.geluTanhWith_K (half c α : ℝ) (h_α_nn : 0 ≤ α) :
    (Activation.geluTanhWith half c α h_α_nn).K = 5 * |half| := rfl

end Flean
