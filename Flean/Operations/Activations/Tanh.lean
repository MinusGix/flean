import Flean.Operations.Activations.Sigmoid
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Tanh as a `Flean.Activation`

Wraps `Real.tanh` as `Flean.Activation ℝ` with proven Lipschitz constant
`K = 1`. The Lipschitz proof is a thin wrapper around the sigmoid one
via the algebraic identity:

```
tanh x = 2·σ(2x) − 1
```

so that `|tanh a − tanh b| = 2·|σ(2a) − σ(2b)| ≤ 2·(1/4)·|2a − 2b| = |a − b|`.

## Main results

* `Real.tanh_eq_two_sigmoid_sub_one` — the algebraic identity.
* `Flean.Real.tanh_lipschitz_one` — Lipschitz bound, flean shape.
* `Flean.Activation.tanh : Flean.Activation ℝ` — bundled instance.

This routing also lets the FP forward implementation reuse
`fpSigmoidFinite` directly (see `TanhFp.lean`).
-/

set_option autoImplicit false

namespace Real

/-- **Identity**: `tanh x = 2·σ(2x) − 1`.

Proof: convert both sides to `(1 − exp(−2x)) / (1 + exp(−2x))`. The
LHS form `(eˣ − e⁻ˣ)/(eˣ + e⁻ˣ)` reaches it by multiplying by `e⁻ˣ`;
the RHS reaches it by `2/(1 + e⁻²ˣ) − 1 = (2 − (1 + e⁻²ˣ))/(1 + e⁻²ˣ)`. -/
lemma tanh_eq_two_sigmoid_sub_one (x : ℝ) :
    Real.tanh x = 2 * Real.sigmoid (2 * x) - 1 := by
  rw [Real.tanh_eq, Real.sigmoid_def]
  have h_2x : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1; ring
  have h_inv : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h_denom_pos : (0 : ℝ) < Real.exp x + Real.exp (-x) := by positivity
  have h_denom_pos' : (0 : ℝ) < 1 + Real.exp (-x) * Real.exp (-x) := by positivity
  rw [h_2x]
  rw [eq_sub_iff_add_eq]
  field_simp
  -- Goal after field_simp: cross-multiplied identity. Use h_inv to simplify.
  nlinarith [h_inv, Real.exp_pos x, Real.exp_pos (-x),
             sq_nonneg (Real.exp x - Real.exp (-x)),
             sq_nonneg (Real.exp x + Real.exp (-x))]

end Real

namespace Flean

open Flean.Lipschitz

/-- **Real.tanh is 1-Lipschitz on ℝ**, derived from `Real.sigmoid` being
`(1/4)`-Lipschitz via the identity `tanh x = 2σ(2x) − 1`. -/
theorem Real.tanh_lipschitz_one :
    LipschitzScalar (R := ℝ) 1 Real.tanh where
  K_nn := zero_le_one
  bound := by
    intro a b
    rw [_root_.Real.tanh_eq_two_sigmoid_sub_one,
        _root_.Real.tanh_eq_two_sigmoid_sub_one]
    -- |2σ(2a) - 1 - (2σ(2b) - 1)| = 2 · |σ(2a) - σ(2b)|
    have h_sig :=
      _root_.Flean.Real.sigmoid_lipschitz_quarter.bound (2 * a) (2 * b)
    -- h_sig : |σ(2a) − σ(2b)| ≤ (1/4) · |2a − 2b|
    have h_simplify :
        |(2 * Real.sigmoid (2 * a) - 1) - (2 * Real.sigmoid (2 * b) - 1)| =
        2 * |Real.sigmoid (2 * a) - Real.sigmoid (2 * b)| := by
      rw [show (2 * Real.sigmoid (2 * a) - 1) - (2 * Real.sigmoid (2 * b) - 1)
            = 2 * (Real.sigmoid (2 * a) - Real.sigmoid (2 * b)) from by ring,
          abs_mul]
      simp
    have h_2ab : |2 * a - 2 * b| = 2 * |a - b| := by
      rw [show 2 * a - 2 * b = 2 * (a - b) from by ring, abs_mul]
      simp
    rw [h_simplify]
    rw [h_2ab] at h_sig
    -- h_sig : |σ(2a) − σ(2b)| ≤ (1/4) · (2 · |a − b|)
    linarith

/-- The tanh activation, bundled as `Flean.Activation ℝ` with K = 1. -/
noncomputable def Activation.tanh : Activation ℝ where
  apply := Real.tanh
  K := 1
  lipschitz := _root_.Flean.Real.tanh_lipschitz_one

@[simp] lemma Activation.tanh_apply (x : ℝ) :
    Activation.tanh.apply x = Real.tanh x := rfl

@[simp] lemma Activation.tanh_K :
    Activation.tanh.K = (1 : ℝ) := rfl

end Flean
