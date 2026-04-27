import Flean.Operations.Activation
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sigmoid as a `Flean.Activation`

Wraps Mathlib's `Real.sigmoid` as a `Flean.Activation ℝ` with proven
Lipschitz constant `K = 1/4`.

## Main results

* `Real.sigmoid_deriv_le_quarter` — `s·(1−s) ≤ 1/4` for `s = σ(x)`.
* `Real.sigmoid_deriv_nonneg` — the derivative is nonneg.
* `Real.abs_deriv_sigmoid_le_quarter` — `|σ'(x)| ≤ 1/4`.
* `Flean.Real.sigmoid_lipschitz_quarter` — `Real.sigmoid` is `(1/4)`-Lipschitz on ℝ
  (in flean's `LipschitzScalar` shape).
* `Flean.Activation.sigmoid : Flean.Activation ℝ` — the bundled instance.

The Lipschitz bound is the canonical max of `s·(1−s)` for `s ∈ [0, 1]`,
attained at `s = 1/2`.
-/

set_option autoImplicit false

namespace Real

/-- Algebraic bound: `s·(1−s) ≤ 1/4` for any `s : ℝ`, via `(s − 1/2)² ≥ 0`.
Specialised here to `Real.sigmoid x`. -/
lemma sigmoid_deriv_le_quarter (x : ℝ) :
    Real.sigmoid x * (1 - Real.sigmoid x) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]

/-- Sigmoid's derivative is nonneg: `σ(x)·(1−σ(x)) ≥ 0` since `σ(x) ∈ (0, 1)`. -/
lemma sigmoid_deriv_nonneg (x : ℝ) :
    0 ≤ Real.sigmoid x * (1 - Real.sigmoid x) := by
  have h1 := Real.sigmoid_pos x
  have h2 := Real.sigmoid_le_one x
  have h3 : 0 ≤ 1 - Real.sigmoid x := by linarith
  positivity

/-- `|σ'(x)| ≤ 1/4` (real-valued absolute value). -/
lemma abs_deriv_sigmoid_le_quarter (x : ℝ) :
    |deriv Real.sigmoid x| ≤ (1 / 4 : ℝ) := by
  rw [Real.deriv_sigmoid, abs_of_nonneg (Real.sigmoid_deriv_nonneg x)]
  exact Real.sigmoid_deriv_le_quarter x

end Real

namespace Flean

open Flean.Lipschitz

/-- **Real.sigmoid is `(1/4)`-Lipschitz on ℝ** (flean's `LipschitzScalar` shape).

Proof via Mathlib's MVT (`Convex.norm_image_sub_le_of_norm_deriv_le`) on
`Set.univ` with derivative bound `|σ'(x)| = σ(x)·(1−σ(x)) ≤ 1/4`. -/
theorem Real.sigmoid_lipschitz_quarter :
    LipschitzScalar (R := ℝ) (1 / 4) Real.sigmoid where
  K_nn := by norm_num
  bound := by
    intro a b
    have h_diff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ Real.sigmoid x :=
      fun x _ => differentiable_sigmoid x
    have h_bnd : ∀ x ∈ (Set.univ : Set ℝ),
        ‖deriv Real.sigmoid x‖ ≤ (1 / 4 : ℝ) := by
      intro x _
      rw [Real.norm_eq_abs]
      exact _root_.Real.abs_deriv_sigmoid_le_quarter x
    have key := convex_univ.norm_image_sub_le_of_norm_deriv_le
      h_diff h_bnd (Set.mem_univ b) (Set.mem_univ a)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at key

/-- The sigmoid activation, bundled as `Flean.Activation ℝ` with Lipschitz
constant `1/4`. -/
noncomputable def Activation.sigmoid : Activation ℝ where
  apply := Real.sigmoid
  K := 1 / 4
  lipschitz := _root_.Flean.Real.sigmoid_lipschitz_quarter

@[simp] lemma Activation.sigmoid_apply (x : ℝ) :
    Activation.sigmoid.apply x = Real.sigmoid x := rfl

@[simp] lemma Activation.sigmoid_K :
    Activation.sigmoid.K = (1 / 4 : ℝ) := rfl

end Flean
