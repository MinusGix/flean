import Flean.Operations.Lipschitz

/-!
# Scalar Activation Functions

A bundled abstraction for scalar activation functions used in ML —
ReLU, sigmoid, tanh, GeLU, etc.  Each is paired with its Lipschitz
constant so that forward-error analyses over activated layers
compose via the existing `LipschitzMax.compScalar` and
`LipschitzScalar.errorAmplification` primitives.

## Contents

* `Activation R`: math function `R → R` + Lipschitz constant + proof.
* `Activation.identity`: the trivial activation (1-Lipschitz).
* `Activation.relu`: max(0, x), 1-Lipschitz.
* `Activation.applyVec`: componentwise application to a vector.
* `Activation.applyVec_lipschitz`: componentwise application is
  `σ.K`-Lipschitz as a vector function.

## Design

* `R`-parametric, matching `LipschitzScalar`.  The same activation
  record works over ℚ, ℝ, or any ordered field.
* `K` is a field of the struct (not a parameter), so different
  activations coexist with different constants without type-gymnastics.
* Math-level only.  A matching FP-level activation is an independent
  concept (see `MLP/LayerActivated.lean` for the FP integration
  that pairs an `Activation R` with an FP implementation via a
  slack-based soundness witness).
-/

set_option autoImplicit false

namespace Flean

open Flean.Lipschitz

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A scalar activation function bundled with its Lipschitz constant. -/
structure Activation (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] where
  /-- The underlying math function. -/
  apply : R → R
  /-- Lipschitz constant. -/
  K : R
  /-- Proof that `apply` is `K`-Lipschitz. -/
  lipschitz : LipschitzScalar K apply

namespace Activation

/-- Lipschitz constant is non-negative. -/
theorem K_nn (σ : Activation R) : 0 ≤ σ.K := σ.lipschitz.K_nn

/-! ## Standard instances -/

/-- The trivial identity activation: 1-Lipschitz. -/
def identity : Activation R where
  apply := fun x => x
  K := 1
  lipschitz := LipschitzScalar.refl

/-- ReLU activation `max 0 x`: 1-Lipschitz.

Proof strategy: `max 0 x - max 0 y ≤ |x - y|` is established by a
three-way case split on the sign of `x`; the two-directional
`|max 0 a - max 0 b| ≤ |a - b|` follows by symmetry. -/
noncomputable def relu : Activation R where
  apply := fun x => max 0 x
  K := 1
  lipschitz := {
    K_nn := zero_le_one
    bound := by
      intro a b
      simp only [one_mul]
      -- Single-direction bound, valid for any two arguments.
      have key : ∀ x y : R, max 0 x - max 0 y ≤ |x - y| := by
        intro x y
        rcases le_total 0 x with hx | hx
        · rcases le_total 0 y with hy | hy
          · rw [max_eq_right hx, max_eq_right hy]
            exact le_abs_self _
          · rw [max_eq_right hx, max_eq_left hy, sub_zero]
            calc x ≤ x - y := by linarith
              _ ≤ |x - y| := le_abs_self _
        · rw [max_eq_left hx]
          have h_nonneg : 0 ≤ max 0 y := le_max_left _ _
          linarith [abs_nonneg (x - y)]
      apply abs_sub_le_iff.mpr
      refine ⟨key a b, ?_⟩
      calc max 0 b - max 0 a
          ≤ |b - a| := key b a
        _ = |a - b| := abs_sub_comm b a
  }

/-! ## Componentwise application -/

/-- Componentwise application of a scalar activation to a vector. -/
def applyVec {n : ℕ} (σ : Activation R) (x : Fin n → R) : Fin n → R :=
  fun i => σ.apply (x i)

/-- Componentwise application is `σ.K`-Lipschitz as a vector function.

Specializes `LipschitzMax.compScalar` with the identity vector
function, giving a freestanding Lipschitz bound for `σ.applyVec`. -/
theorem applyVec_lipschitz {n : ℕ} (σ : Activation R) :
    LipschitzMax (R := R) σ.K (fun x : Fin n → R => σ.applyVec x) where
  K_nn := σ.K_nn
  bound := by
    intro δ x x' h_dx i
    unfold applyVec
    exact σ.lipschitz.bound (x i) (x' i) |>.trans
      (mul_le_mul_of_nonneg_left (h_dx i) σ.K_nn)

end Activation

end Flean
