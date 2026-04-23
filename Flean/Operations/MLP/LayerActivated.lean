import Flean.Operations.MLP.Layer
import Flean.Operations.Activation

/-!
# Activated Linear Layer

`x ↦ σ(W · x + b)` — a linear layer with a scalar activation applied
componentwise.  Pairs `MLP.Layer` with `Flean.Activation`:

* Math: `ActivatedLayer.forward` = `σ ∘ Layer.forward` componentwise.
* FP: `ActivatedLayerFpResult` bundles a `LayerFpResult` with an
  `ActivationFpResult` witness.

## Contents

* `ActivatedLayer R n_in n_out`: struct bundling `layer` + `activation`.
* `ActivatedLayer.forward` / `.forward_lipschitz` / `.forward_abs_le`
  (via `LipschitzMax.compScalar` / triangle on `σ(y) - σ(0) + σ(0)`).
* `ActivationFpResult σ xs`: per-index FP soundness witness (result +
  slack bound).
* `ActivationFpResult.exact`: zero-slack constructor for exact FP
  activations (e.g., ReLU on FP inputs).
* `ActivatedLayerFpResult`: linear FP result + FP activation result.
* `ActivatedLayerFpResult.errorBound` / `.forward_error_bound`
  (via `LipschitzScalar.errorAmplification`).
-/

set_option autoImplicit false

namespace MLP

open Flean.Lipschitz Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R]

/-! ## ActivatedLayer struct + math forward pass -/

/-- Linear layer + scalar activation, applied componentwise. -/
structure ActivatedLayer (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (n_in n_out : ℕ) where
  /-- Underlying linear layer (weights + bias). -/
  layer : Layer n_in n_out
  /-- Scalar activation function. -/
  activation : Flean.Activation R

/-- Math-level forward pass: `σ(W·x + b)` componentwise. -/
noncomputable def ActivatedLayer.forward {n_in n_out : ℕ}
    (LA : ActivatedLayer R n_in n_out) (x : Fin n_in → R) : Fin n_out → R :=
  fun i => LA.activation.apply (LA.layer.forward x i)

/-! ## Lipschitz instance via compScalar -/

/-- The activated layer is Lipschitz in its input with constant
`σ.K · n_in · wMax`, composed via `LipschitzMax.compScalar`. -/
theorem ActivatedLayer.forward_lipschitz {n_in n_out : ℕ}
    (LA : ActivatedLayer R n_in n_out)
    {wMax bMax : R} (hL : BoundedParams (R := R) LA.layer wMax bMax)
    (hwMax_nn : 0 ≤ wMax) :
    LipschitzMax (R := R) (LA.activation.K * ((n_in : R) * wMax))
      LA.forward := by
  unfold ActivatedLayer.forward
  exact LipschitzMax.compScalar
    (LA.layer.forward_lipschitz hL hwMax_nn) LA.activation.lipschitz

/-! ## Real-valued magnitude bound

For any `K`-Lipschitz `σ`: `|σ(y)| ≤ K · |y| + |σ(0)|`, via triangle
on `σ(y) - σ(0) + σ(0)` plus the Lipschitz bound against `σ(0)`.
For ReLU / identity (`σ(0) = 0`) this collapses to `|σ(y)| ≤ K · |y|`. -/

/-- Magnitude bound for the activated layer's real-valued output. -/
noncomputable def ActivatedLayer.outputBoundReal {n_in n_out : ℕ}
    (LA : ActivatedLayer R n_in n_out) (wMax xMax bMax : R) : R :=
  LA.activation.K * LA.layer.outputBoundReal wMax xMax bMax +
    |LA.activation.apply 0|

omit [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R] in
/-- The real-valued activated forward pass lies within its
algebraic magnitude bound. -/
theorem ActivatedLayer.forward_abs_le {n_in n_out : ℕ}
    (LA : ActivatedLayer R n_in n_out)
    {wMax bMax : R} (hL : BoundedParams (R := R) LA.layer wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {x : Fin n_in → R} {xMax : R}
    (hx : ∀ j, |x j| ≤ xMax) (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |LA.forward x i| ≤ LA.outputBoundReal wMax xMax bMax := by
  unfold ActivatedLayer.forward ActivatedLayer.outputBoundReal
  have h_layer := LA.layer.forward_abs_le hL hwMax_nn hx hxMax_nn i
  have h_lip := LA.activation.lipschitz.bound (LA.layer.forward x i) 0
  rw [sub_zero] at h_lip
  have h_tri : |LA.activation.apply (LA.layer.forward x i)|
              ≤ |LA.activation.apply (LA.layer.forward x i)
                  - LA.activation.apply 0|
                + |LA.activation.apply 0| := by
    have h := abs_add_le
      (LA.activation.apply (LA.layer.forward x i) - LA.activation.apply 0)
      (LA.activation.apply 0)
    simpa using h
  have h_amp : LA.activation.K * |LA.layer.forward x i|
             ≤ LA.activation.K * LA.layer.outputBoundReal wMax xMax bMax :=
    mul_le_mul_of_nonneg_left h_layer LA.activation.K_nn
  linarith

/-! ## FP-level activation soundness

`ActivationFpResult σ xs` is the per-index "my FP activation is close
to the math one" witness.  Framework-level: any FP implementation
(exact ReLU, Taylor sigmoid, table-based tanh, …) packages into this
shape. -/

/-- Per-index FP soundness witness for applying `σ` to an FP vector. -/
structure ActivationFpResult {n : ℕ} (σ : Flean.Activation R)
    (xs : Fin n → FiniteFp) where
  /-- FP output. -/
  result : Fin n → FiniteFp
  /-- Uniform slack bound on the per-index deviation. -/
  slack : R
  /-- Slack is non-negative. -/
  slack_nn : 0 ≤ slack
  /-- Per-index `(result i)` is within `slack` of `σ(xs i)`. -/
  h_close : ∀ i, |((result i).toVal : R) -
    σ.apply ((xs i).toVal : R)| ≤ slack

/-- Exact FP activation: `result i` matches `σ(xs i)` bit-exactly
at the real-valued level.  Zero slack. -/
def ActivationFpResult.exact {n : ℕ} {σ : Flean.Activation R}
    {xs : Fin n → FiniteFp} (result : Fin n → FiniteFp)
    (h_exact : ∀ i, ((result i).toVal : R) = σ.apply ((xs i).toVal : R)) :
    ActivationFpResult σ xs where
  result := result
  slack := 0
  slack_nn := le_refl 0
  h_close := by
    intro i
    rw [h_exact i, sub_self, abs_zero]

/-! ## FP-level activated layer -/

/-- FP-level activated layer result: linear layer result + activation
result fed by the linear stage's output. -/
structure ActivatedLayerFpResult {n_in n_out : ℕ}
    (LA : ActivatedLayer R n_in n_out) (x : Fin n_in → FiniteFp) where
  /-- Pre-activation FP layer. -/
  linear : LayerFpResult LA.layer x R
  /-- FP activation applied to the linear stage's output. -/
  activated : ActivationFpResult LA.activation linear.result

/-! ## FP magnitude bound

Mirrors `LayerFpResult.outputBound` / `toVal_abs_le`.  Compose linear
magnitude with the activation's Lipschitz bound against `σ(0)`, plus
the activation's own FP slack:

```
|result.toVal| ≤ σ.K · linear.outputBound + |σ(0)| + slack
```
-/

/-- FP magnitude bound on an activated layer output. -/
noncomputable def ActivatedLayerFpResult.outputBound {n_in n_out : ℕ}
    {LA : ActivatedLayer R n_in n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedLayerFpResult LA x) (wMax xMax bMax : R) : R :=
  LA.activation.K * res.linear.outputBound wMax xMax bMax +
    |LA.activation.apply 0| + res.activated.slack

/-- FP activated-layer magnitude bound is nonneg under the usual
parameter-nonneg hypotheses. -/
theorem ActivatedLayerFpResult.outputBound_nn {n_in n_out : ℕ}
    {LA : ActivatedLayer R n_in n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedLayerFpResult LA x)
    {wMax xMax bMax : R} (hwMax_nn : 0 ≤ wMax) (hxMax_nn : 0 ≤ xMax)
    (hbMax_nn : 0 ≤ bMax) :
    0 ≤ res.outputBound wMax xMax bMax := by
  unfold ActivatedLayerFpResult.outputBound
  have h_lin := res.linear.outputBound_nn hwMax_nn hxMax_nn hbMax_nn
  have h_amp : 0 ≤ LA.activation.K * res.linear.outputBound wMax xMax bMax :=
    mul_nonneg LA.activation.K_nn h_lin
  have h_abs : 0 ≤ |LA.activation.apply 0| := abs_nonneg _
  have h_slack : 0 ≤ res.activated.slack := res.activated.slack_nn
  linarith

/-- FP magnitude bound on the activated layer output: compose the
linear-stage bound with the activation's Lipschitz bound against `σ(0)`
and add the activation's slack. -/
theorem ActivatedLayerFpResult.toVal_abs_le {n_in n_out : ℕ}
    {LA : ActivatedLayer R n_in n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedLayerFpResult LA x)
    {wMax bMax : R} (hL : BoundedParams (R := R) LA.layer wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.activated.result i).toVal : R)| ≤
      res.outputBound wMax xMax bMax := by
  unfold ActivatedLayerFpResult.outputBound
  have h_lin_mag :=
    res.linear.toVal_abs_le hL hwMax_nn hx hxMax_nn i
  have h_close := res.activated.h_close i
  -- |σ(y) - σ(0)| ≤ σ.K · |y|.
  have h_lip := LA.activation.lipschitz.bound
    ((res.linear.result i).toVal : R) 0
  rw [sub_zero] at h_lip
  -- |σ(y)| ≤ σ.K · |y| + |σ(0)| via triangle.
  have h_sigma_mag : |LA.activation.apply ((res.linear.result i).toVal : R)|
      ≤ LA.activation.K * |((res.linear.result i).toVal : R)| +
        |LA.activation.apply 0| := by
    have h := abs_add_le
      (LA.activation.apply ((res.linear.result i).toVal : R) -
        LA.activation.apply 0)
      (LA.activation.apply 0)
    have h' : |LA.activation.apply ((res.linear.result i).toVal : R)|
        ≤ |LA.activation.apply ((res.linear.result i).toVal : R) -
            LA.activation.apply 0| + |LA.activation.apply 0| := by simpa using h
    linarith
  -- |result.toVal| ≤ slack + |σ(linear.toVal)|.
  have h_tri : |((res.activated.result i).toVal : R)|
      ≤ |((res.activated.result i).toVal : R) -
          LA.activation.apply ((res.linear.result i).toVal : R)| +
        |LA.activation.apply ((res.linear.result i).toVal : R)| := by
    have h := abs_add_le
      (((res.activated.result i).toVal : R) -
        LA.activation.apply ((res.linear.result i).toVal : R))
      (LA.activation.apply ((res.linear.result i).toVal : R))
    simpa using h
  have h_amp : LA.activation.K * |((res.linear.result i).toVal : R)|
      ≤ LA.activation.K * res.linear.outputBound wMax xMax bMax :=
    mul_le_mul_of_nonneg_left h_lin_mag LA.activation.K_nn
  linarith

/-- Named forward-error bound for the activated FP layer.

`slack` is the activation's own FP-vs-math error; `σ.K · layer_error`
is Lipschitz amplification of the linear stage's error. -/
noncomputable def ActivatedLayerFpResult.errorBound {n_in n_out : ℕ}
    {LA : ActivatedLayer R n_in n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedLayerFpResult LA x)
    (wMax xMax bMax : R) : R :=
  res.activated.slack +
    LA.activation.K * res.linear.errorBound wMax xMax bMax

/-- **Activated-layer forward error bound**: FP-vs-math deviation on
`σ(W·x + b)`, composed via `LipschitzScalar.errorAmplification`.

Layer error is amplified by `σ.K`; activation slack adds. -/
theorem ActivatedLayerFpResult.forward_error_bound {n_in n_out : ℕ}
    {LA : ActivatedLayer R n_in n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedLayerFpResult LA x)
    {wMax bMax : R} (hL : BoundedParams (R := R) LA.layer wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.activated.result i).toVal : R) -
        LA.forward (fun j => ((x j).toVal : R)) i| ≤
      res.errorBound wMax xMax bMax := by
  unfold ActivatedLayer.forward ActivatedLayerFpResult.errorBound
  have h_layer := res.linear.forward_error_bound hL hwMax_nn hx hxMax_nn i
  have h_act := res.activated.h_close i
  exact LipschitzScalar.errorAmplification LA.activation.lipschitz h_act h_layer

/-! ## Concrete demo: ReLU on a (4 → 3) layer

Smoke test that the framework actually composes for a real activation.
The ReLU `K = 1` makes the activated bound equal to slack + layer
error. -/

/-- Demo: forward error bound on an activated (4 → 3) layer with the
ReLU activation, specialized to ReLU's `K = 1`.  The general
`errorBound` simplifies to `slack + layer.errorBound` — the layer's
error passes through unamplified. -/
theorem ActivatedLayerFpResult.forward_error_bound_relu_demo
    {M : ActivatedLayer R 4 3} {x : Fin 4 → FiniteFp}
    (res : ActivatedLayerFpResult M x)
    (h_relu : M.activation = Flean.Activation.relu)
    {wMax bMax : R} (hL : BoundedParams (R := R) M.layer wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (i : Fin 3) :
    |((res.activated.result i).toVal : R) -
        M.forward (fun j => ((x j).toVal : R)) i| ≤
      res.activated.slack + res.linear.errorBound wMax xMax bMax := by
  have h_main := res.forward_error_bound hL hwMax_nn hx hxMax_nn i
  unfold ActivatedLayerFpResult.errorBound at h_main
  have h_K : M.activation.K = (1 : R) := by rw [h_relu]; rfl
  rw [h_K, one_mul] at h_main
  exact h_main

end MLP
