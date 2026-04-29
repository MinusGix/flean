import Flean.Operations.Activations.SigmoidFpClose
import Flean.Operations.Activations.TanhFpClose
import Flean.Operations.MLP.ActivatedMLP2

/-!
# `ActivatedMLP2` demos with concrete activations

End-to-end forward-error-bound demos for the 2-layer activated MLP,
specialised at `K = 1/4` (sigmoid) and `K = 1` (tanh) and a mixed
sigmoid → tanh chain.  Each one unfolds the activation error
decomposition so the per-layer activation slack and linear error
appear explicitly.

The bound shape after specialisation:

```
  (slack₂ + K₂ · linear₂.errorBound)                          (layer 2 own error)
+ (K₂ · n_hidden · w2Max) · (slack₁ + K₁ · linear₁.errorBound)  (layer 2 amplifying layer 1)
```

with `K = 1/4` for sigmoid and `K = 1` for tanh (and ReLU).

These demos validate that the `ActivatedMLP2` framework composes with
the FP sigmoid/tanh kernels shipped in `SigmoidFpClose` / `TanhFpClose`
without further plumbing.
-/

set_option autoImplicit false

namespace MLP

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]

open Flean.Tags

/-- **Demo**: activated 2-layer MLP with sigmoid on both layers.
`K₁ = K₂ = 1/4` makes both the layer-2 own-error and the cross-layer
amplification halve at each Lipschitz factor:

```
  (slack₂ + (1/4) · linear₂.errorBound)
+ ((1/4) · n_hidden · w2Max) · (slack₁ + (1/4) · linear₁.errorBound)
```
-/
theorem ActivatedMLP2FpResult.forward_error_bound_sigmoid_demo
    {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 ℝ n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    (h_sig1 : M.layer1.activation = Flean.Activation.sigmoid)
    (h_sig2 : M.layer2.activation = Flean.Activation.sigmoid)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : ActivatedMLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.activated.result k).toVal : ℝ) -
        M.forward (fun j => ((x j).toVal : ℝ)) k| ≤
      (res.layer2.activated.slack +
          (1 / 4 : ℝ) * res.layer2.linear.errorBound w2Max
            (res.layer1.outputBound w1Max xMax b1Max) b2Max) +
      ((1 / 4 : ℝ) * ((n_hidden : ℝ) * w2Max)) *
        (res.layer1.activated.slack +
          (1 / 4 : ℝ) * res.layer1.linear.errorBound w1Max xMax b1Max) := by
  have h_main := res.forward_error_bound hM hw1_nn hb1_nn hw2_nn hx hxMax_nn k
  have h_K1 : M.layer1.activation.K = (1 / 4 : ℝ) := by rw [h_sig1]; rfl
  have h_K2 : M.layer2.activation.K = (1 / 4 : ℝ) := by rw [h_sig2]; rfl
  unfold ActivatedMLP2FpResult.errorBound at h_main
  unfold ActivatedLayerFpResult.errorBound at h_main
  rw [h_K1, h_K2] at h_main
  exact h_main

/-- **Demo**: activated 2-layer MLP with tanh on both layers.
`K₁ = K₂ = 1` makes both Lipschitz factors collapse to the unit, so
the bound matches the relu-shape with only the linear errors and
activation slacks visible:

```
  (slack₂ + linear₂.errorBound)
+ (n_hidden · w2Max) · (slack₁ + linear₁.errorBound)
```
-/
theorem ActivatedMLP2FpResult.forward_error_bound_tanh_demo
    {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 ℝ n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    (h_tanh1 : M.layer1.activation = Flean.Activation.tanh)
    (h_tanh2 : M.layer2.activation = Flean.Activation.tanh)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : ActivatedMLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.activated.result k).toVal : ℝ) -
        M.forward (fun j => ((x j).toVal : ℝ)) k| ≤
      (res.layer2.activated.slack +
          res.layer2.linear.errorBound w2Max
            (res.layer1.outputBound w1Max xMax b1Max) b2Max) +
      ((n_hidden : ℝ) * w2Max) *
        (res.layer1.activated.slack +
          res.layer1.linear.errorBound w1Max xMax b1Max) := by
  have h_main := res.forward_error_bound hM hw1_nn hb1_nn hw2_nn hx hxMax_nn k
  have h_K1 : M.layer1.activation.K = (1 : ℝ) := by rw [h_tanh1]; rfl
  have h_K2 : M.layer2.activation.K = (1 : ℝ) := by rw [h_tanh2]; rfl
  unfold ActivatedMLP2FpResult.errorBound at h_main
  unfold ActivatedLayerFpResult.errorBound at h_main
  rw [h_K1, h_K2, one_mul, one_mul, one_mul] at h_main
  exact h_main

/-- **Demo**: mixed activations — sigmoid on layer 1, tanh on layer 2.
Shows the framework handles heterogeneous activations.  `K₂ = 1`
(tanh) keeps the outer cross-layer factor unitary, while `K₁ = 1/4`
(sigmoid) attenuates layer 1's linear error inside the amplified term:

```
  (slack₂ + linear₂.errorBound)
+ (n_hidden · w2Max) · (slack₁ + (1/4) · linear₁.errorBound)
```
-/
theorem ActivatedMLP2FpResult.forward_error_bound_sigmoid_tanh_demo
    {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 ℝ n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    (h_sig1 : M.layer1.activation = Flean.Activation.sigmoid)
    (h_tanh2 : M.layer2.activation = Flean.Activation.tanh)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : ActivatedMLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.activated.result k).toVal : ℝ) -
        M.forward (fun j => ((x j).toVal : ℝ)) k| ≤
      (res.layer2.activated.slack +
          res.layer2.linear.errorBound w2Max
            (res.layer1.outputBound w1Max xMax b1Max) b2Max) +
      ((n_hidden : ℝ) * w2Max) *
        (res.layer1.activated.slack +
          (1 / 4 : ℝ) * res.layer1.linear.errorBound w1Max xMax b1Max) := by
  have h_main := res.forward_error_bound hM hw1_nn hb1_nn hw2_nn hx hxMax_nn k
  have h_K1 : M.layer1.activation.K = (1 / 4 : ℝ) := by rw [h_sig1]; rfl
  have h_K2 : M.layer2.activation.K = (1 : ℝ) := by rw [h_tanh2]; rfl
  unfold ActivatedMLP2FpResult.errorBound at h_main
  unfold ActivatedLayerFpResult.errorBound at h_main
  rw [h_K1, h_K2, one_mul, one_mul] at h_main
  exact h_main

end MLP
