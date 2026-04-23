import Flean.Operations.MLP.LayerActivated

/-!
# Activated MLP — 2-Layer Composition

`x ↦ σ₂(W₂ · σ₁(W₁ · x + b₁) + b₂)`.  Two activated linear layers
chained, one on top of the other.  The activated analog of `MLP2`.

## Contents

* `ActivatedMLP2 n_in n_hidden n_out`: pair of activated layers.
* `ActivatedMLP2.forward`: real-valued forward pass.
* `ActivatedMLP2BoundedParams`: parameter-bound tag (per-layer weights/biases).
* `ActivatedMLP2.hiddenBound`, `ActivatedMLP2.outputBound`: real
  magnitude bounds.
* `ActivatedMLP2.forward_abs_le`: real-valued magnitude bound.
* `ActivatedMLP2FpResult`: bundled FP forward pass (layer₁ + layer₂).
* `ActivatedMLP2FpResult.outputBound` + `toVal_abs_le`: FP magnitude bound.
* `ActivatedMLP2FpResult.errorBound` + `forward_error_bound`: FP-vs-real
  bound, composed via `LipschitzMax.errorAmplification` on the second
  activated layer's Lipschitz constant.
* `ActivatedMLP2.forward_lipschitz`: whole-model Lipschitz constant
  via `LipschitzMax.comp`.
* `ActivatedMLP2FpResult.forward_error_bound_relu_demo`: runnable smoke
  test on shape (4 → 3 → 2) with ReLU on both layers.

## Error-bound composition

The bound decomposes as

```
|fp_k − real_k|
  ≤ layer2.errorBound                             (layer₂'s rounding + activation slack)
  + σ₂.K · n_hidden · w2Max · layer1.errorBound   (layer₂ amplifying layer₁'s rounding
                                                   + activation slack)
```

where the amplification constant is the Lipschitz constant of the
second *activated* layer (composed `σ₂ ∘ Layer₂.forward` via
`LipschitzMax.compScalar`).
-/

set_option autoImplicit false

namespace MLP

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## ActivatedMLP2 struct + real-valued forward pass -/

/-- Two activated linear layers: layer 1 maps `n_in → n_hidden`,
layer 2 maps `n_hidden → n_out`. -/
structure ActivatedMLP2 (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (n_in n_hidden n_out : ℕ) where
  /-- First activated layer. -/
  layer1 : ActivatedLayer R n_in n_hidden
  /-- Second activated layer. -/
  layer2 : ActivatedLayer R n_hidden n_out

/-- Real-valued forward pass: `σ₂(W₂ · σ₁(W₁·x + b₁) + b₂)`. -/
noncomputable def ActivatedMLP2.forward {n_in n_hidden n_out : ℕ}
    (M : ActivatedMLP2 R n_in n_hidden n_out) (x : Fin n_in → R) :
    Fin n_out → R :=
  M.layer2.forward (M.layer1.forward x)

/-! ## Bounded-parameter tag -/

/-- Parameter-bound tag for an activated 2-layer MLP.  Tags the
underlying weights/biases of each layer; activations are already
Lipschitz-constrained via their own `K`. -/
structure ActivatedMLP2BoundedParams {n_in n_hidden n_out : ℕ}
    (M : ActivatedMLP2 R n_in n_hidden n_out)
    (w1Max b1Max w2Max b2Max : R) : Prop where
  /-- Layer 1's weights/biases are bounded. -/
  layer1_bounded : BoundedParams (R := R) M.layer1.layer w1Max b1Max
  /-- Layer 2's weights/biases are bounded. -/
  layer2_bounded : BoundedParams (R := R) M.layer2.layer w2Max b2Max

/-! ## Real-valued magnitude bound -/

/-- Magnitude bound on the hidden activations (after `σ₁`). -/
noncomputable def ActivatedMLP2.hiddenBound {n_in n_hidden n_out : ℕ}
    (M : ActivatedMLP2 R n_in n_hidden n_out)
    (w1Max xMax b1Max : R) : R :=
  M.layer1.outputBoundReal w1Max xMax b1Max

/-- Magnitude bound on the output logits (after `σ₂`). -/
noncomputable def ActivatedMLP2.outputBound {n_in n_hidden n_out : ℕ}
    (M : ActivatedMLP2 R n_in n_hidden n_out)
    (w1Max xMax b1Max w2Max b2Max : R) : R :=
  M.layer2.outputBoundReal w2Max (M.hiddenBound w1Max xMax b1Max) b2Max

/-- The real-valued activated 2-layer forward pass lies within its
algebraic output bound. -/
theorem ActivatedMLP2.forward_abs_le {n_in n_hidden n_out : ℕ}
    (M : ActivatedMLP2 R n_in n_hidden n_out)
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {x : Fin n_in → R} {xMax : R}
    (hx : ∀ j, |x j| ≤ xMax) (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |M.forward x i| ≤ M.outputBound w1Max xMax b1Max w2Max b2Max := by
  unfold ActivatedMLP2.forward ActivatedMLP2.outputBound
  have h_hidden : ∀ j, |M.layer1.forward x j| ≤
      M.hiddenBound w1Max xMax b1Max := fun j =>
    M.layer1.forward_abs_le hM.layer1_bounded hw1_nn hx hxMax_nn j
  have h_hbd_nn : 0 ≤ M.hiddenBound w1Max xMax b1Max := by
    unfold ActivatedMLP2.hiddenBound ActivatedLayer.outputBoundReal
    have h_linHidden : 0 ≤ M.layer1.layer.outputBoundReal w1Max xMax b1Max := by
      unfold Layer.outputBoundReal
      have : 0 ≤ (n_in : R) * w1Max * xMax :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hw1_nn) hxMax_nn
      linarith
    have h_amp : 0 ≤
        M.layer1.activation.K * M.layer1.layer.outputBoundReal w1Max xMax b1Max :=
      mul_nonneg M.layer1.activation.K_nn h_linHidden
    have h_abs : 0 ≤ |M.layer1.activation.apply 0| := abs_nonneg _
    linarith
  exact M.layer2.forward_abs_le hM.layer2_bounded hw2_nn h_hidden h_hbd_nn i

/-! ## Whole-model Lipschitz instance -/

variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R]

/-- The activated 2-layer MLP is Lipschitz in its input via
`LipschitzMax.comp` of the two activated-layer Lipschitz constants.
Lipschitz constant: `(σ₂.K · n_hidden · w2Max) · (σ₁.K · n_in · w1Max)`. -/
theorem ActivatedMLP2.forward_lipschitz {n_in n_hidden n_out : ℕ}
    (M : ActivatedMLP2 R n_in n_hidden n_out)
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hw2_nn : 0 ≤ w2Max) :
    Flean.Lipschitz.LipschitzMax (R := R)
      ((M.layer2.activation.K * ((n_hidden : R) * w2Max)) *
        (M.layer1.activation.K * ((n_in : R) * w1Max)))
      M.forward := by
  unfold ActivatedMLP2.forward
  exact Flean.Lipschitz.LipschitzMax.comp
    (M.layer2.forward_lipschitz hM.layer2_bounded hw2_nn)
    (M.layer1.forward_lipschitz hM.layer1_bounded hw1_nn)

/-! ## FP-level activated 2-layer forward pass witness -/

/-- Witness structure for a 2-layer activated MLP FP forward pass.

Bundles the two `ActivatedLayerFpResult`s with the constraint that
layer 2's input is layer 1's *activated* output. -/
structure ActivatedMLP2FpResult {n_in n_hidden n_out : ℕ}
    (M : ActivatedMLP2 R n_in n_hidden n_out) (x : Fin n_in → FiniteFp) where
  /-- Layer 1 activated FP forward pass. -/
  layer1 : ActivatedLayerFpResult M.layer1 x
  /-- Layer 2 activated FP forward pass, input = layer 1's
  activated output. -/
  layer2 : ActivatedLayerFpResult M.layer2 layer1.activated.result

/-! ## FP magnitude bound -/

/-- FP magnitude bound on the activated 2-layer output.

Layer 2 sees layer-1's activated-output bound as its `xMax`. -/
noncomputable def ActivatedMLP2FpResult.outputBound {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    (w1Max xMax b1Max w2Max b2Max : R) : R :=
  res.layer2.outputBound w2Max
    (res.layer1.outputBound w1Max xMax b1Max) b2Max

/-- The FP activated 2-layer output is magnitude-bounded by the
algebraic composition of the two layer bounds. -/
theorem ActivatedMLP2FpResult.toVal_abs_le {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.activated.result k).toVal : R)| ≤
      res.outputBound w1Max xMax b1Max w2Max b2Max := by
  have h_layer1_bound : ∀ j, HasAbsBound (R := R)
      (res.layer1.outputBound w1Max xMax b1Max)
      (res.layer1.activated.result j) := fun j =>
    ⟨res.layer1.toVal_abs_le hM.layer1_bounded hw1_nn hx hxMax_nn j⟩
  have h_hbound_nn : 0 ≤ res.layer1.outputBound w1Max xMax b1Max :=
    res.layer1.outputBound_nn hw1_nn hxMax_nn hb1_nn
  exact res.layer2.toVal_abs_le hM.layer2_bounded hw2_nn
    h_layer1_bound h_hbound_nn k

/-! ## 2-layer forward error bound

The cleanest expression of the error-composition story: layer 2's
own FP-vs-math error (including its activation slack) plus layer 2
amplifying layer 1's error by its *activated* Lipschitz constant
`σ₂.K · n_hidden · w2Max`. -/

/-- Algebraic forward-error bound on the activated 2-layer output. -/
noncomputable def ActivatedMLP2FpResult.errorBound {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    (w1Max xMax b1Max w2Max b2Max : R) : R :=
  res.layer2.errorBound w2Max
    (res.layer1.outputBound w1Max xMax b1Max) b2Max +
  (M.layer2.activation.K * ((n_hidden : R) * w2Max)) *
    res.layer1.errorBound w1Max xMax b1Max

/-- **Activated 2-layer forward error bound**: the activated capstone.

Relates the FP-computed output to the real-valued ground truth.
Combines two error sources:
* layer 2's own error (including its activation slack);
* layer 2 amplifying layer 1's deviation (including layer 1's
  activation slack) via `ActivatedLayer.forward_lipschitz`
  (constant `σ₂.K · n_hidden · w2Max`).

Composed via `LipschitzMax.errorAmplification`. -/
theorem ActivatedMLP2FpResult.forward_error_bound {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.activated.result k).toVal : R) -
        M.forward (fun j => ((x j).toVal : R)) k| ≤
      res.errorBound w1Max xMax b1Max w2Max b2Max := by
  unfold ActivatedMLP2.forward ActivatedMLP2FpResult.errorBound
  -- Layer 1 magnitude tag: feeds into layer 2's forward_error_bound.
  have h_layer1_bound : ∀ j, HasAbsBound (R := R)
      (res.layer1.outputBound w1Max xMax b1Max)
      (res.layer1.activated.result j) := fun j =>
    ⟨res.layer1.toVal_abs_le hM.layer1_bounded hw1_nn hx hxMax_nn j⟩
  have h_hbound_nn : 0 ≤ res.layer1.outputBound w1Max xMax b1Max :=
    res.layer1.outputBound_nn hw1_nn hxMax_nn hb1_nn
  -- Layer 2's own error at the FP-intermediate input.
  have h_outer := res.layer2.forward_error_bound hM.layer2_bounded hw2_nn
    h_layer1_bound h_hbound_nn k
  -- Layer 1's per-index error (includes its activation slack).
  have h_inner : ∀ j,
      |((res.layer1.activated.result j).toVal : R) -
        M.layer1.forward (fun l => ((x l).toVal : R)) j| ≤
      res.layer1.errorBound w1Max xMax b1Max := fun j =>
    res.layer1.forward_error_bound hM.layer1_bounded hw1_nn hx hxMax_nn j
  -- Compose via Lipschitz framework on the *activated* layer 2.
  exact Flean.Lipschitz.LipschitzMax.errorAmplification
    (M.layer2.forward_lipschitz hM.layer2_bounded hw2_nn) h_outer h_inner

/-! ## Parameter-nonneg accessors -/

/-- Derived accessor: `0 ≤ w1Max` from `ActivatedMLP2BoundedParams`
given non-empty layer 1. -/
theorem ActivatedMLP2BoundedParams.w1_nn {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out}
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_in : 0 < n_in) (h_hidden : 0 < n_hidden) :
    (0 : R) ≤ w1Max :=
  hM.layer1_bounded.wMax_nn h_in h_hidden

/-- Derived accessor: `0 ≤ b1Max`. -/
theorem ActivatedMLP2BoundedParams.b1_nn {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out}
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_hidden : 0 < n_hidden) :
    (0 : R) ≤ b1Max :=
  hM.layer1_bounded.bMax_nn h_hidden

/-- Derived accessor: `0 ≤ w2Max`. -/
theorem ActivatedMLP2BoundedParams.w2_nn {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out}
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_hidden : 0 < n_hidden) (h_out : 0 < n_out) :
    (0 : R) ≤ w2Max :=
  hM.layer2_bounded.wMax_nn h_hidden h_out

/-- Derived accessor: `0 ≤ b2Max`. -/
theorem ActivatedMLP2BoundedParams.b2_nn {n_in n_hidden n_out : ℕ}
    {M : ActivatedMLP2 R n_in n_hidden n_out}
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_out : 0 < n_out) :
    (0 : R) ≤ b2Max :=
  hM.layer2_bounded.bMax_nn h_out

/-! ## Concrete demo -/

/-- **Demo**: activated 2-layer MLP with ReLU on both layers.
Specializes the error bound to the (4 → 3 → 2) shape with both
activations set to `Flean.Activation.relu`. -/
theorem ActivatedMLP2FpResult.forward_error_bound_relu_demo
    {M : ActivatedMLP2 R 4 3 2} {x : Fin 4 → FiniteFp}
    (res : ActivatedMLP2FpResult M x)
    {w1Max b1Max w2Max b2Max : R}
    (hM : ActivatedMLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin 2) :
    |((res.layer2.activated.result k).toVal : R) -
        M.forward (fun j => ((x j).toVal : R)) k| ≤
      res.errorBound w1Max xMax b1Max w2Max b2Max := by
  exact res.forward_error_bound hM
    (hM.w1_nn (by decide) (by decide))
    (hM.b1_nn (by decide))
    (hM.w2_nn (by decide) (by decide))
    hx hxMax_nn k

end MLP
