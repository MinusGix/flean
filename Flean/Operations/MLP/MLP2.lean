import Flean.Operations.MLP.Layer

/-!
# MLP — 2-Layer Composition

`x ↦ W₂ · (W₁ · x + b₁) + b₂`.  Linear (no activation), built on
top of `MLP/Layer.lean`.

## Contents

* `MLP2 n_in n_hidden n_out`: pair of layers.
* `MLP2.forward`: real-valued forward pass.
* `MLP2BoundedParams`: parameter-bound tag (per-layer).
* `MLP2.hiddenBound`, `MLP2.outputBound`: real magnitude bounds.
* `MLP2.forward_abs_le`: real-valued magnitude bound.
* `MLP2FpResult`: bundled FP-level forward pass.
* `MLP2FpResult.outputBound` + `toVal_abs_le`: FP magnitude bound.
* `MLP2FpResult.errorBound` + `forward_error_bound`: FP-vs-real bound.
* `MLP2.forward_lipschitz`: 2-layer Lipschitz constant via composition.
* `MLP2BoundedParams.{w1, b1, w2, b2}_nn` accessors.
* `MLP2FpResult.forward_error_bound_demo`: runnable smoke test on
  shape (4 → 3 → 2).
-/

set_option autoImplicit false

namespace MLP

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## MLP2 struct + real-valued forward pass -/

/-- A 2-layer linear MLP: layer 1 maps `n_in → n_hidden`, layer 2
maps `n_hidden → n_out`. -/
structure MLP2 (n_in n_hidden n_out : ℕ) where
  /-- First layer. -/
  layer1 : Layer n_in n_hidden
  /-- Second layer. -/
  layer2 : Layer n_hidden n_out

/-- Real-valued forward pass.  No activation. -/
noncomputable def MLP2.forward {S : Type*}
    [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    {n_in n_hidden n_out : ℕ} (M : MLP2 n_in n_hidden n_out)
    (x : Fin n_in → S) : Fin n_out → S :=
  M.layer2.forward (M.layer1.forward x)

/-! ## Bounded-parameter tag -/

/-- Parameter-bound tag for a 2-layer MLP.  Separate `wMax`/`bMax`
pairs per layer so tight inner layers don't contaminate loose outer
layers (or vice versa). -/
structure MLP2BoundedParams {n_in n_hidden n_out : ℕ}
    (M : MLP2 n_in n_hidden n_out) (w1Max b1Max w2Max b2Max : R) : Prop where
  layer1_bounded : BoundedParams (R := R) M.layer1 w1Max b1Max
  layer2_bounded : BoundedParams (R := R) M.layer2 w2Max b2Max

/-! ## Real-valued magnitude bound -/

/-- Magnitude bound on the hidden activations. -/
noncomputable def MLP2.hiddenBound {n_in n_hidden n_out : ℕ}
    (_M : MLP2 n_in n_hidden n_out) (w1Max xMax b1Max : R) : R :=
  (n_in : R) * w1Max * xMax + b1Max

/-- Magnitude bound on the output logits. -/
noncomputable def MLP2.outputBound {n_in n_hidden n_out : ℕ}
    (M : MLP2 n_in n_hidden n_out) (w1Max xMax b1Max w2Max b2Max : R) : R :=
  (n_hidden : R) * w2Max * M.hiddenBound w1Max xMax b1Max + b2Max

/-- The real-valued 2-layer forward pass lies within its algebraic
output bound. -/
theorem MLP2.forward_abs_le {n_in n_hidden n_out : ℕ}
    (M : MLP2 n_in n_hidden n_out)
    {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {x : Fin n_in → R} {xMax : R}
    (hx : ∀ j, |x j| ≤ xMax) (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |M.forward x i| ≤ M.outputBound w1Max xMax b1Max w2Max b2Max := by
  unfold MLP2.forward MLP2.outputBound
  have h_hidden : ∀ j, |M.layer1.forward x j| ≤
      M.hiddenBound w1Max xMax b1Max := by
    intro j
    exact M.layer1.forward_abs_le hM.layer1_bounded hw1_nn hx hxMax_nn j
  have h_hbd_nn : 0 ≤ M.hiddenBound w1Max xMax b1Max := by
    unfold MLP2.hiddenBound
    have : 0 ≤ (n_in : R) * w1Max * xMax :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hw1_nn) hxMax_nn
    linarith
  exact M.layer2.forward_abs_le hM.layer2_bounded hw2_nn h_hidden h_hbd_nn i

/-! ## 2-layer FP forward pass witness -/

variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R]

/-- Witness structure for a 2-layer MLP FP forward pass.

Bundles the two single-layer results with the constraint that
layer 2's input is layer 1's output. -/
structure MLP2FpResult {n_in n_hidden n_out : ℕ}
    (M : MLP2 n_in n_hidden n_out) (x : Fin n_in → FiniteFp) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] where
  /-- Layer 1 FP forward pass. -/
  layer1 : LayerFpResult M.layer1 x R
  /-- Layer 2 FP forward pass, input = layer 1 output. -/
  layer2 : LayerFpResult M.layer2 layer1.result R

/-! ## 2-layer FP magnitude bound -/

/-- Algebraic magnitude bound on the 2-layer MLP output.

Layer 2 sees layer-1-output-magnitude as its `xMax`. -/
noncomputable def MLP2FpResult.outputBound {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : MLP2FpResult M x R)
    (w1Max xMax b1Max w2Max b2Max : R) : R :=
  res.layer2.outputBound w2Max
    (res.layer1.outputBound w1Max xMax b1Max) b2Max

/-- The FP 2-layer output is magnitude-bounded by the algebraic
composition of the two layer bounds. -/
theorem MLP2FpResult.toVal_abs_le {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : MLP2FpResult M x R)
    {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.result k).toVal : R)| ≤
      res.outputBound w1Max xMax b1Max w2Max b2Max := by
  have h_layer1_bound : ∀ j, HasAbsBound (R := R)
      (res.layer1.outputBound w1Max xMax b1Max) (res.layer1.result j) := fun j =>
    ⟨res.layer1.toVal_abs_le hM.layer1_bounded hw1_nn hx hxMax_nn j⟩
  have h_hbound_nn : 0 ≤ res.layer1.outputBound w1Max xMax b1Max :=
    res.layer1.outputBound_nn hw1_nn hxMax_nn hb1_nn
  exact res.layer2.toVal_abs_le hM.layer2_bounded hw2_nn h_layer1_bound h_hbound_nn k

/-! ## 2-layer Lipschitz instance -/

/-- 2-layer MLP is Lipschitz in its input via `LipschitzMax.comp`.
Lipschitz constant: `(n_hidden · w2Max) · (n_in · w1Max)`.

Note: this is the **whole-MLP** Lipschitz constant — useful for
input-perturbation analyses (adversarial robustness, confidence
bounds), distinct from `forward_error_bound` which uses *per-layer*
Lipschitz amplification of *rounding* error. -/
theorem MLP2.forward_lipschitz {n_in n_hidden n_out : ℕ}
    (M : MLP2 n_in n_hidden n_out)
    {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hw2_nn : 0 ≤ w2Max) :
    Flean.Lipschitz.LipschitzMax (R := R)
      (((n_hidden : R) * w2Max) * ((n_in : R) * w1Max))
      M.forward := by
  unfold MLP2.forward
  exact Flean.Lipschitz.LipschitzMax.comp
    (M.layer2.forward_lipschitz hM.layer2_bounded hw2_nn)
    (M.layer1.forward_lipschitz hM.layer1_bounded hw1_nn)

/-! ## 2-layer forward error bound

Compositional: layer 2's own error + layer 2 amplifying layer 1's
error via the Lipschitz framework.

```
|fp_k − real_k| ≤ layer2_error + n_hidden · w2Max · layer1_error
```
-/

/-- Algebraic forward-error bound on the 2-layer MLP output. -/
noncomputable def MLP2FpResult.errorBound {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : MLP2FpResult M x R)
    (w1Max xMax b1Max w2Max b2Max : R) : R :=
  res.layer2.errorBound w2Max
    (res.layer1.outputBound w1Max xMax b1Max) b2Max +
  (n_hidden : R) * w2Max * res.layer1.errorBound w1Max xMax b1Max

/-- **2-layer forward error bound**: the full capstone.

Relates the FP-computed output to the real-valued ground truth.
Combines two rounding sources: layer 2's own error, plus layer 2
amplifying layer 1's deviation via `Layer.forward_lipschitz`
(Lipschitz constant `n_hidden · w2Max`). -/
theorem MLP2FpResult.forward_error_bound {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : MLP2FpResult M x R)
    {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.result k).toVal : R) -
        M.forward (fun j => ((x j).toVal : R)) k| ≤
      res.errorBound w1Max xMax b1Max w2Max b2Max := by
  unfold MLP2.forward MLP2FpResult.errorBound
  -- Layer 1 magnitude tag: feeds into layer 2's forward_error_bound.
  have h_layer1_bound : ∀ j, HasAbsBound (R := R)
      (res.layer1.outputBound w1Max xMax b1Max) (res.layer1.result j) := fun j =>
    ⟨res.layer1.toVal_abs_le hM.layer1_bounded hw1_nn hx hxMax_nn j⟩
  have h_hbound_nn : 0 ≤ res.layer1.outputBound w1Max xMax b1Max :=
    res.layer1.outputBound_nn hw1_nn hxMax_nn hb1_nn
  -- Layer 2's own error at the FP-intermediate input.
  have h_outer := res.layer2.forward_error_bound hM.layer2_bounded hw2_nn
    h_layer1_bound h_hbound_nn k
  -- Layer 1's per-index error.
  have h_inner : ∀ j,
      |((res.layer1.result j).toVal : R) -
        M.layer1.forward (fun l => ((x l).toVal : R)) j| ≤
      res.layer1.errorBound w1Max xMax b1Max := fun j =>
    res.layer1.forward_error_bound hM.layer1_bounded hw1_nn hx hxMax_nn j
  -- Compose via Lipschitz framework.
  exact Flean.Lipschitz.LipschitzMax.errorAmplification
    (M.layer2.forward_lipschitz hM.layer2_bounded hw2_nn) h_outer h_inner

/-! ## MLP2 helpers -/

/-- 2-layer accessors: weight nonneg accessors derived from the layer
parameter-bounded sub-structures. -/
theorem MLP2BoundedParams.w1_nn {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_in : 0 < n_in) (h_hidden : 0 < n_hidden) :
    (0 : R) ≤ w1Max :=
  hM.layer1_bounded.wMax_nn h_in h_hidden

theorem MLP2BoundedParams.b1_nn {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_hidden : 0 < n_hidden) :
    (0 : R) ≤ b1Max :=
  hM.layer1_bounded.bMax_nn h_hidden

theorem MLP2BoundedParams.w2_nn {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_hidden : 0 < n_hidden) (h_out : 0 < n_out) :
    (0 : R) ≤ w2Max :=
  hM.layer2_bounded.wMax_nn h_hidden h_out

theorem MLP2BoundedParams.b2_nn {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (h_out : 0 < n_out) :
    (0 : R) ≤ b2Max :=
  hM.layer2_bounded.bMax_nn h_out

/-! ## Ergonomic variant: dim-positivity discharges nonneg hypotheses

`_auto` variants take dim-positivity witnesses (`0 < n_in`, etc.)
instead of parameter-nonneg hypotheses (`0 ≤ w1Max`, etc.).  The
latter are derived via `MLP2BoundedParams.{w1,b1,w2,b2}_nn` accessors.
For concrete shapes, the positivity witnesses discharge via
`by decide`. -/

/-- `_auto` variant of `forward_error_bound`: takes dim-positivity
instead of parameter-nonneg.  Derives `0 ≤ w1Max` / `0 ≤ b1Max` /
`0 ≤ w2Max` from `hM` via the nonneg accessors. -/
theorem MLP2FpResult.forward_error_bound_auto {n_in n_hidden n_out : ℕ}
    (h_in : 0 < n_in) (h_hidden : 0 < n_hidden) (h_out : 0 < n_out)
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : MLP2FpResult M x R)
    {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((res.layer2.result k).toVal : R) -
        M.forward (fun j => ((x j).toVal : R)) k| ≤
      res.errorBound w1Max xMax b1Max w2Max b2Max :=
  res.forward_error_bound hM
    (hM.w1_nn h_in h_hidden) (hM.b1_nn h_hidden) (hM.w2_nn h_hidden h_out)
    hx hxMax_nn k

/-! ## Concrete demo -/

/-- **Demo**: invoking the 2-layer error bound on a concrete network
shape (4 → 3 → 2) via the `_auto` variant.  No specific weight values
needed; the theorem is statement-level applicable.  The `_auto` form
routes through the parameter-nonneg accessors, so only the `(by decide)`
dim-positivity witnesses are visible at the call site. -/
theorem MLP2FpResult.forward_error_bound_demo
    {M : MLP2 4 3 2} {x : Fin 4 → FiniteFp}
    (res : MLP2FpResult M x R)
    {w1Max b1Max w2Max b2Max : R}
    (hM : MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin 2) :
    |((res.layer2.result k).toVal : R) -
        M.forward (fun j => ((x j).toVal : R)) k| ≤
      res.errorBound w1Max xMax b1Max w2Max b2Max :=
  res.forward_error_bound_auto (by decide) (by decide) (by decide)
    hM hx hxMax_nn k

end MLP
