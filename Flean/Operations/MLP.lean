import Flean.Operations.FpMatVec
import Flean.Operations.Add
import Flean.Tags.AbsBoundPropagate
import Flean.Tags.BundleAbsBound
import Flean.Tags.BoundedRange
import Flean.Tags.BoundedRangePropagate

/-!
# Verified Forward Pass of a 2-Layer Linear MLP

**End-to-end capstone.**  Composes every major primitive the library
has built — `FpMatVec`, `FpDotProduct`, `fpAddFinite`, `IsBoundedRange`,
`HasAbsBound` propagation, bundle bridges — over a realistic ML
workload: a 2-layer multilayer perceptron with constrained
("pixel-style") input.

## Scope

- **Linear** (no activation): each layer is `x ↦ W · x + b`.  Leaving
  activation (ReLU/GeLU/tanh) as a follow-up that needs an operation-
  layer piecewise-linearity hook.
- **Fixed precision** (same `FloatFormat` throughout — no
  mixed-precision yet).
- **Constrained inputs**: `IsBoundedRange ⟨0, 1⟩ x` — the
  "pixel values in `[0, 1]`" idiom of image-classification demos.
- **Bounded parameters**: weights and biases each carry
  `IsBoundedRange ⟨-wMax, wMax⟩` / `IsBoundedRange ⟨-bMax, bMax⟩`.

## Main results

1. **`fpMLP2_magnitude_bound`** — forward magnitude bound on the
   MLP output, computed algebraically from the input / weight bounds
   and the dimensions via `HasAbsBound` propagation through each
   layer.
2. **`fpMLP2_forward_error_bound`** — forward error bound relating
   the FP-computed output to the real-valued ground-truth output.

Both bounds are proved compositionally: layer 1 gives `h_j` bounds;
layer 2 composes to give `logits_k` bounds.  The tag framework does
the magnitude propagation; the bundle bridges (`FpDotProductBound`,
`FpMatVecBound`) do the relative-error propagation.

## Design note

The capstone is deliberately a minimal MLP — the goal is to
demonstrate **composition** of the shipped stack, not to showcase
sophisticated network architectures.  Adding ReLU, layer norm,
softmax+CE on top, training dynamics, etc. are all natural
follow-ups.

The bounds are not *tight* — the point is that they exist, compose
mechanically from input-side tag data, and produce a concrete
inequality you could evaluate against a specific format.
-/

set_option autoImplicit false

namespace MLP

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Single-layer definitions -/

/-- Parameters of a single linear layer `x ↦ W · x + b`. -/
structure Layer (n_in n_out : ℕ) where
  /-- Weight matrix: rows are outputs, columns are inputs. -/
  W : Fin n_out → Fin n_in → FiniteFp
  /-- Bias vector: one entry per output. -/
  b : Fin n_out → FiniteFp

/-- Real-valued forward pass of a single layer. -/
noncomputable def Layer.forward {n_in n_out : ℕ} (L : Layer n_in n_out)
    (x : Fin n_in → R) : Fin n_out → R :=
  fun i => (∑ j, ((L.W i j).toVal : R) * x j) + ((L.b i).toVal : R)

/-! ## Single-layer tag + bounds -/

/-- Parameter constraints for a single layer: weights in `[-wMax, wMax]`,
biases in `[-bMax, bMax]`. -/
structure BoundedParams {n_in n_out : ℕ} (L : Layer n_in n_out)
    (wMax bMax : R) : Prop where
  /-- Every weight entry is bounded. -/
  weight_bounded : ∀ i j, |((L.W i j).toVal : R)| ≤ wMax
  /-- Every bias entry is bounded. -/
  bias_bounded : ∀ i, |((L.b i).toVal : R)| ≤ bMax

/-- The ambient bound on any single output entry of the layer's real-valued
forward pass when inputs are magnitude-bounded by `xMax`.

`|W_i · x + b_i| ≤ n · wMax · xMax + bMax`. -/
noncomputable def Layer.outputBoundReal {n_in n_out : ℕ} (_L : Layer n_in n_out)
    (wMax xMax bMax : R) : R :=
  (n_in : R) * wMax * xMax + bMax

/-- The real-valued forward pass lies within its algebraic magnitude bound.

Requires `0 ≤ wMax` explicitly because `BoundedParams` alone doesn't
imply it (the constraint is vacuous for empty matrices). -/
theorem Layer.forward_abs_le {n_in n_out : ℕ} (L : Layer n_in n_out)
    {wMax bMax : R} (hL : BoundedParams L wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {x : Fin n_in → R} {xMax : R} (hx : ∀ j, |x j| ≤ xMax) (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |L.forward x i| ≤ L.outputBoundReal wMax xMax bMax := by
  unfold Layer.forward Layer.outputBoundReal
  have h_sum_bound :
      |∑ j, ((L.W i j).toVal : R) * x j| ≤
        (n_in : R) * wMax * xMax := by
    calc |∑ j, ((L.W i j).toVal : R) * x j|
        ≤ ∑ j, |((L.W i j).toVal : R) * x j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n_in, wMax * xMax := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul (hL.weight_bounded i j) (hx j) (abs_nonneg _) hwMax_nn
      _ = (n_in : R) * (wMax * xMax) := by
          rw [Finset.sum_const]; simp [mul_comm]
      _ = (n_in : R) * wMax * xMax := by ring
  have h_tri :
      |(∑ j, ((L.W i j).toVal : R) * x j) + ((L.b i).toVal : R)| ≤
        |∑ j, ((L.W i j).toVal : R) * x j| + |((L.b i).toVal : R)| :=
    abs_add_le _ _
  linarith [hL.bias_bounded i]

/-! ## FP-level forward pass -/

variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R]

/-- Witness structure bundling a single FP layer forward pass.

Ingredients:
- `matvec` — row-wise dot products via `FpMatVecBound`.
- `result` — per-index FP outputs.
- `h_add` — each `result i = fpAddFinite (matvec.result i) (L.b i)`. -/
structure LayerFpResult {n_in n_out : ℕ} (L : Layer n_in n_out)
    (x : Fin n_in → FiniteFp) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] where
  /-- Matrix-vector product bundle. -/
  matvec : FpMatVec.FpMatVecBound L.W x R
  /-- Final per-index output after bias add. -/
  result : Fin n_out → FiniteFp
  /-- FP correctness of the bias add. -/
  h_add : ∀ i, fpAddFinite (matvec.result i) (L.b i) = Fp.finite (result i)

/-! ## Single-layer FP magnitude bound

Given parameter bounds + input magnitude bound, each FP layer output
is magnitude-bounded by the real-output bound times `(1 + relErr)`
plus `subnormalConst` rounding slack. -/

/-- Named magnitude bound for a single FP layer output:
`(1+η) · ((1+matvec.relErr) · n_in · wMax · xMax + bMax) + subnormalConst`.
Exactly the output shape of `HasAbsBound.fpAdd_unified`. -/
noncomputable def LayerFpResult.outputBound {n_in n_out : ℕ}
    {L : Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (res : LayerFpResult L x R)
    (wMax xMax bMax : R) : R :=
  (1 + (η : R)) *
    ((1 + res.matvec.relErr) * (n_in : R) * wMax * xMax + bMax) +
    FpInterval.subnormalConst

/-- Single-layer FP magnitude bound via composition of the bundle
bridge + `HasAbsBound.fpAdd_unified`. -/
theorem LayerFpResult.toVal_abs_le {n_in n_out : ℕ}
    {L : Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (res : LayerFpResult L x R)
    {wMax bMax : R} (hL : BoundedParams (R := R) L wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.result i).toVal : R)| ≤ res.outputBound wMax xMax bMax := by
  -- Matvec-step magnitude: (1+relErr) · n · wMax · xMax.
  have h_matvec_bound : |((res.matvec.result i).toVal : R)| ≤
      (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax := by
    have h_err := res.matvec.h_bound i
    have h_sum_prod_bound :
        ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
          (n_in : R) * (wMax * xMax) := by
      calc ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)|
          ≤ ∑ _j : Fin n_in, wMax * xMax := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            exact mul_le_mul (hL.weight_bounded i j) (hx j).toVal_abs_le
              (abs_nonneg _) hwMax_nn
        _ = (n_in : R) * (wMax * xMax) := by
            rw [Finset.sum_const]; simp [mul_comm]
    have h_sum_abs_bound :
        |∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
          (n_in : R) * (wMax * xMax) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) h_sum_prod_bound
    have h_tri :
        |((res.matvec.result i).toVal : R)| ≤
          |((res.matvec.result i).toVal : R) -
            ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| +
          |∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| := by
      have : |(((res.matvec.result i).toVal : R) -
               ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)) +
              ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
             |((res.matvec.result i).toVal : R) -
               ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| +
             |∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| := abs_add_le _ _
      simpa using this
    have h_relErr_nn := res.matvec.h_relErr_nn
    have h_err_scaled : res.matvec.relErr *
        ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
        res.matvec.relErr * ((n_in : R) * (wMax * xMax)) :=
      mul_le_mul_of_nonneg_left h_sum_prod_bound h_relErr_nn
    calc |((res.matvec.result i).toVal : R)|
        ≤ _ := h_tri
      _ ≤ res.matvec.relErr *
            ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| +
          (n_in : R) * (wMax * xMax) := by linarith
      _ ≤ res.matvec.relErr * ((n_in : R) * (wMax * xMax)) +
          (n_in : R) * (wMax * xMax) := by linarith
      _ = (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax := by ring
  -- Compose via HasAbsBound.fpAdd_unified.
  have h_matvec_absbound :
      HasAbsBound (R := R)
        ((1 + res.matvec.relErr) * (n_in : R) * wMax * xMax)
        (res.matvec.result i) := ⟨h_matvec_bound⟩
  have h_bias_absbound : HasAbsBound (R := R) bMax (L.b i) :=
    ⟨hL.bias_bounded i⟩
  have h_add := HasAbsBound.fpAdd_unified h_matvec_absbound h_bias_absbound
    (res.h_add i)
  exact h_add.toVal_abs_le

/-! ## Single-layer forward error bound

Relates `result_i.toVal` to the real-valued layer output
`L.forward x.toVal i = Σ W_ij · x_j.toVal + b_i.toVal`.  Two
rounding sources compose additively: the matvec's relative error on
the dot product, and the unified bias-add's `η·|·| + subnormalConst`
slack. -/

/-- Named forward-error bound for a single FP layer.

`matvec.relErr · n · wMax · xMax` is the matvec-step contribution;
`η · ((1+matvec.relErr)·n·wMax·xMax + bMax) + subnormalConst` is the
bias-add-step contribution. -/
noncomputable def LayerFpResult.errorBound {n_in n_out : ℕ}
    {L : Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (res : LayerFpResult L x R) (wMax xMax bMax : R) : R :=
  res.matvec.relErr * (n_in : R) * wMax * xMax +
    ((η : R) *
      ((1 + res.matvec.relErr) * (n_in : R) * wMax * xMax + bMax) +
      FpInterval.subnormalConst)

/-- The FP layer output is close to the real-valued layer output,
up to `errorBound`. -/
theorem LayerFpResult.forward_error_bound {n_in n_out : ℕ}
    {L : Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (res : LayerFpResult L x R)
    {wMax bMax : R} (hL : BoundedParams (R := R) L wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.result i).toVal : R) -
        L.forward (fun j => ((x j).toVal : R)) i| ≤
      res.errorBound wMax xMax bMax := by
  unfold Layer.forward LayerFpResult.errorBound
  -- Bias add's round witness.
  obtain ⟨g, hg_round, hg_eq⟩ :=
    fpAddFinite_round_witness (R := R) (res.matvec.result i) (L.b i) (res.h_add i)
  have h_addErr := round_preserves_abs_error_unified (R := R)
    ((res.matvec.result i).toVal + (L.b i).toVal) hg_round
  -- |result_i.toVal - (matvec_i.toVal + b_i.toVal)| ≤ η·|matvec_i + b_i| + sc
  have h_result_add :
      |((res.result i).toVal : R) -
        (((res.matvec.result i).toVal : R) + ((L.b i).toVal : R))| ≤
      (η : R) * |((res.matvec.result i).toVal : R) + ((L.b i).toVal : R)| +
        FpInterval.subnormalConst := by
    have := h_addErr
    rw [hg_eq] at this
    exact this
  -- Triangle: |matvec_i + b_i| ≤ (1+relErr)·n·wMax·xMax + bMax.
  have h_matvec_bound : |((res.matvec.result i).toVal : R)| ≤
      (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax := by
    -- (Same proof as in toVal_abs_le; inlined to avoid re-abstracting.)
    have h_sum_prod_bound :
        ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
          (n_in : R) * (wMax * xMax) := by
      calc ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)|
          ≤ ∑ _j : Fin n_in, wMax * xMax := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            exact mul_le_mul (hL.weight_bounded i j) (hx j).toVal_abs_le
              (abs_nonneg _) hwMax_nn
        _ = (n_in : R) * (wMax * xMax) := by
            rw [Finset.sum_const]; simp [mul_comm]
    have h_sum_abs_bound :
        |∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
          (n_in : R) * (wMax * xMax) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) h_sum_prod_bound
    have h_err := res.matvec.h_bound i
    have h_tri :
        |((res.matvec.result i).toVal : R)| ≤
          |((res.matvec.result i).toVal : R) -
            ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| +
          |∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| := by
      have : |(((res.matvec.result i).toVal : R) -
               ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)) +
              ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
             |((res.matvec.result i).toVal : R) -
               ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| +
             |∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| := abs_add_le _ _
      simpa using this
    have h_relErr_nn := res.matvec.h_relErr_nn
    have h_err_scaled : res.matvec.relErr *
        ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
        res.matvec.relErr * ((n_in : R) * (wMax * xMax)) :=
      mul_le_mul_of_nonneg_left h_sum_prod_bound h_relErr_nn
    calc |((res.matvec.result i).toVal : R)|
        ≤ _ := h_tri
      _ ≤ res.matvec.relErr *
            ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| +
          (n_in : R) * (wMax * xMax) := by linarith
      _ ≤ res.matvec.relErr * ((n_in : R) * (wMax * xMax)) +
          (n_in : R) * (wMax * xMax) := by linarith
      _ = (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax := by ring
  have h_mpb :
      |((res.matvec.result i).toVal : R) + ((L.b i).toVal : R)| ≤
      (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax + bMax :=
    le_trans (abs_add_le _ _) (by linarith [hL.bias_bounded i])
  -- Matvec error: |matvec_i - Σ W·x| ≤ relErr · Σ|W·x| ≤ relErr · n · wMax · xMax.
  have h_matvec_err :
      |((res.matvec.result i).toVal : R) -
         ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
      res.matvec.relErr * ((n_in : R) * wMax * xMax) := by
    have h_err := res.matvec.h_bound i
    have h_sum_prod_bound :
        ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
          (n_in : R) * (wMax * xMax) := by
      calc ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)|
          ≤ ∑ _j : Fin n_in, wMax * xMax := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            exact mul_le_mul (hL.weight_bounded i j) (hx j).toVal_abs_le
              (abs_nonneg _) hwMax_nn
        _ = (n_in : R) * (wMax * xMax) := by
            rw [Finset.sum_const]; simp [mul_comm]
    have := mul_le_mul_of_nonneg_left h_sum_prod_bound res.matvec.h_relErr_nn
    calc |((res.matvec.result i).toVal : R) -
            ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)|
        ≤ res.matvec.relErr *
            ∑ j, |((L.W i j).toVal : R) * ((x j).toVal : R)| := h_err
      _ ≤ res.matvec.relErr * ((n_in : R) * (wMax * xMax)) := this
      _ = res.matvec.relErr * ((n_in : R) * wMax * xMax) := by ring
  -- Compose via triangle:
  --   |result_i - (Σ W·x + b_i)| ≤ |result_i - (matvec + b_i)| + |matvec - Σ W·x|.
  have h_triangle :
      |((res.result i).toVal : R) -
         ((∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)) + ((L.b i).toVal : R))| ≤
      |((res.result i).toVal : R) -
         (((res.matvec.result i).toVal : R) + ((L.b i).toVal : R))| +
      |((res.matvec.result i).toVal : R) -
         ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| := by
    have h_split :
        ((res.result i).toVal : R) -
           ((∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)) + ((L.b i).toVal : R)) =
        (((res.result i).toVal : R) -
           (((res.matvec.result i).toVal : R) + ((L.b i).toVal : R))) +
        (((res.matvec.result i).toVal : R) -
           ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)) := by ring
    rw [h_split]
    exact abs_add_le _ _
  have h_η_scaled :
      (η : R) * |((res.matvec.result i).toVal : R) + ((L.b i).toVal : R)| ≤
      (η : R) *
        ((1 + res.matvec.relErr) * (n_in : R) * wMax * xMax + bMax) := by
    have hη_nn : (0 : R) ≤ (η : R) := by positivity
    exact mul_le_mul_of_nonneg_left h_mpb hη_nn
  linarith

end MLP

/-! ## 2-Layer MLP

Linear 2-layer MLP: `x ↦ W₂ · (W₁ · x + b₁) + b₂`.
Intermediate activations `h := W₁ · x + b₁` are left unactivated
(this is the capstone's main simplification). -/

namespace MLP

open Finset BigOperators Flean.Tags

variable [FloatFormat]

/-- A 2-layer linear MLP: layer 1 maps `n_in → n_hidden`, layer 2
maps `n_hidden → n_out`. -/
structure MLP2 (n_in n_hidden n_out : ℕ) where
  /-- First layer. -/
  layer1 : Layer n_in n_hidden
  /-- Second layer. -/
  layer2 : Layer n_hidden n_out

/-- Real-valued forward pass.  No activation. -/
noncomputable def MLP2.forward {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {n_in n_hidden n_out : ℕ} (M : MLP2 n_in n_hidden n_out)
    (x : Fin n_in → R) : Fin n_out → R :=
  M.layer2.forward (M.layer1.forward x)

/-! ## Bounded-parameter tag for the 2-layer network -/

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Parameter-bound tag for a 2-layer MLP.  Separate `wMax`/`bMax`
pairs per layer so tight inner layers don't contaminate loose outer
layers (or vice versa). -/
structure MLP2BoundedParams {n_in n_hidden n_out : ℕ}
    (M : MLP2 n_in n_hidden n_out) (w1Max b1Max w2Max b2Max : R) : Prop where
  layer1_bounded : BoundedParams (R := R) M.layer1 w1Max b1Max
  layer2_bounded : BoundedParams (R := R) M.layer2 w2Max b2Max

/-! ## Real-valued magnitude bound

Compositional: the hidden layer's bound becomes the input bound for
the output layer. -/

/-- Magnitude bound on the hidden activations. -/
noncomputable def MLP2.hiddenBound {n_in n_hidden n_out : ℕ}
    (_M : MLP2 n_in n_hidden n_out) (w1Max xMax b1Max : R) : R :=
  (n_in : R) * w1Max * xMax + b1Max

/-- Magnitude bound on the output logits. -/
noncomputable def MLP2.outputBound {n_in n_hidden n_out : ℕ}
    (M : MLP2 n_in n_hidden n_out) (w1Max xMax b1Max w2Max b2Max : R) : R :=
  (n_hidden : R) * w2Max * M.hiddenBound w1Max xMax b1Max + b2Max

/-- The real-valued 2-layer forward pass lies within its algebraic
output bound.  Takes `0 ≤ w1Max, 0 ≤ b1Max, 0 ≤ w2Max` as explicit
hypotheses (vacuous at empty dimensions otherwise). -/
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

/-! ## 2-Layer FP output bound -/

/-- Algebraic magnitude bound on the 2-layer MLP output.

Layer 2 sees layer-1-output-magnitude as its `xMax`.  The bound is
`(1+η)·((1+matvec2.relErr)·n_hidden·w2Max·h_bound + b2Max) + sc`,
where `h_bound := layer1.outputBound w1Max xMax b1Max` is the
layer-1 magnitude. -/
noncomputable def MLP2FpResult.outputBound {n_in n_hidden n_out : ℕ}
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (res : MLP2FpResult M x R)
    (w1Max xMax b1Max w2Max b2Max : R) : R :=
  res.layer2.outputBound w2Max
    (res.layer1.outputBound w1Max xMax b1Max) b2Max

/-- Layer-output magnitude bound is nonneg under the usual
parameter-nonneg hypotheses.  Follows by unfolding the def. -/
theorem LayerFpResult.outputBound_nn {n_in n_out : ℕ}
    {L : Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (res : LayerFpResult L x R)
    {wMax xMax bMax : R} (hwMax_nn : 0 ≤ wMax) (hxMax_nn : 0 ≤ xMax)
    (hbMax_nn : 0 ≤ bMax) :
    0 ≤ res.outputBound wMax xMax bMax := by
  unfold LayerFpResult.outputBound
  have h_relErr_nn := res.matvec.h_relErr_nn
  have hη_nn : (0 : R) ≤ (η : R) := by positivity
  have h_sc_nn := FpInterval.subnormalConst_nn (R := R)
  have h1_plus_relErr : (0 : R) ≤ 1 + res.matvec.relErr := by linarith
  have h_first : (0 : R) ≤
      (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax :=
    mul_nonneg (mul_nonneg (mul_nonneg h1_plus_relErr (Nat.cast_nonneg _)) hwMax_nn) hxMax_nn
  have h_inner : (0 : R) ≤
      (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax + bMax := by linarith
  have h_scaled : (0 : R) ≤
      (1 + (η : R)) *
        ((1 + res.matvec.relErr) * (n_in : R) * wMax * xMax + bMax) :=
    mul_nonneg (by linarith) h_inner
  linarith

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

/-! ## 2-layer forward error bound

Compositional: layer 2's own error + layer 2 amplifying layer 1's
error.  Amplification is `n_hidden · w2Max` per output, from the
linearity of layer 2 in its input.

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

/-- Layer 2's forward pass is linear in its input: replacing the
input by a perturbed version changes each output by at most
`n_hidden · w2Max · (perturbation magnitude)`. -/
private theorem Layer.forward_perturbation {n_in n_out : ℕ}
    (L : Layer n_in n_out)
    {wMax bMax : R} (hL : BoundedParams (R := R) L wMax bMax)
    (hwMax_nn : 0 ≤ wMax)
    (x x' : Fin n_in → R) {δ : R}
    (h_δ : ∀ j, |x j - x' j| ≤ δ)
    (i : Fin n_out) :
    |L.forward x i - L.forward x' i| ≤ (n_in : R) * wMax * δ := by
  unfold Layer.forward
  have h_sub :
      ((∑ j, ((L.W i j).toVal : R) * x j) + ((L.b i).toVal : R)) -
      ((∑ j, ((L.W i j).toVal : R) * x' j) + ((L.b i).toVal : R)) =
      ∑ j, ((L.W i j).toVal : R) * (x j - x' j) := by
    have h_collapse :
        ((∑ j, ((L.W i j).toVal : R) * x j) + ((L.b i).toVal : R)) -
        ((∑ j, ((L.W i j).toVal : R) * x' j) + ((L.b i).toVal : R)) =
        (∑ j, ((L.W i j).toVal : R) * x j) -
        (∑ j, ((L.W i j).toVal : R) * x' j) := by ring
    rw [h_collapse, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [h_sub]
  calc |∑ j, ((L.W i j).toVal : R) * (x j - x' j)|
      ≤ ∑ j, |((L.W i j).toVal : R) * (x j - x' j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n_in, wMax * δ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hL.weight_bounded i j) (h_δ j) (abs_nonneg _) hwMax_nn
    _ = (n_in : R) * (wMax * δ) := by
        rw [Finset.sum_const]; simp [mul_comm]
    _ = (n_in : R) * wMax * δ := by ring

/-- **2-layer forward error bound**: the full capstone.

Relates the FP-computed output to the real-valued ground truth over
the R-lifted inputs.  Combines two rounding sources:

1. Layer 1 → layer 2's rounding + matvec error (captured by
   `res.layer2.forward_error_bound` using `h_bound` as layer-2 input
   magnitude).
2. Layer 2 amplifying layer 1's real-input-vs-FP-output deviation
   (via `Layer.forward_perturbation`, bounded by `n_hidden ·
   w2Max · layer1.errorBound`).
-/
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
  -- Layer 1 HasAbsBound output.
  have h_layer1_bound : ∀ j, HasAbsBound (R := R)
      (res.layer1.outputBound w1Max xMax b1Max) (res.layer1.result j) := fun j =>
    ⟨res.layer1.toVal_abs_le hM.layer1_bounded hw1_nn hx hxMax_nn j⟩
  have h_hbound_nn : 0 ≤ res.layer1.outputBound w1Max xMax b1Max :=
    res.layer1.outputBound_nn hw1_nn hxMax_nn hb1_nn
  -- Layer 2 forward-error bound with `h = layer1.result`.
  have h_layer2_err := res.layer2.forward_error_bound hM.layer2_bounded hw2_nn
    h_layer1_bound h_hbound_nn k
  -- Layer 1 per-index error.
  have h_layer1_err : ∀ j,
      |((res.layer1.result j).toVal : R) -
        M.layer1.forward (fun l => ((x l).toVal : R)) j| ≤
      res.layer1.errorBound w1Max xMax b1Max := fun j =>
    res.layer1.forward_error_bound hM.layer1_bounded hw1_nn hx hxMax_nn j
  -- Layer 2 amplification.
  have h_ampl := M.layer2.forward_perturbation hM.layer2_bounded hw2_nn
    (fun j => ((res.layer1.result j).toVal : R))
    (M.layer1.forward (fun l => ((x l).toVal : R)))
    h_layer1_err k
  -- Triangle: |L2.fp - L2.real(L1.real)| ≤ |L2.fp - L2.real(L1.fp_lifted)|
  --                                         + |L2.real(L1.fp_lifted) - L2.real(L1.real)|.
  have h_triangle :
      |((res.layer2.result k).toVal : R) -
        M.layer2.forward
          (M.layer1.forward (fun l => ((x l).toVal : R))) k| ≤
      |((res.layer2.result k).toVal : R) -
        M.layer2.forward (fun j => ((res.layer1.result j).toVal : R)) k| +
      |M.layer2.forward (fun j => ((res.layer1.result j).toVal : R)) k -
        M.layer2.forward
          (M.layer1.forward (fun l => ((x l).toVal : R))) k| := by
    have h_split :
        ((res.layer2.result k).toVal : R) -
          M.layer2.forward
            (M.layer1.forward (fun l => ((x l).toVal : R))) k =
        (((res.layer2.result k).toVal : R) -
          M.layer2.forward
            (fun j => ((res.layer1.result j).toVal : R)) k) +
        (M.layer2.forward
            (fun j => ((res.layer1.result j).toVal : R)) k -
         M.layer2.forward
            (M.layer1.forward (fun l => ((x l).toVal : R))) k) := by ring
    rw [h_split]; exact abs_add_le _ _
  linarith

/-! ## Helpers and tag-framework bridges

The MLP capstone defines `BoundedParams` as a self-contained struct,
but the wider tag framework speaks `HasAbsBound`.  Bridges in both
directions plus parameter-nonneg accessors make the capstone
interoperate cleanly with downstream tag consumers and free callers
from re-deriving obvious facts. -/

/-- Derive `BoundedParams` from per-entry `HasAbsBound` tags. -/
theorem BoundedParams.ofHasAbsBound {n_in n_out : ℕ}
    {L : Layer n_in n_out} {wMax bMax : R}
    (h_W : ∀ i j, HasAbsBound (R := R) wMax (L.W i j))
    (h_b : ∀ i, HasAbsBound (R := R) bMax (L.b i)) :
    BoundedParams (R := R) L wMax bMax where
  weight_bounded := fun i j => (h_W i j).toVal_abs_le
  bias_bounded := fun i => (h_b i).toVal_abs_le

/-- Project a `BoundedParams` to per-entry `HasAbsBound` tags on the weights. -/
theorem BoundedParams.toHasAbsBound_W {n_in n_out : ℕ}
    {L : Layer n_in n_out} {wMax bMax : R}
    (h : BoundedParams (R := R) L wMax bMax) (i : Fin n_out) (j : Fin n_in) :
    HasAbsBound (R := R) wMax (L.W i j) :=
  ⟨h.weight_bounded i j⟩

/-- Project a `BoundedParams` to per-entry `HasAbsBound` tags on the biases. -/
theorem BoundedParams.toHasAbsBound_b {n_in n_out : ℕ}
    {L : Layer n_in n_out} {wMax bMax : R}
    (h : BoundedParams (R := R) L wMax bMax) (i : Fin n_out) :
    HasAbsBound (R := R) bMax (L.b i) :=
  ⟨h.bias_bounded i⟩

/-- **Parameter-nonneg accessor** for `wMax` (M5).  When the layer
has at least one weight entry, `wMax` is non-negative — derivable
from `0 ≤ |W_ij| ≤ wMax`. -/
theorem BoundedParams.wMax_nn {n_in n_out : ℕ}
    {L : Layer n_in n_out} {wMax bMax : R}
    (h : BoundedParams (R := R) L wMax bMax)
    (h_in : 0 < n_in) (h_out : 0 < n_out) :
    (0 : R) ≤ wMax :=
  le_trans (abs_nonneg _) (h.weight_bounded ⟨0, h_out⟩ ⟨0, h_in⟩)

/-- **Parameter-nonneg accessor** for `bMax`.  When the layer has at
least one output, `bMax` is non-negative. -/
theorem BoundedParams.bMax_nn {n_in n_out : ℕ}
    {L : Layer n_in n_out} {wMax bMax : R}
    (h : BoundedParams (R := R) L wMax bMax)
    (h_out : 0 < n_out) :
    (0 : R) ≤ bMax :=
  le_trans (abs_nonneg _) (h.bias_bounded ⟨0, h_out⟩)

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

/-! ## Concrete demo (M8)

A runnable smoke test: the 2-layer error bound applies to a specific
network shape, with parameter-nonneg derived automatically from the
accessors above. -/

/-- **Demo**: invoking the 2-layer error bound on a concrete network
shape (4 → 3 → 2).  No specific weight values needed; the theorem
is statement-level applicable.  The accessors discharge nonneg
hypotheses automatically. -/
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
      res.errorBound w1Max xMax b1Max w2Max b2Max := by
  exact res.forward_error_bound hM
    (hM.w1_nn (by decide) (by decide))
    (hM.b1_nn (by decide))
    (hM.w2_nn (by decide) (by decide))
    hx hxMax_nn k

end MLP
