import Flean.Operations.FpMatVec
import Flean.Operations.Add
import Flean.Operations.Lipschitz
import Flean.Tags.AbsBoundPropagate
import Flean.Tags.BundleAbsBound
import Flean.Tags.BoundedRange
import Flean.Tags.BoundedRangePropagate

/-!
# MLP — Single Linear Layer

`x ↦ W · x + b`.  The atomic building block of the MLP capstone.

## Contents

* `Layer n_in n_out`: weight matrix + bias vector.
* `Layer.forward`: real-valued forward pass.
* `BoundedParams L wMax bMax`: parameter-bound tag.
* `Layer.outputBoundReal`: algebraic real-output magnitude bound.
* `Layer.forward_abs_le`: real-valued forward magnitude bound.
* `LayerFpResult`: bundled FP-level forward pass (matvec + bias add).
* `LayerFpResult.outputBound` + `toVal_abs_le`: FP magnitude bound.
* `LayerFpResult.errorBound` + `forward_error_bound`: FP-vs-real error bound.
* `Layer.forward_lipschitz`: layer is `n_in · wMax`-Lipschitz in input.
* `BoundedParams.ofHasAbsBound` / `.toHasAbsBound_W` / `.toHasAbsBound_b`:
  tag-framework bridges.
* `BoundedParams.wMax_nn` / `bMax_nn`: parameter-nonneg accessors
  (need nonempty witness).

The 2-layer composition lives in `MLP/MLP2.lean`.
-/

set_option autoImplicit false

namespace MLP

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Layer struct + real-valued forward pass -/

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

/-! ## Parameter-bound tag -/

/-- Parameter constraints for a single layer: weights in `[-wMax, wMax]`,
biases in `[-bMax, bMax]`. -/
structure BoundedParams {n_in n_out : ℕ} (L : Layer n_in n_out)
    (wMax bMax : R) : Prop where
  /-- Every weight entry is bounded. -/
  weight_bounded : ∀ i j, |((L.W i j).toVal : R)| ≤ wMax
  /-- Every bias entry is bounded. -/
  bias_bounded : ∀ i, |((L.b i).toVal : R)| ≤ bMax

/-! ## Real-valued magnitude bound -/

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

/-! ## FP-level forward pass + magnitude/error bounds -/

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

/-- Single-layer FP magnitude bound via composition of
`FpMatVecBound.hasAbsBound_of_uniform` + `HasAbsBound.fpAdd_unified`. -/
theorem LayerFpResult.toVal_abs_le {n_in n_out : ℕ}
    {L : Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (res : LayerFpResult L x R)
    {wMax bMax : R} (hL : BoundedParams (R := R) L wMax bMax)
    (_hwMax_nn : 0 ≤ wMax)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (_hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.result i).toVal : R)| ≤ res.outputBound wMax xMax bMax := by
  have h_W : ∀ i' j, HasAbsBound (R := R) wMax (L.W i' j) :=
    fun i' j => ⟨hL.weight_bounded i' j⟩
  have h_matvec_absbound :=
    res.matvec.hasAbsBound_of_uniform wMax xMax h_W hx i
  have h_bias_absbound : HasAbsBound (R := R) bMax (L.b i) :=
    ⟨hL.bias_bounded i⟩
  have h_add := HasAbsBound.fpAdd_unified h_matvec_absbound h_bias_absbound
    (res.h_add i)
  have h_eq : res.outputBound wMax xMax bMax =
      (1 + (η : R)) *
        (res.matvec.magBound (R := R) wMax xMax + bMax) +
        FpInterval.subnormalConst := by
    unfold LayerFpResult.outputBound FpMatVec.FpMatVecBound.magBound
    ring
  rw [h_eq]
  exact h_add.toVal_abs_le

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
up to `errorBound`.

Composes `FpMatVecBound.hasAbsBound_of_uniform` (matvec magnitude),
`FpMatVecBound.errorBound_of_uniform` (matvec FP-vs-exact error), and
`round_preserves_abs_error_unified` on the bias add. -/
theorem LayerFpResult.forward_error_bound {n_in n_out : ℕ}
    {L : Layer n_in n_out} {x : Fin n_in → FiniteFp}
    (res : LayerFpResult L x R)
    {wMax bMax : R} (hL : BoundedParams (R := R) L wMax bMax)
    (_hwMax_nn : 0 ≤ wMax)
    {xMax : R} (hx : ∀ j, HasAbsBound (R := R) xMax (x j))
    (_hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.result i).toVal : R) -
        L.forward (fun j => ((x j).toVal : R)) i| ≤
      res.errorBound wMax xMax bMax := by
  unfold Layer.forward LayerFpResult.errorBound
  have h_W : ∀ i' j, HasAbsBound (R := R) wMax (L.W i' j) :=
    fun i' j => ⟨hL.weight_bounded i' j⟩
  obtain ⟨g, hg_round, hg_eq⟩ :=
    fpAddFinite_round_witness (R := R) (res.matvec.result i) (L.b i) (res.h_add i)
  have h_addErr := round_preserves_abs_error_unified (R := R)
    ((res.matvec.result i).toVal + (L.b i).toVal) hg_round
  have h_result_add :
      |((res.result i).toVal : R) -
        (((res.matvec.result i).toVal : R) + ((L.b i).toVal : R))| ≤
      (η : R) * |((res.matvec.result i).toVal : R) + ((L.b i).toVal : R)| +
        FpInterval.subnormalConst := by
    have := h_addErr
    rw [hg_eq] at this
    exact this
  -- Matvec magnitude via the bundle bridge.
  have h_matvec_absbound :=
    res.matvec.hasAbsBound_of_uniform wMax xMax h_W hx i
  have h_matvec_bound : |((res.matvec.result i).toVal : R)| ≤
      (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax := by
    have := h_matvec_absbound.toVal_abs_le
    unfold FpMatVec.FpMatVecBound.magBound at this
    nlinarith [this]
  have h_mpb :
      |((res.matvec.result i).toVal : R) + ((L.b i).toVal : R)| ≤
      (1 + res.matvec.relErr) * (n_in : R) * wMax * xMax + bMax :=
    le_trans (abs_add_le _ _) (by linarith [hL.bias_bounded i])
  -- Matvec FP-vs-exact error via the bundle bridge.
  have h_matvec_err_raw :=
    res.matvec.errorBound_of_uniform wMax xMax h_W hx i
  have h_matvec_err :
      |((res.matvec.result i).toVal : R) -
         ∑ j, ((L.W i j).toVal : R) * ((x j).toVal : R)| ≤
      res.matvec.relErr * ((n_in : R) * wMax * xMax) := by
    nlinarith [h_matvec_err_raw]
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

/-! ## Lipschitz instance for `Layer.forward` -/

/-- **Layer is Lipschitz in its input** with constant `n_in · wMax`.
Stated as `LipschitzMax` so it composes via the framework's
`LipschitzMax.comp`. -/
theorem Layer.forward_lipschitz {n_in n_out : ℕ} (L : Layer n_in n_out)
    {wMax bMax : R} (hL : BoundedParams (R := R) L wMax bMax)
    (hwMax_nn : 0 ≤ wMax) :
    Flean.Lipschitz.LipschitzMax (R := R) ((n_in : R) * wMax) L.forward where
  K_nn := mul_nonneg (Nat.cast_nonneg _) hwMax_nn
  bound := by
    intro δ x x' h_dx i
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
          exact mul_le_mul (hL.weight_bounded i j) (h_dx j) (abs_nonneg _) hwMax_nn
      _ = (n_in : R) * (wMax * δ) := by
          rw [Finset.sum_const]; simp [mul_comm]
      _ = (n_in : R) * wMax * δ := by ring

/-! ## Helpers and tag-framework bridges

`BoundedParams` is a self-contained struct, but the wider tag framework
speaks `HasAbsBound`.  Bridges in both directions plus parameter-nonneg
accessors make the layer interoperate cleanly. -/

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

/-- **Parameter-nonneg accessor** for `wMax`.  When the layer has at
least one weight entry, `wMax` is non-negative — derivable from
`0 ≤ |W_ij| ≤ wMax`. -/
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

end MLP
