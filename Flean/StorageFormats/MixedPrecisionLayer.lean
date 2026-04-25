import Flean.StorageFormats.MixedPrecision
import Flean.StorageFormats.NarrowingContext
import Flean.StorageFormats.ToFp
import Flean.StorageFormats.TagBridge
import Flean.Operations.MLP.Layer

/-!
# Mixed-precision linear layer (R6.5)

A linear layer `y = Wx + b` with weights and biases stored in a *narrow*
storage format `sf` (e.g., E4M3), computing in a *wider* arithmetic
format (e.g., Binary32), and narrowing the result back to `sf`.

The pipeline per output row `i`:

```
W_i, x  : Fin n_in → StorageFp sf      (E4M3)
  │   widen (exact, FitsInNormal)
  ▼
W_i_w, x_w : Fin n_in → FiniteFp ff_wide  (Binary32)
  │   wide-format dot-product (FpDotProductBound, error: relErr · Σ|w·x|)
  │   wide-format bias add (η_wide · |·| + tail_wide)
  ▼
withBias_i : FiniteFp ff_wide
  │   narrow (η_sf · |·| + tail_sf)
  ▼
result_i : StorageFp sf                  (E4M3)
```

Composes the existing `MLP.LayerFpResult` (wide-format layer) with the
mixed-precision narrowing chain shipped in R6.

## Caller responsibilities

The bound theorem takes:
- A wide-format `MLP.LayerFpResult` for the *widened* layer.
- A `NarrowingContext` for `sf`.
- Per-row narrow-round witnesses (finiteness, no-overflow,
  `avoidsNanReservedEncoding`).
- Bounded-parameter hypotheses on the storage layer.

Output: per-row error bound `|result.toVal - exact| ≤ closed-form` in
`(wMax, xMax, bMax, η_wide, η_sf, n_in, layerRes.relErr, tails)`.
-/

set_option autoImplicit false

namespace StorageFp

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Layer struct + real-valued forward pass -/

/-- A linear layer with weights and biases stored in narrow `sf`. -/
structure MixedPrecisionLayer (sf : StorageFormat) (n_in n_out : ℕ) where
  /-- Weight matrix: rows are outputs, columns are inputs. -/
  W : Fin n_out → Fin n_in → StorageFp sf
  /-- Bias vector. -/
  b : Fin n_out → StorageFp sf

/-- Real-valued forward pass: `y_i = Σ W_ij · x_j + b_i`, in `R`. -/
noncomputable def MixedPrecisionLayer.forward {sf : StorageFormat} {n_in n_out : ℕ}
    (L : MixedPrecisionLayer sf n_in n_out) (x : Fin n_in → R) : Fin n_out → R :=
  fun i => (∑ j, ((L.W i j).toVal : R) * x j) + ((L.b i).toVal : R)

/-! ## Widening to a wide-format `MLP.Layer`

The wide-format computation in R6.5 is performed via the existing
`MLP.LayerFpResult` infrastructure.  To use it, we widen the storage
layer to a `MLP.Layer` whose `W`, `b` are `FiniteFp` at the ambient
wide format.
-/

section Widening

variable [ff_wide : FloatFormat]

/-- Widen the storage layer to a wide-format `MLP.Layer`. -/
noncomputable def MixedPrecisionLayer.widen {sf : StorageFormat} {n_in n_out : ℕ}
    (L : MixedPrecisionLayer sf n_in n_out)
    (h_FIN_W : ∀ i j, (L.W i j).isFinite) (h_FIN_b : ∀ i, (L.b i).isFinite)
    (h_widen : sf.FitsInNormal ff_wide) :
    MLP.Layer n_in n_out :=
  { W := fun i j => (L.W i j).toFiniteFpWiden ff_wide h_widen (h_FIN_W i j)
    b := fun i => (L.b i).toFiniteFpWiden ff_wide h_widen (h_FIN_b i) }

/-- Widening preserves the real-valued forward pass: the widened
layer's `forward` (in `R`) on widened inputs equals the storage
layer's `forward` on the storage inputs' real values. -/
theorem MixedPrecisionLayer.forward_widen {sf : StorageFormat} {n_in n_out : ℕ}
    (L : MixedPrecisionLayer sf n_in n_out)
    (h_FIN_W : ∀ i j, (L.W i j).isFinite) (h_FIN_b : ∀ i, (L.b i).isFinite)
    (h_widen : sf.FitsInNormal ff_wide)
    (x : Fin n_in → StorageFp sf) (h_FIN_x : ∀ j, (x j).isFinite) (i : Fin n_out) :
    (L.widen h_FIN_W h_FIN_b h_widen).forward (R := R)
      (fun j => ((x j).toFiniteFpWiden ff_wide h_widen (h_FIN_x j)).toVal) i
      = L.forward (fun j => ((x j).toVal : R)) i := by
  unfold MLP.Layer.forward MixedPrecisionLayer.forward MixedPrecisionLayer.widen
  simp only
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [StorageFp.toFiniteFpWiden_toVal, StorageFp.toFiniteFpWiden_toVal]
  · rw [StorageFp.toFiniteFpWiden_toVal]

end Widening

/-! ## FP-level forward + per-row error bound -/

section FpForward

variable [ff_wide : FloatFormat]
variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeZero R]

/-- Witness bundle for a mixed-precision layer's FP computation.

Carries:
- `wide` — the wide-format `MLP.LayerFpResult` for the widened layer
  (matvec + bias add in `ff_wide`).
- `result` — the narrowed per-row outputs in storage format.
- The per-row witnesses connecting `wide.result i` to `result i` via
  the narrowing chain.
-/
structure MixedPrecisionLayerFpResult {sf : StorageFormat} {n_in n_out : ℕ}
    (L : MixedPrecisionLayer sf n_in n_out) (x : Fin n_in → StorageFp sf)
    (h_FIN_W : ∀ i j, (L.W i j).isFinite) (h_FIN_b : ∀ i, (L.b i).isFinite)
    (h_FIN_x : ∀ j, (x j).isFinite) (h_widen : sf.FitsInNormal ff_wide)
    (nctx : NarrowingContext R sf) where
  /-- The wide-format layer FP result. -/
  wide : MLP.LayerFpResult (L.widen h_FIN_W h_FIN_b h_widen)
    (fun j => (x j).toFiniteFpWiden ff_wide h_widen (h_FIN_x j)) R
  /-- The per-row narrowed storage outputs. -/
  result : Fin n_out → StorageFp sf
  /-- Per-row narrow-round target: rounding `wide.result i` produces a finite. -/
  fp_narrow : Fin n_out → @FiniteFp nctx.floatFormat
  /-- The narrow-round equation. -/
  h_round : ∀ i, @RMode.round R nctx.floatFormat nctx.instM
    ((wide.result i).toVal : R) = @Fp.finite nctx.floatFormat (fp_narrow i)
  /-- The wide intermediate has nonzero significand (used by no-overflow). -/
  hm : ∀ i, (wide.result i).m ≠ 0
  /-- No-overflow witness for each row's narrow round. -/
  h_no_ov : ∀ i, (StorageFp.roundSigCore (wide.result i).s (wide.result i).m
      ((wide.result i).e - ff_wide.prec + 1) (sf.manBits + 1)
      (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
      StorageFp.rneRoundUp).2.2 = false
  /-- NaN-pattern avoidance for each row. -/
  h_no_nan : ∀ i, avoidsNanReservedEncoding sf
      (StorageFp.roundSigCore (wide.result i).s (wide.result i).m
        ((wide.result i).e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).1
      (StorageFp.roundSigCore (wide.result i).s (wide.result i).m
        ((wide.result i).e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).2.1
  /-- The narrowed storage result equals `fromFp` of the wide intermediate. -/
  h_result : ∀ i, result i = @StorageFp.fromFp ff_wide sf .saturate
      (@Fp.finite ff_wide (wide.result i))

/-- Closed-form per-row error bound: combines the wide-format
`LayerFpResult.errorBound` with the narrowing tail. -/
noncomputable def MixedPrecisionLayerFpResult.errorBound
    {sf : StorageFormat} {n_in n_out : ℕ}
    {L : MixedPrecisionLayer sf n_in n_out} {x : Fin n_in → StorageFp sf}
    {h_FIN_W : ∀ i j, (L.W i j).isFinite} {h_FIN_b : ∀ i, (L.b i).isFinite}
    {h_FIN_x : ∀ j, (x j).isFinite} {h_widen : sf.FitsInNormal ff_wide}
    {nctx : NarrowingContext R sf}
    (res : MixedPrecisionLayerFpResult L x h_FIN_W h_FIN_b h_FIN_x h_widen nctx)
    (wMax xMax bMax : R) : R :=
  let η_sf := @FloatFormat.hEps nctx.floatFormat R _
  let τ_sf := (2 : R) ^ ((@FloatFormat.min_exp nctx.floatFormat : ℤ)
    - (@FloatFormat.prec nctx.floatFormat : ℤ))
  -- target magnitude bound = MLP layer's algebraic real-output bound.
  let M := (n_in : R) * wMax * xMax + bMax
  -- wide-format layer error
  let ε_wide := res.wide.errorBound wMax xMax bMax
  η_sf * M + (1 + η_sf) * ε_wide + τ_sf

/-- The mixed-precision FP layer output is close to the real-valued
forward pass, up to `errorBound`. -/
theorem MixedPrecisionLayerFpResult.forward_error_bound
    {sf : StorageFormat} {n_in n_out : ℕ}
    {L : MixedPrecisionLayer sf n_in n_out} {x : Fin n_in → StorageFp sf}
    {h_FIN_W : ∀ i j, (L.W i j).isFinite} {h_FIN_b : ∀ i, (L.b i).isFinite}
    {h_FIN_x : ∀ j, (x j).isFinite} {h_widen : sf.FitsInNormal ff_wide}
    {nctx : NarrowingContext R sf}
    (res : MixedPrecisionLayerFpResult L x h_FIN_W h_FIN_b h_FIN_x h_widen nctx)
    (hsigned : sf.hasSigned = true)
    {wMax bMax : R}
    (hWBound : ∀ i j, |((L.W i j).toVal : R)| ≤ wMax)
    (hBBound : ∀ i, |((L.b i).toVal : R)| ≤ bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R}
    (hxBound : ∀ j, |((x j).toVal : R)| ≤ xMax) (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.result i).toVal : R) - L.forward (fun j => ((x j).toVal : R)) i|
      ≤ res.errorBound wMax xMax bMax := by
  -- Bounded-params for the widened layer (BoundedParams transfers because widening is exact).
  have hL_widen : MLP.BoundedParams (R := R) (L.widen h_FIN_W h_FIN_b h_widen) wMax bMax := by
    refine ⟨?_, ?_⟩
    · intro i j
      simp only [MixedPrecisionLayer.widen]
      rw [StorageFp.toFiniteFpWiden_toVal]
      exact hWBound i j
    · intro i
      simp only [MixedPrecisionLayer.widen]
      rw [StorageFp.toFiniteFpWiden_toVal]
      exact hBBound i
  -- Each widened input has the input bound.
  have hx_widen : ∀ j, Flean.Tags.HasAbsBound (R := R) xMax
      ((x j).toFiniteFpWiden ff_wide h_widen (h_FIN_x j)) := by
    intro j
    refine ⟨?_⟩
    rw [StorageFp.toFiniteFpWiden_toVal]
    exact hxBound j
  -- Wide-format layer error: |wide.result i - widenedLayer.forward (widenedX) i| ≤ wide.errorBound.
  have h_wide_err := res.wide.forward_error_bound (R := R) hL_widen hwMax_nn hx_widen hxMax_nn i
  -- Reshape the wide forward into the storage forward.
  rw [L.forward_widen h_FIN_W h_FIN_b h_widen x h_FIN_x i] at h_wide_err
  -- Now h_wide_err : |wide.result_i.toVal - L.forward x_real i| ≤ wide.errorBound.
  -- Apply mixed_precision_narrowing_error_unified with target = L.forward (x_real) i and
  -- ε_wide = wide.errorBound.
  have h_mixed := mixed_precision_narrowing_error_unified (R := R) ff_wide sf nctx
    .saturate hsigned
    (res.wide.result i) (res.hm i) (res.h_no_ov i) (res.h_no_nan i)
    (res.fp_narrow i) (res.h_round i)
    (L.forward (fun j => ((x j).toVal : R)) i)
    (res.wide.errorBound wMax xMax bMax) h_wide_err
  -- Rewrite result_i to fromFp form using h_result.
  rw [res.h_result i]
  -- Plug into errorBound.
  unfold MixedPrecisionLayerFpResult.errorBound
  -- The bound uses M = n·wMax·xMax + bMax as the target magnitude bound, but
  -- mixed_precision_narrowing_error_unified outputs η·|target| + (1+η)·ε + tail.
  -- We need: η·|target| ≤ η·M, which uses |target| ≤ M = L.outputBoundReal.
  have h_target_bound : |L.forward (fun j => ((x j).toVal : R)) i|
      ≤ (n_in : R) * wMax * xMax + bMax := by
    have := MLP.Layer.forward_abs_le (L.widen h_FIN_W h_FIN_b h_widen) hL_widen hwMax_nn
      (R := R) (x := fun j => ((x j).toFiniteFpWiden ff_wide h_widen (h_FIN_x j)).toVal)
      (xMax := xMax) (fun j => by
        show |((x j).toFiniteFpWiden ff_wide h_widen (h_FIN_x j)).toVal| ≤ xMax
        rw [StorageFp.toFiniteFpWiden_toVal]
        exact hxBound j)
      hxMax_nn i
    rw [L.forward_widen h_FIN_W h_FIN_b h_widen x h_FIN_x i] at this
    unfold MLP.Layer.outputBoundReal at this
    exact this
  -- η_sf is nonneg.
  have hη_sf_nn : (0 : R) ≤ @FloatFormat.hEps nctx.floatFormat R _ := by
    unfold FloatFormat.hEps; positivity
  -- Combine: |result - target| ≤ η_sf·|target| + (1+η_sf)·ε_wide + tail_sf
  --                            ≤ η_sf·M + (1+η_sf)·ε_wide + tail_sf
  calc |((@StorageFp.fromFp ff_wide sf .saturate (@Fp.finite ff_wide (res.wide.result i))).toVal : R)
          - L.forward (fun j => ((x j).toVal : R)) i|
      ≤ _ := h_mixed
    _ ≤ @FloatFormat.hEps nctx.floatFormat R _ * ((n_in : R) * wMax * xMax + bMax)
          + (1 + @FloatFormat.hEps nctx.floatFormat R _) * res.wide.errorBound wMax xMax bMax
          + (2 : R) ^ ((@FloatFormat.min_exp nctx.floatFormat : ℤ)
              - (@FloatFormat.prec nctx.floatFormat : ℤ)) := by
        have h1 : @FloatFormat.hEps nctx.floatFormat R _
            * |L.forward (fun j => ((x j).toVal : R)) i|
              ≤ @FloatFormat.hEps nctx.floatFormat R _ * ((n_in : R) * wMax * xMax + bMax) :=
          mul_le_mul_of_nonneg_left h_target_bound hη_sf_nn
        linarith

/-! ## Vector-form magnitude bound (`HasAbsBoundSVec`)

Lift the per-row error bound to a per-index magnitude bound on the
storage outputs.  Triangle inequality with `Layer.outputBoundReal`:

`|result_i.toVal| ≤ errorBound + (n_in·wMax·xMax + bMax)`.

This integrates with the R6.1 tag-framework so consumers can chain a
`MixedPrecisionLayer` into further mixed-precision computation. -/

theorem MixedPrecisionLayerFpResult.toVal_abs_le
    {sf : StorageFormat} {n_in n_out : ℕ}
    {L : MixedPrecisionLayer sf n_in n_out} {x : Fin n_in → StorageFp sf}
    {h_FIN_W : ∀ i j, (L.W i j).isFinite} {h_FIN_b : ∀ i, (L.b i).isFinite}
    {h_FIN_x : ∀ j, (x j).isFinite} {h_widen : sf.FitsInNormal ff_wide}
    {nctx : NarrowingContext R sf}
    (res : MixedPrecisionLayerFpResult L x h_FIN_W h_FIN_b h_FIN_x h_widen nctx)
    (hsigned : sf.hasSigned = true)
    {wMax bMax : R}
    (hWBound : ∀ i j, |((L.W i j).toVal : R)| ≤ wMax)
    (hBBound : ∀ i, |((L.b i).toVal : R)| ≤ bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R}
    (hxBound : ∀ j, |((x j).toVal : R)| ≤ xMax) (hxMax_nn : 0 ≤ xMax)
    (i : Fin n_out) :
    |((res.result i).toVal : R)| ≤
      res.errorBound wMax xMax bMax + ((n_in : R) * wMax * xMax + bMax) := by
  -- Per-row error bound.
  have h_err := res.forward_error_bound hsigned hWBound hBBound hwMax_nn hxBound hxMax_nn i
  -- Real-valued target magnitude bound.
  have hL_widen : MLP.BoundedParams (R := R) (L.widen h_FIN_W h_FIN_b h_widen) wMax bMax := by
    refine ⟨?_, ?_⟩
    · intro i j
      simp only [MixedPrecisionLayer.widen]
      rw [StorageFp.toFiniteFpWiden_toVal]
      exact hWBound i j
    · intro i
      simp only [MixedPrecisionLayer.widen]
      rw [StorageFp.toFiniteFpWiden_toVal]
      exact hBBound i
  have h_target_bound : |L.forward (fun j => ((x j).toVal : R)) i|
      ≤ (n_in : R) * wMax * xMax + bMax := by
    have := MLP.Layer.forward_abs_le (L.widen h_FIN_W h_FIN_b h_widen) hL_widen hwMax_nn
      (R := R) (x := fun j => ((x j).toFiniteFpWiden ff_wide h_widen (h_FIN_x j)).toVal)
      (xMax := xMax) (fun j => by
        show |((x j).toFiniteFpWiden ff_wide h_widen (h_FIN_x j)).toVal| ≤ xMax
        rw [StorageFp.toFiniteFpWiden_toVal]
        exact hxBound j)
      hxMax_nn i
    rw [L.forward_widen h_FIN_W h_FIN_b h_widen x h_FIN_x i] at this
    unfold MLP.Layer.outputBoundReal at this
    exact this
  -- Triangle.
  have h_tri : |((res.result i).toVal : R)| ≤
      |((res.result i).toVal : R) - L.forward (fun j => ((x j).toVal : R)) i|
        + |L.forward (fun j => ((x j).toVal : R)) i| := by
    have heq : ((res.result i).toVal : R) =
        (((res.result i).toVal : R) - L.forward (fun j => ((x j).toVal : R)) i)
          + L.forward (fun j => ((x j).toVal : R)) i := by ring
    calc |((res.result i).toVal : R)|
        = |(((res.result i).toVal : R) - L.forward (fun j => ((x j).toVal : R)) i)
            + L.forward (fun j => ((x j).toVal : R)) i| := by rw [← heq]
      _ ≤ _ := abs_add_le _ _
  linarith

/-- The vector form of `toVal_abs_le`: per-index magnitude bound on
the storage output, packaged as a `HasAbsBoundSVec`. -/
theorem MixedPrecisionLayerFpResult.hasAbsBoundSVec
    {sf : StorageFormat} {n_in n_out : ℕ}
    {L : MixedPrecisionLayer sf n_in n_out} {x : Fin n_in → StorageFp sf}
    {h_FIN_W : ∀ i j, (L.W i j).isFinite} {h_FIN_b : ∀ i, (L.b i).isFinite}
    {h_FIN_x : ∀ j, (x j).isFinite} {h_widen : sf.FitsInNormal ff_wide}
    {nctx : NarrowingContext R sf}
    (res : MixedPrecisionLayerFpResult L x h_FIN_W h_FIN_b h_FIN_x h_widen nctx)
    (hsigned : sf.hasSigned = true)
    {wMax bMax : R}
    (hWBound : ∀ i j, |((L.W i j).toVal : R)| ≤ wMax)
    (hBBound : ∀ i, |((L.b i).toVal : R)| ≤ bMax)
    (hwMax_nn : 0 ≤ wMax)
    {xMax : R}
    (hxBound : ∀ j, |((x j).toVal : R)| ≤ xMax) (hxMax_nn : 0 ≤ xMax) :
    Flean.Tags.HasAbsBoundSVec (R := R)
      (fun (_ : Fin n_out) =>
        res.errorBound wMax xMax bMax + ((n_in : R) * wMax * xMax + bMax))
      res.result := by
  refine ⟨fun i => ⟨?_⟩⟩
  exact res.toVal_abs_le hsigned hWBound hBBound hwMax_nn hxBound hxMax_nn i

end FpForward

end StorageFp
