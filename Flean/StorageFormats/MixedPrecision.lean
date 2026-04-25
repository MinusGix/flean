import Flean.StorageFormats.FromFpBound
import Flean.StorageFormats.ToFp

/-!
# Mixed-precision composition

Compose:
1. A wider-format computation that approximates a real target with error ε_wide,
2. With the sf-narrowing rounding, which adds error ≤ η_sf · |.| + subnormalConst_sf,

into a single end-to-end error bound for "compute-in-wide, store-in-narrow".

Pattern: `StorageFp sf → widen → FiniteFp ff_wide → [op] → FiniteFp ff_wide → narrow → StorageFp sf`.

The widening step (`ToFp.lean`) is exact, so it contributes no error.  The
op in ff_wide contributes whatever error its bound specifies.  The final
narrow (`FromFpBound.lean`) adds the η_sf tail.  This file supplies the
triangle-inequality glue.
-/

/-! ### Triangle-inequality composition -/

section TriangleCompose

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Triangle-style error composition (pure real-valued form).

If `|a − b| ≤ ε₁ · |b| + δ₁` (narrowing error of `a` vs intermediate `b`)
and `|b − c| ≤ ε₂` (wide-format error of `b` vs target `c`), with both
bounds nonneg, then
`|a − c| ≤ ε₁ · |c| + (1 + ε₁) · ε₂ + δ₁`.

This is the composition primitive for mixed-precision: `c` is the real
target, `b` is the wide-format computation result, `a` is the narrowed
storage result. -/
theorem narrow_wide_error_triangle
    (a b c : R) (ε₁ δ₁ : R) (ε₂ : R)
    (hε₁_nn : 0 ≤ ε₁)
    (h_narrow : |a - b| ≤ ε₁ * |b| + δ₁)
    (h_wide : |b - c| ≤ ε₂) :
    |a - c| ≤ ε₁ * |c| + (1 + ε₁) * ε₂ + δ₁ := by
  have h_tri : |a - c| ≤ |a - b| + |b - c| := by
    have : a - c = (a - b) + (b - c) := by ring
    rw [this]; exact abs_add_le _ _
  have h_b_bound : |b| ≤ |c| + ε₂ := by
    have : b = (b - c) + c := by ring
    calc |b| = |(b - c) + c| := by rw [← this]
      _ ≤ |b - c| + |c| := abs_add_le _ _
      _ ≤ ε₂ + |c| := by linarith
      _ = |c| + ε₂ := by ring
  have h_mul : ε₁ * |b| ≤ ε₁ * (|c| + ε₂) := mul_le_mul_of_nonneg_left h_b_bound hε₁_nn
  calc |a - c|
      ≤ |a - b| + |b - c| := h_tri
    _ ≤ (ε₁ * |b| + δ₁) + ε₂ := by linarith
    _ ≤ (ε₁ * (|c| + ε₂) + δ₁) + ε₂ := by linarith
    _ = ε₁ * |c| + (1 + ε₁) * ε₂ + δ₁ := by ring

end TriangleCompose

/-! ### Mixed-precision bound: compute-in-wide → narrow-to-sf

Given an `fp : FiniteFp ff_wide` that approximates a real target `target`
with error ε_wide, narrowing it via `fromFp` to `StorageFp sf` yields a
result that approximates `target` with bounded total error.
-/

namespace StorageFp

theorem mixed_precision_narrowing_error_unified
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat)
    (sf : StorageFormat) (ctx : NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (fp : @FiniteFp ff_wide) (hm : fp.m ≠ 0)
    (h_no_ov : (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ)) rneRoundUp).2.2 = false)
    (h_no_nan : avoidsNanReservedEncoding sf
        (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (sf.manBits + 1)
          (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ)) rneRoundUp).1
        (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (sf.manBits + 1)
          (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ)) rneRoundUp).2.1)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM
          (@FiniteFp.toVal ff_wide R _ fp)
          = @Fp.finite ctx.floatFormat fp_out)
    -- Wide-format error: `fp` approximates `target` with absolute error `ε_wide`.
    (target : R) (ε_wide : R)
    (h_wide_err : |@FiniteFp.toVal ff_wide R _ fp - target| ≤ ε_wide) :
    |@StorageFp.toVal sf (@StorageFp.fromFp ff_wide sf policy (@Fp.finite ff_wide fp)) R _
        - target|
      ≤ @FloatFormat.hEps ctx.floatFormat R _ * |target|
        + (1 + @FloatFormat.hEps ctx.floatFormat R _) * ε_wide
        + (2 : R) ^ (@FloatFormat.min_exp ctx.floatFormat
            - @FloatFormat.prec ctx.floatFormat) := by
  have h_narrow := fromFp_widen_abs_error_unified (R := R) ff_wide sf ctx
    policy hsigned fp hm h_no_ov h_no_nan fp_out h_round_finite
  have hEps_nn : (0 : R) ≤ @FloatFormat.hEps ctx.floatFormat R _ := by
    unfold FloatFormat.hEps
    positivity
  exact narrow_wide_error_triangle _ _ _ _ _ _ hEps_nn h_narrow h_wide_err

end StorageFp
