import Flean.StorageFormats.FromFp
import Flean.StorageFormats.FromFpCorrect
import Flean.StorageFormats.Conversion
import Flean.StorageFormats.ToFp
import Flean.StorageFormats.NarrowingContext
import Flean.Rounding.RoundPreserves

/-!
# Narrowing error bound: `fromFp : Fp ff_wide → StorageFp sf`

Error bounds for rounding a `FiniteFp` (in a wider arithmetic `FloatFormat`
such as Binary32) down to a `StorageFp sf` (e.g. E4M3).  Complements
`ToFp.lean`: widening is exact, narrowing pays an `η_sf`-relative error.

## The generalized capstone

`fromFp_correct` in `FromFpCorrect.lean` proves `fromFp = RMode.round` only
when the scoped `FloatFormat` matches `sf.toFloatFormat`.  For mixed
precision we want the narrowing theorem when the scoped format is
*strictly wider* than `sf.toFloatFormat` — this file supplies that
variant via `fromFp_widen_val_eq_round`.

All theorems take the narrow-format typeclass setup bundled in a
`StorageFp.NarrowingContext R sf`.  See
`Flean/StorageFormats/NarrowingContext.lean`.
-/

namespace StorageFp

variable {R : Type*}

/-- `η` parameterised by a storage format: `2 ^ (-prec_sf) = 2 ^ (-(manBits + 1))`.
This is half machine epsilon — the RNE bound coefficient — at sf's precision,
equal to `@FloatFormat.hEps (sf.toFloatFormat _ _ _) _`. -/
noncomputable def η_sf (sf : StorageFormat) [Field R] : R :=
  (2 : R) ^ (-((sf.manBits : ℤ) + 1))

/-- `subnormalConst` parameterised by a storage format:
`2 ^ (min_exp_sf - prec_sf) = 2 ^ (1 - bias - (manBits + 1)) = 2 ^ (-bias - manBits)`. -/
noncomputable def subnormalConst_sf (sf : StorageFormat) [Field R] : R :=
  (2 : R) ^ (-(sf.bias : ℤ) - (sf.manBits : ℤ))

end StorageFp

/-!
## The generalized `fromFp_correct` for wider working formats

Both FloatFormats are taken as explicit arguments (not instance binders)
to avoid typeclass-resolution ambiguity when both are in scope.  Inside
the proof, `letI` switches the ambient format as needed for each of the
pre-existing scope-aware lemmas.
-/

namespace StorageFp

theorem fromFp_widen_val_eq_round
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat)
    (sf : StorageFormat) (ctx : NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (h_no_nan : sf.maxManFieldAtMaxExp ≥ 2 ^ sf.manBits - 1)
    (fp : @FiniteFp ff_wide) (hm : fp.m ≠ 0)
    (h_no_ov : (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ)) rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM
          (@FiniteFp.toVal ff_wide R _ fp) = @Fp.finite ctx.floatFormat fp_out) :
    @StorageFp.toVal sf (@StorageFp.fromFp ff_wide sf policy (@Fp.finite ff_wide fp)) R _ =
      @FiniteFp.toVal ctx.floatFormat R _ fp_out := by
  -- Step (a): under ff_wide, `fromFp.toVal = intSigVal fp.s rc.1 rc.2.1`.
  have h_fromFp_val := @fromFp_val_eq_intSigVal ff_wide R _ sf policy fp hsigned
    ctx.h_prec hm h_no_ov h_no_nan
  simp only at h_fromFp_val
  rw [h_fromFp_val]
  -- Step (b): rewrite `roundSigCore`'s target parameters into the
  -- `sf.toFloatFormat` scoped form (`.prec.toNat`, `.min_exp`, `.max_exp`).
  have h_ff_prec_toNat :
      (@FloatFormat.prec ctx.floatFormat).toNat = sf.manBits + 1 := by
    show ((sf.manBits : ℤ) + 1).toNat = sf.manBits + 1
    omega
  have h_rc_eq :
    roundSigCore (@FiniteFp.s ff_wide fp) (@FiniteFp.m ff_wide fp)
        (@FiniteFp.e ff_wide fp - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ)) rneRoundUp =
    roundSigCore (@FiniteFp.s ff_wide fp) (@FiniteFp.m ff_wide fp)
        (@FiniteFp.e ff_wide fp - ff_wide.prec + 1)
        (@FloatFormat.prec ctx.floatFormat).toNat
        (@FloatFormat.min_exp ctx.floatFormat)
        (@FloatFormat.max_exp ctx.floatFormat)
        rneRoundUp := by
    rw [h_ff_prec_toNat]; rfl
  rw [h_rc_eq] at h_no_ov ⊢
  -- Step (c): reshape `h_round_finite` to use `intSigVal` instead of `fp.toVal`.
  have h_fp_toVal :
      @FiniteFp.toVal ff_wide R _ fp =
      intSigVal (R := R) (@FiniteFp.s ff_wide fp) (@FiniteFp.m ff_wide fp)
        (@FiniteFp.e ff_wide fp - ff_wide.prec + 1) :=
    @finiteFp_toVal_eq_intSigVal ff_wide R _ fp
  rw [h_fp_toVal] at h_round_finite
  -- Step (d): apply the core identity under the narrow scope.
  have h_core := @roundIntSigM_val_eq_roundSigCore_val
    ctx.floatFormat R _ ctx.execNarrow _ _ _ ctx.instM ctx.soundNarrow
    (@FiniteFp.s ff_wide fp) (@FiniteFp.m ff_wide fp)
    (@FiniteFp.e ff_wide fp - ff_wide.prec + 1) hm fp_out
    ctx.isRNE h_no_ov h_round_finite
  exact h_core.symm

/-!
## Error bounds

`fromFp_widen_abs_error_normal` bounds the rounding error by `η_sf · |x|`
when the source value sits in sf's normal range.  The unified variant adds
an additive `subnormalConst_sf` tail to cover the subnormal regime.

These reduce to the matching `round_preserves_abs_error_*` kernel lemmas,
invoked under the narrow FloatFormat (`sf.toFloatFormat`) scope.
-/

/-- Rounding-narrowing error bound, normal-range regime.

When `|fp.toVal| ≥ 2^(1 - sf.bias)` (sf's smallest normal magnitude), the
narrowing error is bounded by `η_sf · |fp.toVal|` — a pure relative error,
no subnormal tail. -/
theorem fromFp_widen_abs_error_normal
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat)
    (sf : StorageFormat) (ctx : NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (h_no_nan : sf.maxManFieldAtMaxExp ≥ 2 ^ sf.manBits - 1)
    (fp : @FiniteFp ff_wide) (hm : fp.m ≠ 0)
    (h_no_ov : (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ)) rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM
          (@FiniteFp.toVal ff_wide R _ fp)
          = @Fp.finite ctx.floatFormat fp_out)
    (h_x_normal :
        (2 : R) ^ (1 - (sf.bias : ℤ)) ≤ |@FiniteFp.toVal ff_wide R _ fp|) :
    |@StorageFp.toVal sf (@StorageFp.fromFp ff_wide sf policy (@Fp.finite ff_wide fp)) R _
        - @FiniteFp.toVal ff_wide R _ fp|
      ≤ @FloatFormat.hEps ctx.floatFormat R _
          * |@FiniteFp.toVal ff_wide R _ fp| := by
  have h_eq := fromFp_widen_val_eq_round (R := R) ff_wide sf ctx
    policy hsigned h_no_nan fp hm h_no_ov fp_out h_round_finite
  rw [h_eq]
  exact @round_preserves_abs_error_normal ctx.floatFormat
    R _ _ _ _ ctx.instM ctx.nearestNarrow ctx.conjNarrow
    (@FiniteFp.toVal ff_wide R _ fp) h_x_normal fp_out h_round_finite

/-- Rounding-narrowing error bound, unified regime (no normal-range precondition). -/
theorem fromFp_widen_abs_error_unified
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat)
    (sf : StorageFormat) (ctx : NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (h_no_nan : sf.maxManFieldAtMaxExp ≥ 2 ^ sf.manBits - 1)
    (fp : @FiniteFp ff_wide) (hm : fp.m ≠ 0)
    (h_no_ov : (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ)) rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM
          (@FiniteFp.toVal ff_wide R _ fp)
          = @Fp.finite ctx.floatFormat fp_out) :
    |@StorageFp.toVal sf (@StorageFp.fromFp ff_wide sf policy (@Fp.finite ff_wide fp)) R _
        - @FiniteFp.toVal ff_wide R _ fp|
      ≤ @FloatFormat.hEps ctx.floatFormat R _
          * |@FiniteFp.toVal ff_wide R _ fp|
        + (2 : R) ^ (@FloatFormat.min_exp ctx.floatFormat
            - @FloatFormat.prec ctx.floatFormat) := by
  have h_eq := fromFp_widen_val_eq_round (R := R) ff_wide sf ctx
    policy hsigned h_no_nan fp hm h_no_ov fp_out h_round_finite
  rw [h_eq]
  exact @round_preserves_abs_error_unified ctx.floatFormat
    R _ _ _ _ ctx.instM ctx.nearestNarrow ctx.conjNarrow ctx.zeroNarrow
    (@FiniteFp.toVal ff_wide R _ fp) fp_out h_round_finite

end StorageFp
