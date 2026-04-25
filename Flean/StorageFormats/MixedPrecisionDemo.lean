import Flean.StorageFormats.MixedPrecision
import Flean.StorageFormats.Quantization

/-!
# Mixed-precision demo: E3M2 ↔ Binary32 (concrete instantiation)

End-to-end example exercising the mixed-precision pipeline at concrete
numerical values:

* `narrowingContextE3M2` — the bundled `NarrowingContext ℚ E3M2` produced
  by `NarrowingContext.ofRNE` from an ambient
  `[UseRoundingPolicy RoundNearestEvenPolicy]` instance.

* `mixed_precision_E3M2_error_bound` — the abstract
  `mixed_precision_narrowing_error_unified` theorem specialised to
  `sf = E3M2`, with the symbolic `FloatFormat.hEps` and
  `2^(min_exp - prec)` coefficients evaluated to the concrete
  rationals `1/8` and `1/32`.

This demonstrates that the abstract Phase 4 composition theorem
produces a closed-form numerical bound when applied — and exercises
the `NarrowingContext` API end-to-end against a wider format.

## Why E3M2 and not E4M3?

The narrowing theorem requires
`sf.maxManFieldAtMaxExp ≥ 2^sf.manBits - 1` (no mantissa values are
reserved for NaN at the maximum exponent).  E3M2 (which has no NaN)
satisfies this trivially, while E4M3 (which reserves one mantissa
pattern for NaN) does not.  E5M2 / E2M3 / E2M1 also satisfy it; E4M3
narrowing would need a separate proof path that handles the NaN-
adjusted maximum.
-/

namespace StorageFp

/-! ## E3M2 narrowing context -/

variable [UseRoundingPolicy RoundNearestEvenPolicy]

/-- The `NarrowingContext ℚ E3M2` corresponding to the ambient RNE policy. -/
noncomputable def narrowingContextE3M2 : NarrowingContext ℚ E3M2 :=
  NarrowingContext.ofRNE ℚ E3M2 (by decide) (by decide) (by decide)

/-- The narrow `FloatFormat` carried by `narrowingContextE3M2` is exactly
`FloatFormat.ofE3M2`. -/
theorem narrowingContextE3M2_floatFormat :
    narrowingContextE3M2.floatFormat = FloatFormat.ofE3M2 := rfl

/-! ## Concrete numerical bound

Specialise `mixed_precision_narrowing_error_unified` to `sf = E3M2`,
evaluating the symbolic coefficients to rationals.
-/

/-- Mixed-precision error bound for narrowing into E3M2 (RNE), with the
symbolic coefficients evaluated to the concrete rationals `1/8` and
`1/32`.

Given a wide-format result `fp : FiniteFp ff_wide` that approximates a
real `target` with absolute error `ε_wide`, narrowing to E3M2 yields a
result whose distance to `target` is bounded by
`(1/8)·|target| + (1 + 1/8)·ε_wide + 1/32`.

The coefficients come from
* `1/8 = 2^(-3) = η_E3M2` — half machine epsilon at E3M2's precision,
* `1/32 = 2^(-5) = 2^(min_exp_E3M2 - prec_E3M2)` — the subnormal tail. -/
theorem mixed_precision_E3M2_error_bound
    (ff_wide : FloatFormat)
    (fp : @FiniteFp ff_wide) (hm : fp.m ≠ 0)
    (h_no_ov : (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (E3M2.manBits + 1)
        (1 - (E3M2.bias : ℤ)) ((E3M2.maxExpField : ℤ) - (E3M2.bias : ℤ)) rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp FloatFormat.ofE3M2)
    (h_round_finite :
        @RMode.round ℚ FloatFormat.ofE3M2 _
          (@FiniteFp.toVal ff_wide ℚ _ fp)
          = @Fp.finite FloatFormat.ofE3M2 fp_out)
    (target ε_wide : ℚ)
    (h_wide_err : |@FiniteFp.toVal ff_wide ℚ _ fp - target| ≤ ε_wide) :
    |(@StorageFp.toVal E3M2
          (@StorageFp.fromFp ff_wide E3M2 .saturate (@Fp.finite ff_wide fp)) ℚ _)
        - target|
      ≤ (1 / 8 : ℚ) * |target| + (1 + 1 / 8 : ℚ) * ε_wide + (1 / 32 : ℚ) := by
  -- Apply the abstract theorem with the bundled context.
  have h_abstract :=
    mixed_precision_narrowing_error_unified (R := ℚ)
      ff_wide E3M2 narrowingContextE3M2 .saturate (by decide) (by decide)
      fp hm h_no_ov fp_out h_round_finite target ε_wide h_wide_err
  -- Evaluate the symbolic hEps coefficient: 2^(-prec_E3M2) = 2^(-3) = 1/8.
  have h_hEps : @FloatFormat.hEps narrowingContextE3M2.floatFormat ℚ _ = (1 / 8 : ℚ) := by
    rw [narrowingContextE3M2_floatFormat]
    show (2 : ℚ) ^ (-(3 : ℤ)) = 1 / 8
    norm_num
  -- Evaluate the symbolic subnormal tail: 2^(min_exp - prec) = 2^(-5) = 1/32.
  have h_tail : (2 : ℚ) ^ (@FloatFormat.min_exp narrowingContextE3M2.floatFormat
      - @FloatFormat.prec narrowingContextE3M2.floatFormat) = (1 / 32 : ℚ) := by
    rw [narrowingContextE3M2_floatFormat]
    show (2 : ℚ) ^ ((-2 : ℤ) - (3 : ℤ)) = 1 / 32
    norm_num
  rw [h_hEps, h_tail] at h_abstract
  exact h_abstract

end StorageFp
