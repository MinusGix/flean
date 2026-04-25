import Flean.StorageFormats.MixedPrecision
import Flean.StorageFormats.Quantization

/-!
# Mixed-precision demos: E3M2 / E4M3 ↔ Binary32 (concrete instantiations)

End-to-end examples exercising the mixed-precision pipeline at concrete
numerical values:

* `narrowingContextE3M2` / `narrowingContextE4M3` — bundled
  `NarrowingContext ℚ sf` instances from `NarrowingContext.ofRNE`
  given an ambient `[UseRoundingPolicy RoundNearestEvenPolicy]`.

* `mixed_precision_E3M2_error_bound` /
  `mixed_precision_E4M3_error_bound` — the abstract
  `mixed_precision_narrowing_error_unified` specialised to each
  storage format, with the symbolic `FloatFormat.hEps` and
  `2^(min_exp - prec)` coefficients evaluated to concrete rationals.

This demonstrates that the abstract Phase 4 composition theorem
produces closed-form numerical bounds when applied — and exercises
the `NarrowingContext` + `avoidsNanReservedEncoding` API end-to-end.

## E3M2 vs E4M3 narrowing

The narrowing theorem now takes `avoidsNanReservedEncoding sf m e_ulp`
in place of the old format-wide `h_no_nan` hypothesis.

- **E3M2** (no NaN reserved at maxExp): the disjunction's left branch
  `Or.inl (by decide)` discharges `sf.maxManFieldAtMaxExp ≥ 2^manBits - 1`.
- **E4M3** (one NaN-reserved mantissa pattern at maxExp): the
  format-wide condition fails, so callers supply a per-result witness
  `Or.inr h_per_result` that the rounded `(m_final, e_ulp_final)`
  doesn't land on the reserved pattern.  Practically derivable from a
  magnitude bound on the wide-format input that avoids E4M3 saturation.
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
      ff_wide E3M2 narrowingContextE3M2 .saturate (by decide)
      fp hm h_no_ov (Or.inl (by decide)) fp_out h_round_finite target ε_wide h_wide_err
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

/-! ## E4M3 narrowing context -/

/-- The `NarrowingContext ℚ E4M3` corresponding to the ambient RNE policy.

E4M3's bundle structure is identical to E3M2's — the `NarrowingContext`
machinery is unaware of the NaN-reserved-pattern issue, which surfaces
only at the bound theorem.  -/
noncomputable def narrowingContextE4M3 : NarrowingContext ℚ E4M3 :=
  NarrowingContext.ofRNE ℚ E4M3 (by decide) (by decide) (by decide)

/-- The narrow `FloatFormat` carried by `narrowingContextE4M3` is exactly
`FloatFormat.ofE4M3`. -/
theorem narrowingContextE4M3_floatFormat :
    narrowingContextE4M3.floatFormat = FloatFormat.ofE4M3 := rfl

/-! ## E4M3 concrete numerical bound

Specialise `mixed_precision_narrowing_error_unified` to `sf = E4M3`,
evaluating the symbolic coefficients to rationals: `η_E4M3 = 1/16` and
`subnormalConst_E4M3 = 1/1024`.

The user supplies the per-result `avoidsNanReservedEncoding` witness
ruling out E4M3's NaN-reserved mantissa pattern at maxExp (`m=15, e=8`,
i.e., the would-be encoding of `480 = 1.111 · 2^8`).
-/

/-- Mixed-precision error bound for narrowing into E4M3 (RNE), with the
symbolic coefficients evaluated to the concrete rationals `1/16` and
`1/1024`.

Given a wide-format result `fp : FiniteFp ff_wide` that approximates a
real `target` with absolute error `ε_wide`, narrowing to E4M3 yields a
result whose distance to `target` is bounded by
`(1/16)·|target| + (1 + 1/16)·ε_wide + 1/1024`,
**provided** the rounded result avoids E4M3's NaN-reserved mantissa
pattern.

The coefficients come from
* `1/16 = 2^(-4) = η_E4M3` — half machine epsilon at E4M3's precision,
* `1/1024 = 2^(-10) = 2^(min_exp_E4M3 - prec_E4M3)` — the subnormal
  tail.

The `h_no_nan_pat` hypothesis takes the form
`¬ (rounded exp_field = E4M3.maxExpField ∧ rounded man_field > 6)`.
It rules out the case where rounding would land on `(m_final = 15,
e_ulp_final = 5)`, which `fromFp` would saturate to `448` rather than
emit the NaN pattern. -/
theorem mixed_precision_E4M3_error_bound
    (ff_wide : FloatFormat)
    (fp : @FiniteFp ff_wide) (hm : fp.m ≠ 0)
    (h_no_ov : (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (E4M3.manBits + 1)
        (1 - (E4M3.bias : ℤ)) ((E4M3.maxExpField : ℤ) - (E4M3.bias : ℤ)) rneRoundUp).2.2 = false)
    (h_no_nan_pat :
      ¬ (((roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (E4M3.manBits + 1)
              (1 - (E4M3.bias : ℤ)) ((E4M3.maxExpField : ℤ) - (E4M3.bias : ℤ)) rneRoundUp).2.1
              + (E4M3.manBits : ℤ) + (E4M3.bias : ℤ)).toNat = E4M3.maxExpField
            ∧ (roundSigCore fp.s fp.m (fp.e - ff_wide.prec + 1) (E4M3.manBits + 1)
                (1 - (E4M3.bias : ℤ)) ((E4M3.maxExpField : ℤ) - (E4M3.bias : ℤ)) rneRoundUp).1
                - 2 ^ E4M3.manBits > E4M3.maxManFieldAtMaxExp))
    (fp_out : @FiniteFp FloatFormat.ofE4M3)
    (h_round_finite :
        @RMode.round ℚ FloatFormat.ofE4M3 _
          (@FiniteFp.toVal ff_wide ℚ _ fp)
          = @Fp.finite FloatFormat.ofE4M3 fp_out)
    (target ε_wide : ℚ)
    (h_wide_err : |@FiniteFp.toVal ff_wide ℚ _ fp - target| ≤ ε_wide) :
    |(@StorageFp.toVal E4M3
          (@StorageFp.fromFp ff_wide E4M3 .saturate (@Fp.finite ff_wide fp)) ℚ _)
        - target|
      ≤ (1 / 16 : ℚ) * |target| + (1 + 1 / 16 : ℚ) * ε_wide + (1 / 1024 : ℚ) := by
  have h_abstract :=
    mixed_precision_narrowing_error_unified (R := ℚ)
      ff_wide E4M3 narrowingContextE4M3 .saturate (by decide)
      fp hm h_no_ov (Or.inr h_no_nan_pat) fp_out h_round_finite target ε_wide h_wide_err
  -- Evaluate η_E4M3: 2^(-prec_E4M3) = 2^(-4) = 1/16.
  have h_hEps : @FloatFormat.hEps narrowingContextE4M3.floatFormat ℚ _ = (1 / 16 : ℚ) := by
    rw [narrowingContextE4M3_floatFormat]
    show (2 : ℚ) ^ (-(4 : ℤ)) = 1 / 16
    norm_num
  -- Evaluate the subnormal tail: 2^(min_exp - prec) = 2^(-6 - 4) = 1/1024.
  have h_tail : (2 : ℚ) ^ (@FloatFormat.min_exp narrowingContextE4M3.floatFormat
      - @FloatFormat.prec narrowingContextE4M3.floatFormat) = (1 / 1024 : ℚ) := by
    rw [narrowingContextE4M3_floatFormat]
    show (2 : ℚ) ^ ((-6 : ℤ) - (4 : ℤ)) = 1 / 1024
    norm_num
  rw [h_hEps, h_tail] at h_abstract
  exact h_abstract

end StorageFp
