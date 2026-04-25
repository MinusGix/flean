import Flean.StorageFormats.WideContext
import Flean.StorageFormats.MixedPrecision
import Flean.StorageFormats.ToFp
import Flean.Operations.Mul
import Flean.Operations.Add
import Flean.Operations.FpFiniteRound

/-!
# Concrete mixed-precision FP primitives

`StorageFp.mixedFpMul` and `StorageFp.mixedFpAdd`: storage → widen →
wide-format op → narrow → storage, packaged as single functions with
end-to-end error bounds.

## Pipeline

```
a, b : StorageFp sf
  │   widen (exact, FitsInNormal)
  ▼
a_wide, b_wide : FiniteFp ff_wide
  │   fpMul / fpAdd in ff_wide (wide-format error: η_wide·|·| + tail_wide)
  ▼
prod_wide / sum_wide : Fp ff_wide
  │   StorageFp.fromFp (narrow error: η_sf·|·| + tail_sf)
  ▼
result : StorageFp sf
```

The error bound composes the two rounding errors via the
`narrow_wide_error_triangle` lemma in `MixedPrecision.lean`:

```
|result.toVal - exact| ≤ η_sf·|exact| + (1+η_sf)·ε_wide + tail_sf
```

where `ε_wide = η_wide·|exact| + tail_wide` (RNE bound on the
wide-format op's rounding).

## Hypotheses

The bound theorems take "wide-op produced finite", "narrow round
produced finite", and "no overflow during narrowing" as explicit
hypotheses.  Callers discharge these from format-specific reasoning
about the input range.
-/

set_option autoImplicit false

namespace StorageFp

/-! ## Mixed-precision multiplication -/

/-- Mixed-precision multiplication: widen inputs to `ff_wide`, multiply
there, then narrow back to `sf`. -/
noncomputable def mixedFpMul (ff_wide : FloatFormat) (exec_wide : @RModeExec ff_wide)
    {sf : StorageFormat} (h_FIN : sf.FitsInNormal ff_wide)
    (policy : StorageOverflowPolicy)
    (a b : StorageFp sf) (ha : a.isFinite) (hb : b.isFinite) :
    StorageFp sf :=
  @StorageFp.fromFp ff_wide sf policy
    (@fpMulFinite ff_wide exec_wide
      (a.toFiniteFpWiden ff_wide h_FIN ha)
      (b.toFiniteFpWiden ff_wide h_FIN hb))

/-- End-to-end error bound for `mixedFpMul`.

Given:
- a `WideContext` for the wide format and a `NarrowingContext` for the
  storage format,
- finiteness of the wide-format multiplication and the narrow round,
- the no-overflow witness for the narrow round,

the result satisfies
```
|mixedFpMul a b - a.toVal · b.toVal|
  ≤ η_sf · |a.toVal · b.toVal|
    + (1 + η_sf) · (η_wide · |a.toVal · b.toVal| + tail_wide)
    + tail_sf
```

where `η_*` and `tail_*` are the half-machine-epsilon and the
subnormal-tail constants for the respective formats. -/
theorem mixedFpMul_error_bound
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat) (wctx : WideContext R ff_wide)
    {sf : StorageFormat} (h_FIN : sf.FitsInNormal ff_wide)
    (nctx : NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (a b : StorageFp sf) (ha : a.isFinite) (hb : b.isFinite)
    (prod_wide : @FiniteFp ff_wide)
    (h_prod_finite : @fpMulFinite ff_wide wctx.execWide
        (a.toFiniteFpWiden ff_wide h_FIN ha) (b.toFiniteFpWiden ff_wide h_FIN hb)
        = @Fp.finite ff_wide prod_wide)
    (hm : prod_wide.m ≠ 0)
    (h_no_ov : (StorageFp.roundSigCore prod_wide.s prod_wide.m
        (prod_wide.e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).2.2 = false)
    (h_no_nan : avoidsNanReservedEncoding sf
        (StorageFp.roundSigCore prod_wide.s prod_wide.m
          (prod_wide.e - ff_wide.prec + 1) (sf.manBits + 1)
          (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
          StorageFp.rneRoundUp).1
        (StorageFp.roundSigCore prod_wide.s prod_wide.m
          (prod_wide.e - ff_wide.prec + 1) (sf.manBits + 1)
          (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
          StorageFp.rneRoundUp).2.1)
    (fp_out : @FiniteFp nctx.floatFormat)
    (h_round_finite :
        @RMode.round R nctx.floatFormat nctx.instM
          (@FiniteFp.toVal ff_wide R _ prod_wide)
          = @Fp.finite nctx.floatFormat fp_out) :
    |((mixedFpMul ff_wide wctx.execWide h_FIN policy a b ha hb).toVal : R)
        - (a.toVal : R) * (b.toVal : R)|
      ≤ @FloatFormat.hEps nctx.floatFormat R _
          * |((a.toVal : R) * (b.toVal : R))|
        + (1 + @FloatFormat.hEps nctx.floatFormat R _) *
            (@FloatFormat.hEps ff_wide R _ * |((a.toVal : R) * (b.toVal : R))|
              + (2 : R) ^ ((@FloatFormat.min_exp ff_wide : ℤ)
                  - (@FloatFormat.prec ff_wide : ℤ)))
        + (2 : R) ^ ((@FloatFormat.min_exp nctx.floatFormat : ℤ)
            - (@FloatFormat.prec nctx.floatFormat : ℤ)) := by
  -- Make wide-format typeclasses ambient for the wide-side rounding lemmas.
  letI : FloatFormat := ff_wide
  letI : @RMode R ff_wide := wctx.instM
  letI : @RModeExec ff_wide := wctx.execWide
  letI : @RoundIntSigMSound R _ _ _ _ ff_wide _ _ := wctx.soundWide
  letI : @RModeNearest R ff_wide _ _ _ _ _ := wctx.nearestWide
  letI : @RModeConj R ff_wide _ _ _ := wctx.conjWide
  letI : @RModeZero R ff_wide _ _ := wctx.zeroWide
  -- Step 1: wide-format mul error.  fpMulFinite_round_witness gives a `g` whose
  -- toVal equals `prod_wide.toVal` and which is `RMode.round (a_wide.toVal * b_wide.toVal)`.
  obtain ⟨g, hg_round, hg_eq⟩ :=
    fpMulFinite_round_witness (R := R) (a.toFiniteFpWiden ff_wide h_FIN ha)
      (b.toFiniteFpWiden ff_wide h_FIN hb) h_prod_finite
  -- Apply round_preserves_abs_error_unified to get the wide-format error bound.
  have h_wide_err :
      |(g.toVal : R) - (a.toFiniteFpWiden ff_wide h_FIN ha).toVal
          * (b.toFiniteFpWiden ff_wide h_FIN hb).toVal|
        ≤ (FloatFormat.hEps R : R) * |(a.toFiniteFpWiden ff_wide h_FIN ha).toVal
              * (b.toFiniteFpWiden ff_wide h_FIN hb).toVal|
          + (2 : R) ^ ((FloatFormat.min_exp : ℤ) - (FloatFormat.prec : ℤ)) :=
    round_preserves_abs_error_unified (R := R)
      ((a.toFiniteFpWiden ff_wide h_FIN ha).toVal * (b.toFiniteFpWiden ff_wide h_FIN hb).toVal)
      hg_round
  -- Rewrite g.toVal = prod_wide.toVal and a_wide.toVal = a.toVal etc.
  rw [hg_eq] at h_wide_err
  rw [StorageFp.toFiniteFpWiden_toVal, StorageFp.toFiniteFpWiden_toVal] at h_wide_err
  -- Step 2: invoke the triangle composition with target = a.toVal * b.toVal.
  have h_mixed := mixed_precision_narrowing_error_unified (R := R) ff_wide sf nctx
    policy hsigned prod_wide hm h_no_ov h_no_nan fp_out h_round_finite
    ((a.toVal : R) * b.toVal) _ h_wide_err
  -- mixedFpMul reduces by definition to fromFp ∘ fpMulFinite ∘ widen×widen.
  -- Use h_prod_finite to rewrite the argument.
  have h_unfold : (mixedFpMul ff_wide wctx.execWide h_FIN policy a b ha hb).toVal (R := R)
      = (@StorageFp.fromFp ff_wide sf policy (@Fp.finite ff_wide prod_wide)).toVal := by
    unfold mixedFpMul
    rw [show (@fpMulFinite ff_wide wctx.execWide
        (a.toFiniteFpWiden ff_wide h_FIN ha) (b.toFiniteFpWiden ff_wide h_FIN hb))
        = @Fp.finite ff_wide prod_wide from h_prod_finite]
  rw [h_unfold]
  exact h_mixed

/-! ## Mixed-precision addition -/

/-- Mixed-precision addition: widen inputs to `ff_wide`, add there, then
narrow back to `sf`. -/
noncomputable def mixedFpAdd (ff_wide : FloatFormat) (exec_wide : @RModeExec ff_wide)
    {sf : StorageFormat} (h_FIN : sf.FitsInNormal ff_wide)
    (policy : StorageOverflowPolicy)
    (a b : StorageFp sf) (ha : a.isFinite) (hb : b.isFinite) :
    StorageFp sf :=
  @StorageFp.fromFp ff_wide sf policy
    (@fpAddFinite ff_wide exec_wide
      (a.toFiniteFpWiden ff_wide h_FIN ha)
      (b.toFiniteFpWiden ff_wide h_FIN hb))

/-- End-to-end error bound for `mixedFpAdd`.  Same composition pattern
as `mixedFpMul`, but the exact target is `a.toVal + b.toVal`. -/
theorem mixedFpAdd_error_bound
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat) (wctx : WideContext R ff_wide)
    {sf : StorageFormat} (h_FIN : sf.FitsInNormal ff_wide)
    (nctx : NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (a b : StorageFp sf) (ha : a.isFinite) (hb : b.isFinite)
    (sum_wide : @FiniteFp ff_wide)
    (h_sum_finite : @fpAddFinite ff_wide wctx.execWide
        (a.toFiniteFpWiden ff_wide h_FIN ha) (b.toFiniteFpWiden ff_wide h_FIN hb)
        = @Fp.finite ff_wide sum_wide)
    (hm : sum_wide.m ≠ 0)
    (h_no_ov : (StorageFp.roundSigCore sum_wide.s sum_wide.m
        (sum_wide.e - ff_wide.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).2.2 = false)
    (h_no_nan : avoidsNanReservedEncoding sf
        (StorageFp.roundSigCore sum_wide.s sum_wide.m
          (sum_wide.e - ff_wide.prec + 1) (sf.manBits + 1)
          (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
          StorageFp.rneRoundUp).1
        (StorageFp.roundSigCore sum_wide.s sum_wide.m
          (sum_wide.e - ff_wide.prec + 1) (sf.manBits + 1)
          (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
          StorageFp.rneRoundUp).2.1)
    (fp_out : @FiniteFp nctx.floatFormat)
    (h_round_finite :
        @RMode.round R nctx.floatFormat nctx.instM
          (@FiniteFp.toVal ff_wide R _ sum_wide)
          = @Fp.finite nctx.floatFormat fp_out) :
    |((mixedFpAdd ff_wide wctx.execWide h_FIN policy a b ha hb).toVal : R)
        - ((a.toVal : R) + (b.toVal : R))|
      ≤ @FloatFormat.hEps nctx.floatFormat R _
          * |((a.toVal : R) + (b.toVal : R))|
        + (1 + @FloatFormat.hEps nctx.floatFormat R _) *
            (@FloatFormat.hEps ff_wide R _ * |((a.toVal : R) + (b.toVal : R))|
              + (2 : R) ^ ((@FloatFormat.min_exp ff_wide : ℤ)
                  - (@FloatFormat.prec ff_wide : ℤ)))
        + (2 : R) ^ ((@FloatFormat.min_exp nctx.floatFormat : ℤ)
            - (@FloatFormat.prec nctx.floatFormat : ℤ)) := by
  letI : FloatFormat := ff_wide
  letI : @RMode R ff_wide := wctx.instM
  letI : @RModeExec ff_wide := wctx.execWide
  letI : @RoundIntSigMSound R _ _ _ _ ff_wide _ _ := wctx.soundWide
  letI : @RModeNearest R ff_wide _ _ _ _ _ := wctx.nearestWide
  letI : @RModeConj R ff_wide _ _ _ := wctx.conjWide
  letI : @RModeZero R ff_wide _ _ := wctx.zeroWide
  obtain ⟨g, hg_round, hg_eq⟩ :=
    fpAddFinite_round_witness (R := R) (a.toFiniteFpWiden ff_wide h_FIN ha)
      (b.toFiniteFpWiden ff_wide h_FIN hb) h_sum_finite
  have h_wide_err :
      |(g.toVal : R) - ((a.toFiniteFpWiden ff_wide h_FIN ha).toVal
          + (b.toFiniteFpWiden ff_wide h_FIN hb).toVal)|
        ≤ (FloatFormat.hEps R : R) * |((a.toFiniteFpWiden ff_wide h_FIN ha).toVal
              + (b.toFiniteFpWiden ff_wide h_FIN hb).toVal)|
          + (2 : R) ^ ((FloatFormat.min_exp : ℤ) - (FloatFormat.prec : ℤ)) :=
    round_preserves_abs_error_unified (R := R)
      ((a.toFiniteFpWiden ff_wide h_FIN ha).toVal + (b.toFiniteFpWiden ff_wide h_FIN hb).toVal)
      hg_round
  rw [hg_eq] at h_wide_err
  rw [StorageFp.toFiniteFpWiden_toVal, StorageFp.toFiniteFpWiden_toVal] at h_wide_err
  have h_mixed := mixed_precision_narrowing_error_unified (R := R) ff_wide sf nctx
    policy hsigned sum_wide hm h_no_ov h_no_nan fp_out h_round_finite
    ((a.toVal : R) + b.toVal) _ h_wide_err
  have h_unfold : (mixedFpAdd ff_wide wctx.execWide h_FIN policy a b ha hb).toVal (R := R)
      = (@StorageFp.fromFp ff_wide sf policy (@Fp.finite ff_wide sum_wide)).toVal := by
    unfold mixedFpAdd
    rw [show (@fpAddFinite ff_wide wctx.execWide
        (a.toFiniteFpWiden ff_wide h_FIN ha) (b.toFiniteFpWiden ff_wide h_FIN hb))
        = @Fp.finite ff_wide sum_wide from h_sum_finite]
  rw [h_unfold]
  exact h_mixed

end StorageFp
