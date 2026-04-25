import Flean.Tags.AbsBound
import Flean.Tags.BoundedRange
import Flean.Tags.BundleAbsBound
import Flean.Tags.FpInterval
import Flean.StorageFormats.NarrowingContext
import Flean.StorageFormats.FromFpBound
import Flean.StorageFormats.ToFp

/-!
# Tag-framework bridges for `StorageFp`

Connects `Flean/Tags/HasAbsBound` and `IsBoundedRange` (defined on
`FiniteFp`) to the storage-format pipeline: widen → wide-format ops →
narrow.

## Storage-side tags

- `Flean.Tags.HasAbsBoundS R c sx` — `|(sx.toVal : R)| ≤ c`.
- `Flean.Tags.HasAbsBoundSVec R c sxs` — pointwise vector form.
- `Flean.Tags.IsBoundedRangeS R I sxs` — interval bound on a vector.

These mirror the existing `HasAbsBound` / `HasAbsBoundVec` /
`IsBoundedRange` tags but operate on `StorageFp sf` (no ambient
FloatFormat needed — `StorageFp.toVal` is FloatFormat-agnostic).

## Bridges shipped

- Widening (storage → widened FiniteFp): `HasAbsBoundS.toFiniteFpWiden`,
  `HasAbsBoundSVec.toFiniteFpWiden`, `IsBoundedRangeS.toFiniteFpWiden`.
  Trivial because widening is exact.
- Narrowing (FiniteFp → narrowed storage): `HasAbsBound.fromFp_narrow_unified`
  and `..._normal`, packaging `(1 + η_sf)·c [+ subnormalConst_sf]`.

The wide format is taken as `[FloatFormat]` instance binding (since
each bridge handles one wide format at a time); the narrow format
arrives via the `StorageFp.NarrowingContext R sf` bundle from
`Flean/StorageFormats/NarrowingContext.lean`.

Together these enable end-to-end magnitude reasoning across a
mixed-precision pipeline using the existing tag-framework infrastructure
in the wide-format middle.
-/

set_option autoImplicit false

namespace Flean.Tags

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Storage-side tags -/

variable {sf : StorageFormat}

/-- `HasAbsBoundS R c sx` asserts `|(sx.toVal : R)| ≤ c`.  Storage-format
analog of `HasAbsBound`. -/
structure HasAbsBoundS (c : R) (sx : StorageFp sf) : Prop where
  /-- `|sx.toVal| ≤ c`. -/
  toVal_abs_le : |((sx.toVal : R))| ≤ c

/-- Vector form: per-index magnitude bounds on a storage vector. -/
structure HasAbsBoundSVec {n : ℕ} (c : Fin n → R) (sxs : Fin n → StorageFp sf) : Prop where
  /-- Pointwise bound. -/
  pointwise : ∀ i, HasAbsBoundS (R := R) (c i) (sxs i)

/-- `IsBoundedRangeS R I sxs` asserts each entry of
`sxs : Fin n → StorageFp sf` lies in `I : FpInterval R`. -/
structure IsBoundedRangeS {n : ℕ} (I : FpInterval R) (sxs : Fin n → StorageFp sf) : Prop where
  /-- Pointwise lower bound. -/
  lower : ∀ i, I.lo ≤ ((sxs i).toVal : R)
  /-- Pointwise upper bound. -/
  upper : ∀ i, ((sxs i).toVal : R) ≤ I.hi

/-! ## Properties -/

omit [IsStrictOrderedRing R] in
theorem HasAbsBoundS.weaken {c c' : R} {sx : StorageFp sf}
    (h : HasAbsBoundS (R := R) c sx) (hcc : c ≤ c') :
    HasAbsBoundS (R := R) c' sx :=
  ⟨le_trans h.toVal_abs_le hcc⟩

theorem HasAbsBoundS.c_nonneg {c : R} {sx : StorageFp sf}
    (h : HasAbsBoundS (R := R) c sx) : (0 : R) ≤ c :=
  le_trans (abs_nonneg _) h.toVal_abs_le

omit [IsStrictOrderedRing R] in
theorem IsBoundedRangeS.lo_le_hi {n : ℕ} (hn : 0 < n) {I : FpInterval R}
    {sxs : Fin n → StorageFp sf} (h : IsBoundedRangeS (R := R) I sxs) :
    I.lo ≤ I.hi :=
  le_trans (h.lower ⟨0, hn⟩) (h.upper ⟨0, hn⟩)

theorem IsBoundedRangeS.toVal_abs_le {n : ℕ} {I : FpInterval R}
    {sxs : Fin n → StorageFp sf} (h : IsBoundedRangeS (R := R) I sxs) (i : Fin n) :
    |((sxs i).toVal : R)| ≤ I.maxMag := by
  rcases le_or_gt 0 ((sxs i).toVal : R) with hi_nn | hi_neg
  · have habs : |((sxs i).toVal : R)| = (sxs i).toVal := abs_of_nonneg hi_nn
    rw [habs, FpInterval.maxMag]
    exact le_trans (le_trans (h.upper i) (le_abs_self _)) (le_max_right _ _)
  · have habs : |((sxs i).toVal : R)| = -((sxs i).toVal : R) := abs_of_neg hi_neg
    rw [habs, FpInterval.maxMag]
    have h1 : -((sxs i).toVal : R) ≤ -I.lo := neg_le_neg (h.lower i)
    exact le_trans (le_trans h1 (neg_le_abs _)) (le_max_left _ _)

/-! ## Bridge: storage → widened-FiniteFp

Widening is exact (`toFiniteFpWiden_toVal`), so any tag stating a
`.toVal`-magnitude property carries across unchanged.
-/

section WidenBridges

variable [ff_wide : FloatFormat]

theorem HasAbsBoundS.toFiniteFpWiden
    (h_FIN : sf.FitsInNormal ff_wide)
    (sx : StorageFp sf) (hfin : sx.isFinite)
    {c : R} (h : HasAbsBoundS (R := R) c sx) :
    HasAbsBound (R := R) c (sx.toFiniteFpWiden ff_wide h_FIN hfin) := by
  refine ⟨?_⟩
  rw [StorageFp.toFiniteFpWiden_toVal]
  exact h.toVal_abs_le

theorem HasAbsBoundSVec.toFiniteFpWiden
    (h_FIN : sf.FitsInNormal ff_wide)
    {n : ℕ} (sxs : Fin n → StorageFp sf) (hfin : ∀ i, (sxs i).isFinite)
    {c : Fin n → R} (h : HasAbsBoundSVec (R := R) c sxs) :
    HasAbsBoundVec (R := R) c
      (fun i => (sxs i).toFiniteFpWiden ff_wide h_FIN (hfin i)) := by
  refine ⟨fun i => ?_⟩
  exact (h.pointwise i).toFiniteFpWiden h_FIN (sxs i) (hfin i)

theorem IsBoundedRangeS.toFiniteFpWiden
    (h_FIN : sf.FitsInNormal ff_wide)
    {n : ℕ} (sxs : Fin n → StorageFp sf) (hfin : ∀ i, (sxs i).isFinite)
    {I : FpInterval R} (h : IsBoundedRangeS (R := R) I sxs) :
    IsBoundedRange (R := R) I
      (fun i => (sxs i).toFiniteFpWiden ff_wide h_FIN (hfin i)) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [StorageFp.toFiniteFpWiden_toVal]
    exact h.lower i
  · rw [StorageFp.toFiniteFpWiden_toVal]
    exact h.upper i

end WidenBridges

/-! ## Bridge: widened-FiniteFp → narrowed-storage

Triangle inequality on the narrowing-error bound: from a `HasAbsBound c`
on the wide-format value `fp`, we get a magnitude bound on the narrowed
output via `|narrowed| ≤ |narrowed - fp| + |fp| ≤ (η_sf · c + tail) + c`.
-/

section NarrowBridges

variable [ff_wide : FloatFormat] [FloorRing R]

/-- Unified narrow bridge: a `HasAbsBound c` on a wide-format value
yields a tightened `HasAbsBoundS` on the narrowed storage value.

Output bound: `(1 + η_sf) · c + 2^(min_exp_sf - prec_sf)`. -/
theorem HasAbsBound.fromFp_narrow_unified
    (sf : StorageFormat) (ctx : StorageFp.NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (h_no_nan : sf.maxManFieldAtMaxExp ≥ 2 ^ sf.manBits - 1)
    (fp : FiniteFp) (hm : fp.m ≠ 0)
    (h_no_ov : (StorageFp.roundSigCore fp.s fp.m (fp.e - FloatFormat.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM (fp.toVal : R)
          = @Fp.finite ctx.floatFormat fp_out)
    {c : R} (h : HasAbsBound (R := R) c fp) :
    HasAbsBoundS (R := R)
      ((1 + @FloatFormat.hEps ctx.floatFormat R _) * c
        + (2 : R) ^ (@FloatFormat.min_exp ctx.floatFormat
              - @FloatFormat.prec ctx.floatFormat))
      (StorageFp.fromFp sf policy (Fp.finite fp)) := by
  refine ⟨?_⟩
  have h_err := StorageFp.fromFp_widen_abs_error_unified (R := R) ff_wide sf ctx
    policy hsigned h_no_nan fp hm h_no_ov fp_out h_round_finite
  have h_fp_le : |(fp.toVal : R)| ≤ c := h.toVal_abs_le
  have hEps_nn : (0 : R) ≤ @FloatFormat.hEps ctx.floatFormat R _ := by
    unfold FloatFormat.hEps; positivity
  set N := @StorageFp.toVal sf
    (StorageFp.fromFp sf policy (Fp.finite fp)) R _
  set W := (fp.toVal : R)
  set t := @FloatFormat.hEps ctx.floatFormat R _
  set τ := (2 : R) ^ (@FloatFormat.min_exp ctx.floatFormat
    - @FloatFormat.prec ctx.floatFormat)
  have h_tri : |N| ≤ |N - W| + |W| := by
    have heq : N = (N - W) + W := by ring
    calc |N| = |(N - W) + W| := by rw [← heq]
      _ ≤ |N - W| + |W| := abs_add_le _ _
  calc |N| ≤ |N - W| + |W| := h_tri
    _ ≤ (t * |W| + τ) + |W| := by gcongr
    _ = (1 + t) * |W| + τ := by ring
    _ ≤ (1 + t) * c + τ := by
      have h1 : (1 + t) * |W| ≤ (1 + t) * c :=
        mul_le_mul_of_nonneg_left h_fp_le (by linarith)
      linarith

/-- Normal-range narrow bridge: when the wide value sits in sf's normal
range, the narrow bound is `(1 + η_sf) · c` with no subnormal tail. -/
theorem HasAbsBound.fromFp_narrow_normal
    (sf : StorageFormat) (ctx : StorageFp.NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (h_no_nan : sf.maxManFieldAtMaxExp ≥ 2 ^ sf.manBits - 1)
    (fp : FiniteFp) (hm : fp.m ≠ 0)
    (h_no_ov : (StorageFp.roundSigCore fp.s fp.m (fp.e - FloatFormat.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM (fp.toVal : R)
          = @Fp.finite ctx.floatFormat fp_out)
    (h_x_normal : (2 : R) ^ (1 - (sf.bias : ℤ)) ≤ |(fp.toVal : R)|)
    {c : R} (h : HasAbsBound (R := R) c fp) :
    HasAbsBoundS (R := R)
      ((1 + @FloatFormat.hEps ctx.floatFormat R _) * c)
      (StorageFp.fromFp sf policy (Fp.finite fp)) := by
  refine ⟨?_⟩
  have h_err := StorageFp.fromFp_widen_abs_error_normal (R := R) ff_wide sf ctx
    policy hsigned h_no_nan fp hm h_no_ov fp_out h_round_finite h_x_normal
  have h_fp_le : |(fp.toVal : R)| ≤ c := h.toVal_abs_le
  have hEps_nn : (0 : R) ≤ @FloatFormat.hEps ctx.floatFormat R _ := by
    unfold FloatFormat.hEps; positivity
  set N := @StorageFp.toVal sf
    (StorageFp.fromFp sf policy (Fp.finite fp)) R _
  set W := (fp.toVal : R)
  set t := @FloatFormat.hEps ctx.floatFormat R _
  have h_tri : |N| ≤ |N - W| + |W| := by
    have heq : N = (N - W) + W := by ring
    calc |N| = |(N - W) + W| := by rw [← heq]
      _ ≤ |N - W| + |W| := abs_add_le _ _
  calc |N| ≤ |N - W| + |W| := h_tri
    _ ≤ t * |W| + |W| := by gcongr
    _ = (1 + t) * |W| := by ring
    _ ≤ (1 + t) * c := mul_le_mul_of_nonneg_left h_fp_le (by linarith)

end NarrowBridges

/-! ## Chain bridges: bundle → narrowed-storage

Compose `FpSumBound.hasAbsBound_of_uniform` (and the dot-product variant)
with `HasAbsBound.fromFp_narrow_unified`: takes a wide-format algorithm
bundle plus a uniform input bound, produces a magnitude bound on the
*narrowed* storage output of `fromFp ∘ b.result`.

The output bound is `(1 + η_sf) · b.magBound(...) + 2^(min_exp_sf - prec_sf)`
— linear in the bundle's `magBound` plus the standard subnormal tail.
-/

section ChainBridges

open FpSum FpDotProduct

variable [ff_wide : FloatFormat] [FloorRing R]

/-- `FpSumBound` composed with narrowing: from a uniform per-index bound
on the wide-format inputs, derive a `HasAbsBoundS` on the narrowed sum. -/
theorem FpSum.FpSumBound.hasAbsBoundS_uniform_via_narrow
    {n : ℕ} {xs : Fin n → FiniteFp} (b : FpSumBound xs R)
    (sf : StorageFormat) (ctx : StorageFp.NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (h_no_nan : sf.maxManFieldAtMaxExp ≥ 2 ^ sf.manBits - 1)
    (hm : b.result.m ≠ 0)
    (h_no_ov : (StorageFp.roundSigCore b.result.s b.result.m
        (b.result.e - FloatFormat.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM (b.result.toVal : R)
          = @Fp.finite ctx.floatFormat fp_out)
    (c : R) (h_bounds : ∀ i, HasAbsBound (R := R) c (xs i)) :
    HasAbsBoundS (R := R)
      ((1 + @FloatFormat.hEps ctx.floatFormat R _) * b.magBound c
        + (2 : R) ^ (@FloatFormat.min_exp ctx.floatFormat
              - @FloatFormat.prec ctx.floatFormat))
      (StorageFp.fromFp sf policy (Fp.finite b.result)) :=
  HasAbsBound.fromFp_narrow_unified sf ctx policy hsigned h_no_nan
    b.result hm h_no_ov fp_out h_round_finite (b.hasAbsBound_of_uniform c h_bounds)

/-- `FpDotProductBound` composed with narrowing: from uniform per-index
bounds on both wide-format input vectors, derive a `HasAbsBoundS` on the
narrowed dot-product result. -/
theorem FpDotProduct.FpDotProductBound.hasAbsBoundS_uniform_via_narrow
    {n : ℕ} {xs ys : Fin n → FiniteFp} (b : FpDotProductBound xs ys R)
    (sf : StorageFormat) (ctx : StorageFp.NarrowingContext R sf)
    (policy : StorageOverflowPolicy)
    (hsigned : sf.hasSigned = true)
    (h_no_nan : sf.maxManFieldAtMaxExp ≥ 2 ^ sf.manBits - 1)
    (hm : b.result.m ≠ 0)
    (h_no_ov : (StorageFp.roundSigCore b.result.s b.result.m
        (b.result.e - FloatFormat.prec + 1) (sf.manBits + 1)
        (1 - (sf.bias : ℤ)) ((sf.maxExpField : ℤ) - (sf.bias : ℤ))
        StorageFp.rneRoundUp).2.2 = false)
    (fp_out : @FiniteFp ctx.floatFormat)
    (h_round_finite :
        @RMode.round R ctx.floatFormat ctx.instM (b.result.toVal : R)
          = @Fp.finite ctx.floatFormat fp_out)
    (c_x c_y : R)
    (h_x : ∀ i, HasAbsBound (R := R) c_x (xs i))
    (h_y : ∀ i, HasAbsBound (R := R) c_y (ys i)) :
    HasAbsBoundS (R := R)
      ((1 + @FloatFormat.hEps ctx.floatFormat R _) * b.magBound c_x c_y
        + (2 : R) ^ (@FloatFormat.min_exp ctx.floatFormat
              - @FloatFormat.prec ctx.floatFormat))
      (StorageFp.fromFp sf policy (Fp.finite b.result)) :=
  HasAbsBound.fromFp_narrow_unified sf ctx policy hsigned h_no_nan
    b.result hm h_no_ov fp_out h_round_finite (b.hasAbsBound_of_uniform c_x c_y h_x h_y)

end ChainBridges

end Flean.Tags
