import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Rounding.ModeClass

/-!
# Phase 0 Pilot: Constraint-Tagged Values — IsNonneg (Composition)

**Status**: Phase 0 composition test. Fourth pilot. Explicitly tests
that a tag propagates across **two different operations** in sequence —
not just through one op applied repeatedly.

## What this pilot tests

Previous pilots (`Simplex`, `Normal`, `Sterbenz`) each tagged ONE
operation, leaving composition unvalidated. This file tags two:
`fpMulFinite` and `fpAddFinite`. The end-to-end demo theorem
`fpMulAdd_isNonneg` chains them: `(x · y) + bias` stays `IsNonneg` when
all three inputs are.

The preservation lemmas thread `IsNonneg` from inputs to output
conditional on the op's result being finite. Downstream consumers who
track finiteness separately (via `FpSumBound.ofNaive`-style builders or
direct witnesses) get the tag-propagation "for free" once they hand
over finiteness witnesses.

## What composition tells us

With three single-op pilots and one two-op composition pilot in hand,
the pattern's open questions on composition are:

* **Preservation lemmas are boilerplate** — each is "result of round is
  nonneg if input was nonneg," varying only by which `fp*Finite` def
  you unfold. A typeclass (`IsNonneg.preserves`) + one meta-lemma could
  auto-discharge these from the correctness + monotonicity laws the
  operation already provides.
* **Finiteness is an orthogonal concern**. The tag says "if the result
  exists, it's non-negative." Finiteness witnesses come from a
  different chain (range bounds, `FpSumBound`-style abstraction).
  Framework design shouldn't bundle the two.
* **Zero-sum / zero-product cases need structural handling**, because
  `fp*Finite_correct` only applies to non-zero results. This pilot
  handles them via the existing `fpAddFinite_zero_left_val` helper
  (for fpAdd) and inline unfolding (for fpMul). A tag framework should
  factor this out as a reusable `round_preserves_nonneg` lemma.

## Friction points surfaced

* `fpMulFinite_correct` requires `(x.toVal * y.toVal) ≠ 0`; the
  zero-product case needs separate treatment. A `fpMulFinite_toVal`
  lemma covering both cases (like `fpAddFinite_zero_left_val` does for
  zero-sum) would smooth this.
* `round_nonneg_of_nonneg` is genuinely reusable infrastructure — it's
  what ties `RModeMono` + `RModeZero` together for nonneg-propagation.
  Should live in `Rounding/` eventually.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag -/

/-- `IsNonneg R x` asserts that the real value of `x : FiniteFp`
(evaluated in `R`) is non-negative. -/
structure IsNonneg (x : FiniteFp) : Prop where
  /-- `0 ≤ x.toVal`. -/
  toVal_nonneg : (0 : R) ≤ x.toVal

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- The canonical zero float satisfies `IsNonneg`. -/
theorem IsNonneg.zero : IsNonneg (R := R) (0 : FiniteFp) :=
  ⟨by rw [FiniteFp.toVal_zero]⟩

/-! ## Rounding helper

`round_nonneg_of_nonneg` is the core fact tying tag preservation through
any rounded op to `RModeMono` + `RModeZero`. -/

omit [FloorRing R] in
private theorem round_nonneg_of_nonneg [RMode R] [RModeMono R] [RModeZero R]
    {x : R} (hx : 0 ≤ x) {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    (0 : R) ≤ f.toVal := by
  have h_mono := RModeMono.round_mono (R := R) hx
  rw [RModeZero.round_zero (R := R), hf] at h_mono
  have hle : (0 : FiniteFp) ≤ f := (Fp.finite_le_finite_iff 0 f).mp h_mono
  have := FiniteFp.le_toVal_le R hle
  rwa [FiniteFp.toVal_zero] at this

/-! ## Preservation: `fpAddFinite` -/

/-- Adding two non-negative floats yields a non-negative result,
conditional on finiteness. -/
theorem IsNonneg.fpAdd [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeMono R] [RModeZero R] [RModeIdem R]
    {x y f : FiniteFp} (hx : IsNonneg (R := R) x) (hy : IsNonneg (R := R) y)
    (hf : fpAddFinite x y = Fp.finite f) :
    IsNonneg (R := R) f := by
  refine ⟨?_⟩
  by_cases hsum : (x.toVal : R) + y.toVal = 0
  · -- `x.toVal + y.toVal = 0` with both ≥ 0 forces both to be zero.
    have hx_val : (x.toVal : R) = 0 := by linarith [hx.toVal_nonneg, hy.toVal_nonneg]
    have hy_val : (y.toVal : R) = 0 := by linarith [hx.toVal_nonneg, hy.toVal_nonneg]
    have hxm : x.m = 0 := (FiniteFp.toVal_significand_zero_iff (R := R)).mpr hx_val
    have hadd' : x + y = Fp.finite f := by simpa using hf
    have hfval := fpAddFinite_zero_left_val (R := R) x y hxm f hadd'
    rw [hfval]; exact le_of_eq hy_val.symm
  · have hcorr := fpAddFinite_correct (R := R) x y hsum
    simp only [add_eq_fpAdd, fpAdd_coe_coe] at hcorr
    rw [hcorr] at hf
    exact round_nonneg_of_nonneg (add_nonneg hx.toVal_nonneg hy.toVal_nonneg) hf

/-! ## Preservation: `fpMulFinite`

The zero-product case is handled inline by unfolding `fpMulFinite` to
`roundIntSigM`, which returns a signed zero when the magnitude is 0. -/

omit [FloorRing R] in
/-- `roundIntSigM` with a zero magnitude returns a finite signed zero
whose significand is 0. Local helper for the mul preservation below. -/
private lemma roundIntSigM_mag_zero_m [RModeExec]
    {sign : Bool} {e_base : ℤ} {f : FiniteFp}
    (hf : roundIntSigM sign 0 e_base = Fp.finite f) :
    f.m = 0 := by
  unfold roundIntSigM at hf
  simp only at hf
  have : f = (if sign then (-0 : FiniteFp) else (0 : FiniteFp)) := by
    exact (Fp.finite.inj hf).symm
  rw [this]
  cases sign <;> simp [FiniteFp.neg_def]

/-- Multiplying two non-negative floats yields a non-negative result,
conditional on finiteness. -/
theorem IsNonneg.fpMul [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeMono R] [RModeZero R]
    {x y f : FiniteFp} (hx : IsNonneg (R := R) x) (hy : IsNonneg (R := R) y)
    (hf : fpMulFinite x y = Fp.finite f) :
    IsNonneg (R := R) f := by
  refine ⟨?_⟩
  by_cases hprod : (x.toVal : R) * y.toVal = 0
  · -- `x.toVal * y.toVal = 0` means one operand is zero; the FP mul
    -- returns a signed zero, hence `f.m = 0` and `f.toVal = 0`.
    have hmag : x.m * y.m = 0 := by
      rcases mul_eq_zero.mp hprod with hx0 | hy0
      · rw [(FiniteFp.toVal_significand_zero_iff (R := R)).mpr hx0, zero_mul]
      · rw [(FiniteFp.toVal_significand_zero_iff (R := R)).mpr hy0, mul_zero]
    have hf' : roundIntSigM (x.s ^^ y.s) (x.m * y.m)
        (x.e + y.e - 2 * FloatFormat.prec + 2) = Fp.finite f := hf
    rw [hmag] at hf'
    have hfm : f.m = 0 := roundIntSigM_mag_zero_m hf'
    rw [(FiniteFp.toVal_significand_zero_iff (R := R)).mp hfm]
  · have hcorr := fpMulFinite_correct (R := R) x y hprod
    simp only [mul_eq_fpMul, fpMul_coe_coe] at hcorr
    rw [hcorr] at hf
    exact round_nonneg_of_nonneg (mul_nonneg hx.toVal_nonneg hy.toVal_nonneg) hf

/-! ## Composition demo: mul then add -/

/-- **Composition**: `(x · y) + bias` is non-negative when all three
inputs are non-negative. The tag threads through `fpMulFinite` then
`fpAddFinite`, requiring two separate preservation applications. -/
theorem fpMulAdd_isNonneg [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeMono R] [RModeZero R] [RModeIdem R]
    {x y bias prod result : FiniteFp}
    (hx : IsNonneg (R := R) x) (hy : IsNonneg (R := R) y)
    (hbias : IsNonneg (R := R) bias)
    (hprod : fpMulFinite x y = Fp.finite prod)
    (hresult : fpAddFinite prod bias = Fp.finite result) :
    IsNonneg (R := R) result :=
  (IsNonneg.fpMul hx hy hprod).fpAdd hbias hresult

end Flean.Tags
