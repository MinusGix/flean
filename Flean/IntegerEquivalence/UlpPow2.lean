import Flean.Operations.MulPow2
import Flean.Ulp

/-! # FP ↔ Integer equivalence: ULP as a `pow2Float`

Phase 1.6 of the FP ↔ Integer equivalence area
(see `.claude/notes/fp-integer-equivalence.md`).

For a value `v` whose unit in last place lands in the *normal* exponent
range (`min_exp ≤ Int.log 2 |v| - prec + 1`), the ULP `Fp.ulp v` is itself
a representable normal float — namely `pow2Float (Int.log 2 |v| - prec + 1)`.

This bridges `Flean/Ulp.lean` to the `pow2Float` infrastructure shipped in
`Flean/Operations/MulPow2.lean`. Downstream consequences:

* The bit-level pattern of the ULP can be constructed via `setBiasedExponent`
  (the `pow2Float k` workhorse).
* `nextUp f - f = ulp f` (within a binade) becomes a `pow2Float` identity.

The subnormal-ULP case (`Int.log 2 |v| < min_exp + prec - 1`) is excluded by
`pow2Float`'s `min_exp ≤ k` precondition; it gives a subnormal float and
needs a different bit pattern.
-/

namespace Fp

/-! ## Generic value-level bridge -/

/-- For `v` whose ULP lands in the normal exponent range,
`ulp v = pow2Float (Int.log 2 |v| - prec + 1)`. -/
theorem ulp_eq_pow2Float_toVal {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] [FloatFormat] (v : R)
    (hv : (2 : R) ^ FloatFormat.min_exp ≤ |v|)
    (h_lo : FloatFormat.min_exp ≤ Int.log 2 |v| - FloatFormat.prec + 1)
    (h_hi : Int.log 2 |v| - FloatFormat.prec + 1 ≤ FloatFormat.max_exp) :
    Fp.ulp v = (pow2Float (Int.log 2 |v| - FloatFormat.prec + 1) h_lo h_hi).toVal := by
  rw [ulp_normal_eq v hv, pow2Float_toVal]

/-! ## FiniteFp specialization (normal `f`)

For normal `f`, `Int.log 2 |f.toVal| = f.e`, so the ULP exponent is just
`f.e - prec + 1`. -/

/-- For a normal `f` whose `f.e - prec + 1` lands in the normal exponent
range, `ulp f.toVal` is the value of `pow2Float (f.e - prec + 1)`. -/
theorem ulp_finite_eq_pow2Float_toVal {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] [FloatFormat] (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_lo : FloatFormat.min_exp ≤ f.e - FloatFormat.prec + 1) :
    Fp.ulp (f.toVal : R) =
      (pow2Float (f.e - FloatFormat.prec + 1) h_lo
        (by have := f.valid.2.1; have := FloatFormat.valid_prec; omega)).toVal := by
  -- Route through `ulp_har` to avoid `Int.log` reasoning.
  -- `ulp_har_normal_eq f hn : ulp_har f = (2 : ℚ)^(f.e - prec + 1)`
  -- `ulp_har_eq_ulp     f hn : (ulp_har f : R) = ulp f.toVal`
  rw [← ulp_har_eq_ulp (R := R) f hn, ulp_har_normal_eq f hn, pow2Float_toVal]
  push_cast
  rfl

end Fp
