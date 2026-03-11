import Flean.StorageFormats.Defs
import Flean.StorageFormats.Conversion
import Flean.Defs

/-!
# Conversion from IEEE Fp to StorageFp

Converts an `Fp` value (which may be finite, infinite, or NaN) from a wider IEEE format
to a `StorageFp` storage encoding, with configurable overflow handling.

The OCP MX specification defines two overflow behaviors:
- **Saturate**: clamp to ±maxFinite (universal in ML practice)
- **Overflow to infinity/NaN**: produce ∞ (E5M2) or NaN (E4M3) on overflow

The conversion pipeline:
1. NaN → target format's canonical NaN
2. ±∞ → keep if target has infinity, else apply overflow policy
3. Finite → round significand, check overflow/underflow, encode
-/

/-!
## Overflow Policy
-/

/-- Controls what happens when a value exceeds the target storage format's range. -/
inductive StorageOverflowPolicy where
  /-- Clamp to ±maxFinite. The standard behavior for ML workloads. -/
  | saturate
  /-- Produce ±∞ if the format supports it, otherwise produce NaN.
      This is the IEEE-like behavior for E5M2. -/
  | overflow
deriving Repr, DecidableEq

/-!
## Canonical Encodings
-/

namespace StorageFp

variable {f : StorageFormat}

/-- The canonical NaN encoding for a storage format.
    For nanCount=1 (E4M3 style): all-ones exponent and all-ones mantissa.
    For nanCount>1 (E5M2 style): all-ones exponent and mantissa=1. -/
def canonicalNaN (f : StorageFormat) : StorageFp f :=
  if f.hasNaN then
    let nanMan := if f.nanCount = 1 then 2 ^ f.manBits - 1 else 1
    ofFields f false (2 ^ f.expBits - 1) nanMan
  else
    -- Format has no NaN encoding; return zero as fallback
    zero f

/-- The ±infinity encoding. Only meaningful when f.hasInf = true. -/
def infEncoding (f : StorageFormat) (sign : Bool) : StorageFp f :=
  ofFields f sign (2 ^ f.expBits - 1) 0

/-- The ±maxFinite encoding (largest representable finite magnitude). -/
def signedMaxFinite (f : StorageFormat) (sign : Bool) : StorageFp f :=
  ofFields f sign f.maxExpField f.maxManFieldAtMaxExp

/-- Apply the overflow policy to produce a result when a value exceeds the target range. -/
def applyOverflow (f : StorageFormat) (policy : StorageOverflowPolicy) (sign : Bool) :
    StorageFp f :=
  match policy with
  | .saturate => signedMaxFinite f sign
  | .overflow =>
    if f.hasInf then infEncoding f sign
    else canonicalNaN f

/-!
## Significand Rounding (RNE)

Round a natural number significand by discarding `shift` low bits,
using round-to-nearest-ties-to-even.
-/

/-- Round a natural number right by `shift` bits using round-to-nearest-ties-to-even.
    Returns the rounded value (shifted right). -/
def roundRNE (mag : ℕ) (shift : ℕ) : ℕ :=
  if shift = 0 then mag
  else
    let truncated := mag >>> shift
    let halfBit := (mag >>> (shift - 1)) &&& 1  -- the bit just below the cut
    let lowerBits := mag &&& (2 ^ (shift - 1) - 1)  -- bits below the half bit
    if halfBit = 1 then
      if lowerBits ≠ 0 then
        -- Above halfway: round up
        truncated + 1
      else
        -- Exactly halfway: round to even
        if truncated &&& 1 = 1 then truncated + 1  -- odd → round up
        else truncated  -- even → keep
    else
      -- Below halfway: round down (truncate)
      truncated

/-!
## Core Rounding Computation

The shared rounding algorithm for floating-point conversions. Given a significand
magnitude, base exponent, target format parameters, and a rounding decision function,
computes the rounded significand and exponent.

Both `fromFp` (RNE-hardcoded) and `roundIntSigM` (configurable mode) use essentially
this same algorithm. Factoring it out makes correctness proofs straightforward.
-/

/-- RNE rounding decision: should we round up given quotient, remainder, and shift?
    This is the `policyShouldRoundUp .nearestEven` function, defined independently
    to avoid importing the rounding mode infrastructure. -/
def rneRoundUp (_sign : Bool) (q r shift : ℕ) : Bool :=
  if r = 0 then false
  else
    let half := 2 ^ (shift - 1)
    if r > half then true
    else if r < half then false
    else q % 2 ≠ 0

/-- Core rounding computation: round magnitude `mag` with base exponent `e_base`
    to the given format parameters. Returns `(m_final, e_ulp_final, overflow)`.

    The `shouldRoundUp sign q r shift` parameter decides whether to round up,
    enabling different rounding modes to share this computation. -/
def roundSigCore (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (prec : ℕ) (min_exp max_exp : ℤ)
    (shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool) : ℕ × ℤ × Bool :=
  let bits : ℤ := (Nat.log2 mag + 1 : ℕ)
  let e_ulp := max (e_base + bits - ↑prec) (min_exp - ↑prec + 1)
  let shift := e_ulp - e_base
  if shift ≤ 0 then
    -- Exact: value fits without rounding (left-shift to align)
    let m := mag * 2 ^ (-shift).toNat
    let e_stored := e_ulp + ↑prec - 1
    if e_stored > max_exp then (m, e_ulp, true) else (m, e_ulp, false)
  else
    -- Rounding needed: discard low bits
    let shift_nat := shift.toNat
    let q := mag / 2 ^ shift_nat
    let r := mag % 2 ^ shift_nat
    let m_rounded := if shouldRoundUp sign q r shift_nat then q + 1 else q
    -- Carry check: rounding may push significand to 2^prec
    if m_rounded ≥ 2 ^ prec then
      let m_final := m_rounded / 2
      let e_ulp_final := e_ulp + 1
      if e_ulp_final + ↑prec - 1 > max_exp then (m_final, e_ulp_final, true)
      else (m_final, e_ulp_final, false)
    else
      if e_ulp + ↑prec - 1 > max_exp then (m_rounded, e_ulp, true)
      else (m_rounded, e_ulp, false)

/-- Encode a rounded result `(m_final, e_ulp_final)` as a `StorageFp`,
    handling zero, subnormal, normal, and NaN-exclusion cases. -/
def encodeRounded (f : StorageFormat) (policy : StorageOverflowPolicy)
    (sign : Bool) (m_final : ℕ) (e_ulp_final : ℤ) : StorageFp f :=
  if m_final = 0 then
    if sign then negZero f else zero f
  else if m_final < 2 ^ f.manBits then
    -- Subnormal: exp_field = 0, man = m_final (no implicit leading 1)
    ofFields f sign 0 m_final
  else
    -- Normal encoding
    let e_stored := e_ulp_final + (f.manBits : ℤ)
    let exp_field := (e_stored + (f.bias : ℤ)).toNat
    let man_field := m_final - 2 ^ f.manBits
    -- E4M3-style NaN exclusion at max exponent
    if exp_field = f.maxExpField && man_field > f.maxManFieldAtMaxExp then
      applyOverflow f policy sign
    else
      ofFields f sign exp_field man_field

/-!
## Core Conversion: Fp → StorageFp
-/

/-- Convert an `Fp` value to a `StorageFp` in the target storage format.

    The conversion handles NaN, infinity, and finite values with rounding (RNE)
    and overflow/underflow according to the given policy.

    The significand is rounded in a single pass via `roundSigCore`, using the
    correct ULP exponent clamped to the subnormal minimum. This avoids
    double-rounding errors that would occur from separate normal/subnormal steps.

    This function shares its core rounding computation with `roundIntSigM`,
    making correctness proofs straightforward. -/
def fromFp [inst : FloatFormat] (f : StorageFormat)
    (policy : StorageOverflowPolicy)
    (x : @Fp inst) : StorageFp f :=
  match x with
  | .NaN => canonicalNaN f
  | .infinite sign =>
    if f.hasInf then infEncoding f sign
    else applyOverflow f policy sign
  | .finite fp =>
    if fp.m = 0 then
      if fp.s then negZero f else zero f
    else
      let (m_final, e_ulp_final, overflow) := roundSigCore fp.s fp.m
        (fp.e - inst.prec + 1) (f.manBits + 1)
        (1 - (f.bias : ℤ)) ((f.maxExpField : ℤ) - (f.bias : ℤ))
        rneRoundUp
      if overflow then applyOverflow f policy fp.s
      else encodeRounded f policy fp.s m_final e_ulp_final

/-!
## Basic Properties
-/

/-- Convenience wrapper for converting a finite value. -/
def fromFiniteFp [FloatFormat] (f : StorageFormat) (policy : StorageOverflowPolicy)
    (fp : FiniteFp) : StorageFp f :=
  fromFp f policy (Fp.finite fp)

theorem fromFp_nan [FloatFormat] (f : StorageFormat) (policy : StorageOverflowPolicy) :
    fromFp f policy (@Fp.NaN _) = canonicalNaN f := rfl

theorem fromFp_inf [FloatFormat] (f : StorageFormat) (policy : StorageOverflowPolicy) (sign : Bool) :
    fromFp f policy (Fp.infinite sign) =
      if f.hasInf then infEncoding f sign else applyOverflow f policy sign := rfl

/-!
## Concrete Verification

Verify the conversion produces correct encodings for known values.
Uses the matching FloatFormat as the source (identity precision conversion),
which exercises every code path: NaN, infinity, overflow, normal, subnormal, zero.
-/

section E4M3_verification

private local instance : FloatFormat := FloatFormat.ofE4M3

-- NaN → canonical NaN
theorem fromFp_nan_E4M3 :
    (fromFp E4M3 .saturate Fp.NaN).isNaN = true := by decide

-- Infinity → saturate to maxFinite (E4M3 has no infinity)
theorem fromFp_posInf_saturate_E4M3 :
    fromFp E4M3 .saturate (Fp.infinite false) = signedMaxFinite E4M3 false := by decide

-- Infinity → NaN under overflow policy
theorem fromFp_posInf_overflow_E4M3 :
    fromFp E4M3 .overflow (Fp.infinite false) = canonicalNaN E4M3 := by decide

-- Zero → zero
theorem fromFp_zero_E4M3 :
    fromFp E4M3 .saturate (Fp.finite ⟨false, -6, 0, by decide⟩) = zero E4M3 := by decide

-- Negative zero → negative zero
theorem fromFp_negZero_E4M3 :
    fromFp E4M3 .saturate (Fp.finite ⟨true, -6, 0, by decide⟩) = negZero E4M3 := by decide

-- 1.0 (normal: e=0, m=8) → one E4M3
theorem fromFp_one_E4M3 :
    fromFiniteFp E4M3 .saturate ⟨false, 0, 8, by decide⟩ = one E4M3 := by decide

-- 448.0 (max finite: e=8, m=14) → maxFinite
theorem fromFp_maxFinite_E4M3 :
    fromFiniteFp E4M3 .saturate ⟨false, 8, 14, by decide⟩ = maxFinite E4M3 := by decide

-- Overflow: e=8, m=15 (would be 480, exceeds 448) → saturate to maxFinite
-- m=15 at exp 8: 15 * 2^(8 - 3) = 15 * 32 = 480 > 448
-- But m=15 at E4M3 max exp with man_field=7 hits NaN exclusion
theorem fromFp_overflow_E4M3 :
    fromFiniteFp E4M3 .saturate ⟨false, 8, 15, by decide⟩ =
      signedMaxFinite E4M3 false := by decide

-- Smallest subnormal: e=-6, m=1 → minPos
theorem fromFp_minPos_E4M3 :
    fromFiniteFp E4M3 .saturate ⟨false, -6, 1, by decide⟩ = minPos E4M3 := by decide

-- Negative value: -1.0
theorem fromFp_negOne_E4M3 :
    fromFiniteFp E4M3 .saturate ⟨true, 0, 8, by decide⟩ =
      ofFields E4M3 true 7 0 := by decide

end E4M3_verification

section E5M2_verification

private local instance : FloatFormat := FloatFormat.ofE5M2

-- NaN → canonical NaN
theorem fromFp_nan_E5M2 :
    (fromFp E5M2 .saturate Fp.NaN).isNaN = true := by decide

-- Infinity → kept (E5M2 supports infinity)
theorem fromFp_posInf_E5M2 :
    (fromFp E5M2 .saturate (Fp.infinite false)).isInf = true := by decide

-- Zero → zero
theorem fromFp_zero_E5M2 :
    fromFp E5M2 .saturate (Fp.finite ⟨false, -14, 0, by decide⟩) = zero E5M2 := by decide

-- 1.0 (normal: e=0, m=4) → one E5M2
theorem fromFp_one_E5M2 :
    fromFiniteFp E5M2 .saturate ⟨false, 0, 4, by decide⟩ = one E5M2 := by decide

-- Smallest subnormal
theorem fromFp_minPos_E5M2 :
    fromFiniteFp E5M2 .saturate ⟨false, -14, 1, by decide⟩ = minPos E5M2 := by decide

end E5M2_verification

section E3M2_verification

private local instance : FloatFormat := FloatFormat.ofE3M2

-- Zero → zero
theorem fromFp_zero_E3M2 :
    fromFp E3M2 .saturate (Fp.finite ⟨false, -2, 0, by decide⟩) = zero E3M2 := by decide

-- 1.0 (normal: e=0, m=4) → one E3M2
theorem fromFp_one_E3M2 :
    fromFiniteFp E3M2 .saturate ⟨false, 0, 4, by decide⟩ = one E3M2 := by decide

-- maxFinite (e=4, m=7) → maxFinite E3M2
theorem fromFp_maxFinite_E3M2 :
    fromFiniteFp E3M2 .saturate ⟨false, 4, 7, by decide⟩ = maxFinite E3M2 := by decide

-- Smallest subnormal: e=-2, m=1 → minPos E3M2
theorem fromFp_minPos_E3M2 :
    fromFiniteFp E3M2 .saturate ⟨false, -2, 1, by decide⟩ = minPos E3M2 := by decide

end E3M2_verification

section E2M3_verification

private local instance : FloatFormat := FloatFormat.ofE2M3

-- Zero → zero
theorem fromFp_zero_E2M3 :
    fromFp E2M3 .saturate (Fp.finite ⟨false, 0, 0, by decide⟩) = zero E2M3 := by decide

-- 1.0 (normal: e=0, m=8) → one E2M3
theorem fromFp_one_E2M3 :
    fromFiniteFp E2M3 .saturate ⟨false, 0, 8, by decide⟩ = one E2M3 := by decide

-- maxFinite (e=2, m=15) → maxFinite E2M3
theorem fromFp_maxFinite_E2M3 :
    fromFiniteFp E2M3 .saturate ⟨false, 2, 15, by decide⟩ = maxFinite E2M3 := by decide

-- Smallest subnormal: e=0, m=1 → minPos E2M3
theorem fromFp_minPos_E2M3 :
    fromFiniteFp E2M3 .saturate ⟨false, 0, 1, by decide⟩ = minPos E2M3 := by decide

end E2M3_verification

section E2M1_verification

private local instance : FloatFormat := FloatFormat.ofE2M1

-- Zero → zero
theorem fromFp_zero_E2M1 :
    fromFp E2M1 .saturate (Fp.finite ⟨false, 0, 0, by decide⟩) = zero E2M1 := by decide

-- 1.0 (normal: e=0, m=2) → one E2M1
theorem fromFp_one_E2M1 :
    fromFiniteFp E2M1 .saturate ⟨false, 0, 2, by decide⟩ = one E2M1 := by decide

-- maxFinite (e=2, m=3) → maxFinite E2M1
theorem fromFp_maxFinite_E2M1 :
    fromFiniteFp E2M1 .saturate ⟨false, 2, 3, by decide⟩ = maxFinite E2M1 := by decide

-- Smallest subnormal: e=0, m=1 → minPos E2M1
theorem fromFp_minPos_E2M1 :
    fromFiniteFp E2M1 .saturate ⟨false, 0, 1, by decide⟩ = minPos E2M1 := by decide

end E2M1_verification

end StorageFp
