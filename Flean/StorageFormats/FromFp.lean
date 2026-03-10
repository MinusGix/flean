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
## Core Conversion: Fp → StorageFp
-/

/-- Convert an `Fp` value to a `StorageFp` in the target storage format.

    The conversion handles NaN, infinity, and finite values with rounding (RNE)
    and overflow/underflow according to the given policy. -/
def fromFp [inst : FloatFormat] (f : StorageFormat)
    (policy : StorageOverflowPolicy)
    (x : @Fp inst) : StorageFp f :=
  match x with
  | .NaN => canonicalNaN f
  | .infinite sign =>
    if f.hasInf then infEncoding f sign
    else applyOverflow f policy sign
  | .finite fp =>
    -- The source value is: (-1)^s * m * 2^(e - prec + 1)
    -- where prec = FloatFormat.prec (source format precision)
    if fp.m = 0 then
      -- Zero (preserve sign)
      if fp.s then negZero f else zero f
    else
      -- Nonzero finite value
      -- Source ULP exponent: e - (src_prec - 1)
      -- Target ULP exponent for normal: target_e - manBits
      -- Target ULP exponent for subnormal: (1 - bias) - manBits
      let target_prec : ℕ := f.manBits + 1  -- including implicit bit
      let target_max_exp : ℤ := (f.maxExpField : ℤ) - (f.bias : ℤ)
      -- Compute the significand at the target's ULP scale
      -- We need: m_target * 2^(target_ulp_exp) = m * 2^(src_ulp_exp)
      -- First, find what exponent the source value would have in the target format
      -- The source significand m is in [2^(prec-1), 2^prec) for normal values
      -- We need to express it at the target precision
      let shift : ℤ := inst.prec - 1 - (f.manBits : ℤ)
        -- How many bits to discard from the source significand
        -- (positive when source has more precision than target)
      -- Compute target exponent: the binade exponent
      -- Source: m ∈ [2^(prec-1), 2^prec), exponent e
      -- Target: m_t ∈ [2^manBits, 2^(manBits+1)), exponent e_t
      -- We want e_t = e (same binade) when shift ≥ 0
      let target_e : ℤ := fp.e
      -- Round the significand
      let rounded_m : ℕ :=
        if shift ≥ 0 then roundRNE fp.m shift.toNat
        else fp.m * 2 ^ (-shift).toNat  -- target has MORE precision; shift left
      -- Check if rounding caused a carry (rounded_m = 2^target_prec)
      let (final_m, final_e) : ℕ × ℤ :=
        if rounded_m ≥ 2 ^ target_prec then
          (rounded_m / 2, target_e + 1)
        else
          (rounded_m, target_e)
      -- Now check overflow/underflow
      if final_e > target_max_exp then
        -- Overflow
        applyOverflow f policy fp.s
      else if final_e < 1 - (f.bias : ℤ) then
        -- Below minimum normal exponent — try subnormal
        let subnorm_shift : ℤ := (1 - (f.bias : ℤ)) - final_e
        if subnorm_shift ≥ target_prec then
          -- Complete underflow: flush to zero
          if fp.s then negZero f else zero f
        else
          -- Subnormal: shift significand right
          let sub_m := roundRNE final_m subnorm_shift.toNat
          if sub_m = 0 then
            if fp.s then negZero f else zero f
          else
            -- Subnormal encoding: exp field = 0, man field = sub_m
            ofFields f fp.s 0 sub_m
      else
        -- Normal encoding
        let exp_field : ℕ := (final_e + (f.bias : ℤ)).toNat
        let man_field : ℕ := final_m - 2 ^ f.manBits  -- strip implicit bit
        -- Check if this is at maxExpField with mantissa exceeding maxManFieldAtMaxExp
        -- (for E4M3 style where some patterns at max exp are NaN)
        if exp_field = f.maxExpField && man_field > f.maxManFieldAtMaxExp then
          applyOverflow f policy fp.s
        else
          ofFields f fp.s exp_field man_field

/-!
## Basic Properties
-/

theorem fromFp_nan [FloatFormat] (f : StorageFormat) (policy : StorageOverflowPolicy) :
    fromFp f policy (@Fp.NaN _) = canonicalNaN f := rfl

theorem fromFp_inf [FloatFormat] (f : StorageFormat) (policy : StorageOverflowPolicy) (sign : Bool) :
    fromFp f policy (Fp.infinite sign) =
      if f.hasInf then infEncoding f sign else applyOverflow f policy sign := rfl

/-!
## Concrete Verification (E4M3)

Verify the conversion produces correct encodings for known values.
-/

section E4M3_verification

-- Use E4M3's matching FloatFormat as the source
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

end E5M2_verification

end StorageFp
