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
    -- Source value = (-1)^s * m * 2^(e - prec + 1)
    if fp.m = 0 then
      -- Zero (preserve sign)
      if fp.s then negZero f else zero f
    else
      -- Nonzero finite value.
      -- Use Nat.log to find the true MSB position of the significand.
      -- This correctly handles both normal (m ∈ [2^(prec-1), 2^prec))
      -- and subnormal (m < 2^(prec-1)) source values.
      let src_ulp_exp : ℤ := fp.e - inst.prec + 1
      let msb_pos := Nat.log 2 fp.m  -- position of leading 1 bit
      -- The true binade exponent of the value
      let target_e : ℤ := src_ulp_exp + msb_pos
      -- How many bits to shift: msb_pos - manBits
      -- Positive → discard low bits; negative → pad with zeros
      let shift : ℤ := (msb_pos : ℤ) - (f.manBits : ℤ)
      let target_max_exp : ℤ := (f.maxExpField : ℤ) - (f.bias : ℤ)
      -- Round the significand to target precision
      let rounded_m : ℕ :=
        if shift ≥ 0 then roundRNE fp.m shift.toNat
        else fp.m * 2 ^ (-shift).toNat
      -- Check if rounding caused a carry (rounded_m ≥ 2^(manBits+1))
      let (final_m, final_e) : ℕ × ℤ :=
        if rounded_m ≥ 2 ^ (f.manBits + 1) then
          (rounded_m / 2, target_e + 1)
        else
          (rounded_m, target_e)
      -- Overflow check
      if final_e > target_max_exp then
        applyOverflow f policy fp.s
      -- Subnormal check
      else if final_e < 1 - (f.bias : ℤ) then
        let subnorm_shift : ℤ := (1 - (f.bias : ℤ)) - final_e
        if subnorm_shift ≥ (f.manBits + 1 : ℤ) then
          -- Complete underflow
          if fp.s then negZero f else zero f
        else
          let sub_m := roundRNE final_m subnorm_shift.toNat
          if sub_m = 0 then
            if fp.s then negZero f else zero f
          else
            ofFields f fp.s 0 sub_m
      else
        -- Normal encoding
        let exp_field : ℕ := (final_e + (f.bias : ℤ)).toNat
        let man_field : ℕ := final_m - 2 ^ f.manBits
        -- E4M3-style NaN exclusion at max exponent
        if exp_field = f.maxExpField && man_field > f.maxManFieldAtMaxExp then
          applyOverflow f policy fp.s
        else
          ofFields f fp.s exp_field man_field

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

end StorageFp
