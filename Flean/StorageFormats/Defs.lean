import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Init.Data.BitVec.Lemmas

/-!
# Storage Float Formats

Storage-only floating point formats used as interchange/memory formats in ML workloads.
These formats do not define arithmetic — values are converted to a wider IEEE format
(e.g. FP16, FP32) for computation, then converted back with saturation on overflow.

Covers: E4M3, E5M2, E3M2, E2M3, E2M1, E8M0 from the OCP MX specification.

## Design

Each format is a `BitVec n` wrapper (`StorageFp`) with:
- Field extraction (sign, exponent, mantissa)
- `toVal` generic over any `Field R` (like `FiniteFp.toVal`)
- No arithmetic, no rounding — just encoding/decoding and conversion theorems
-/

/-- A storage float format specifies the bit layout of a storage-only floating point number. -/
structure StorageFormat where
  /-- Number of exponent bits -/
  expBits : ℕ
  /-- Number of mantissa (trailing significand) bits -/
  manBits : ℕ
  /-- Whether the format has a sign bit -/
  hasSigned : Bool := true
  /-- Exponent bias -/
  bias : ℕ
  /-- Whether the format has any NaN encoding -/
  hasNaN : Bool := true
  /-- Number of NaN encodings (0 if hasNaN = false) -/
  nanCount : ℕ := if hasNaN then 1 else 0
  /-- Whether the format has infinity encodings -/
  hasInf : Bool := false
  -- Validity constraints
  /-- Exponent bits must be positive -/
  expBits_pos : 0 < expBits
  /-- Format must have at least 2 bits total -/
  total_ge_two : (if hasSigned then 1 else 0) + expBits + manBits ≥ 2
deriving Repr, DecidableEq

namespace StorageFormat

/-- Total number of bits in the format -/
def bitSize (f : StorageFormat) : ℕ :=
  (if f.hasSigned then 1 else 0) + f.expBits + f.manBits

theorem bitSize_pos (f : StorageFormat) : 0 < f.bitSize := by
  unfold bitSize
  have := f.total_ge_two
  omega

end StorageFormat

/-- A floating point value stored in a storage format. Wraps a `BitVec` of the appropriate width. -/
structure StorageFp (f : StorageFormat) where
  bits : BitVec f.bitSize

namespace StorageFp

variable {f : StorageFormat}

/-- Extract the sign bit (MSB). Returns false (positive) for unsigned formats. -/
def sign (v : StorageFp f) : Bool :=
  if f.hasSigned then
    v.bits.getMsbD 0
  else
    false

/-- Extract the exponent field as a natural number -/
def exp (v : StorageFp f) : ℕ :=
  ((v.bits >>> f.manBits) &&& (BitVec.allOnes f.expBits).zeroExtend f.bitSize).toNat % (2 ^ f.expBits)

/-- Extract the mantissa field as a natural number -/
def man (v : StorageFp f) : ℕ :=
  (v.bits &&& (BitVec.allOnes f.manBits).zeroExtend f.bitSize).toNat % (2 ^ f.manBits)

/-- Whether the exponent field is all ones -/
def isExpAllOnes (v : StorageFp f) : Prop :=
  v.exp = 2 ^ f.expBits - 1

instance : DecidablePred (fun v : StorageFp f => v.isExpAllOnes) :=
  fun v => inferInstanceAs (Decidable (v.exp = 2 ^ f.expBits - 1))

/-- Whether the exponent field is all zeros -/
def isExpZero (v : StorageFp f) : Prop :=
  v.exp = 0

instance : DecidablePred (fun v : StorageFp f => v.isExpZero) :=
  fun v => inferInstanceAs (Decidable (v.exp = 0))

/-- Whether this value is a NaN encoding.
    For E4M3: all-ones exponent AND all-ones mantissa (single NaN pattern).
    For E5M2: all-ones exponent AND nonzero mantissa (multiple NaN patterns).
    For FP6/FP4: no NaN encodings exist. -/
def isNaN (v : StorageFp f) : Prop :=
  f.hasNaN ∧ v.isExpAllOnes ∧
    if f.nanCount = 1 then
      -- Single NaN pattern: mantissa is all ones (E4M3 style)
      v.man = 2 ^ f.manBits - 1
    else if 0 < f.nanCount then
      -- Multiple NaN patterns: mantissa is nonzero (E5M2/IEEE style)
      v.man ≠ 0
    else
      False

/-- Whether this value is an infinity encoding -/
def isInf (v : StorageFp f) : Prop :=
  f.hasInf ∧ v.isExpAllOnes ∧ v.man = 0

/-- Whether this value represents a finite number -/
def isFinite (v : StorageFp f) : Prop :=
  ¬v.isNaN ∧ ¬v.isInf

/-- Whether this is a subnormal number (exponent field is zero, value is not zero) -/
def isSubnormal (v : StorageFp f) : Prop :=
  v.isExpZero ∧ v.man ≠ 0

/-- Whether this is the zero encoding -/
def isZero (v : StorageFp f) : Prop :=
  v.isExpZero ∧ v.man = 0

/-- The unbiased exponent for a finite, nonzero value.
    For normal numbers: exp - bias
    For subnormal numbers: 1 - bias (like IEEE) -/
def unbiasedExp (v : StorageFp f) : ℤ :=
  if v.isExpZero then
    1 - (f.bias : ℤ)
  else
    (v.exp : ℤ) - (f.bias : ℤ)

/-- The effective significand including the implicit bit.
    Normal numbers have an implicit leading 1.
    Subnormal numbers have an implicit leading 0. -/
def effectiveSignificand (v : StorageFp f) : ℕ :=
  if v.isExpZero then
    v.man
  else
    2 ^ f.manBits + v.man

/-- The sign multiplier: 1 for positive, -1 for negative -/
def signVal (v : StorageFp f) {R : Type*} [Field R] : R :=
  if v.sign then -1 else 1

/-- The real value represented by a finite storage float.
    `v = (-1)^s × significand × 2^(unbiasedExp - manBits)`
    This is undefined/meaningless for NaN and infinity encodings. -/
def toVal (v : StorageFp f) {R : Type*} [Field R] : R :=
  v.signVal * (v.effectiveSignificand : R) * (2 : R) ^ (v.unbiasedExp - (f.manBits : ℤ))

/-- The absolute value (magnitude) of the represented number -/
def toValMag (v : StorageFp f) {R : Type*} [Field R] : R :=
  (v.effectiveSignificand : R) * (2 : R) ^ (v.unbiasedExp - (f.manBits : ℤ))

/-! ### Range bounds -/

theorem exp_lt (v : StorageFp f) : v.exp < 2 ^ f.expBits :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))

theorem man_lt (v : StorageFp f) : v.man < 2 ^ f.manBits :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))

end StorageFp

namespace StorageFormat

/-- The maximum valid exponent field value for finite numbers.
    For IEEE-style formats (E5M2): all-ones exponent is fully reserved → max is 2^expBits - 2.
    For E4M3-style: all-ones exponent is partially valid → max is 2^expBits - 1.
    For no-special-value formats (E3M2, E2M1): all exponents valid → max is 2^expBits - 1. -/
def maxExpField (f : StorageFormat) : ℕ :=
  if f.hasInf then
    -- IEEE style: all-ones exponent is fully reserved for inf/NaN
    2 ^ f.expBits - 2
  else
    -- E4M3 style or no specials: all-ones exponent has valid finite values
    2 ^ f.expBits - 1

/-- The maximum mantissa field value for a finite number at the maximum exponent.
    For formats where NaN uses some patterns at all-ones exponent, this excludes those. -/
def maxManFieldAtMaxExp (f : StorageFormat) : ℕ :=
  if f.hasNaN ∧ ¬f.hasInf ∧ f.maxExpField = 2 ^ f.expBits - 1 then
    -- E4M3 style: NaN takes some patterns from all-ones exponent row
    -- For single NaN: max mantissa is 2^manBits - 2 (all ones minus 1)
    if f.nanCount = 1 then 2 ^ f.manBits - 2
    -- For multiple NaN patterns at all-ones exp: only mantissa = 0 is finite (this is unusual)
    else 0
  else
    -- Normal case: all mantissa values are valid at max exponent
    2 ^ f.manBits - 1

/-- The maximum representable finite magnitude in the format -/
noncomputable def maxFiniteMag (f : StorageFormat) {R : Type*} [Field R] : R :=
  let maxExp : ℤ := (f.maxExpField : ℤ) - (f.bias : ℤ)
  let maxMan : ℕ := 2 ^ f.manBits + f.maxManFieldAtMaxExp  -- implicit bit + mantissa
  (maxMan : R) * (2 : R) ^ (maxExp - (f.manBits : ℤ))

end StorageFormat

/-!
## Concrete Format Definitions
-/

/-- FP8 E4M3: 4-bit exponent, 3-bit mantissa, no infinity, single NaN pattern.
    Used for weights and activations in ML training/inference. -/
def E4M3 : StorageFormat where
  expBits := 4
  manBits := 3
  hasSigned := true
  bias := 7
  hasNaN := true
  nanCount := 1
  hasInf := false
  expBits_pos := by norm_num
  total_ge_two := by norm_num

/-- FP8 E5M2: 5-bit exponent, 2-bit mantissa, full IEEE 754 special values.
    Used for gradients in ML training. -/
def E5M2 : StorageFormat where
  expBits := 5
  manBits := 2
  hasSigned := true
  bias := 15
  hasNaN := true
  nanCount := 3  -- nonzero mantissa with all-ones exp: 01, 10, 11
  hasInf := true
  expBits_pos := by norm_num
  total_ge_two := by norm_num

/-- FP6 E3M2: 3-bit exponent, 2-bit mantissa, no infinity, no NaN.
    Part of MXFP6. -/
def E3M2 : StorageFormat where
  expBits := 3
  manBits := 2
  hasSigned := true
  bias := 3
  hasNaN := false
  nanCount := 0
  hasInf := false
  expBits_pos := by norm_num
  total_ge_two := by norm_num

/-- FP6 E2M3: 2-bit exponent, 3-bit mantissa, no infinity, no NaN.
    Part of MXFP6. -/
def E2M3 : StorageFormat where
  expBits := 2
  manBits := 3
  hasSigned := true
  bias := 1
  hasNaN := false
  nanCount := 0
  hasInf := false
  expBits_pos := by norm_num
  total_ge_two := by norm_num

/-- FP4 E2M1: 2-bit exponent, 1-bit mantissa, no infinity, no NaN.
    Part of MXFP4. -/
def E2M1 : StorageFormat where
  expBits := 2
  manBits := 1
  hasSigned := true
  bias := 1
  hasNaN := false
  nanCount := 0
  hasInf := false
  expBits_pos := by norm_num
  total_ge_two := by norm_num

/-- E8M0: 8-bit exponent, 0-bit mantissa, unsigned, single NaN pattern.
    Used as the shared scale factor in MX-compliant formats.
    Represents powers of 2 from 2^(-127) to 2^(127). -/
def E8M0 : StorageFormat where
  expBits := 8
  manBits := 0
  hasSigned := false
  bias := 127
  hasNaN := true
  nanCount := 1
  hasInf := false
  expBits_pos := by norm_num
  total_ge_two := by norm_num

/-!
## Basic Properties
-/

-- Bit sizes
@[simp] theorem E4M3_bitSize : E4M3.bitSize = 8 := by decide
@[simp] theorem E5M2_bitSize : E5M2.bitSize = 8 := by decide
@[simp] theorem E3M2_bitSize : E3M2.bitSize = 6 := by decide
@[simp] theorem E2M3_bitSize : E2M3.bitSize = 6 := by decide
@[simp] theorem E2M1_bitSize : E2M1.bitSize = 4 := by decide
@[simp] theorem E8M0_bitSize : E8M0.bitSize = 8 := by decide

-- Max exponent field values (verify against spec)
-- E4M3: no infinity, so all-ones exponent (15) is valid for finite values
@[simp] theorem E4M3_maxExpField : E4M3.maxExpField = 15 := by decide
-- E5M2: IEEE style, all-ones exponent (31) reserved → max is 30
@[simp] theorem E5M2_maxExpField : E5M2.maxExpField = 30 := by decide
-- E3M2: no specials, all exponents valid → max is 7
@[simp] theorem E3M2_maxExpField : E3M2.maxExpField = 7 := by decide
@[simp] theorem E2M3_maxExpField : E2M3.maxExpField = 3 := by decide
@[simp] theorem E2M1_maxExpField : E2M1.maxExpField = 3 := by decide

-- Max mantissa at max exponent (verify NaN exclusion)
-- E4M3: single NaN at 1111.111, so max mantissa at exp 15 is 110₂ = 6
@[simp] theorem E4M3_maxManFieldAtMaxExp : E4M3.maxManFieldAtMaxExp = 6 := by decide
-- E5M2: all-ones exp is fully reserved, so max exp is 30 where all mantissa values are valid
@[simp] theorem E5M2_maxManFieldAtMaxExp : E5M2.maxManFieldAtMaxExp = 3 := by decide
-- E3M2: no specials, all mantissa values valid
@[simp] theorem E3M2_maxManFieldAtMaxExp : E3M2.maxManFieldAtMaxExp = 3 := by decide

-- Verify no infinities for E4M3
@[simp] theorem E4M3_hasInf : E4M3.hasInf = false := rfl
-- Verify E5M2 has infinities
@[simp] theorem E5M2_hasInf : E5M2.hasInf = true := rfl
-- Verify no NaN for FP6/FP4
@[simp] theorem E3M2_hasNaN : E3M2.hasNaN = false := rfl
@[simp] theorem E2M3_hasNaN : E2M3.hasNaN = false := rfl
@[simp] theorem E2M1_hasNaN : E2M1.hasNaN = false := rfl
