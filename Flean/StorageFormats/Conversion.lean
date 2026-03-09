import Flean.StorageFormats.Defs
import Flean.Defs
import Flean.ToVal

/-!
# Storage Format Conversions

Conversion between `StorageFp` (storage-only formats like E4M3) and `FiniteFp`
(IEEE arithmetic formats).

The key operations are:
- `StorageFp.toFiniteFp`: decode a storage float into a `FiniteFp` (if finite)
- `FiniteFp.toStorageFp`: encode a `FiniteFp` into a storage format with saturation

These are the only entry/exit points between storage and arithmetic domains.
-/

/-!
## StorageFp → FiniteFp

A finite `StorageFp` can be decoded into a `FiniteFp` when the target `FloatFormat`
is wide enough to represent all finite values of the storage format.

The natural `FloatFormat` for a `StorageFormat` has:
- `prec = manBits + 1` (mantissa bits + implicit bit)
- `min_exp = 1 - bias` (subnormal exponent)
- `max_exp = maxExpField - bias` (largest normal exponent)
-/

/-- A `FloatFormat` that exactly matches a `StorageFormat`'s representable range.
    Requires manBits ≥ 1 (so prec ≥ 2), bias ≥ 1 (so min_exp ≤ 0),
    and maxExpField > bias (so max_exp > 0). -/
def StorageFormat.toFloatFormat (f : StorageFormat)
    (h_prec : f.manBits ≥ 1)
    (h_bias : f.bias ≥ 1)
    (h_exp : f.maxExpField > f.bias) : FloatFormat where
  prec := (f.manBits : ℤ) + 1
  min_exp := 1 - (f.bias : ℤ)
  max_exp := (f.maxExpField : ℤ) - (f.bias : ℤ)
  valid_prec := by omega
  exp_order := by omega
  max_exp_pos := by omega
  min_exp_nonpos := by omega

/-!
## Concrete FloatFormat instances for each storage format
-/

/-- The `FloatFormat` matching E4M3's representable range.
    prec = 4, min_exp = -6, max_exp = 8. -/
def FloatFormat.ofE4M3 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E4M3 (by decide) (by decide) (by decide)

/-- The `FloatFormat` matching E5M2's representable range.
    prec = 3, min_exp = -14, max_exp = 15. -/
def FloatFormat.ofE5M2 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E5M2 (by decide) (by decide) (by decide)

/-- The `FloatFormat` matching E3M2's representable range.
    prec = 3, min_exp = -2, max_exp = 4. -/
def FloatFormat.ofE3M2 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E3M2 (by decide) (by decide) (by decide)

/-- The `FloatFormat` matching E2M3's representable range.
    prec = 4, min_exp = 0, max_exp = 2. -/
def FloatFormat.ofE2M3 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E2M3 (by decide) (by decide) (by decide)

-- Verify concrete parameters
theorem FloatFormat.ofE4M3_prec : FloatFormat.ofE4M3.prec = 4 := by decide
theorem FloatFormat.ofE4M3_min_exp : FloatFormat.ofE4M3.min_exp = -6 := by decide
theorem FloatFormat.ofE4M3_max_exp : FloatFormat.ofE4M3.max_exp = 8 := by decide

theorem FloatFormat.ofE5M2_prec : FloatFormat.ofE5M2.prec = 3 := by decide
theorem FloatFormat.ofE5M2_min_exp : FloatFormat.ofE5M2.min_exp = -14 := by decide
theorem FloatFormat.ofE5M2_max_exp : FloatFormat.ofE5M2.max_exp = 15 := by decide

theorem FloatFormat.ofE3M2_prec : FloatFormat.ofE3M2.prec = 3 := by decide
theorem FloatFormat.ofE3M2_min_exp : FloatFormat.ofE3M2.min_exp = -2 := by decide
theorem FloatFormat.ofE3M2_max_exp : FloatFormat.ofE3M2.max_exp = 4 := by decide

theorem FloatFormat.ofE2M3_prec : FloatFormat.ofE2M3.prec = 4 := by decide
theorem FloatFormat.ofE2M3_min_exp : FloatFormat.ofE2M3.min_exp = 0 := by decide
theorem FloatFormat.ofE2M3_max_exp : FloatFormat.ofE2M3.max_exp = 2 := by decide

/-!
## Concrete zero and common values for StorageFp
-/

namespace StorageFp

variable {f : StorageFormat}

/-- The positive zero encoding: all bits zero -/
def zero (f : StorageFormat) : StorageFp f :=
  ⟨0⟩

/-- The negative zero encoding (for signed formats): sign bit set, rest zero -/
def negZero (f : StorageFormat) : StorageFp f :=
  ⟨BitVec.ofNat f.bitSize (2 ^ (f.bitSize - 1))⟩

theorem zero_exp (f : StorageFormat) : (zero f).exp = 0 := by
  unfold zero exp
  simp [StorageFormat.bitSize]

theorem zero_man (f : StorageFormat) : (zero f).man = 0 := by
  unfold zero man
  simp [StorageFormat.bitSize]

theorem zero_sign (f : StorageFormat) : (zero f).sign = false := by
  unfold zero sign
  simp [StorageFormat.bitSize]

theorem zero_isExpZero (f : StorageFormat) : (zero f).isExpZero :=
  zero_exp f

theorem zero_isZero (f : StorageFormat) : (zero f).isZero :=
  ⟨zero_exp f, zero_man f⟩

private theorem zero_ne_all_ones (f : StorageFormat) : ¬(zero f).isExpAllOnes := by
  unfold isExpAllOnes
  rw [zero_exp]
  have : 1 < 2 ^ f.expBits := Nat.one_lt_pow f.expBits_pos.ne' (by norm_num)
  omega

theorem zero_isFinite (f : StorageFormat) : (zero f).isFinite :=
  ⟨fun ⟨_, h, _⟩ => absurd h (zero_ne_all_ones f),
   fun ⟨_, h, _⟩ => absurd h (zero_ne_all_ones f)⟩

/-- Zero has toVal = 0 -/
theorem zero_toVal (f : StorageFormat) {R : Type*} [Field R] :
    (zero f).toVal = (0 : R) := by
  simp only [toVal, signVal, effectiveSignificand, unbiasedExp,
    zero_sign, zero_man, zero_isExpZero, ↓reduceIte, Nat.cast_zero, mul_zero, zero_mul]

end StorageFp
