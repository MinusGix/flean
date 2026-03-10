import Flean.StorageFormats.Defs
import Flean.Defs
import Flean.ToVal

/-!
# Storage Format Conversions

Conversion between `StorageFp` (storage-only formats like E4M3) and `FiniteFp`
(IEEE arithmetic formats).

The conversion targets the *matching* `FloatFormat` (via `StorageFormat.toFloatFormat`)
where the exponent/significand fields map directly. To use the result in a wider
format (e.g. FP16, FP32), apply a separate widening operation on `FiniteFp`.
-/

/-!
## StorageFormat → FloatFormat
-/

/-- A `FloatFormat` that exactly matches a `StorageFormat`'s representable range. -/
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

/-- Predicate: a `FloatFormat` can represent all finite values of a `StorageFormat`. -/
structure StorageFormat.FitsIn (sf : StorageFormat) (ff : FloatFormat) : Prop where
  prec_ge : ff.prec ≥ (sf.manBits : ℤ) + 1
  min_exp_le : ff.min_exp ≤ 1 - (sf.bias : ℤ)
  max_exp_ge : ff.max_exp ≥ (sf.maxExpField : ℤ) - (sf.bias : ℤ)

/-!
## Concrete FloatFormat instances
-/

def FloatFormat.ofE4M3 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E4M3 (by decide) (by decide) (by decide)

def FloatFormat.ofE5M2 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E5M2 (by decide) (by decide) (by decide)

def FloatFormat.ofE3M2 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E3M2 (by decide) (by decide) (by decide)

def FloatFormat.ofE2M3 : FloatFormat :=
  StorageFormat.toFloatFormat _root_.E2M3 (by decide) (by decide) (by decide)

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

-- FitsIn instances
theorem E4M3_fitsIn_Binary16 : E4M3.FitsIn FloatFormat.Binary16.toFloatFormat :=
  ⟨by decide, by decide, by decide⟩

theorem E5M2_fitsIn_Binary16 : E5M2.FitsIn FloatFormat.Binary16.toFloatFormat :=
  ⟨by decide, by decide, by decide⟩

/-!
## StorageFp → FiniteFp (exact matching format)
-/

namespace StorageFp

variable {f : StorageFormat}

/-- For a finite StorageFp, the exponent field is at most maxExpField.
    This uses integer arithmetic to avoid nat subtraction issues. -/
theorem exp_le_maxExpField_of_isFinite (v : StorageFp f)
    (hfin : v.isFinite) : (v.exp : ℤ) ≤ f.maxExpField := by
  have hexp_lt := v.exp_lt
  unfold StorageFormat.maxExpField
  split
  · -- hasInf = true: maxExpField = 2^expBits - 2
    rename_i hinf
    -- v.exp ≤ 2^expBits - 1 from exp_lt
    have hle : v.exp ≤ 2 ^ f.expBits - 1 := Nat.le_sub_one_of_lt hexp_lt
    -- If v.exp ≤ 2^expBits - 2, we're done. Otherwise v.exp = 2^expBits - 1 (all-ones).
    by_cases h : v.exp ≤ 2 ^ f.expBits - 2
    · exact_mod_cast h
    · -- v.exp = 2^expBits - 1, contradicts isFinite
      push_neg at h
      have heq : v.exp = 2 ^ f.expBits - 1 := by omega
      have hallones : v.isExpAllOnes := heq
      obtain ⟨hnan, hnc⟩ := f.inf_implies_nan hinf
      cases eq_or_ne v.man 0 with
      | inl h0 => exact absurd ⟨hinf, hallones, h0⟩ hfin.2
      | inr hne =>
        have : v.isNaN := by
          refine ⟨hnan, hallones, ?_⟩
          simp only [show f.nanCount ≠ 1 by omega, ↓reduceIte, show 0 < f.nanCount by omega]
          exact hne
        exact absurd this hfin.1
  · -- hasInf = false: maxExpField = 2^expBits - 1
    have h1le : 1 ≤ 2 ^ f.expBits := Nat.one_le_pow _ _ (by norm_num)
    have : v.exp ≤ 2 ^ f.expBits - 1 := Nat.le_sub_one_of_lt hexp_lt
    exact_mod_cast this

/-- Convert a finite `StorageFp` to a `FiniteFp` in the matching `FloatFormat`. -/
def toFiniteFp (v : StorageFp f)
    (h_prec : f.manBits ≥ 1) (h_bias : f.bias ≥ 1) (h_exp : f.maxExpField > f.bias)
    (hfin : v.isFinite) :
    @FiniteFp (f.toFloatFormat h_prec h_bias h_exp) := by
  letI ff := f.toFloatFormat h_prec h_bias h_exp
  have ff_prec_eq : ff.prec = (f.manBits : ℤ) + 1 := rfl
  have ff_min_exp_eq : ff.min_exp = 1 - (f.bias : ℤ) := rfl
  have ff_max_exp_eq : ff.max_exp = (f.maxExpField : ℤ) - (f.bias : ℤ) := rfl
  have ff_prec_nat : ff.prec.toNat = f.manBits + 1 := by omega
  have ff_prec_sub_one_nat : (ff.prec - 1).toNat = f.manBits := by omega
  refine ⟨v.sign, v.unbiasedExp, v.effectiveSignificand, ?_⟩
  simp only [IsValidFiniteVal, _root_.isNormal, _root_.isSubnormal,
    ff_prec_nat, ff_prec_sub_one_nat]
  show v.unbiasedExp ≥ 1 - (f.bias : ℤ) ∧
    v.unbiasedExp ≤ (f.maxExpField : ℤ) - (f.bias : ℤ) ∧
    v.effectiveSignificand < 2 ^ (f.manBits + 1) ∧
    (2 ^ f.manBits ≤ v.effectiveSignificand ∧ v.effectiveSignificand < 2 ^ (f.manBits + 1) ∨
     v.unbiasedExp = 1 - (f.bias : ℤ) ∧ v.effectiveSignificand ≤ 2 ^ f.manBits - 1)
  have hman := v.man_lt
  by_cases hexp : v.isExpZero
  · -- Subnormal
    have he : v.unbiasedExp = 1 - (f.bias : ℤ) := by simp [unbiasedExp, hexp]
    have hm : v.effectiveSignificand = v.man := by simp [effectiveSignificand, hexp]
    rw [he, hm]
    exact ⟨le_refl _, by omega, by omega, Or.inr ⟨rfl, by omega⟩⟩
  · -- Normal
    have hexp_le := v.exp_le_maxExpField_of_isFinite hfin
    have hexp_pos : 0 < v.exp := by unfold isExpZero at hexp; omega
    have he : v.unbiasedExp = (v.exp : ℤ) - (f.bias : ℤ) := by simp [unbiasedExp, hexp]
    have hm : v.effectiveSignificand = 2 ^ f.manBits + v.man := by
      simp [effectiveSignificand, hexp]
    rw [he, hm]
    have hm_lt : 2 ^ f.manBits + v.man < 2 ^ (f.manBits + 1) := by
      calc 2 ^ f.manBits + v.man
          < 2 ^ f.manBits + 2 ^ f.manBits := by omega
        _ = 2 ^ (f.manBits + 1) := by ring
    exact ⟨by omega, by linarith, hm_lt, Or.inl ⟨Nat.le_add_right _ _, hm_lt⟩⟩

/-- The conversion to `FiniteFp` preserves the mathematical value. -/
theorem toFiniteFp_toVal (v : StorageFp f)
    (h_prec : f.manBits ≥ 1) (h_bias : f.bias ≥ 1) (h_exp : f.maxExpField > f.bias)
    (hfin : v.isFinite) {R : Type*} [Field R] :
    @FiniteFp.toVal (f.toFloatFormat h_prec h_bias h_exp) R _
      (v.toFiniteFp h_prec h_bias h_exp hfin) = v.toVal := by
  letI : FloatFormat := f.toFloatFormat h_prec h_bias h_exp
  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two]
  -- The fields of the constructed FiniteFp match StorageFp's components
  have hs : (v.toFiniteFp h_prec h_bias h_exp hfin).s = v.sign := rfl
  have he : (v.toFiniteFp h_prec h_bias h_exp hfin).e = v.unbiasedExp := rfl
  have hm : (v.toFiniteFp h_prec h_bias h_exp hfin).m = v.effectiveSignificand := rfl
  rw [hs, he, hm]
  unfold toVal signVal
  -- Both sides: (if sign then -1 else 1) * ↑effectiveSignificand * 2^(exp_term)
  -- LHS exp: unbiasedExp - (manBits + 1) + 1, RHS exp: unbiasedExp - manBits
  have hprec : FloatFormat.prec = (f.manBits : ℤ) + 1 := rfl
  rw [hprec]
  push_cast
  ring_nf

/-!
## Concrete zero and common values
-/

/-- Construct a `StorageFp` from sign, exponent field, and mantissa field values.
    The bit layout is `[sign][exponent][mantissa]` from MSB to LSB. -/
def ofFields (f : StorageFormat) (s : Bool) (e : ℕ) (m : ℕ) : StorageFp f :=
  ⟨BitVec.ofNat f.bitSize
    ((if s ∧ f.hasSigned then 1 else 0) * 2 ^ (f.expBits + f.manBits) +
     e * 2 ^ f.manBits + m)⟩

/-- The positive zero encoding: all bits zero -/
def zero (f : StorageFormat) : StorageFp f :=
  ⟨0⟩

/-- The negative zero encoding (for signed formats): sign bit set, rest zero -/
def negZero (f : StorageFormat) : StorageFp f :=
  ⟨BitVec.ofNat f.bitSize (2 ^ (f.bitSize - 1))⟩

/-- The encoding of 1.0: sign=0, exponent=bias, mantissa=0. -/
def one (f : StorageFormat) : StorageFp f := ofFields f false f.bias 0

/-- The largest finite positive value. -/
def maxFinite (f : StorageFormat) : StorageFp f :=
  ofFields f false f.maxExpField f.maxManFieldAtMaxExp

/-- The smallest positive value (smallest subnormal). -/
def minPos (f : StorageFormat) : StorageFp f := ofFields f false 0 1

theorem zero_exp (f : StorageFormat) : (zero f).exp = 0 := by
  unfold zero exp; simp [StorageFormat.bitSize]

theorem zero_man (f : StorageFormat) : (zero f).man = 0 := by
  unfold zero man; simp [StorageFormat.bitSize]

theorem zero_sign (f : StorageFormat) : (zero f).sign = false := by
  unfold zero sign; simp [StorageFormat.bitSize]

theorem zero_isExpZero (f : StorageFormat) : (zero f).isExpZero :=
  zero_exp f

theorem zero_isZero (f : StorageFormat) : (zero f).isZero :=
  ⟨zero_exp f, zero_man f⟩

private theorem zero_ne_all_ones (f : StorageFormat) : ¬(zero f).isExpAllOnes := by
  unfold isExpAllOnes; rw [zero_exp]
  have : 1 < 2 ^ f.expBits := Nat.one_lt_pow f.expBits_pos.ne' (by norm_num)
  omega

theorem zero_isFinite (f : StorageFormat) : (zero f).isFinite :=
  ⟨fun ⟨_, h, _⟩ => absurd h (zero_ne_all_ones f),
   fun ⟨_, h, _⟩ => absurd h (zero_ne_all_ones f)⟩

theorem zero_toVal (f : StorageFormat) {R : Type*} [Field R] :
    (zero f).toVal = (0 : R) := by
  simp only [toVal, signVal, effectiveSignificand, unbiasedExp,
    zero_sign, zero_man, zero_isExpZero, ↓reduceIte, Nat.cast_zero, mul_zero, zero_mul]

/-!
### Field extraction for concrete values
-/

-- one (E4M3): exp=7 (bias), man=0, sign=false → toVal = 1
@[simp] theorem one_exp_E4M3 : (one E4M3).exp = 7 := by decide
@[simp] theorem one_man_E4M3 : (one E4M3).man = 0 := by decide
@[simp] theorem one_sign_E4M3 : (one E4M3).sign = false := by decide

-- one (E5M2): exp=15 (bias), man=0, sign=false → toVal = 1
@[simp] theorem one_exp_E5M2 : (one E5M2).exp = 15 := by decide
@[simp] theorem one_man_E5M2 : (one E5M2).man = 0 := by decide
@[simp] theorem one_sign_E5M2 : (one E5M2).sign = false := by decide

-- maxFinite (E4M3): exp=15, man=6, sign=false → toVal = 448
@[simp] theorem maxFinite_exp_E4M3 : (maxFinite E4M3).exp = 15 := by decide
@[simp] theorem maxFinite_man_E4M3 : (maxFinite E4M3).man = 6 := by decide
@[simp] theorem maxFinite_sign_E4M3 : (maxFinite E4M3).sign = false := by decide

-- maxFinite (E5M2): exp=30, man=3, sign=false → toVal = 57344
@[simp] theorem maxFinite_exp_E5M2 : (maxFinite E5M2).exp = 30 := by decide
@[simp] theorem maxFinite_man_E5M2 : (maxFinite E5M2).man = 3 := by decide
@[simp] theorem maxFinite_sign_E5M2 : (maxFinite E5M2).sign = false := by decide

-- minPos (E4M3): exp=0, man=1, sign=false
@[simp] theorem minPos_exp_E4M3 : (minPos E4M3).exp = 0 := by decide
@[simp] theorem minPos_man_E4M3 : (minPos E4M3).man = 1 := by decide
@[simp] theorem minPos_sign_E4M3 : (minPos E4M3).sign = false := by decide

-- minPos (E5M2): exp=0, man=1, sign=false
@[simp] theorem minPos_exp_E5M2 : (minPos E5M2).exp = 0 := by decide
@[simp] theorem minPos_man_E5M2 : (minPos E5M2).man = 1 := by decide
@[simp] theorem minPos_sign_E5M2 : (minPos E5M2).sign = false := by decide

/-!
### Finiteness of concrete values
-/

theorem one_isFinite_E4M3 : (one E4M3).isFinite := by decide
theorem one_isFinite_E5M2 : (one E5M2).isFinite := by decide
theorem maxFinite_isFinite_E4M3 : (maxFinite E4M3).isFinite := by decide
theorem maxFinite_isFinite_E5M2 : (maxFinite E5M2).isFinite := by decide
theorem minPos_isFinite_E4M3 : (minPos E4M3).isFinite := by decide
theorem minPos_isFinite_E5M2 : (minPos E5M2).isFinite := by decide

/-!
### toVal for concrete values
-/

theorem one_toVal_E4M3 {R : Type*} [Field R] [NeZero (2 : R)] :
    (one E4M3).toVal = (1 : R) := by
  simp only [toVal, signVal, effectiveSignificand, unbiasedExp, isExpZero,
    one_sign_E4M3, one_exp_E4M3, one_man_E4M3, ↓reduceIte]
  simp only [E4M3]; push_cast; simp only [one_mul, Nat.add_zero]
  -- Goal: 8 * 2^(-3) = 1
  rw [show (8 : R) = 2 ^ 3 from by norm_num]; rw [show (-3 : ℤ) = -(3 : ℤ) from by norm_num]
  rw [← zpow_natCast (2 : R) 3, ← zpow_add₀ (two_ne_zero' R)]; simp

theorem one_toVal_E5M2 {R : Type*} [Field R] [NeZero (2 : R)] :
    (one E5M2).toVal = (1 : R) := by
  simp only [toVal, signVal, effectiveSignificand, unbiasedExp, isExpZero,
    one_sign_E5M2, one_exp_E5M2, one_man_E5M2, ↓reduceIte]
  simp only [E5M2]; push_cast; simp only [one_mul, Nat.add_zero]
  -- Goal: 4 * 2^(-2) = 1
  rw [show (4 : R) = 2 ^ 2 from by norm_num]; rw [show (-2 : ℤ) = -(2 : ℤ) from by norm_num]
  rw [← zpow_natCast (2 : R) 2, ← zpow_add₀ (two_ne_zero' R)]; simp

theorem maxFinite_toVal_E4M3 {R : Type*} [Field R] [NeZero (2 : R)] :
    (maxFinite E4M3).toVal = (448 : R) := by
  simp only [toVal, signVal, effectiveSignificand, unbiasedExp, isExpZero,
    maxFinite_sign_E4M3, maxFinite_exp_E4M3, maxFinite_man_E4M3, ↓reduceIte]
  simp only [E4M3, StorageFormat.maxExpField, StorageFormat.maxManFieldAtMaxExp]
  push_cast; norm_num [zpow_natCast]

theorem minPos_toVal_E4M3 {R : Type*} [Field R] :
    (minPos E4M3).toVal = (2 : R)⁻¹ ^ 9 := by
  simp only [toVal, signVal, effectiveSignificand, unbiasedExp, isExpZero,
    minPos_sign_E4M3, minPos_exp_E4M3, minPos_man_E4M3, ↓reduceIte]
  simp only [E4M3]; push_cast; simp only [one_mul]
  -- Goal: 2^(-9) = 2⁻¹ ^ 9
  rw [show (-9 : ℤ) = Int.negSucc 8 from rfl, zpow_negSucc, ← inv_pow]

end StorageFp
