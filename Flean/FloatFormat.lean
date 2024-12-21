import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

@[ext]
structure Radix where
  val : ℤ
  valid : val ≥ 2
deriving Repr, DecidableEq
namespace Radix

instance : LawfulBEq Radix where
  eq_of_beq {a b} h := by
    rw [beq_iff_eq] at h
    exact h
  rfl {a} := by simp only [beq_self_eq_true]

-- TODO: linear order on Radix

def Binary : Radix := ⟨2, by norm_num⟩
def Decimal : Radix := ⟨10, by norm_num⟩

variable {β : Radix}

@[simp]
theorem gt_zero : β.val > 0 := by
  have h := β.valid
  omega

@[simp]
theorem gt_one : β.val > 1 := by
  have h := β.valid
  omega

@[simp]
theorem zero_lt : 0 < β.val := by
  have h := β.valid
  omega

@[simp]
theorem one_lt : 1 < β.val := by
  have h := β.valid
  omega

@[simp]
theorem ne_zero : β.val ≠ 0 := by
  have h := β.valid
  omega

@[simp]
theorem two_le : 2 ≤ β.val := by
  have h := β.valid
  omega

end Radix

class FloatFormat where
  -- radix : Radix
  prec : ℕ
  min_exp : ℤ
  max_exp : ℤ
  valid_prec : prec ≥ 2
  exp_order : min_exp < max_exp
  max_exp_pos : 0 < max_exp
  min_exp_nonpos : min_exp ≤ 0

attribute [simp] FloatFormat.valid_prec
attribute [simp] FloatFormat.exp_order
attribute [simp] FloatFormat.max_exp_pos
attribute [simp] FloatFormat.min_exp_nonpos

namespace FloatFormat

def isStandardExpRange [FloatFormat] : Prop :=
  FloatFormat.min_exp = 1 - FloatFormat.max_exp

end FloatFormat

-- TODO(minor): Should we split the emax pow requirement the is standard exp range?
class StdFloatFormat extends FloatFormat where
  -- emax is of the form 2^n - 1
  exp_pow : ℕ
  -- We could make this > 1 without really losing anything
  exp_pow_pos : exp_pow > 0
  max_exp_pow : max_exp = 2 ^ exp_pow - 1
  st : FloatFormat.isStandardExpRange

attribute [simp] StdFloatFormat.exp_pow_pos
attribute [simp] StdFloatFormat.max_exp_pow
attribute [simp] StdFloatFormat.st

namespace FloatFormat

def radix [FloatFormat] : Radix := Radix.Binary

def Binary16 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 11,
  min_exp := -14,
  max_exp := 15,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 4
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

/-- Commonly known as 'float' or 'single-precision' -/
def Binary32 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 24,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 7
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

/-- Commonly known as 'double' or 'double-precision' -/
def Binary64 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 53,
  min_exp := -1022,
  max_exp := 1023,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 10
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

def Binary128 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 113,
  min_exp := -16382,
  max_exp := 16383,
  valid_prec := by norm_num,
  exp_order := by norm_num
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 14
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

-- TODO: 80-bit floating point formats

/-- BFloat16 format. Has a lower precision but a higher exponent, which gives it a higher range for less precision. -/
def BF16 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 8,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 7
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

/-- NVIDIA's Tensor Float 32 Format. This uses the same half-precision of FP16, while having the exponent of FP32.
This is termed '32' though it really only uses 19 bits, but in practice it is stored using 32-bits.  -/
def TF32 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 11,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 7
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

-- TODO: is there a way to just put @ simp on fields?

-- Unfortunately simp doesn't seem to understand it can turn < into ≤?? so I have to have this def
@[simp]
theorem exp_order_le [FloatFormat] : min_exp ≤ max_exp := FloatFormat.exp_order.le

@[simp]
theorem prec_pow_le [FloatFormat] : 4 ≤ 2^FloatFormat.prec := by
  rw [show 4 = 2^2 by norm_num]
  apply pow_le_pow_right₀ (by norm_num) FloatFormat.valid_prec

theorem prec_pred_pow_le [FloatFormat] : 2 ≤ 2^(FloatFormat.prec - 1) := by
  rw [show 2 = 2^1 by norm_num]
  have := FloatFormat.valid_prec
  apply pow_le_pow_right₀ (by norm_num) (by omega)

-- def Decimal32 : FloatFormat := {
--   radix := Radix.Decimal,
--   prec := 7,
--   min_exp := -95,
--   max_exp := 96,
--   valid_prec := by norm_num,
--   valid_exp := by norm_num
-- }

-- def Decimal64 : FloatFormat := {
--   radix := Radix.Decimal,
--   prec := 16,
--   min_exp := -383,
--   max_exp := 384,
--   valid_prec := by norm_num,
--   valid_exp := by norm_num
-- }

-- def Decimal128 : FloatFormat := {
--   radix := Radix.Decimal,
--   prec := 34,
--   min_exp := -6143,
--   max_exp := 6144,
--   valid_prec := by norm_num,
--   valid_exp := by norm_num
-- }

theorem standardExpRange_pos [FloatFormat] (standard : FloatFormat.isStandardExpRange) : 0 < FloatFormat.max_exp - FloatFormat.min_exp := by
  have := FloatFormat.exp_order
  rw [standard] at this ⊢
  omega

-- theorem binary16_standard_exp_range : Binary16.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary16, min_exp, max_exp]
--   norm_num

-- theorem binary32_standard_exp_range : Binary32.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary32, min_exp, max_exp]
--   norm_num

-- theorem binary64_standard_exp_range : Binary64.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary64, min_exp, max_exp]
--   norm_num

-- theorem binary128_standard_exp_range : Binary128.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary128, min_exp, max_exp]
--   norm_num

-- theorem bf16_standard_exp_range : BF16.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [BF16, min_exp, max_exp]
--   norm_num

-- theorem tf32_standard_exp_range : TF32.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [TF32, min_exp, max_exp]
--   norm_num

-- theorem decimal32_standard_exp_range : Decimal32.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Decimal32, min_exp, max_exp]
--   norm_num

-- theorem decimal64_standard_exp_range : Decimal64.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Decimal64, min_exp, max_exp]
--   norm_num

-- theorem decimal128_standard_exp_range : Decimal128.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Decimal128, min_exp, max_exp]
--   norm_num

end FloatFormat

namespace StdFloatFormat

@[simp]
def max_exp_def [StdFloatFormat] : FloatFormat.max_exp = 2 ^ StdFloatFormat.exp_pow - 1 := StdFloatFormat.max_exp_pow

@[simp]
def std_exp_range_def [StdFloatFormat] : FloatFormat.min_exp = 1 - FloatFormat.max_exp := StdFloatFormat.st

end StdFloatFormat
