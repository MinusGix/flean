import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

@[ext]
structure Radix where
  val : ℤ
  valid : val ≥ 2
deriving Repr, DecidableEq
namespace Radix

instance : LawfulBEq Radix where
  eq_of_beq {a b} h := by
    induction' a with a; induction' b with b
    simp only [beq_iff_eq, mk.injEq] at h
    rename_i valid valid_i
    simp_all only [mk.injEq]
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
  radix : Radix
  prec : ℕ
  min_exp : ℤ
  max_exp : ℤ
  valid_prec : prec ≥ 2
  valid_exp : min_exp < max_exp
namespace FloatFormat

def Binary16 : FloatFormat := {
  radix := Radix.Binary,
  prec := 11,
  min_exp := -14,
  max_exp := 15,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

/-- Commonly known as 'float' or 'single-precision' -/
def Binary32 : FloatFormat := {
  radix := Radix.Binary,
  prec := 24,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

/-- Commonly known as 'double' or 'double-precision' -/
def Binary64 : FloatFormat := {
  radix := Radix.Binary,
  prec := 53,
  min_exp := -1022,
  max_exp := 1023,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

def Binary128 : FloatFormat := {
  radix := Radix.Binary,
  prec := 113,
  min_exp := -16382,
  max_exp := 16383,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

-- TODO: 80-bit floating point formats

/-- BFloat16 format. Has a lower precision but a higher exponent, which gives it a higher range for less precision. -/
def BF16 : FloatFormat := {
  radix := Radix.Binary,
  prec := 8,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

/-- NVIDIA's Tensor Float 32 Format. This uses the same half-precision of FP16, while having the exponent of FP32.
This is termed '32' though it really only uses 19 bits, but in practice it is stored using 32-bits.  -/
def TF32 : FloatFormat := {
  radix := Radix.Binary,
  prec := 11,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

def Decimal32 : FloatFormat := {
  radix := Radix.Decimal,
  prec := 7,
  min_exp := -95,
  max_exp := 96,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

def Decimal64 : FloatFormat := {
  radix := Radix.Decimal,
  prec := 16,
  min_exp := -383,
  max_exp := 384,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

def Decimal128 : FloatFormat := {
  radix := Radix.Decimal,
  prec := 34,
  min_exp := -6143,
  max_exp := 6144,
  valid_prec := by norm_num,
  valid_exp := by norm_num
}

def isStandardExpRange (F : FloatFormat) : Prop :=
  F.min_exp = 1 - F.max_exp

end FloatFormat
