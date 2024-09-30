import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LiftLets

import Flean.Basic
import Flean.BitVecUtil

namespace Fp

section BitSize


@[reducible]
def FloatFormat.signBits : ℕ := 1

@[reducible]
def FloatFormat.significandBits [FloatFormat] : ℕ :=
  FloatFormat.prec - 1

theorem FloatFormat.significandBits_ge_one [FloatFormat] :
  FloatFormat.significandBits ≥ 1 := by
  unfold FloatFormat.significandBits
  have := FloatFormat.valid_prec
  omega

theorem FloatFormat.significandBits_pos [FloatFormat] :
  FloatFormat.significandBits > 0 := by
  have := FloatFormat.significandBits_ge_one
  omega

@[reducible]
def FloatFormat.exponentRange [FloatFormat] : ℤ :=
  FloatFormat.max_exp - FloatFormat.min_exp + 1

@[reducible]
def FloatFormat.exponentBits [FloatFormat] : ℕ :=
  Nat.log2 ((FloatFormat.exponentRange).toNat - 1) + 1

@[simp]
theorem FloatFormat.exponentRange_nonneg [FloatFormat] :
  FloatFormat.exponentRange ≥ 0 := by
  simp only [exponentRange, ge_iff_le]
  have h := FloatFormat.valid_exp
  omega

@[simp]
theorem FloatFormat.exponentBits_pos [FloatFormat] :
  FloatFormat.exponentBits > 0 := by
  unfold FloatFormat.exponentBits
  have := FloatFormat.valid_exp
  omega

@[reducible]
def FloatFormat.bitSize [FloatFormat] : ℕ :=
  -- 1 for the sign bit, F.prec - 1 for the significand, and F.prec for the exponent
  -- we can skip 1 bit because we don't need to represent the leading 1/0 in the significand
  FloatFormat.signBits + FloatFormat.exponentBits + FloatFormat.significandBits

def FloatFormat.bitSize_eq [FloatFormat] : FloatFormat.bitSize = FloatFormat.signBits + FloatFormat.exponentBits + FloatFormat.significandBits := rfl

/-- Added to the exponent to make the biased exponent, a non-negative number -/
@[reducible]
def FloatFormat.exponentBias [FloatFormat] : ℤ :=
  FloatFormat.max_exp

-- TODO: any ways to weaken this for non-standard exp values?
theorem FloatFormat.exponentBias_add_standard_pos [FloatFormat] (e : ℤ) (e_range : FloatFormat.min_exp ≤ e ∧ e ≤ FloatFormat.max_exp) (standard : FloatFormat.isStandardExpRange) :
  e + FloatFormat.exponentBias > 0 := by
  unfold FloatFormat.exponentBias
  unfold FloatFormat.isStandardExpRange at standard
  omega

theorem FloatFormat.exponentBias_add_standard_nonneg [FloatFormat] (e : ℤ) (e_range : FloatFormat.min_exp ≤ e ∧ e ≤ FloatFormat.max_exp) (standard : FloatFormat.isStandardExpRange) :
  e + FloatFormat.exponentBias ≥ 0 := by
  unfold FloatFormat.exponentBias
  unfold FloatFormat.isStandardExpRange at standard
  omega

/-- The biased exponent as a nat is equivalent to the biased exponent as an int -/
theorem FloatFormat.exponentBias_add_standard_toNat [FloatFormat] (e : ℤ) (e_range : FloatFormat.min_exp ≤ e ∧ e ≤ FloatFormat.max_exp) (standard : FloatFormat.isStandardExpRange) :
  ↑(e + FloatFormat.exponentBias).toNat = e + FloatFormat.exponentBias := by
  apply Int.toNat_of_nonneg
  exact FloatFormat.exponentBias_add_standard_nonneg e e_range standard

-- TODO: RFL can solve these, but the speed is very slow.
theorem FloatFormat.Binary16.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary16 = 16 := by
  native_decide

theorem FloatFormat.Binary32.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary32 = 32 := by
  native_decide

theorem FloatFormat.Binary64.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary64 = 64 := by
  native_decide

theorem FloatFormat.Binary128.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary128 = 128 := by
  native_decide

theorem FloatFormat.BF16.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.BF16 = 16 := by
  native_decide

theorem FloatFormat.TF32.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.TF32 = 19 := by
  native_decide

end BitSize

end Fp
