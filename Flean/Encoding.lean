import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

import Flean.Basic

namespace Fp

-- TODO: It would be interesting to have a softfloat implementation that operates on bits
-- rather than the triples.

-- TODO: when converting NaNs to floats should we instead convert to a Quotient type over the bit representations
-- to be very explicit about there not being a strict single NaN value?

section BitSize
variable [F : FloatFormat]

def FloatFormat.signBits : ℕ := 1

def FloatFormat.significandBits : ℕ :=
  F.prec - 1

def FloatFormat.exponentRange : ℤ :=
  F.max_exp - F.min_exp + 1

def FloatFormat.exponentBits : ℕ :=
  Nat.log2 ((FloatFormat.exponentRange).toNat - 1) + 1

theorem FloatFormat.exponentRange_nonneg :
  FloatFormat.exponentRange ≥ 0 := by
  simp [FloatFormat.exponentRange]
  have h := F.valid_exp
  linarith


def FloatFormat.bitSize : ℕ :=
  if F.radix = Radix.Binary then
    -- 1 for the sign bit, F.prec - 1 for the significand, and F.prec for the exponent
    -- we can skip 1 bit because we don't need to represent the leading 1/0 in the significand
    FloatFormat.signBits + FloatFormat.significandBits + FloatFormat.exponentBits
  else
    -- TODO: How do you compute this for the decimal format, or other cases?
    -- Should we have this be in the units that the radix is defined in, instead of general bits?
    0

end BitSize

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

-- def toTriple (f : Fp) : Bool × ℤ × ℤ := by
--   if F.radix = Radix.Binary then
--     match f with
--     | .finite f =>
--       return (f.s, f.m, f.e)
--     | .infinite b =>
--       return (if b then 1 else -1, 0, 0)
--     | .nan =>
--       return (0, 0, 0)
--   else
--     return (0, 0, 0)

-- TODO: We should hopefully be able to use the bitvec representation with the solver integrated into lean, but I need to look into that more.
def toBits (f : Fp) : BitVec F.bitSize := by
  if F.radix == Radix.Binary then
    match f with
    | .finite f =>
      sorry
    | .infinite b =>
      sorry
    | .nan =>
      sorry
  else
    return BitVec.empty

end Fp
