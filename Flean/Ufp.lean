import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LiftLets
import Mathlib.Tactic.Rify
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Flean.Basic
import Flean.BitVecUtil
import Flean.Ulp

namespace Fp

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

/-- Unit in the First Place. `2^floor(log2(|x|))`. -/
def ufp (x : R) : R := if x = 0 then 0 else 2^(Int.log 2 (|x|))

theorem ufp_nonneg (x : R) : 0 ≤ ufp x := by
  delta ufp
  split_ifs
  · trivial
  · apply zpow_nonneg
    norm_num

@[simp]
theorem ufp_zero : ufp (0 : R) = 0 := by simp [ufp]

-- TODO(minor): better name
theorem ufp_ulp_eq [FloatFormat] (x : R) (xnz : x ≠ 0) (xge : 2^FloatFormat.min_exp ≤ |x|) : ufp x = 2^(FloatFormat.prec - 1) * ulp x := by
  delta ufp ulp
  -- delta ufp
  have hz : (2 : R)^(FloatFormat.prec - 1) = (2 : R)^((FloatFormat.prec : ℤ) - 1) := by
    conv => rhs; rw [← Nat.cast_one]
    rw [← Nat.cast_sub]
    rw [zpow_natCast]
    have := FloatFormat.valid_prec
    omega
  rw [hz]
  norm_num
  split_ifs with h
  · contradiction
  · rw [← zpow_add']
    ring_nf
    rw [max_eq_left]
    apply (Int.zpow_le_iff_le_log _ (by simp_all only [ne_eq, not_false_eq_true, abs_pos])).mp
    · simp_all only [ne_eq, not_false_eq_true, Nat.cast_ofNat]
    · norm_num
    · norm_num

end Fp
