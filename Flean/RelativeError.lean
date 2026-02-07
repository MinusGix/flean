import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Rify
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Flean.Basic
import Flean.BitVecUtil

namespace Fp

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloatFormat]

def relativeError (x : R) (y : FiniteFp) : R := |(x - y.toVal) / x|

theorem relativeError_zero_right (x : R) (xnz : x ≠ 0): relativeError x 0 = 1 := by
  delta relativeError
  rw [FiniteFp.toVal_zero, sub_zero, div_self xnz, abs_one]

theorem relativeError_zero_left (y : FiniteFp) : relativeError (0 : R) y = 0 := by
  delta relativeError
  rw [div_zero, abs_zero]

theorem relativeError_toVal_eq (x : R) (y : FiniteFp) : x = y.toVal → relativeError x y = 0 := by
  intro h
  delta relativeError
  rw [h, sub_self, zero_div, abs_zero]

theorem relativeError_neg (x : R) (f : FiniteFp) :
    relativeError x f = relativeError (-x) (-f) := by
  unfold relativeError
  rw [FiniteFp.toVal_neg_eq_neg]
  simp only [abs_div, abs_neg]
  congr 1
  have : (-x : R) - -(f.toVal : R) = -(x - (f.toVal : R)) := by ring
  rw [this, abs_neg]

end Fp
