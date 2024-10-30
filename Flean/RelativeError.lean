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

namespace Fp

variable {R : Type*} [LinearOrderedField R] [FloatFormat]
-- [FloorSemiring R]

def relativeError (x : R) (y : FiniteFp) : R := (x - y.toVal) / x

theorem relativeError_zero_right (x : R) (xnz : x ≠ 0): relativeError x 0 = 1 := by
  delta relativeError
  rw [FiniteFp.toVal_zero, sub_zero, div_self xnz]

theorem relativeError_zero_left (y : FiniteFp) : @relativeError R _ _ 0 y = 0 := by
  delta relativeError
  rw [div_zero]

theorem relativeError_toVal_eq (x : R) (y : FiniteFp) : x = y.toVal → relativeError x y = 0 := by
  intro h
  delta relativeError
  rw [h, sub_self, zero_div]

end Fp
