import Flean.Operations.RangeReduction.XorNet

/-! # The concrete Binary32/RNE XOR reduction -/

set_option autoImplicit false

namespace Flean.RangeReduction.XorNet.Binary32

private local instance binary32Format : FloatFormat := FloatFormat.Binary32.toFloatFormat
private local instance nearestEvenPolicy : UseRoundingPolicy RoundNearestEvenPolicy := {}

/-- The generic capacity contract is discharged by Binary32. -/
theorem fpEval_toVal_eq_xor (x y : Bool) :
    ((XorNet.fpEval x y).toVal : ℝ) = (XorNet.bitInt (x ^^ y) : ℝ) := by
  apply XorNet.fpEval_toVal_eq_xor (R := ℝ)
  · change 4 < 2 ^ (24 : ℕ)
    norm_num
  · change (24 : ℤ) - 1 ≤ 127
    norm_num

/-- The literal Binary32/RNE trace returns the canonical finite encoding of the XOR bit, not
merely a float with the same decoded real value. -/
theorem fpEval_eq_fpBit (x y : Bool) : XorNet.fpEval x y = XorNet.fpBit (x ^^ y) := by
  cases x <;> cases y <;> decide

end Flean.RangeReduction.XorNet.Binary32
