import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.Polyrith

import Flean.Util
import Flean.Basic
import Flean.Ulp
import Flean.Ufp
import Flean.Linearize.Linearize
import Flean.Rounding.Neighbor

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]

/-- Extract the significand's least significant bit to check evenness for tie-breaking -/
def isEvenSignificand [FloatFormat] (f : FiniteFp) : Bool :=
  f.m % 2 = 0

-- Round to nearest, ties to even (default IEEE 754 rounding)
section RoundNearestTiesToEven

/-- Round to nearest, ties to even -/
def roundNearestTiesToEven [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then Fp.finite 0
  else if |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp then Fp.infinite (x < 0)
  else
    let pred := findPredecessor x
    let succ := findSuccessor x
    match pred, succ with
    | Fp.finite p, Fp.finite s =>
      let midpoint := (p.toVal + s.toVal) / 2
      if x < midpoint then pred
      else if x > midpoint then succ
      else  -- x is exactly at midpoint, round to even
        if isEvenSignificand p then pred else succ
    | _, _ => Fp.NaN  -- Should not happen in normal range

/-- roundNearestTiesToEven returns 0 when input is 0 -/
theorem roundNearestTiesToEven_zero [FloatFormat] : roundNearestTiesToEven (0 : R) = Fp.finite 0 := by
  unfold roundNearestTiesToEven
  simp

theorem rnEven_le_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesToEven x = Fp.finite 0 := by
  unfold roundNearestTiesToEven
  -- Check the conditions
  simp [ne_of_gt hn]
  -- Need to show |x| < smallestPosSubnormal / 2
  have h_abs : |x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hn]
    exact hs
  simp [h_abs]

-- TODO: negative values?
-- TODO: better name.
-- Closely related to largest positive normal number.
theorem rnEven_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesToEven x = Fp.infinite false := by
  sorry

end RoundNearestTiesToEven

-- Round to nearest, ties away from zero
section RoundNearestTiesAwayFromZero

/-- Round to nearest, ties away from zero -/
def roundNearestTiesAwayFromZero [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then Fp.finite 0
  else if |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp then Fp.infinite (x < 0)
  else
    let pred := findPredecessor x
    let succ := findSuccessor x
    match pred, succ with
    | Fp.finite p, Fp.finite s =>
      let midpoint := (p.toVal + s.toVal) / 2
      if x < midpoint then pred
      else if x > midpoint then succ
      else  -- x is exactly at midpoint, round away from zero
        if x > 0 then succ else pred
    | _, _ => Fp.NaN  -- Should not happen in normal range

/-- roundNearestTiesAwayFromZero returns 0 when input is 0 -/
theorem roundNearestTiesAwayFromZero_zero [FloatFormat] : roundNearestTiesAwayFromZero (0 : R) = Fp.finite 0 := by
  unfold roundNearestTiesAwayFromZero
  simp

theorem rnAway_lt_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesAwayFromZero x = Fp.finite 0 := by
  unfold roundNearestTiesAwayFromZero
  -- Check the conditions - same logic as rnEven
  simp [ne_of_gt hn]
  have h_abs : |x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hn]
    exact hs
  simp [h_abs]

theorem rnAway_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesAwayFromZero x = Fp.infinite false := by
  sorry

end RoundNearestTiesAwayFromZero

end Rounding
