import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Polyrith

import Flean.Util
import Flean.Basic
import Flean.Ulp
import Flean.Ufp
import Flean.Linearize.Linearize
import Flean.Rounding.Neighbor
import Flean.Rounding.RoundDown
import Flean.Rounding.RoundUp
import Flean.Rounding.RoundTowardZero
import Flean.Rounding.RoundNearest

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]

-- Rounding mode enumeration and general interface
section RoundingModes

inductive RoundingMode
  | Down
  | Up
  | TowardZero
  | NearestTiesToEven
  | NearestTiesAwayFromZero

def RoundingMode.toRoundingFunction [FloatFormat] (mode : RoundingMode) : R → Fp :=
  match mode with
  | .Down => roundDown
  | .Up => roundUp
  | .TowardZero => roundTowardZero
  | .NearestTiesToEven => roundNearestTiesToEven
  | .NearestTiesAwayFromZero => roundNearestTiesAwayFromZero

def RoundingMode.round [FloatFormat] (mode : RoundingMode) (x : R) : Fp :=
  mode.toRoundingFunction x

/-- General property: all rounding modes preserve exact zero -/
theorem all_rounding_modes_preserve_zero [FloatFormat] (mode : RoundingMode) :
  mode.round (0 : R) = Fp.finite 0 := by
  cases mode with
  | Down => exact roundDown_zero
  | Up => exact roundUp_zero
  | TowardZero => exact roundTowardZero_zero
  | NearestTiesToEven => exact roundNearestTiesToEven_zero
  | NearestTiesAwayFromZero => exact roundNearestTiesAwayFromZero_zero

/-- All rounding functions are well-defined (always return a valid Fp) -/
theorem rounding_mode_total [FloatFormat] (mode : RoundingMode) (x : R) :
  ∃ y : Fp, mode.round x = y := ⟨mode.round x, rfl⟩

-- TODO: Add monotonicity properties once we define an ordering on Fp
-- This would be useful for proving that rounding preserves order relations

end RoundingModes

end Rounding
