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
import Flean.Rounding.RelativeErrorBounds
import Flean.Rounding.Idempotence

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
deriving DecidableEq

/-- Conjugate rounding mode: swaps Down ↔ Up, keeps symmetric modes.
    Key property: `mode.round(-x) = -(mode.conjugate.round x)` for `x ≠ 0`. -/
def RoundingMode.conjugate : RoundingMode → RoundingMode
  | .Down => .Up
  | .Up => .Down
  | m => m

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

/-- Rounding a negated value equals negating the conjugate round.
    Down(-x) = -(Up(x)), Up(-x) = -(Down(x)), and the symmetric modes
    commute with negation. -/
theorem RoundingMode.round_neg [FloatFormat] (mode : RoundingMode) (x : R) (hx : x ≠ 0) :
    mode.round (-x) = -(mode.conjugate.round x) := by
  cases mode with
  | Down => exact roundDown_neg_eq_neg_roundUp x hx
  | Up => exact roundUp_neg_eq_neg_roundDown x hx
  | TowardZero => exact roundTowardZero_neg_eq_neg x hx
  | NearestTiesToEven => exact rnEven_neg_eq_neg x hx
  | NearestTiesAwayFromZero => exact rnAway_neg_eq_neg x hx

/-- All rounding modes are monotone: `x ≤ y → round(x) ≤ round(y)`. -/
theorem RoundingMode.round_mono [FloatFormat] (mode : RoundingMode) {x y : R} (h : x ≤ y) :
    mode.round x ≤ mode.round y := by
  cases mode with
  | Down => exact roundDown_mono h
  | Up => exact roundUp_mono h
  | TowardZero => exact roundTowardZero_mono h
  | NearestTiesToEven => exact roundNearestTE_mono h
  | NearestTiesAwayFromZero => exact roundNearestTA_mono h

/-- For nearest modes, values at or above the overflow threshold round to positive infinity. -/
theorem nearest_round_overflow [FloatFormat] (mode : RoundingMode) (x : R)
    (hmode : mode = .NearestTiesToEven ∨ mode = .NearestTiesAwayFromZero)
    (hx : FloatFormat.overflowThreshold R ≤ x) :
    mode.round x = Fp.infinite false := by
  cases hmode with
  | inl hTE => subst hTE; simp only [RoundingMode.round, RoundingMode.toRoundingFunction]
               exact rnEven_ge_inf _ hx
  | inr hTA => subst hTA; simp only [RoundingMode.round, RoundingMode.toRoundingFunction]
               exact rnAway_ge_inf _ hx

end RoundingModes

end Rounding
