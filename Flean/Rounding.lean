import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Flean.Basic

section Rounding

variable [F : FloatFormat]

-- TODO: we should probably have real versions of these
/-- Round toward negative infinity -/
def roundDown (x : ℚ) : Fp :=
  sorry -- Implementation needed

/-- Round toward positive infinity -/
def roundUp (x : ℚ) : Fp :=
  sorry -- Implementation needed

/-- Round toward zero -/
def roundTowardZero (x : ℚ) : Fp :=
  if x ≥ 0 then roundDown x else roundUp x

/-- Round to nearest, ties to even -/
def roundNearestTiesToEven (x : ℚ) : Fp :=
  sorry -- Implementation needed

/-- Round to nearest, ties away from zero -/
def roundNearestTiesAwayFromZero (x : ℚ) : Fp :=
  sorry -- Implementation needed


inductive RoundingMode
  | Down
  | Up
  | TowardZero
  | NearestTiesToEven
  | NearestTiesAwayFromZero

def RoundingMode.toRoundingFunction (mode : RoundingMode) : ℚ → Fp :=
  match mode with
  | .Down => roundDown
  | .Up => roundUp
  | .TowardZero => roundTowardZero
  | .NearestTiesToEven => roundNearestTiesToEven
  | .NearestTiesAwayFromZero => roundNearestTiesAwayFromZero

def RoundingMode.round (mode : RoundingMode) (x : ℚ) : Fp :=
  mode.toRoundingFunction x

end Rounding
