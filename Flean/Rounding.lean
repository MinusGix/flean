import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Flean.Basic

section Rounding

variable {R : Type*} [LinearOrderedField R] [FloorSemiring R]

-- TODO: should this be more central as a type rather than a one-off for bracketing pairs?
-- Possibly non-valid finite fp
@[ext]
structure QFiniteFp [FloatFormat] where
  /-- The sign of the number. -/
  s : Bool
  /-- The exponent -/
  e : ℤ
  /-- The integral significand. Without the sign. -/
  m : ℕ

namespace QFiniteFp

instance [FloatFormat] : Zero QFiniteFp :=
  ⟨{
    s := false,
    e := FloatFormat.min_exp,
    m := 0,
  }⟩

end QFiniteFp

def bracketingPair_handleSubnormals [FloatFormat] (x : R) (e : ℤ) (z1 z2 : QFiniteFp) (is_exact : Bool)  : (QFiniteFp × QFiniteFp) :=
  if e < FloatFormat.min_exp then
    let shift := FloatFormat.min_exp - e
    let z1 := denormalize z1 shift
    let z2 := if is_exact then z2 else denormalize z2 shift
    (z1, z2)
  else
    (z1, z2)

def bracketingPair_handleLargeSignificands [FloatFormat] (z1 z2 : QFiniteFp) (is_exact : Bool) : (QFiniteFp × QFiniteFp) :=
  if z1.m ≥ (2 : R)^(FloatFormat.prec : ℤ) || (!is_exact && z2.m ≥ (2 : R)^(FloatFormat.prec : ℤ)) then
    let z1 := normalize z1
    if !is_exact then
      let z2 := normalize z2
      (z1, z2)
    else
      (z1, z2)
  else
    (z1, z2)

-- Based off of "An Implementation Guide to a Proposed Standard for Floating-Point Arithmetic" by Jerome T. Coonen
def bracketingPair [FloatFormat] (x : R) : (QFiniteFp × QFiniteFp) :=
  if x = 0 then (0, 0)
  else
  let sign := x < 0
  let e : ℤ := Int.log 2 (|x|)

  let scaled := |x| / (2 : R)^e
  let shifted := scaled * (2 : R)^(FloatFormat.prec : ℤ)

  let is_exact := ⌊shifted⌋₊ == ⌈shifted⌉₊

  let z1 := QFiniteFp.mk sign e ⌊shifted⌋₊
  let z2 := QFiniteFp.mk sign e ⌈shifted⌉₊

  if e > FloatFormat.max_exp then
    sorry -- overflow error?
  else
    let ⟨z1, z2⟩ := bracketingPair_handleSubnormals x e z1 z2 is_exact
    let ⟨z1, z2⟩ := bracketingPair_handleLargeSignificands (R := R) z1 z2 is_exact
    (z1, z2)

-- TODO: proof that if the number is exactly representable then the returned pair is just (num, num)

-- TODO: we should probably have real versions of these
/-- Round toward negative infinity -/
def roundDown [FloatFormat] (x : R) : Fp :=
  sorry -- Implementation needed

theorem roundDown_le_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundDown x = 0 := by
  sorry

theorem roundDown_ge_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x ≥ FiniteFp.largestFiniteFloat.toVal):
  roundDown x = Fp.infinite false := by
  sorry

/-- Round toward positive infinity -/
def roundUp [FloatFormat] (x : R) : Fp :=
  sorry -- Implementation needed

theorem roundUp_lt_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundUp x = 0 := by
  sorry

theorem roundUp_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x > FiniteFp.largestFiniteFloat.toVal):
  roundUp x = Fp.infinite false := by
  sorry

/-- Round toward zero -/
def roundTowardZero [FloatFormat] (x : R) : Fp :=
  if x ≥ 0 then roundDown x else roundUp x

/-- Round to nearest, ties to even -/
def roundNearestTiesToEven [FloatFormat] (x : R) : Fp :=
  if x = 0 then 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then 0
  else if |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp then Fp.infinite (x < 0)
  else
    let e

theorem rnEven_le_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesToEven x = 0 := by
  sorry

-- TODO: negative values?
-- TODO: better name.
-- Closely related to largest positive normal number.
theorem rnEven_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesToEven x = Fp.infinite false := by
  sorry

/-- Round to nearest, ties away from zero -/
def roundNearestTiesAwayFromZero [FloatFormat] (x : R) : Fp :=
  sorry -- Implementation needed

theorem rnAway_lt_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesAwayFromZero x = 0 := by
  sorry

theorem rnAway_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesAwayFromZero x = Fp.infinite false := by
  sorry


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

end Rounding
