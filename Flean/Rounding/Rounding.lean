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

/-- Helper function to determine if a real value is exactly representable as a floating-point number -/
def isExactlyRepresentable [FloatFormat] (x : R) : Prop :=
  ∃ (f : FiniteFp), f.toVal = x

/-- Check if a value is exactly at the midpoint between two consecutive floating-point values -/
def isMidpoint [FloatFormat] (x : R) : Prop :=
  let pred := findPredecessor x
  let succ := findSuccessor x
  match pred, succ with
  | Fp.finite p, Fp.finite s => x = (p.toVal + s.toVal) / 2
  | _, _ => False

/-- Extract the significand's least significant bit to check evenness for tie-breaking -/
def isEvenSignificand [FloatFormat] (f : FiniteFp) : Bool :=
  f.m % 2 = 0

-- Round toward negative infinity (floor)
section RoundDown

/-- Round toward negative infinity -/
def roundDown [FloatFormat] (x : R) : Fp :=
  findPredecessor x

/-- roundDown returns 0 when input is 0 -/
theorem roundDown_zero [FloatFormat] : roundDown (0 : R) = Fp.finite 0 := by
  unfold roundDown
  exact findPredecessor_zero

/-- roundDown never produces positive infinity -/
theorem roundDown_ne_pos_inf [FloatFormat] (x : R) : roundDown x ≠ Fp.infinite false := by
  unfold roundDown findPredecessor
  intro a
  split at a
  · -- Case: x = 0, returns Fp.finite 0 ≠ Fp.infinite false
    simp_all
  · split_ifs at a with h2
    -- Case: x ≠ 0 and x ≤ 0, so x < 0 by trichotomy
    -- The result is match findSuccessorPos (-x) with | Fp.infinite b => Fp.infinite (!b) | ..
    -- For result to be Fp.infinite false, we need findSuccessorPos (-x) = Fp.infinite true
    -- But findSuccessorPos never returns Fp.infinite true
    have h_lt : x < 0 := by
      rename_i h1 h3
      apply lt_of_le_of_ne (not_lt.mp h2) h3
    have h_neg_pos : 0 < -x := neg_pos.mpr h_lt
    have : findSuccessorPos (-x) h_neg_pos ≠ Fp.infinite true := findSuccessorPos_ne_neg_inf (-x) h_neg_pos
    generalize heq : findSuccessorPos (-x) h_neg_pos = result
    simp only [heq] at a
    cases result with
    | finite f => simp_all
    | infinite b =>
      simp_all only [Bool.not_eq_false]
      rw [← heq] at this
      simp_all
    | NaN => simp_all

theorem roundDown_lt_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundDown x = Fp.finite 0 := by
  unfold roundDown findPredecessor
  simp only [ne_of_gt hn, ↓reduceDIte, hn]
  unfold findPredecessorPos
  -- Since x < smallestPosSubnormal, x is in subnormal range
  have h_sub : x < (2 : R) ^ FloatFormat.min_exp := by
    -- smallestPosSubnormal = 2^(min_exp - prec + 1) < 2^min_exp
    have : FiniteFp.smallestPosSubnormal.toVal < (2 : R) ^ FloatFormat.min_exp := by
      rw [FiniteFp.smallestPosSubnormal_toVal]
      flinearize!
    exact lt_trans hs this
  simp only [h_sub, ↓reduceDIte]
  rw [Fp.finite.injEq]
  apply roundSubnormalDown_eq_zero_iff.mpr
  trivial

theorem roundDown_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x ≥ (2 : R) ^ (FloatFormat.max_exp + 1)):
  roundDown x = Fp.finite FiniteFp.largestFiniteFloat := by
  unfold roundDown findPredecessor
  simp [ne_of_gt hn, hn]
  unfold findPredecessorPos
  -- Since x ≥ 2^(max_exp + 1), we're beyond the normal range
  have h_sub : ¬(x < (2 : R) ^ FloatFormat.min_exp) := by
    have h2 : (2 : R) ^ FloatFormat.min_exp ≤ (2 : R) ^ (FloatFormat.max_exp + 1) := by flinearize!
    linarith
  simp [h_sub]
  -- The second condition is also false since x ≥ 2^(max_exp + 1)
  have h_overflow : ¬(x < (2 : R) ^ (FloatFormat.max_exp + 1)) := by
    exact not_lt.mpr hs
  simp [h_overflow]

theorem roundDown_nonneg_imp_nonneg [FloatFormat] (x : R) (hs : 0 ≤ x) (f : FiniteFp) (h' : roundDown x = Fp.finite f) : (0 : R) ≤ f.toVal := by
  unfold roundDown findPredecessor at h'
  split_ifs at h'
  · rw [Fp.finite.injEq] at h'
    simp [← h']
  · rw [Fp.finite.injEq] at h'
    rw [← h']
    apply findPredecessorPos_nonneg
  · norm_num at h'
    rename_i h1 h2
    norm_num at h1 h2
    have := (hs.ge_iff_eq.mp h2).symm
    contradiction

theorem roundDown_pos_imp_pos [FloatFormat] (x : R) (hs : FiniteFp.smallestPosSubnormal.toVal ≤ x) (f : FiniteFp) (h' : roundDown x = Fp.finite f) : (0 : R) < f.toVal := by
  unfold roundDown findPredecessor at h'
  have hpos : 0 < x := by linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  split_ifs at h'
  · simp_all only [lt_self_iff_false]
  · rw [Fp.finite.injEq] at h'
    rw [← h']
    apply findPredecessorPos_pos hs

end RoundDown

-- Round toward positive infinity (ceiling)
section RoundUp

/-- Round toward positive infinity -/
def roundUp [FloatFormat] (x : R) : Fp :=
  findSuccessor x

/-- roundUp returns 0 when input is 0 -/
theorem roundUp_zero [FloatFormat] : roundUp (0 : R) = Fp.finite 0 := by
  unfold roundUp
  exact findSuccessor_zero

/-- roundUp never produces negative infinity -/
theorem roundUp_ne_neg_inf [FloatFormat] (x : R) : roundUp x ≠ Fp.infinite true := by
  unfold roundUp findSuccessor
  intro a
  split at a
  · -- Case: x = 0, returns Fp.finite 0 ≠ Fp.infinite true
    simp_all only [reduceCtorEq]
  · split_ifs at a with h2
    -- Case: x ≠ 0 and x > 0, uses findSuccessorPos which never returns negative infinity
    have : findSuccessorPos x (by assumption) ≠ Fp.infinite true := findSuccessorPos_ne_neg_inf x (by assumption)
    contradiction

theorem roundUp_lt_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundUp x = Fp.finite FiniteFp.smallestPosSubnormal := by
  unfold roundUp findSuccessor
  simp [ne_of_gt hn, hn]
  unfold findSuccessorPos
  -- We need to show x < 2^min_exp to enter the subnormal case
  -- smallestPosSubnormal = 2^(min_exp - prec + 1) < 2^min_exp
  have h_sub : x < (2 : R) ^ FloatFormat.min_exp := lt_trans hs FiniteFp.smallestPosSubnormal_lt_minExp
  simp only [h_sub, ↓reduceDIte]
  unfold roundSubnormalUp
  -- The ULP in subnormal range is 2^(min_exp - prec + 1) = smallestPosSubnormal
  -- So ⌈x / smallestPosSubnormal⌉ = 1 since 0 < x < smallestPosSubnormal
  rw [FiniteFp.smallestPosSubnormal_toVal] at hs
  have h_ceil : ⌈x / FiniteFp.smallestPosSubnormal.toVal⌉ = 1 := by
    rw [Int.ceil_eq_iff, FiniteFp.smallestPosSubnormal_toVal]
    norm_num
    constructor
    · exact div_pos hn (by linearize)
    · exact div_le_one_of_le₀ (le_of_lt hs) (by linearize)
  rw [FiniteFp.smallestPosSubnormal_toVal] at h_ceil
  simp [h_ceil]
  -- Show k = 1 and 1 < 2^(prec-1), so go to else branch
  have h_k_lt : 1 < (2 : ℤ)^(FloatFormat.prec - 1) := by
    apply one_lt_pow₀ (by norm_num)
    fomega
  simp only [h_k_lt.not_ge] -- for some reason need the opposite to recognize it
  rw [dite_false, FiniteFp.smallestPosSubnormal]

-- Main theorem: roundUp returns a value ≥ input (fundamental property of rounding up)
theorem roundUp_ge [FloatFormat] (x : R) (f : FiniteFp)
  (h : roundUp x = Fp.finite f) : x ≤ f.toVal := by
  unfold roundUp findSuccessor at h
  split_ifs at h with h_zero h_pos
  · -- Case: x = 0
    simp at h
    rw [h.symm, h_zero, FiniteFp.toVal_zero]
  · -- Case: x > 0
    exact findSuccessorPos_ge x h_pos f h
  · -- Case: x < 0
    have h_neg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h_pos) h_zero)
    unfold findPredecessorPos at h
    norm_num at h
    split at h
    <;> rename_i heq
    · rw [neg_eq_iff_eq_neg] at h
      have a := roundSubnormalDown_le (-x) (by trivial)
      rw [h, FiniteFp.toVal_neg_eq_neg] at a
      linarith
    · split at h
      · rw [neg_eq_iff_eq_neg] at h
        have h1 : isNormalRange (-x) := by split_ands <;> linarith
        have a := roundNormalDown_le (-x) h1
        rw [h, FiniteFp.toVal_neg_eq_neg] at a
        linarith
      · rw [← h, FiniteFp.toVal_neg_eq_neg]
        linarith [FiniteFp.largestFiniteFloat_lt_maxExp_succ (R := R)]

-- roundUp doesn't return NaN for positive finite inputs
theorem roundUp_pos_not_nan [FloatFormat] (x : R) (xpos : 0 < x) :
  roundUp x ≠ Fp.NaN := by
  unfold roundUp findSuccessor
  intro a
  simp [ne_of_gt xpos] at a
  unfold findSuccessorPos at a
  split_ifs at a with h1 h2
  -- Normal case: roundNormalUp
  norm_num at h1
  have h : isNormalRange x := ⟨h1, h2⟩
  have := roundNormalUp_ne_nan x h
  contradiction

theorem roundUp_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x > FiniteFp.largestFiniteFloat.toVal):
  roundUp x = Fp.infinite false := by
  -- Proof by contradiction: assume roundUp returns something other than positive infinity
  match h : roundUp x with
  | Fp.finite f =>
    -- If it returns a finite float f, then f.toVal ≥ x (property of rounding up)
    -- But f.toVal ≤ largestFiniteFloat (all finite floats are bounded)
    -- This gives largestFiniteFloat < x ≤ f.toVal ≤ largestFiniteFloat, contradiction!
    have h1 : (f.toVal : R) ≤ (FiniteFp.largestFiniteFloat.toVal : R) := FiniteFp.finite_le_largestFiniteFloat f
    have h2 : x ≤ (f.toVal : R) := roundUp_ge x f h
    have : (FiniteFp.largestFiniteFloat.toVal : R) < (FiniteFp.largestFiniteFloat.toVal : R) := by
      calc (FiniteFp.largestFiniteFloat.toVal : R) < x := hs
           _ ≤ (f.toVal : R) := h2
           _ ≤ (FiniteFp.largestFiniteFloat.toVal : R) := h1
    exact absurd this (lt_irrefl _)
  | Fp.infinite b =>
    -- Need to show b = false (positive infinity)
    by_cases hb : b
    · -- If b = true (negative infinity), contradiction since x > 0
      have : roundUp x ≠ Fp.infinite true := roundUp_ne_neg_inf x
      rw [h] at this
      simp [hb] at this
    · -- If b = false, we're done
      simp [hb]
  | Fp.NaN =>
    -- roundUp of valid positive input should not return NaN
    have : roundUp x ≠ Fp.NaN := roundUp_pos_not_nan x hn
    exact absurd h this

end RoundUp

-- Round toward zero (truncation)
section RoundTowardZero

/-- Round toward zero -/
def roundTowardZero [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if x > 0 then
    -- For positive x, round down (toward zero)
    roundDown x
  else
    -- For negative x, round up (toward zero)
    roundUp x

/-- roundTowardZero returns 0 when input is 0 -/
theorem roundTowardZero_zero [FloatFormat] : roundTowardZero (0 : R) = Fp.finite 0 := by
  unfold roundTowardZero
  simp

theorem roundTowardZero_pos_eq [FloatFormat] (x : R) (hpos : 0 < x) : roundTowardZero x = roundDown x := by
  simp [roundTowardZero, hpos]
  intro hz
  linarith

theorem roundTowardZero_neg_eq [FloatFormat] (x : R) (hneg : x < 0) : roundTowardZero x = roundUp x := by
  have xnz : x ≠ 0 := by linarith
  have xngt : ¬0 < x := by linarith
  simp only [roundTowardZero, xnz, ↓reduceIte, gt_iff_lt, xngt] -- because it is too dumb to figure this out...

/-- roundTowardZero never increases magnitude -/
theorem roundTowardZero_magnitude_le [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → |f.toVal| ≤ |x| := by
  intro h
  cases' lt_trichotomy x 0 with h1 h2
  · rw [roundTowardZero_neg_eq x h1] at h
    unfold roundUp at h
    rw [findSuccessor_neg_eq x h1, Fp.finite.injEq] at h
    have ha := findPredecessorPos_le (-x) (neg_pos.mpr h1)
    rw [neg_eq_iff_eq_neg] at h
    rw [h, FiniteFp.toVal_neg_eq_neg] at ha
    norm_num at ha
    apply abs_le_abs_of_nonpos
    · have := findPredecessorPos_nonneg (x := -x) (hpos := neg_pos.mpr h1)
      rw [h, FiniteFp.toVal_neg_eq_neg] at this
      linarith
    · trivial
  · cases' h2 with h2 h3
    · rw [h2, abs_zero]
      rw [h2, roundTowardZero_zero, Fp.finite.injEq] at h
      rw [← h, FiniteFp.toVal_zero, abs_zero]
    · rw [roundTowardZero_pos_eq x h3] at h
      unfold roundDown at h
      rw [findPredecessor_pos_eq x h3, Fp.finite.injEq] at h
      have ha := findPredecessorPos_le x h3
      rw [← h]
      apply abs_le_abs_of_nonneg
      apply findPredecessorPos_nonneg
      trivial

theorem roundTowardZero_le_pos [FloatFormat] (x : R) (f : FiniteFp) (hpos : 0 < x) :
  roundTowardZero x = Fp.finite f → f.toVal ≤ x := by
  intro hf
  apply le_of_abs_le
  rw [← abs_of_pos hpos]
  apply roundTowardZero_magnitude_le x f hf

/-- roundTowardZero preserves sign for non-zero finite results -/
theorem roundTowardZero_pos [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → f.toVal ≠ (0 : R) → (0 < x ↔ (0 : R) < f.toVal) := by
  intro hf fnz
  constructor
  · intro xpos
    rw [roundTowardZero_pos_eq x xpos] at hf
    unfold roundDown at hf
    rw [findPredecessor_pos_eq x xpos, Fp.finite.injEq] at hf
    rw [← hf]
    apply findPredecessorPos_pos
    have := findPredecessorPos_nonneg (x := x) (hpos := xpos)
    rw [← hf] at fnz
    have : (0 : R) < (findPredecessorPos x xpos).toVal := lt_of_le_of_ne this fnz.symm
    apply findPredecessorPos_pos_iff.mpr this
  · intro fpos
    unfold roundTowardZero at hf
    split_ifs at hf with h1 h2
    · rw [Fp.finite.injEq] at hf
      rw [← hf, FiniteFp.toVal_zero] at fnz
      contradiction
    · trivial
    · norm_num at h2
      have h2 : x < 0 := h2.lt_of_ne h1
      unfold roundUp at hf
      rw [findSuccessor_neg_eq x h2, Fp.finite.injEq] at hf
      rw [neg_eq_iff_eq_neg] at hf
      have ha := findPredecessorPos_le (-x) (neg_pos.mpr h2)
      rw [hf, FiniteFp.toVal_neg_eq_neg] at ha
      have ha' := findPredecessorPos_nonneg (x := -x) (hpos := neg_pos.mpr h2)
      rw [hf, FiniteFp.toVal_neg_eq_neg] at ha'
      norm_num at ha'
      linarith

end RoundTowardZero

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
