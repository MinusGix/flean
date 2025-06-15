import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational

import Flean.Basic
import Flean.Ulp
import Flean.Ufp
import Flean.RoundingImpl

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

-- Basic properties of rounding with zero
section ZeroProperties

/-- findPredecessor returns 0 when input is 0 -/
theorem findPredecessor_zero [FloatFormat] : findPredecessor (0 : R) = Fp.finite 0 := by
  -- By definition, findPredecessor checks if x = 0 first
  unfold findPredecessor
  -- The condition (0 : R) = 0 is true, so we take the first branch
  simp

/-- findSuccessor returns 0 when input is 0 -/
theorem findSuccessor_zero [FloatFormat] : findSuccessor (0 : R) = Fp.finite 0 := by
  -- By definition, findSuccessor also checks if x = 0 first
  unfold findSuccessor
  -- The condition (0 : R) = 0 is true, so we take the first branch
  simp

end ZeroProperties


-- Helper lemmas about internal rounding functions
section HelperLemmas

/-- roundSubnormalDown never returns positive infinity -/
theorem roundSubnormalDown_ne_pos_inf [FloatFormat] (x : R) (h : isSubnormalRange x) :
  roundSubnormalDown x h ≠ Fp.infinite false := by
  unfold roundSubnormalDown
  -- By definition, it returns either Fp.finite _ or Fp.NaN, never Fp.infinite false
  simp only [ite_ne_right_iff]
  -- intro k_eq_zero -- this would introduce the whole if and make the goal be to prove false from it
  split_ifs
  · simp -- zero branch
  · simp_all only [Int.floor_eq_zero_iff, Set.mem_Ico, not_and, not_lt, ne_eq]
    intro a -- intro so that it is not a ¬(match ....)
    split at a <;> simp_all only [reduceCtorEq]


/-- roundNormalDown never returns positive infinity -/
theorem roundNormalDown_ne_pos_inf [FloatFormat] (x : R) (h : isNormalRange x) :
  roundNormalDown x h ≠ Fp.infinite false := by
  unfold roundNormalDown
  -- By definition, it returns either Fp.finite _ or Fp.NaN, never Fp.infinite false
  norm_num
  intro a
  split at a <;> simp_all only [reduceCtorEq]

/-- findPredecessorPos never returns positive infinity -/
theorem findPredecessorPos_ne_pos_inf [FloatFormat] (x : R) (hpos : 0 < x) :
  findPredecessorPos x hpos ≠ Fp.infinite false := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · -- Subnormal case
    exact roundSubnormalDown_ne_pos_inf x ⟨hpos, h1⟩
  · -- Normal case
    exact roundNormalDown_ne_pos_inf x ⟨le_of_not_gt h1, h2⟩
  · -- Too large case: returns largest finite float
    simp

/-- roundSubnormalUp never returns negative infinity -/
theorem roundSubnormalUp_ne_neg_inf [FloatFormat] (x : R) (h : isSubnormalRange x) :
  roundSubnormalUp x h ≠ Fp.infinite true := by
  -- unfold roundSubnormalUp
  -- norm_num -- simplify variables into if statements and such, generally messier but easier to throw tactics at
  -- unfold mkFiniteFp -- need to unfold to talk about the actual values it creates
  -- intro a -- get out of the ne
  -- split at a -- I believe this is getting the domain you're in
  -- <;> split at a -- we need to do a double split on both the branches
  -- all_goals simp_all -- get rid of easy branches
  -- -- the remaining need another split and cleanup
  -- <;> split at a <;> simp_all
  -- But. We can also replace it with the experimental grind tactic!
  grind [roundSubnormalUp]

/-- roundNormalUp never returns negative infinity -/
theorem roundNormalUp_ne_neg_inf [FloatFormat] (x : R) (h : isNormalRange x) :
  roundNormalUp x h ≠ Fp.infinite true := by
  -- Unfold the definition to see the actual if-then-else structure
  unfold roundNormalUp
  -- Simplify numerical expressions and convert to simpler if-then-else chains
  norm_num
  -- Convert ¬(expr = Fp.infinite true) to (expr = Fp.infinite true → False)
  -- Now 'a' is the hypothesis that the expression equals Fp.infinite true
  intro a
  -- Split on the first if-then-else condition in hypothesis 'a'
  -- This handles: if m ≥ 2^FloatFormat.prec then ...
  split at a
  -- For each goal, split again on nested if-then-else conditions
  -- This handles: if e + 1 > FloatFormat.max_exp then ... and match expressions
  all_goals split at a
  -- Try to close simple goals where the branches clearly don't return Fp.infinite true
  all_goals simp_all
  -- Handle any remaining goals with one more split (for deeply nested matches) and cleanup
  split at a <;> simp_all

/-- findSuccessorPos never returns negative infinity -/
theorem findSuccessorPos_ne_neg_inf [FloatFormat] (x : R) (hpos : 0 < x) :
  findSuccessorPos x hpos ≠ Fp.infinite true := by
  unfold findSuccessorPos
  split_ifs with h1 h2
  · -- Subnormal case
    exact roundSubnormalUp_ne_neg_inf x ⟨hpos, h1⟩
  · -- Normal case
    exact roundNormalUp_ne_neg_inf x ⟨le_of_not_gt h1, h2⟩
  · -- Overflow case: returns Fp.infinite false, not true
    simp

end HelperLemmas

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
  · split at a
    · -- Case: x ≠ 0 and x > 0, uses findPredecessorPos which never returns positive infinity
      have : findPredecessorPos x (by assumption) ≠ Fp.infinite false := findPredecessorPos_ne_pos_inf x (by assumption)
      contradiction
    · -- Case: x ≠ 0 and x ≤ 0, so x < 0 by trichotomy
      -- The result is match findSuccessorPos (-x) with | Fp.infinite b => Fp.infinite (!b) | ..
      -- For result to be Fp.infinite false, we need findSuccessorPos (-x) = Fp.infinite true
      -- But findSuccessorPos never returns Fp.infinite true
      have h_lt : x < 0 := by
        -- We have ¬x = 0 and ¬0 < x, so by trichotomy x < 0
        cases' lt_trichotomy x 0 with h h
        · exact h
        · cases' h with h h
          · simp_all
          · simp_all
      have h_neg_pos : 0 < -x := neg_pos.mpr h_lt
      have : findSuccessorPos (-x) h_neg_pos ≠ Fp.infinite true := findSuccessorPos_ne_neg_inf (-x) h_neg_pos
      -- Now split on the match expression
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
  sorry

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
    simp_all
  · split at a
    · -- Case: x ≠ 0 and x > 0, uses findSuccessorPos which never returns negative infinity
      have : findSuccessorPos x (by assumption) ≠ Fp.infinite true := findSuccessorPos_ne_neg_inf x (by assumption)
      contradiction
    · -- Case: x ≠ 0 and x ≤ 0, so x < 0 by trichotomy
      -- The result is match findPredecessorPos (-x) with | Fp.infinite b => Fp.infinite (!b) | ..
      -- For result to be Fp.infinite true, we need findPredecessorPos (-x) = Fp.infinite false
      -- But findPredecessorPos never returns Fp.infinite false
      have h_lt : x < 0 := by
        -- We have ¬x = 0 and ¬0 < x, so by trichotomy x < 0
        cases' lt_trichotomy x 0 with h h
        · exact h
        · cases' h with h h
          · simp_all
          · simp_all
      have h_neg_pos : 0 < -x := neg_pos.mpr h_lt
      have : findPredecessorPos (-x) h_neg_pos ≠ Fp.infinite false := findPredecessorPos_ne_pos_inf (-x) h_neg_pos
      -- Now split on the match expression
      generalize heq : findPredecessorPos (-x) h_neg_pos = result
      simp only [heq] at a
      cases result with
      | finite f => simp_all
      | infinite b =>
        simp_all only [Bool.not_eq_true]
        rw [← heq] at this
        simp_all
      | NaN => simp_all

theorem roundUp_lt_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundUp x = Fp.finite FiniteFp.smallestPosSubnormal := by
  unfold roundUp findSuccessor
  simp [ne_of_gt hn, hn]
  unfold findSuccessorPos
  -- We need to show x < 2^min_exp to enter the subnormal case
  -- smallestPosSubnormal = 2^(min_exp - prec + 1) < 2^min_exp
  have h_sub : x < (2 : R) ^ FloatFormat.min_exp := by
    have : FiniteFp.smallestPosSubnormal.toVal < (2 : R) ^ FloatFormat.min_exp := by
      sorry -- Need lemma about smallestPosSubnormal < 2^min_exp
    exact lt_trans hs this
  simp [h_sub]
  unfold roundSubnormalUp
  sorry -- Need to prove the ceiling calculation gives smallestPosSubnormal

-- This is a fundamental property that should be in Basic.lean
-- but is missing per the TODO there
theorem finite_le_largestFiniteFloat [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (f : FiniteFp) : (f.toVal : R) ≤ (FiniteFp.largestFiniteFloat.toVal : R) := by
  sorry -- TODO: This requires analyzing all possible finite floats

-- roundUp returns a value ≥ input (fundamental property of rounding up)
theorem roundUp_ge [FloatFormat] (x : R) (f : FiniteFp) 
  (h : roundUp x = Fp.finite f) : x ≤ f.toVal := by
  sorry -- TODO: Fundamental property of rounding up

-- roundUp doesn't return NaN for positive finite inputs
theorem roundUp_pos_not_nan [FloatFormat] (x : R) (h : 0 < x) : 
  roundUp x ≠ Fp.NaN := by
  sorry -- TODO: NaN only for invalid inputs

theorem roundUp_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x > FiniteFp.largestFiniteFloat.toVal):
  roundUp x = Fp.infinite false := by
  -- Proof by contradiction: assume roundUp returns something other than positive infinity
  match h : roundUp x with
  | Fp.finite f =>
    -- If it returns a finite float f, then f.toVal ≥ x (property of rounding up)
    -- But f.toVal ≤ largestFiniteFloat (all finite floats are bounded)
    -- This gives largestFiniteFloat < x ≤ f.toVal ≤ largestFiniteFloat, contradiction!
    have h1 : (f.toVal : R) ≤ (FiniteFp.largestFiniteFloat.toVal : R) := finite_le_largestFiniteFloat f
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

/-- roundTowardZero never increases magnitude -/
theorem roundTowardZero_magnitude_le [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → |f.toVal| ≤ |x| := by
  sorry

/-- roundTowardZero preserves sign for non-zero finite results -/
theorem roundTowardZero_sign_preservation [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → f.toVal ≠ (0 : R) → (x > 0 ↔ f.toVal > (0 : R)) := by
  sorry

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
  sorry

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
  sorry

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
