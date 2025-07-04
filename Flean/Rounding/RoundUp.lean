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
section RoundUp

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]

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
