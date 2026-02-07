import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Flean.Rounding.RoundDown
import Flean.Rounding.RoundUp
import Flean.Rounding.RoundTowardZero
import Flean.Rounding.RoundNearest

/-! # Relative Error Bounds for Rounding

This module proves the core theorem of floating-point arithmetic:
rounding introduces at most machine-epsilon relative error.

## Main results

* `roundDown_relativeError_le` — For positive x in the normal range,
  `relativeError x (roundDown x) ≤ 2^(1-prec)` (machine epsilon).
* `roundTowardZero_relativeError_le` — For positive x in the normal range,
  `relativeError x (roundTowardZero x) ≤ 2^(1-prec)`.
* `roundTowardZero_relativeError_le_neg` — For negative x with -x in the normal range,
  `relativeError x (roundTowardZero x) ≤ 2^(1-prec)`.
* `roundUp_relativeError_le` — For positive x in the normal range,
  `relativeError x (roundUp x) ≤ 2^(1-prec)`.
* `roundNearestTiesToEven_relativeError_le` — For positive x in the normal range,
  `relativeError x (roundNearestTiesToEven x) ≤ 2^(1-prec)`.
* `roundNearestTiesAwayFromZero_relativeError_le` — For positive x in the normal range,
  `relativeError x (roundNearestTiesAwayFromZero x) ≤ 2^(1-prec)`.
-/

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-- For positive x in the normal range, roundDown produces a finite float
    whose absolute error is less than ulp(x). -/
theorem roundDown_abs_error_lt_ulp_pos (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundDown x = Fp.finite f) :
    |x - f.toVal| < Fp.ulp x := by
  -- roundDown of positive x = Fp.finite (findPredecessorPos x hpos)
  have hxpos := isNormalRange_pos x hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  -- Unfold roundDown to get findPredecessorPos
  unfold roundDown findPredecessor at hf
  simp only [hxne, hxpos, ↓reduceDIte, Fp.finite.injEq] at hf
  -- Now f = findPredecessorPos x hxpos
  rw [← hf]
  -- findPredecessorPos in normal range is roundNormalDown
  unfold findPredecessorPos
  have h_not_sub : ¬(x < (2 : R) ^ FloatFormat.min_exp) := not_lt.mpr hx.left
  simp only [h_not_sub, ↓reduceDIte]
  have h_not_over : x < (2 : R) ^ (FloatFormat.max_exp + 1) := hx.right
  simp only [h_not_over, ↓reduceDIte]
  -- Now the goal is |x - roundNormalDown(x, h).toVal| < ulp(x)
  -- where h : isNormalRange x
  -- Since roundNormalDown(x) ≤ x, the difference is nonneg
  rw [abs_of_nonneg (roundNormalDown_error_nonneg x ⟨not_lt.mp h_not_sub, h_not_over⟩)]
  exact roundNormalDown_error_lt_ulp x ⟨not_lt.mp h_not_sub, h_not_over⟩

/-- roundDown of a positive normal value is finite -/
theorem roundDown_normal_is_finite (x : R) (hx : isNormalRange x) :
    ∃ f : FiniteFp, roundDown x = Fp.finite f := by
  have hxpos := isNormalRange_pos x hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  unfold roundDown findPredecessor
  simp only [hxne, hxpos, ↓reduceDIte]
  exact ⟨findPredecessorPos x hxpos, rfl⟩

/-- **Machine Epsilon Bound for Round-Down**: For positive x in the normal range,
the relative error of rounding down is at most 2^(1-prec) (machine epsilon).

This is one of the central results in floating-point arithmetic:
  `relativeError x (roundDown x) ≤ 2^(1-prec)`
-/
theorem roundDown_relativeError_le (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundDown x = Fp.finite f) :
    Fp.relativeError x f ≤ 2^(1 - (FloatFormat.prec : ℤ)) := by
  have hxpos := isNormalRange_pos x hx
  -- The absolute error is < ulp(x), so ≤ 1 * ulp(x)
  have h_abs_err := roundDown_abs_error_lt_ulp_pos x hx f hf
  -- |x| ≥ 2^min_exp since x is in normal range
  have h_abs_ge : (2 : R) ^ FloatFormat.min_exp ≤ |x| := by
    rw [abs_of_pos hxpos]; exact hx.left
  -- Use the bridge lemma: |x - y| ≤ α * ulp(x) implies relativeError ≤ α * 2^(1-prec)
  -- with α = 1
  have h_le : |x - f.toVal| ≤ 1 * Fp.ulp x := by linarith
  have h := Fp.relativeError_ulp_upper_bound_le x f 1 (by norm_num) h_abs_ge h_le
  linarith

/-- For positive x in the normal range, relative error of roundTowardZero
    is at most machine epsilon. Follows directly since roundTowardZero = roundDown
    for positive inputs. -/
theorem roundTowardZero_relativeError_le (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundTowardZero x = Fp.finite f) :
    Fp.relativeError x f ≤ 2^(1 - (FloatFormat.prec : ℤ)) := by
  rw [roundTowardZero_pos_eq x (isNormalRange_pos x hx)] at hf
  exact roundDown_relativeError_le x hx f hf

/-- For negative x with -x in the normal range, relative error of roundTowardZero
    is at most machine epsilon. For negative inputs, roundTowardZero = roundUp,
    and the error mirrors roundDown applied to -x. -/
theorem roundTowardZero_relativeError_le_neg (x : R) (hx : isNormalRange (-x)) (f : FiniteFp)
    (hf : roundTowardZero x = Fp.finite f) :
    Fp.relativeError x f ≤ 2^(1 - (FloatFormat.prec : ℤ)) := by
  have hneg : x < 0 := by linarith [isNormalRange_pos (-x) hx]
  -- Transform relative error: relativeError x f = relativeError (-x) (-f)
  rw [Fp.relativeError_neg]
  -- Suffices to show roundDown (-x) = Fp.finite (-f)
  apply roundDown_relativeError_le (-x) hx (-f)
  -- Extract: roundTowardZero x = roundUp x = -findPredecessorPos(-x)
  rw [roundTowardZero_neg_eq x hneg] at hf
  unfold roundUp at hf
  rw [findSuccessor_neg_eq x hneg, Fp.finite.injEq] at hf
  -- hf : -findPredecessorPos (-x) _ = f, so -f = findPredecessorPos (-x) _
  have hpos : 0 < -x := neg_pos.mpr hneg
  unfold roundDown
  rw [findPredecessor_pos_eq (-x) hpos, Fp.finite.injEq]
  rw [← hf, neg_neg]

/-- For positive x in the normal range, roundUp produces a finite float
    whose absolute error is less than ulp(x). -/
theorem roundUp_abs_error_lt_ulp_pos (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundUp x = Fp.finite f) :
    |f.toVal - x| < Fp.ulp x := by
  have hxpos := isNormalRange_pos x hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  -- Unfold roundUp to get findSuccessorPos
  unfold roundUp findSuccessor at hf
  simp only [hxne, hxpos, ↓reduceDIte] at hf
  -- Now hf : findSuccessorPos x hxpos = Fp.finite f
  unfold findSuccessorPos at hf
  have h_not_sub : ¬(x < (2 : R) ^ FloatFormat.min_exp) := not_lt.mpr hx.left
  simp only [h_not_sub, ↓reduceDIte] at hf
  have h_not_over : x < (2 : R) ^ (FloatFormat.max_exp + 1) := hx.right
  simp only [h_not_over, ↓reduceDIte] at hf
  -- Now hf : roundNormalUp x _ = Fp.finite f
  rw [abs_of_nonneg (roundNormalUp_error_nonneg x ⟨not_lt.mp h_not_sub, h_not_over⟩ f hf)]
  exact roundNormalUp_error_lt_ulp x ⟨not_lt.mp h_not_sub, h_not_over⟩ f hf

/-- **Machine Epsilon Bound for Round-Up**: For positive x in the normal range,
the relative error of rounding up is at most 2^(1-prec) (machine epsilon). -/
theorem roundUp_relativeError_le (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundUp x = Fp.finite f) :
    Fp.relativeError x f ≤ 2^(1 - (FloatFormat.prec : ℤ)) := by
  have hxpos := isNormalRange_pos x hx
  have h_abs_err := roundUp_abs_error_lt_ulp_pos x hx f hf
  have h_abs_ge : (2 : R) ^ FloatFormat.min_exp ≤ |x| := by
    rw [abs_of_pos hxpos]; exact hx.left
  -- |x - f.toVal| = |f.toVal - x| (by abs symmetry), and we know |f.toVal - x| < ulp(x)
  have h_abs_swap : |x - (f.toVal : R)| = |(f.toVal : R) - x| := by
    rw [show x - (f.toVal : R) = -(((f.toVal : R) - x)) from by ring, abs_neg]
  have h_le : |x - (f.toVal : R)| ≤ 1 * Fp.ulp x := by
    rw [h_abs_swap]; linarith
  have h := Fp.relativeError_ulp_upper_bound_le x f 1 (by norm_num) h_abs_ge h_le
  linarith

/-- For positive x in the normal range, roundNearestTiesToEven returns either
    roundDown x or roundUp x (when the result is finite). -/
theorem roundNearestTiesToEven_is_roundDown_or_roundUp (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundNearestTiesToEven x = Fp.finite f) :
    roundDown x = Fp.finite f ∨ roundUp x = Fp.finite f := by
  have hxpos := isNormalRange_pos x hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have h_not_small : ¬(|x| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    intro h_abs
    rw [abs_of_pos hxpos] at h_abs
    have := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp (R := R)
    linarith [hx.left]
  -- Unfold and dismiss the first two ifs using rw [if_neg]
  unfold roundNearestTiesToEven at hf
  rw [if_neg hxne] at hf
  rw [if_neg h_not_small] at hf
  -- Handle the overflow condition
  by_cases h_overflow : |x| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * 2 ^ FloatFormat.max_exp
  · rw [if_pos h_overflow] at hf; exact absurd hf (by simp)
  · rw [if_neg h_overflow] at hf
    -- Now in the else branch with let/match
    -- Inline the lets and rewrite findPredecessor/findSuccessor for positive x
    simp only [findPredecessor_pos_eq x hxpos, findSuccessor_pos_eq x hxpos] at hf
    -- Case split on findSuccessorPos result
    generalize hsucc : findSuccessorPos x hxpos = succ_val at hf
    cases succ_val with
    | finite s =>
      -- Force match reduction after cases
      dsimp only at hf
      split_ifs at hf with h1 h2 h3
      all_goals simp only [Fp.finite.injEq] at hf
      · left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos, Fp.finite.injEq]; exact hf
      · right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hsucc, Fp.finite.injEq]; exact hf
      · left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos, Fp.finite.injEq]; exact hf
      · right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hsucc, Fp.finite.injEq]; exact hf
    | infinite b => simp at hf
    | NaN => simp at hf

/-- **Machine Epsilon Bound for Round-Nearest-Ties-to-Even**: For positive x in the normal range,
the relative error of rounding to nearest (ties to even) is at most 2^(1-prec) (machine epsilon). -/
theorem roundNearestTiesToEven_relativeError_le (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundNearestTiesToEven x = Fp.finite f) :
    Fp.relativeError x f ≤ 2^(1 - (FloatFormat.prec : ℤ)) := by
  rcases roundNearestTiesToEven_is_roundDown_or_roundUp x hx f hf with h | h
  · exact roundDown_relativeError_le x hx f h
  · exact roundUp_relativeError_le x hx f h

/-- For positive x in the normal range, roundNearestTiesAwayFromZero returns either
    roundDown x or roundUp x (when the result is finite). -/
theorem roundNearestTiesAwayFromZero_is_roundDown_or_roundUp (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundNearestTiesAwayFromZero x = Fp.finite f) :
    roundDown x = Fp.finite f ∨ roundUp x = Fp.finite f := by
  have hxpos := isNormalRange_pos x hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have h_not_small : ¬(|x| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    intro h_abs
    rw [abs_of_pos hxpos] at h_abs
    have := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp (R := R)
    linarith [hx.left]
  unfold roundNearestTiesAwayFromZero at hf
  rw [if_neg hxne] at hf
  rw [if_neg h_not_small] at hf
  by_cases h_overflow : |x| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * 2 ^ FloatFormat.max_exp
  · rw [if_pos h_overflow] at hf; exact absurd hf (by simp)
  · rw [if_neg h_overflow] at hf
    simp only [findPredecessor_pos_eq x hxpos, findSuccessor_pos_eq x hxpos] at hf
    generalize hsucc : findSuccessorPos x hxpos = succ_val at hf
    cases succ_val with
    | finite s =>
      dsimp only at hf
      split_ifs at hf with h1 h2
      · -- x < midpoint → roundDown
        left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos, Fp.finite.injEq]
        simp only [Fp.finite.injEq] at hf; exact hf
      · -- x > midpoint → roundUp
        right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hsucc, Fp.finite.injEq]
        simp only [Fp.finite.injEq] at hf; exact hf
      · -- tie (x = midpoint), x > 0 resolved automatically → roundUp
        right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hsucc, Fp.finite.injEq]
        simp only [Fp.finite.injEq] at hf; exact hf
    | infinite b => simp at hf
    | NaN => simp at hf

/-- **Machine Epsilon Bound for Round-Nearest-Ties-Away**: For positive x in the normal range,
the relative error of rounding to nearest (ties away from zero) is at most 2^(1-prec) (machine epsilon). -/
theorem roundNearestTiesAwayFromZero_relativeError_le (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : roundNearestTiesAwayFromZero x = Fp.finite f) :
    Fp.relativeError x f ≤ 2^(1 - (FloatFormat.prec : ℤ)) := by
  rcases roundNearestTiesAwayFromZero_is_roundDown_or_roundUp x hx f hf with h | h
  · exact roundDown_relativeError_le x hx f h
  · exact roundUp_relativeError_le x hx f h

end Rounding
