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
import Flean.Gsplit.Gsplit
import Flean.Util

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

section isSubnormalRange

/-- Check if a positive number is in the subnormal range -/
def isSubnormalRange (x : R) : Prop :=
  0 < x ∧ x < (2 : R) ^ FloatFormat.min_exp


theorem isSubnormalRange_div_binade_upper {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {x : R} (h : isSubnormalRange x) :
    x / (2 : R)^(FloatFormat.min_exp - FloatFormat.prec + 1) < (2 : R)^((FloatFormat.prec : ℤ) - 1) := by
  unfold isSubnormalRange at h
  rw [div_lt_iff₀, ← zpow_add₀ (by norm_num)]
  norm_num
  exact h.right
  linearize

end isSubnormalRange


section isNormalRange

/-- Check if a positive number is in the normal range -/
def isNormalRange (x : R) : Prop :=
  (2 : R) ^ FloatFormat.min_exp ≤ x ∧ x < (2 : R) ^ (FloatFormat.max_exp + 1)

@[simp]
theorem isNormalRange_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) : isNormalRange x → 0 < x := by
  intro h
  have : (0 :R) < (2 : R) ^(FloatFormat.min_exp : ℤ) := by linearize
  apply lt_of_lt_of_le this h.left

-- theorem isNormalRange_isNormal_m (x : R) (h : isNormalRange x) : isNormal m

end isNormalRange

/-- Check if a positive number causes overflow -/
def isOverflow (x : R) : Prop :=
  (2 : R) ^ (FloatFormat.max_exp + 1) ≤ x


section findExponentDown

/-- Find the exponent for rounding down (largest e such that 2^e <= x) -/
def findExponentDown (x : R) : ℤ :=
  max (min (Int.log 2 x) FloatFormat.max_exp) FloatFormat.min_exp

theorem findExponentDown_min (x : R) : FloatFormat.min_exp ≤ findExponentDown x := by
  unfold findExponentDown
  simp only [le_sup_right]

theorem findExponentDown_max (x : R) : findExponentDown x ≤ FloatFormat.max_exp := by
  unfold findExponentDown
  simp only [sup_le_iff, inf_le_right, FloatFormat.exp_order_le, and_self]

theorem findExponentDown_normal (x : R) (h : isNormalRange x) : findExponentDown x = Int.log 2 x := by
  have xpos := isNormalRange_pos x h
  have ha₁ : Int.log 2 x < FloatFormat.max_exp + 1 := (Int.lt_zpow_iff_log_lt (by norm_num) xpos).mp h.right
  unfold findExponentDown
  rw [max_eq_left]
  rw [min_eq_left (by linarith)]
  rw [min_eq_left (by linarith)]
  apply (Int.zpow_le_iff_le_log (by norm_num) xpos).mp
  exact h.left

theorem findExponentDown_subnormal (x : R) (h : isSubnormalRange x) : findExponentDown x = FloatFormat.min_exp := by
  have hu : Int.log 2 x < FloatFormat.min_exp := by
    apply (Int.lt_zpow_iff_log_lt (by norm_num) h.left).mp
    exact h.right
  unfold findExponentDown
  rw [max_eq_right]
  rw [min_eq_left]
  · apply le_of_lt hu
  · apply le_of_lt
    apply lt_trans
    exact hu
    exact FloatFormat.exp_order

theorem findExponentDown_overflow (x : R) (h : isOverflow x) : findExponentDown x = FloatFormat.max_exp := by
  unfold findExponentDown
  unfold isOverflow at h
  have a1 := Int.log_mono_right (b := 2) ?_ h
  have a2 := Int.log_zpow (R := R) (b := 2) (by norm_num : 1 < 2) (FloatFormat.max_exp + 1)
  rw_mod_cast [a2] at a1
  rw [max_eq_left]
  rw [min_eq_right]
  · linarith
  · gsplit min with ha
    <;> flinarith
  · linearize

theorem findExponentDown_IsValidFiniteVal (x : R) (m : ℕ) (h : isNormal m ∨ isSubnormal (findExponentDown x) m) : IsValidFiniteVal (findExponentDown x) m := by
  unfold IsValidFiniteVal
  split_ands
  · apply findExponentDown_min
  · apply findExponentDown_max
  · cases h with
    | inl h => exact h.right
    | inr h =>
      have : 2 ^ (FloatFormat.prec - 1) - 1 < 2 ^ (FloatFormat.prec - 1) := by norm_num
      apply lt_of_le_of_lt h.right
      linarith [FloatFormat.valid_prec, FloatFormat.exp_order, FloatFormat.max_exp_pos, FloatFormat.min_exp_nonpos, FloatFormat.prec_pred_pow_le (R := R), FloatFormat.pow_prec_pred_lt]
  · exact h

theorem findExponentDown_IsValidFiniteVal_normal (x : R) (m : ℕ) (h : isNormal m) : IsValidFiniteVal (findExponentDown x) m := findExponentDown_IsValidFiniteVal x m (Or.inl h)

theorem findExponentDown_IsValidFiniteVal_subnormal (x : R) (m : ℕ) (h : isSubnormal (findExponentDown x) m) : IsValidFiniteVal (findExponentDown x) m := findExponentDown_IsValidFiniteVal x m (Or.inr h)

/-- A value in the normal range will have a binade within `1 ≤ e < 2` -/
theorem findExponentDown_div_binade_normal {x : R} (h : isNormalRange x) :
  (1 : R) ≤ x / ((2 : R)^(findExponentDown x)) ∧
  x / ((2 : R)^(findExponentDown x)) < (2 : R) := by
  have xpos := isNormalRange_pos x h
  rw [findExponentDown_normal x h]
  have hl : (2 : R) ^ (Int.log 2 x) ≤ x := by apply Int.zpow_log_le_self (by norm_num) xpos
  have hu : x < (2 : R)^(Int.log 2 x + 1) := by apply Int.lt_zpow_succ_log_self (by norm_num)
  split_ands
  · apply (one_le_div ?_).mpr (by trivial)
    linearize
  · apply (div_lt_iff₀ ?_).mpr
    rw [mul_comm]
    rw [← zpow_add_one₀ (by norm_num)]
    trivial
    linearize

theorem findExponentDown_div_binade_subnormal {x : R} (h : isSubnormalRange x) :
  0 < x / ((2 : R)^(findExponentDown x)) ∧
  x / ((2 : R)^(findExponentDown x)) < 1 := by
  rw [findExponentDown_subnormal x h]
  split_ands
  · apply div_pos h.left
    apply zpow_pos (by norm_num)
  · apply (div_lt_one ?_).mpr
    · exact h.right
    · linearize

theorem findExponentDown_div_binade_overflow {x : R} (h : isOverflow x) :
  2 ≤ x / ((2 : R)^(findExponentDown x)) := by
  rw [findExponentDown_overflow x h]
  unfold isOverflow at h
  apply (le_div_iff₀ ?_).mpr
  rw [← zpow_one_add₀ (by norm_num)]
  rw [add_comm]
  trivial
  linearize

end findExponentDown

end Rounding
