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
import Flean.Rounding.RoundDown
import Flean.Rounding.RoundUp

section Rounding
section RoundTowardZero

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]


/-- Round toward zero -/
def roundTowardZero [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if x > 0 then
    -- For positive x, round down (toward zero)
    roundDown x
  else
    -- For negative x, round up (toward zero)
    roundUp x

theorem roundTowardZero_mono [FloatFormat] {x y : R} (h : x ≤ y) : roundTowardZero x ≤ roundTowardZero y := by
  sorry

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

end Rounding
