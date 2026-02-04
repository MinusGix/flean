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

section Rounding
section RoundDown

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]


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

end Rounding
