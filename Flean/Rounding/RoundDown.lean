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

/-- Strengthened version: roundDown returns largestFiniteFloat for any x > largestFiniteFloat.toVal.
    This covers both x ≥ 2^(max_exp+1) (overflow range) and largestFiniteFloat.toVal < x < 2^(max_exp+1)
    (last binade where the floor gives the maximum significand). -/
theorem roundDown_gt_lff [FloatFormat] (x : R) (hn : 0 < x)
    (hgt : x > (FiniteFp.largestFiniteFloat.toVal : R)) :
    roundDown x = Fp.finite FiniteFp.largestFiniteFloat := by
  by_cases hge : x ≥ (2 : R) ^ (FloatFormat.max_exp + 1)
  · exact roundDown_gt_largestFiniteFloat x hn hge
  · -- x is in the last binade: largestFiniteFloat.toVal < x < 2^(max_exp+1)
    push_neg at hge
    -- Helper: 2^max_exp ≤ largestFiniteFloat.toVal
    have hlff_ge : (2 : R) ^ FloatFormat.max_exp ≤ FiniteFp.largestFiniteFloat.toVal := by
      rw [FiniteFp.largestFiniteFloat_toVal]
      calc (2 : R) ^ FloatFormat.max_exp
          = (2 : R) ^ FloatFormat.max_exp * 1 := by ring
        _ ≤ (2 : R) ^ FloatFormat.max_exp * ((2 : R) - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt (zpow_pos (by norm_num) _))
            have h1 : (0 : R) < (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := zpow_pos (by norm_num) _
            have h2 : (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) ≤ 1 := by
              calc (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) ≤ (2 : R) ^ (0 : ℤ) :=
                    zpow_le_zpow_right₀ (by norm_num) (by linarith [FloatFormat.valid_prec])
                _ = 1 := zpow_zero _
            linarith
    have hnr : isNormalRange x := ⟨le_trans (le_trans (zpow_le_zpow_right₀ (by norm_num)
      (by linarith [FloatFormat.exp_order])) hlff_ge) (le_of_lt hgt), hge⟩
    unfold roundDown findPredecessor
    simp [ne_of_gt hn, hn]
    unfold findPredecessorPos
    simp [not_lt.mpr hnr.1, hge]
    -- Now show roundNormalDown x = largestFiniteFloat
    have hlog : Int.log 2 x = FloatFormat.max_exp := by
      have h_lb := (Int.zpow_le_iff_le_log (by norm_num : 1 < 2) hn).mp
        (le_trans hlff_ge (le_of_lt hgt))
      have h_ub := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < 2) hn).mp hge
      omega
    have hefd : findExponentDown x = FloatFormat.max_exp := by
      rw [findExponentDown_normal x hnr, hlog]
    -- x > lff.toVal = (2^prec - 1) * 2^(max_exp - prec + 1)
    -- So x / 2^(max_exp - prec + 1) > 2^prec - 1
    -- And x / 2^(max_exp - prec + 1) < 2^prec (from x < 2^(max_exp+1))
    -- Therefore floor(x / ulp) = 2^prec - 1
    have hstep_pos : (0 : R) < (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) :=
      zpow_pos (by norm_num) _
    have hlff_eq : (FiniteFp.largestFiniteFloat.toVal : R) =
        ((2 : R) ^ FloatFormat.prec - 1) * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
      -- Both sides equal 2^(max_exp+1) - 2^(max_exp - prec + 1)
      rw [FiniteFp.largestFiniteFloat_toVal, sub_mul]
      -- LHS: 2^max_exp * (2 - 2^(-prec+1)) = 2^max_exp * 2 - 2^max_exp * 2^(-prec+1)
      rw [mul_sub]
      -- Need: 2^max_exp * 2 = 2^prec * 2^(max_exp - prec + 1)
      -- and: 2^max_exp * 2^(-prec+1) = 1 * 2^(max_exp - prec + 1)
      have h1 : (2 : R) ^ FloatFormat.max_exp * 2 = (2 : R) ^ FloatFormat.prec * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
        rw [mul_comm, show (2 : R) * (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ (FloatFormat.max_exp + 1) from by
          rw [show FloatFormat.max_exp + 1 = 1 + FloatFormat.max_exp from by ring, ← two_zpow_mul, zpow_one]]
        rw [two_zpow_mul]; congr 1; ring
      have h2 : (2 : R) ^ FloatFormat.max_exp * (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) =
          1 * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
        rw [one_mul, two_zpow_mul]; congr 1; ring
      rw [h1, h2]
    have hdiv_lb : (2 : R) ^ FloatFormat.prec - 1 < x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
      rw [lt_div_iff₀ hstep_pos]; linarith [hlff_eq]
    have hdiv_ub : x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) < (2 : R) ^ FloatFormat.prec := by
      rw [div_lt_iff₀ hstep_pos, two_zpow_mul]
      rw [show (FloatFormat.prec : ℤ) + (FloatFormat.max_exp - FloatFormat.prec + 1) = FloatFormat.max_exp + 1 from by ring]
      exact hge
    have hfloor_eq : ⌊x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1)⌋ =
        (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
      apply le_antisymm
      · have hlt : ⌊x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1)⌋ <
            (2 : ℤ) ^ FloatFormat.prec.toNat := by
          rw [Int.floor_lt]; push_cast
          rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]
          exact hdiv_ub
        omega
      · rw [Int.le_floor]; push_cast
        rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]
        linarith
    unfold roundNormalDown
    simp only
    rw [FiniteFp.eq_def]
    simp only [FiniteFp.largestFiniteFloat]
    rw [hefd, floor_scaled_eq_floor_div_ulp_step, hfloor_eq]
    have h4 := FloatFormat.nat_four_le_two_pow_prec
    refine ⟨trivial, rfl, ?_⟩
    -- natAbs of (2^prec.toNat - 1) = 2^prec.toNat - 1 (as ℕ)
    -- Lift to ℤ
    suffices h : ((2 : ℤ) ^ FloatFormat.prec.toNat - 1).natAbs = (2 ^ FloatFormat.prec.toNat - 1 : ℕ) from h
    zify [Nat.one_le_two_pow]
    have : (4 : ℤ) ≤ (2 : ℤ) ^ FloatFormat.prec.toNat := by exact_mod_cast h4
    rw [abs_of_nonneg (by omega)]

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
