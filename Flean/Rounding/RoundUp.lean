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
import Flean.Rounding.RoundDown

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
  -- The condition uses prec.toNat - 1 with (2 : ℤ)^n
  have h_k_lt : (2 : ℤ) ^ (FloatFormat.prec.toNat - 1) > 1 := by
    have hp := FloatFormat.valid_prec
    have h2 : FloatFormat.prec.toNat ≥ 2 := by
      apply (Int.le_toNat (by omega)).mpr
      exact FloatFormat.valid_prec
    have hne : FloatFormat.prec.toNat - 1 ≠ 0 := by omega
    have hnat : 1 < (2 : ℕ) ^ (FloatFormat.prec.toNat - 1) := Nat.one_lt_pow hne (by norm_num : 1 < 2)
    -- (2 : ℤ)^n = (↑(2 : ℕ))^n = ↑((2 : ℕ)^n) by Nat.cast_pow
    calc (2 : ℤ) ^ (FloatFormat.prec.toNat - 1)
        = ((2 : ℕ) ^ (FloatFormat.prec.toNat - 1) : ℤ) := by simp only [Nat.cast_ofNat]
      _ > 1 := by omega
  have h_not_ge : ¬((2 : ℤ) ^ (FloatFormat.prec.toNat - 1) ≤ 1) := not_le.mpr h_k_lt
  simp only [h_not_ge, ↓reduceDIte]
  rfl

/-- `nextUp` of zero is the smallest positive subnormal finite float. -/
@[simp] theorem nextUp_zero [FloatFormat] :
    nextUp (0 : Fp) = Fp.finite FiniteFp.smallestPosSubnormal := by
  have hpos : (0 : ℚ) < (FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2 := by
    have hssps_pos : (0 : ℚ) < (FiniteFp.smallestPosSubnormal.toVal : ℚ) :=
      FiniteFp.smallestPosSubnormal_toVal_pos
    positivity
  have hlt : ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) < FiniteFp.smallestPosSubnormal.toVal := by
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  simpa [nextUp, stepUpVal, neighborStep, FiniteFp.toVal_zero] using
    (roundUp_lt_smallestPosSubnormal
      ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hpos hlt)

/-- `nextDown` of zero is the negative smallest positive subnormal finite float. -/
@[simp] theorem nextDown_zero [FloatFormat] :
    nextDown (0 : Fp) = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
  have hpos : (0 : ℚ) < (FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2 := by
    have hssps_pos : (0 : ℚ) < (FiniteFp.smallestPosSubnormal.toVal : ℚ) :=
      FiniteFp.smallestPosSubnormal_toVal_pos
    positivity
  have hneg : -((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) < 0 := by linarith
  have hsucc : findSuccessorPos ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hpos =
      Fp.finite FiniteFp.smallestPosSubnormal := by
    have hlt : ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) < FiniteFp.smallestPosSubnormal.toVal := by
      linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
    have hsucc' : findSuccessor ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) =
        Fp.finite FiniteFp.smallestPosSubnormal := by
      simpa [roundUp] using
        (roundUp_lt_smallestPosSubnormal
          ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hpos hlt)
    simpa [findSuccessor_pos_eq ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hpos] using hsucc'
  calc
    nextDown (0 : Fp)
        = findPredecessor (-((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2)) := by
          simp [nextDown, stepDownVal, neighborStep, FiniteFp.toVal_zero]
    _ = -(findSuccessorPos ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hpos) := by
          simpa using (findPredecessor_neg_eq (-((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2)) hneg)
    _ = -(Fp.finite FiniteFp.smallestPosSubnormal) := by rw [hsucc]
    _ = Fp.finite (-FiniteFp.smallestPosSubnormal) := by simp

/-- Signed-zero behavior: `nextUp(-0) = smallestPosSubnormal`. -/
@[simp] theorem nextUp_neg_zero [FloatFormat] :
    nextUp (Fp.finite (-0 : FiniteFp)) = Fp.finite FiniteFp.smallestPosSubnormal := by
  have hpos : (0 : ℚ) < (FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2 := by
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hlt : ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) < FiniteFp.smallestPosSubnormal.toVal := by
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  simpa [nextUp_finite, stepUpVal, neighborStep] using
    (roundUp_lt_smallestPosSubnormal
      ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hpos hlt)

/-- Signed-zero behavior: `nextDown(-0) = -smallestPosSubnormal`. -/
@[simp] theorem nextDown_neg_zero [FloatFormat] :
    nextDown (Fp.finite (-0 : FiniteFp)) = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
  calc
    nextDown (Fp.finite (-0 : FiniteFp))
        = nextDown (Fp.finite (0 : FiniteFp)) := by
          simp [nextDown_finite, stepDownVal, neighborStep]
    _ = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
          exact (nextDown_zero)

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

/-- `nextUp` of the largest finite float overflows to `+∞`. -/
@[simp] theorem nextUp_largestFiniteFloat [FloatFormat] :
    nextUp (Fp.finite FiniteFp.largestFiniteFloat) = Fp.infinite false := by
  have hpos : (0 : ℚ) < stepUpVal FiniteFp.largestFiniteFloat := by
    unfold stepUpVal neighborStep
    linarith [FiniteFp.largestFiniteFloat_toVal_pos (R := ℚ),
      FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hgt : (FiniteFp.largestFiniteFloat.toVal : ℚ) < stepUpVal FiniteFp.largestFiniteFloat := by
    unfold stepUpVal neighborStep
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hru : roundUp (stepUpVal FiniteFp.largestFiniteFloat) = Fp.infinite false :=
    roundUp_gt_largestFiniteFloat (R := ℚ) (stepUpVal FiniteFp.largestFiniteFloat) hpos hgt
  simpa [roundUp, nextUp_finite] using hru

/-- `nextDown` of the most-negative finite float underflows to `-∞`. -/
@[simp] theorem nextDown_neg_largestFiniteFloat [FloatFormat] :
    nextDown (Fp.finite (-FiniteFp.largestFiniteFloat)) = Fp.infinite true := by
  have hxneg : stepDownVal (-FiniteFp.largestFiniteFloat) < 0 := by
    unfold stepDownVal neighborStep
    rw [FiniteFp.toVal_neg_eq_neg]
    linarith [FiniteFp.largestFiniteFloat_toVal_pos (R := ℚ),
      FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hxpos : (0 : ℚ) < -stepDownVal (-FiniteFp.largestFiniteFloat) := by linarith
  have hgt : (FiniteFp.largestFiniteFloat.toVal : ℚ) <
      -stepDownVal (-FiniteFp.largestFiniteFloat) := by
    unfold stepDownVal neighborStep
    rw [FiniteFp.toVal_neg_eq_neg]
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hsucc : findSuccessor (-stepDownVal (-FiniteFp.largestFiniteFloat)) = Fp.infinite false := by
    simpa [roundUp] using
      (roundUp_gt_largestFiniteFloat (R := ℚ) (-stepDownVal (-FiniteFp.largestFiniteFloat)) hxpos hgt)
  have hsuccPos : findSuccessorPos (-stepDownVal (-FiniteFp.largestFiniteFloat)) hxpos = Fp.infinite false := by
    have hsucc' := hsucc
    rw [findSuccessor_pos_eq (-stepDownVal (-FiniteFp.largestFiniteFloat)) hxpos] at hsucc'
    exact hsucc'
  calc
    nextDown (Fp.finite (-FiniteFp.largestFiniteFloat))
        = findPredecessor (stepDownVal (-FiniteFp.largestFiniteFloat)) := by
          simpa using (nextDown_finite (-FiniteFp.largestFiniteFloat))
    _ = -(findSuccessorPos (-stepDownVal (-FiniteFp.largestFiniteFloat)) hxpos) := by
          simpa using (findPredecessor_neg_eq (stepDownVal (-FiniteFp.largestFiniteFloat)) hxneg)
    _ = -(Fp.infinite false) := by rw [hsuccPos]
    _ = Fp.infinite true := by simp

/-- `nextDown` of the smallest positive subnormal is `+0`. -/
@[simp] theorem nextDown_smallestPosSubnormal [FloatFormat] :
    nextDown (Fp.finite FiniteFp.smallestPosSubnormal) = Fp.finite 0 := by
  have hpos : (0 : ℚ) < stepDownVal FiniteFp.smallestPosSubnormal := by
    unfold stepDownVal neighborStep
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hlt : stepDownVal FiniteFp.smallestPosSubnormal < FiniteFp.smallestPosSubnormal.toVal := by
    unfold stepDownVal neighborStep
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hrd : roundDown (stepDownVal FiniteFp.smallestPosSubnormal) = Fp.finite 0 := by
    exact roundDown_lt_smallestPosSubnormal (R := ℚ) (stepDownVal FiniteFp.smallestPosSubnormal) hpos hlt
  simpa [roundDown, nextDown_finite] using hrd

/-- `nextUp` of the negative smallest positive subnormal is `-0`. -/
@[simp] theorem nextUp_neg_smallestPosSubnormal [FloatFormat] :
    nextUp (Fp.finite (-FiniteFp.smallestPosSubnormal)) = Fp.finite (-0) := by
  have hhalf_pos : (0 : ℚ) < (FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2 := by
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hhalf_lt : ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) <
      FiniteFp.smallestPosSubnormal.toVal := by
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hpred_half : findPredecessor ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) = Fp.finite 0 := by
    simpa [roundDown] using
      (roundDown_lt_smallestPosSubnormal (R := ℚ)
        ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hhalf_pos hhalf_lt)
  have hpredPos : findPredecessorPos ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hhalf_pos = 0 := by
    have hpred_half' : Fp.finite (findPredecessorPos ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hhalf_pos) =
        Fp.finite 0 := by
      simpa [findPredecessor_pos_eq ((FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2) hhalf_pos] using hpred_half
    exact Fp.finite.inj hpred_half'
  have hxneg : stepUpVal (-FiniteFp.smallestPosSubnormal) < 0 := by
    unfold stepUpVal neighborStep
    rw [FiniteFp.toVal_neg_eq_neg]
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hneg_step : -stepUpVal (-FiniteFp.smallestPosSubnormal) =
      (FiniteFp.smallestPosSubnormal.toVal : ℚ) / 2 := by
    unfold stepUpVal neighborStep
    rw [FiniteFp.toVal_neg_eq_neg]
    ring
  have hpredPos' : findPredecessorPos (-stepUpVal (-FiniteFp.smallestPosSubnormal))
      (neg_pos.mpr hxneg) = 0 := by
    simpa [hneg_step] using hpredPos
  calc
    nextUp (Fp.finite (-FiniteFp.smallestPosSubnormal))
        = findSuccessor (stepUpVal (-FiniteFp.smallestPosSubnormal)) := by
          simpa using (nextUp_finite (-FiniteFp.smallestPosSubnormal))
    _ = Fp.finite (-findPredecessorPos (-stepUpVal (-FiniteFp.smallestPosSubnormal)) (neg_pos.mpr hxneg)) := by
          simpa using (findSuccessor_neg_eq (stepUpVal (-FiniteFp.smallestPosSubnormal)) hxneg)
    _ = Fp.finite (-0) := by rw [hpredPos']

/-! ## Directed Idempotence Helpers (moved from `Idempotence`) -/

section DirectedIdempotence

variable [FloatFormat]

omit [FloorRing R] in
/-- For a positive normal float, its toVal lies in [2^e, 2^(e+1)). -/
theorem toVal_normal_bounds (f : FiniteFp) (hs : f.s = false) (hn : isNormal f.m) :
    (2 : R) ^ f.e ≤ f.toVal ∧ f.toVal < (2 : R) ^ (f.e + 1) := by
  have hm_lb := hn.1
  have hm_ub := hn.2
  have hstep_pos : (0 : R) < (2 : R) ^ (f.e - FloatFormat.prec + 1) := two_zpow_pos' _
  have htoVal : f.toVal (R := R) = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp [hs]
  rw [htoVal]
  constructor
  · calc (2 : R) ^ f.e
        = (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
          rw [two_zpow_mul]; congr 1; ring
      _ ≤ (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hstep_pos)
          calc (2 : R) ^ (FloatFormat.prec - 1)
              = (2 : R) ^ (FloatFormat.prec - 1).toNat := FloatFormat.pow_prec_sub_one_nat_int.symm
            _ ≤ (f.m : R) := by exact_mod_cast hm_lb
  · calc (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)
        < (2 : R) ^ FloatFormat.prec * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
          apply mul_lt_mul_of_pos_right _ hstep_pos
          calc (f.m : R) < (2 : R) ^ FloatFormat.prec.toNat := by exact_mod_cast hm_ub
            _ = (2 : R) ^ FloatFormat.prec := by
                rw [← zpow_natCast]; congr 1; exact FloatFormat.prec_toNat_eq
      _ = (2 : R) ^ (f.e + 1) := by
          rw [two_zpow_mul]; congr 1; ring

/-- For a positive normal float, Int.log 2 of its toVal equals its exponent. -/
theorem Int_log_of_normal_toVal (f : FiniteFp) (hs : f.s = false) (hn : isNormal f.m) :
    Int.log 2 (f.toVal (R := R)) = f.e := by
  have hbounds := toVal_normal_bounds (R := R) f hs hn
  have hpos : (0 : R) < f.toVal := lt_of_lt_of_le (two_zpow_pos' f.e) hbounds.1
  have hlog_lb : f.e ≤ Int.log 2 (f.toVal (R := R)) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < 2) hpos).mp hbounds.1
  have hlog_ub : Int.log 2 (f.toVal (R := R)) < f.e + 1 :=
    (Int.lt_zpow_iff_log_lt (by norm_num : 1 < 2) hpos).mp hbounds.2
  omega

/-- For a positive normal float, findExponentDown of its toVal equals its exponent. -/
theorem findExponentDown_of_normal_toVal (f : FiniteFp) (hs : f.s = false) (hn : isNormal f.m) :
    findExponentDown (f.toVal (R := R)) = f.e := by
  have hbounds := toVal_normal_bounds (R := R) f hs hn
  have hnr : isNormalRange (f.toVal (R := R)) := by
    constructor
    · calc (2 : R) ^ FloatFormat.min_exp
          ≤ (2 : R) ^ f.e := two_zpow_mono f.valid_min_exp
        _ ≤ f.toVal := hbounds.1
    · calc f.toVal
          < (2 : R) ^ (f.e + 1) := hbounds.2
        _ ≤ (2 : R) ^ (FloatFormat.max_exp + 1) :=
            two_zpow_mono (by linarith [f.valid_max_exp])
  rw [findExponentDown_normal _ hnr, Int_log_of_normal_toVal f hs hn]

omit [FloorRing R] in
/-- The scaled significand of a normal positive float equals its significand. -/
theorem scaled_significand_eq_m (f : FiniteFp) (hs : f.s = false) :
    f.toVal (R := R) / (2 : R) ^ f.e * (2 : R) ^ (FloatFormat.prec - 1) = (f.m : R) := by
  have htoVal : f.toVal (R := R) = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp [hs]
  rw [htoVal, mul_two_zpow_div_two_zpow, mul_two_zpow_right]
  have : f.e - FloatFormat.prec + 1 - f.e + (FloatFormat.prec - 1) = 0 := by ring
  rw [this, zpow_zero, mul_one]

omit [FloorRing R] in
private theorem toVal_normal_isNormalRange (f : FiniteFp) (hs : f.s = false) (hn : isNormal f.m) :
    isNormalRange (f.toVal (R := R)) := by
  have hbounds := toVal_normal_bounds (R := R) f hs hn
  constructor
  · calc (2 : R) ^ FloatFormat.min_exp
        ≤ (2 : R) ^ f.e := two_zpow_mono f.valid_min_exp
      _ ≤ f.toVal := hbounds.1
  · calc f.toVal
        < (2 : R) ^ (f.e + 1) := hbounds.2
      _ ≤ (2 : R) ^ (FloatFormat.max_exp + 1) :=
          two_zpow_mono (by linarith [f.valid_max_exp])

/-- Rounding a normal positive float down gives back the same float. -/
theorem roundNormalDown_of_normal_toVal (f : FiniteFp) (hs : f.s = false) (hn : isNormal f.m)
    (hr : isNormalRange (f.toVal (R := R))) :
    roundNormalDown (f.toVal (R := R)) hr = f := by
  unfold roundNormalDown
  simp only
  have heq : findExponentDown (f.toVal (R := R)) = f.e :=
    findExponentDown_of_normal_toVal f hs hn
  have hscaled : (f.toVal (R := R)) / (2 : R) ^ findExponentDown (f.toVal (R := R)) *
      (2 : R) ^ (FloatFormat.prec - 1) = (f.m : R) := by
    rw [heq]
    exact scaled_significand_eq_m f hs
  have hfloor : ⌊(f.m : R)⌋ = (f.m : ℤ) := Int.floor_natCast f.m
  have hnatabs : (f.m : ℤ).natAbs = f.m := Int.natAbs_natCast f.m
  conv_lhs => simp only [hscaled, hfloor]
  rw [FiniteFp.eq_def]
  exact ⟨hs.symm, heq, hnatabs⟩

omit [FloorRing R] in
/-- For a positive subnormal float with m > 0, its toVal is in the subnormal range. -/
theorem toVal_subnormal_isSubnormalRange (f : FiniteFp) (hs : f.s = false)
    (hsub : isSubnormal f.e f.m) (hm : 0 < f.m) :
    isSubnormalRange (f.toVal (R := R)) := by
  have he : f.e = FloatFormat.min_exp := hsub.1
  have htoVal : f.toVal (R := R) = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp [hs]
  rw [htoVal]
  constructor
  · apply mul_pos
    · exact_mod_cast hm
    · exact two_zpow_pos' _
  · rw [he]
    have hm_lt : (f.m : R) < (2 : R) ^ (FloatFormat.prec - 1) := by
      have hm_lt_nat : f.m < 2 ^ (FloatFormat.prec - 1).toNat := by omega
      calc (f.m : R) < (2 : R) ^ (FloatFormat.prec - 1).toNat := by exact_mod_cast hm_lt_nat
        _ = (2 : R) ^ (FloatFormat.prec - 1) := FloatFormat.pow_prec_sub_one_nat_int
    calc (f.m : R) * (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
        < (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) :=
          mul_lt_mul_of_pos_right hm_lt (two_zpow_pos' _)
      _ = (2 : R) ^ FloatFormat.min_exp := by
          rw [two_zpow_mul]; congr 1; ring

omit [FloorRing R] in
/-- f.toVal / 2^(min_exp - prec + 1) = f.m for a subnormal float. -/
theorem subnormal_toVal_div_ulp_eq_m (f : FiniteFp) (hs : f.s = false)
    (hsub : isSubnormal f.e f.m) :
    f.toVal (R := R) / (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) = (f.m : R) := by
  have he : f.e = FloatFormat.min_exp := hsub.1
  have htoVal : f.toVal (R := R) = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp [hs]
  rw [htoVal, he, mul_div_cancel_right₀ _ (two_zpow_ne_zero _)]

/-- Rounding a subnormal positive float down gives back the same float. -/
theorem roundSubnormalDown_of_subnormal_toVal (f : FiniteFp) (hs : f.s = false)
    (hsub : isSubnormal f.e f.m) (hm : 0 < f.m)
    (hr : isSubnormalRange (f.toVal (R := R))) :
    roundSubnormalDown (f.toVal (R := R)) hr = f := by
  unfold roundSubnormalDown
  simp only
  have he : f.e = FloatFormat.min_exp := hsub.1
  have hdiv : f.toVal (R := R) / (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) = (f.m : R) :=
    subnormal_toVal_div_ulp_eq_m f hs hsub
  have hfloor : ⌊(f.m : R)⌋ = (f.m : ℤ) := Int.floor_natCast f.m
  have hk_eq : ⌊f.toVal (R := R) / (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)⌋ = (f.m : ℤ) := by
    rw [hdiv, hfloor]
  have hk_ne_zero : (f.m : ℤ) ≠ 0 := by omega
  conv_lhs => simp only [hk_eq]
  simp only [hk_ne_zero, ↓reduceDIte]
  have hnatabs : (f.m : ℤ).natAbs = f.m := Int.natAbs_natCast f.m
  rw [FiniteFp.eq_def]
  exact ⟨hs.symm, he.symm, hnatabs⟩

/-- For a non-negative-zero float, roundDown gives back the same float. -/
theorem roundDown_idempotent_nonneg (f : FiniteFp) (hs : f.s = false) (hm : 0 < f.m) :
    roundDown (f.toVal (R := R)) = Fp.finite f := by
  have hfpos : (0 : R) < f.toVal := FiniteFp.toVal_pos f hs hm
  unfold roundDown findPredecessor
  simp only [ne_of_gt hfpos, ↓reduceDIte, hfpos, Fp.finite.injEq]
  unfold findPredecessorPos
  rcases f.isNormal_or_isSubnormal with hnormal | hsubnormal
  · have hnr := toVal_normal_isNormalRange (R := R) f hs hnormal
    have h_not_sub : ¬(f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp) := not_lt.mpr hnr.1
    have h_not_over : f.toVal (R := R) < (2 : R) ^ (FloatFormat.max_exp + 1) := hnr.2
    simp only [h_not_sub, ↓reduceDIte, h_not_over]
    exact roundNormalDown_of_normal_toVal f hs hnormal hnr
  · have hsr := toVal_subnormal_isSubnormalRange (R := R) f hs hsubnormal hm
    have h_sub : f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp := hsr.2
    simp only [h_sub, ↓reduceDIte]
    exact roundSubnormalDown_of_subnormal_toVal f hs hsubnormal hm hsr

/-- Rounding a normal positive float up gives back the same float (as Fp.finite). -/
theorem roundNormalUp_of_normal_toVal (f : FiniteFp) (hs : f.s = false) (hn : isNormal f.m)
    (hr : isNormalRange (f.toVal (R := R))) :
    roundNormalUp (f.toVal (R := R)) hr = Fp.finite f := by
  unfold roundNormalUp
  simp only
  have heq : findExponentDown (f.toVal (R := R)) = f.e :=
    findExponentDown_of_normal_toVal f hs hn
  have hscaled : (f.toVal (R := R)) / (2 : R) ^ findExponentDown (f.toVal (R := R)) *
      (2 : R) ^ (FloatFormat.prec - 1) = (f.m : R) := by
    rw [heq]; exact scaled_significand_eq_m f hs
  have hceil : ⌈(f.m : R)⌉ = (f.m : ℤ) := Int.ceil_natCast f.m
  have h_no_overflow : ¬((2 : ℤ) ^ FloatFormat.prec.toNat ≤ (f.m : ℤ)) := by
    push_neg; exact_mod_cast hn.2
  conv_lhs => simp only [hscaled, hceil]
  simp only [h_no_overflow, ↓reduceDIte, Fp.finite.injEq]
  have hnatabs : (f.m : ℤ).natAbs = f.m := Int.natAbs_natCast f.m
  rw [FiniteFp.eq_def]
  exact ⟨hs.symm, heq, hnatabs⟩

/-- Rounding a subnormal positive float up gives back the same float. -/
theorem roundSubnormalUp_of_subnormal_toVal (f : FiniteFp) (hs : f.s = false)
    (hsub : isSubnormal f.e f.m) (hm : 0 < f.m)
    (hr : isSubnormalRange (f.toVal (R := R))) :
    roundSubnormalUp (f.toVal (R := R)) hr = f := by
  unfold roundSubnormalUp
  simp only
  have he : f.e = FloatFormat.min_exp := hsub.1
  have hdiv : f.toVal (R := R) / (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) = (f.m : R) :=
    subnormal_toVal_div_ulp_eq_m f hs hsub
  have hceil : ⌈(f.m : R)⌉ = (f.m : ℤ) := Int.ceil_natCast f.m
  have hk_eq : ⌈f.toVal (R := R) / (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)⌉ = (f.m : ℤ) := by
    rw [hdiv, hceil]
  conv_lhs => simp only [hk_eq]
  have h_no_transition : ¬((2 : ℤ) ^ (FloatFormat.prec - 1).toNat ≤ (f.m : ℤ)) := by
    push_neg
    have : f.m < 2 ^ (FloatFormat.prec - 1).toNat := by omega
    exact_mod_cast this
  simp only [h_no_transition, ↓reduceDIte]
  have hnatabs : (f.m : ℤ).natAbs = f.m := Int.natAbs_natCast f.m
  rw [FiniteFp.eq_def]
  exact ⟨hs.symm, he.symm, hnatabs⟩

/-- For a positive float, roundUp gives back the same float. -/
theorem roundUp_idempotent_nonneg (f : FiniteFp) (hs : f.s = false) (hm : 0 < f.m) :
    roundUp (f.toVal (R := R)) = Fp.finite f := by
  have hfpos : (0 : R) < f.toVal := FiniteFp.toVal_pos f hs hm
  unfold roundUp findSuccessor
  simp only [ne_of_gt hfpos, ↓reduceDIte, hfpos]
  unfold findSuccessorPos
  rcases f.isNormal_or_isSubnormal with hnormal | hsubnormal
  · have hnr := toVal_normal_isNormalRange (R := R) f hs hnormal
    have h_not_sub : ¬(f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp) := not_lt.mpr hnr.1
    have h_not_over : f.toVal (R := R) < (2 : R) ^ (FloatFormat.max_exp + 1) := hnr.2
    simp only [h_not_sub, ↓reduceDIte, h_not_over]
    exact roundNormalUp_of_normal_toVal f hs hnormal hnr
  · have hsr := toVal_subnormal_isSubnormalRange (R := R) f hs hsubnormal hm
    have h_sub : f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp := hsr.2
    simp only [h_sub, ↓reduceDIte, Fp.finite.injEq]
    exact roundSubnormalUp_of_subnormal_toVal f hs hsubnormal hm hsr

/-- For a negative float with m > 0, roundDown gives back the same float. -/
theorem roundDown_idempotent_neg (f : FiniteFp) (hs : f.s = true) (hm : 0 < f.m) :
    roundDown (f.toVal (R := R)) = Fp.finite f := by
  have hnf_s : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
  have hnf_m : 0 < (-f).m := by rw [FiniteFp.neg_def]; exact hm
  have hnf_pos : (0 : R) < (-f).toVal := FiniteFp.toVal_pos (-f) hnf_s hnf_m
  have hfneg : f.toVal (R := R) < 0 := by
    rw [FiniteFp.toVal_neg_eq_neg] at hnf_pos; linarith
  rw [roundDown, findPredecessor_neg_eq _ hfneg]
  have hup := roundUp_idempotent_nonneg (R := R) (-f) hnf_s hnf_m
  rw [roundUp, findSuccessor_pos_eq _ hnf_pos] at hup
  have key : findSuccessorPos (-f.toVal (R := R)) (neg_pos.mpr hfneg) =
             findSuccessorPos ((-f).toVal (R := R)) hnf_pos := by
    congr 1; rw [FiniteFp.toVal_neg_eq_neg]
  rw [key, hup, Fp.neg_finite, neg_neg]

/-- For a negative float with m > 0, roundUp gives back the same float. -/
theorem roundUp_idempotent_neg (f : FiniteFp) (hs : f.s = true) (hm : 0 < f.m) :
    roundUp (f.toVal (R := R)) = Fp.finite f := by
  have hnf_s : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
  have hnf_m : 0 < (-f).m := by rw [FiniteFp.neg_def]; exact hm
  have hnf_pos : (0 : R) < (-f).toVal := FiniteFp.toVal_pos (-f) hnf_s hnf_m
  have hfneg : f.toVal (R := R) < 0 := by
    rw [FiniteFp.toVal_neg_eq_neg] at hnf_pos; linarith
  rw [roundUp, findSuccessor_neg_eq _ hfneg]
  have hdown := roundDown_idempotent_nonneg (R := R) (-f) hnf_s hnf_m
  rw [roundDown, findPredecessor_pos_eq _ hnf_pos, Fp.finite.injEq] at hdown
  have key : findPredecessorPos (-f.toVal (R := R)) (neg_pos.mpr hfneg) =
             findPredecessorPos ((-f).toVal (R := R)) hnf_pos := by
    congr 1; rw [FiniteFp.toVal_neg_eq_neg]
  rw [Fp.finite.injEq, key, hdown, neg_neg]

/-- Helper: if f.m = 0 and f.s = false, then f = 0. -/
theorem eq_zero_of_sign_false_m_zero (f : FiniteFp) (hs : f.s = false) (hm : f.m = 0) :
    f = (0 : FiniteFp) := by
  ext
  · exact hs
  · have := f.isNormal_or_isSubnormal
    rcases this with hn | hsub
    · exfalso
      have := hn.1
      have : 0 < 2 ^ (FloatFormat.prec - 1).toNat := Nat.pos_of_ne_zero (by positivity)
      omega
    · exact hsub.1
  · exact hm

/-- roundDown is idempotent on non-negative-zero floats. -/
theorem roundDown_idempotent (f : FiniteFp) (h : f.s = false ∨ 0 < f.m) :
    roundDown (f.toVal (R := R)) = Fp.finite f := by
  rcases h with hs | hm
  · by_cases hm : 0 < f.m
    · exact roundDown_idempotent_nonneg f hs hm
    · push_neg at hm
      have hm0 : f.m = 0 := by omega
      rw [eq_zero_of_sign_false_m_zero f hs hm0, FiniteFp.toVal_zero, roundDown_zero]
  · by_cases hs : f.s = false
    · exact roundDown_idempotent_nonneg f hs hm
    · have hs_true : f.s = true := by revert hs; cases f.s <;> simp
      exact roundDown_idempotent_neg f hs_true hm

/-- roundUp is idempotent on non-negative-zero floats. -/
theorem roundUp_idempotent (f : FiniteFp) (h : f.s = false ∨ 0 < f.m) :
    roundUp (f.toVal (R := R)) = Fp.finite f := by
  rcases h with hs | hm
  · by_cases hm : 0 < f.m
    · exact roundUp_idempotent_nonneg f hs hm
    · push_neg at hm
      have hm0 : f.m = 0 := by omega
      rw [eq_zero_of_sign_false_m_zero f hs hm0, FiniteFp.toVal_zero, roundUp_zero]
  · by_cases hs : f.s = false
    · exact roundUp_idempotent_nonneg f hs hm
    · have hs_true : f.s = true := by revert hs; cases f.s <;> simp
      exact roundUp_idempotent_neg f hs_true hm

end DirectedIdempotence

/-- `roundUp` of a positive value `mag * 2^e_base` produces a float with significand
`⌈val / 2^e_ulp⌉` in the no-carry case (q+1 < 2^prec).

Mirror of `roundDown_nat_mul_zpow` for the ceiling direction. -/
private lemma isValid_roundUpNatMulZpowTarget [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (_hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hceil : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1)
    (_hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq1_bound : q + 1 < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    IsValidFiniteVal (e_ulp + FloatFormat.prec - 1) (q + 1) := by
  refine ⟨by omega, by omega, hq1_bound, ?_⟩
  by_cases hn : 2 ^ (FloatFormat.prec - 1).toNat ≤ q + 1
  · left; exact ⟨hn, hq1_bound⟩
  · right; push_neg at hn; constructor
    · by_contra h_ne
      have h_gt : e_ulp + FloatFormat.prec - 1 > FloatFormat.min_exp := by omega
      have h_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
        rw [h_e_ulp_eq]; apply max_eq_left; omega
      have hval_ge_binade : (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) ≤
          (mag : R) * (2 : R) ^ e_base := by
        rw [← two_zpow_mul, zpow_natCast]
        apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num) _)
        rw [← Nat.cast_ofNat, ← Nat.cast_pow]
        exact_mod_cast Nat.log2_self_le hmag
      have he_eq : e_ulp = (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 := by
        push_cast at h_normal ⊢; omega
      have hq_ge_prec : (2 : R) ^ (FloatFormat.prec - 1) ≤
          (mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp := by
        rw [le_div_iff₀ (zpow_pos (by norm_num) _)]
        calc (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e_ulp
            = (2 : R) ^ ((FloatFormat.prec - 1) + e_ulp) := by rw [two_zpow_mul]
          _ = (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) := by congr 1; rw [he_eq]; ring
          _ ≤ (mag : R) * (2 : R) ^ e_base := hval_ge_binade
      have hq1_ge_z : (q : ℤ) + 1 ≥ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
        rw [← hceil]
        exact Int.le_ceil_iff.mpr (by
          push_cast
          rw [← zpow_natCast (2 : R) (FloatFormat.prec - 1).toNat,
            FloatFormat.prec_sub_one_toNat_eq]
          linarith [hq_ge_prec])
      have : 2 ^ (FloatFormat.prec - 1).toNat ≤ q + 1 := by zify; exact hq1_ge_z
      omega
    · omega

private def mkRoundUpNatMulZpowTarget [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hceil : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1)
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq1_bound : q + 1 < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    FiniteFp :=
  ⟨false, e_ulp + FloatFormat.prec - 1, q + 1,
    isValid_roundUpNatMulZpowTarget
      (R := R) mag e_base e_ulp q
      hmag hval_pos hceil hint_log he_ulp_ge_sub he_stored_le hq1_bound h_e_ulp_eq⟩

private abbrev roundUpNatMulZpowTarget [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hceil : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1)
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq1_bound : q + 1 < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    Fp :=
  Fp.finite <|
    mkRoundUpNatMulZpowTarget
      (R := R) mag e_base e_ulp q
      hmag hval_pos hceil hint_log he_ulp_ge_sub he_stored_le hq1_bound h_e_ulp_eq

theorem roundUp_nat_mul_zpow [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hval_lt : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1))
    (hceil : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1)
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq1_bound : q + 1 < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    roundUp ((mag : R) * (2 : R) ^ e_base) =
      Fp.finite (mkRoundUpNatMulZpowTarget
        (R := R) mag e_base e_ulp q
        hmag hval_pos hceil hint_log he_ulp_ge_sub he_stored_le hq1_bound h_e_ulp_eq) := by
  unfold mkRoundUpNatMulZpowTarget
  unfold roundUp findSuccessor
  simp [ne_of_gt hval_pos, hval_pos]
  unfold findSuccessorPos
  by_cases h_sub : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ FloatFormat.min_exp
  · -- SUBNORMAL CASE
    simp [h_sub]
    unfold roundSubnormalUp
    have he_ulp_sub : e_ulp = FloatFormat.min_exp - FloatFormat.prec + 1 := by
      rw [h_e_ulp_eq]; apply max_eq_right
      have h_log_lt : (Nat.log2 mag : ℤ) + e_base < FloatFormat.min_exp := by
        rw [← hint_log]
        exact (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2:ℕ)) hval_pos).mp
          (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
      omega
    have hceil_sub : ⌈(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌉ = (q : ℤ) + 1 := by
      rw [← he_ulp_sub]; exact hceil
    -- val < 2^min_exp and ulp_sub = 2^(min_exp-prec+1), so val/ulp < 2^(prec-1)
    -- ⌈val/ulp⌉ ≤ 2^(prec-1), giving q+1 ≤ 2^(prec-1)
    have hval_div_le : (mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) ≤
        (2 : R) ^ (FloatFormat.prec - 1) := by
      rw [div_le_iff₀ (zpow_pos (by norm_num : (0:R) < 2) _)]
      have h2 : (2 : R) ^ (FloatFormat.prec - 1) *
          (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) =
          (2 : R) ^ FloatFormat.min_exp := by
        rw [two_zpow_mul]; congr 1; ring
      rw [h2]; linarith [h_sub]
    have hq1_le_half : (q : ℤ) + 1 ≤ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
      rw [← hceil_sub]
      apply Int.ceil_le.mpr
      push_cast
      rw [← zpow_natCast (2 : R) (FloatFormat.prec - 1).toNat,
          FloatFormat.prec_sub_one_toNat_eq]
      exact hval_div_le
    have he_stored : e_ulp + FloatFormat.prec - 1 = FloatFormat.min_exp := by
      rw [he_ulp_sub]; ring
    simp only [hceil_sub]
    by_cases hk_ge : (q : ℤ) + 1 ≥ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat
    · -- q + 1 = 2^(prec-1): roundSubnormalUp returns smallestPosNormal
      simp only [hk_ge, ↓reduceDIte]
      have hq1_eq : (q : ℤ) + 1 = (2 : ℤ) ^ (FloatFormat.prec - 1).toNat :=
        le_antisymm hq1_le_half hk_ge
      -- smallestPosNormal = ⟨false, min_exp, 2^(prec-1).toNat, _⟩
      -- Our target = ⟨false, e_ulp+prec-1, q+1, _⟩ = ⟨false, min_exp, 2^(prec-1).toNat, _⟩
      unfold FiniteFp.smallestPosNormal
      congr 1
      · exact he_stored.symm
      · -- q + 1 = 2^(prec-1).toNat in ℕ
        have : q + 1 = 2 ^ (FloatFormat.prec - 1).toNat := by
          zify; exact hq1_eq
        omega
    · -- q + 1 < 2^(prec-1): roundSubnormalUp returns ⟨false, min_exp, (q+1).natAbs, _⟩
      simp only [hk_ge, ↓reduceDIte]
      have hnatabs : ((q : ℤ) + 1).natAbs = q + 1 := by
        rw [show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) from by push_cast; ring]
        exact Int.natAbs_natCast (q + 1)
      rw [FiniteFp.eq_def]
      exact ⟨rfl, he_stored.symm, hnatabs⟩
  · -- NOT SUBNORMAL
    push_neg at h_sub
    by_cases h_normal : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1)
    · -- NORMAL CASE
      simp [not_lt.mpr h_sub, h_normal]
      unfold roundNormalUp
      simp only
      have h_nr : isNormalRange ((mag : R) * (2 : R) ^ e_base) := ⟨h_sub, h_normal⟩
      have h_fed : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
          (Nat.log2 mag : ℤ) + e_base := by
        rw [findExponentDown_normal _ h_nr, hint_log]
      have he_ulp_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
        rw [h_e_ulp_eq]; apply max_eq_left
        have h_log_ge : FloatFormat.min_exp ≤ (Nat.log2 mag : ℤ) + e_base := by
          rw [← hint_log]
          exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2:ℕ)) hval_pos).mp
            (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
        omega
      have h_fed_ulp : findExponentDown ((mag : R) * (2 : R) ^ e_base) -
          FloatFormat.prec + 1 = e_ulp := by
        rw [h_fed, he_ulp_normal]; push_cast; ring
      -- The ceil via ceil_scaled_eq_ceil_div_ulp_step
      have hceil_normal : ⌈(mag : R) * (2 : R) ^ e_base /
          (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1)⌉ = (q : ℤ) + 1 := by
        have : (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 = e_ulp := by
          rw [he_ulp_normal]; push_cast; ring
        rw [this]; exact hceil
      -- The ceil of the scaled value = q + 1
      have hceil_scaled : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ findExponentDown ((mag : R) * (2 : R) ^ e_base) *
          (2 : R) ^ (FloatFormat.prec - 1)⌉ = (q : ℤ) + 1 := by
        rw [ceil_scaled_eq_ceil_div_ulp_step, h_fed_ulp]; exact hceil
      -- No binade overflow: q + 1 < 2^prec
      have hno_binade : ¬((2 : ℤ) ^ FloatFormat.prec.toNat ≤ (q : ℤ) + 1) := by
        push_neg; exact_mod_cast hq1_bound
      simp only [hceil_scaled, hno_binade, ↓reduceDIte]
      have hnatabs : ((q : ℤ) + 1).natAbs = q + 1 := by
        rw [show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) from by push_cast; ring]
        exact Int.natAbs_natCast (q + 1)
      have he_fed_eq_stored : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
          e_ulp + FloatFormat.prec - 1 := by
        rw [h_fed, he_ulp_normal]; push_cast; ring
      -- Goal: Fp.finite ⟨..., findExponentDown(val), (q+1).natAbs, _⟩ = Fp.finite ⟨..., e_ulp+prec-1, q+1, _⟩
      congr 1
      rw [FiniteFp.eq_def]
      exact ⟨rfl, he_fed_eq_stored, hnatabs⟩
    · exfalso; linarith

/-- `roundUp` in the carry case: when `q + 1 = 2^prec`, the ceiling crosses a binade boundary.
The result is `2^(e_ulp+prec)` stored as `⟨false, e_ulp+prec, 2^(prec-1), _⟩`. -/
private lemma isValid_roundUpNatMulZpowCarryTarget [FloatFormat]
    (e_ulp : ℤ)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp) :
    IsValidFiniteVal (e_ulp + FloatFormat.prec) (2 ^ (FloatFormat.prec - 1).toNat) := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have := FloatFormat.valid_prec
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · left
    exact ⟨le_refl _, Nat.pow_lt_pow_right (by norm_num) (by
      have := FloatFormat.valid_prec; omega)⟩

private def mkRoundUpNatMulZpowCarryTarget [FloatFormat]
    (e_ulp : ℤ)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp) :
    FiniteFp :=
  ⟨false, e_ulp + FloatFormat.prec, 2 ^ (FloatFormat.prec - 1).toNat,
    isValid_roundUpNatMulZpowCarryTarget
      e_ulp he_ulp_ge_sub he_stored_le⟩

private abbrev roundUpNatMulZpowCarryTarget [FloatFormat]
    (e_ulp : ℤ)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp) :
    Fp :=
  Fp.finite <| mkRoundUpNatMulZpowCarryTarget e_ulp he_ulp_ge_sub he_stored_le

theorem roundUp_nat_mul_zpow_carry [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (_hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hval_lt : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1))
    (hceil : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1)
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp)
    (hq1_eq_pow : q + 1 = 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    roundUp ((mag : R) * (2 : R) ^ e_base) =
      Fp.finite (mkRoundUpNatMulZpowCarryTarget e_ulp he_ulp_ge_sub he_stored_le) := by
  unfold mkRoundUpNatMulZpowCarryTarget
  -- val > q * 2^e_ulp ≥ 2^(prec-1) * 2^(min_exp-prec+1) = 2^min_exp
  have hval_gt_q_ulp : (q : R) * (2 : R) ^ e_ulp < (mag : R) * (2 : R) ^ e_base := by
    -- ⌈val/ulp⌉ = q+1 and q is an integer, so val/ulp > q (since ⌈x⌉ ≥ n+1 means x > n)
    have h_ceil_gt : (q : R) < (mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp := by
      have := Int.lt_ceil.mp (show (q : ℤ) < ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ from
        by rw [hceil]; omega)
      exact_mod_cast this
    rwa [lt_div_iff₀ (zpow_pos (by norm_num : (0:R) < 2) _)] at h_ceil_gt
  have hval_ge_min : (2 : R) ^ FloatFormat.min_exp ≤ (mag : R) * (2 : R) ^ e_base := by
    have hq_ge_half : (2 : R) ^ (FloatFormat.prec - 1) ≤ (q : R) := by
      have hp := FloatFormat.valid_prec
      have hq_nat_ge : 2 ^ (FloatFormat.prec.toNat - 1) ≤ q := by
        have h1 := Nat.one_le_two_pow (n := FloatFormat.prec.toNat - 1)
        have h2 : 2 ^ FloatFormat.prec.toNat = 2 ^ (FloatFormat.prec.toNat - 1 + 1) := by
          congr 1; omega
        rw [pow_succ] at h2
        omega
      -- (2:R)^(prec-1) ≤ (q:R) since 2^(prec.toNat-1) ≤ q in ℕ
      rw [← FloatFormat.pow_toNat_sub_one_eq_zpow_sub_one (R := R)]
      rw [← Nat.cast_ofNat, ← Nat.cast_pow]
      exact_mod_cast hq_nat_ge
    calc (2 : R) ^ FloatFormat.min_exp
        = (2 : R) ^ ((FloatFormat.prec - 1) + (FloatFormat.min_exp - FloatFormat.prec + 1)) := by
          congr 1; ring
      _ ≤ (2 : R) ^ ((FloatFormat.prec - 1) + e_ulp) := by
          apply two_zpow_mono; omega
      _ = (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e_ulp := by rw [two_zpow_mul]
      _ ≤ (q : R) * (2 : R) ^ e_ulp := by
          apply mul_le_mul_of_nonneg_right hq_ge_half (le_of_lt (zpow_pos (by norm_num) _))
      _ ≤ (mag : R) * (2 : R) ^ e_base := le_of_lt hval_gt_q_ulp
  unfold roundUp findSuccessor
  simp [ne_of_gt hval_pos, hval_pos]
  unfold findSuccessorPos
  simp [not_lt.mpr hval_ge_min, hval_lt]
  -- Now in roundNormalUp
  unfold roundNormalUp
  simp only
  have h_nr : isNormalRange ((mag : R) * (2 : R) ^ e_base) := ⟨hval_ge_min, hval_lt⟩
  have h_fed : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
      (Nat.log2 mag : ℤ) + e_base := by
    rw [findExponentDown_normal _ h_nr, hint_log]
  have he_ulp_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
    rw [h_e_ulp_eq]; apply max_eq_left
    have h_log_ge : FloatFormat.min_exp ≤ (Nat.log2 mag : ℤ) + e_base := by
      rw [← hint_log]
      exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2:ℕ)) hval_pos).mp
        (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
    omega
  have h_fed_ulp : findExponentDown ((mag : R) * (2 : R) ^ e_base) -
      FloatFormat.prec + 1 = e_ulp := by
    rw [h_fed, he_ulp_normal]; push_cast; ring
  -- The ceil of the scaled value = q + 1
  have hceil_scaled : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ findExponentDown ((mag : R) * (2 : R) ^ e_base) *
      (2 : R) ^ (FloatFormat.prec - 1)⌉ = (q : ℤ) + 1 := by
    rw [ceil_scaled_eq_ceil_div_ulp_step, h_fed_ulp]; exact hceil
  -- Binade overflow: q + 1 = 2^prec ≥ 2^prec
  have hbinade : (2 : ℤ) ^ FloatFormat.prec.toNat ≤ (q : ℤ) + 1 := by
    exact_mod_cast (show 2 ^ FloatFormat.prec.toNat ≤ q + 1 from by omega)
  -- Not above max_exp + 1
  have hfed_le_max : findExponentDown ((mag : R) * (2 : R) ^ e_base) + 1 ≤ FloatFormat.max_exp := by
    rw [h_fed]
    have : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp := he_stored_le
    rw [he_ulp_normal] at this
    have := FloatFormat.prec_pos; push_cast at this ⊢; omega
  have hno_overflow : ¬(findExponentDown ((mag : R) * (2 : R) ^ e_base) + 1 >
      FloatFormat.max_exp) := by
    push_neg; exact hfed_le_max
  simp only [hceil_scaled, hbinade, hno_overflow, ↓reduceDIte]
  -- Goal: Fp.finite ⟨false, fed+1, 2^(prec-1).toNat, _⟩ = Fp.finite ⟨false, e_ulp+prec, 2^(prec.toNat-1), _⟩
  have he_eq : findExponentDown ((mag : R) * (2 : R) ^ e_base) + 1 =
      e_ulp + FloatFormat.prec := by
    rw [h_fed, he_ulp_normal]; push_cast; ring
  have hm_eq : 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
  simp only [he_eq, hm_eq]

/-- roundUp of a positive value is ≥ Fp.finite 0 -/
theorem roundUp_zero_le_pos [FloatFormat] (x : R) (hx : 0 < x) :
    Fp.finite 0 ≤ roundUp x := by
  unfold roundUp
  rw [findSuccessor_pos_eq x hx]
  match hfsp : findSuccessorPos x hx with
  | Fp.finite f =>
    rw [Fp.finite_le_finite_iff]
    have hf_pos := findSuccessorPos_pos hfsp
    have hnz : ¬f.isZero := by
      intro hz; have := FiniteFp.toVal_isZero (R := R) hz; linarith
    exact FiniteFp.toVal_le R (by rw [FiniteFp.toVal_zero]; linarith) (Or.inr hnz)
  | Fp.infinite b =>
    rw [Fp.le_def]; left
    have := findSuccessorPos_ne_neg_inf x hx
    rw [hfsp] at this; simp at this; subst this; simp
  | Fp.NaN => exact absurd hfsp (findSuccessorPos_ne_nan x hx)

/-- roundUp of a negative value is ≤ Fp.finite 0 -/
theorem roundUp_neg_le_zero [FloatFormat] (x : R) (hx : x < 0) :
    roundUp x ≤ Fp.finite 0 := by
  unfold roundUp findSuccessor
  have hne : x ≠ 0 := ne_of_lt hx
  have hnpos : ¬(0 < x) := not_lt.mpr (le_of_lt hx)
  simp only [hne, ↓reduceDIte, hnpos]
  -- Result: Fp.finite (-(findPredecessorPos (-x) _))
  have hneg_pos : 0 < -x := neg_pos.mpr hx
  rw [Fp.finite_le_finite_iff]
  apply FiniteFp.toVal_le_handle R
  · rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_zero]
    linarith [findPredecessorPos_nonneg (x := -x) (hpos := hneg_pos)]
  · intro ⟨hx_zero, _⟩
    -- (-pred).isZero: m = 0, and (-pred).s = true (since pred has s = false)
    -- 0 has s = false, so (-pred) < 0 by sign comparison
    rw [FiniteFp.le_def]; left
    rw [FiniteFp.lt_def]
    left
    unfold FiniteFp.isZero at hx_zero
    simp [FiniteFp.neg_def] at hx_zero ⊢
    exact ⟨findPredecessorPos_sign_false (-x) hneg_pos, rfl⟩

/-- roundUp is monotone: x ≤ y → roundUp x ≤ roundUp y -/
theorem roundUp_mono [FloatFormat] {x y : R} (h : x ≤ y) : roundUp x ≤ roundUp y := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0
    rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · -- Both negative: use findSuccessor_mono_neg
      unfold roundUp
      exact findSuccessor_mono_neg hx_neg hy_neg h
    · -- x < 0, y = 0
      rw [hy_zero, roundUp_zero]
      exact roundUp_neg_le_zero x hx_neg
    · -- x < 0 < y: roundUp x ≤ 0 ≤ roundUp y
      have h1 := roundUp_neg_le_zero x hx_neg
      have h2 := roundUp_zero_le_pos y hy_pos
      -- roundUp x is always finite for x < 0
      unfold roundUp findSuccessor at h1 h2 ⊢
      simp only [ne_of_lt hx_neg, ↓reduceDIte, not_lt.mpr (le_of_lt hx_neg)] at h1 ⊢
      simp only [ne_of_gt hy_pos, ↓reduceDIte, hy_pos] at h2 ⊢
      -- Now goal has Fp.finite (-v) ≤ findSuccessorPos y hy_pos
      -- h1 : Fp.finite (-v) ≤ Fp.finite 0
      -- h2 : Fp.finite 0 ≤ findSuccessorPos y hy_pos
      match hfsp : findSuccessorPos y hy_pos with
      | Fp.finite fy =>
        rw [hfsp] at h2
        exact Fp.finite_le_trans h1 h2
      | Fp.infinite b =>
        have := findSuccessorPos_ne_neg_inf y hy_pos
        rw [hfsp] at this; simp at this; subst this
        rw [Fp.le_def]; left; simp
      | Fp.NaN => exact absurd hfsp (findSuccessorPos_ne_nan y hy_pos)
  · -- x = 0
    rw [hx_zero, roundUp_zero]
    rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · linarith
    · rw [hy_zero, roundUp_zero]; exact Fp.le_refl _
    · exact roundUp_zero_le_pos y hy_pos
  · -- x > 0
    have hy_pos : 0 < y := lt_of_lt_of_le hx_pos h
    unfold roundUp
    rw [findSuccessor_pos_eq x hx_pos, findSuccessor_pos_eq y hy_pos]
    exact findSuccessorPos_mono hx_pos hy_pos h

/-- If `g` is a valid finite float with `x ≤ g.toVal`, then `roundUp x ≤ g`. -/
theorem roundUp_le_of_fp_ge [FloatFormat]
    (x : R) (g : FiniteFp) (hg : g.s = false ∨ 0 < g.m)
    (hge : x ≤ g.toVal) : roundUp x ≤ Fp.finite g := by
  have hidem : roundUp (g.toVal (R := R)) = Fp.finite g := roundUp_idempotent g hg
  rw [← hidem]
  exact roundUp_mono hge

/-- If `f` is a valid finite float with `f.toVal ≤ y`, then `f ≤ roundDown y`. -/
theorem roundDown_ge_of_fp_le [FloatFormat]
    (y : R) (f : FiniteFp) (hf : f.s = false ∨ 0 < f.m)
    (hle : f.toVal ≤ y) : Fp.finite f ≤ roundDown y := by
  have hidem : roundDown (f.toVal (R := R)) = Fp.finite f := roundDown_idempotent f hf
  rw [← hidem]
  exact roundDown_mono hle

/-- Zero-domain inverse behavior: `nextDown (nextUp (+0)) = +0`. -/
@[simp] theorem nextDown_nextUp_pos_zero [FloatFormat] :
    nextDown (nextUp (Fp.finite (0 : FiniteFp))) = Fp.finite 0 := by
  have h0 : nextUp (Fp.finite (0 : FiniteFp)) = Fp.finite FiniteFp.smallestPosSubnormal := by
    exact (nextUp_zero)
  rw [h0]
  exact nextDown_smallestPosSubnormal

/-- Zero-domain inverse behavior: `nextUp (nextDown (+0)) = -0`. -/
@[simp] theorem nextUp_nextDown_pos_zero [FloatFormat] :
    nextUp (nextDown (Fp.finite (0 : FiniteFp))) = Fp.finite (-0) := by
  have h0 : nextDown (Fp.finite (0 : FiniteFp)) = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
    exact (nextDown_zero)
  rw [h0]
  exact nextUp_neg_smallestPosSubnormal

end RoundUp

end Rounding
