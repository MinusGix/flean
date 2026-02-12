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
import Flean.Rounding.RoundUp
import Flean.Rounding.RoundTowardZero
import Flean.Rounding.RoundNearest

/-! # Rounding Idempotence

Floating-point values are fixed points of rounding:
`round(f.toVal) = Fp.finite f` for all non-negative-zero finite floats.

The hypothesis excludes negative zero because `(-0).toVal = 0` and
`roundDown(0) = Fp.finite (+0) ≠ Fp.finite (-0)`.
-/

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-! ## Step 1: Normal positive helpers -/

/-- For a positive normal float, its toVal lies in [2^e, 2^(e+1)). -/
theorem toVal_normal_bounds (f : FiniteFp) (hs : f.s = false) (hn : isNormal f.m) :
    (2 : R) ^ f.e ≤ f.toVal ∧ f.toVal < (2 : R) ^ (f.e + 1) := by
  have hm_lb := hn.1  -- 2^(prec-1).toNat ≤ f.m
  have hm_ub := hn.2  -- f.m < 2^prec.toNat
  have hstep_pos : (0 : R) < (2 : R) ^ (f.e - FloatFormat.prec + 1) := two_zpow_pos' _
  -- toVal = f.m * 2^(e - prec + 1) for s = false
  have htoVal : f.toVal (R := R) = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp [hs]
  rw [htoVal]
  constructor
  · -- Lower bound: 2^(prec-1) * 2^(e-prec+1) = 2^e ≤ f.m * 2^(e-prec+1)
    calc (2 : R) ^ f.e
        = (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
          rw [two_zpow_mul]; congr 1; ring
      _ ≤ (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hstep_pos)
          calc (2 : R) ^ (FloatFormat.prec - 1)
              = (2 : R) ^ (FloatFormat.prec - 1).toNat := FloatFormat.pow_prec_sub_one_nat_int.symm
            _ ≤ (f.m : R) := by exact_mod_cast hm_lb
  · -- Upper bound: f.m * 2^(e-prec+1) < 2^prec * 2^(e-prec+1) = 2^(e+1)
    calc (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)
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

/-- The scaled significand of a normal positive float equals its significand:
    f.toVal / 2^f.e * 2^(prec-1) = f.m -/
theorem scaled_significand_eq_m (f : FiniteFp) (hs : f.s = false) :
    f.toVal (R := R) / (2 : R) ^ f.e * (2 : R) ^ (FloatFormat.prec - 1) = (f.m : R) := by
  have htoVal : f.toVal (R := R) = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp [hs]
  rw [htoVal, mul_two_zpow_div_two_zpow, mul_two_zpow_right]
  have : f.e - FloatFormat.prec + 1 - f.e + (FloatFormat.prec - 1) = 0 := by ring
  rw [this, zpow_zero, mul_one]

/-! ## Step 2: roundNormalDown idempotence -/

/-- Helper: positive normal float has isNormalRange toVal -/
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
  -- Rewrite the exponent
  have heq : findExponentDown (f.toVal (R := R)) = f.e :=
    findExponentDown_of_normal_toVal f hs hn
  -- Rewrite the scaled significand
  have hscaled : (f.toVal (R := R)) / (2 : R) ^ findExponentDown (f.toVal (R := R)) *
      (2 : R) ^ (FloatFormat.prec - 1) = (f.m : R) := by
    rw [heq]
    exact scaled_significand_eq_m f hs
  -- Floor of a natural number cast to R is itself
  have hfloor : ⌊(f.m : R)⌋ = (f.m : ℤ) := Int.floor_natCast f.m
  -- natAbs of a natural number cast to ℤ is itself
  have hnatabs : (f.m : ℤ).natAbs = f.m := Int.natAbs_natCast f.m
  -- Simplify the let bindings
  conv_lhs => simp only [hscaled, hfloor]
  -- Now use eq_def to match fields
  rw [FiniteFp.eq_def]
  exact ⟨hs.symm, heq, hnatabs⟩

/-! ## Step 3: Subnormal positive helpers + roundSubnormalDown idempotence -/

/-- For a positive subnormal float with m > 0, its toVal is in the subnormal range. -/
theorem toVal_subnormal_isSubnormalRange (f : FiniteFp) (hs : f.s = false)
    (hsub : isSubnormal f.e f.m) (hm : 0 < f.m) :
    isSubnormalRange (f.toVal (R := R)) := by
  have he : f.e = FloatFormat.min_exp := hsub.1
  have hm_ub : f.m ≤ 2 ^ (FloatFormat.prec - 1).toNat - 1 := hsub.2
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
      have h4 := FloatFormat.nat_four_le_two_pow_prec
      have hm_lt_nat : f.m < 2 ^ (FloatFormat.prec - 1).toNat := by omega
      calc (f.m : R) < (2 : R) ^ (FloatFormat.prec - 1).toNat := by exact_mod_cast hm_lt_nat
        _ = (2 : R) ^ (FloatFormat.prec - 1) := FloatFormat.pow_prec_sub_one_nat_int
    calc (f.m : R) * (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
        < (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) :=
          mul_lt_mul_of_pos_right hm_lt (two_zpow_pos' _)
      _ = (2 : R) ^ FloatFormat.min_exp := by
          rw [two_zpow_mul]; congr 1; ring

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

/-! ## Step 4: Combined positive roundDown -/

/-- For a non-negative-zero float, roundDown gives back the same float. -/
theorem roundDown_idempotent_nonneg (f : FiniteFp) (hs : f.s = false) (hm : 0 < f.m) :
    roundDown (f.toVal (R := R)) = Fp.finite f := by
  have hfpos : (0 : R) < f.toVal := FiniteFp.toVal_pos f hs hm
  unfold roundDown findPredecessor
  simp only [ne_of_gt hfpos, ↓reduceDIte, hfpos, Fp.finite.injEq]
  unfold findPredecessorPos
  rcases f.isNormal_or_isSubnormal with hnormal | hsubnormal
  · -- Normal case
    have hnr := toVal_normal_isNormalRange (R := R) f hs hnormal
    have h_not_sub : ¬(f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp) := not_lt.mpr hnr.1
    have h_not_over : f.toVal (R := R) < (2 : R) ^ (FloatFormat.max_exp + 1) := hnr.2
    simp only [h_not_sub, ↓reduceDIte, h_not_over]
    exact roundNormalDown_of_normal_toVal f hs hnormal hnr
  · -- Subnormal case
    have hsr := toVal_subnormal_isSubnormalRange (R := R) f hs hsubnormal hm
    have h_sub : f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp := hsr.2
    simp only [h_sub, ↓reduceDIte]
    exact roundSubnormalDown_of_subnormal_toVal f hs hsubnormal hm hsr

/-! ## Step 5: roundUp positive idempotence -/

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
  -- The overflow condition is false since f.m < 2^prec
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
  have hm_ub : f.m ≤ 2 ^ (FloatFormat.prec - 1).toNat - 1 := hsub.2
  have hdiv : f.toVal (R := R) / (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) = (f.m : R) :=
    subnormal_toVal_div_ulp_eq_m f hs hsub
  have hceil : ⌈(f.m : R)⌉ = (f.m : ℤ) := Int.ceil_natCast f.m
  have hk_eq : ⌈f.toVal (R := R) / (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)⌉ = (f.m : ℤ) := by
    rw [hdiv, hceil]
  conv_lhs => simp only [hk_eq]
  -- The transition condition is false: f.m < 2^(prec-1)
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
  · -- Normal case
    have hnr := toVal_normal_isNormalRange (R := R) f hs hnormal
    have h_not_sub : ¬(f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp) := not_lt.mpr hnr.1
    have h_not_over : f.toVal (R := R) < (2 : R) ^ (FloatFormat.max_exp + 1) := hnr.2
    simp only [h_not_sub, ↓reduceDIte, h_not_over]
    exact roundNormalUp_of_normal_toVal f hs hnormal hnr
  · -- Subnormal case
    have hsr := toVal_subnormal_isSubnormalRange (R := R) f hs hsubnormal hm
    have h_sub : f.toVal (R := R) < (2 : R) ^ FloatFormat.min_exp := hsr.2
    simp only [h_sub, ↓reduceDIte, Fp.finite.injEq]
    exact roundSubnormalUp_of_subnormal_toVal f hs hsubnormal hm hsr

/-! ## Step 6: Negative cases + full idempotence -/

/-- For a negative float with m > 0, roundDown gives back the same float. -/
theorem roundDown_idempotent_neg (f : FiniteFp) (hs : f.s = true) (hm : 0 < f.m) :
    roundDown (f.toVal (R := R)) = Fp.finite f := by
  have hnf_s : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
  have hnf_m : 0 < (-f).m := by rw [FiniteFp.neg_def]; exact hm
  have hnf_pos : (0 : R) < (-f).toVal := FiniteFp.toVal_pos (-f) hnf_s hnf_m
  have hfneg : f.toVal (R := R) < 0 := by
    rw [FiniteFp.toVal_neg_eq_neg] at hnf_pos; linarith
  -- roundDown(f.toVal) = findPredecessor(f.toVal) = -(findSuccessorPos(-f.toVal, _))
  rw [roundDown, findPredecessor_neg_eq _ hfneg]
  -- roundUp((-f).toVal) = findSuccessorPos((-f).toVal, hnf_pos)
  have hup := roundUp_idempotent_nonneg (R := R) (-f) hnf_s hnf_m
  rw [roundUp, findSuccessor_pos_eq _ hnf_pos] at hup
  -- Connect the two findSuccessorPos calls via congr (proof irrelevance)
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
  -- roundUp(f.toVal) = findSuccessor(f.toVal) = Fp.finite(-(findPredecessorPos(-f.toVal, _)))
  rw [roundUp, findSuccessor_neg_eq _ hfneg]
  -- roundDown((-f).toVal) = Fp.finite(findPredecessorPos((-f).toVal, hnf_pos))
  have hdown := roundDown_idempotent_nonneg (R := R) (-f) hnf_s hnf_m
  rw [roundDown, findPredecessor_pos_eq _ hnf_pos, Fp.finite.injEq] at hdown
  -- Connect the two findPredecessorPos calls via congr (proof irrelevance)
  have key : findPredecessorPos (-f.toVal (R := R)) (neg_pos.mpr hfneg) =
             findPredecessorPos ((-f).toVal (R := R)) hnf_pos := by
    congr 1; rw [FiniteFp.toVal_neg_eq_neg]
  rw [Fp.finite.injEq, key, hdown, neg_neg]

/-- Helper: if f.m = 0 and f.s = false, then f = 0 -/
private theorem eq_zero_of_sign_false_m_zero (f : FiniteFp) (hs : f.s = false) (hm : f.m = 0) :
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

/-! ## Step 7: Other rounding modes -/

/-- roundTowardZero is idempotent on non-negative-zero floats. -/
theorem roundTowardZero_idempotent (f : FiniteFp) (h : f.s = false ∨ 0 < f.m) :
    roundTowardZero (f.toVal (R := R)) = Fp.finite f := by
  by_cases hm : f.m = 0
  · rcases h with hs | hm'
    · rw [eq_zero_of_sign_false_m_zero f hs hm, FiniteFp.toVal_zero, roundTowardZero_zero]
    · omega
  · have hm_pos : 0 < f.m := by omega
    by_cases hs : f.s = false
    · rw [roundTowardZero_pos_eq _ (FiniteFp.toVal_pos f hs hm_pos)]
      exact roundDown_idempotent_nonneg f hs hm_pos
    · have hs_true : f.s = true := by revert hs; cases f.s <;> simp
      have hfneg : f.toVal (R := R) < 0 := by
        have hnf_pos : (0 : R) < (-f).toVal :=
          FiniteFp.toVal_pos (-f) (by rw [FiniteFp.neg_def]; simp [hs_true]) hm_pos
        rw [FiniteFp.toVal_neg_eq_neg] at hnf_pos; linarith
      rw [roundTowardZero_neg_eq _ hfneg]
      exact roundUp_idempotent_neg f hs_true hm_pos

/-- Helper: toVal of a nonzero float has |toVal| ≥ smallestPosSubnormal.toVal -/
theorem toVal_abs_ge_smallest (f : FiniteFp) (hm : 0 < f.m) :
    FiniteFp.smallestPosSubnormal.toVal ≤ |f.toVal (R := R)| := by
  rw [FiniteFp.smallestPosSubnormal_toVal]
  -- smallestPosSubnormal.toVal = 2^(min_exp - prec + 1)
  -- |f.toVal| = f.m * 2^(f.e - prec + 1) (for the appropriate sign)
  -- Since f.m ≥ 1 and f.e ≥ min_exp, we have f.m * 2^(f.e-p+1) ≥ 1 * 2^(min_exp-p+1)
  by_cases hs : f.s = false
  · have hpos : (0 : R) < f.toVal := FiniteFp.toVal_pos f hs hm
    rw [abs_of_pos hpos]
    have htoVal : f.toVal (R := R) = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
      unfold FiniteFp.toVal FiniteFp.sign'
      rw [FloatFormat.radix_val_eq_two]
      simp [hs]
    rw [htoVal]
    calc (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
        = 1 * (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by ring
      _ ≤ (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
          apply mul_le_mul
          · exact_mod_cast hm
          · exact two_zpow_mono
              (by linarith [f.valid_min_exp])
          · exact le_of_lt (two_zpow_pos' _)
          · exact Nat.cast_nonneg _
  · have hs_true : f.s = true := by revert hs; cases f.s <;> simp
    have hnf_pos : (0 : R) < (-f).toVal :=
      FiniteFp.toVal_pos (-f) (by rw [FiniteFp.neg_def]; simp [hs_true]) hm
    have hfneg : f.toVal (R := R) < 0 := by
      rw [FiniteFp.toVal_neg_eq_neg] at hnf_pos; linarith
    rw [abs_of_neg hfneg]
    -- -f.toVal = (-f).toVal
    rw [show -f.toVal (R := R) = (-f).toVal from by rw [FiniteFp.toVal_neg_eq_neg]]
    have htoVal : (-f).toVal (R := R) = ((-f).m : R) * (2 : R) ^ ((-f).e - FloatFormat.prec + 1) := by
      unfold FiniteFp.toVal FiniteFp.sign'
      rw [FloatFormat.radix_val_eq_two]
      simp [show (-f).s = false from by rw [FiniteFp.neg_def]; simp [hs_true]]
    rw [htoVal]
    have : (-f).m = f.m := by rw [FiniteFp.neg_def]
    have : (-f).e = f.e := by rw [FiniteFp.neg_def]
    rw [‹(-f).m = f.m›, ‹(-f).e = f.e›]
    calc (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
        = 1 * (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by ring
      _ ≤ (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
          apply mul_le_mul
          · exact_mod_cast hm
          · exact two_zpow_mono
              (by linarith [f.valid_min_exp])
          · exact le_of_lt (two_zpow_pos' _)
          · exact Nat.cast_nonneg _

/-- Helper: toVal of any finite float has |toVal| < overflow threshold -/
theorem toVal_abs_lt_overflow (f : FiniteFp) :
    |f.toVal (R := R)| < FloatFormat.overflowThreshold R := by
  -- |f.toVal| ≤ largestFiniteFloat.toVal < 2^(max_exp+1)
  -- And 2^(max_exp+1) ≤ (2 - eps/2) * 2^max_exp since eps ≤ 1 means 2 - eps/2 ≥ 3/2 > ... actually 2 - eps/2 ≥ 2 - 1/2 = 3/2
  -- Actually (2 - eps/2) * 2^max_exp ≥ 2 * 2^max_exp = 2^(max_exp+1) is what we need
  -- And 2 - eps/2 ≥ 2 since eps = 2^(1-prec) ≤ 1 means eps/2 ≤ 1/2, so 2 - eps/2 ≥ 3/2 ... but 3/2 < 2
  -- Wait, we need (2 - eps/2) * 2^max_exp ≥ 2^(max_exp+1). That means 2 - eps/2 ≥ 2, which needs eps ≤ 0.
  -- That's false. So the chain goes the other way: we need |f.toVal| < this threshold.
  -- largestFiniteFloat.toVal < 2^(max_exp+1). And 2^(max_exp+1) = 2 * 2^max_exp.
  -- (2 - eps/2) * 2^max_exp = 2 * 2^max_exp - eps/2 * 2^max_exp < 2 * 2^max_exp = 2^(max_exp+1)
  -- So we just need |f.toVal| < 2^(max_exp+1) and we're done since threshold < 2^(max_exp+1) is wrong.
  -- Actually: threshold is LESS than 2^(max_exp+1) since eps > 0.
  -- The bound should be: |f.toVal| ≤ largest.toVal < threshold.
  -- largest.toVal = (2^p - 1) * 2^(max_exp - p + 1) = 2^(max_exp+1) - 2^(max_exp - p + 1)
  -- threshold = (2 - 2^(1-p)/2) * 2^max_exp = 2^(max_exp+1) - 2^(1-p)/2 * 2^max_exp
  --           = 2^(max_exp+1) - 2^(max_exp+1-p)/2 = 2^(max_exp+1) - 2^(max_exp-p)
  -- We need largest.toVal < threshold, i.e.,
  -- 2^(max_exp+1) - 2^(max_exp-p+1) < 2^(max_exp+1) - 2^(max_exp-p)
  -- i.e., 2^(max_exp-p) < 2^(max_exp-p+1), which is true.
  -- So the chain is: |f.toVal| ≤ largest.toVal < threshold.
  have h_abs_le : |f.toVal (R := R)| ≤ FiniteFp.largestFiniteFloat.toVal := by
    rw [abs_le]
    constructor
    · -- -largest ≤ f.toVal
      -- f.toVal ≤ largest, so -f.toVal ≤ largest
      -- Also: (-f).toVal = -f.toVal, and (-f).toVal ≤ largest
      have : (-f).toVal (R := R) ≤ FiniteFp.largestFiniteFloat.toVal :=
        FiniteFp.finite_le_largestFiniteFloat (-f)
      rw [FiniteFp.toVal_neg_eq_neg] at this
      linarith
    · exact FiniteFp.finite_le_largestFiniteFloat f
  have h_largest_lt : FiniteFp.largestFiniteFloat.toVal <
      FloatFormat.overflowThreshold R := by
    rw [FiniteFp.largestFiniteFloat_toVal]
    -- largest = 2^max_exp * (2 - 2^(-prec+1)) = 2^max_exp * (2 - 2^(1-prec))
    -- threshold = (2 - 2^(1-prec)/2) * 2^max_exp
    -- threshold - largest = 2^max_exp * 2^(1-prec) / 2 > 0
    have h2max_pos : (0 : R) < (2 : R) ^ FloatFormat.max_exp := two_zpow_pos' _
    have h_eps_pos : (0 : R) < (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) := two_zpow_pos' _
    have h_eq : (-(FloatFormat.prec : ℤ) + 1) = (1 - (FloatFormat.prec : ℤ)) := by ring
    rw [h_eq]; unfold FloatFormat.overflowThreshold at *
    nlinarith
  linarith

/-- roundNearestTiesToEven is idempotent on non-negative-zero floats. -/
theorem roundNearestTiesToEven_idempotent (f : FiniteFp) (h : f.s = false ∨ 0 < f.m) :
    roundNearestTiesToEven (f.toVal (R := R)) = Fp.finite f := by
  unfold roundNearestTiesToEven
  by_cases hm : f.m = 0
  · rcases h with hs | hm'
    · rw [eq_zero_of_sign_false_m_zero f hs hm, FiniteFp.toVal_zero]; simp
    · omega
  have hm_pos : 0 < f.m := by omega
  have hval_ne : f.toVal (R := R) ≠ 0 := by
    intro habs; exact hm (FiniteFp.toVal_significand_zero_iff.mpr habs)
  simp only [hval_ne, ↓reduceIte]
  -- |f.toVal| ≥ smallestPosSubnormal/2
  have habs_ge : ¬(|f.toVal (R := R)| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    push_neg
    have := toVal_abs_ge_smallest (R := R) f hm_pos
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  simp only [habs_ge, ↓reduceIte]
  -- |f.toVal| < overflow threshold
  have habs_lt : ¬(|f.toVal (R := R)| ≥ FloatFormat.overflowThreshold R) := by
    push_neg; exact toVal_abs_lt_overflow f
  simp only [habs_lt, ↓reduceIte]
  -- pred = succ = Fp.finite f
  have hpred : findPredecessor (f.toVal (R := R)) = Fp.finite f := by
    exact roundDown_idempotent (R := R) f h
  have hsucc : findSuccessor (f.toVal (R := R)) = Fp.finite f := by
    exact roundUp_idempotent (R := R) f h
  rw [hpred, hsucc]
  simp only
  -- midpoint = f.toVal, all branches give Fp.finite f
  have hmid : (f.toVal + f.toVal (R := R)) / 2 = f.toVal := by ring
  simp only [hmid, lt_irrefl, ↓reduceIte]
  split_ifs <;> rfl

/-- roundNearestTiesAwayFromZero is idempotent on non-negative-zero floats. -/
theorem roundNearestTiesAwayFromZero_idempotent (f : FiniteFp) (h : f.s = false ∨ 0 < f.m) :
    roundNearestTiesAwayFromZero (f.toVal (R := R)) = Fp.finite f := by
  unfold roundNearestTiesAwayFromZero
  by_cases hm : f.m = 0
  · rcases h with hs | hm'
    · rw [eq_zero_of_sign_false_m_zero f hs hm, FiniteFp.toVal_zero]; simp
    · omega
  have hm_pos : 0 < f.m := by omega
  have hval_ne : f.toVal (R := R) ≠ 0 := by
    intro habs; exact hm (FiniteFp.toVal_significand_zero_iff.mpr habs)
  simp only [hval_ne, ↓reduceIte]
  have habs_ge : ¬(|f.toVal (R := R)| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    push_neg
    have := toVal_abs_ge_smallest (R := R) f hm_pos
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  simp only [habs_ge, ↓reduceIte]
  have habs_lt : ¬(|f.toVal (R := R)| ≥ FloatFormat.overflowThreshold R) := by
    push_neg; exact toVal_abs_lt_overflow f
  simp only [habs_lt, ↓reduceIte]
  have hpred : findPredecessor (f.toVal (R := R)) = Fp.finite f := by
    exact roundDown_idempotent (R := R) f h
  have hsucc : findSuccessor (f.toVal (R := R)) = Fp.finite f := by
    exact roundUp_idempotent (R := R) f h
  rw [hpred, hsucc]
  simp only
  have hmid : (f.toVal + f.toVal (R := R)) / 2 = f.toVal := by ring
  simp only [hmid, lt_irrefl, ↓reduceIte]
  split_ifs <;> rfl

/-! ## Rounding Symmetry and Ordering Properties -/

/-- Negation symmetry: rounding down the negation equals negating the round-up.
    The hypothesis `x ≠ 0` is necessary because `roundDown(0) = +0` but `-(roundUp(0)) = -(+0) = -0`,
    and `+0 ≠ -0` structurally. -/
theorem roundDown_neg_eq_neg_roundUp (x : R) (hx : x ≠ 0) :
    roundDown (-x) = -(roundUp x) := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · -- Case x < 0: -x > 0
    have hnxpos : 0 < -x := neg_pos.mpr hneg
    -- roundDown(-x) = findPredecessor(-x) = Fp.finite(findPredecessorPos(-x) _)  [since -x > 0]
    rw [roundDown, findPredecessor_pos_eq (-x) hnxpos]
    -- roundUp(x) = findSuccessor(x) = Fp.finite(-findPredecessorPos(-x) _)  [since x < 0]
    rw [roundUp, findSuccessor_neg_eq x hneg]
    -- -(Fp.finite(-findPredecessorPos(-x) _)) = Fp.finite(--findPredecessorPos(-x) _)
    rw [Fp.neg_finite, neg_neg]
  · exact absurd hzero hx
  · -- Case x > 0: -x < 0
    have hnxneg : -x < 0 := neg_lt_zero.mpr hpos
    -- roundDown(-x) = findPredecessor(-x) = -(findSuccessorPos(--x) _) = -(findSuccessorPos(x) _)
    rw [roundDown, findPredecessor_neg_eq (-x) hnxneg]
    -- roundUp(x) = findSuccessor(x) = findSuccessorPos(x) _
    rw [roundUp, findSuccessor_pos_eq x hpos]
    -- Both sides equal -(findSuccessorPos x _), just need to match proof terms
    simp only [neg_neg]

/-- Dual symmetry: rounding up the negation equals negating the round-down. -/
theorem roundUp_neg_eq_neg_roundDown (x : R) (hx : x ≠ 0) :
    roundUp (-x) = -(roundDown x) := by
  have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
  have h := roundDown_neg_eq_neg_roundUp (-x) hnx
  rw [neg_neg] at h
  rw [h, neg_neg]

/-- For any x, roundDown x ≤ roundUp x. -/
theorem roundDown_le_roundUp (x : R) : roundDown x ≤ roundUp x := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · -- Case x < 0
    have hnxpos : 0 < -x := neg_pos.mpr hneg
    -- roundDown(x) = -(findSuccessorPos(-x) _)
    rw [roundDown, findPredecessor_neg_eq x hneg]
    -- roundUp(x) = Fp.finite(-findPredecessorPos(-x) _)
    rw [roundUp, findSuccessor_neg_eq x hneg]
    -- Need: -(findSuccessorPos(-x) _) ≤ Fp.finite(-findPredecessorPos(-x) _)
    match hsucc_eq : findSuccessorPos (-x) hnxpos with
    | Fp.finite g =>
      rw [Fp.neg_finite, Fp.finite_le_finite_iff]
      have hpred_le : (findPredecessorPos (-x) hnxpos).toVal (R := R) ≤ -x :=
        findPredecessorPos_le (-x) hnxpos
      have hsucc_ge : -x ≤ (g.toVal : R) := findSuccessorPos_ge (-x) hnxpos g hsucc_eq
      have hval_le : (-g).toVal (R := R) ≤ (-(findPredecessorPos (-x) hnxpos)).toVal := by
        rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
        linarith
      apply FiniteFp.toVal_le_handle R hval_le
      intro ⟨hgz, hpz⟩
      rw [FiniteFp.isZero_iff] at hgz hpz
      rcases hgz with hgz1 | hgz2
      · exfalso
        rw [FiniteFp.neg_def, FiniteFp.eq_def] at hgz1
        simp only [FiniteFp.zero_def] at hgz1
        have hgs : g.s = true := by
          have := hgz1.left; revert this; cases g.s <;> simp
        have hgtpos : (0 : R) < g.toVal := lt_of_lt_of_le hnxpos hsucc_ge
        have : (0 : R) ≤ (-g).toVal :=
          FiniteFp.toVal_nonneg (-g) (by rw [FiniteFp.neg_def]; simp [hgs])
        rw [FiniteFp.toVal_neg_eq_neg] at this
        linarith
      · rcases hpz with hpz1 | hpz2
        · exfalso
          rw [FiniteFp.neg_def, FiniteFp.eq_def] at hpz1
          simp only [FiniteFp.zero_def] at hpz1
          have := findPredecessorPos_sign_false (-x) hnxpos
          rw [this] at hpz1
          simp at hpz1
        · rw [hgz2, hpz2]
    | Fp.infinite b =>
      have hne := findSuccessorPos_ne_neg_inf (-x) hnxpos
      rw [hsucc_eq] at hne
      simp at hne
      subst hne
      rw [Fp.le_def]
      left
      rfl
    | Fp.NaN =>
      exact absurd hsucc_eq (findSuccessorPos_ne_nan (-x) hnxpos)
  · -- Case x = 0
    subst hzero
    rw [roundDown_zero, roundUp_zero]
    exact Fp.le_refl _
  · -- Case x > 0
    -- roundDown(x) = Fp.finite(findPredecessorPos(x) _)
    rw [roundDown, findPredecessor_pos_eq x hpos]
    -- roundUp(x) = findSuccessorPos(x) _
    rw [roundUp, findSuccessor_pos_eq x hpos]
    -- Case split on whether findSuccessorPos returns finite or infinite
    match hsucc_eq : findSuccessorPos x hpos with
    | Fp.finite g =>
      -- Both sides finite
      rw [Fp.finite_le_finite_iff]
      have hpred_le : (findPredecessorPos x hpos).toVal (R := R) ≤ x := findPredecessorPos_le x hpos
      have hsucc_ge : x ≤ (g.toVal : R) := findSuccessorPos_ge x hpos g hsucc_eq
      have hval_le : (findPredecessorPos x hpos).toVal (R := R) ≤ g.toVal := le_trans hpred_le hsucc_ge
      apply FiniteFp.toVal_le_handle R hval_le
      intro ⟨hpz, hgz⟩
      have hps := findPredecessorPos_sign_false x hpos
      rw [FiniteFp.isZero_iff] at hpz hgz
      rcases hpz with hpz1 | hpz2
      · rcases hgz with hgz1 | hgz2
        · rw [hpz1, hgz1]
        · exfalso
          rw [FiniteFp.neg_def, FiniteFp.eq_def] at hgz2
          simp only [FiniteFp.zero_def] at hgz2
          have hgtpos : (0 : R) < g.toVal := lt_of_lt_of_le hpos hsucc_ge
          have hgs : g.s = true := by
            have := hgz2.left; revert this; cases g.s <;> simp
          have : (0 : R) ≤ (-g).toVal :=
            FiniteFp.toVal_nonneg (-g) (by rw [FiniteFp.neg_def]; simp [hgs])
          rw [FiniteFp.toVal_neg_eq_neg] at this
          linarith
      · exfalso
        rw [FiniteFp.neg_def, FiniteFp.eq_def] at hpz2
        simp only [FiniteFp.zero_def, Bool.not_false] at hpz2
        rw [hps] at hpz2
        simp at hpz2
    | Fp.infinite b =>
      have hne := findSuccessorPos_ne_neg_inf x hpos
      rw [hsucc_eq] at hne
      simp at hne
      subst hne
      rw [Fp.le_def]
      left
      rfl
    | Fp.NaN =>
      exact absurd hsucc_eq (findSuccessorPos_ne_nan x hpos)

/-- For positive x, roundNearestTiesToEven equals roundDown or roundUp -/
theorem rnTE_eq_roundDown_or_roundUp_pos (x : R) (hxpos : 0 < x) :
    roundNearestTiesToEven x = roundDown x ∨ roundNearestTiesToEven x = roundUp x := by
  have hxne : x ≠ 0 := ne_of_gt hxpos
  unfold roundNearestTiesToEven
  rw [if_neg hxne]
  by_cases hsmall : |x| < FiniteFp.smallestPosSubnormal.toVal / 2
  · -- Small: returns Fp.finite 0 = roundDown x
    rw [if_pos hsmall, if_neg (not_lt.mpr (le_of_lt hxpos))]
    left
    have hlt_ssps : x < FiniteFp.smallestPosSubnormal.toVal := by
      rw [abs_of_pos hxpos] at hsmall
      linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
    exact (roundDown_lt_smallestPosSubnormal x hxpos hlt_ssps).symm
  · rw [if_neg hsmall]
    by_cases hoverflow : |x| ≥ FloatFormat.overflowThreshold R
    · -- Overflow: returns Fp.infinite false = roundUp x
      rw [if_pos hoverflow]
      have hnotlt : ¬(x < 0) := not_lt.mpr (le_of_lt hxpos)
      simp only [hnotlt, decide_false]
      right
      have hlff : x > FiniteFp.largestFiniteFloat.toVal (R := R) := by
        rw [abs_of_pos hxpos] at hoverflow
        exact lt_of_lt_of_le largestFiniteFloat_lt_overflow_threshold hoverflow
      exact (roundUp_gt_largestFiniteFloat x hxpos hlff).symm
    · -- Normal range: dispatches to pred or succ
      rw [if_neg hoverflow]
      simp only [findPredecessor_pos_eq x hxpos, findSuccessor_pos_eq x hxpos]
      -- Match on findSuccessorPos result
      match hfsp : findSuccessorPos x hxpos with
      | Fp.finite s =>
        dsimp only
        split_ifs
        · left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos]
        · right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hfsp]
        · left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos]
        · right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hfsp]
      | Fp.infinite _ =>
        -- findSuccessorPos returns +∞ (succ case), match falls to Fp.finite p, _ branch
        dsimp only
        left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos]
      | Fp.NaN =>
        exact absurd hfsp (findSuccessorPos_ne_nan x hxpos)

/-- For positive x, roundNearestTiesAwayFromZero equals roundDown or roundUp -/
theorem rnTA_eq_roundDown_or_roundUp_pos (x : R) (hxpos : 0 < x) :
    roundNearestTiesAwayFromZero x = roundDown x ∨ roundNearestTiesAwayFromZero x = roundUp x := by
  have hxne : x ≠ 0 := ne_of_gt hxpos
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hxne]
  by_cases hsmall : |x| < FiniteFp.smallestPosSubnormal.toVal / 2
  · rw [if_pos hsmall, if_neg (not_lt.mpr (le_of_lt hxpos))]
    left
    have hlt_ssps : x < FiniteFp.smallestPosSubnormal.toVal := by
      rw [abs_of_pos hxpos] at hsmall
      linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
    exact (roundDown_lt_smallestPosSubnormal x hxpos hlt_ssps).symm
  · rw [if_neg hsmall]
    by_cases hoverflow : |x| ≥ FloatFormat.overflowThreshold R
    · rw [if_pos hoverflow]
      have hnotlt : ¬(x < 0) := not_lt.mpr (le_of_lt hxpos)
      simp only [hnotlt, decide_false]
      right
      have hlff : x > FiniteFp.largestFiniteFloat.toVal (R := R) := by
        rw [abs_of_pos hxpos] at hoverflow
        exact lt_of_lt_of_le largestFiniteFloat_lt_overflow_threshold hoverflow
      exact (roundUp_gt_largestFiniteFloat x hxpos hlff).symm
    · rw [if_neg hoverflow]
      simp only [findPredecessor_pos_eq x hxpos, findSuccessor_pos_eq x hxpos]
      match hfsp : findSuccessorPos x hxpos with
      | Fp.finite s =>
        dsimp only
        split_ifs
        · left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos]
        · right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hfsp]
        · right; unfold roundUp; rw [findSuccessor_pos_eq x hxpos, hfsp]
      | Fp.infinite _ =>
        dsimp only
        left; unfold roundDown; rw [findPredecessor_pos_eq x hxpos]
      | Fp.NaN =>
        exact absurd hfsp (findSuccessorPos_ne_nan x hxpos)

/-- For non-zero x, roundNearestTiesToEven equals roundDown or roundUp -/
theorem rnTE_eq_roundDown_or_roundUp (x : R) (hx : x ≠ 0) :
    roundNearestTiesToEven x = roundDown x ∨ roundNearestTiesToEven x = roundUp x := by
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · -- x < 0: use negation symmetry
    have hnx_pos : 0 < -x := neg_pos.mpr hxneg
    have hnx_ne : (-x : R) ≠ 0 := ne_of_gt hnx_pos
    have h_neg_sym : roundNearestTiesToEven x = -(roundNearestTiesToEven (-x)) := by
      have h := rnEven_neg_eq_neg (-x) hnx_ne; simp [neg_neg] at h; exact h
    rcases rnTE_eq_roundDown_or_roundUp_pos (-x) hnx_pos with hrD | hrU
    · -- rnTE(-x) = roundDown(-x), so rnTE(x) = -(roundDown(-x)) = roundUp(x)
      right; rw [h_neg_sym, hrD]
      have h2 := roundUp_neg_eq_neg_roundDown (-x) hnx_ne; simp [neg_neg] at h2; exact h2.symm
    · -- rnTE(-x) = roundUp(-x), so rnTE(x) = -(roundUp(-x)) = roundDown(x)
      left; rw [h_neg_sym, hrU]
      have h2 := roundDown_neg_eq_neg_roundUp (-x) hnx_ne; simp [neg_neg] at h2; exact h2.symm
  · exact absurd hxzero hx
  · exact rnTE_eq_roundDown_or_roundUp_pos x hxpos

/-- roundNearestTiesToEven equals roundDown or roundUp for all x -/
theorem rnTE_eq_roundDown_or_roundUp' (x : R) :
    roundNearestTiesToEven x = roundDown x ∨ roundNearestTiesToEven x = roundUp x := by
  by_cases hx : x = 0
  · left; rw [hx, roundNearestTiesToEven_zero, roundDown_zero]
  · exact rnTE_eq_roundDown_or_roundUp x hx

/-- For non-zero x, roundNearestTiesAwayFromZero equals roundDown or roundUp -/
theorem rnTA_eq_roundDown_or_roundUp (x : R) (hx : x ≠ 0) :
    roundNearestTiesAwayFromZero x = roundDown x ∨ roundNearestTiesAwayFromZero x = roundUp x := by
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hnx_pos : 0 < -x := neg_pos.mpr hxneg
    have hnx_ne : (-x : R) ≠ 0 := ne_of_gt hnx_pos
    have h_neg_sym : roundNearestTiesAwayFromZero x = -(roundNearestTiesAwayFromZero (-x)) := by
      have h := rnAway_neg_eq_neg (-x) hnx_ne; simp [neg_neg] at h; exact h
    rcases rnTA_eq_roundDown_or_roundUp_pos (-x) hnx_pos with hrD | hrU
    · right; rw [h_neg_sym, hrD]
      have h2 := roundUp_neg_eq_neg_roundDown (-x) hnx_ne; simp [neg_neg] at h2; exact h2.symm
    · left; rw [h_neg_sym, hrU]
      have h2 := roundDown_neg_eq_neg_roundUp (-x) hnx_ne; simp [neg_neg] at h2; exact h2.symm
  · exact absurd hxzero hx
  · exact rnTA_eq_roundDown_or_roundUp_pos x hxpos

/-- roundNearestTiesAwayFromZero equals roundDown or roundUp for all x -/
theorem rnTA_eq_roundDown_or_roundUp' (x : R) :
    roundNearestTiesAwayFromZero x = roundDown x ∨ roundNearestTiesAwayFromZero x = roundUp x := by
  by_cases hx : x = 0
  · left; rw [hx, roundNearestTiesAwayFromZero_zero, roundDown_zero]
  · exact rnTA_eq_roundDown_or_roundUp x hx

/-- roundDown x ≤ roundNearestTiesToEven x for all x -/
theorem roundDown_le_roundNearestTE (x : R) :
    roundDown x ≤ roundNearestTiesToEven x := by
  by_cases hx : x = 0
  · rw [hx, roundDown_zero, roundNearestTiesToEven_zero]; exact Fp.le_refl _
  · rcases rnTE_eq_roundDown_or_roundUp x hx with hrD | hrU
    · rw [hrD]; exact Fp.le_refl _
    · rw [hrU]; exact roundDown_le_roundUp x

/-- roundNearestTiesToEven x ≤ roundUp x for all x -/
theorem roundNearestTE_le_roundUp (x : R) :
    roundNearestTiesToEven x ≤ roundUp x := by
  by_cases hx : x = 0
  · rw [hx, roundUp_zero, roundNearestTiesToEven_zero]; exact Fp.le_refl _
  · rcases rnTE_eq_roundDown_or_roundUp x hx with hrD | hrU
    · rw [hrD]; exact roundDown_le_roundUp x
    · rw [hrU]; exact Fp.le_refl _

/-- roundDown x ≤ roundNearestTiesAwayFromZero x for all x -/
theorem roundDown_le_roundNearestTA (x : R) :
    roundDown x ≤ roundNearestTiesAwayFromZero x := by
  by_cases hx : x = 0
  · rw [hx, roundDown_zero, roundNearestTiesAwayFromZero_zero]; exact Fp.le_refl _
  · rcases rnTA_eq_roundDown_or_roundUp x hx with hrD | hrU
    · rw [hrD]; exact Fp.le_refl _
    · rw [hrU]; exact roundDown_le_roundUp x

/-- roundNearestTiesAwayFromZero x ≤ roundUp x for all x -/
theorem roundNearestTA_le_roundUp (x : R) :
    roundNearestTiesAwayFromZero x ≤ roundUp x := by
  by_cases hx : x = 0
  · rw [hx, roundUp_zero, roundNearestTiesAwayFromZero_zero]; exact Fp.le_refl _
  · rcases rnTA_eq_roundDown_or_roundUp x hx with hrD | hrU
    · rw [hrD]; exact roundDown_le_roundUp x
    · rw [hrU]; exact Fp.le_refl _

/-- If g is a valid finite FP with g.toVal ≥ x, then roundUp x ≤ Fp.finite g.
    This is the minimality of roundUp: it's the smallest FP ≥ x. -/
theorem roundUp_le_of_fp_ge (x : R) (g : FiniteFp) (hg : g.s = false ∨ 0 < g.m)
    (hge : x ≤ g.toVal) : roundUp x ≤ Fp.finite g := by
  have hidem : roundUp (g.toVal (R := R)) = Fp.finite g := roundUp_idempotent g hg
  rw [← hidem]
  exact roundUp_mono hge

/-- If f is a valid finite FP with f.toVal ≤ y, then Fp.finite f ≤ roundDown y.
    This is the maximality of roundDown: it's the largest FP ≤ y. -/
theorem roundDown_ge_of_fp_le (y : R) (f : FiniteFp) (hf : f.s = false ∨ 0 < f.m)
    (hle : f.toVal ≤ y) : Fp.finite f ≤ roundDown y := by
  have hidem : roundDown (f.toVal (R := R)) = Fp.finite f := roundDown_idempotent f hf
  rw [← hidem]
  exact roundDown_mono hle

/-- If x ≤ y and roundUp(x) = Fp.finite f with f.toVal ≤ y, then roundUp(x) ≤ roundDown(y). -/
private theorem roundUp_le_roundDown_of_toVal_le {x y : R} (f : FiniteFp)
    (hfU : roundUp x = Fp.finite f) (hf_le : (f.toVal : R) ≤ y)
    (hvalid : f.s = false ∨ 0 < f.m) : roundUp x ≤ roundDown y := by
  rw [hfU]; exact roundDown_ge_of_fp_le y f hvalid hf_le

/-! ### Same-interval and dispatch lemmas for round-to-nearest monotonicity -/

/-- If x < y and roundUp(x) = Fp.finite f with f.toVal > y, then x and y share
    the same roundDown and roundUp (they're in the same FP interval).
    Restricted to positive values to avoid ±0 complications. -/
private theorem same_interval_pos {x y : R} (hx : 0 < x) (hlt : x < y)
    (f : FiniteFp) (hfU : roundUp x = Fp.finite f) (hval_gt : y < (f.toVal : R)) :
    roundDown x = roundDown y ∧ roundUp x = roundUp y := by
  have hfy : (f.toVal : R) > y := hval_gt
  have hfpos : (0 : R) < f.toVal := lt_of_lt_of_le hx (roundUp_ge x f hfU)
  have hfs : f.s = false ∨ 0 < f.m := by
    exact Or.inl (FiniteFp.toVal_pos_iff.mpr hfpos).1
  constructor
  · -- roundDown equality
    apply Fp.le_antisymm
    · exact roundDown_mono (le_of_lt hlt)
    · -- roundDown(y) is a float with toVal ≤ y < f.toVal
      -- If its toVal ≥ x, it would be a float ≥ x smaller than roundUp(x), contradiction
      -- So its toVal < x, making it ≤ roundDown(x)
      have hy : 0 < y := lt_trans hx hlt
      -- Extract g from roundDown(y)
      have hrDy := roundDown_zero_le_pos y hy
      -- roundDown(y) is ≥ Fp.finite 0, so it's finite
      rcases hgD : roundDown y with g | b | _
      · -- roundDown(y) = Fp.finite g
        -- Extract g = findPredecessorPos y hy
        have hg_eq : g = findPredecessorPos y hy := by
          have hgD' := hgD; unfold roundDown at hgD'
          rw [findPredecessor_pos_eq y hy] at hgD'
          exact (Fp.finite.injEq g _).mp hgD'.symm
        have hgs : g.s = false := by rw [hg_eq]; exact findPredecessorPos_sign_false y hy
        have hgv : (g.toVal : R) ≤ y := by rw [hg_eq]; exact findPredecessorPos_le y hy
        have hgvalid : g.s = false ∨ 0 < g.m := Or.inl hgs
        -- g.toVal ≤ y < f.toVal
        by_contra hne
        -- If g.toVal ≥ x, then roundUp(x) ≤ Fp.finite g
        by_cases hgx : x ≤ (g.toVal : R)
        · have hUg := roundUp_le_of_fp_ge x g hgvalid hgx
          -- But Fp.finite f = roundUp(x) ≤ Fp.finite g, so f.toVal ≤ g.toVal
          rw [hfU] at hUg
          have hfleg := FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff f g).mp hUg)
          -- Yet f.toVal ≤ g.toVal ≤ y < f.toVal → contradiction
          exact absurd hval_gt (not_lt.mpr (le_trans hfleg hgv))
        · -- g.toVal < x
          push_neg at hgx
          have hgle : (g.toVal : R) ≤ x := le_of_lt hgx
          exact hne (roundDown_ge_of_fp_le x g hgvalid hgle)
      · -- roundDown(y) = Fp.infinite b: impossible
        cases b
        · exact absurd hgD (roundDown_ne_pos_inf y)
        · rw [hgD] at hrDy; simp [Fp.le_def] at hrDy
      · -- roundDown(y) = Fp.NaN: impossible
        rw [hgD] at hrDy; simp [Fp.le_def] at hrDy
  · -- roundUp equality
    apply Fp.le_antisymm
    · exact roundUp_mono (le_of_lt hlt)
    · rw [hfU]; exact roundUp_le_of_fp_ge y f hfs (le_of_lt hfy)

/-! ### Monotonicity of round-to-nearest modes -/

/-- When roundDown(y) = Fp.finite dy for y < 0, we have dy.toVal ≤ y.
    This follows because roundDown is the floor function. -/
private theorem roundDown_neg_toVal_le {y : R} (hy : y < 0) (dy : FiniteFp)
    (hdy : roundDown y = Fp.finite dy) : (dy.toVal : R) ≤ y := by
  unfold roundDown at hdy
  rw [findPredecessor_neg_eq y hy] at hdy
  rcases hfsp : findSuccessorPos (-y) (neg_pos.mpr hy) with g | b | _
  · rw [hfsp] at hdy; rw [Fp.neg_finite, Fp.finite.injEq] at hdy
    have hg_ge := findSuccessorPos_ge (-y) (neg_pos.mpr hy) g hfsp
    rw [← hdy, FiniteFp.toVal_neg_eq_neg]; linarith
  · rw [hfsp] at hdy; cases b <;> simp at hdy
  · exact absurd hfsp (findSuccessorPos_ne_nan (-y) (neg_pos.mpr hy))

/-- Negation reversal for Fp ordering in the rounding context:
    if -(roundDown y) ≤ -(roundUp x) with x < 0 and y < 0, then roundUp x ≤ roundDown y. -/
private theorem neg_round_le_imp_round_le {x y : R} (hx_neg : x < 0) (hy_neg : y < 0)
    (h : -(roundDown y) ≤ -(roundUp x)) : roundUp x ≤ roundDown y := by
  rcases hux : roundUp x with ux | ub | _
  · -- roundUp x = Fp.finite ux
    rw [hux, Fp.neg_finite] at h
    rcases hdy : roundDown y with dy | db | _
    · -- Both finite: toVal comparison
      rw [hdy, Fp.neg_finite, Fp.finite_le_finite_iff] at h
      rw [Fp.finite_le_finite_iff]
      apply FiniteFp.toVal_le_handle R
      · linarith [FiniteFp.le_toVal_le R h,
          FiniteFp.toVal_neg_eq_neg (R := R) (x := dy),
          FiniteFp.toVal_neg_eq_neg (R := R) (x := ux)]
      · intro ⟨_, hdyz⟩
        exfalso
        linarith [roundDown_neg_toVal_le hy_neg dy hdy, FiniteFp.toVal_isZero (R := R) hdyz]
    · cases db with
      | false => exact absurd hdy (roundDown_ne_pos_inf y)
      | true => rw [hdy] at h; simp [Fp.neg_def, Fp.le_def] at h
    · -- roundDown y = NaN: impossible (findPredecessor never returns NaN for y < 0)
      exfalso
      have hdy_eq : roundDown y = -(findSuccessorPos (-y) (neg_pos.mpr hy_neg)) := by
        unfold roundDown; exact findPredecessor_neg_eq y hy_neg
      rw [hdy] at hdy_eq
      rcases hfsp : findSuccessorPos (-y) (neg_pos.mpr hy_neg) with g | gb | _
      · rw [hfsp] at hdy_eq; simp at hdy_eq
      · rw [hfsp] at hdy_eq; cases gb <;> simp at hdy_eq
      · exact findSuccessorPos_ne_nan (-y) (neg_pos.mpr hy_neg) hfsp
  · -- roundUp x = infinite: impossible for x < 0
    exfalso; cases ub with
    | true => exact absurd hux (roundUp_ne_neg_inf x)
    | false =>
      have := roundUp_neg_le_zero x hx_neg
      rw [hux] at this; simp [Fp.le_def] at this
  · -- roundUp x = NaN: impossible for x < 0
    exfalso
    have : roundUp x = Fp.finite (-findPredecessorPos (-x) (neg_pos.mpr hx_neg)) := by
      unfold roundUp; exact findSuccessor_neg_eq x hx_neg
    rw [hux] at this; simp at this

/-- Helper for TE monotonicity: the hard case where rnTE(x) = roundUp(x) and
    rnTE(y) = roundDown(y) with 0 < x < y. In this case, either the FP intervals
    differ (roundUp(x).toVal ≤ y) or they match (midpoint contradiction). -/
private theorem rnTE_roundUp_le_roundDown_pos {x y : R} (hx : 0 < x) (hxy : x < y)
    (hrUx : roundNearestTiesToEven x = roundUp x)
    (hrDy : roundNearestTiesToEven y = roundDown y) :
    roundUp x ≤ roundDown y := by
  have hy : 0 < y := lt_trans hx hxy
  rcases hfU : roundUp x with f | b | _
  · -- roundUp(x) = Fp.finite f
    have hfpos : (0 : R) < f.toVal := lt_of_lt_of_le hx (roundUp_ge x f hfU)
    have hfs : f.s = false ∨ 0 < f.m := Or.inl (FiniteFp.toVal_pos_iff.mpr hfpos).1
    rcases le_or_gt (f.toVal : R) y with hfle | hfgt
    · rw [← hfU]; exact roundUp_le_roundDown_of_toVal_le f hfU hfle hfs
    · -- f.toVal > y: same interval
      have hsame := same_interval_pos hx hxy f hfU hfgt
      rcases hsame with ⟨hrD_eq, hrU_eq⟩
      by_cases hrDU : roundDown x = roundUp x
      · rw [← hfU, ← hrDU, hrD_eq]; exact Fp.le_refl _
      · -- Midpoint contradiction
        exfalso
        have hrDx : roundDown x = Fp.finite (findPredecessorPos x hx) := by
          unfold roundDown; rw [findPredecessor_pos_eq]
        have hval_ge : x ≥ FiniteFp.smallestPosSubnormal.toVal / 2 := by
          by_contra habs; push_neg at habs
          have h1 := rnEven_le_half_subnormal x hx habs
          rw [hrUx, hfU] at h1
          rw [(Fp.finite.injEq f 0).mp h1] at hfpos
          exact absurd hfpos (by rw [FiniteFp.toVal_zero]; exact lt_irrefl 0)
        have hval_lt : x < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp :=
          calc x ≤ f.toVal := roundUp_ge x f hfU
            _ ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
            _ < _ := largestFiniteFloat_lt_overflow_threshold
        have hrnx_ne_rD : roundNearestTiesToEven x ≠ roundDown x := by
          rw [hrUx]; exact Ne.symm hrDU
        have hx_ge_mid : x ≥ ((findPredecessorPos x hx).toVal (R := R) + (f.toVal : R)) / 2 := by
          by_contra hlt; push_neg at hlt
          exact hrnx_ne_rD (rnEven_below_mid_eq_roundDown x (findPredecessorPos x hx) f
            hx hval_ge hval_lt hrDx hfU hlt)
        have hy_gt_mid : y > ((findPredecessorPos x hx).toVal (R := R) + (f.toVal : R)) / 2 :=
          lt_of_le_of_lt hx_ge_mid hxy
        have hrDy_eq : roundDown y = Fp.finite (findPredecessorPos x hx) := hrD_eq ▸ hrDx
        have hrUy : roundUp y = Fp.finite f := hrU_eq ▸ hfU
        have rnTE_y_rU := rnEven_above_mid_eq_roundUp y (findPredecessorPos x hx) f hy
          (le_trans hval_ge (le_of_lt hxy))
          (calc y < f.toVal := hfgt
            _ ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
            _ < _ := largestFiniteFloat_lt_overflow_threshold)
          hrDy_eq hrUy hy_gt_mid
        exact hrDU (calc roundDown x = roundDown y := hrD_eq
          _ = roundUp y := by rw [← hrDy, rnTE_y_rU]
          _ = roundUp x := hrU_eq.symm)
  · -- roundUp(x) = Fp.infinite b
    exfalso
    cases b with
    | true => exact absurd hfU (roundUp_ne_neg_inf x)
    | false =>
      by_cases hthresh : x ≥ (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp
      · have := rnEven_ge_inf y (le_of_lt (lt_of_le_of_lt hthresh hxy))
        rw [hrDy] at this; exact roundDown_ne_pos_inf y this
      · push_neg at hthresh
        have hrDx : roundDown x = Fp.finite (findPredecessorPos x hx) := by
          unfold roundDown; rw [findPredecessor_pos_eq]
        have := rnEven_pos_succ_overflow x (findPredecessorPos x hx) hx hthresh hrDx hfU
        rw [hrUx, hfU] at this; exact absurd this (by simp)
  · exact absurd hfU (roundUp_pos_not_nan x hx)

/-- Helper for TA monotonicity: same structure as TE but using TA dispatch lemmas. -/
private theorem rnTA_roundUp_le_roundDown_pos {x y : R} (hx : 0 < x) (hxy : x < y)
    (hrUx : roundNearestTiesAwayFromZero x = roundUp x)
    (hrDy : roundNearestTiesAwayFromZero y = roundDown y) :
    roundUp x ≤ roundDown y := by
  have hy : 0 < y := lt_trans hx hxy
  rcases hfU : roundUp x with f | b | _
  · have hfpos : (0 : R) < f.toVal := lt_of_lt_of_le hx (roundUp_ge x f hfU)
    have hfs : f.s = false ∨ 0 < f.m := Or.inl (FiniteFp.toVal_pos_iff.mpr hfpos).1
    rcases le_or_gt (f.toVal : R) y with hfle | hfgt
    · rw [← hfU]; exact roundUp_le_roundDown_of_toVal_le f hfU hfle hfs
    · have hsame := same_interval_pos hx hxy f hfU hfgt
      rcases hsame with ⟨hrD_eq, hrU_eq⟩
      by_cases hrDU : roundDown x = roundUp x
      · rw [← hfU, ← hrDU, hrD_eq]; exact Fp.le_refl _
      · exfalso
        have hrDx : roundDown x = Fp.finite (findPredecessorPos x hx) := by
          unfold roundDown; rw [findPredecessor_pos_eq]
        have hval_ge : x ≥ FiniteFp.smallestPosSubnormal.toVal / 2 := by
          by_contra habs; push_neg at habs
          have h1 := rnAway_lt_half_subnormal x hx habs
          rw [hrUx, hfU] at h1
          rw [(Fp.finite.injEq f 0).mp h1] at hfpos
          exact absurd hfpos (by rw [FiniteFp.toVal_zero]; exact lt_irrefl 0)
        have hval_lt : x < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp :=
          calc x ≤ f.toVal := roundUp_ge x f hfU
            _ ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
            _ < _ := largestFiniteFloat_lt_overflow_threshold
        have hrnx_ne_rD : roundNearestTiesAwayFromZero x ≠ roundDown x := by
          rw [hrUx]; exact Ne.symm hrDU
        have hx_ge_mid : x ≥ ((findPredecessorPos x hx).toVal (R := R) + (f.toVal : R)) / 2 := by
          by_contra hlt; push_neg at hlt
          exact hrnx_ne_rD (rnAway_lt_mid_eq_roundDown x (findPredecessorPos x hx) f
            hx hval_ge hval_lt hrDx hfU hlt)
        have hy_gt_mid : y > ((findPredecessorPos x hx).toVal (R := R) + (f.toVal : R)) / 2 :=
          lt_of_le_of_lt hx_ge_mid hxy
        have hrDy_eq : roundDown y = Fp.finite (findPredecessorPos x hx) := hrD_eq ▸ hrDx
        have hrUy : roundUp y = Fp.finite f := hrU_eq ▸ hfU
        have rnTA_y_rU := rnAway_ge_mid_eq_roundUp y (findPredecessorPos x hx) f hy
          (le_trans hval_ge (le_of_lt hxy))
          (calc y < f.toVal := hfgt
            _ ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
            _ < _ := largestFiniteFloat_lt_overflow_threshold)
          hrDy_eq hrUy (le_of_lt hy_gt_mid)
        exact hrDU (calc roundDown x = roundDown y := hrD_eq
          _ = roundUp y := by rw [← hrDy, rnTA_y_rU]
          _ = roundUp x := hrU_eq.symm)
  · exfalso
    cases b with
    | true => exact absurd hfU (roundUp_ne_neg_inf x)
    | false =>
      by_cases hthresh : x ≥ (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp
      · have := rnAway_ge_inf y (le_of_lt (lt_of_le_of_lt hthresh hxy))
        rw [hrDy] at this; exact roundDown_ne_pos_inf y this
      · push_neg at hthresh
        have hrDx : roundDown x = Fp.finite (findPredecessorPos x hx) := by
          unfold roundDown; rw [findPredecessor_pos_eq]
        have := rnAway_pos_succ_overflow x (findPredecessorPos x hx) hx hthresh hrDx hfU
        rw [hrUx, hfU] at this; exact absurd this (by simp)
  · exact absurd hfU (roundUp_pos_not_nan x hx)

/-- roundNearestTiesToEven is monotone: x ≤ y → rnTE(x) ≤ rnTE(y) -/
theorem roundNearestTE_mono {x y : R} (h : x ≤ y) :
    roundNearestTiesToEven x ≤ roundNearestTiesToEven y := by
  rcases rnTE_eq_roundDown_or_roundUp' x with hrDx | hrUx
  · -- rnTE(x) = roundDown(x): easy via roundDown_mono
    rw [hrDx]; exact Fp.le_trans (roundDown_mono h) (roundDown_le_roundNearestTE y)
  · rcases rnTE_eq_roundDown_or_roundUp' y with hrDy | hrUy
    · -- Hard case: rnTE(x) = roundUp(x), rnTE(y) = roundDown(y)
      rw [hrUx, hrDy]
      rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; rw [← hrDy, hrUx]; exact Fp.le_refl _
      · -- x < y
        rcases le_or_gt 0 x with hx_nonneg | hx_neg
        · -- 0 ≤ x < y
          rcases eq_or_lt_of_le hx_nonneg with heq0 | hx_pos
          · subst heq0; rw [roundUp_zero (R := R), ← roundDown_zero (R := R)]
            exact roundDown_mono (le_of_lt hlt)
          · exact rnTE_roundUp_le_roundDown_pos hx_pos hlt hrUx hrDy
        · rcases le_or_gt 0 y with hy_nonneg | hy_neg
          · -- x < 0 ≤ y: zero bridge
            exact Fp.le_trans (roundUp_neg_le_zero x hx_neg)
              (Fp.le_trans (roundDown_zero (R := R) ▸ Fp.le_refl (Fp.finite 0))
                (roundDown_mono hy_nonneg))
          · -- x < y < 0: negation reduction to positive case
            have hx_ne : (x : R) ≠ 0 := ne_of_lt hx_neg
            have hy_ne : (y : R) ≠ 0 := ne_of_lt hy_neg
            have hrnTE_nx : roundNearestTiesToEven (-x) = roundDown (-x) := by
              rw [rnEven_neg_eq_neg x hx_ne, hrUx, roundDown_neg_eq_neg_roundUp x hx_ne]
            have hrnTE_ny : roundNearestTiesToEven (-y) = roundUp (-y) := by
              rw [rnEven_neg_eq_neg y hy_ne, hrDy, roundUp_neg_eq_neg_roundDown y hy_ne]
            have h_pos := rnTE_roundUp_le_roundDown_pos (neg_pos.mpr hy_neg)
              (neg_lt_neg_iff.mpr hlt) hrnTE_ny hrnTE_nx
            rw [roundUp_neg_eq_neg_roundDown y hy_ne,
                roundDown_neg_eq_neg_roundUp x hx_ne] at h_pos
            exact neg_round_le_imp_round_le hx_neg hy_neg h_pos
    · -- rnTE(y) = roundUp(y): easy via roundUp_mono
      rw [hrUx, hrUy]; exact roundUp_mono h

/-- roundNearestTiesAwayFromZero is monotone: x ≤ y → rnTA(x) ≤ rnTA(y) -/
theorem roundNearestTA_mono {x y : R} (h : x ≤ y) :
    roundNearestTiesAwayFromZero x ≤ roundNearestTiesAwayFromZero y := by
  rcases rnTA_eq_roundDown_or_roundUp' x with hrDx | hrUx
  · rw [hrDx]; exact Fp.le_trans (roundDown_mono h) (roundDown_le_roundNearestTA y)
  · rcases rnTA_eq_roundDown_or_roundUp' y with hrDy | hrUy
    · rw [hrUx, hrDy]
      rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; rw [← hrDy, hrUx]; exact Fp.le_refl _
      · rcases le_or_gt 0 x with hx_nonneg | hx_neg
        · rcases eq_or_lt_of_le hx_nonneg with heq0 | hx_pos
          · subst heq0; rw [roundUp_zero (R := R), ← roundDown_zero (R := R)]
            exact roundDown_mono (le_of_lt hlt)
          · exact rnTA_roundUp_le_roundDown_pos hx_pos hlt hrUx hrDy
        · rcases le_or_gt 0 y with hy_nonneg | hy_neg
          · exact Fp.le_trans (roundUp_neg_le_zero x hx_neg)
              (Fp.le_trans (roundDown_zero (R := R) ▸ Fp.le_refl (Fp.finite 0))
                (roundDown_mono hy_nonneg))
          · have hx_ne : (x : R) ≠ 0 := ne_of_lt hx_neg
            have hy_ne : (y : R) ≠ 0 := ne_of_lt hy_neg
            have hrnTA_nx : roundNearestTiesAwayFromZero (-x) = roundDown (-x) := by
              rw [rnAway_neg_eq_neg x hx_ne, hrUx, roundDown_neg_eq_neg_roundUp x hx_ne]
            have hrnTA_ny : roundNearestTiesAwayFromZero (-y) = roundUp (-y) := by
              rw [rnAway_neg_eq_neg y hy_ne, hrDy, roundUp_neg_eq_neg_roundDown y hy_ne]
            have h_pos := rnTA_roundUp_le_roundDown_pos (neg_pos.mpr hy_neg)
              (neg_lt_neg_iff.mpr hlt) hrnTA_ny hrnTA_nx
            rw [roundUp_neg_eq_neg_roundDown y hy_ne,
                roundDown_neg_eq_neg_roundUp x hx_ne] at h_pos
            exact neg_round_le_imp_round_le hx_neg hy_neg h_pos
    · rw [hrUx, hrUy]; exact roundUp_mono h

end Rounding
