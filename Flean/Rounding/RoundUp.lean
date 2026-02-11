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
        = ((2 : ℕ) ^ (FloatFormat.prec.toNat - 1) : ℤ) := by simp only [Nat.cast_pow, Nat.cast_ofNat]
      _ > 1 := by omega
  have h_not_ge : ¬((2 : ℤ) ^ (FloatFormat.prec.toNat - 1) ≤ 1) := not_le.mpr h_k_lt
  simp only [h_not_ge, ↓reduceDIte]
  rfl

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

/-- `roundUp` of a positive value `mag * 2^e_base` produces a float with significand
`⌈val / 2^e_ulp⌉` in the no-carry case (q+1 < 2^prec).

Mirror of `roundDown_nat_mul_zpow` for the ceiling direction. -/
private lemma isValid_roundUpNatMulZpowTarget [FloatFormat]
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
      simp only [hk_ge, ↓reduceDIte, not_false_eq_true]
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
    (hmag : mag ≠ 0)
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
          apply zpow_le_zpow_right₀ (by norm_num); omega
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
  simp only [hceil_scaled, hbinade, hno_overflow, ↓reduceDIte, ite_false]
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

end RoundUp

end Rounding
