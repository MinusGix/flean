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
import Flean.Rounding.Defs

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-- Round a positive normal value down -/
def roundNormalDown (x : R) (h : isNormalRange x) : FiniteFp :=
  -- Find the exponent by comparing with powers of 2
  -- We know x >= 2^min_exp from the range condition
  let e := findExponentDown x
  let binade_base := (2 : R) ^ e
  let scaled := x / binade_base
  -- scaled is now in [1, 2)
  let m_scaled := scaled * (2 : R) ^ (FloatFormat.prec - 1)
  let m := ⌊m_scaled⌋
  have mpos : m > 0 := by
    have hb := findExponentDown_div_binade_normal h
    apply Int.floor_pos.mpr
    apply le_trans
    apply hb.left
    conv_lhs => rw [← mul_one (x / 2 ^ (findExponentDown x))]
    rw [mul_le_mul_iff_of_pos_left (by linarith)]
    linearize
  have vf : IsValidFiniteVal e m.natAbs := by
    have hb := findExponentDown_div_binade_normal h
    apply findExponentDown_IsValidFiniteVal_normal
    split_ands
    <;> zify
    <;> rw [abs_of_pos mpos]
    · apply Int.le_floor.mpr
      zify
      conv_lhs => rw [← one_mul (2 ^ (FloatFormat.prec - 1))]
      rw [mul_le_mul_iff_of_pos_right]
      · exact hb.left
      · linearize
    · apply Int.floor_lt.mpr
      unfold m_scaled scaled binade_base e
      rw [FloatFormat.natCast_pow_prec_msb, mul_comm, mul_assoc]
      norm_num
      rw [← lt_div_iff₀' (by norm_num)]
      linarith
  FiniteFp.mk false e m.natAbs vf

/-- A rounded down x bounds the resulting finite float from above -/
theorem roundNormalDown_le (x : R) (h : isNormalRange x) : (roundNormalDown x h).toVal ≤ x := by
  unfold roundNormalDown
  simp
  unfold isNormalRange at h
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  norm_num
  obtain ⟨hb, _⟩ := findExponentDown_div_binade_normal h
  have hfloor_pos : 0 < ⌊x / 2 ^ findExponentDown x * (2 : R) ^ ((FloatFormat.prec : ℤ) - 1)⌋ := by
    apply Int.floor_pos.mpr
    apply le_mul_of_le_mul_of_nonneg_left
    · rw [mul_one]
      exact hb
    · apply one_le_zpow₀ (by norm_num : (1 : R) ≤ 2)
      have := FloatFormat.valid_prec
      omega
    · linarith
  have hcast_pos : (0 : R) < (⌊x / 2 ^ findExponentDown x * (2 : R) ^ ((FloatFormat.prec : ℤ) - 1)⌋ : R) := Int.cast_pos.mpr hfloor_pos
  rw [abs_of_pos hcast_pos]
  rw [div_eq_mul_inv, ← inv_zpow, inv_zpow', mul_assoc, ← zpow_add₀]
  rw [mul_comm, ← le_div_iff₀']
  rw [div_eq_mul_inv, ← inv_zpow, inv_zpow', neg_add, neg_sub', sub_neg_eq_add]
  rw [add_sub]
  apply Int.floor_le
  linearize
  norm_num

-- TODO: we could certainly put a tighter lower bound on roundNormalDown
theorem roundNormalDown_pos (x : R) (h : isNormalRange x) : (0 : R) < (roundNormalDown x h).toVal := by
  unfold roundNormalDown
  norm_num
  unfold FiniteFp.toVal FiniteFp.sign'
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  apply mul_pos
  rw [Int.cast_natAbs]
  apply Int.cast_pos.mpr
  -- apply abs_pos.mpr
  obtain ⟨h3, h4⟩ := findExponentDown_div_binade_normal h
  rw [abs_of_pos]
  apply Int.floor_pos.mpr
  · apply one_le_mul_of_one_le_of_one_le
    trivial
    apply one_le_zpow₀ (by norm_num) -- TODO linearize should solve this
    flinarith
  · apply Int.floor_pos.mpr
    apply one_le_mul_of_one_le_of_one_le
    trivial
    apply one_le_zpow₀ (by norm_num) -- TODO linearize should solve this
    flinarith
  · rw [FloatFormat.radix_val_eq_two]
    norm_num -- TODO: linearize shouldn't need norm num to get rid of cast for this
    linearize


theorem roundNormalDown_nonneg (x : R) (h : isNormalRange x) : (0 : R) ≤ (roundNormalDown x h).toVal := le_of_lt (roundNormalDown_pos x h)

/-- Round a positive normal value up -/
def roundNormalUp (x : R) (h : isNormalRange x) : Fp :=
  -- Find the exponent by comparing with powers of 2
  let e := findExponentDown x
  let binade_base := (2 : R) ^ e
  let scaled := x / binade_base
  -- scaled is now in [1, 2)
  let m_scaled := scaled * (2 : R) ^ (FloatFormat.prec - 1)
  let m := ⌈m_scaled⌉

  have mpos : m > 0 := by
    unfold m m_scaled scaled binade_base
    norm_num
    apply mul_pos
    apply div_pos
    exact isNormalRange_pos x h
    all_goals linearize

  -- Handle overflow within the binade
  if hm : 2^FloatFormat.prec ≤ m then
    -- Need to move to next binade
    if he : e + 1 > FloatFormat.max_exp then
      -- Overflow to infinity
      Fp.infinite false
    else
      have vf : IsValidFiniteVal (e + 1) (2^(FloatFormat.prec - 1)) := by
        norm_num at he
        unfold e at ⊢ he
        split_ands
        · have := findExponentDown_min x
          linarith
        · exact he
        · flinarith
        · left
          split_ands
          · rfl
          · flinarith
      Fp.finite (FiniteFp.mk false (e + 1) (2^(FloatFormat.prec - 1)) vf)
  else
    have vf : IsValidFiniteVal e m.natAbs := by
      norm_num at hm
      apply findExponentDown_IsValidFiniteVal_normal
      unfold isNormal
      zify
      rw [abs_of_pos mpos]
      unfold m m_scaled scaled binade_base at ⊢ hm
      have hx := findExponentDown_div_binade_normal h
      split_ands
      · apply Int.le_ceil_iff.mpr
        -- TODO: it'd be cool to have a tactic to say a simple "replace this value with the worst case lower bound from this other hypothesis"
        have j : 2^(FloatFormat.prec - 1) ≤ x / 2^e * 2^(FloatFormat.prec - 1) := by
          unfold e
          conv_lhs => rw [← one_mul (2^(FloatFormat.prec - 1))]
          rw [mul_le_mul_iff_of_pos_right] -- why is linarith not smart enough to use this
          linarith
          linearize
        apply lt_of_le_of_lt' j
        norm_num
      · exact hm
    Fp.finite (FiniteFp.mk false e m.natAbs vf)

@[simp]
theorem roundNormalUp_ne_nan (x : R) (h : isNormalRange x) : roundNormalUp x h ≠ Fp.NaN := by
  unfold roundNormalUp
  norm_num
  split_ifs <;> simp only [not_false_eq_true]

@[simp]
theorem roundNormalUp_ne_neg_infinite (x : R) (h : isNormalRange x) : roundNormalUp x h ≠ Fp.infinite true := by
  unfold roundNormalUp
  norm_num
  split_ifs
  <;> simp

/-- rounding a normal up is bounded above by the float's representation -/
lemma roundNormalUp_ge (x : R) (hnr : isNormalRange x) (f : FiniteFp)
  (h : roundNormalUp x hnr = Fp.finite f) : x ≤ f.toVal := by
  unfold roundNormalUp at h
  let e := findExponentDown x
  let binade_base := (2 : R) ^ e
  let scaled := x / binade_base
  let m_scaled := scaled * (2 : R) ^ (FloatFormat.prec - 1)
  let m := ⌈m_scaled⌉

  have m_pos : 0 < m := by
    apply Int.ceil_pos.mpr
    apply mul_pos
    apply div_pos (isNormalRange_pos x hnr)
    unfold binade_base
    all_goals linearize

  by_cases hm : 2^FloatFormat.prec ≤ m
  · -- Case: overflow within binade
    unfold m m_scaled scaled binade_base e at hm
    by_cases he : e + 1 > FloatFormat.max_exp
    · -- Overflow to infinity case - contradiction since h says result is finite
      unfold e at he
      simp only [ge_iff_le, hm, he, ↓reduceDIte] at h
      -- This returns Fp.infinite false, but h says result is Fp.finite f
      exfalso
      cases h
    · -- Move to next exponent case
      unfold e at he
      simp only [ge_iff_le, hm, he, ↓reduceDIte, Fp.finite.injEq] at h
      rw [← h]
      unfold FiniteFp.toVal FiniteFp.sign'
      rw [FloatFormat.radix_val_eq_two]
      simp
      -- Goal: x ≤ 2^(prec-1) * 2^(e + 1 - prec + 1) = 2^(e + 1)
      rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
      ring_nf
      -- Goal is x ≤ 2 ^ (e + 1)
      -- Use that findExponentDown gives us e such that 2^e ≤ x < 2^(e+1) in normal range
      have hbound := findExponentDown_div_binade_normal hnr
      have : x < binade_base * 2 := by
        unfold binade_base
        have : binade_base * 2 = (2 : R) ^ (e + 1) := by
          rw [← zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]
        rw [this]
        -- hbound says x / 2^e < 2, so x < 2^(e+1)
        have h1 : x / (2 : R) ^ e < 2 := hbound.right
        rw [zpow_add_one₀, mul_comm]
        exact (div_lt_iff₀ (zpow_pos (by norm_num : (0 : R) < 2) e)).mp h1
        norm_num
      unfold binade_base e at this
      rw [zpow_one_add₀, mul_comm]
      linarith
      norm_num
  · -- Case: no overflow, m < 2^prec
    unfold m m_scaled scaled binade_base e at hm
    simp only [ge_iff_le, hm, ↓reduceDIte, Fp.finite.injEq] at h
    rw [← h]
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp only [Bool.false_eq_true, ↓reduceIte, FloatFormat.pow_prec_sub_one_nat_int, one_mul,
      Int.cast_ofNat, ge_iff_le]
    -- Goal: x ≤ m.natAbs * 2^(e - prec + 1)
    -- First we need to show m > 0 and m.natAbs = m
    have h_natAbs := Int.cast_natAbs_pos (R := R) m_pos
    unfold m m_scaled scaled binade_base e at h_natAbs m_pos
    have m_pos' : 0 < x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1) := by
      apply Int.ceil_pos.mp
      trivial
    simp_all only [FloatFormat.pow_prec_sub_one_nat_int, Int.ceil_pos, ge_iff_le]

    -- Now x ≤ m * 2^(e - prec + 1)
    have h_pos : (0 : R) < (2 : R) ^ ((e : ℤ) - (FloatFormat.prec : ℤ) + 1) := by linearize
    -- Show x ≤ m * 2^(e - prec + 1)
    calc x = x / (2 : R) ^ e * (2 : R) ^ (FloatFormat.prec - 1) / (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e := by {
        rw [FloatFormat.pow_prec_sub_one_nat_int]
        rw [mul_div_cancel_right₀, div_mul_cancel₀]
        <;> linearize
      }
      _ ≤ (m : R) / (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e := by
        apply mul_le_mul_of_nonneg_right
        apply div_le_div_of_nonneg_right
        exact Int.le_ceil _
        all_goals linearize
      _ = (m : R) * (2 : R) ^ (e - (FloatFormat.prec : ℤ) + 1) := by
        rw [div_mul_eq_mul_div]
        rw [mul_div_assoc]
        rw [FloatFormat.pow_prec_sub_one_nat_int]
        rw [← zpow_sub₀ (by norm_num)]
        ring_nf
    unfold m m_scaled scaled binade_base e
    simp only [FloatFormat.pow_prec_sub_one_nat_int, le_refl]

theorem roundNormalUp_pos {x : R} {h : isNormalRange x} {f : FiniteFp} (hf : roundNormalUp x h = Fp.finite f): (0 : R) < f.toVal := by
  unfold roundNormalUp at hf
  extract_lets e binade_base scaled m_scaled m mpos at hf
  norm_num at hf
  split_ifs at hf with h1 h2
  · rw [Fp.finite.injEq] at hf
    rw [← hf]
    apply FiniteFp.toVal_pos
    <;> norm_num
  · rw [Fp.finite.injEq] at hf
    rw [← hf]
    apply FiniteFp.toVal_pos
    norm_num
    norm_num
    unfold m
    apply Int.ceil_ne_zero_pos
    apply mul_pos
    · apply div_pos
      · apply isNormalRange_pos x h
      · unfold binade_base
        linearize
    · linearize

theorem roundNormalUp_nonneg {x : R} {h : isNormalRange x} {f : FiniteFp} (hf : roundNormalUp x h = Fp.finite f): (0 : R) ≤ f.toVal := le_of_lt (roundNormalUp_pos hf)

end Rounding
