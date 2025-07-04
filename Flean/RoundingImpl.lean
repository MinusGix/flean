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

/-!
# Floating-Point Rounding Implementation

This file provides a complete implementation of IEEE 754 rounding modes.
It includes helper functions for finding neighboring floating-point values
and implements all five standard rounding modes.
-/

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-- Check if a positive number is in the subnormal range -/
def isSubnormalRange (x : R) : Prop :=
  0 < x ∧ x < (2 : R) ^ FloatFormat.min_exp

/-- Check if a positive number is in the normal range -/
def isNormalRange (x : R) : Prop :=
  (2 : R) ^ FloatFormat.min_exp ≤ x ∧ x < (2 : R) ^ (FloatFormat.max_exp + 1)

@[simp]
theorem isNormalRange_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) : isNormalRange x → 0 < x := by
  intro h
  have : (0 :R) < (2 : R) ^(FloatFormat.min_exp : ℤ) := by linearize
  apply lt_of_lt_of_le this h.left

-- theorem isNormalRange_isNormal_m (x : R) (h : isNormalRange x) : isNormal m

/-- Check if a positive number causes overflow -/
def isOverflow (x : R) : Prop :=
  (2 : R) ^ (FloatFormat.max_exp + 1) ≤ x

theorem isSubnormalRange_div_binade_upper {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {x : R} (h : isSubnormalRange x) :
    x / (2 : R)^(FloatFormat.min_exp - FloatFormat.prec + 1) < (2 : R)^((FloatFormat.prec : ℤ) - 1) := by
  unfold isSubnormalRange at h
  rw [div_lt_iff₀, ← zpow_add₀ (by norm_num)]
  norm_num
  exact h.right
  linearize

/-- Round a positive subnormal value down -/
def roundSubnormalDown (x : R) (h : isSubnormalRange x) : FiniteFp :=
  -- In subnormal range, spacing is uniform: 2^(min_exp - prec + 1)
  let ulp := (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)
  let k := ⌊x / ulp⌋
  if knz : k = 0 then
    0
  else
    have vf : IsValidFiniteVal FloatFormat.min_exp k.natAbs := by
      unfold isSubnormalRange at h
      have kpos : 0 < k := by
        apply lt_of_le_of_ne
        apply Int.floor_nonneg.mpr
        apply div_nonneg
        linarith
        unfold ulp; linearize
        omega

      apply IsValidFiniteVal_subnormal
      zify
      rw [abs_of_pos kpos]
      apply Int.floor_le_iff.mpr
      norm_num
      exact isSubnormalRange_div_binade_upper h
    FiniteFp.mk false FloatFormat.min_exp k.natAbs vf

/-- Round a positive subnormal value up -/
def roundSubnormalUp (x : R) (h : isSubnormalRange x) : FiniteFp :=
  -- In subnormal range, spacing is uniform: 2^(min_exp - prec + 1)
  let k := ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉
  if hk : k ≥ 2^(FloatFormat.prec - 1) then
    -- Transition to normal range
    FiniteFp.smallestPosNormal
  else
    have vf : IsValidFiniteVal FloatFormat.min_exp k.natAbs := by
      norm_num at hk
      have hu := isSubnormalRange_div_binade_upper h
      unfold isSubnormalRange at h
      have kpos : k > 0 := by
        apply Int.ceil_pos.mpr
        apply div_pos h.left
        linearize
      apply IsValidFiniteVal_subnormal
      zify
      rw [abs_of_pos kpos]
      apply Int.ceil_le.mpr
      have hk' := Int.ceil_lt_iff.mp hk
      norm_num at ⊢ hk'
      exact hk'

    FiniteFp.mk false FloatFormat.min_exp k.natAbs vf

theorem roundSubnormalDown_eq_zero_iff {x : R} {h : isSubnormalRange x} : roundSubnormalDown x h = 0 ↔ x < FiniteFp.smallestPosSubnormal.toVal := by
  unfold roundSubnormalDown
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  rw [FiniteFp.smallestPosSubnormal_toVal]
  have hz := FloatFormat.zpow_min_exp_prec_plus_one_le_zpow_min_exp (R := R)
  split_ifs with h1
  · have h1 := Int.floor_eq_zero_iff.mp h1
    obtain ⟨h1, h2⟩ := Set.mem_Ico.mp h1
    rw [div_lt_iff₀, one_mul] at h2
    constructor
    <;> intro h
    · trivial
    · trivial
    · linearize
  · constructor
    rw [FiniteFp.zero_def]
    norm_num
    · intro h h2
      rw [div_lt_iff₀, one_mul] at h2
      trivial
      linearize
    · intro h2
      rw [FiniteFp.zero_def]
      norm_num
      constructor
      · apply div_nonneg h.left.le (by linearize)
      · rw [div_lt_one_iff]
        left
        constructor
        · linearize
        · trivial

-- Fundamental ceiling property for subnormal range
lemma roundSubnormalUp_ge (x : R) (hsr : isSubnormalRange x) (f : FiniteFp)
  (h : roundSubnormalUp x hsr = f) : x ≤ f.toVal := by
  unfold roundSubnormalUp at h
  let k := ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉
  by_cases hk : k ≥ 2^(FloatFormat.prec - 1)
  · -- Case: k ≥ 2^(prec-1), transition to normal range
    unfold k at hk
    simp only [ge_iff_le, hk, ↓reduceDIte, Fp.finite.injEq] at h
    -- h now shows: f = FiniteFp.smallestPosNormal
    rw [← h, FiniteFp.smallestPosNormal_toVal]
    exact le_of_lt (hsr.right)
  · -- Case: k < 2^(prec-1), stays in subnormal range
    unfold k at hk
    simp only [ge_iff_le, hk, ↓reduceDIte, Fp.finite.injEq] at h
    rw [← h]
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Int.cast_ofNat, ge_iff_le]
    -- Goal: x ≤ k.natAbs * 2^(min_exp - prec + 1)
    -- We know k = ⌈x / 2^(min_exp - prec + 1)⌉ and k > 0 in subnormal range
    -- So k.natAbs = k and k ≥ x / 2^(min_exp - prec + 1)
    -- Therefore k * 2^(min_exp - prec + 1) ≥ x
    have k_pos : 0 < k := Int.ceil_div_pos hsr.left (by linearize)
    rw [Int.cast_natAbs_pos k_pos]
    have h_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by linearize
    -- x / 2^(min_exp - prec + 1) ≤ k
    -- So x ≤ k * 2^(min_exp - prec + 1)
    calc x = x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) *
              (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by {
        rw [div_mul_cancel₀ _ (ne_of_gt h_pos)]
      }
      _ ≤ (k : R) * (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
        apply mul_le_mul_of_nonneg_right
        · exact Int.le_ceil _
        · linearize

theorem roundSubnormalUp_pos {x : R} {hsr : isSubnormalRange x} : (0 : R) < (roundSubnormalUp x hsr).toVal := by
  unfold roundSubnormalUp
  extract_lets k
  split_ifs with h1
  · apply FiniteFp.smallestPosNormal_toVal_pos
  · norm_num
    apply FiniteFp.toVal_pos
    norm_num
    norm_num
    apply Int.ceil_ne_zero_pos
    apply div_pos
    · exact hsr.left
    · linearize

theorem roundSubnormalUp_nonneg {x : R} {hsr : isSubnormalRange x} : (0 : R) ≤ (roundSubnormalUp x hsr).toVal := le_of_lt roundSubnormalUp_pos

theorem roundSubnormalDown_eq_zero_iff' {x : R} {h : isSubnormalRange x} : roundSubnormalDown x h = 0 ↔ x < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
  rw [← FiniteFp.smallestPosSubnormal_toVal]
  exact roundSubnormalDown_eq_zero_iff

/-- A rounded down x bounds the resulting finite float from above -/
theorem roundSubnormalDown_le (x : R) (h : isSubnormalRange x) : (roundSubnormalDown x h).toVal ≤ x := by
  unfold roundSubnormalDown
  simp
  unfold isSubnormalRange at h
  split
  · rw [FiniteFp.toVal_zero]
    linarith
  · rename_i h'
    rw [not_and_or] at h'
    norm_num at h'
    unfold FiniteFp.toVal FiniteFp.sign'
    norm_num
    have : ¬(x / 2 ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1) < 0) := by
      norm_num
      apply div_nonneg
      linarith
      linearize
    simp only [this, false_or] at h'

    rw [Int.cast_natAbs_pos (Int.floor_pos.mpr (by trivial))]

    rw[FloatFormat.radix_val_eq_two]
    apply mul_le_of_le_div₀
    · linarith
    · linearize
    · rw [Int.cast_two]
      apply Int.floor_le

theorem roundSubnormalDown_nonneg {x : R} {h : isSubnormalRange x} : (0 : R) ≤ (roundSubnormalDown x h).toVal := by
  unfold roundSubnormalDown
  simp
  unfold isSubnormalRange at h
  split_ifs
  · rw [FiniteFp.toVal_zero]
  · unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    norm_num
    apply mul_nonneg
    apply Nat.cast_nonneg
    linearize

theorem roundSubnormalDown_pos {x : R} {h : isSubnormalRange x} (hx : FiniteFp.smallestPosSubnormal.toVal ≤ x) : (0 : R) < (roundSubnormalDown x h).toVal := by
  unfold roundSubnormalDown
  extract_lets ulp k
  have : k ≠ 0 := by
    apply Int.floor_ne_zero_ge_one
    unfold ulp
    apply (one_le_div₀ ?_).mpr
    rw [FiniteFp.smallestPosSubnormal_toVal] at hx
    exact hx
    linearize
  simp only [this, ↓reduceDIte, gt_iff_lt]
  apply FiniteFp.toVal_pos
  · norm_num
  · norm_num
    exact this

/-- If the output is positive, then the input is at least the smallest positive subnormal (and thus wasn't rounded down to zero) -/
theorem roundSubnormalDown_pos_iff {x : R} {h : isSubnormalRange x} : FiniteFp.smallestPosSubnormal.toVal ≤ x ↔ (0 : R) < (roundSubnormalDown x h).toVal := by
  constructor
  · exact roundSubnormalDown_pos
  · intro hf
    unfold roundSubnormalDown at hf
    extract_lets ulp k at hf
    split_ifs at hf with h1
    · rw [FiniteFp.toVal_zero] at hf
      linarith
    · norm_num at hf
      obtain ⟨h2, h3⟩ := FiniteFp.toVal_pos_iff.mpr hf
      norm_num at h2 h3
      unfold k ulp at h3
      cases' (Int.floor_ne_zero_iff).mp h3 with h4 h5
      · rw [FiniteFp.smallestPosSubnormal_toVal]
        rw [one_le_div₀] at h4
        trivial
        linearize
      · rw [FiniteFp.smallestPosSubnormal_toVal]
        rw [div_lt_iff₀, zero_mul] at h5
        have xpos := h.left
        linarith
        linearize

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
    rw [mul_le_mul_left (by linarith)]
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
      rw [mul_le_mul_right]
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
  rw [Int.cast_natAbs_pos]
  · rw [div_eq_mul_inv, ← inv_zpow, inv_zpow', mul_assoc, ← zpow_add₀]
    rw [mul_comm, ← le_div_iff₀']
    rw [div_eq_mul_inv, ← inv_zpow, inv_zpow', neg_add, neg_sub', sub_neg_eq_add]
    rw [add_sub]
    apply Int.floor_le
    linearize
    norm_num
  · apply Int.floor_pos.mpr
    apply le_mul_of_le_mul_of_nonneg_left
    · rw [mul_one]
      exact hb
    · apply one_le_zpow₀ (by norm_num) -- TODO linearize should solve this
      flinarith
    · linarith

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
          rw [mul_le_mul_right] -- why is linarith not smart enough to use this
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

/-- Find the predecessor of a positive number -/
def findPredecessorPos (x : R) (hpos : 0 < x) : FiniteFp :=
  -- Check ranges manually without decidability
  if hlt : x < (2 : R) ^ FloatFormat.min_exp then
    -- Subnormal range
    roundSubnormalDown x ⟨hpos, hlt⟩
  else if hlt2 : x < (2 : R) ^ (FloatFormat.max_exp + 1) then
    -- Normal range
    roundNormalDown x ⟨le_of_not_gt hlt, hlt2⟩
  else
    -- x is too large, return largest finite float
    FiniteFp.largestFiniteFloat

/-- Find the successor of a positive number -/
def findSuccessorPos (x : R) (hpos : 0 < x) : Fp :=
  -- Check ranges manually without decidability
  if hlt : x < (2 : R) ^ FloatFormat.min_exp then
    -- Subnormal range
    Fp.finite (roundSubnormalUp x ⟨hpos, hlt⟩)
  else if hlt2 : x < (2 : R) ^ (FloatFormat.max_exp + 1) then
    -- Normal range
    roundNormalUp x ⟨le_of_not_gt hlt, hlt2⟩
  else
    -- Overflow
    Fp.infinite false

@[simp]
theorem findSuccessorPos_ne_nan (x : R) (hpos : 0 < x) : findSuccessorPos x hpos ≠ Fp.NaN := by
  unfold findSuccessorPos
  split_ifs
  <;> simp

@[simp]
theorem findSuccessorPos_ne_neg_inf (x : R) (hpos : 0 < x) : findSuccessorPos x hpos ≠ Fp.infinite true := by
  unfold findSuccessorPos
  split_ifs
  <;> simp

theorem findPredecessorPos_pos {x : R} {hpos : 0 < x} (hx : FiniteFp.smallestPosSubnormal.toVal ≤ x) : (0 : R) < (findPredecessorPos x hpos).toVal := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · apply roundSubnormalDown_pos hx
  · apply roundNormalDown_pos
  · apply FiniteFp.largestFiniteFloat_toVal_pos

/-- If the output is positive, then the input is at least the smallest positive subnormal (and thus wasn't rounded down to zero) -/
theorem findPredecessorPos_pos_iff {x : R} {hpos : 0 < x} : FiniteFp.smallestPosSubnormal.toVal ≤ x ↔ (0 : R) < (findPredecessorPos x hpos).toVal := by
  constructor
  · exact findPredecessorPos_pos
  · intro hf
    unfold findPredecessorPos at hf
    split_ifs at hf with h1 h2
    · apply roundSubnormalDown_pos_iff.mpr hf
    · norm_num at h1
      rw [FiniteFp.smallestPosSubnormal_toVal]
      apply le_trans' h1
      gcongr; norm_num
      fomega
    · norm_num at h1 h2
      rw [FiniteFp.smallestPosSubnormal_toVal]
      apply le_trans' h1
      gcongr; norm_num
      fomega

theorem findPredecessorPos_nonneg {x : R} {hpos : 0 < x} : (0 : R) ≤ (findPredecessorPos x hpos).toVal := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · apply roundSubnormalDown_nonneg
  · apply roundNormalDown_nonneg
  · apply le_of_lt FiniteFp.largestFiniteFloat_toVal_pos

-- findPredecessorPos preserves the floor property
lemma findPredecessorPos_le (x : R) (hpos : 0 < x) : (findPredecessorPos x hpos).toVal ≤ x := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · apply roundSubnormalDown_le
  · apply roundNormalDown_le
  · linarith [FiniteFp.largestFiniteFloat_lt_maxExp_succ (R := R)]

/-- Find the largest floating-point value less than or equal to x (predecessor) -/
def findPredecessor (x : R) : Fp :=
  if h : x = 0 then Fp.finite 0
  else if hpos : 0 < x then
    Fp.finite (findPredecessorPos x hpos)
  else
    -(findSuccessorPos (-x) (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) h)))

@[simp]
theorem findPredecessor_zero : findPredecessor (0 : R) = Fp.finite 0 := by simp [findPredecessor]

@[simp]
theorem findPredecessor_pos_eq (x : R) (hpos : 0 < x) : findPredecessor x = Fp.finite (findPredecessorPos x hpos) := by
  unfold findPredecessor findPredecessorPos
  simp_all only [↓reduceDIte, dite_eq_ite, ite_eq_right_iff]
  intro hx
  linarith

@[simp]
theorem findPredecessor_neg_eq (x : R) (hneg : x < 0) :
  findPredecessor x = -(findSuccessorPos (-x) (neg_pos.mpr hneg)) := by
  have hnz : x ≠ 0 := by linarith
  have hnpos : ¬0 < x := by linarith
  simp [findPredecessor, hneg, hnz, hnpos]

-- findSuccessorPos preserves the ceiling property
lemma findSuccessorPos_ge (x : R) (hpos : 0 < x) (f : FiniteFp)
  (h : findSuccessorPos x hpos = Fp.finite f) : x ≤ f.toVal := by
  unfold findSuccessorPos at h
  split_ifs at h with h_sub h_normal
  · -- Subnormal case
    rw [Fp.finite.injEq] at h
    exact roundSubnormalUp_ge x ⟨hpos, h_sub⟩ f h
  · -- Normal case
    exact roundNormalUp_ge x ⟨le_of_not_gt h_sub, h_normal⟩ f h
  -- Overflow case handled automatically

theorem findSuccessorPos_pos {x : R} {hpos : 0 < x} {f : FiniteFp} (hf : findSuccessorPos x hpos = Fp.finite f): (0 : R) < f.toVal := by
  unfold findSuccessorPos at hf
  split_ifs at hf with h1 h2
  · rw [Fp.finite.injEq] at hf
    rw [← hf]
    apply roundSubnormalUp_pos
  · exact roundNormalUp_pos hf

/-- Find the smallest floating-point value greater than or equal to x (successor) -/
def findSuccessor (x : R) : Fp :=
  if h : x = 0 then Fp.finite 0
  else if hpos : 0 < x then
    findSuccessorPos x hpos
  else
    -- x < 0: use symmetry
    have hne : x ≠ 0 := h
    have hneg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hne)
    let v := findPredecessorPos (-x) hneg
    Fp.finite (-v)

theorem findSuccessor_symm (x : R) (h : x < 0) : findSuccessor x = -findPredecessor (-x) := by
  unfold findSuccessor findPredecessor
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · extract_lets hne hneg v
    unfold v
    rw [Fp.neg_finite]
  · linarith

@[simp]
theorem findSuccessor_zero : findSuccessor (0 : R) = Fp.finite 0 := by simp [findSuccessor]

@[simp]
theorem findSuccessor_pos_eq (x : R) (hpos : 0 < x) : findSuccessor x = findSuccessorPos x hpos := by
  unfold findSuccessor findSuccessorPos
  simp_all only [↓reduceDIte, dite_eq_ite, ite_eq_right_iff]
  intro a
  subst a
  split
  next h =>
    simp_all only [Fp.finite.injEq]
    linarith
  next h => simp_all only [lt_self_iff_false]

@[simp]
theorem findSuccessor_neg_eq (x : R) (hneg : x < 0) :
  findSuccessor x = Fp.finite (-findPredecessorPos (-x) (neg_pos.mpr hneg)) := by
  have hnz : x ≠ 0 := by linarith
  have hnpos : ¬0 < x := by linarith
  simp [findSuccessor, hneg, hnz, hnpos]

end Rounding
