import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational

import Flean.Basic
import Flean.Ulp
import Flean.Ufp
import Flean.Gsplit.Gsplit
import Flean.Util
import Flean.Rounding.Defs

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-! ## Helper theorems for normal rounding -/

/-- When n > 0, casting natAbs to R equals casting n directly -/
theorem Int.cast_natAbs_of_pos {n : ℤ} (hn : 0 < n) : (↑n.natAbs : R) = (↑n : R) := by
  rw [Nat.cast_natAbs, abs_of_nonneg (le_of_lt hn)]

/-- The floor of a normal value scaled to the precision range is positive -/
theorem floor_scaled_normal_pos (x : R) (hx : isNormalRange x) :
    0 < ⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ := by
  apply Int.floor_pos.mpr
  apply one_le_mul_of_one_le_of_one_le
  · exact (findExponentDown_div_binade_normal hx).left
  · have hp := FloatFormat.prec_sub_one_pos
    exact one_le_zpow₀ (by norm_num : (1 : R) ≤ 2) (by omega)

/-- Scaling preserves inequalities in the same binade -/
theorem scaled_le_of_le {x y : R} (e : ℤ) (h : x ≤ y) :
    x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) ≤
    y / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) := by
  apply mul_le_mul_of_nonneg_right
  · apply div_le_div_of_nonneg_right h
    exact le_of_lt (zpow_pos (by norm_num : (0 : R) < 2) _)
  · have hp := FloatFormat.prec_sub_one_pos
    exact zpow_nonneg (by norm_num : (0 : R) ≤ 2) _

/-! ## Int/Nat power bounds for omega

These helper lemmas convert ℤ power inequalities to ℕ inequalities that omega can solve.
The key pattern is: `(2 : ℤ)^n.toNat = ↑((2 : ℕ)^n.toNat)` via Int.two_pow_eq_nat_cast,
then omega can compare natural numbers directly. -/

/-- Convert a lower bound from ℤ power to ℕ for omega -/
theorem int_pow_le_natAbs_of_nonneg {m : ℤ} (hm_pos : 0 < m) (n : ℕ)
    (h : (2 : ℤ)^n ≤ m) : 2^n ≤ m.natAbs := by
  have hnatAbs_eq : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt hm_pos)
  have h1 : (2 : ℤ)^n ≤ m.natAbs := by rw [hnatAbs_eq]; exact h
  simp only [Int.two_pow_eq_nat_cast] at h1
  omega

/-- Convert an upper bound from ℤ power to ℕ for omega -/
theorem natAbs_lt_int_pow_of_nonneg {m : ℤ} (hm_pos : 0 < m) (n : ℕ)
    (h : m < (2 : ℤ)^n) : m.natAbs < 2^n := by
  have hnatAbs_eq : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt hm_pos)
  have h1 : (m.natAbs : ℤ) < (2 : ℤ)^n := by rw [hnatAbs_eq]; exact h
  simp only [Int.two_pow_eq_nat_cast] at h1
  omega

/-- A positive integer floor is normal if it satisfies the scaled bounds -/
theorem floor_isNormal_of_bounds (x : R) (hx : isNormalRange x) :
    let e := findExponentDown x
    let m := ⌊x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1)⌋
    let hb := findExponentDown_div_binade_normal hx
    isNormal m.natAbs := by
  intro e m hb
  have mpos := floor_scaled_normal_pos x hx
  have hnatAbs_eq : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt mpos)
  -- Lower bound
  have hm_lb_R : (2 : R)^(FloatFormat.prec - 1) ≤ x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) := by
    calc (2 : R)^(FloatFormat.prec - 1)
        = 1 * (2 : R)^(FloatFormat.prec - 1) := by rw [one_mul]
      _ ≤ (x / 2 ^ e) * (2 : R)^(FloatFormat.prec - 1) := by
          apply mul_le_mul_of_nonneg_right hb.left
          exact zpow_nonneg (by norm_num) _
  have hm_lb_int : (2 : ℤ)^(FloatFormat.prec - 1).toNat ≤ m := by
    apply Int.le_floor.mpr
    simp only [Int.cast_pow, Int.cast_ofNat]
    calc (2 : R)^(FloatFormat.prec - 1).toNat
        = (2 : R)^(FloatFormat.prec - 1) := FloatFormat.natCast_pow_prec_pred
      _ ≤ x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) := hm_lb_R
  -- Upper bound
  have hm_ub_R : x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) < (2 : R)^FloatFormat.prec := by
    have hpow_eq : (2 : R)^(FloatFormat.prec - 1) = (2 : R)^FloatFormat.prec / 2 := by
      rw [zpow_sub_one₀ (by norm_num : (2 : R) ≠ 0), div_eq_mul_inv]
    calc x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1)
        = x / 2 ^ e * ((2 : R)^FloatFormat.prec / 2) := by rw [hpow_eq]
      _ < 2 * ((2 : R)^FloatFormat.prec / 2) := by
          apply mul_lt_mul_of_pos_right hb.right
          apply div_pos (zpow_pos (by norm_num) _) (by norm_num)
      _ = (2 : R)^FloatFormat.prec := by ring
  have hm_ub_int : m < (2 : ℤ)^FloatFormat.prec.toNat := by
    apply Int.floor_lt.mpr
    simp only [Int.cast_pow, Int.cast_ofNat]
    have hp := FloatFormat.prec_pos
    calc (x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) : R) < (2 : R)^FloatFormat.prec := hm_ub_R
      _ = (2 : R)^FloatFormat.prec.toNat := by
          rw [← zpow_natCast]; congr 1
          exact (Int.toNat_of_nonneg (by omega)).symm
  -- Convert to ℕ
  constructor
  · exact int_pow_le_natAbs_of_nonneg mpos _ hm_lb_int
  · exact natAbs_lt_int_pow_of_nonneg mpos _ hm_ub_int

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
  have mpos : m > 0 := floor_scaled_normal_pos x h
  have vf : IsValidFiniteVal e m.natAbs :=
    findExponentDown_IsValidFiniteVal_normal x m.natAbs (floor_isNormal_of_bounds x h)
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
  obtain ⟨h3, h4⟩ := findExponentDown_div_binade_normal h
  rw [abs_of_pos]
  apply Int.floor_pos.mpr
  · apply one_le_mul_of_one_le_of_one_le
    trivial
    apply one_le_zpow₀ (by norm_num)
    have := FloatFormat.valid_prec
    omega
  · apply Int.floor_pos.mpr
    apply one_le_mul_of_one_le_of_one_le
    trivial
    apply one_le_zpow₀ (by norm_num)
    have := FloatFormat.valid_prec
    omega
  · rw [FloatFormat.radix_val_eq_two]
    norm_num
    linearize


theorem roundNormalDown_nonneg (x : R) (h : isNormalRange x) : (0 : R) ≤ (roundNormalDown x h).toVal := le_of_lt (roundNormalDown_pos x h)

/-- roundNormalDown has toVal ≥ 2^(findExponentDown y) -/
theorem roundNormalDown_ge_zpow_exp (y : R) (h : isNormalRange y) :
    (2 : R) ^ findExponentDown y ≤ (roundNormalDown y h).toVal (R := R) := by
  -- Key idea: toVal = m * 2^(e - prec + 1) where m ≥ 2^(prec-1)
  -- So toVal ≥ 2^(prec-1) * 2^(e - prec + 1) = 2^e
  unfold roundNormalDown FiniteFp.toVal FiniteFp.sign'
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [FloatFormat.radix_val_eq_two]
  have hb := findExponentDown_div_binade_normal h
  have hprec_ge := FloatFormat.valid_prec
  -- floor(y/2^e * 2^(prec-1)) ≥ 1 * 2^(prec-1) = 2^(prec-1)
  have hscaled_ge : (2 : R) ^ (FloatFormat.prec - 1) ≤ y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1) := by
    calc (2 : R) ^ (FloatFormat.prec - 1)
        = 1 * (2 : R) ^ (FloatFormat.prec - 1) := by ring
      _ ≤ y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1) := by
          apply mul_le_mul_of_nonneg_right hb.left
          positivity
  have hfloor_pos : 0 < ⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ := by
    apply Int.floor_pos.mpr
    calc (1 : R) ≤ (2 : R) ^ (FloatFormat.prec - 1) := one_le_zpow₀ (by norm_num : (1 : R) ≤ 2) (by omega)
      _ ≤ y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1) := hscaled_ge
  -- floor(...) ≥ 2^(prec-1) as integers
  have hfloor_lb_int : (2 : ℤ) ^ (FloatFormat.prec - 1).toNat ≤ ⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ := by
    rw [Int.le_floor]
    simp only [Int.cast_pow, Int.cast_ofNat]
    calc (2 : R)^(FloatFormat.prec - 1).toNat
        = (2 : R)^(FloatFormat.prec - 1) := FloatFormat.natCast_pow_prec_pred
      _ ≤ y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1) := hscaled_ge
  -- Simplify the goal: natAbs of floor = floor since floor is positive
  have hfloor_cast_eq : (↑(⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋.natAbs) : R) =
      (⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) := by
    rw [Nat.cast_natAbs]
    -- Goal: ↑|⌊...⌋| = ↑⌊...⌋  where |.| is integer absolute value
    congr 1
    exact abs_of_pos hfloor_pos
  rw [hfloor_cast_eq]
  -- 2^e = 2^(prec-1) * 2^(e - prec + 1) ≤ floor(...) * 2^(e - prec + 1)
  have hpow_split : (2 : R) ^ findExponentDown y =
      (2 : R) ^ (FloatFormat.prec - 1 : ℤ) * (2 : R) ^ (findExponentDown y - (FloatFormat.prec - 1 : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
    congr 1; ring
  have hexp_eq2 : findExponentDown y - (FloatFormat.prec - 1 : ℤ) = findExponentDown y - ↑FloatFormat.prec + 1 := by ring
  -- Convert the integer floor bound to R using zpow
  have hfloor_lb : (2 : R) ^ (FloatFormat.prec - 1 : ℤ) ≤ ⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ := by
    -- From hfloor_lb_int: (2 : ℤ)^(prec-1).toNat ≤ ⌊...⌋ in ℤ, cast to R
    have h_cast := (@Int.cast_mono R _ _ _ _) hfloor_lb_int
    -- h_cast : ↑((2 : ℤ)^n) ≤ ↑⌊...⌋, simp to get (2 : R)^n
    simp only [Int.cast_pow, Int.cast_ofNat] at h_cast
    -- h_cast : (2 : R) ^ (FloatFormat.prec - 1).toNat ≤ ↑⌊...⌋
    calc (2 : R) ^ (FloatFormat.prec - 1 : ℤ)
        = (2 : R) ^ (FloatFormat.prec - 1).toNat := FloatFormat.natCast_pow_prec_pred.symm
      _ ≤ ⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ := h_cast
  have hmain : (2 : R) ^ findExponentDown y ≤
      ↑⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ *
      (2 : R) ^ (findExponentDown y - ↑FloatFormat.prec + 1) := by
    calc (2 : R) ^ findExponentDown y
        = (2 : R) ^ (FloatFormat.prec - 1 : ℤ) * (2 : R) ^ (findExponentDown y - (FloatFormat.prec - 1 : ℤ)) := hpow_split
      _ ≤ ↑⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ *
          (2 : R) ^ (findExponentDown y - (FloatFormat.prec - 1 : ℤ)) := by
            apply mul_le_mul_of_nonneg_right hfloor_lb
            positivity
      _ = ↑⌊y / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ *
          (2 : R) ^ (findExponentDown y - ↑FloatFormat.prec + 1) := by
            rw [hexp_eq2]
  convert hmain using 2 <;> norm_cast

/-- roundNormalDown y has toVal ≥ 2^min_exp (the smallest normal value) -/
theorem roundNormalDown_ge_zpow_min_exp (y : R) (h : isNormalRange y) :
    (2 : R) ^ FloatFormat.min_exp ≤ (roundNormalDown y h).toVal := by
  -- Use transitivity: 2^min_exp ≤ 2^(findExponentDown y) ≤ toVal
  have hexp_ge := findExponentDown_min y
  calc (2 : R) ^ FloatFormat.min_exp
      ≤ (2 : R) ^ findExponentDown y := by
          apply zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2)
          exact hexp_ge
    _ ≤ (roundNormalDown y h).toVal := roundNormalDown_ge_zpow_exp y h

/-- roundNormalDown is monotone on toVal -/
theorem roundNormalDown_toVal_mono {x y : R} (hx : isNormalRange x) (hy : isNormalRange y) (h : x ≤ y) :
    (roundNormalDown x hx).toVal (R := R) ≤ (roundNormalDown y hy).toVal (R := R) := by
  -- Case 1: same binade - floor monotonicity applies directly
  -- Case 2: x in lower binade - roundNormalDown x ≤ x < 2^ey ≤ roundNormalDown y
  have hex := findExponentDown_normal x hx
  have hey := findExponentDown_normal y hy
  by_cases hexp : findExponentDown x = findExponentDown y
  · -- Same binade: use floor monotonicity
    -- Both have same exponent e, so toVal = ⌊scaled⌋ * 2^(e - prec + 1)
    -- Since x ≤ y and same e, scaled_x ≤ scaled_y, so ⌊scaled_x⌋ ≤ ⌊scaled_y⌋
    unfold roundNormalDown FiniteFp.toVal FiniteFp.sign'
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [hexp, FloatFormat.radix_val_eq_two]
    -- Goal: ↑⌊scaled_x⌋.natAbs * 2^(...) ≤ ↑⌊scaled_y⌋.natAbs * 2^(...)
    -- Since floors are positive, natAbs = floor
    have hfloor_x_pos : 0 < ⌊x / 2 ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌋ := by
      rw [← hexp]; exact floor_scaled_normal_pos x hx
    have hfloor_y_pos := floor_scaled_normal_pos y hy
    -- The scaled inequality follows from h : x ≤ y
    have hscaled_le := scaled_le_of_le (findExponentDown y) h
    -- Use Nat.cast_natAbs and abs_of_nonneg to simplify
    simp only [Nat.cast_natAbs, abs_of_nonneg (le_of_lt hfloor_x_pos),
               abs_of_nonneg (le_of_lt hfloor_y_pos), Nat.cast_ofNat]
    apply mul_le_mul_of_nonneg_right
    · -- ⌊scaled_x⌋ ≤ ⌊scaled_y⌋
      apply Int.cast_le.mpr
      exact Int.floor_le_floor hscaled_le
    · -- 2^(e - prec + 1) ≥ 0
      linearize
  · -- Different binades: x is in a lower binade than y
    have hxpos := isNormalRange_pos x hx
    have hmono : findExponentDown x ≤ findExponentDown y := by
      rw [hex, hey]
      exact Int.log_mono_right hxpos h
    have hexp_lt : findExponentDown x < findExponentDown y := lt_of_le_of_ne hmono hexp
    have hexp_bound : findExponentDown x + 1 ≤ findExponentDown y := by linarith
    apply le_of_lt
    calc (roundNormalDown x hx).toVal (R := R)
        ≤ x := roundNormalDown_le x hx
      _ < (2 : R) ^ (Int.log 2 x + 1) := Int.lt_zpow_succ_log_self (by norm_num : 1 < 2) x
      _ = (2 : R) ^ (findExponentDown x + 1) := by rw [hex]
      _ ≤ (2 : R) ^ findExponentDown y := by
          apply zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2)
          exact hexp_bound
      _ ≤ (roundNormalDown y hy).toVal := roundNormalDown_ge_zpow_exp y hy

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
  if hm : (2 : ℤ)^FloatFormat.prec.toNat ≤ m then
    -- Need to move to next binade
    if he : e + 1 > FloatFormat.max_exp then
      -- Overflow to infinity
      Fp.infinite false
    else
      have vf : IsValidFiniteVal (e + 1) (2^(FloatFormat.prec - 1).toNat) := by
        norm_num at he
        unfold e at ⊢ he
        split_ands
        · have := findExponentDown_min x
          linarith
        · exact he
        · have hp := FloatFormat.valid_prec
          have hpow_lt := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
          omega
        · left
          split_ands
          · -- 2^(prec-1).toNat ≤ 2^(prec-1).toNat is reflexive
            rfl
          · have hp := FloatFormat.valid_prec
            have hpow_lt := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
            omega
      Fp.finite (FiniteFp.mk false (e + 1) (2^(FloatFormat.prec - 1).toNat) vf)
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
      · -- Goal: 2^(prec-1).toNat ≤ ⌈m_scaled⌉ as ℤ
        -- We use Int.le_ceil_iff: z ≤ ⌈a⌉ ↔ (z : R) - 1 < a
        apply Int.le_ceil_iff.mpr
        -- Goal involves double cast ℕ → ℤ → R
        have j : (2 : R)^(FloatFormat.prec - 1) ≤ x / 2^e * 2^(FloatFormat.prec - 1) := by
          unfold e
          conv_lhs => rw [← one_mul ((2 : R)^(FloatFormat.prec - 1))]
          rw [mul_le_mul_iff_of_pos_right]
          linarith
          linearize
        have hprec_pos := FloatFormat.prec_sub_one_pos
        have hpow_ge_one : (1 : R) ≤ (2 : R)^(FloatFormat.prec - 1) :=
          one_le_zpow₀ (by norm_num : (1 : R) ≤ 2) (by omega)
        -- Use push_cast to simplify the double cast and power
        push_cast
        -- The goal is now (2 : R)^n - 1 < m_scaled where n = (prec-1).toNat
        have hpow_nat_eq : (2 : R)^(FloatFormat.prec - 1).toNat = (2 : R)^(FloatFormat.prec - 1) := by
          rw [← zpow_natCast]
          congr 1
          exact FloatFormat.prec_sub_one_toNat_eq
        calc (2 : R)^(FloatFormat.prec - 1).toNat - 1
            = (2 : R)^(FloatFormat.prec - 1) - 1 := by rw [hpow_nat_eq]
          _ < (2 : R)^(FloatFormat.prec - 1) := by linarith
          _ ≤ x / 2 ^ e * 2 ^ (FloatFormat.prec - 1) := j
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

  by_cases hm : (2 : ℤ)^FloatFormat.prec.toNat ≤ m
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
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Int.cast_ofNat, ge_iff_le,
                 Nat.cast_pow, Nat.cast_ofNat]
      -- Goal: x ≤ (2 : R)^(prec-1).toNat * (2 : R)^(e + 1 - prec + 1)
      -- Convert the Nat pow to zpow first
      rw [FloatFormat.pow_prec_sub_one_nat_int]
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
        rw [← zpow_sub₀ (by norm_num)]
        ring_nf

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
