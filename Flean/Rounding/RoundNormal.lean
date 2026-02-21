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

omit [LinearOrder R] [IsStrictOrderedRing R] [FloatFormat] in
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

omit [FloorRing R] in
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

omit [FloatFormat] in
/-- Convert a lower bound from ℤ power to ℕ for omega -/
theorem int_pow_le_natAbs_of_nonneg {m : ℤ} (hm_pos : 0 < m) (n : ℕ)
    (h : (2 : ℤ)^n ≤ m) : 2^n ≤ m.natAbs := by
  have hnatAbs_eq : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt hm_pos)
  have h1 : (2 : ℤ)^n ≤ m.natAbs := by rw [hnatAbs_eq]; exact h
  simp only [Int.two_pow_eq_nat_cast] at h1
  omega

omit [FloatFormat] in
/-- Convert an upper bound from ℤ power to ℕ for omega -/
theorem natAbs_lt_int_pow_of_nonneg {m : ℤ} (hm_pos : 0 < m) (n : ℕ)
    (h : m < (2 : ℤ)^n) : m.natAbs < 2^n := by
  have hnatAbs_eq : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt hm_pos)
  have h1 : (m.natAbs : ℤ) < (2 : ℤ)^n := by rw [hnatAbs_eq]; exact h
  simp only [Int.two_pow_eq_nat_cast] at h1
  omega

/-- Floor of the normal-range scaled significand expression used by normal rounding. -/
abbrev floorScaledNormal (x : R) : ℤ :=
  ⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋

/-- A positive integer floor is normal if it satisfies the scaled bounds -/
theorem floor_isNormal_of_bounds (x : R) (hx : isNormalRange x) :
    isNormal (floorScaledNormal (R := R) x).natAbs := by
  let e : ℤ := findExponentDown x
  let m : ℤ := floorScaledNormal (R := R) x
  have hb : (1 : R) ≤ x / 2 ^ e ∧ x / 2 ^ e < 2 := by
    simpa [e] using (findExponentDown_div_binade_normal hx)
  change isNormal m.natAbs
  have mpos : 0 < m := by
    simpa [m, floorScaledNormal] using (floor_scaled_normal_pos x hx)
  -- Lower bound
  have hm_lb_R : (2 : R)^(FloatFormat.prec - 1) ≤ x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) := by
    calc (2 : R)^(FloatFormat.prec - 1)
        = 1 * (2 : R)^(FloatFormat.prec - 1) := by rw [one_mul]
      _ ≤ (x / 2 ^ e) * (2 : R)^(FloatFormat.prec - 1) := by
          apply mul_le_mul_of_nonneg_right hb.left
          exact zpow_nonneg (by norm_num) _
  have hm_lb_int : (2 : ℤ)^(FloatFormat.prec - 1).toNat ≤ m := by
    have hm_lb_int' : (2 : ℤ)^(FloatFormat.prec - 1).toNat ≤ ⌊x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1)⌋ := by
      apply Int.le_floor.mpr
      simp only [Int.cast_pow, Int.cast_ofNat]
      calc (2 : R)^(FloatFormat.prec - 1).toNat
          = (2 : R)^(FloatFormat.prec - 1) := FloatFormat.natCast_pow_prec_pred
        _ ≤ x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) := hm_lb_R
    simpa [m, floorScaledNormal, e] using hm_lb_int'
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
    have hm_ub_int' : ⌊x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1)⌋ < (2 : ℤ)^FloatFormat.prec.toNat := by
      apply Int.floor_lt.mpr
      simp only [Int.cast_pow, Int.cast_ofNat]
      have hp := FloatFormat.prec_pos
      calc (x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1) : R) < (2 : R)^FloatFormat.prec := hm_ub_R
        _ = (2 : R)^FloatFormat.prec.toNat := by
            rw [← zpow_natCast]; congr 1
            exact (Int.toNat_of_nonneg (by omega)).symm
    simpa [m, floorScaledNormal, e] using hm_ub_int'
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
  have _mpos : m > 0 := floor_scaled_normal_pos x h
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
  rw [Nat.cast_natAbs]
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
    rw [two_zpow_mul]; congr 1; ring
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
  convert hmain using 2; norm_cast

/-- roundNormalDown y has toVal ≥ 2^min_exp (the smallest normal value) -/
theorem roundNormalDown_ge_zpow_min_exp (y : R) (h : isNormalRange y) :
    (2 : R) ^ FloatFormat.min_exp ≤ (roundNormalDown y h).toVal := by
  -- Use transitivity: 2^min_exp ≤ 2^(findExponentDown y) ≤ toVal
  have hexp_ge := findExponentDown_min y
  calc (2 : R) ^ FloatFormat.min_exp
      ≤ (2 : R) ^ findExponentDown y := by
          apply two_zpow_mono
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
               abs_of_nonneg (le_of_lt hfloor_y_pos)]
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
          apply two_zpow_mono
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
      simp only [hm, he, ↓reduceDIte] at h
      -- This returns Fp.infinite false, but h says result is Fp.finite f
      exfalso
      cases h
    · -- Move to next exponent case
      unfold e at he
      simp only [hm, he, ↓reduceDIte, Fp.finite.injEq] at h
      rw [← h]
      unfold FiniteFp.toVal FiniteFp.sign'
      rw [FloatFormat.radix_val_eq_two]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Int.cast_ofNat, ge_iff_le,
                 Nat.cast_pow, Nat.cast_ofNat]
      -- Goal: x ≤ (2 : R)^(prec-1).toNat * (2 : R)^(e + 1 - prec + 1)
      -- Convert the Nat pow to zpow first
      rw [FloatFormat.pow_prec_sub_one_nat_int]
      rw [two_zpow_mul]
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
    simp only [hm, ↓reduceDIte, Fp.finite.injEq] at h
    rw [← h]
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul,
      Int.cast_ofNat, ge_iff_le]
    -- Goal: x ≤ m.natAbs * 2^(e - prec + 1)
    -- First we need to show m > 0 and m.natAbs = m
    have h_natAbs := Int.cast_natAbs_pos (R := R) m_pos
    unfold m m_scaled scaled binade_base e at h_natAbs m_pos
    have m_pos' : 0 < x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1) := by
      apply Int.ceil_pos.mp
      trivial
    simp_all only [Int.ceil_pos, ge_iff_le]

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
        rw [div_two_zpow_mul_two_zpow]
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

/-- roundNormalUp finite result toVal ≤ 2^(e+1) where e = findExponentDown x -/
theorem roundNormalUp_toVal_le_zpow_succ {x : R} (hx : isNormalRange x) {f : FiniteFp}
    (hf : roundNormalUp x hx = Fp.finite f) :
    f.toVal (R := R) ≤ (2 : R) ^ (findExponentDown x + 1) := by
  -- roundNormalUp returns either:
  --   (a) ⟨false, e+1, 2^(prec-1), _⟩ when ceiling ≥ 2^prec (binade overflow, finite)
  --   (b) ⟨false, e, m.natAbs, _⟩ when ceiling < 2^prec
  -- In case (a): toVal = 2^(e+1). In case (b): toVal = m.natAbs * 2^(e-prec+1) ≤ 2^(e+1)
  have hpos := isNormalRange_pos x hx
  -- Upper bound: x < 2^(e+1) so ⌈x/2^e * 2^(prec-1)⌉ ≤ 2^prec (roughly)
  -- But the ceiling can be exactly 2^prec, that's the overflow case
  -- In both cases, the result toVal ≤ 2^(e+1)
  have hge := roundNormalUp_ge x hx f hf
  -- f.toVal ≥ x, and f is a float with exponent ≤ e+1
  -- Direct proof: unfold and case-split
  unfold roundNormalUp at hf
  simp only at hf
  split_ifs at hf with hm he
  · -- Carry overflow: f = ⟨false, e+1, 2^(prec-1), _⟩, toVal = 2^(e+1)
    rw [Fp.finite.injEq] at hf; rw [← hf]
    simp only [FiniteFp.toVal, FiniteFp.sign', Bool.false_eq_true, ↓reduceIte, one_mul,
               FloatFormat.radix_val_eq_two]
    push_cast
    rw [← zpow_natCast (2 : R), FloatFormat.prec_sub_one_toNat_eq, two_zpow_mul]
    -- Goal: 2^(prec-1 + (e+1-prec+1)) ≤ 2^(e+1). Exponents equal by ring.
    have : FloatFormat.prec - 1 + (findExponentDown x + 1 - FloatFormat.prec + 1) =
        findExponentDown x + 1 := by ring
    rw [this]
  · -- No carry: f = ⟨false, e, m.natAbs, _⟩
    rw [Fp.finite.injEq] at hf; rw [← hf]
    simp only [FiniteFp.toVal, FiniteFp.sign', Bool.false_eq_true, ↓reduceIte, one_mul,
               FloatFormat.radix_val_eq_two]
    push_neg at hm
    have hm_pos : 0 < ⌈x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌉ := by
      apply Int.ceil_pos.mpr
      apply mul_pos (div_pos hpos (by linearize)) (by linearize)
    -- Normalize the goal with push_cast
    push_cast
    -- natAbs bound: natAbs ≤ 2^prec (since ceil < 2^prec and ceil > 0)
    have hnatabs_le : (⌈x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌉.natAbs : R) ≤
        (2 : R) ^ FloatFormat.prec := by
      rw [Int.cast_natAbs_pos hm_pos]
      have hle : ⌈x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌉ ≤
          (2 : ℤ) ^ FloatFormat.prec.toNat := le_of_lt hm
      calc (⌈x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌉ : R)
          ≤ ((2 : ℤ) ^ FloatFormat.prec.toNat : R) := by exact_mod_cast hle
        _ = (2 : R) ^ FloatFormat.prec := by
            push_cast; rw [← zpow_natCast]; exact congrArg _ FloatFormat.prec_toNat_eq
    calc (⌈x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌉.natAbs : R) *
            (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1)
        ≤ (2 : R) ^ FloatFormat.prec * (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by
          apply mul_le_mul_of_nonneg_right hnatabs_le (by linearize)
      _ = (2 : R) ^ (findExponentDown x + 1) := by
          rw [two_zpow_mul]; congr 1; ring

/-- roundNormalUp is monotone on toVal for finite results -/
theorem roundNormalUp_toVal_mono {x y : R} (hx : isNormalRange x) (hy : isNormalRange y)
    {gx gy : FiniteFp} (hgx : roundNormalUp x hx = Fp.finite gx)
    (hgy : roundNormalUp y hy = Fp.finite gy) (h : x ≤ y) :
    gx.toVal (R := R) ≤ gy.toVal (R := R) := by
  have hex := findExponentDown_normal x hx
  have hey := findExponentDown_normal y hy
  by_cases hexp : findExponentDown x = findExponentDown y
  · -- Same binade: ceiling monotonicity
    -- Save original hypotheses before unfolding
    have hgx_orig := hgx
    have hgy_orig := hgy
    unfold roundNormalUp at hgx hgy
    simp only at hgx hgy
    split_ifs at hgx with hmx hex'
    · -- x carries
      split_ifs at hgy with hmy hey'
      · -- Both carry: both return ⟨false, e+1, 2^(prec-1), _⟩ so same toVal (same binade)
        rw [Fp.finite.injEq] at hgx hgy; rw [← hgx, ← hgy]
        have : findExponentDown x = findExponentDown y := hexp
        simp [this]
      · -- x carries, y doesn't: since ⌈x_scaled⌉ ≤ ⌈y_scaled⌉ and mx ≥ 2^prec, contradiction
        exfalso; push_neg at hmy
        rw [hexp] at hmx
        have hceil_mono : ⌈x / (2 : R) ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌉ ≤
               ⌈y / (2 : R) ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌉ := by
          apply Int.ceil_le_ceil; rw [← hexp]; exact scaled_le_of_le _ h
        linarith
    · -- x doesn't carry
      split_ifs at hgy with hmy hey'
      · -- x doesn't carry, y carries: gx.toVal ≤ 2^(e+1) = gy.toVal
        have hgx_le := roundNormalUp_toVal_le_zpow_succ hx hgx_orig
        -- gy is the carry result with toVal = 2^(ey+1)
        rw [Fp.finite.injEq] at hgy
        have hgy_toVal : gy.toVal (R := R) = (2 : R) ^ (findExponentDown y + 1) := by
          rw [← hgy]; simp only [FiniteFp.toVal, FiniteFp.sign', Bool.false_eq_true, ↓reduceIte,
                                  one_mul, FloatFormat.radix_val_eq_two]
          push_cast
          rw [← zpow_natCast (2 : R), FloatFormat.prec_sub_one_toNat_eq, two_zpow_mul]
          congr 1; ring
        rw [hgy_toVal]
        calc gx.toVal (R := R) ≤ (2 : R) ^ (findExponentDown x + 1) := hgx_le
          _ = (2 : R) ^ (findExponentDown y + 1) := by rw [hexp]
      · -- Neither carries: both have same exponent, just compare natAbs
        rw [Fp.finite.injEq] at hgx hgy; rw [← hgx, ← hgy]
        simp only [FiniteFp.toVal, FiniteFp.sign', Bool.false_eq_true, ↓reduceIte, one_mul,
                   FloatFormat.radix_val_eq_two]
        push_cast
        rw [show findExponentDown x = findExponentDown y from hexp]
        apply mul_le_mul_of_nonneg_right _ (by linearize)
        -- mx.natAbs ≤ my.natAbs since mx, my > 0 and mx ≤ my (ceiling monotonicity)
        have hceil_mono : ⌈x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌉ ≤
            ⌈y / (2 : R) ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌉ := by
          rw [← hexp]; apply Int.ceil_le_ceil; exact scaled_le_of_le _ h
        rw [hexp] at hceil_mono
        have hmx_pos : 0 < ⌈x / (2 : R) ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌉ := by
          rw [← hexp]; apply Int.ceil_pos.mpr
          apply mul_pos (div_pos (isNormalRange_pos x hx) (by linearize)) (by linearize)
        have hmy_pos : 0 < ⌈y / (2 : R) ^ findExponentDown y * (2 : R) ^ (FloatFormat.prec - 1)⌉ := by
          apply Int.ceil_pos.mpr
          apply mul_pos (div_pos (isNormalRange_pos y hy) (by linearize)) (by linearize)
        simp only [Nat.cast_natAbs, abs_of_nonneg (le_of_lt hmx_pos),
                   abs_of_nonneg (le_of_lt hmy_pos)]
        exact_mod_cast hceil_mono
  · -- Different binades: gx.toVal ≤ 2^(e_x+1) ≤ 2^e_y ≤ y ≤ gy.toVal
    have hxpos := isNormalRange_pos x hx
    have hypos := isNormalRange_pos y hy
    have hmono : findExponentDown x ≤ findExponentDown y := by
      rw [hex, hey]; exact Int.log_mono_right hxpos h
    have hexp_lt : findExponentDown x < findExponentDown y := lt_of_le_of_ne hmono hexp
    have hexp_bound : findExponentDown x + 1 ≤ findExponentDown y := by linarith
    calc gx.toVal (R := R)
        ≤ (2 : R) ^ (findExponentDown x + 1) := roundNormalUp_toVal_le_zpow_succ hx hgx
      _ ≤ (2 : R) ^ findExponentDown y := by
          apply two_zpow_mono hexp_bound
      _ ≤ y := by rw [hey]; exact Int.zpow_log_le_self (by norm_num) hypos
      _ ≤ gy.toVal := roundNormalUp_ge y hy gy hgy

/-- The key scaling identity: ⌊x / 2^e * 2^(prec-1)⌋ = ⌊x / 2^(e - prec + 1)⌋.
This connects the way roundNormalDown computes the significand with the ULP grid. -/
theorem floor_scaled_eq_floor_div_ulp_step (x : R) (e : ℤ) :
    ⌊x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1)⌋ = ⌊x / (2 : R) ^ (e - FloatFormat.prec + 1)⌋ := by
  congr 1
  have : (2 : R) ^ e = (2 : R) ^ (e - FloatFormat.prec + 1) * (2 : R) ^ (FloatFormat.prec - 1) := by
    rw [two_zpow_mul]; congr 1; ring
  rw [this, div_mul_eq_div_div, div_mul_cancel₀ _ (two_zpow_ne_zero _)]

/-- The absolute error of rounding a normal value down is strictly less than ulp(x).
This is the fundamental property: x - roundNormalDown(x).toVal < ulp(x). -/
theorem roundNormalDown_error_lt_ulp (x : R) (h : isNormalRange x) :
    x - (roundNormalDown x h).toVal < Fp.ulp x := by
  -- Step 1: Unfold roundNormalDown to expose the floor
  unfold roundNormalDown
  simp only
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  -- Step 2: Simplify natAbs since the floor is positive
  have hfloor_pos := floor_scaled_normal_pos x h
  rw [Int.cast_natAbs_of_pos hfloor_pos]
  -- Step 3: In normal range, findExponentDown x = Int.log 2 x, so ulp simplifies
  have hxpos := isNormalRange_pos x h
  have he := findExponentDown_normal x h
  -- Step 4: Show ulp x = 2^(e - prec + 1) where e = findExponentDown x
  have hulp : Fp.ulp x = (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
    unfold Fp.ulp
    rw [abs_of_pos hxpos, he]
    have hge : FloatFormat.min_exp ≤ Int.log 2 x := by
      rw [← he]; exact findExponentDown_min x
    simp [max_eq_left hge]
  rw [hulp]
  -- Step 5: Rewrite the floor using the scaling identity
  rw [floor_scaled_eq_floor_div_ulp_step]
  -- Step 6: The radix cast ↑2 needs to match (2 : R)
  -- The goal has ↑⌊x / 2^(...)⌋ * ↑2^(...) but we need ↑⌊x / 2^(...)⌋ * 2^(...)
  -- After the rewrite, sub_floor_div_mul_lt gives us what we need
  have h_step := Int.sub_floor_div_mul_lt x (two_zpow_pos' (findExponentDown x - FloatFormat.prec + 1))
  -- h_step : x - ↑⌊x / 2^(e-p+1)⌋ * 2^(e-p+1) < 2^(e-p+1)
  -- The FloatFormat.radix is 2, so ↑2 = (2 : R) which should unify
  push_cast at h_step ⊢
  linarith

/-- The absolute error of rounding a normal value down is nonneg: 0 ≤ x - roundNormalDown(x).toVal -/
theorem roundNormalDown_error_nonneg (x : R) (h : isNormalRange x) :
    0 ≤ x - (roundNormalDown x h).toVal := by
  linarith [roundNormalDown_le x h]

/-- Ceiling scaling identity: ⌈x / 2^e * 2^(prec-1)⌉ = ⌈x / 2^(e - prec + 1)⌉.
Ceiling analog of `floor_scaled_eq_floor_div_ulp_step`. -/
theorem ceil_scaled_eq_ceil_div_ulp_step (x : R) (e : ℤ) :
    ⌈x / 2 ^ e * (2 : R) ^ (FloatFormat.prec - 1)⌉ = ⌈x / (2 : R) ^ (e - FloatFormat.prec + 1)⌉ := by
  congr 1
  have : (2 : R) ^ e = (2 : R) ^ (e - FloatFormat.prec + 1) * (2 : R) ^ (FloatFormat.prec - 1) := by
    rw [two_zpow_mul]; congr 1; ring
  rw [this, div_mul_eq_div_div, div_mul_cancel₀ _ (two_zpow_ne_zero _)]

omit [FloatFormat] in
/-- For b > 0, ⌈a/b⌉ * b - a < b. Ceiling analog of `Int.sub_floor_div_mul_lt`. -/
private theorem ceil_div_mul_sub_lt (a : R) {b : R} (hb : 0 < b) :
    (↑⌈a / b⌉ : R) * b - a < b := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have h := Int.ceil_lt_add_one (a / b)
  have : (↑⌈a / b⌉ : R) * b < (a / b + 1) * b :=
    mul_lt_mul_of_pos_right h hb
  rw [add_mul, div_mul_cancel₀ _ hb_ne, one_mul] at this
  linarith

/-- The absolute error of rounding a normal value up is nonneg: 0 ≤ f.toVal - x -/
theorem roundNormalUp_error_nonneg (x : R) (h : isNormalRange x) (f : FiniteFp)
    (hf : roundNormalUp x h = Fp.finite f) :
    0 ≤ (f.toVal : R) - x := by
  linarith [roundNormalUp_ge x h f hf]

/-- The absolute error of rounding a normal value up is strictly less than ulp(x).
This is the fundamental property: f.toVal - x < ulp(x) for roundNormalUp. -/
theorem roundNormalUp_error_lt_ulp (x : R) (h : isNormalRange x) (f : FiniteFp)
    (hf : roundNormalUp x h = Fp.finite f) :
    (f.toVal : R) - x < Fp.ulp x := by
  have hxpos := isNormalRange_pos x h
  have he := findExponentDown_normal x h
  -- ulp(x) = 2^(e - prec + 1) in normal range
  have hulp : Fp.ulp x = (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
    unfold Fp.ulp
    rw [abs_of_pos hxpos, he]
    have hge : FloatFormat.min_exp ≤ Int.log 2 x := by
      rw [← he]; exact findExponentDown_min x
    simp [max_eq_left hge]
  rw [hulp]
  -- Unfold roundNormalUp and split on cases (overflow case auto-closed by norm_num)
  unfold roundNormalUp at hf
  extract_lets e binade_base scaled m_scaled m mpos at hf
  norm_num at hf
  split_ifs at hf with hm heover
  · -- Binade overflow case
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    push_cast
    -- Goal: (2:R)^(prec.toNat-1) * (2:R)^(e+1-prec+1) - x < (2:R)^(findExponentDown x - prec+1)
    -- Convert npow (2:R)^(prec.toNat-1) to zpow
    have hprec_nat : (FloatFormat.prec.toNat - 1 : ℕ) = (FloatFormat.prec - 1).toNat := by
      have := FloatFormat.valid_prec; omega
    rw [← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
        show ((FloatFormat.prec.toNat - 1 : ℕ) : ℤ) = FloatFormat.prec - 1
          from by rw [hprec_nat]; exact FloatFormat.prec_sub_one_toNat_eq,
        two_zpow_mul,
        show (FloatFormat.prec : ℤ) - 1 + (e + 1 - FloatFormat.prec + 1) = e + 1 from by ring]
    -- Goal: (2:R)^(e+1) - x < (2:R)^(e - prec + 1)
    -- From ceiling condition: m_scaled > 2^prec - 1
    have hceil := Int.le_ceil_iff.mp hm
    push_cast at hceil
    rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq] at hceil
    -- hceil: (2:R)^prec - 1 < m_scaled
    -- Factor m_scaled = x / 2^(e-prec+1)
    have hfactor : m_scaled = x / (2 : R) ^ (e - FloatFormat.prec + 1) := by
      show x / (2 : R) ^ e * (2 : R) ^ (FloatFormat.prec - 1) =
          x / (2 : R) ^ (e - FloatFormat.prec + 1)
      have : (2 : R) ^ e =
          (2 : R) ^ (e - FloatFormat.prec + 1) * (2 : R) ^ (FloatFormat.prec - 1) := by
        rw [two_zpow_mul]; congr 1; ring
      rw [this, div_mul_eq_div_div, div_mul_cancel₀ _ (two_zpow_ne_zero _)]
    rw [hfactor] at hceil
    -- Multiply: x > (2^prec - 1) * 2^(e-prec+1) = 2^(e+1) - 2^(e-prec+1)
    have hstep_pos : (0 : R) < (2 : R) ^ (e - FloatFormat.prec + 1) := two_zpow_pos' _
    have hx_lb : ((2 : R) ^ (FloatFormat.prec : ℤ) - 1) *
        (2 : R) ^ (e - FloatFormat.prec + 1) < x := by
      rwa [lt_div_iff₀ hstep_pos] at hceil
    have hpow_prod : (2 : R) ^ (FloatFormat.prec : ℤ) *
        (2 : R) ^ (e - FloatFormat.prec + 1) = (2 : R) ^ (e + 1) := by
      rw [two_zpow_mul]; congr 1; ring
    linarith
  · -- Normal case: f = ⟨false, e, m.natAbs, vf⟩
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [Int.cast_natAbs_of_pos mpos]
    push_cast
    -- Goal: (↑m : R) * (2:R)^(e-prec+1) - x < (2:R)^(findExponentDown x - prec+1)
    -- Unfold m to ⌈m_scaled⌉ = ⌈x / 2^e * 2^(prec-1)⌉ and use scaling identity
    change (↑⌈m_scaled⌉ : R) * (2 : R) ^ (e - FloatFormat.prec + 1) - x <
        (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)
    -- m_scaled = x / 2^e * 2^(prec-1) by definition
    -- Use ceiling scaling identity: ⌈x / 2^e * 2^(prec-1)⌉ = ⌈x / 2^(e-prec+1)⌉
    show (↑⌈x / (2 : R) ^ e * (2 : R) ^ (FloatFormat.prec - 1)⌉ : R) *
        (2 : R) ^ (e - FloatFormat.prec + 1) - x <
        (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)
    rw [ceil_scaled_eq_ceil_div_ulp_step]
    exact ceil_div_mul_sub_lt x (two_zpow_pos' _)

/-- The gap between roundNormalUp and roundNormalDown is at most ulp(x).
This is the key lemma for half-machine-epsilon bounds on roundNearest. -/
theorem roundNormalUp_sub_roundNormalDown_le_ulp (x : R) (h : isNormalRange x) (f : FiniteFp)
    (hf : roundNormalUp x h = Fp.finite f) :
    (f.toVal : R) - (roundNormalDown x h).toVal ≤ Fp.ulp x := by
  have hxpos := isNormalRange_pos x h
  have he := findExponentDown_normal x h
  -- ulp(x) = 2^(e - prec + 1) in normal range
  have hulp : Fp.ulp x = (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
    unfold Fp.ulp
    rw [abs_of_pos hxpos, he]
    have hge : FloatFormat.min_exp ≤ Int.log 2 x := by
      rw [← he]; exact findExponentDown_min x
    simp [max_eq_left hge]
  rw [hulp]
  -- Unfold roundNormalDown to expose the floor
  unfold roundNormalDown FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  have hfloor_pos := floor_scaled_normal_pos x h
  rw [Int.cast_natAbs_of_pos hfloor_pos]
  -- Unfold roundNormalUp and split on cases
  unfold roundNormalUp at hf
  extract_lets e binade_base scaled m_scaled m mpos at hf
  norm_num at hf
  split_ifs at hf with hm heover
  · -- Binade overflow case: f.toVal = 2^(prec-1) * 2^(e+1-prec+1) = 2^(e+1)
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    push_cast
    rw [← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
        show ((FloatFormat.prec.toNat - 1 : ℕ) : ℤ) = FloatFormat.prec - 1
          from by rw [show (FloatFormat.prec.toNat - 1 : ℕ) = (FloatFormat.prec - 1).toNat
            from by have := FloatFormat.valid_prec; omega]; exact FloatFormat.prec_sub_one_toNat_eq,
        two_zpow_mul,
        show (FloatFormat.prec : ℤ) - 1 + (e + 1 - FloatFormat.prec + 1) = e + 1 from by ring]
    -- Goal: 2^(e+1) - ⌊x / 2^e * 2^(prec-1)⌋ * 2^(e - prec + 1) ≤ 2^(e - prec + 1)
    -- The floor ≥ 2^(prec-1), so floor * step ≥ 2^(prec-1) * 2^(e-prec+1) = 2^e
    -- Also floor < 2^prec (from floor_isNormal_of_bounds), so floor * step < 2^(e+1)
    -- From ceiling condition: ⌈m_scaled⌉ ≥ 2^prec, and ⌊m_scaled⌋ ≥ ⌈m_scaled⌉ - 1 ≥ 2^prec - 1
    -- So floor * step ≥ (2^prec - 1) * 2^(e-prec+1) = 2^(e+1) - 2^(e-prec+1)
    have hceil_lb : (2 : ℤ) ^ FloatFormat.prec.toNat ≤ ⌈m_scaled⌉ := hm
    have hfloor_from_ceil : (2 : ℤ) ^ FloatFormat.prec.toNat - 1 ≤ ⌊m_scaled⌋ := by
      calc (2 : ℤ) ^ FloatFormat.prec.toNat - 1
          ≤ ⌈m_scaled⌉ - 1 := by linarith
        _ ≤ ⌊m_scaled⌋ := by linarith [Int.ceil_le_floor_add_one m_scaled]
    -- Cast to R
    have hfloor_lb_R : (2 : R) ^ FloatFormat.prec.toNat - 1 ≤
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) := by
      have h_cast := (@Int.cast_mono R _ _ _ _) hfloor_from_ceil
      simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one] at h_cast
      convert h_cast using 1
    -- Convert nat pow to zpow
    have hpow_nat_eq : (2 : R) ^ FloatFormat.prec.toNat = (2 : R) ^ (FloatFormat.prec : ℤ) := by
      rw [← zpow_natCast]; congr 1; exact FloatFormat.prec_toNat_eq
    rw [hpow_nat_eq] at hfloor_lb_R
    -- Now: 2^(e+1) - floor * 2^(e-prec+1) ≤ 2^(e-prec+1)
    -- iff floor * 2^(e-prec+1) ≥ 2^(e+1) - 2^(e-prec+1)
    -- iff floor ≥ 2^prec - 1 (dividing by 2^(e-prec+1))
    have hstep_pos : (0 : R) < (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := two_zpow_pos' _
    -- floor * step ≥ (2^prec - 1) * step
    have hmul_lb : ((2 : R) ^ (FloatFormat.prec : ℤ) - 1) *
        (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) ≤
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) *
        (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
      apply mul_le_mul_of_nonneg_right hfloor_lb_R (le_of_lt hstep_pos)
    -- (2^prec - 1) * step = 2^(e+1) - step
    have hprod : ((2 : R) ^ (FloatFormat.prec : ℤ) - 1) *
        (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) =
        (2 : R) ^ (findExponentDown x + 1) - (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
      rw [sub_mul, one_mul, two_zpow_mul]
      congr 1; ring
    linarith
  · -- Normal case: f = ⟨false, e, m.natAbs, vf⟩
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [Int.cast_natAbs_of_pos mpos]
    push_cast
    -- Goal: ⌈m_scaled⌉ * 2^(e-prec+1) - ⌊m_scaled⌋ * 2^(e-prec+1) ≤ 2^(e-prec+1)
    -- Suffices: ⌈m_scaled⌉ - ⌊m_scaled⌋ ≤ 1 (by Int.ceil_le_floor_add_one)
    have hgap : ⌈m_scaled⌉ - ⌊m_scaled⌋ ≤ 1 := by linarith [Int.ceil_le_floor_add_one m_scaled]
    have hstep_pos : (0 : R) < (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := two_zpow_pos' _
    have hgap_R : (↑⌈m_scaled⌉ : R) - (↑⌊m_scaled⌋ : R) ≤ 1 := by
      have := (@Int.cast_mono R _ _ _ _) hgap
      push_cast at this ⊢
      linarith
    have : (↑⌈m_scaled⌉ : R) * (2 : R) ^ (e - ↑FloatFormat.prec + 1) -
        (↑⌊m_scaled⌋ : R) * (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) =
        ((↑⌈m_scaled⌉ : R) - (↑⌊m_scaled⌋ : R)) *
        (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by ring
    linarith [mul_le_mul_of_nonneg_right hgap_R (le_of_lt hstep_pos)]

/-- Exact normal-range gap: if `x` is strictly above `roundNormalDown x`, then the
round-up / round-down gap is exactly one `ulp(x)`. -/
theorem roundNormalUp_sub_roundNormalDown_eq_ulp_of_down_lt
    (x : R) (h : isNormalRange x) (f : FiniteFp)
    (hf : roundNormalUp x h = Fp.finite f)
    (hdown_lt : (roundNormalDown x h).toVal < x) :
    (f.toVal : R) - (roundNormalDown x h).toVal = Fp.ulp x := by
  have hxpos := isNormalRange_pos x h
  have he := findExponentDown_normal x h
  have hulp : Fp.ulp x = (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
    unfold Fp.ulp
    rw [abs_of_pos hxpos, he]
    have hge : FloatFormat.min_exp ≤ Int.log 2 x := by
      rw [← he]; exact findExponentDown_min x
    simp [max_eq_left hge]
  rw [hulp]
  unfold roundNormalDown FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  have hfloor_pos := floor_scaled_normal_pos x h
  rw [Int.cast_natAbs_of_pos hfloor_pos]
  unfold roundNormalUp at hf
  extract_lets e binade_base scaled m_scaled m mpos at hf
  norm_num at hf
  split_ifs at hf with hm heover
  · -- Binade-overflow case
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    push_cast
    rw [← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
        show ((FloatFormat.prec.toNat - 1 : ℕ) : ℤ) = FloatFormat.prec - 1
          from by rw [show (FloatFormat.prec.toNat - 1 : ℕ) = (FloatFormat.prec - 1).toNat
            from by have := FloatFormat.valid_prec; omega]; exact FloatFormat.prec_sub_one_toNat_eq,
        two_zpow_mul,
        show (FloatFormat.prec : ℤ) - 1 + (e + 1 - FloatFormat.prec + 1) = e + 1 from by ring]
    have hfloor_from_ceil : (2 : ℤ) ^ FloatFormat.prec.toNat - 1 ≤ ⌊m_scaled⌋ := by
      have hceil_lb : (2 : ℤ) ^ FloatFormat.prec.toNat ≤ ⌈m_scaled⌉ := hm
      calc (2 : ℤ) ^ FloatFormat.prec.toNat - 1
          ≤ ⌈m_scaled⌉ - 1 := by linarith
        _ ≤ ⌊m_scaled⌋ := by linarith [Int.ceil_le_floor_add_one m_scaled]
    have hfloor_norm : isNormal (floorScaledNormal (R := R) x).natAbs :=
      floor_isNormal_of_bounds x h
    have hfloor_ub : ⌊m_scaled⌋ ≤ (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
      have hlt_nat : (floorScaledNormal (R := R) x).natAbs < 2 ^ FloatFormat.prec.toNat := hfloor_norm.2
      have hlt_int : ((floorScaledNormal (R := R) x).natAbs : ℤ) < (2 : ℤ) ^ FloatFormat.prec.toNat := by
        exact_mod_cast hlt_nat
      have hnatabs_eq : ((floorScaledNormal (R := R) x).natAbs : ℤ) = floorScaledNormal (R := R) x := by
        exact Int.natAbs_of_nonneg (le_of_lt hfloor_pos)
      rw [hnatabs_eq] at hlt_int
      -- `m_scaled` is the scaled expression used by `floorScaledNormal`.
      have hm_floor : ⌊m_scaled⌋ = floorScaledNormal (R := R) x := by
        simp [m_scaled, scaled, binade_base, e, floorScaledNormal]
      rw [hm_floor]
      omega
    have hfloor_eq : ⌊m_scaled⌋ = (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by omega
    have hm_floor : ⌊m_scaled⌋ = floorScaledNormal (R := R) x := by
      simp [m_scaled, scaled, binade_base, e, floorScaledNormal]
    have hfloor_cast :
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) =
        (2 : R) ^ (FloatFormat.prec : ℤ) - 1 := by
      have hfloor_eq' : floorScaledNormal (R := R) x = (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
        rw [← hm_floor, hfloor_eq]
      have hpow_nat_eq : ((2 : ℤ) ^ FloatFormat.prec.toNat : R) = (2 : R) ^ (FloatFormat.prec : ℤ) := by
        calc
          ((2 : ℤ) ^ FloatFormat.prec.toNat : R) = (2 : R) ^ FloatFormat.prec.toNat := by
            norm_num
          _ = (2 : R) ^ (FloatFormat.prec : ℤ) := by
                rw [← zpow_natCast]
                congr 1
                exact FloatFormat.prec_toNat_eq
      calc
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R)
            = (floorScaledNormal (R := R) x : R) := by simp [floorScaledNormal]
        _ = ((2 : ℤ) ^ FloatFormat.prec.toNat - 1 : ℤ) := by exact_mod_cast hfloor_eq'
        _ = ((2 : ℤ) ^ FloatFormat.prec.toNat : R) - 1 := by norm_cast
        _ = (2 : R) ^ (FloatFormat.prec : ℤ) - 1 := by rw [hpow_nat_eq]
    rw [hfloor_cast]
    have hprod : ((2 : R) ^ (FloatFormat.prec : ℤ) - 1) *
        (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) =
        (2 : R) ^ (findExponentDown x + 1) - (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
      rw [sub_mul, one_mul, two_zpow_mul]
      congr 1; ring
    linarith [hprod]
  · -- No-overflow case
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [Int.cast_natAbs_of_pos mpos]
    push_cast
    have hstep_pos : (0 : R) < (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := two_zpow_pos' _
    have hdown_lt' :
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) *
            (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) < x := by
      simpa [roundNormalDown, FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
        Int.cast_natAbs_of_pos hfloor_pos] using hdown_lt
    have hx_scaled :
        (x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)) *
            (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) = x := by
      calc
        (x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)) *
            (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)
            = x / 2 ^ findExponentDown x *
              ((2 : R) ^ (FloatFormat.prec - 1) *
                (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)) := by ring
        _ = x / 2 ^ findExponentDown x * (2 : R) ^ findExponentDown x := by
              congr 1
              rw [two_zpow_mul]
              congr 1
              ring
        _ = x := by
              rw [div_mul_cancel₀ _ (two_zpow_ne_zero _)]
    have hfloor_lt_scaled :
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) <
          x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1) := by
      have hmul :
          (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) *
              (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)
            < (x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)) *
              (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
        simpa [hx_scaled] using hdown_lt'
      exact lt_of_mul_lt_mul_right hmul (le_of_lt hstep_pos)
    have hfloor_lt_ceil_R : (⌊m_scaled⌋ : R) < (⌈m_scaled⌉ : R) := by
      have h1 : (⌊m_scaled⌋ : R) < m_scaled := by simpa [m_scaled] using hfloor_lt_scaled
      exact lt_of_lt_of_le h1 (Int.le_ceil _)
    have hfloor_lt_ceil : ⌊m_scaled⌋ < ⌈m_scaled⌉ := by
      exact_mod_cast hfloor_lt_ceil_R
    have hgap_ge : 1 ≤ ⌈m_scaled⌉ - ⌊m_scaled⌋ := by omega
    have hgap_le : ⌈m_scaled⌉ - ⌊m_scaled⌋ ≤ 1 := by
      linarith [Int.ceil_le_floor_add_one m_scaled]
    have hgap_eq : ⌈m_scaled⌉ - ⌊m_scaled⌋ = 1 := by omega
    have hgap_R_eq : (↑⌈m_scaled⌉ : R) - (↑⌊m_scaled⌋ : R) = 1 := by
      exact_mod_cast hgap_eq
    calc
      (↑⌈m_scaled⌉ : R) * (2 : R) ^ (e - ↑FloatFormat.prec + 1) -
          (↑⌊m_scaled⌋ : R) * (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1)
          = ((↑⌈m_scaled⌉ : R) - (↑⌊m_scaled⌋ : R)) *
            (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by ring
      _ = (1 : R) * (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by
            rw [hgap_R_eq]
      _ = (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by ring

/-- Exact normal-range gap: if `x` is strictly below `roundNormalUp x`, then the
round-up / round-down gap is exactly one `ulp(x)`. -/
theorem roundNormalUp_sub_roundNormalDown_eq_ulp_of_lt_up
    (x : R) (h : isNormalRange x) (f : FiniteFp)
    (hf : roundNormalUp x h = Fp.finite f)
    (hup_gt : x < (f.toVal : R)) :
    (f.toVal : R) - (roundNormalDown x h).toVal = Fp.ulp x := by
  have hxpos := isNormalRange_pos x h
  have he := findExponentDown_normal x h
  have hulp : Fp.ulp x = (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
    unfold Fp.ulp
    rw [abs_of_pos hxpos, he]
    have hge : FloatFormat.min_exp ≤ Int.log 2 x := by
      rw [← he]; exact findExponentDown_min x
    simp [max_eq_left hge]
  rw [hulp]
  unfold roundNormalDown FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  have hfloor_pos := floor_scaled_normal_pos x h
  rw [Int.cast_natAbs_of_pos hfloor_pos]
  unfold roundNormalUp at hf
  extract_lets e binade_base scaled m_scaled m mpos at hf
  norm_num at hf
  split_ifs at hf with hm heover
  · -- Binade-overflow case
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    push_cast
    rw [← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
        show ((FloatFormat.prec.toNat - 1 : ℕ) : ℤ) = FloatFormat.prec - 1
          from by rw [show (FloatFormat.prec.toNat - 1 : ℕ) = (FloatFormat.prec - 1).toNat
            from by have := FloatFormat.valid_prec; omega]; exact FloatFormat.prec_sub_one_toNat_eq,
        two_zpow_mul,
        show (FloatFormat.prec : ℤ) - 1 + (e + 1 - FloatFormat.prec + 1) = e + 1 from by ring]
    have hfloor_from_ceil : (2 : ℤ) ^ FloatFormat.prec.toNat - 1 ≤ ⌊m_scaled⌋ := by
      have hceil_lb : (2 : ℤ) ^ FloatFormat.prec.toNat ≤ ⌈m_scaled⌉ := hm
      calc (2 : ℤ) ^ FloatFormat.prec.toNat - 1
          ≤ ⌈m_scaled⌉ - 1 := by linarith
        _ ≤ ⌊m_scaled⌋ := by linarith [Int.ceil_le_floor_add_one m_scaled]
    have hfloor_norm : isNormal (floorScaledNormal (R := R) x).natAbs :=
      floor_isNormal_of_bounds x h
    have hfloor_ub : ⌊m_scaled⌋ ≤ (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
      have hlt_nat : (floorScaledNormal (R := R) x).natAbs < 2 ^ FloatFormat.prec.toNat := hfloor_norm.2
      have hlt_int : ((floorScaledNormal (R := R) x).natAbs : ℤ) < (2 : ℤ) ^ FloatFormat.prec.toNat := by
        exact_mod_cast hlt_nat
      have hnatabs_eq : ((floorScaledNormal (R := R) x).natAbs : ℤ) = floorScaledNormal (R := R) x := by
        exact Int.natAbs_of_nonneg (le_of_lt hfloor_pos)
      rw [hnatabs_eq] at hlt_int
      have hm_floor : ⌊m_scaled⌋ = floorScaledNormal (R := R) x := by
        simp [m_scaled, scaled, binade_base, e, floorScaledNormal]
      rw [hm_floor]
      omega
    have hfloor_eq : ⌊m_scaled⌋ = (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by omega
    have hm_floor : ⌊m_scaled⌋ = floorScaledNormal (R := R) x := by
      simp [m_scaled, scaled, binade_base, e, floorScaledNormal]
    have hfloor_cast :
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R) =
        (2 : R) ^ (FloatFormat.prec : ℤ) - 1 := by
      have hfloor_eq' : floorScaledNormal (R := R) x = (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
        rw [← hm_floor, hfloor_eq]
      have hpow_nat_eq : ((2 : ℤ) ^ FloatFormat.prec.toNat : R) = (2 : R) ^ (FloatFormat.prec : ℤ) := by
        calc
          ((2 : ℤ) ^ FloatFormat.prec.toNat : R) = (2 : R) ^ FloatFormat.prec.toNat := by
            norm_num
          _ = (2 : R) ^ (FloatFormat.prec : ℤ) := by
                rw [← zpow_natCast]
                congr 1
                exact FloatFormat.prec_toNat_eq
      calc
        (⌊x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)⌋ : R)
            = (floorScaledNormal (R := R) x : R) := by simp [floorScaledNormal]
        _ = ((2 : ℤ) ^ FloatFormat.prec.toNat - 1 : ℤ) := by exact_mod_cast hfloor_eq'
        _ = ((2 : ℤ) ^ FloatFormat.prec.toNat : R) - 1 := by norm_cast
        _ = (2 : R) ^ (FloatFormat.prec : ℤ) - 1 := by rw [hpow_nat_eq]
    rw [hfloor_cast]
    have hprod : ((2 : R) ^ (FloatFormat.prec : ℤ) - 1) *
        (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) =
        (2 : R) ^ (findExponentDown x + 1) - (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
      rw [sub_mul, one_mul, two_zpow_mul]
      congr 1; ring
    linarith [hprod]
  · -- No-overflow case
    rw [Fp.finite.injEq] at hf
    rw [← hf]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [Int.cast_natAbs_of_pos mpos]
    push_cast
    have hstep_pos : (0 : R) < (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := two_zpow_pos' _
    have hup_gt' :
        x < (↑⌈m_scaled⌉ : R) * (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
      have hup_gt0 := hup_gt
      rw [← hf] at hup_gt0
      unfold FiniteFp.toVal FiniteFp.sign' at hup_gt0
      rw [FloatFormat.radix_val_eq_two] at hup_gt0
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hup_gt0
      rw [Int.cast_natAbs_of_pos mpos] at hup_gt0
      push_cast at hup_gt0
      simpa [e] using hup_gt0
    have hx_scaled :
        (x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)) *
            (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) = x := by
      calc
        (x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)) *
            (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)
            = x / 2 ^ findExponentDown x *
              ((2 : R) ^ (FloatFormat.prec - 1) *
                (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)) := by ring
        _ = x / 2 ^ findExponentDown x * (2 : R) ^ findExponentDown x := by
              congr 1
              rw [two_zpow_mul]
              congr 1
              ring
        _ = x := by
              rw [div_mul_cancel₀ _ (two_zpow_ne_zero _)]
    have hscaled_lt_ceil :
        m_scaled < (⌈m_scaled⌉ : R) := by
      have hmul :
          (x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1)) *
              (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1)
            < (↑⌈m_scaled⌉ : R) * (2 : R) ^ (findExponentDown x - FloatFormat.prec + 1) := by
        simpa [hx_scaled] using hup_gt'
      have hlt_scaled :
          x / 2 ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1) < (↑⌈m_scaled⌉ : R) := by
        exact lt_of_mul_lt_mul_right hmul (le_of_lt hstep_pos)
      simpa [m_scaled, scaled, binade_base, e] using hlt_scaled
    have hfloor_lt_ceil_R : (⌊m_scaled⌋ : R) < (⌈m_scaled⌉ : R) := by
      exact lt_of_le_of_lt (Int.floor_le m_scaled) hscaled_lt_ceil
    have hfloor_lt_ceil : ⌊m_scaled⌋ < ⌈m_scaled⌉ := by
      exact_mod_cast hfloor_lt_ceil_R
    have hgap_ge : 1 ≤ ⌈m_scaled⌉ - ⌊m_scaled⌋ := by omega
    have hgap_le : ⌈m_scaled⌉ - ⌊m_scaled⌋ ≤ 1 := by
      linarith [Int.ceil_le_floor_add_one m_scaled]
    have hgap_eq : ⌈m_scaled⌉ - ⌊m_scaled⌋ = 1 := by omega
    have hgap_R_eq : (↑⌈m_scaled⌉ : R) - (↑⌊m_scaled⌋ : R) = 1 := by
      exact_mod_cast hgap_eq
    calc
      (↑⌈m_scaled⌉ : R) * (2 : R) ^ (e - ↑FloatFormat.prec + 1) -
          (↑⌊m_scaled⌋ : R) * (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1)
          = ((↑⌈m_scaled⌉ : R) - (↑⌊m_scaled⌋ : R)) *
            (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by ring
      _ = (1 : R) * (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by
            rw [hgap_R_eq]
      _ = (2 : R) ^ (findExponentDown x - ↑FloatFormat.prec + 1) := by ring

end Rounding
