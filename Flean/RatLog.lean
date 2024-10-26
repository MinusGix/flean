import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Bound

import Flean.Encoding.Util

-- TODO: We don't actually need `Rat.flog`. We can just use `Int.log` because that takes an arbitrary ~field, which includes the rationals.
-- Ugh, all that work and time for nothing.
-- Still, there's probably a few lemmas here that should be in mathlib.

-- TODO: should we have a Rat.log version that returns a way to compute more and more accurate results?
-- or it takes a precision parameter that just multiplies the result by b^precision?

/-- ⌊log 2 x⌋ for rationals. Used primarily for acquiring the proper `e` value computably, as `Real.log` is not computable. -/
def Rat.flog (b : ℕ) (x : ℚ) : ℤ :=
  if x = 0 then 0
  -- We duplicate the logic for the positive case because terminating_by is a PAIN. I don't know any way to just go
  -- "split these three branches, okay, x = 0 terminates automatically, x > 0 terminates automatically, prove x < 0 terminates"
  -- and then doing "okay unfold Rat.flog, show that it always takes the third branch which terminates. Thus it terminates."
  -- else if x < 0 then -Rat.flog b (-x)
  else if x < 0 then
    let x' := -x
    let ex := (Nat.log b x'.num.natAbs) - (Nat.log b x'.den)
    if x' >= b ^ ex then
      ex
    else
      ex - 1
  else
    let ex := (Nat.log b (x.num.natAbs) : ℤ) - (Nat.log b x.den : ℤ)
    if x >= b ^ ex then
      ex
    else
      ex - 1

theorem Nat.le_log {b n k : ℕ} (hb : b > 1) (h : n ≠ 0) : k ≤ Nat.log b n ↔ b ^ k ≤ n := by
  match k with
  | 0 => simp [show 1 ≤ n from Nat.pos_of_ne_zero h]
  | k+1 =>
    rw [Nat.log]; split
    · have n0 : 0 < n / b := (Nat.le_div_iff_mul_le ?_).2 ?_
      simp only [Nat.add_le_add_iff_right, le_log hb (Nat.ne_of_gt n0), le_div_iff_mul_le,
        Nat.pow_succ]
      refine Nat.le_div_iff_mul_le ?_
      omega
      omega
      omega
    · rename_i h1
      rw [not_and_or] at h1
      simp
      cases' h1 with h2 h2
      · norm_num at h2
        apply lt_of_lt_of_le h2
        rw [pow_add, pow_one]
        apply Nat.le_mul_of_pos_left
        apply pow_pos
        omega
      · omega

theorem Nat.log_self_le {b : ℕ} {n : ℕ} (hb : b > 1) (h : n ≠ 0) : b ^ Nat.log b n ≤ n := (le_log hb h).1 (Nat.le_refl _)

/-- `ℕ` as a `ℚ` is equivalent to `Nat.log 2` -/
theorem Rat.flog_eq_Nat_log_2 {b : ℕ} {x : ℕ} (hb : b > 1) (hx : x ≠ 0) : Rat.flog b x = Nat.log b x := by
  delta Rat.flog
  split_ifs with h h'
  · norm_cast at h ⊢
  · norm_cast at h'
  · norm_cast at h ⊢
    rw [Int.subNatNat]
    norm_num
    have := Nat.log_self_le hb h
    exact_mod_cast this

-- Was going to use this for apply_fun but it doesn't seem to support StrictMonoOn!
-- theorem Real.logb_strictMonoOn {b : ℝ} (hb : 1 < b) : StrictMonoOn (fun (x : ℝ) => Real.logb b x) (Set.Ioi 1) := by
--   intro x xmem y ymem hxy
--   beta_reduce
--   rw [Set.mem_Ioi] at xmem ymem
--   apply Real.logb_lt_logb hb (by linarith) hxy

-- Only defined for Real.log, not Real.logb in mathlib. Should we make a version that doesn't require `0 < x`?
theorem Real.logb_zpow {b x : ℝ} {y : ℤ} (hx : 0 < x) : Real.logb b (x ^ y) = y * Real.logb b x := by
  induction y
  · rw [Int.ofNat_eq_coe, zpow_natCast, logb_pow, Int.cast_natCast]
    exact hx
  rw [zpow_negSucc, logb_inv, logb_pow, Int.cast_negSucc, Nat.cast_add_one, neg_mul_eq_neg_mul]
  exact hx

theorem floor_pred_succ_cases {x : ℝ} {n : ℤ} : x < n + 1 → n - 1 ≤ x → ⌊x⌋ = n ∨ ⌊x⌋ = n - 1 := by
  intro h1 h2
  if h : n ≤ x then
    left
    apply Int.floor_eq_iff.mpr
    constructor <;> trivial
  else
    right
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast h2
    · norm_num at h
      simp_arith
      exact h

theorem floor_pred_eq {x : ℝ} {n : ℤ} : n - 1 < x → x < n → ⌊x⌋ = n - 1 := by
  intro h1 h2
  apply Int.floor_eq_iff.mpr
  constructor
  · exact_mod_cast h1.le
  · norm_num
    exact_mod_cast h2


theorem Real.rpow_logb_self_le_pos {b x : ℝ} (b_pos : 0 < b) (b_ne_one : b ≠ 1) (hx : 0 < x) : b ^ Real.logb b x ≤ x := by
  rw [Real.rpow_logb_eq_abs b_pos b_ne_one hx.ne.symm]
  apply abs_le.mpr ⟨neg_le_self hx.le, by rfl⟩


-- TODO: For negative numbers, `Real.logb` is defined as `Real.logb b |x|`.
-- There's also the [0, 1] range to consider.
theorem Rat.flog_eq_Real_floor_log2 {b : ℕ} {x : ℚ} (hb : b > 1) (hx1 : 1 < x):
  Rat.flog b x = ⌊Real.logb b (x : ℝ)⌋ := by
  delta Rat.flog
  split_ifs with h
  · linarith -- zero, contradiction but would be equivalent
  · linarith -- negative, contradiction but would be equivalent
  · have num_pos : 0 < x.num := Rat.num_pos.mpr (by linarith)
    have den_pos : 0 < x.den := Rat.den_pos _
    have lb : b^(Nat.log b x.num.natAbs) / b^(Nat.log b x.den + 1) < x := by
      conv => rhs; rw [← Rat.num_div_den x]
      apply div_lt_div'
      any_goals norm_cast
      · have := @Nat.pow_log_le_self b x.num.natAbs (by omega)
        qify at this
        rw [abs_of_pos (by simp_all only [not_le, Rat.num_pos, Int.cast_pos])] at this
        exact_mod_cast this
      · have := @Nat.lt_pow_succ_log_self b (by omega) x.den
        norm_cast
    have ub : x < b^(Nat.log b x.num.natAbs + 1) / b^(Nat.log b x.den) := by
      conv => lhs; rw [← Rat.num_div_den x]
      apply div_lt_div
      · have := @Nat.lt_pow_succ_log_self b (by omega) x.num.natAbs
        qify at this
        rw [abs_of_pos (by simp_all only [not_le, Rat.num_pos, Nat.succ_eq_add_one, Int.cast_pos])] at this
        -- apply le_of_lt
        exact_mod_cast this
      · exact_mod_cast @Nat.pow_log_le_self b x.den (by omega)
      · apply pow_nonneg
        norm_num
      · apply pow_pos
        norm_cast; omega
    have lbr : b^(⌊Real.logb b x.num⌋) / b^(⌊Real.logb b x.den⌋ + 1) < x := by
      rw [show Real.logb b x.num = Real.logb b x.num by norm_cast]
      rw [show Real.logb b x.den = Real.logb b x.den by norm_cast]
      rw [@Real.floor_logb_natCast b x.num, @Real.floor_logb_natCast b x.den]
      rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]]
      exact_mod_cast lb
      all_goals norm_cast
      linarith
      linarith
    have ubr : x < b^(⌊Real.logb b x.num⌋ + 1) / b^(⌊Real.logb b x.den⌋) := by
      rw [show Real.logb b x.num = Real.logb b x.num by norm_cast]
      rw [show Real.logb b x.den = Real.logb b x.den by norm_cast]
      rw [@Real.floor_logb_natCast b x.num, @Real.floor_logb_natCast b x.den]
      rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]]
      exact_mod_cast ub
      all_goals norm_cast
      linarith
      linarith
    have lbr : b^(⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ - 1) < x := by
      rw [sub_sub, zpow_sub₀]
      trivial
      norm_cast; omega
    have ubr : x < b^((⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋) + 1) := by
      rw [show ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ + 1 = (⌊Real.logb b x.num⌋ + 1) - ⌊Real.logb b x.den⌋ by ring]
      rw [zpow_sub₀ (by norm_cast; linarith)]
      trivial

    rify at lbr
    rify at ubr
    have lbr' : Real.logb b (b ^ (⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ - 1)) < Real.logb b x := by
      gcongr
      norm_cast
    have ubr' : Real.logb b x < Real.logb b (b ^ (⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ + 1)) := by
      gcongr
      norm_cast
    have lbr' : ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ - 1 < Real.logb b x := by
      rify at lbr'
      rw [Real.logb_zpow (by norm_cast; linarith)] at lbr'
      simp_all only [gt_iff_lt, not_le, num_pos, Int.cast_sub, Int.cast_one, Nat.one_lt_cast,
        Real.logb_self_eq_one, mul_one, cast_pos]
    have ubr' : Real.logb b x < ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ + 1 := by
      rify at ubr'
      rw [Real.logb_zpow (by norm_cast; linarith), Real.logb_self_eq_one (by norm_cast), mul_one] at ubr'
      exact_mod_cast ubr'
    have ubr_u : ⌊Real.logb b x⌋ < ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ + 1 := by
      apply Int.floor_lt.mpr
      simp_all only [not_le, Rat.num_pos, Nat.one_lt_ofNat, Set.mem_Ioi, gt_iff_lt, cast_ofNat, Set.mem_Iio,
        Nat.ofNat_pos, cast_pos, Int.cast_add, Int.cast_sub, Int.cast_one]
    have ubr_ur : Real.logb b x < ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ + 1 := by
      simp_all only [not_le, Rat.num_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, cast_pos]
    have lbr_u : ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ - 1 ≤ ⌊Real.logb b x⌋ := by
      have := Int.lt_floor_add_one (Real.logb b x)
      apply Int.le_floor.mpr
      exact_mod_cast lbr'.le
    have lbr_ur : ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ - 1 ≤ Real.logb b x := by
      have := Int.le_floor.mp lbr_u
      exact_mod_cast this
    have not_min : (⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ - 1 : ℝ) ≠ Real.logb b x := by
      intro h
      rw [h] at lbr'
      have := lbr'.ne
      contradiction
    have lbr_ur := lt_of_le_of_ne lbr_ur not_min
    rw [← Int.cast_sub] at ubr_ur
    rw [← Int.cast_sub] at lbr_ur
    norm_num
    split_ifs with hz
    · norm_num at hz
      have real_lbr : ↑(Nat.log b x.num.natAbs) - ↑(Nat.log b x.den) ≤ Real.logb b x := by
        apply (Real.le_logb_iff_rpow_le _ _).mpr
        rify at hz
        exact_mod_cast hz
        norm_cast
        norm_cast; linarith

      -- With hz we have ⌊Real.logb 2 x⌋ = ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋
      symm
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast real_lbr
      · rw [@Real.floor_logb_natCast b x.num, @Real.floor_logb_natCast b x.den] at ubr_ur
        rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]] at ubr_ur
        rw [Int.log_natCast, Int.log_natCast] at ubr_ur
        exact_mod_cast ubr_ur
        all_goals norm_num
        all_goals linarith
    · norm_num at hz
      have real_ubr : Real.logb b x < ↑(Nat.log b x.num.natAbs) - ↑(Nat.log b x.den) := by
        apply (Real.logb_lt_iff_lt_rpow (by norm_num; linarith) (by norm_cast; linarith)).mpr
        rify at hz
        exact_mod_cast hz
      -- With hz we have ⌊Real.logb b x⌋ = ⌊Real.logb b x.num⌋ - ⌊Real.logb b x.den⌋ - 1
      have fl_pred := @floor_pred_eq (Real.logb b x) ((Nat.log b x.num.natAbs : ℤ) - (Nat.log b x.den : ℤ)) ?_ (by exact_mod_cast real_ubr)
      pick_goal 2
      · rw [@Real.floor_logb_natCast b x.num, @Real.floor_logb_natCast b x.den] at lbr_ur
        rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]] at lbr_ur
        rw [Int.log_natCast, Int.log_natCast] at lbr_ur
        exact_mod_cast lbr_ur
        all_goals norm_num
        all_goals linarith
      rw [fl_pred]

-- These should be in mathlib
@[simp] theorem Rat.natCast_den (a : Nat) : (a : Rat).den = 1 := rfl

@[simp] theorem Rat.natCast_num (a : Nat) : (a : Rat).num = a := rfl

theorem Rat.abs_num (x : ℚ) : |x|.num = |x.num| := by
  if x < 0 then
    rw [abs_of_neg (by trivial), abs_of_neg, Rat.neg_num]
    apply Rat.num_neg.mpr (by trivial)
  else
    rw [abs_of_nonneg (by linarith), abs_of_nonneg]
    apply Rat.num_nonneg.mpr
    linarith

theorem Rat.abs_den (x : ℚ) : |x|.den = x.den := by
  if x < 0 then
    rw [abs_of_neg, Rat.neg_den]
    trivial
  else
    rw [abs_of_nonneg]
    linarith

-- TODO(minor): I believe this can be an iff
theorem Rat.ge_one_num_le_denom {x : ℚ} : 1 ≤ x → x.den ≤ x.num := by
  contrapose
  norm_num
  exact Rat.lt_one_iff_num_lt_denom.mpr

theorem Rat.ge_one_num_le_denom_iff {x : ℚ} : 1 ≤ x ↔ x.den ≤ x.num := by simp [Rat.le_def]

theorem Rat.le_one_iff_num_le_denom {x : ℚ} : x ≤ 1 ↔ x.num ≤ x.den := by simp [Rat.le_def]

theorem Rat.gt_one_num_lt_denom_iff {x : ℚ} : 1 < x ↔ x.den < x.num := by simp [Rat.lt_def]

theorem Rat.abs_lt_one_iff_num_lt_denom {x : ℚ} : |x| < 1 ↔ x.num.natAbs < x.den := by
  cases' abs_cases x with h h
  <;> rw [h.left]
  <;> zify
  · rw [abs_of_nonneg]
    apply Rat.lt_one_iff_num_lt_denom
    apply Rat.num_nonneg.mpr (by linarith)
  · rw [abs_of_neg]
    conv => rhs; rhs; rw [show x.den = (-x).den by simp_all only [abs_eq_neg_self, neg_den]]
    apply Rat.lt_one_iff_num_lt_denom
    apply Rat.num_neg.mpr (by linarith)

theorem Rat.abs_ge_one_iff_num_le_denom {x : ℚ} : 1 ≤ |x| ↔ x.den ≤ x.num.natAbs := by
  cases' abs_cases x with h h
  <;> rw [h.left]
  <;> zify
  · rw [abs_of_nonneg]
    apply Rat.ge_one_num_le_denom_iff
    apply Rat.num_nonneg.mpr (by linarith)
  · rw [abs_of_neg]
    conv => rhs; lhs; rw [show x.den = (-x).den by simp_all only [abs_eq_neg_self, neg_den]]
    apply Rat.ge_one_num_le_denom_iff
    apply Rat.num_neg.mpr (by linarith)

@[simp]
theorem Rat.neg_one_den : (-1 : ℚ).den = 1 := rfl

@[simp]
theorem Rat.neg_one_num : (-1 : ℚ).num = -1 := rfl

-- #eval Rat.flog 2 1
-- #eval Rat.flog 2 0
-- #eval Rat.flog 2 (1/3)
-- #eval Rat.flog 2 (1/10)
-- #eval Nat.log 2 1
-- #eval Nat.log 2 10
-- #eval Int.log (R := ℚ) 2 (1/10)

-- #eval (Nat.log 2 1 : ℤ) - (Nat.log 2 10 : ℤ)
-- #eval ((2 : ℕ) : ℚ)^((Nat.log 2 1 : ℤ) - (Nat.log 2 10 : ℤ))
-- #eval 1/10 > ((2 : ℕ) : ℚ)^((Nat.log 2 1 : ℤ) - (Nat.log 2 10 : ℤ))

@[simp]
theorem Nat.log_self_eq_one (hb : 1 < b) : Nat.log b b = 1 := by
  rw [Nat.log_eq_one_iff]
  split_ands
  · apply lt_mul_self
    omega
  · omega
  · rfl

namespace Rat

variable {b : ℕ}

@[simp]
theorem flog_zero : flog b 0 = 0 := by rfl

@[simp]
theorem flog_one : flog b 1 = 0 := by simp [flog]

@[simp]
theorem logb_self_eq_one (hb : 1 < b) : flog b b = 1 := by
  delta flog
  norm_cast
  split_ifs with h h'
  · omega
  · omega
  · lift_lets; norm_num
    split_ifs with h1
    · unfold Int.subNatNat
      norm_num
      apply Nat.log_self_eq_one (by omega)
    · unfold Int.subNatNat at h1
      norm_num at h1
      rw [Nat.log_self_eq_one (by omega)] at h1
      linarith

@[simp]
theorem logb_self_eq_one_iff : flog b b = 1 ↔ b > 1 := by
  constructor
  · intro h
    unfold flog at h
    split_ifs at h with h1 h2
    · contradiction
    · norm_cast at h2
    · norm_cast at h2
      lift_lets at h
      extract_lets ex at h
      split_ifs at h with h3
      · unfold_let ex at h
        rw [Rat.natCast_den, Rat.natCast_num, Nat.log_one_right, Int.natAbs_cast, Nat.cast_zero, sub_zero] at h
        norm_cast at h
        have := Nat.log_eq_one_iff.mp h
        omega
      · have h' : ex = 2 := by linarith
        rw [h'] at h3
        simp at h3
        if hb : b = 1 then
          rw [hb, Nat.cast_one, one_zpow] at h3
          linarith
        else
          rw [Nat.cast_eq_zero] at h1
          omega
  · exact logb_self_eq_one

-- @[simp]
-- theorem logb_abs (x : ℚ) : flog b |x| = flog b x := by
--   delta flog
--   cases' abs_cases x with h h'
--   · rw [h.left]
--   · rw [h'.left]
--     split_ifs
--     · rfl
--     · simp_all only [abs_eq_zero, and_true]
--     · simp_all only [abs_eq_zero, and_self]
--     · rename_i h_2
--       subst h_2
--       simp_all only [abs_zero, neg_zero, lt_self_iff_false, and_false]
--     · linarith
--     · linarith
--     · rename_i h_2
--       subst h_2
--       simp_all only [abs_zero, neg_zero, lt_self_iff_false, and_false]
--     · norm_num
--       -- annoying to prove
--       sorry
--     · simp_all only [abs_eq_neg_self, and_false]

    -- split_ifs
    -- · rfl
    -- · simp_all only [abs_eq_self, le_refl, not_true_eq_false]
    -- · simp_all only [abs_eq_self, le_refl, not_true_eq_false]
    -- · rename_i h_3
    --   subst h_3
    --   simp_all only [abs_zero, le_refl, and_self, not_true_eq_false]
    -- · have := abs_nonneg x
    --   linarith
    -- · have := abs_nonneg x
    --   linarith
    -- · rename_i h_3
    --   subst h_3
    --   simp_all only [abs_zero, le_refl, and_self, not_true_eq_false]
    -- · linarith
    -- · norm_num
    --   split_ifs
    --   · rw [h.left]

  -- split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  -- · rfl
  -- · simp_all only [abs_eq_zero]
  -- · simp_all only [abs_eq_zero]
  -- · subst h5
  --   simp_all only [abs_zero, not_true_eq_false]
  -- · have := abs_nonneg x
  --   linarith
  -- · have := abs_nonneg x
  --   linarith
  -- · subst h7
  --   simp_all only [abs_zero, not_true_eq_false]
  -- · lift_lets
  --   norm_num
  --   split_ifs with hz1 hz2
  --   · rw [Rat.abs_num, Rat.abs_den]
  --     rw [Int.abs_eq_natAbs, Int.natAbs_cast]
  --     rw [Nat.cast_sub]
  --     apply Nat.log_mono_right
  --     if ha : |x| = 1 then
  --       rw [abs_of_neg] at ha
  --       have ha : x = -1 := by linarith
  --       rw [ha, Rat.neg_one_den, Rat.neg_one_num, Int.natAbs_neg, Int.natAbs_one]
  --       trivial
  --     else if ho : |x| > 1 then
  --       -- num > den
  --       apply Rat.abs_ge_one_num_le_denom
  --       linarith
  --     else
  --       -- between 0 and 1 so num < den
  --       have a := (@Nat.sub_eq_zero_iff_le (Nat.log b x.num.natAbs) (Nat.log b x.den)).mpr
  --       rw [a, pow_zero] at hz2
  --       -- contradiction really
  --       apply Rat.abs_ge_one_num_le_denom
  --       rw [abs_of_neg h8]
  --       trivial
  --       apply Nat.log_mono_right
  --       apply le_of_lt
  --       apply Rat.abs_lt_one_iff_num_lt_denom.mp
  --       rw [← ne_eq] at ha
  --       apply lt_of_le_of_ne
  --       linarith
  --       trivial
  --   · simp_all only [abs_eq_zero, not_false_eq_true, not_lt, abs_nonneg, not_le]
  --     rw [Rat.abs_num, Rat.abs_den]
      -- essentially requires that x.num =

-- @[simp]
-- theorem logb_neg_eq_logb (x : ℚ) : flog b (-x) = flog b x := by
--   delta flog
--   split_ifs
--   · rfl
--   · linarith
--   · norm_num
--     split_ifs
--     · symm
--       apply Int.sub_eq_zero_of_eq

      -- apply Nat.sub_eq_zero_iff_le.mpr

-- TODO: we obviously need to weaken it to an inequality
-- theorem logb_pow (x : ℚ) (k : ℕ) : flog b (x ^ k) = k * flog b x := by

-- theorem Rat.flog_eq_zero_iff (x : ℚ) : flog b x = 0 ↔ |x| ≤ 1 := by
--   constructor
--   · intro h
--     unfold flog at h
--     split_ifs at h with h1 h2
--     · simp [h1]
--     · norm_num at h
--       rw [abs_of_neg (by trivial)]
--       split_ifs at h with h3
--       · have := floor_pred_eq
--         sorry
--       · sorry


--   cases' abs_cases x with h h'
--   · rw [h.left]
--     constructor
--     · intro h
--       unfold flog at h
--       split_ifs at h with h1 h2
--       · rw [h1]
--         trivial
--       · linarith
--       · norm_num at h
--         split_ifs at h with h3
--         · have he := Int.sub_eq_zero.mp h
--           rw [h, zpow_zero] at h3
--           if h4 : x = 1 then
--             rw [h4]
--           else
--             -- Why in the world can't linarith figure out the symm?
--             have : 1 < x := by apply lt_of_le_of_ne; linarith; symm; trivial
--             have := Rat.gt_one_num_lt_denom_iff.mp this
--             apply Rat.le_one_iff_num_le_denom.mpr
--             sorry
--         · norm_num at h3
--           have h : ↑(Nat.log b x.num.natAbs) - ↑(Nat.log b x.den) = (1 : ℤ) := by omega
--           rw [h, zpow_one] at h3
--           if hb : b = 0 then
--             rw [hb, Nat.cast_zero] at h3
--             contradiction
--           else
--             apply le_of_lt
--             sorry
--     · intro hl
--       unfold flog
--       lift_lets
--       norm_num
--       intro hn
--       split_ifs
--       · linarith
--       · linarith
--       · sorry
--       · sorry




-- TODO: lemmas for rewriting it into Real.logb, and Nat.log for naturals

end Rat
