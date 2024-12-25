import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LiftLets
import Mathlib.Tactic.Rify
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Flean.Basic
import Flean.BitVecUtil
import Flean.RelativeError

namespace Fp

-- We need LinearOrderedField instead of LinearOrderedSemifield because we need to take absolute values.
-- (I mean, technically, if your R was purely positive then you don't need neg! So this limits the expressivity for our definition of ulp. But that's fine for now.)
variable {R : Type*} [LinearOrderedField R] [FloorSemiring R]

/-- The gap between the two floating-point numbers nearest to a given number, including the number itself.
**Harrison's ulp**: The distance between the closest fp-numbers `x`,`y` (`x ≤ f ≤ y` with `x ≠ y`), assuming that the exponent range is not upper bounded.
Harrison's ulp is equivalent to the quantum of `f`, except when `x` is of the form `β^e` (`e ≥ 0`). -/
def ulp_har [FloatFormat] (f : FiniteFp) : ℚ := sorry

-- theorem ulp_har_def [FloatFormat] (f : FiniteFp) : sorry := sorry

def ulp [FloatFormat] (v : R) : R :=
  -- Get the e for the power of two interval containing v |v| ∈ [2^e, 2^(e+1))
  let e : ℤ := Int.log 2 (|v|)
  let e := max e FloatFormat.min_exp
  2 ^ (e - FloatFormat.prec + 1)

theorem ulp_ne_zero [FloatFormat] (v : R)  : ulp v ≠ 0 := by
  apply zpow_ne_zero
  norm_num

theorem ulp_pos [FloatFormat] (v : R) : ulp v > 0 := by
  apply zpow_pos
  norm_num

/-- Distance between 1 and its floating-point successor. Sometimes called the 'machine epsilon'. This is the value of MATLAB's `eps`. -/
theorem ulp_one [FloatFormat] : ulp (1 : R) = 2^(1 - (FloatFormat.prec : ℤ)) := by
  delta ulp
  norm_num
  ring

def machineEpsilon [FloatFormat] : R := ulp (1 : R)

theorem ulp_zero [FloatFormat] : ulp (0 : R) = 2 ^ (-(FloatFormat.prec : ℤ) + 1) := by simp [ulp]

/-- Symmetric about 0. Which makes sense because floating point formats are symmetric about 0. -/
theorem ulp_eq_neg [FloatFormat] (v : R) : ulp (-v) = ulp v := by simp [ulp]

theorem ulp_ge [FloatFormat] : ∀ (v : R), 2^(FloatFormat.min_exp - FloatFormat.prec + 1) ≤ ulp v := by
  intro v
  delta ulp
  norm_num

/-- Being in the same power of two interval means the ULP is the same. -/
theorem ulp_step_log [FloatFormat] (v x : R) : Int.log 2 (|v|) = Int.log 2 (|x|) → ulp v = ulp x := by
  delta ulp
  intro h
  rw [h]

-- TODO: Can we clean this up, making it more clear about which parts are disjoint?
theorem ulp_step_log' [FloatFormat] (v x : R) : ulp v = ulp x →
  Int.log 2 (|v|) = Int.log 2 (|x|) ∨
  Int.log 2 (|v|) = FloatFormat.min_exp ∨
  Int.log 2 (|x|) = FloatFormat.min_exp ∨
  (Int.log 2 (|v|) < FloatFormat.min_exp ∧ Int.log 2 (|x|) < FloatFormat.min_exp) := by

  delta ulp
  norm_num
  intro hv
  cases' max_cases (Int.log 2 (|v|)) FloatFormat.min_exp with h h
  <;> cases' max_cases (Int.log 2 (|x|)) FloatFormat.min_exp with h' h'
  <;> rw [h.left, h'.left] at hv
  <;> rw [hv]
  <;> simp [hv, h, h']


-- theorem ulp_pow_mul [FloatFormat] (v : ℝ) (k : ℤ) : ulp (2^k * v) = 2^k * ulp v := by
--   delta ulp
--   norm_num
--   cases' abs_cases (2 ^ k * v) with h1 h2
--   · rw [h1.left]
--     have vnonneg : 0 ≤ v := by
--       have : 0 < (2 : ℝ) ^ k := by
--         apply zpow_pos_of_pos
--         norm_num
--       exact (mul_nonneg_iff_of_pos_left this).mp h1.right
--     rw [abs_of_nonneg vnonneg]
--     rw [← @Real.floor_logb_natCast 2 (2 ^ k * v), ← @Real.floor_logb_natCast 2 v]
--     norm_num
--     rw [Real.logb_mul]
--     cases' max_cases ⌊Real.logb 2 (2 ^ k) + Real.logb 2 v⌋ FloatFormat.min_exp with h3 h4
--     · rw [h3.left]
--       cases' max_cases ⌊Real.logb 2 v⌋ FloatFormat.min_exp with h5 h6
--       · rw [h5.left]



-- TODO: There's multiple definitions of ULP, prove equivalence conditions if they're useful.

-- theorem diff_lt_half_ulp_imp_rn [FloatFormat] (f : FiniteFp) (x : ℝ) : |f.toRat - x| < 1/2 * ulp x → Fp.finite f = round_nearest x := by
--   sorry

-- theorem Nat.pow_le_of_le_log_abs {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ Nat.log b y) : b ^ x ≤ |y| := by
--   refine (le_or_lt b 1).elim (fun hb => ?_) fun hb => (Nat.pow_le_iff_le_log hb hy).2 h
--   rw [Nat.log_of_left_le_one hb, Nat.le_zero] at h
--   rwa [h, Nat.pow_zero, one_le_iff_ne_zero]

-- theorem Nat.pow_log_le_self_abs (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ Nat.log b x ≤ |x| :=
--   Nat.pow_le_of_le_log_abs hx le_rfl

-- TODO: should this be in mathlib?
theorem Int.zpow_log_le_abs_self {b : ℕ} {r : R} (hb : 1 < b) (rnz : r ≠ 0) (hra : |r| ≥ 1): (b : R) ^ Int.log b r ≤ |r| := by
  rcases le_total 1 r with hr1 | hr1
  · rw [Int.log_of_one_le_right _ hr1]
    rw [zpow_natCast, ← Nat.cast_pow, ← Nat.le_floor_iff (abs_nonneg _)]
    have h : b ^ Nat.log b ⌊r⌋₊ ≤ ⌊r⌋₊ := Nat.pow_log_le_self b (Nat.floor_pos.mpr hr1).ne'
    -- have h' : ⌊|r|⌋₊ ≤ |r| := Nat.floor_le (abs_nonneg r)
    have h'' : ⌊r⌋₊ ≤ ⌊|r|⌋₊ := by
      cases' abs_cases r with h1 h1
      · rw [h1.left]
      · linarith
    apply le_trans h h''
  · rw [Int.log_of_right_le_one _ hr1, zpow_neg, zpow_natCast, ← Nat.cast_pow]
    -- original version was for without abs
    -- exact inv_le_of_inv_le₀ (abs_pos.mpr rnz) (Nat.ceil_le.1 <| Nat.le_pow_clog hb _)
    apply inv_le_of_inv_le₀ (abs_pos.mpr rnz)
    have h : ⌈|r|⁻¹⌉₊ ≤ b ^ Nat.clog b ⌈|r|⁻¹⌉₊ := by
      apply Nat.le_pow_clog hb
    simp_all only [ne_eq, Nat.ceil_le, Nat.cast_pow, ge_iff_le]
    cases' abs_cases r with h1 h1
    · rw [h1.left] at h ⊢
      exact h
    · rw [h1.left] at h ⊢
      rw [(@Nat.ceil_eq_zero _ _ _ r⁻¹).mpr, Nat.clog_zero_right, pow_zero]
      rw [h1.left] at hra
      rw [show (1 : R) = (1 : R)⁻¹ by ring]
      apply (inv_le_inv₀ _ _).mpr hra
      linarith
      norm_num
      simp_all only [abs_eq_neg_self, inv_nonpos]

theorem relativeError_ulp_eq [FloatFormat] (x : R) (y : FiniteFp) (α : R) (xge : 2^FloatFormat.min_exp ≤ |x|) (hdiff : |x - y.toVal| = α * ulp x) : relativeError x y ≤ α * 2^(1 - (FloatFormat.prec : ℤ)) := by
  delta relativeError
  delta ulp at hdiff
  norm_num at hdiff
  have xabspos : 0 < |x| := by
    apply lt_of_le_of_lt'
    -- apply zpow_nonneg (by norm_num : (0 : R) ≤ 2)
    exact xge
    apply zpow_pos (by norm_num : (0 : R) < 2)
  have xnz : x ≠ 0 := by simp_all only [abs_pos, ne_eq, not_false_eq_true]

  -- rw [abs_div, hdiff]

  -- if hαz : α = 0 then
  --   rw [hαz, zero_mul, zero_mul, zero_div]
  -- else
  cases' abs_cases (x - y.toVal) with h h
  · obtain ⟨h1, h2⟩ := h
    rw [h1] at hdiff
    rw [hdiff] at h2 ⊢
    -- rw [abs_div]


    have hα : 0 ≤ α := by
      apply le_of_mul_le_mul_right
      rw [zero_mul]
      exact h2
      apply zpow_pos
      norm_num
    -- rw [abs_of_nonneg]
    rw [← mul_div]
    if hαz : α = 0 then
      rw [hαz, zero_mul, zero_mul, abs_zero]
    else
      have hα : 0 < α := hα.lt_of_ne (Ne.symm hαz)
      have xge' : FloatFormat.min_exp ≤ Int.log 2 |x| := by
        apply (Int.zpow_le_iff_le_log _ _).mp
        norm_cast
        norm_num
        apply abs_pos.mpr xnz

      cases' abs_cases x with hx hx
      rw [abs_of_nonneg]
      pick_goal 3; rw [abs_of_neg]; rw [← neg_mul, neg_mul_comm]

      pick_goal 2
      · apply mul_neg_iff.mpr
        left; split_ands
        trivial
        apply div_neg_iff.mpr
        left; split_ands
        apply zpow_pos (by norm_num)
        exact hx.right
      pick_goal 3
      · apply mul_nonneg
        linarith
        apply div_nonneg
        apply zpow_nonneg (by norm_num)
        exact hx.right

      -- Now we have the two simple branches where one is positive and the other is negative.
      all_goals apply (mul_le_mul_left hα).mpr -- get rid of the α
      all_goals rw [sub_add, zpow_sub₀ (by norm_num)]

      all_goals rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, ← mul_assoc, mul_comm x⁻¹, ← div_eq_mul_inv _ x, ← inv_zpow, inv_zpow', neg_sub]
      all_goals rw [max_eq_left xge']

      all_goals rw [← one_mul ((2 : R) ^ (1 - (FloatFormat.prec : ℤ)))]

      rw [← neg_mul]

      all_goals apply mul_le_mul

      pick_goal 2; rw [one_mul]
      pick_goal 2; rw [one_mul]; apply zpow_nonneg; norm_num
      pick_goal 2; norm_num

      pick_goal 3; rw [one_mul];
      pick_goal 3; rw [one_mul]; apply zpow_nonneg; norm_num
      pick_goal 3; norm_num

      rw [neg_div']

      rw [show -2 ^ Int.log 2 |x| / x = 2 ^ Int.log 2 |x| / -x by ring]

      all_goals rw [hx.left]
      all_goals apply (div_le_one (by linarith)).mpr
      all_goals apply Int.zpow_log_le_self (by norm_num) (by linarith)
  · sorry

      -- apply (Int.zpow_le_iff_le_log _ _).mp




      -- apply (mul_le_mul_left hα).mpr
      -- rw [sub_add, zpow_sub₀]

      -- rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, ← mul_assoc, mul_comm x⁻¹, ← div_eq_mul_inv _ x, ← inv_zpow, inv_zpow', neg_sub]
      -- rw [max_eq_left]

      -- rw [← one_mul ((2 : R) ^ (1 - (FloatFormat.prec : ℤ)))]
      -- apply mul_le_mul
      -- · cases' abs_cases x with hx hx
      --   · rw [hx.left]
      --     apply (div_le_one _).mpr
      --     apply Int.zpow_log_le_self (by norm_num) (by linarith)
      --     linarith
      --   · apply @le_trans _ _ _ 0
      --     apply div_nonpos_iff.mpr
      --     left; split_ands
      --     · apply zpow_nonneg (by norm_num)
      --     · linarith
      --     norm_num
      -- · rw [one_mul]
      -- · rw [one_mul]; apply zpow_nonneg; norm_num
      -- · norm_num
      -- · apply (Int.zpow_le_iff_le_log _ _).mp
      --   simp_all only [abs_pos, ne_eq, not_false_eq_true, abs_eq_self, mul_nonneg_iff_of_pos_left, Nat.cast_ofNat]
      --   norm_num
      --   linarith
      -- · norm_num




      -- cases' abs_cases x with hx hx
      -- · rw [hx.left]
      --   apply mul_le_mul
      --   · apply (div_le_one _).mpr
      --     apply Int.zpow_log_le_self (by norm_num) (by linarith)
      --     linarith
      --   · rw [one_mul]
      -- · rw [Int.log_of_right_le_zero, zpow_zero]



      -- have hn : (2 : R) ^ (Int.log 2 x ⊔ FloatFormat.min_exp) / (2 : R) ^ ((FloatFormat.prec : ℤ) - 1) / x = ((2 : R) ^ Int.log 2 x / x) * (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) := by
      --   rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, ← mul_assoc, mul_comm x⁻¹, ← div_eq_mul_inv _ x, ← inv_zpow, inv_zpow', neg_sub]
      --   rw [max_eq_left]
      --   have := FloatFormat.min_exp_nonpos


      -- rw [← one_mul ((2 : R) ^ (1 - (FloatFormat.prec : ℤ)))]
      -- rw [hn]
      -- -- have ha : 2 ^ (Int.log 2 |x|) ≤ |x| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr xnz)

      -- cases' abs_cases x with hx hx
      -- · apply mul_le_mul
      --   · rw [hx.left]
      --     apply (div_le_one _).mpr
      --     apply Int.zpow_log_le_self (by norm_num) (by linarith)
      --     linarith
      --   · rfl
      -- · rw [Int.log_of_right_le_zero, zpow_zero, one_mul]


      -- apply mul_le_mul
      -- · cases' abs_cases x with hx hx
      --   · rw [hx.left]
      --     apply (div_le_one _).mpr
      --     exact Int.zpow_log_le_self (by norm_num) (by linarith)
      --     linarith
      --   · rw [Int.log_of_right_le_zero, zpow_zero]
      --     apply (div_le_one _).mpr

      --     sorry
      --     all_goals linarith
      -- · rfl

    --   apply zpow_nonneg (by norm_num)
    --   norm_num
    --   norm_num
    -- simp_all only [abs_pos, ne_eq, not_false_eq_true, abs_eq_self]


      -- have hn' : (2 : R) ^ (Int.log 2 |x| ⊔ FloatFormat.min_exp) / x ≤ 1 := by
      --   sorry

      -- have hn' : (2 : R) ^ (Int.log 2 x) / |x| ≤ 1 := by
      --   apply (div_le_one _).mpr

        -- apply Int.zpow_log_le_abs_self
        -- norm_num
        -- trivial



      -- apply mul_le_mul





    -- cases' abs_cases x with hx hx
    -- · obtain ⟨hx1, hx2⟩ := hx
    --   rw [hx1] at xge ⊢
    --   rw [abs_of_nonneg]
    --   rw [← mul_div]
    --   have hpos : 0 < x := by simp_all only [ne_eq, abs_eq_self]

    --   have hα : 0 ≤ α := by
    --     apply le_of_mul_le_mul_right
    --     rw [zero_mul]
    --     exact h2
    --     apply zpow_pos
    --     norm_num
    --   if hαz : α = 0 then
    --     rw [hαz, zero_mul, zero_mul]
    --   else
    --     have hα : 0 < α := hα.lt_of_ne (Ne.symm hαz)
    --     apply (mul_le_mul_left hα).mpr
    --     cases' max_cases (Int.log 2 x) FloatFormat.min_exp with hr hr
    --     · rw [hr.left]
    --       rw [sub_add, zpow_sub₀]
    --       have hn : (2 : R) ^ Int.log 2 x / (2 : R) ^ ((FloatFormat.prec : ℤ) - 1) / x = ((2 : R) ^ Int.log 2 x / x) * (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) := by
    --         rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, ← mul_assoc, mul_comm x⁻¹, ← div_eq_mul_inv _ x, ← inv_zpow, inv_zpow', neg_sub]
    --       rw [hn]
    --       have hn' : (2 : R) ^ (Int.log 2 x) / x ≤ 1 := by
    --         apply (div_le_one _).mpr
    --         apply Int.zpow_log_le_self
    --         all_goals trivial
    --       rw [← one_mul ((2 : R) ^ (1 - (FloatFormat.prec : ℤ)))]
    --       apply mul_le_mul hn' (by norm_num)
    --       norm_num
    --       apply zpow_nonneg (by norm_num)
    --       norm_num
    --       norm_num
    --     · rw [hr.left]
    --       have hn : x⁻¹ ≤ (2 : R) ^ (-FloatFormat.min_exp) := by
    --         rw [← inv_zpow', inv_zpow]
    --         apply le_inv_of_le_inv₀
    --         apply zpow_pos (by norm_num)
    --         rw [inv_inv]
    --         trivial
    --       have hn' : (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) = (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) * (2 : R) ^ (-FloatFormat.min_exp) := by
    --         rw [← zpow_add']
    --         norm_num
    --         ring
    --         norm_num
    --       rw [hn']
    --       rw [div_eq_inv_mul, mul_comm x⁻¹]
    --       apply mul_le_mul
    --       · rfl
    --       · trivial
    --       · simp_all only [ne_eq, abs_eq_self, mul_nonneg_iff_of_pos_left, sup_eq_right, zpow_neg, inv_nonneg]
    --       · apply zpow_nonneg (by norm_num)
    --   rw [hx1] at h2
    --   exact h2
    -- -- neg case
    -- · sorry

end Fp

-- #eval @Fp.ulp ℚ _ _ FloatFormat.Binary32.toFloatFormat 0
