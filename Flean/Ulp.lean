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

namespace Fp

-- We need LinearOrderedField instead of LinearOrderedSemifield because we need to take absolute values.
-- (I mean, technically, if your R was purely positive then you don't need neg! So this limits the expressivity for our definition of ulp. But that's fine for now.)
variable {R : Type*} [LinearOrderedField R] [FloorSemiring R]

/-- The gap between the two floating-point numbers nearest to a given number, including the number itself.
**Harrison's ulp**: The distance between the closest fp-numbers `x`,`y` (`x ≤ f ≤ y` with `x ≠ y`), assuming that the exponent range is not upper bounded.
Harrison's ulp is equivalent to the quantum of `f`, except when `x` is of the form `β^e` (`e ≥ 0`). -/
def ulp_har [FloatFormat] (f : FiniteFp) : ℚ := sorry

-- theorem ulp_har_def [FloatFormat] (f : FiniteFp) : sorry := sorry

-- TODO: is there any good way to have a computable version of this using rationals? (or even a version that does it up to some finite precision)
def ulp_goldberg [FloatFormat] (v : R) : R :=
  -- Get the e for the power of two interval containing v |v| ∈ [2^e, 2^(e+1))
  let e := Int.log 2 (|v|)
  let e := max e FloatFormat.min_exp
  2 ^ (e - FloatFormat.prec + 1)

theorem ulp_goldberg_ne_zero [FloatFormat] (v : R)  : ulp_goldberg v ≠ 0 := by
  apply zpow_ne_zero
  norm_num

theorem ulp_goldberg_pos [FloatFormat] (v : R) : ulp_goldberg v > 0 := by
  apply zpow_pos_of_pos
  norm_num

/-- Symmetric about 0. Which makes sense because floating point formats are symmetric about 0. -/
theorem ulp_goldberg_eq_neg [FloatFormat] (v : R) : ulp_goldberg (-v) = ulp_goldberg v := by simp [ulp_goldberg]

theorem ulp_goldberg_ge [FloatFormat] : ∀ (v : R), 2^(FloatFormat.min_exp - FloatFormat.prec + 1) ≤ ulp_goldberg v := by
  intro v
  delta ulp_goldberg
  norm_num

/-- Being in the same power of two interval means the ULP is the same. -/
theorem ulp_goldberg_step_log [FloatFormat] (v x : R) : Int.log 2 (|v|) = Int.log 2 (|x|) → ulp_goldberg v = ulp_goldberg x := by
  delta ulp_goldberg
  intro h
  rw [h]

-- TODO: Can we clean this up, making it more clear about which parts are disjoint?
theorem ulp_goldberg_step_log' [FloatFormat] (v x : R) : ulp_goldberg v = ulp_goldberg x →
  Int.log 2 (|v|) = Int.log 2 (|x|) ∨
  Int.log 2 (|v|) = FloatFormat.min_exp ∨
  Int.log 2 (|x|) = FloatFormat.min_exp ∨
  (Int.log 2 (|v|) < FloatFormat.min_exp ∧ Int.log 2 (|x|) < FloatFormat.min_exp) := by

  delta ulp_goldberg
  norm_num
  intro hv
  cases' max_cases (Int.log 2 (|v|)) FloatFormat.min_exp with h h
  <;> cases' max_cases (Int.log 2 (|x|)) FloatFormat.min_exp with h' h'
  <;> rw [h.left, h'.left] at hv
  <;> rw [hv]
  <;> simp [hv, h, h']


-- theorem ulp_goldberg_pow_mul [FloatFormat] (v : ℝ) (k : ℤ) : ulp_goldberg (2^k * v) = 2^k * ulp_goldberg v := by
--   delta ulp_goldberg
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

-- theorem diff_lt_half_ulp_goldberg_imp_rn [FloatFormat] (f : FiniteFp) (x : ℝ) : |f.toRat - x| < 1/2 * ulp_goldberg x → Fp.finite f = round_nearest x := by
--   sorry

end Fp

-- #eval @Fp.ulp_goldberg ℚ _ _ FloatFormat.Binary32.toFloatFormat 0
