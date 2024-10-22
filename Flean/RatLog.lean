import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Bound

import Flean.Encoding.Util
-- log2 a/b = log2 a - log2 b


/-- ⌊log 2 x⌋ for rationals. Used primarily for acquiring the proper `e` value computably, as `Real.log` is not computable. -/
def Rat.flog2 (x : ℚ) : ℤ :=
  if x ≤ 1 then 0
  else
    -- ⌊log 2 x⌋ = ⌊log 2 num - log 2 denom⌋
    -- But we clearly can't use `Real.log` here, since that's not computable.
    -- We can, however, calculate `⌊log 2 num⌋` and `⌊log 2 denom⌋` separately, using `Nat.log2` which is computable.
    -- `⌊log 2 num⌋ = n` and `⌊log 2 denom⌋ = d`
    -- we get that `2^n ≤ num < 2^(n+1)` and `2^d ≤ denom < 2^(d+1)`
    -- have := div_le_div
    -- ⌊log 2 num⌋ = n
    -- let n := Nat.log 2 (x.num.natAbs)
    -- -- ⌊log 2 denom⌋ = d
    -- let d := Nat.log 2 x.den
    let ex := (Nat.log 2 (x.num.natAbs) : ℤ) - (Nat.log 2 x.den : ℤ)
    if x >= 2 ^ ex then
      ex
    else
      ex - 1
    -- have num_pos : 0 < x.num := by
    --   apply Rat.num_pos.mpr
    --   linarith
    -- have den_pos : 0 < x.den := Rat.den_pos _
    -- have : 2^n / 2^(d+1) < x := by
    --   rw [← Rat.num_div_den x]
    --   apply div_lt_div'
    --   · unfold_let n
    --     have := @Nat.pow_log_le_self 2 x.num.natAbs (by omega)
    --     qify at this
    --     rw [abs_of_pos (by norm_cast)] at this
    --     trivial
    --   · have j := @Nat.lt_pow_succ_log_self 2 (by norm_num) x.den
    --     norm_cast
    --   · norm_cast
    --   · norm_cast

/-- `ℕ` as a `ℚ` is equivalent to `Nat.log 2` -/
theorem Rat.flog2_eq_Nat_log_2 {x : ℕ} : Rat.flog2 x = Nat.log 2 x := by
  delta Rat.flog2
  split_ifs with h
  · norm_cast at h ⊢
    symm
    apply Nat.log_eq_zero_iff.mpr
    omega
  · simp_arith at h
    norm_cast
    rw [Int.subNatNat]
    norm_num
    have := Nat.log2_self_le (by omega : x ≠ 0)
    rw [Nat.log2_eq_log_two] at this
    qify at this
    exact this

theorem Real.logb_strictMonoOn {b : ℝ} (hb : 1 < b) : StrictMonoOn (fun (x : ℝ) => Real.logb b x) (Set.Ioi 1) := by
  intro x xmem y ymem hxy
  beta_reduce
  rw [Set.mem_Ioi] at xmem ymem
  apply Real.logb_lt_logb hb (by linarith) hxy

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


-- TODO: For negative numbers, `Real.logb` is defined as `Real.logb b |x|`. Should we mimic that for `Rat.flog2`?
-- There's also the [0, 1] range to consider.
theorem Rat.flog2_eq_Real_floor_log2 {x : ℚ} (hx1 : 1 < x):
  Rat.flog2 x = ⌊Real.logb 2 (x : ℝ)⌋ := by
  delta Rat.flog2
  split_ifs with h
  · linarith
  · --rw [show x = (x.num : ℤ) / (x.den : ℤ) by norm_cast; simp only [divInt_ofNat,
    --mkRat_num_den']]
    -- rw [Real.logb_div]
    -- conv => rhs; rw [← Rat.mkRat_num_den' x, ← Rat.divInt_ofNat]
    -- push_cast
    -- rw [Real.logb_div]
    -- rw [Real.floor_logb_natCast]

    have num_pos : 0 < x.num := Rat.num_pos.mpr (by linarith)
    have den_pos : 0 < x.den := Rat.den_pos _
    have lb : 2^(Nat.log 2 x.num.natAbs) / 2^(Nat.log 2 x.den + 1) < x := by
      conv => rhs; rw [← Rat.num_div_den x]
      apply div_lt_div'
      any_goals norm_cast
      · have := @Nat.pow_log_le_self 2 x.num.natAbs (by omega)
        qify at this
        rw [abs_of_pos (by simp_all only [not_le, Rat.num_pos, Int.cast_pos])] at this
        exact_mod_cast this
      · have := @Nat.lt_pow_succ_log_self 2 (by norm_num) x.den
        norm_cast
    have ub : x < 2^(Nat.log 2 x.num.natAbs + 1) / 2^(Nat.log 2 x.den) := by
      conv => lhs; rw [← Rat.num_div_den x]
      apply div_lt_div
      · have := @Nat.lt_pow_succ_log_self 2 (by norm_num) x.num.natAbs
        qify at this
        rw [abs_of_pos (by simp_all only [not_le, Rat.num_pos, Nat.succ_eq_add_one, Int.cast_pos])] at this
        -- apply le_of_lt
        exact_mod_cast this
      · exact_mod_cast @Nat.pow_log_le_self 2 x.den (by omega)
      · apply pow_nonneg
        norm_num
      · apply pow_pos
        norm_num
    have lbr : 2^(⌊Real.logb 2 x.num⌋) / 2^(⌊Real.logb 2 x.den⌋ + 1) < x := by
      rw [show Real.logb 2 x.num = Real.logb (2 : ℕ) x.num by norm_cast]
      rw [show Real.logb 2 x.den = Real.logb (2 : ℕ) x.den by norm_cast]
      rw [@Real.floor_logb_natCast 2 x.num, @Real.floor_logb_natCast 2 x.den]
      rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]]
      exact_mod_cast lb
      all_goals norm_num
      linarith
    have ubr : x < 2^(⌊Real.logb 2 x.num⌋ + 1) / 2^(⌊Real.logb 2 x.den⌋) := by
      rw [show Real.logb 2 x.num = Real.logb (2 : ℕ) x.num by norm_cast]
      rw [show Real.logb 2 x.den = Real.logb (2 : ℕ) x.den by norm_cast]
      rw [@Real.floor_logb_natCast 2 x.num, @Real.floor_logb_natCast 2 x.den]
      rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]]
      exact_mod_cast ub
      all_goals norm_num
      linarith
    have lbr : 2^(⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ - 1) < x := by
      rw [sub_sub, zpow_sub₀]
      trivial
      norm_num
    have ubr : x < 2^((⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋) + 1) := by
      rw [show ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ + 1 = (⌊Real.logb 2 x.num⌋ + 1) - ⌊Real.logb 2 x.den⌋ by ring]
      rw [zpow_sub₀ (by norm_num)]
      trivial

    rify at lbr
    rify at ubr
    have lbr' : Real.logb 2 (2 ^ (⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ - 1)) < Real.logb 2 x := by
      gcongr
      norm_num
    have ubr' : Real.logb 2 x < Real.logb 2 (2 ^ (⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ + 1)) := by
      gcongr
      norm_num
    have lbr' : ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ - 1 < Real.logb 2 x := by
      rify at lbr'
      rw [Real.logb_zpow (by norm_num)] at lbr'
      simp_all only [not_le, Rat.num_pos, Nat.one_lt_ofNat, Set.mem_Ioi, gt_iff_lt, cast_ofNat, Set.mem_Iio,
        Int.cast_sub, Int.cast_one, Real.logb_self_eq_one, mul_one, cast_pos, Nat.ofNat_pos]
    have ubr' : Real.logb 2 x < ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ + 1 := by
      rify at ubr'
      rw [Real.logb_zpow (by norm_num), Real.logb_self_eq_one (by norm_num), mul_one] at ubr'
      exact_mod_cast ubr'
    have ubr_u : ⌊Real.logb 2 x⌋ < ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ + 1 := by
      apply Int.floor_lt.mpr
      simp_all only [not_le, Rat.num_pos, Nat.one_lt_ofNat, Set.mem_Ioi, gt_iff_lt, cast_ofNat, Set.mem_Iio,
        Nat.ofNat_pos, cast_pos, Int.cast_add, Int.cast_sub, Int.cast_one]
    have ubr_ur : Real.logb 2 x < ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ + 1 := by
      simp_all only [not_le, Rat.num_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, cast_pos]
    have lbr_u : ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ - 1 ≤ ⌊Real.logb 2 x⌋ := by
      -- rw [show ∀ (x y z : ℤ), x - y - 1 ≤ z ↔ x - y ≤ z + 1 by omega]
      -- have := Int.sub_one_lt_floor (Real.logb 2 x)
      have := Int.lt_floor_add_one (Real.logb 2 x)
      -- rify
      -- apply lt_trans ?_ this
      -- apply Int.le_add
      -- exact_mod_cast lbr'
      apply Int.le_floor.mpr
      exact_mod_cast lbr'.le
    have lbr_ur : ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ - 1 ≤ Real.logb 2 x := by
      have := Int.le_floor.mp lbr_u
      exact_mod_cast this
    have not_min : (⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ - 1 : ℝ) ≠ Real.logb 2 x := by
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
      have real_lbr : ↑(Nat.log 2 x.num.natAbs) - ↑(Nat.log 2 x.den) ≤ Real.logb 2 x := by
        apply (Real.le_logb_iff_rpow_le _ _).mpr
        rify at hz
        exact_mod_cast hz
        norm_num
        norm_cast; linarith
      -- With hz we have ⌊Real.logb 2 x⌋ = ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋
      symm
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast real_lbr
      · conv at ubr_ur => rhs; rw [← Nat.cast_two]
        rw [@Real.floor_logb_natCast 2 x.num, @Real.floor_logb_natCast 2 x.den] at ubr_ur
        rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]] at ubr_ur
        rw [Int.log_natCast, Int.log_natCast] at ubr_ur
        exact_mod_cast ubr_ur
        all_goals norm_num
        linarith
    · norm_num at hz
      have real_ubr : Real.logb 2 x < ↑(Nat.log 2 x.num.natAbs) - ↑(Nat.log 2 x.den) := by
        apply (Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_cast; linarith)).mpr
        rify at hz
        exact_mod_cast hz
      -- With hz we have ⌊Real.logb 2 x⌋ = ⌊Real.logb 2 x.num⌋ - ⌊Real.logb 2 x.den⌋ - 1
      have fl_pred := @floor_pred_eq (Real.logb 2 x) ((Nat.log 2 x.num.natAbs : ℤ) - (Nat.log 2 x.den : ℤ)) ?_ (by exact_mod_cast real_ubr)
      pick_goal 2
      · conv at lbr_ur => lhs; rw [← Nat.cast_two]
        rw [@Real.floor_logb_natCast 2 x.num, @Real.floor_logb_natCast 2 x.den] at lbr_ur
        rw [show (x.num : ℝ) = x.num.natAbs by rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]] at lbr_ur
        rw [Int.log_natCast, Int.log_natCast] at lbr_ur
        exact_mod_cast lbr_ur
        all_goals norm_num
        linarith
      rw [fl_pred]
