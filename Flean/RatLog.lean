import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Bound

import Flean.Encoding.Util
-- log2 a/b = log2 a - log2 b


/-- ⌊log 2 x⌋ for rationals. Used primarily for acquiring the proper `e` value computably, as `Real.log` is not computable. -/
def Rat.flog (b : ℕ) (x : ℚ) : ℤ :=
  if x ≤ 1 then 0
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
theorem Rat.flog_eq_Nat_log_2 {b : ℕ} {x : ℕ} (hb : b > 1) : Rat.flog b x = Nat.log b x := by
  delta Rat.flog
  split_ifs with h
  · norm_cast at h ⊢
    symm
    apply Nat.log_eq_zero_iff.mpr
    omega
  · simp_arith at h
    norm_cast
    rw [Int.subNatNat]
    norm_num
    have := Nat.log_self_le hb (by omega : x ≠ 0)
    exact_mod_cast this

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
theorem Rat.flog_eq_Real_floor_log2 {b : ℕ} {x : ℚ} (hb : b > 1) (hx1 : 1 < x):
  Rat.flog b x = ⌊Real.logb b (x : ℝ)⌋ := by
  delta Rat.flog
  split_ifs with h
  · linarith
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
