import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

import Mathlib.Tactic.Qify

-- From more recent mathlib
-- lemma Nat.log2_eq_log_two {n : ℕ} : Nat.log2 n = Nat.log 2 n := by
--   rcases eq_or_ne n 0 with rfl | hn
--   · rw [log2_zero, log_zero_right]
--   apply eq_of_forall_le_iff
--   intro m
--   rw [Nat.le_log2 hn, ← Nat.pow_le_iff_le_log Nat.one_lt_two hn]

theorem two_pow_pred_lt_two_pow_sub_one {n : ℕ} (hn : n ≥ 2) : (2 : ℚ) ^ (n - 1) < (2 : ℚ) ^ n - 1 := by
  have : (2 : ℚ) ^ n / 2 ≤ (2 : ℚ) ^ n := half_le_self (by simp_all only [Nat.ofNat_nonneg, pow_nonneg])
  have a1 : (2 : ℚ)^n - 1 = (2 : ℚ)^(n - 1) * 2 - 1 := by
    have a0 : (2 : ℚ) ^ (n - 1) * 2 = 2 ^ (n - 1) * 2^1 := by rw [pow_one]
    rw [a0, ← pow_add]
    norm_num
    omega
  rw [a1, mul_two]
  rw [add_sub_assoc]
  apply (lt_add_iff_pos_right _).mpr
  simp only [sub_pos]
  apply (one_lt_pow_iff_of_nonneg _ _).mpr
  norm_num
  norm_num
  omega

theorem lt_add_neg_toNat_lt (a b : ℤ) (c : ℕ) (a_pos : a > 0) : a < c → b ≤ 0 → ↑(a + b).toNat < c := by
  intro ha hb
  zify at hb ⊢
  rw [show (↑c : ℤ) = ↑(↑c : ℤ).toNat by norm_cast]
  apply Nat.cast_lt.mpr
  apply (Int.toNat_lt_toNat _).mpr
  rw [show a +b = b + a by ring]
  apply add_lt_of_nonpos_of_lt
  exact hb
  exact ha
  omega

theorem Nat.clog_eq_zero_iff {b x : ℕ} (hb : 1 < b) : Nat.clog b x = 0 ↔ x ≤ 1 := by
  constructor
  · intro h
    by_contra hx
    push_neg at hx
    have := Nat.clog_pos hb hx
    omega
  · intro h
    interval_cases x <;> simp [Nat.clog_zero_right, Nat.clog_one_right]

theorem Nat.clog_ne_zero_iff {b x : ℕ} (hb : 1 < b) : Nat.clog b x ≠ 0 ↔ 2 ≤ x := by
  rw [ne_eq, Nat.clog_eq_zero_iff hb]
  omega

-- Obviously we can't have the backwards direction in general. Nat.clog 2 3 = Nat.clog 2 4 = 2, but 3 ≠ 4.
-- we could with some powers stuff if that would be useful
theorem Nat.clog_ne {b x y : ℕ} : Nat.clog b x ≠ Nat.clog b y → x ≠ y := by
  intro h
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [not_true_eq_false]

-- theorem Int.log_nonneg {R : Type*} [LinearOrderedField R] [FloorSemiring R] (x : R) (hx : 1 ≤ (|x|)) : 0 ≤ Int.log 2 x := by
--   unfold Int.log
--   split_ifs with h1
--   <;> norm_cast
--   · omega
--   · norm_num at h1
--     cases' abs_cases x with ha ha
--     · rw [ha.left] at hx
--       linarith
--     · rw [ha.left] at hx
--       have : x ≤ -1 := by linarith
--       have : x < 1 := by linarith
--       have : x⁻¹ ≤ -1 := by
--         -- apply inv_le_of_inv_le
--         apply (inv_le_of_neg _ _).mp
--         rw [inv_neg, inv_one]


-- theorem Nat.clog_ne_iff {b x y : ℕ} (hb : 1 < b) (hy : 1 < y) : Nat.clog b x ≠ Nat.clog b y ↔ x ≠ y := by
--   simp_all only [ne_eq]
--   apply Iff.intro
--   · intro a
--     apply Aesop.BuiltinRules.not_intro
--     intro a_1
--     subst a_1
--     simp_all only [not_true_eq_false]
--   · intro a
--     apply Aesop.BuiltinRules.not_intro
--     intro a_1
--     induction x with
--     | zero =>
--       induction y with
--       | zero => contradiction
--       | succ y ay =>
--         rw [Nat.clog_zero_right] at a_1
--         symm at a_1
--         have j := (Nat.clog_eq_zero_iff hb).mp a_1
--         apply ay
--         · simp_all only [clog_zero_right, imp_false, lt_add_iff_pos_left, self_eq_add_left,
--           AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, add_le_iff_nonpos_left,
--           nonpos_iff_eq_zero, not_lt_zero', not_true_eq_false, imp_self, false_implies, lt_self_iff_false]
--         · simp_all only [imp_false, lt_add_iff_pos_left, self_eq_add_left, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
--           and_false, not_false_eq_true, clog_zero_right, implies_true]
--           apply Aesop.BuiltinRules.not_intro
--           intro a
--           simp_all only [lt_self_iff_false]
--         · simp_all only [clog_zero_right, imp_false, lt_add_iff_pos_left, self_eq_add_left,
--           AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, add_le_iff_nonpos_left,
--           nonpos_iff_eq_zero]
--     | succ x ax =>
--       induction y with
--       | zero =>
--         rw [Nat.clog_zero_right] at a_1
--         have j := (Nat.clog_eq_zero_iff hb).mp a_1
--         simp_all only [not_lt_zero']
--       | succ y ay =>
--         have h1 : x ≠ y := by omega
--         if h2 : x ≤ y then
--           have a1 := Nat.clog_mono_right b h2
--           have h2 : x < y := by omega
--           have hy : 0 < y := by omega
--           if h3 : x = 0 then
--             rw [h3, zero_add, Nat.clog_one_right] at a_1
--             have j := (Nat.clog_eq_zero_iff hb).mp a_1.symm
--             have a2 : y ≤ 0 := by omega
--             omega
--           else if h3 : x = 1 then
--             rw [h3, one_add_one_eq_two] at a_1
--             rw [h3] at ax
--             simp only [self_eq_add_left, clog_one_right, imp_false] at ax
--             specialize ax (by omega)
--             rw [← ne_eq] at ax
--             have k := (Nat.clog_ne_zero_iff hb).mp ax.symm
--             specialize ay (by omega)


--             sorry
--           else
--             sorry
--         else
--           sorry
--         -- if h2 : 1 < y then
--         --   specialize ay h2
--         --   sorry
--         -- else
--         --   simp_arith at h2
--         --   have hy' : y = 1 := by omega
--         --   rw [hy'] at a ax a_1 h1
--         --   rw [one_add_one_eq_two] at a_1 ax
--         --   unfold Nat.clog at a_1
--         --   lift_lets at a_1
--         --   extract_lets n at a_1
--         --   split_ifs at a_1 with h3
--         --   simp_all only [lt_self_iff_false, not_true_eq_false, clog_one_right, implies_true,
--         --     imp_self, add_left_eq_self, false_implies, lt_add_iff_pos_right, zero_lt_one, imp_false,
--         --     add_left_inj, not_false_eq_true, ne_eq, one_lt_ofNat, succ_add_sub_one, and_self,
--         --     dite_eq_ite, ite_true]

--         -- if h2 : x ≠ y + 1 then
--         --   specialize ax h2

--         -- else
--         --   sorry
