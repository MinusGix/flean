import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Qify

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

