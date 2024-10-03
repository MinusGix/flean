import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

import Mathlib.Tactic.Qify

-- From more recent mathlib
lemma Nat.log2_eq_log_two {n : ℕ} : Nat.log2 n = Nat.log 2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [log2_zero, log_zero_right]
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn, ← Nat.pow_le_iff_le_log Nat.one_lt_two hn]

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
  simp_arith
  apply (one_lt_pow_iff_of_nonneg _ _).mpr
  norm_num
  norm_num
  omega
