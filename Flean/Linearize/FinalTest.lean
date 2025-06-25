import Flean.Linearize.Linearize
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Mathlib.Tactic.Linearize

section BasicTests

-- set_option trace.linearize true
-- set_option diagnostics true

-- Test 1: Basic < transformation (lhs < base^exp)
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^100) : Int.log 2 a < 100 := by
  linearize at h
  trivial

-- Test 2: Basic ≤ transformation (lhs ≤ base^exp)
example (a : ℝ) (ha : 0 < a) (h : a ≤ (2 : ℝ)^100) : Int.log 2 a ≤ 100 := by
  linearize at h
  trivial

-- Test 3: Reverse < transformation (base^exp < rhs)
example (a : ℝ) (ha : 0 < a) (h : (2 : ℝ)^100 < a) : 100 < Int.log 2 a + 1 := by
  linearize at h
  trivial

-- Test 4: Reverse ≤ transformation (base^exp ≤ rhs)
example (a : ℝ) (ha : 0 < a) (h : (2 : ℝ)^100 ≤ a) : 100 ≤ Int.log 2 a := by
  linearize at h
  trivial

end BasicTests

section IntegerExponentTests

-- Test 5: Integer exponent
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^(100 : ℤ)) : Int.log 2 a < 100 := by
  linearize at h
  trivial

end IntegerExponentTests

section MultipleBaseTests

-- Test 6: Different bases
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^50) (h2 : b ≤ (3 : ℝ)^30) :
        Int.log 2 a < 50 ∧ Int.log 3 b ≤ 30 := by
  linearize at h1
  linearize at h2
  trivial

end MultipleBaseTests

section AllHypothesesTest

-- Test 7: Linearize all hypotheses at once
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^100) (h2 : b ≤ (2 : ℝ)^200) :
        Int.log 2 a < 100 ∧ Int.log 2 b ≤ 200 := by
  linearize
  trivial

end AllHypothesesTest

section RealWorldExample

-- Test 8: More realistic example using linearize with linarith
example (x y : ℝ) (hx : 1 < x) (hy : 1 < y)
        (h1 : x < (2 : ℝ)^10) (h2 : y < (2 : ℝ)^20) :
        x * y < (2 : ℝ)^31 := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith

  -- Transform to logarithmic form
  linearize at h1
  linearize at h2
  sorry

end RealWorldExample

section ZpowGoalTests

-- set_option trace.linearize true
-- set_option diagnostics true
-- Test 9: Goal linearization - 2^m < 2^n reduces to m < n
example (m n : ℤ) (h : m < n) : (2 : ℝ)^m < (2 : ℝ)^n := by
  linearize

-- Test 10: Goal linearization - 2^m ≤ 2^n reduces to m ≤ n
example (m n : ℤ) (h : m ≤ n) : (2 : ℝ)^m ≤ (2 : ℝ)^n := by
  linearize

-- Test 11: Goal linearization with different base
example (m n : ℤ) (h : m < n) : (3 : ℝ)^m < (3 : ℝ)^n := by
  linearize

-- Test 12: Goal linearization with more complex expressions
example (m n k : ℤ) (h : m + k < n + k) : (2 : ℝ)^(m + k) < (2 : ℝ)^(n + k) := by
  linearize

end ZpowGoalTests

section LinearizeBangTests

-- Test 13: linearize! with simple hypothesis transformation
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^5) : Int.log 2 a ≤ 4 := by
  linearize! at h

-- Test 14: linearize! with goal transformation
example (m : ℤ) (h : m ≤ 5) : (2 : ℝ)^m ≤ (2 : ℝ)^5 := by
  linearize!

-- Test 15: linearize! with wildcard (all hypotheses and goal)
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^3) : (2 : ℝ)^1 < (2 : ℝ)^3 := by
  linearize!

-- Test 16: linearize! with additional lemmas
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^5) (extra : Int.log 2 a ≥ 2) : Int.log 2 a = 4 ∨ Int.log 2 a = 3 ∨ Int.log 2 a = 2 := by
  linearize! [extra] at h

-- Test 17: linearize! with only modifier and lemmas
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^5) (extra : Int.log 2 a ≥ 2) : Int.log 2 a ≤ 4 := by
  linearize! only [h, extra] at h

end LinearizeBangTests

section ZpowTests

-- Test 18: Goal linearization using zpow_pos for 0 < a^n pattern
example : (0 : ℝ) < (2 : ℝ)^5 := by
  linearize

-- Test 19: Goal linearization using zpow_pos with integer exponent
example : (0 : ℝ) < (2 : ℝ)^(-3 : ℤ) := by
  linearize

-- Test 20: Goal linearization using zpow_pos with variable exponent
example (n : ℤ) : (0 : ℝ) < (3 : ℝ)^n := by
  linearize

-- Test 21: Goal linearization using zpow_nonneg for 0 ≤ a^n pattern
example : (0 : ℝ) ≤ (2 : ℝ)^5 := by
  linearize

-- Test 22: Goal linearization using zpow_nonneg with integer exponent
example : (0 : ℝ) ≤ (2 : ℝ)^(-3 : ℤ) := by
  linearize

-- Test 23: Goal linearization using zpow_nonneg with variable exponent
example (n : ℤ) : (0 : ℝ) ≤ (3 : ℝ)^n := by
  linearize

-- Test 24: Goal linearization using one_lt_zpow₀ for 1 < a^n pattern
example : (1 : ℝ) < (2 : ℝ)^(5 : ℤ) := by
  linearize

-- Test 25: Goal linearization using one_lt_zpow₀ with variable exponent
example (n : ℤ) (hn : 0 < n) : (1 : ℝ) < (3 : ℝ)^n := by
  linearize

-- Test 26: Goal linearization using one_lt_pow for 1 < a^n pattern with natural exponent
example : (1 : ℝ) < (2 : ℝ)^5 := by
  linearize

-- Test 27: Goal linearization using one_lt_pow with variable natural exponent
example (n : ℕ) (hn : n ≠ 0) : (1 : ℝ) < (3 : ℝ)^n := by
  linearize

-- Test 28: Goal linearization using one_le_zpow₀ for 1 ≤ a^n pattern with integer exponent
example : (1 : ℝ) ≤ (2 : ℝ)^(5 : ℤ) := by
  linearize

-- Test 29: Goal linearization using one_le_zpow₀ with variable exponent
example (n : ℤ) (hn : 0 ≤ n) : (1 : ℝ) ≤ (3 : ℝ)^n := by
  linearize

-- Test 30: Goal linearization using one_le_pow₀ for 1 ≤ a^n pattern with natural exponent
example : (1 : ℝ) ≤ (2 : ℝ)^5 := by
  linearize

-- Test 31: Goal linearization using one_le_pow₀ with variable natural exponent
example (n : ℕ) : (1 : ℝ) ≤ (3 : ℝ)^n := by
  linearize

end ZpowTests
