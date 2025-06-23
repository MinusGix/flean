import Flean.Linearize.Linearize
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Mathlib.Tactic.Linearize

section BasicTests

set_option trace.linearize true
set_option diagnostics true

-- Test 1: Basic < transformation (lhs < base^exp)
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^100) : Int.log 2 a < 100 := by
  linearize h
  · -- Goal: Int.log 2 a < 100 with h : Int.log 2 a < Int.ofNat 100
    -- Int.ofNat 100 = 100, so this follows directly
    exact h
  · norm_num  -- 1 < 2
  · exact ha  -- 0 < a

example (a : ℝ) (ha : 0 < a) : Int.log 2 ((2 : ℝ) ^ 100) ≤ Int.ofNat 100 := by
  sorry

-- Test 2: Basic ≤ transformation (lhs ≤ base^exp)
example (a : ℝ) (ha : 0 < a) (h : a ≤ (2 : ℝ)^100) : Int.log 2 a ≤ 100 := by
  linearize h
  · exact h
  · norm_num
  · trivial

-- Test 3: Reverse < transformation (base^exp < rhs)
example (a : ℝ) (ha : 0 < a) (h : (2 : ℝ)^100 < a) : 100 < Int.log 2 a + 1 := by
  linearize h
  · exact h  -- h : Int.ofNat 100 < Int.log 2 a + 1
  · norm_num  -- 1 < 2
  · exact ha  -- 0 < a

-- Test 4: Reverse ≤ transformation (base^exp ≤ rhs)
example (a : ℝ) (ha : 0 < a) (h : (2 : ℝ)^100 ≤ a) : 100 ≤ Int.log 2 a := by
  linearize h
  · exact h  -- h : Int.ofNat 100 ≤ Int.log 2 a
  · norm_num  -- 1 < 2
  · exact ha  -- 0 < a

end BasicTests

section IntegerExponentTests

-- Test 5: Integer exponent
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^(100 : ℤ)) : Int.log 2 a < 100 := by
  linearize h
  · exact h  -- h : Int.log 2 a < 100
  · norm_num  -- 1 < 2
  · exact ha  -- 0 < a

end IntegerExponentTests

section MultipleBaseTests

-- Test 6: Different bases
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^50) (h2 : b ≤ (3 : ℝ)^30) :
        Int.log 2 a < 50 ∧ Int.log 3 b ≤ 30 := by
  linearize h1
  · linearize h2
    · exact ⟨h1, h2⟩
    · norm_num  -- 1 < 3
    · exact hb  -- 0 < b
  · norm_num  -- 1 < 2
  · exact ha  -- 0 < a

end MultipleBaseTests

section AllHypothesesTest

-- Test 7: Linearize all hypotheses at once
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^100) (h2 : b ≤ (2 : ℝ)^200) :
        Int.log 2 a < 100 ∧ Int.log 2 b ≤ 200 := by
  linearize  -- No targets specified, should linearize all applicable hypotheses
  · exact ⟨h1, h2⟩
  · norm_num  -- 1 < 2 for h1
  · exact ha  -- 0 < a for h1
  · norm_num  -- 1 < 2 for h2
  · exact hb  -- 0 < b for h2

end AllHypothesesTest

section RealWorldExample

-- Test 8: More realistic example using linearize with linarith
example (x y : ℝ) (hx : 1 < x) (hy : 1 < y)
        (h1 : x < (2 : ℝ)^10) (h2 : y < (2 : ℝ)^20) :
        x * y < (2 : ℝ)^31 := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith

  -- Transform to logarithmic form
  linearize h1
  · linearize h2
    · -- Now we have:
      -- h1 : Int.log 2 x < 10
      -- h2 : Int.log 2 y < 20
      -- Goal: x * y < 2^31

      -- Would need additional lemmas about Int.log and multiplication
      -- For example: Int.log b (x * y) = Int.log b x + Int.log b y
      sorry
    · norm_num
    · exact hy_pos
  · norm_num
  · exact hx_pos

end RealWorldExample
