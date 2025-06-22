import Flean.Linearize.Linearize
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Mathlib.Tactic.Linearize

-- Test basic transformation with side conditions proven
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^100) : a < (2 : ℝ)^200 := by
  linearize h
  · -- Main goal: a < 2^200 with linearized hypothesis
    -- We have h : Int.log 2 a < 100
    -- We need to prove a < 2^200
    sorry  -- Would need additional reasoning here
  · -- Side condition: 1 < 2
    norm_num
  · -- Side condition: 0 < a
    exact ha

-- Test ≤ case
example (a : ℝ) (ha : 0 < a) (h : a ≤ (2 : ℝ)^100) : a ≤ (2 : ℝ)^200 := by
  linearize h
  · -- Main goal with h : Int.log 2 a ≤ 100
    sorry
  · -- Side condition: 1 < 2
    norm_num
  · -- Side condition: 0 < a
    exact ha

-- Test reverse direction: (b : R)^z < rhs
example (a : ℝ) (ha : 0 < a) (h : (2 : ℝ)^100 < a) : (2 : ℝ)^50 < a := by
  linearize h
  -- Should transform to: 100 < Int.log 2 a + 1
  all_goals { sorry }  -- Check if this case is implemented

-- Test multiple hypotheses
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^50) (h2 : b ≤ (3 : ℝ)^30) :
        a * b < (2 : ℝ)^100 := by
  linearize h1
  linearize h2
  · -- Main goal with linearized hypotheses
    -- h1 : Int.log 2 a < 50
    -- h2 : Int.log 3 b ≤ 30
    sorry
  · norm_num  -- 1 < 3 for h2
  · exact hb  -- 0 < b for h2
  · norm_num  -- 1 < 2 for h1
  · exact ha  -- 0 < a for h1

-- Test without specifying targets (should linearize all)
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^100) (h2 : b ≤ (2 : ℝ)^200) :
        a + b < (2 : ℝ)^201 := by
  linearize
  · -- Main goal with all linearized hypotheses
    sorry
  · norm_num  -- 1 < 2 for h1
  · exact ha  -- 0 < a for h1
  · norm_num  -- 1 < 2 for h2
  · exact hb  -- 0 < b for h2
