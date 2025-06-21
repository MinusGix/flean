import Flean.Linearize.Linearize
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Mathlib.Tactic.Linearize

-- Test with complete proof including side conditions
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^100) : a < (2 : ℝ)^200 := by
  linearize h
  · -- Main goal: a < 2^200 given Int.log 2 a < 100
    linarith
  · -- Side condition: 1 < 2
    norm_num
  · -- Side condition: 0 < a
    exact ha

-- Test with multiple hypotheses
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) 
        (h1 : a < (2 : ℝ)^50) (h2 : b ≤ (3 : ℝ)^30) : 
        a + b < (2 : ℝ)^100 + (3 : ℝ)^50 := by
  linearize h1 h2
  · -- Main goal with linearized hypotheses
    sorry -- Would need more complex arithmetic
  · -- 1 < 2
    norm_num
  · -- 0 < a
    exact ha
  · -- 1 < 3  
    norm_num
  · -- 0 < b
    exact hb