import Flean.Linearize.Linearize
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Mathlib.Tactic.Linearize

-- Test basic transformation
example (a : ℝ) (h : a < (2 : ℝ)^100) : True := by
  linearize h
  -- Should add: Int.log 2 a < Int.ofNat 100
  trivial

-- Test with zpow notation
example (a : ℝ) (h : a < (2 : ℝ)^(100 : ℤ)) : True := by
  linearize h
  trivial

-- Test reverse direction
example (a : ℝ) (h : (2 : ℝ)^100 < a) : True := by
  linearize h
  -- Should add: 100 < Int.log 2 a + 1
  trivial

-- Test ≤
example (a : ℝ) (h : a ≤ (2 : ℝ)^100) : True := by
  linearize h
  -- Should add: Int.log 2 a ≤ 100
  trivial

-- Test multiple hypotheses
example (a b : ℝ) (h1 : a < (2 : ℝ)^100) (h2 : b ≤ (2 : ℝ)^200) : True := by
  linearize
  trivial

-- Test without specific targets (should try all hypotheses)
example (a b : ℝ) (h1 : a < (2 : ℝ)^100) (h2 : b ≤ (2 : ℝ)^200) : True := by
  linearize
  trivial