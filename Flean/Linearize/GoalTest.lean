import Flean.Linearize.Linearize
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Mathlib.Tactic.Linearize

-- Test to see goal state
example (a : ℝ) (h : a < (2 : ℝ)^100) : True := by
  linearize h
  -- Let's see what the goal state is after linearize
  sorry
