import Flean.Gsplit.Gsplit
import Mathlib.Data.Real.Basic

example (x y : ℝ) : min x y ≤ x := by
  gsplit min with h
  · rw [h.left]
  · rw [h.left]
    apply le_of_lt h.right
