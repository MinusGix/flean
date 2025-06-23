import Mathlib.Data.Int.Log
import Mathlib.Algebra.Group.Defs

/-!
# Linearize tactic helper lemmas

Helper theorems for the linearize tactic that encapsulate common transformation patterns.
-/

namespace Mathlib.Tactic.Linearize

variable {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

/-- Helper lemma for linearizing `r ≤ b^n` inequalities.
    This combines the case split `r ≤ b^n ↔ r < b^n ∨ r = b^n` with the appropriate logarithm theorems. -/
theorem le_zpow_imp_log_le {b : ℕ} (hb : 1 < b) {n : ℕ} {r : R} (hr : 0 < r) :
  r ≤ (b : R) ^ n → Int.log b r ≤ ↑n := by
  intro h
  cases' le_iff_lt_or_eq.mp h with h_lt h_eq
  · -- Case: r < b^n
    exact le_of_lt ((Int.lt_zpow_iff_log_lt hb hr).mp (by convert h_lt; simp [zpow_natCast]))
  · -- Case: r = b^n
    rw [h_eq]
    have h2_cast : (b : R) = ↑b := by norm_cast
    rw [h2_cast]
    rw [← zpow_natCast (↑b : R) n]
    rw [Int.log_zpow hb]

end Mathlib.Tactic.Linearize
