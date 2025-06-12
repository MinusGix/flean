import Batteries.Tactic.Lint.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Ineq

-- Based off of linarith

namespace PowLinarith

lemma eq_of_not_lt_of_not_gt {α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
  le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

end PowLinarith
