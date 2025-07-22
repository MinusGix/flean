import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.TypeTags
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
-- class BoundedSymm (R : Type*) [LE R] [Neg R] extends BoundedOrder R where
--   top_eq_neg_bot : (⊤ : R) = -(⊥ : R)

-- The idea  behind these is/was to make so that R and an Extended R are related in a way that makes sense
-- Primarily for abstracting over EReal <-> ℝ, and a custom ERat <-> ℚ
-- However, I decied to instead make a total order on the `Fp` as that seemed simpler even if it was also more case-work

class CoeNeg (R : Type*) (α : Type*) [Neg R] [Neg α] [CoeHTCT R α] where
  coe_neg : ∀ (a : R), (↑(-a) : α) = (-a : α)

instance : CoeNeg ℤ ℚ := {
  coe_neg := fun a => by rfl
}

instance : CoeNeg ℚ ℝ := {
  coe_neg := fun a => by simp only [instCoeHTCTRatOfRatCast, Rat.cast_neg]
}

instance : CoeNeg ℤ ℝ := {
  coe_neg := fun a => by simp [instCoeHTCTIntOfIntCast]
}

instance : CoeNeg ℝ EReal := {
  coe_neg := fun a => by
    simp [instCoeHTCTOfCoeHTC, instCoeHTCOfCoeOTC, instCoeOTCOfCoeTC, instCoeTCOfCoe_1, EReal.instCoeReal]
}

-- TODO: EInt, ERat

class BoundedSymm (R : Type*) [Neg R] [Top R] [Bot R] where
  top_eq_neg_bot : (⊤ : R) = -(⊥ : R)

theorem coe_eq_coe {α} (a b : α) : (a : WithBot α) = b ↔ a = b := Option.some_inj
