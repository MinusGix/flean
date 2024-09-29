import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Bits

import Flean.FloatFormat

/-! Based off of 'Handbook of Floating Point Arithmetic' by Jean-Michel Muller et al. -/
-- Some designs of floating point arithmetic talk about floats as a subset of the reals/rationals with some extra properties
-- This is helpful for nicer integration and extreme generality, but I believe is overkill and obscures the core idea.

variable [F : FloatFormat]

-- We want to constraint `m`'s bitsize to be less than `FloatFormat.prec`
-- but we also need to constraint the values, as `m` should be less than `1.0`, of which our current comparison is essentially just asking if it is less than 2^prec
--
/-- Whether the (e, M)-pair of the exponent and integral significand is valid for a finite floating point number  -/
@[reducible]
def IsValidFiniteVal [FloatFormat] (e : ℤ) (m : ℕ) : Prop :=
  -- TODO: is this properly normalized?

  -- The exponent is above the minimum
  e ≥ FloatFormat.min_exp ∧ e ≤ FloatFormat.max_exp ∧
  -- We can represent the integral significand with prec bits
  m ≤ 2^FloatFormat.prec - 1 ∧
  -- Normal/subnormal; as well as ensuring that (s, M, e) is a unique repr for some number
  (
    -- normal number
    (2^(FloatFormat.prec - 1) ≤ m ∧ m < 2^FloatFormat.prec) ∨
    -- subnormal number
    (e = FloatFormat.min_exp ∧ m ≤ 2^(FloatFormat.prec - 1) - 1)
  )

@[ext]
structure FiniteFp where
  /-- The sign of the number. -/
  s : Bool
  /-- The exponent -/
  e : ℤ
  /-- The integral significand. Without the sign. -/
  m : ℕ
  valid : IsValidFiniteVal e m
deriving Repr
namespace FiniteFp

instance : Zero FiniteFp :=
  ⟨{
    s := false,
    m := 0,
    e := FloatFormat.min_exp,
    valid := by
      unfold IsValidFiniteVal
      simp only [ge_iff_le, le_refl, FloatFormat.valid_exp'_le, zero_le, nonpos_iff_eq_zero,
        pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, Nat.ofNat_pos, pow_pos, and_true,
        and_self, or_true]
  }⟩

def sign (x : FiniteFp) : ℤ :=
  if x.s then -1 else 1

def toRat (x : FiniteFp) : ℚ :=
  x.sign * x.m * (F.radix.val : ℚ)^(x.e - FloatFormat.prec + 1)

noncomputable
def toReal (x : FiniteFp) : ℝ :=
  x.toRat

end FiniteFp

inductive Fp where
  | finite : FiniteFp → Fp
  | infinite : Bool → Fp
  /-- Indeterminate NaN value. At this level, the specific bits are not considered. -/
  | NaN : Fp

namespace Fp

instance : Zero Fp := ⟨.finite 0⟩

/-- The sign of the number. The sign of NaN is left defined as 0 but that may not result in the same sign as the bit repr -/
def sign (x : Fp) : ℤ :=
  match x with
  | .finite x => x.sign
  | .infinite b => if b then 1 else -1
  | .NaN => 0

-- TODO: to EReal

-- TODO: convert to typical bit repr

end Fp

-- def f := @FiniteFp.toRat FloatFormat.Binary32
-- #eval! f (0 : @FiniteFp FloatFormat.Binary32)
