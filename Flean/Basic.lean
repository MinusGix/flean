import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

import Flean.FloatFormat

/-! Based off of 'Handbook of Floating Point Arithmetic' by Jean-Michel Muller et al. -/
-- Some designs of floating point arithmetic talk about floats as a subset of the reals/rationals with some extra properties
-- This is helpful for nicer integration and extreme generality, but I believe is overkill and obscures the core idea.

variable [F : FloatFormat]

/-- Whether the (e, M)-pair of the exponent and integral significand is valid for a finite floating point number  -/
def IsValidFiniteVal [F : FloatFormat] (e : ℤ) (m : ℤ) : Prop :=
  sorry

@[ext]
structure FiniteFp where
  /-- The sign of the number. -/
  s : Bool
  /-- The normal significand. -/
  m : ℕ
  /-- The exponent -/
  e : ℤ
  valid : IsValidFiniteVal e m
deriving Repr
namespace FiniteFp

instance : Zero FiniteFp :=
  ⟨{ s := false, m := 0, e := 0, valid := sorry }⟩

def sign (x : FiniteFp) : ℤ :=
  if x.s then -1 else 1

def toRat (x : FiniteFp) : ℚ :=
  x.sign * x.m * (F.radix.val : ℚ)^x.e

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

/-- The sign of the number. The sign of NaN is left defined as 0 but that may not result in the same sign as the bit repr -/
def sign (x : Fp) : ℤ :=
  match x with
  | .finite x => x.sign
  | .infinite b => if b then 1 else -1
  | .NaN => 0

-- TODO: to EReal

-- TODO: convert to typical bit repr

end Fp
