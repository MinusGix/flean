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

@[reducible]
def isNormal [FloatFormat] (m : ℕ) : Prop := (2^(FloatFormat.prec - 1) ≤ m ∧ m < 2^FloatFormat.prec)
@[reducible]
def isSubnormal [FloatFormat] (e : ℤ) (m : ℕ) : Prop := (e = FloatFormat.min_exp ∧ m ≤ 2^(FloatFormat.prec - 1) - 1)

/-- Whether the (e, M)-pair of the exponent and integral significand is valid for a finite floating point number  -/
@[reducible]
def IsValidFiniteVal [FloatFormat] (e : ℤ) (m : ℕ) : Prop :=
  -- TODO: is this properly normalized?

  -- The exponent is above the minimum
  e ≥ FloatFormat.min_exp ∧ e ≤ FloatFormat.max_exp ∧
  -- We can represent the integral significand with prec bits
  m < 2^FloatFormat.prec ∧
  -- Normal/subnormal; as well as ensuring that (s, M, e) is a unique repr for some number
  (isNormal m ∨ isSubnormal e m)

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
      unfold IsValidFiniteVal isNormal isSubnormal
      simp [ge_iff_le, le_refl, FloatFormat.exp_order_le, zero_le, nonpos_iff_eq_zero,
        pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, Nat.ofNat_pos, pow_pos, and_true,
        and_self, or_true]
  }⟩

def sign (x : FiniteFp) : ℤ :=
  if x.s then -1 else 1

def toRat (x : FiniteFp) : ℚ :=
  x.sign * x.m * (FloatFormat.radix.val : ℚ)^(x.e - FloatFormat.prec + 1)

def isNormal (x : FiniteFp) : Prop := _root_.isNormal x.m

def isSubnormal (x : FiniteFp) : Prop := _root_.isSubnormal x.e x.m

def smallestPosSubnormal : FiniteFp := ⟨
  false,
  FloatFormat.min_exp,
  1,
  by
    unfold IsValidFiniteVal
    have := FloatFormat.valid_prec
    have := FloatFormat.prec_pow_le
    have := FloatFormat.prec_pred_pow_le
    split_ands
    · trivial
    · exact FloatFormat.exp_order_le
    · omega
    · right
      split_ands <;> omega
⟩

theorem smallestPosSubnormal_isSubnormal : smallestPosSubnormal.isSubnormal := by
  have := FloatFormat.prec_pred_pow_le
  apply And.intro
  · rfl
  · unfold smallestPosSubnormal
    norm_num
    omega

def smallestPosNormal : FiniteFp := ⟨
  false,
  FloatFormat.min_exp,
  2^(FloatFormat.prec - 1),
  by
    unfold IsValidFiniteVal
    have := FloatFormat.valid_prec
    split_ands
    · trivial
    · exact FloatFormat.exp_order_le
    · apply pow_lt_pow_right (by norm_num) (by omega)
    · left
      split_ands
      · apply pow_le_pow_right (by norm_num) (by omega)
      · apply pow_lt_pow_right (by norm_num) (by omega)
 ⟩

theorem smallestPosNormal_isNormal : smallestPosNormal.isNormal := by
  have := FloatFormat.valid_prec
  apply And.intro
  · apply pow_le_pow_right (by norm_num) (by omega)
  · apply pow_lt_pow_right (by norm_num) (by omega)

def largestFiniteFloat : FiniteFp := ⟨
  false,
  FloatFormat.max_exp,
  2^(FloatFormat.prec) - 1,
  by
    unfold IsValidFiniteVal
    have := FloatFormat.valid_prec
    have := FloatFormat.prec_pow_le
    have := FloatFormat.prec_pred_pow_le
    split_ands
    · exact FloatFormat.exp_order_le
    · rfl
    · omega
    · left
      split_ands
      · apply Nat.le_pred_of_lt
        norm_num
        apply pow_lt_pow_right (by norm_num) (by omega)
      · omega
⟩

-- TODO: prove that the smallest positive normal, smallest positive subnormal, and largest finite float are all truely their namesakes



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

instance : Inhabited Fp := ⟨0⟩

theorem zero_def : (0 : Fp) = .finite 0 := rfl

/-- The sign of the number. The sign of NaN is left defined as 0 but that may not result in the same sign as the bit repr -/
def sign (x : Fp) : ℤ :=
  match x with
  | .finite x => x.sign
  | .infinite b => if b then 1 else -1
  | .NaN => 0

def isNaN (x : Fp) : Prop := x = .NaN

def isInfinite (x : Fp) : Prop := x = .infinite true ∨ x = .infinite false

-- Is there a better way to write these Matches are kinda weird for a Prop...
def isFinite (x : Fp) : Prop := match x with
  | .finite _ => true
  | .infinite _ => false
  | .NaN => false

def toRat? (x : Fp) : Option ℚ :=
  match x with
  | .finite x => some (FiniteFp.toRat x)
  | .infinite _ => none
  | .NaN => none

-- TODO: to EReal

-- TODO: convert to typical bit repr

end Fp

-- def f := @FiniteFp.toRat FloatFormat.Binary32
-- #eval! f (0 : @FiniteFp FloatFormat.Binary32)
