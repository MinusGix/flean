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


-- We want to constraint `m`'s bitsize to be less than `FloatFormat.prec`
-- but we also need to constraint the values, as `m` should be less than `1.0`, of which our current comparison is essentially just asking if it is less than 2^prec
--

-- TODO: these should be defined in a namespace, possibly under a different name
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
structure FiniteFp [FloatFormat] where
  /-- The sign of the number. -/
  s : Bool
  /-- The exponent -/
  e : ℤ
  /-- The integral significand. Without the sign. -/
  m : ℕ
  valid : IsValidFiniteVal e m
deriving Repr
namespace FiniteFp

variable [FloatFormat]

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

theorem zero_def : (0 : FiniteFp) = {
  s := false,
  m := 0,
  e := FloatFormat.min_exp,
  -- TODO: is there a better way to do this?
  valid := (0 : FiniteFp).valid
} := rfl

instance : One FiniteFp :=
  ⟨{
    s := false,
    m := 2^(FloatFormat.prec - 1),
    e := 0,
    valid := by
      unfold IsValidFiniteVal isNormal isSubnormal
      have := FloatFormat.valid_prec
      have := FloatFormat.prec_pred_pow_le
      have := FloatFormat.exp_order_le
      have := FloatFormat.max_exp_pos
      have := FloatFormat.min_exp_nonpos
      split_ands
      · omega
      · omega
      · apply pow_lt_pow_right (by norm_num) (by omega)
      · left
        split_ands
        · rfl
        · apply pow_lt_pow_right (by norm_num) (by omega)
  }⟩

theorem one_def : (1 : FiniteFp) = {
  s := false,
  e := 0,
  m := 2^(FloatFormat.prec - 1),
  valid := (1 : FiniteFp).valid
} := rfl

instance : Neg FiniteFp := ⟨fun x => {
  s := !x.s,
  e := x.e,
  m := x.m,
  valid := x.valid
}⟩

theorem neg_def (x : FiniteFp) : -x = {
  s := !x.s,
  e := x.e,
  m := x.m,
  valid := x.valid
} := rfl

def sign (x : FiniteFp) : Bool := x.s

def sign'  {R : Type*} [Neg R] [One R] (x : FiniteFp) : R :=
  if x.s then -1 else 1

section toVal

variable {R : Type*} [LinearOrderedField R]

-- TODO: is there a way to make this default to ℚ? That's the most natural type to represent any floating point number.
def toVal (x : FiniteFp) : R :=
  x.sign' * x.m * (FloatFormat.radix.val : R)^(x.e - FloatFormat.prec + 1)

@[simp]
theorem toVal_zero : toVal (0 : FiniteFp) = (0 : R) := by
  delta toVal sign'
  norm_num
  left
  rfl

@[simp]
theorem toVal_one : toVal (1 : FiniteFp) = (1 : R) := by
  rw [one_def]
  delta toVal sign'
  unfold FloatFormat.radix Radix.Binary
  norm_num
  have : (2 : R)^(FloatFormat.prec - 1) = (2 : R)^((FloatFormat.prec : ℤ) - 1) := by
    conv => rhs; rw [← Nat.cast_one]
    rw [← Nat.cast_sub]
    rw [zpow_natCast]
    have := FloatFormat.valid_prec
    omega
  rw [this]
  rw [← @zpow_add' R _ 2]
  · simp_all only [sub_add_add_cancel, add_neg_cancel, zpow_zero]
  · simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_add_add_cancel, add_neg_cancel,
    not_true_eq_false, false_or, true_or]

@[simp]
theorem toVal_neg_eq_neg (x : FiniteFp) : @toVal _ R _ (-x) = -toVal x := by
  rw [neg_def]
  delta toVal sign'
  norm_num
  split
  next h => simp_all only [Bool.false_eq_true, ↓reduceIte]
  next h => simp_all only [Bool.not_eq_false, ↓reduceIte, neg_neg]

@[simp]
theorem toVal_neg_one : toVal (-1 : FiniteFp) = (-1 : R) := by
  rw [toVal_neg_eq_neg, toVal_one]

@[simp]
theorem toVal_neg_zero : toVal (-(0 : FiniteFp)) = (0 : R) := by
  rw [toVal_neg_eq_neg, toVal_zero, neg_zero]

end toVal

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

def toRat (x : FiniteFp) : ℚ := x.toVal

noncomputable
def toReal (x : FiniteFp) : ℝ := x.toVal

end FiniteFp

inductive Fp [FloatFormat] where
  | finite : FiniteFp → Fp
  | infinite : Bool → Fp
  /-- Indeterminate NaN value. At this level, the specific bits are not considered. -/
  | NaN : Fp

namespace Fp

variable [FloatFormat]

instance : Zero Fp := ⟨.finite 0⟩

instance : Inhabited Fp := ⟨0⟩

theorem zero_def : (0 : Fp) = .finite 0 := rfl

def sign (x : Fp) : Bool :=
  match x with
  | .finite x => x.sign
  | .infinite b => b
  | .NaN => false

/-- The sign of the number. The sign of NaN is left defined as 1 but that may not result in the same sign as the bit repr -/
def sign' {R : Type*} [Neg R] [One R] (x : Fp) : R :=
  match x with
  | .finite x => x.sign'
  | .infinite b => if b then 1 else -1
  | .NaN => 1

def isNaN (x : Fp) : Prop := x = .NaN

def isInfinite (x : Fp) : Prop := x = .infinite true ∨ x = .infinite false

-- Is there a better way to write these Matches are kinda weird for a Prop...
def isFinite (x : Fp) : Prop := match x with
  | .finite _ => true
  | .infinite _ => false
  | .NaN => false

def toVal? {R : Type*} [LinearOrderedField R] (x : Fp) : Option R :=
  match x with
  | .finite x => some (FiniteFp.toVal x)
  | .infinite _ => none
  | .NaN => none

def toRat? (x : Fp) : Option ℚ := toVal? x

noncomputable
def toReal? (x : Fp) : Option ℝ := toVal? x

def finite_isFinite (x : FiniteFp) : (Fp.finite x).isFinite := by
  unfold isFinite
  simp only

def infinite_isInfinite (x : Bool) : (Fp.infinite x).isInfinite := by
  unfold isInfinite
  simp only [infinite.injEq, Bool.eq_true_or_eq_false_self]

def NaN_isNaN : (Fp.NaN).isNaN := by
  unfold isNaN
  simp only

def isFinite_notNaN (x : Fp) : x.isFinite → ¬x.isNaN := by
  intro h
  unfold isNaN
  unfold isFinite at h
  simp_all only [Bool.false_eq_true]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only

def isFinite_notInfinite (x : Fp) : x.isFinite → ¬x.isInfinite := by
  intro h
  unfold isInfinite
  unfold isFinite at h
  simp_all only [Bool.false_eq_true, not_or]
  apply And.intro
  · apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only
  · apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only

def isInfinite_notNaN (x : Fp) : x.isInfinite → ¬x.isNaN := by
  intro h
  unfold isNaN
  unfold isInfinite at h
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [or_self]

def isInfinite_notFinite (x : Fp) : x.isInfinite → ¬x.isFinite := by
  intro h
  unfold isFinite
  unfold isInfinite at h
  simp_all only [Bool.false_eq_true]
  apply Aesop.BuiltinRules.not_intro
  intro a
  cases h with
  | inl h_1 =>
    subst h_1
    simp_all only
  | inr h_2 =>
    subst h_2
    simp_all only

def isNaN_notFinite (x : Fp) : x.isNaN → ¬x.isFinite := by
  intro h
  unfold isFinite
  unfold isNaN at h
  subst h
  simp_all only [Bool.false_eq_true, not_false_eq_true]

def isNaN_notInfinite (x : Fp) : x.isNaN → ¬x.isInfinite := by
  intro h
  unfold isInfinite
  unfold isNaN at h
  subst h
  simp_all only [or_self, not_false_eq_true]

def notNaN_notInfinite {x : Fp} : ¬x.isNaN → ¬x.isInfinite → x.isFinite := by
  intro hn hi
  unfold isFinite
  unfold isNaN at hn
  unfold isInfinite at hi
  simp_all only [not_or, Bool.false_eq_true]
  obtain ⟨left, right⟩ := hi
  split
  next x x_1 => simp_all only [not_false_eq_true]
  next x b => simp_all only [not_false_eq_true, infinite.injEq, Bool.not_eq_true, not_true_eq_false]
  next x => simp_all only [not_true_eq_false]


-- TODO: to EReal

end Fp
