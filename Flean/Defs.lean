import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Bits

import Flean.FloatFormat
import Flean.Util


-- TODO: these should be defined in a namespace, possibly under a different name
@[reducible]
def isNormal [FloatFormat] (m : ℕ) : Prop := (2^(FloatFormat.prec - 1) ≤ m ∧ m < 2^FloatFormat.prec)
@[reducible]
def isSubnormal [FloatFormat] (e : ℤ) (m : ℕ) : Prop := (e = FloatFormat.min_exp ∧ m ≤ 2^(FloatFormat.prec - 1) - 1)

/-- sig_msb stands for significand most significant bit, because `2^(prec - 1)` means that only the topmost bit is set-/
theorem isNormal.sig_msb [FloatFormat] : isNormal (2^(FloatFormat.prec - 1)) := by
  have := FloatFormat.valid_prec
  exact ⟨by linarith, by apply pow_lt_pow_right₀ (by norm_num) (by omega)⟩

/-- sig_max stands for significand max, where all bits are set -/
theorem isNormal.sig_max [FloatFormat] : isNormal (2^(FloatFormat.prec) - 1) := by
  exact ⟨by apply Nat.le_pred_of_lt; norm_num, by norm_num⟩

theorem isSubnormal.min_exp_one [FloatFormat] : isSubnormal FloatFormat.min_exp 1 := by
  have := FloatFormat.prec_pred_pow_le (R := ℕ)
  exact ⟨by rfl, by omega⟩

theorem isSubnormal.zero [FloatFormat] : isSubnormal FloatFormat.min_exp 0 := by exact ⟨by rfl, by omega⟩

theorem isSubnormal.zero_iff [FloatFormat] {e : ℤ} : isSubnormal e 0 ↔ e = FloatFormat.min_exp := by simp [isSubnormal]

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

theorem IsValidFiniteVal.zero [FloatFormat] : IsValidFiniteVal FloatFormat.min_exp 0 := by
  have := FloatFormat.prec_pow_le (R := ℕ)
  exact ⟨by rfl, FloatFormat.exp_order_le, by omega, Or.inr isSubnormal.zero⟩

theorem IsValidFiniteVal.one [FloatFormat] : IsValidFiniteVal 0 (2^(FloatFormat.prec - 1)) := by
  have := FloatFormat.valid_prec
  have := FloatFormat.prec_pred_pow_le (R := ℕ)
  have := FloatFormat.exp_order_le
  have := FloatFormat.max_exp_pos
  have := FloatFormat.min_exp_nonpos
  exact ⟨by omega, by omega, by apply pow_lt_pow_right₀ (by norm_num) (by omega), Or.inl isNormal.sig_msb⟩

theorem IsValidFiniteVal.smallestPosSubnormal [FloatFormat] : IsValidFiniteVal FloatFormat.min_exp 1 := by
  have := FloatFormat.prec_pow_le (R := ℕ)
  exact ⟨by trivial, FloatFormat.exp_order_le, by omega, Or.inr isSubnormal.min_exp_one⟩

theorem IsValidFiniteVal.smallestPosNormal [FloatFormat] : IsValidFiniteVal FloatFormat.min_exp (2^(FloatFormat.prec - 1)) :=
  ⟨by trivial, FloatFormat.exp_order_le, FloatFormat.pow_prec_pred_lt, Or.inl isNormal.sig_msb⟩

theorem IsValidFiniteVal.largestFiniteFloat [FloatFormat] : IsValidFiniteVal FloatFormat.max_exp (2^(FloatFormat.prec) - 1) := by
  have := FloatFormat.valid_prec
  have := FloatFormat.prec_pow_le (R := ℕ)
  have := FloatFormat.prec_pred_pow_le (R := ℕ)
  exact ⟨FloatFormat.exp_order_le, by rfl, by omega, Or.inl isNormal.sig_max⟩

/-- Minor helper theorem to remove some verbosity from proving a subnormal valid finite float -/
theorem IsValidFiniteVal_subnormal [FloatFormat] (m : ℕ) : m ≤ 2^(FloatFormat.prec - 1) - 1 → IsValidFiniteVal FloatFormat.min_exp m := by
  intro hm
  split_ands
  · rfl
  · exact FloatFormat.exp_order_le
  · apply lt_of_le_of_lt hm
    have := FloatFormat.valid_prec
    have := FloatFormat.pow_prec_pred_lt
    apply lt_trans
    exact (by norm_num : 2 ^ (FloatFormat.prec - 1) - 1 < 2 ^ (FloatFormat.prec - 1)) -- for some reason can't pick up on this obvious fact and no clear lemma to use??
    simp only [FloatFormat.pow_prec_pred_lt]
  · right
    trivial

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

theorem valid_min_exp (x : FiniteFp) : FloatFormat.min_exp ≤ x.e := by
  have := x.valid
  unfold IsValidFiniteVal at this
  simp_all

theorem valid_max_exp (x : FiniteFp) : x.e ≤ FloatFormat.max_exp := by
  have := x.valid
  unfold IsValidFiniteVal at this
  simp_all

theorem valid_min_exp_lt_imp_isNormal {x : FiniteFp} : FloatFormat.min_exp < x.e → isNormal x.m := by
  intro h
  have := x.valid
  unfold IsValidFiniteVal at this
  grind


def isNormal (x : FiniteFp) : Prop := _root_.isNormal x.m

def isSubnormal (x : FiniteFp) : Prop := _root_.isSubnormal x.e x.m

instance : Zero FiniteFp :=
  ⟨{
    s := false,
    m := 0,
    e := FloatFormat.min_exp,
    valid := IsValidFiniteVal.zero
  }⟩

theorem zero_def : (0 : FiniteFp) = {
  s := false,
  m := 0,
  e := FloatFormat.min_exp,
  -- TODO: is there a better way to do this?
  valid := IsValidFiniteVal.zero
} := rfl

instance : One FiniteFp :=
  ⟨{
    s := false,
    m := 2^(FloatFormat.prec - 1),
    e := 0,
    valid := IsValidFiniteVal.one
  }⟩

theorem one_def : (1 : FiniteFp) = {
  s := false,
  e := 0,
  m := 2^(FloatFormat.prec - 1),
  valid := IsValidFiniteVal.one
} := rfl

theorem eq_def (x y : FiniteFp) : x = y ↔ x.s = y.s ∧ x.e = y.e ∧ x.m = y.m := by
  constructor
  · intro h
    simp [h]
  · intro h
    ext
    <;> simp [h]

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

instance : InvolutiveNeg FiniteFp := ⟨
  by
    intro x
    rw [neg_def, neg_def]
    norm_num
⟩

def sign (x : FiniteFp) : Bool := x.s

def sign'  {R : Type*} [Neg R] [One R] (x : FiniteFp) : R :=
  if x.s then -1 else 1

def isZero (x : FiniteFp) : Prop := x.m = 0

/-- There are only two representations of zero -/
def isZero_iff (x : FiniteFp) : x.isZero ↔ (x = 0 ∨ x = -0) := by
  rw [isZero, neg_def, zero_def]
  constructor
  · intro h
    rw [eq_def, eq_def]
    norm_num
    have vf := x.valid
    unfold IsValidFiniteVal at vf
    rw [h] at vf
    have : ¬_root_.isNormal 0 := by simp [_root_.isNormal]
    norm_num [this] at vf
    have := isSubnormal.zero_iff.mp vf.right.right
    simp [this, h]
  · intro h
    rw [eq_def, eq_def] at h
    norm_num at h
    cases' h with h1 h1 <;> simp [h1]

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

theorem zero_def : (0 : Fp) = .finite (
  {
  s := false,
  m := 0,
  e := FloatFormat.min_exp,
  -- TODO: is there a better way to do this?
  valid := IsValidFiniteVal.zero
}
) := rfl

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

instance : Neg Fp := ⟨fun x => match x with
  | .finite x => .finite (-x)
  | .infinite b => .infinite (!b)
  | .NaN => .NaN⟩

@[simp]
theorem neg_def (x : Fp) : -x = match x with
  | .finite x => .finite (-x)
  | .infinite b => .infinite (!b)
  | .NaN => .NaN := rfl

instance : InvolutiveNeg Fp := ⟨by
  intro x
  rw [neg_def, neg_def]
  match x with
  | .finite x => norm_num
  | .infinite b => norm_num
  | .NaN => norm_num
⟩

@[simp]
theorem neg_finite (f : FiniteFp) : -Fp.finite f = Fp.finite (-f) := rfl

def isNaN (x : Fp) : Prop := x = .NaN

def isInfinite (x : Fp) : Prop := x = .infinite true ∨ x = .infinite false

-- Is there a better way to write these Matches are kinda weird for a Prop...
def isFinite (x : Fp) : Prop := match x with
  | .finite _ => true
  | .infinite _ => false
  | .NaN => false

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
  simp_all only [reduceCtorEq, or_self]

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
  simp_all only [reduceCtorEq, or_self, not_false_eq_true]

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
