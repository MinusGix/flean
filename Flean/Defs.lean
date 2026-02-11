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
def isNormal [FloatFormat] (m : ℕ) : Prop := (2^(FloatFormat.prec - 1).toNat ≤ m ∧ m < 2^FloatFormat.prec.toNat)
/-- Subnormal numbers are those with exponent `FloatFormat.min_exp` and significand less than `2^(FloatFormat.prec - 1)`. Note that we include zero in our notion of a subnormal number, even if it is not quite the same. -/
@[reducible]
def isSubnormal [FloatFormat] (e : ℤ) (m : ℕ) : Prop := (e = FloatFormat.min_exp ∧ m ≤ 2^(FloatFormat.prec - 1).toNat - 1)

/-- Characterize isNormal using ℤ comparisons for omega compatibility -/
theorem isNormal_iff_int [FloatFormat] (m : ℕ) :
    isNormal m ↔ (2 : ℤ)^(FloatFormat.prec - 1).toNat ≤ m ∧ (m : ℤ) < (2 : ℤ)^FloatFormat.prec.toNat := by
  simp only [isNormal, Int.two_pow_eq_nat_cast]
  constructor <;> intro h <;> omega

/-- Characterize isSubnormal using ℤ comparisons for omega compatibility -/
theorem isSubnormal_iff_int [FloatFormat] (e : ℤ) (m : ℕ) :
    isSubnormal e m ↔ e = FloatFormat.min_exp ∧ (m : ℤ) ≤ (2 : ℤ)^(FloatFormat.prec - 1).toNat - 1 := by
  simp only [isSubnormal, Int.two_pow_eq_nat_cast]
  have hpow_pos : 1 ≤ (2 : ℕ)^(FloatFormat.prec - 1).toNat := Nat.one_le_two_pow
  constructor <;> intro h <;> omega

/-- sig_msb stands for significand most significant bit, because `2^(prec - 1)` means that only the topmost bit is set-/
theorem isNormal.sig_msb [FloatFormat] : isNormal (2^(FloatFormat.prec - 1).toNat) := by
  have := FloatFormat.valid_prec
  constructor
  · rfl
  · exact FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec

/-- sig_max stands for significand max, where all bits are set -/
theorem isNormal.sig_max [FloatFormat] : isNormal (2^FloatFormat.prec.toNat - 1) := by
  have hlt := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
  have hge := FloatFormat.nat_four_le_two_pow_prec
  constructor
  · apply Nat.le_pred_of_lt hlt
  · omega

theorem isSubnormal.min_exp_one [FloatFormat] : isSubnormal FloatFormat.min_exp 1 := by
  have := FloatFormat.nat_two_le_two_pow_prec_sub_one
  exact ⟨rfl, by omega⟩

theorem isSubnormal.zero [FloatFormat] : isSubnormal FloatFormat.min_exp 0 := ⟨rfl, by omega⟩

theorem isSubnormal.zero_iff [FloatFormat] {e : ℤ} : isSubnormal e 0 ↔ e = FloatFormat.min_exp := by simp [isSubnormal]

/-- Whether the (e, M)-pair of the exponent and integral significand is valid for a finite floating point number  -/
@[reducible]
def IsValidFiniteVal [FloatFormat] (e : ℤ) (m : ℕ) : Prop :=
  -- TODO: is this properly normalized?

  -- The exponent is above the minimum
  e ≥ FloatFormat.min_exp ∧ e ≤ FloatFormat.max_exp ∧
  -- We can represent the integral significand with prec bits
  m < 2^FloatFormat.prec.toNat ∧
  -- Normal/subnormal; as well as ensuring that (s, M, e) is a unique repr for some number
  (isNormal m ∨ isSubnormal e m)

theorem IsValidFiniteVal.zero [FloatFormat] : IsValidFiniteVal FloatFormat.min_exp 0 := by
  have := FloatFormat.nat_four_le_two_pow_prec
  exact ⟨le_refl _, FloatFormat.exp_order_le, by omega, Or.inr isSubnormal.zero⟩

theorem IsValidFiniteVal.one [FloatFormat] : IsValidFiniteVal 0 (2^(FloatFormat.prec - 1).toNat) := by
  have := FloatFormat.valid_prec
  have := FloatFormat.nat_two_le_two_pow_prec_sub_one
  have hlt := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
  have := FloatFormat.exp_order_le
  have := FloatFormat.max_exp_pos
  have := FloatFormat.min_exp_nonpos
  exact ⟨by omega, by omega, hlt, Or.inl isNormal.sig_msb⟩

theorem IsValidFiniteVal.smallestPosSubnormal [FloatFormat] : IsValidFiniteVal FloatFormat.min_exp 1 := by
  have := FloatFormat.nat_four_le_two_pow_prec
  exact ⟨le_refl _, FloatFormat.exp_order_le, by omega, Or.inr isSubnormal.min_exp_one⟩

theorem IsValidFiniteVal.smallestPosNormal [FloatFormat] : IsValidFiniteVal FloatFormat.min_exp (2^(FloatFormat.prec - 1).toNat) :=
  ⟨le_refl _, FloatFormat.exp_order_le, FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec, Or.inl isNormal.sig_msb⟩

theorem IsValidFiniteVal.largestFiniteFloat [FloatFormat] : IsValidFiniteVal FloatFormat.max_exp (2^FloatFormat.prec.toNat - 1) := by
  have := FloatFormat.valid_prec
  have := FloatFormat.nat_four_le_two_pow_prec
  have := FloatFormat.nat_two_le_two_pow_prec_sub_one
  exact ⟨FloatFormat.exp_order_le, le_refl _, by omega, Or.inl isNormal.sig_max⟩

/-- Minor helper theorem to remove some verbosity from proving a subnormal valid finite float -/
theorem IsValidFiniteVal_subnormal [FloatFormat] (m : ℕ) : m ≤ 2^(FloatFormat.prec - 1).toNat - 1 → IsValidFiniteVal FloatFormat.min_exp m := by
  intro hm
  have hlt := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
  split_ands
  · exact le_refl _
  · exact FloatFormat.exp_order_le
  · calc m ≤ 2^(FloatFormat.prec - 1).toNat - 1 := hm
      _ < 2^(FloatFormat.prec - 1).toNat := Nat.sub_lt (Nat.one_le_two_pow) (by norm_num)
      _ < 2^FloatFormat.prec.toNat := hlt
  · right
    exact ⟨rfl, hm⟩

/-- Conditionally negate a value based on a sign bit. -/
def condNeg {α : Type*} [Neg α] (s : Bool) (x : α) : α :=
  if s then -x else x

@[simp] theorem condNeg_true {α : Type*} [Neg α] (x : α) :
    condNeg true x = -x := rfl

@[simp] theorem condNeg_false {α : Type*} [Neg α] (x : α) :
    condNeg false x = x := rfl

@[ext]
structure FiniteFp [FloatFormat] where
  /-- The sign of the number. -/
  s : Bool
  /-- The exponent -/
  e : ℤ
  /-- The integral significand. Without the sign. -/
  m : ℕ
  valid : IsValidFiniteVal e m
deriving Repr, DecidableEq

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

instance : Inhabited FiniteFp := ⟨0⟩

instance : One FiniteFp :=
  ⟨{
    s := false,
    m := 2^(FloatFormat.prec - 1).toNat,
    e := 0,
    valid := IsValidFiniteVal.one
  }⟩

theorem one_def : (1 : FiniteFp) = {
  s := false,
  e := 0,
  m := 2^(FloatFormat.prec - 1).toNat,
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

@[simp] theorem neg_s (x : FiniteFp) : (-x).s = !x.s := rfl
@[simp] theorem neg_e (x : FiniteFp) : (-x).e = x.e := rfl
@[simp] theorem neg_m (x : FiniteFp) : (-x).m = x.m := rfl

instance : InvolutiveNeg FiniteFp := ⟨
  by
    intro x
    rw [neg_def, neg_def]
    norm_num
⟩

def sign (x : FiniteFp) : Bool := x.s

def sign'  {R : Type*} [Neg R] [One R] (x : FiniteFp) : R :=
  if x.s then -1 else 1

abbrev isZero (x : FiniteFp) : Prop := x.m = 0

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

instance {x : FiniteFp} : Decidable (x.isZero) := by
  unfold isZero
  infer_instance

end FiniteFp

-- /-- Floating point numbers with infinite values -/
-- inductive InfFp [FloatFormat]
-- | finite : FiniteFp → InfFp
-- | infinite : Bool → InfFp
-- deriving Repr, DecidableEq

-- namespace InfFp

-- variable [FloatFormat]

-- instance : Zero InfFp := ⟨.finite 0⟩

-- instance : Inhabited InfFp := ⟨0⟩

-- theorem zero_def : (0 : InfFp) = .finite 0 := rfl

-- instance : One InfFp := ⟨.finite 1⟩

-- theorem one_def : (1 : InfFp) = .finite 1 := rfl

-- def sign (x : InfFp) : Bool :=
--   match x with
--   | .finite x => x.sign
--   | .infinite b => b

-- def sign' {R : Type*} [Neg R] [One R] (x : InfFp) : R :=
--   match x with
--   | .finite x => x.sign'
--   | .infinite b => if b then 1 else -1

-- instance : Neg InfFp := ⟨fun x => match x with
--   | .finite x => .finite (-x)
--   | .infinite b => .infinite (!b)
-- ⟩

-- theorem neg_def (x : InfFp) : -x = match x with
--   | .finite x => .finite (-x)
--   | .infinite b => .infinite (!b) := rfl

-- instance : InvolutiveNeg InfFp := ⟨by
--   intro x
--   rw [neg_def, neg_def]
--   match x with
--   | .finite x => norm_num
--   | .infinite b => norm_num
-- ⟩

-- def isZero (x : InfFp) : Prop :=
--   match x with
--   | .finite x => x.isZero
--   | .infinite _ => false

-- theorem isZero_infinite (b : Bool) : ¬(InfFp.infinite b).isZero := by
--   simp [isZero]

-- def isInfinite (x : InfFp) : Prop :=
--   match x with
--   | .finite _ => false
--   | .infinite _ => true

-- def isFinite (x : InfFp) : Prop :=
--   match x with
--   | .finite _ => true
--   | .infinite _ => false

-- def finite_isFinite (x : FiniteFp) : (InfFp.finite x).isFinite := by
--   simp only [isFinite]

-- def infinite_isInfinite (x : Bool) : (InfFp.infinite x).isInfinite := by
--   simp only [isInfinite]

-- def isInfinite_notFinite (x : InfFp) : x.isInfinite → ¬x.isFinite := by
--   unfold isInfinite isFinite
--   aesop

-- def isFinite_notInfinite (x : InfFp) : x.isFinite → ¬x.isInfinite := by
--   unfold isInfinite isFinite
--   aesop



-- instance : Coe FiniteFp InfFp := ⟨InfFp.finite⟩


-- end InfFp



inductive Fp [FloatFormat] where
  | finite : FiniteFp → Fp
  | infinite : Bool → Fp
  /-- Indeterminate NaN value. At this level, the specific bits are not considered. -/
  | NaN : Fp
deriving Repr, DecidableEq

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

instance : One Fp := ⟨.finite 1⟩

theorem one_def : (1 : Fp) = .finite 1 := rfl

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
  next x x_1 => simp_all only []
  next x b => simp_all only [infinite.injEq, Bool.not_eq_true, not_true_eq_false]
  next x => simp_all only [not_true_eq_false]


-- TODO: to EReal

end Fp

-- This might be a better formulation due to a more automatic linking between the two types
abbrev InfFp [FloatFormat] := {x : Fp // x ≠ Fp.NaN}

namespace InfFp

variable [FloatFormat]

instance : Zero InfFp := ⟨⟨0, by simp⟩⟩

instance : Inhabited InfFp := ⟨0⟩

theorem zero_def : (0 : InfFp) = ⟨0, by simp⟩ := rfl

instance : One InfFp := ⟨⟨1, by simp⟩⟩

@[simp, reducible] def finite (x : FiniteFp) : InfFp := ⟨.finite x, by simp⟩

@[simp, reducible] def infinite (b : Bool) : InfFp := ⟨.infinite b, by simp⟩

def sign (x : InfFp) : Bool :=
  match x with
  | ⟨.finite x, _⟩ => x.sign
  | ⟨.infinite b, _⟩ => b
  | ⟨.NaN, _⟩ => false

def sign' {R : Type*} [Neg R] [One R] (x : InfFp) : R :=
  match x with
  | ⟨.finite x, _⟩ => x.sign'
  | ⟨.infinite b, _⟩ => if b then 1 else -1
  | ⟨.NaN, _⟩ => 1

instance : Neg InfFp := ⟨fun x => match x with
  | ⟨.finite x, _⟩ => ⟨.finite (-x), by simp⟩
  | ⟨.infinite b, _⟩ => ⟨.infinite (!b), by simp⟩
  | ⟨.NaN, _⟩ => ⟨0, by simp⟩⟩ -- can't occur

theorem neg_def (x : InfFp) : -x = match x with
  | ⟨.finite x, _⟩ => ⟨.finite (-x), by simp⟩
  | ⟨.infinite b, _⟩ => ⟨.infinite (!b), by simp⟩
  | ⟨.NaN, _⟩ => ⟨0, by simp⟩ := rfl -- can't occur

instance : InvolutiveNeg InfFp := ⟨by
  intro x
  rw [neg_def, neg_def]
  match x with
  | ⟨.finite x, _⟩ => norm_num
  | ⟨.infinite b, _⟩ => grind
  | ⟨.NaN, _⟩ => grind
⟩

def isZero (x : InfFp) : Prop :=
  match x with
  | ⟨.finite x, _⟩ => x.isZero
  | ⟨.infinite _, _⟩ => false
  | ⟨.NaN, _⟩ => false


theorem isZero_infinite (b : Bool) : ¬(InfFp.infinite b).isZero := by
  simp [isZero]

def isInfinite (x : InfFp) : Prop :=
  match x with
  | .finite _ => false
  | .infinite _ => true

def isFinite (x : InfFp) : Prop :=
  match x with
  | .finite _ => true
  | .infinite _ => false

def finite_isFinite (x : FiniteFp) : (InfFp.finite x).isFinite := by
  simp only [isFinite]

def infinite_isInfinite (x : Bool) : (InfFp.infinite x).isInfinite := by
  simp only [isInfinite]

def isInfinite_notFinite (x : InfFp) : x.isInfinite → ¬x.isFinite := by
  unfold isInfinite isFinite
  aesop

def isFinite_notInfinite (x : InfFp) : x.isFinite → ¬x.isInfinite := by
  unfold isInfinite isFinite
  aesop

instance : Coe FiniteFp InfFp := ⟨InfFp.finite⟩

-- instance : ConditionallyCompleteLattice

end InfFp
