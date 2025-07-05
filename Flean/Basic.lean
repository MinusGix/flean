import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Bits

import Flean.FloatFormat
import Flean.Util

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

section toVal

variable {R : Type*}

-- TODO: is there a way to make this default to ℚ? That's the most natural type to represent any floating point number.
def toVal [Field R] (x : FiniteFp) : R :=
  x.sign' * x.m * (FloatFormat.radix.val : R)^(x.e - FloatFormat.prec + 1)

@[simp]
theorem toVal_zero [Field R] : toVal (0 : FiniteFp) = (0 : R) := by
  delta toVal sign'
  norm_num
  simp_all only [reduceCtorEq, ↓reduceIte, mul_eq_zero]
  unfold_projs
  norm_num

@[simp]
theorem toVal_one [Field R] [LinearOrder R] [IsStrictOrderedRing R] : toVal (1 : FiniteFp) = (1 : R) := by
  rw [one_def]
  delta toVal sign'
  unfold FloatFormat.radix Radix.Binary
  norm_num
  rw [← @zpow_add' R _ 2]
  · simp_all only [sub_add_add_cancel, add_neg_cancel, zpow_zero]
  · simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_add_add_cancel, add_neg_cancel,
    not_true_eq_false, false_or, true_or]

@[simp]
theorem toVal_neg_eq_neg [Field R] (x : FiniteFp) : @toVal _ R _ (-x) = -toVal x := by
  rw [neg_def]
  delta toVal sign'
  norm_num
  split
  next h => simp_all only [Bool.false_eq_true, ↓reduceIte]
  next h => simp_all only [Bool.not_eq_false, ↓reduceIte, neg_neg]

@[simp]
theorem toVal_neg_one [Field R] [LinearOrder R] [IsStrictOrderedRing R] : toVal (-1 : FiniteFp) = (-1 : R) := by
  rw [toVal_neg_eq_neg, toVal_one]

@[simp]
theorem toVal_neg_zero [Field R] : toVal (-(0 : FiniteFp)) = (0 : R) := by
  rw [toVal_neg_eq_neg, toVal_zero, neg_zero]

/-- The integral significand of a finite float is zero iff the float converted to a value is zero -/
theorem toVal_significand_zero_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x : FiniteFp} : x.m = 0 ↔ toVal x = (0 : R) := by
  constructor
  · intro h
    unfold toVal sign'
    simp [h]
  · intro h
    unfold toVal sign' at h
    cases' (mul_eq_zero.mp h) with h1 h2
    · cases' (mul_eq_zero.mp h1) with h3
      · split_ifs at h3 <;> linarith
      · assumption_mod_cast
    · have : (FloatFormat.radix.val : R) ^ (x.e - ↑FloatFormat.prec + 1) ≠ 0 := by
        rw [FloatFormat.radix_val_eq_two]
        apply zpow_ne_zero
        norm_num
      contradiction

@[simp]
theorem toVal_pos [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : FiniteFp) (hs : x.s = false) (hm : 0 < x.m) : (0 : R) < toVal x := by
  unfold toVal sign'
  simp only [hs, Bool.false_eq_true, ↓reduceIte, one_mul, FloatFormat.radix_val_eq_two,
    Int.cast_ofNat, Nat.cast_pos, hm, mul_pos_iff_of_pos_left]
  linearize

/-- The float is positive iff the significand is positive and the sign is false -/
theorem toVal_pos_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x : FiniteFp} : x.s = false ∧ 0 < x.m ↔ (0 : R) < toVal x := by
  constructor
  · intro h
    exact toVal_pos x h.1 h.2
  · intro h
    split_ands
    · if h1 : x.s = true then
        rw [h1]
        unfold toVal sign' at h
        have : 0 ≤ ↑x.m * (FloatFormat.radix.val : R) ^ (x.e - ↑FloatFormat.prec + 1) := by
          apply mul_nonneg
          · simp
          · rw [FloatFormat.radix_val_eq_two]
            norm_num
            linearize
        simp [h1] at h
        linarith
      else
        simp [h1]
    · have mnz : x.m ≠ 0 := by
        intro hm
        have := (FiniteFp.toVal_significand_zero_iff (R := R)).mp hm
        linarith
      omega

@[simp]
theorem toVal_nonneg [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : FiniteFp) (hs : x.s = false) : (0 : R) ≤ toVal x := by
  unfold toVal sign'
  simp [hs, FloatFormat.radix_val_eq_two]
  apply mul_nonneg
  linarith
  linearize

-- There can't be a toVal_nonneg_iff in full generality because -0 ends up >= 0


end toVal

theorem eq_def (x y : FiniteFp) : x = y ↔ x.s = y.s ∧ x.e = y.e ∧ x.m = y.m := by
  constructor
  · intro h
    simp [h]
  · intro h
    ext
    <;> simp [h]

@[reducible]
def is_mag_le (x y : FiniteFp) : Prop :=
  if x.e = y.e then x.m ≤ y.m
  else if x.e > y.e then x.m * 2^((x.e - y.e).natAbs) ≤ y.m
  else x.m ≤ y.m * 2^((y.e - x.e).natAbs)

theorem is_mag_le_refl (x : FiniteFp) : is_mag_le x x := by
  simp [is_mag_le]

@[reducible]
def is_le (x y : FiniteFp) : Prop := (x.s ∧ !y.s) ∨
  (!x.s ∧ y.s ∧ x.m = 0 ∧ y.m = 0) ∨
  (!x.s ∧ !y.s ∧ is_mag_le x y) ∨
  (x.s ∧ y.s ∧ is_mag_le y x)

instance : LE FiniteFp := ⟨is_le⟩

instance : LT FiniteFp := ⟨fun x y => is_le x y ∧ x ≠ y⟩

theorem le_def (x y : FiniteFp) : x ≤ y ↔ is_le x y := by rfl

theorem le_def' (x y : FiniteFp) : x ≤ y ↔ ((x.s ∧ !y.s) ∨
  (!x.s ∧ y.s ∧ x.m = 0 ∧ y.m = 0) ∨
  (!x.s ∧ !y.s ∧ is_mag_le x y) ∨
  (x.s ∧ y.s ∧ is_mag_le y x)) := by rfl

theorem lt_def (x y : FiniteFp) : x < y ↔ is_le x y ∧ x ≠ y := by rfl

theorem mag_le_significand_le {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {j k : FiniteFp} : (j.is_mag_le k) ↔ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) ≤ (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) := by
  -- have ha : (j k : FiniteFp) → (j.is_mag_le k) ↔ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) ≤ (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) := by
  -- intro j k
  constructor
  · intro h
    unfold is_mag_le at h
    split_ifs at h with h1 h2
    · rw [h1]
      apply mul_le_mul_of_nonneg_right
      exact_mod_cast h
      linearize
    · --apply mul_le_of_le_div₀
      rw [mul_comm]
      apply mul_le_mul_of_mul_div_le
      rw [← zpow_sub₀]
      norm_num
      rw [← zpow_natAbs_nonneg_eq_zpow]
      exact_mod_cast h
      norm_num
      omega
      norm_num
      linearize
    · norm_num at h2
      apply mul_le_of_le_div₀
      · apply mul_nonneg
        linarith
        linearize
      · linearize
      · rw [mul_div_assoc, ← zpow_sub₀]
        norm_num
        rw [← zpow_natAbs_nonneg_eq_zpow]
        exact_mod_cast h
        norm_num
        omega
        norm_num
  · intro h
    unfold is_mag_le
    -- TODO: A lot of the logic is similar between forward/backward directions.
    split_ifs with h1 h2
    · rw [h1] at h
      apply (Nat.cast_le (α := R)).mp
      apply (mul_le_mul_right ?_).mp
      exact h
      linearize
    · apply (Nat.cast_le (α := R)).mp
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [zpow_natAbs_nonneg_eq_zpow]
      norm_num
      have h' : (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) / (2 : R)^(k.e - ↑FloatFormat.prec + 1) ≤ ↑k.m := by
        apply div_le_of_le_mul₀
        linearize
        linarith
        trivial
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      norm_num at h'
      trivial
      norm_num
      norm_num
      linarith
    · norm_num at h2
      apply (Nat.cast_le (α := R)).mp
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [zpow_natAbs_nonneg_eq_zpow]
      norm_num
      have h' : (j.m : R) ≤ (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) / (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
        apply (le_div_iff₀ ?_).mpr
        trivial
        linearize
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      norm_num at h'
      trivial
      norm_num
      norm_num
      omega

/-- The order on floats is the same as the order on their values
    This allows easier proofs for various properties. -/
theorem le_iff_toVal_le {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {x y : FiniteFp} : x ≤ y ↔ x.toVal (R := R) ≤ y.toVal (R := R) := by
  constructor
  · intro h
    rw [le_def'] at h
    unfold toVal sign'
    rw [FloatFormat.radix_val_eq_two]

    rcases h with _ | _ | _ | _
    <;> simp_all [mag_le_significand_le.mp]
    · have rhs_ng : 0 ≤ (y.m : R) * (2 : R) ^ (y.e - ↑FloatFormat.prec + 1) := by
        apply mul_nonneg
        linarith
        linearize
      have lhs_ng : 0 ≤ (x.m : R) * (2 : R) ^ (x.e - ↑FloatFormat.prec + 1) := by
        apply mul_nonneg
        linarith
        linearize
      linarith
  · intro h
    rw [le_def']
    unfold toVal sign' at h
    rw [FloatFormat.radix_val_eq_two] at h
    split_ifs at h with h1 h2 h3
    <;> simp_all
    · apply mag_le_significand_le.mpr h
    · have hj : (j : FiniteFp) → 0 ≤ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
        intro j
        apply mul_nonneg
        linarith
        linearize
      have hy := hj y
      have hx := hj x
      have hny := le_trans hx h
      have hy' : 0 ≤ (y.m : R) := by linarith
      have hny' : 0 ≤ -(y.m : R) := by
        rw [← neg_mul] at hny
        apply nonneg_of_mul_nonneg_left hny
        linearize
      have hyz : (y.m : R) = 0 := by linarith
      have hyz : y.m = 0 := by exact_mod_cast hyz
      have hx' : 0 ≤ (x.m : R) := by linarith
      if x.m = 0 then trivial
      else
        rename_i xnz
        have hx : 0 < (x.m : R) * (2 : R) ^ (x.e - ↑FloatFormat.prec + 1) := by
          apply mul_pos
          apply lt_of_le_of_ne hx'
          symm
          norm_num
          exact xnz
          linearize
        linarith
    · apply mag_le_significand_le.mpr h

theorem toVal_le (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x.toVal (R := R) ≤ y.toVal (R := R) → x ≤ y := by
  intro h
  apply (le_iff_toVal_le (R := R)).mpr
  exact h

theorem le_toVal_le (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x ≤ y → x.toVal (R := R) ≤ y.toVal (R := R) := by
  intro h
  apply (le_iff_toVal_le (R := R)).mp
  exact h

instance : Preorder FiniteFp := {
  le_refl := by simp [le_def', is_mag_le]
  le_trans := by
    intro a b c hab hbc
    have hab := le_toVal_le ℚ hab
    have hbc := le_toVal_le ℚ hbc
    apply toVal_le ℚ
    linarith
  lt := fun x y => x ≤ y ∧ ¬y ≤ x
  lt_iff_le_not_ge := by simp_all [le_def']
}

instance : PartialOrder FiniteFp := {
  le_antisymm := by
    intro a b hab hba
    rw [le_def'] at hab hba
    sorry
}

-- instance : IsStrictTotalOrder FiniteFp is_le := by

def isNormal (x : FiniteFp) : Prop := _root_.isNormal x.m

def isSubnormal (x : FiniteFp) : Prop := _root_.isSubnormal x.e x.m

def smallestPosSubnormal : FiniteFp := ⟨
  false,
  FloatFormat.min_exp,
  1,
  IsValidFiniteVal.smallestPosSubnormal
⟩

theorem smallestPosSubnormal_toVal {R : Type*} [Field R] : smallestPosSubnormal.toVal = (2 : R)^(FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
  unfold smallestPosSubnormal toVal sign'
  rw [FloatFormat.radix_val_eq_two]
  norm_num

theorem smallestPosSubnormal_isSubnormal : smallestPosSubnormal.isSubnormal := by
  have := FloatFormat.prec_pred_pow_le (R := ℕ)
  apply And.intro
  · rfl
  · unfold smallestPosSubnormal
    norm_num
    omega

theorem smallestPosSubnormal_lt_minExp {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
  smallestPosSubnormal.toVal < (2 : R) ^ FloatFormat.min_exp := by
  rw [smallestPosSubnormal_toVal]
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : R) < 2)
  have := FloatFormat.valid_prec
  omega

theorem smallestPosSubnormal_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : (0 : R) < smallestPosSubnormal.toVal := by
  rw [smallestPosSubnormal_toVal]
  linearize

def smallestPosNormal : FiniteFp := ⟨
  false,
  FloatFormat.min_exp,
  2^(FloatFormat.prec - 1),
  IsValidFiniteVal.smallestPosNormal
 ⟩

theorem smallestPosNormal_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : smallestPosNormal.toVal = (2 : R)^(FloatFormat.min_exp) := by
  unfold smallestPosNormal FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  norm_num
  rw [← zpow_add₀]
  simp only [sub_add_add_cancel, add_sub_cancel]
  norm_num

theorem smallestPosNormal_isNormal : smallestPosNormal.isNormal := by
  have := FloatFormat.valid_prec
  apply And.intro
  · apply pow_le_pow_right₀ (by norm_num) (by omega)
  · apply pow_lt_pow_right₀ (by norm_num) (by omega)

theorem smallestPosNormal_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : (0 : R) < smallestPosNormal.toVal := by
  rw [smallestPosNormal_toVal]
  linearize

def largestFiniteFloat : FiniteFp := ⟨
  false,
  FloatFormat.max_exp,
  2^(FloatFormat.prec) - 1,
  IsValidFiniteVal.largestFiniteFloat
⟩

theorem largestFiniteFloat_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : largestFiniteFloat.toVal = (2 : R)^(FloatFormat.max_exp) * ((2 : R) - (2 : R)^(-(FloatFormat.prec : ℤ) + 1)) := by
  unfold largestFiniteFloat FiniteFp.toVal FiniteFp.sign'
  have := FloatFormat.valid_prec
  rw [FloatFormat.radix_val_eq_two]
  norm_num
  rw [mul_comm, mul_sub, mul_one]
  rw [FloatFormat.pow_prec_nat_int]
  rw [sub_add, zpow_sub₀, zpow_sub₀]

  ring_nf
  rw [mul_comm _ 2, mul_assoc]
  rw [mul_inv_cancel₀, mul_one]
  have : (2 : R) ^ FloatFormat.max_exp * (2 ^ (FloatFormat.prec : ℤ))⁻¹ = 2 ^ FloatFormat.max_exp / (2 ^ (FloatFormat.prec : ℤ)) := by
    field_simp
  rw [this]
  rw [mul_comm _ 2, ← mul_sub]
  have : (2 : R) ^ FloatFormat.max_exp - (2 : R) ^ FloatFormat.max_exp / (2 : R) ^ (FloatFormat.prec : ℤ) = 2 ^ FloatFormat.max_exp * (1 - (2 ^ (FloatFormat.prec : ℤ))⁻¹) := by
    rw [division_def]
    have : ∀ (x y : R), x - x * y = x * (1 - y) := by
      intro x y
      ring_nf
    rw [this]
  rw [this]
  rw [← inv_zpow, inv_zpow']
  rw [← mul_assoc]
  rw [mul_comm 2 _, mul_assoc, mul_sub, mul_one]
  rw [show (2 : R) * (2 : R) ^ (-(FloatFormat.prec : ℤ)) = (2 : R)^(1 : ℤ) * (2 : R) ^ (-(FloatFormat.prec : ℤ)) by ring]
  rw [← zpow_add₀, ← sub_eq_add_neg]
  rw [← mul_sub]
  all_goals norm_num

theorem largestFiniteFloat_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : largestFiniteFloat.toVal > (0 : R) := by
  rw [largestFiniteFloat_toVal]
  have a1 := FloatFormat.max_exp_pos
  have a2 := FloatFormat.valid_prec
  have a3 := FloatFormat.prec_pred_pow_le (R := ℕ)
  have a4 := FloatFormat.exp_order_le
  have a5 := FloatFormat.min_exp_nonpos
  apply mul_pos
  · apply zpow_pos (by norm_num)
  · norm_num
    apply lt_trans
    apply zpow_lt_one_of_neg₀ (by norm_num) (by linarith)
    norm_num

theorem largestFiniteFloat_lt_maxExp_succ {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
  largestFiniteFloat.toVal < (2 : R) ^ (FloatFormat.max_exp + 1) := by
  rw [largestFiniteFloat_toVal]
  -- largestFiniteFloat = 2^max_exp * (2 - 2^(-prec+1))
  -- We need to show: 2^max_exp * (2 - 2^(-prec+1)) < 2^(max_exp + 1) = 2 * 2^max_exp
  -- This simplifies to: 2 - 2^(-prec+1) < 2
  -- Which is equivalent to: 0 < 2^(-prec+1)
  have h_pos : (0 : R) < (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := by
    apply zpow_pos (by norm_num)
  have h_lt : (2 : R) - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) < 2 := by
    linarith
  calc (2 : R) ^ FloatFormat.max_exp * ((2 : R) - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1))
    < (2 : R) ^ FloatFormat.max_exp * 2 := by {
      apply mul_lt_mul_of_pos_left h_lt
      apply zpow_pos (by norm_num) }
  _ = 2 * (2 : R) ^ FloatFormat.max_exp := by ring
  _ = (2 : R) ^ (FloatFormat.max_exp + 1) := by {
      rw [← zpow_one_add₀ (by norm_num : (2 : R) ≠ 0)]
      ring_nf }


-- TODO: prove that the smallest positive normal, smallest positive subnormal, and largest finite float are all truely their namesakes

-- Helper lemmas for the main theorem

theorem finite_neg_le_largest {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (f : FiniteFp) (h : f.s = true) : (f.toVal : R) ≤ (largestFiniteFloat.toVal : R) := by
  -- Negative float ≤ 0 ≤ positive largestFiniteFloat
  have h_neg : (f.toVal : R) ≤ 0 := by
    unfold toVal sign'
    simp [h, FloatFormat.radix_val_eq_two]
    apply mul_nonneg
    · apply Nat.cast_nonneg
    · apply zpow_nonneg (by norm_num : (0 : R) ≤ 2)
  exact le_trans h_neg (le_of_lt largestFiniteFloat_toVal_pos)

theorem finite_pos_le_largest {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (f : FiniteFp) (h_pos : f.s = false) :
  (f.toVal : R) ≤ (largestFiniteFloat.toVal : R) := by
  unfold toVal sign' largestFiniteFloat
  simp [h_pos]
  rw [FloatFormat.radix_val_eq_two]
  -- Goal: f.m * 2^(f.e - prec + 1) ≤ (2^prec - 1) * 2^(max_exp - prec + 1)

  have h_valid := f.valid
  unfold IsValidFiniteVal at h_valid
  have h_e_bound : f.e ≤ FloatFormat.max_exp := h_valid.2.1
  have h_m_bound : f.m < 2^FloatFormat.prec := h_valid.2.2.1

  by_cases h_e : f.e = FloatFormat.max_exp
  · -- Case: f.e = max_exp, need f.m ≤ 2^prec - 1
    rw [h_e]
    apply mul_le_mul_of_nonneg_right
    · -- f.m ≤ 2^prec - 1
      rw [FloatFormat.natCast_pow_prec_pred]
      norm_cast
      omega
    · exact zpow_nonneg (by norm_num) _
  · -- Case: f.e < max_exp
    have h_lt : f.e < FloatFormat.max_exp := lt_of_le_of_ne h_e_bound h_e
    have h_pow_le : ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R) ≤
                     ((2 : R) ^ (FloatFormat.max_exp - (FloatFormat.prec : ℤ) + 1) : R) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2)
      omega
    have h_m_le : (f.m : R) ≤ (2 : R) ^ FloatFormat.prec - 1 := by
      rw [FloatFormat.natCast_pow_prec_pred]
      norm_cast
      omega

    rw [Int.cast_two]
    calc (f.m : R) * ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R)
       ≤ ((2 : R) ^ FloatFormat.prec - 1) * ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R) := by {
         apply mul_le_mul_of_nonneg_right h_m_le
         exact zpow_nonneg (by norm_num) _ }
     _ ≤ ((2 : R) ^ FloatFormat.prec - 1) * ((2 : R) ^ (FloatFormat.max_exp - (FloatFormat.prec : ℤ) + 1) : R) := by {
         apply mul_le_mul_of_nonneg_left h_pow_le
         simp only [sub_nonneg]
         apply le_trans (by norm_num : (1 : R) ≤ 4)
         exact FloatFormat.prec_pow_le }

-- Main theorem: largestFiniteFloat is indeed the largest
theorem finite_le_largestFiniteFloat {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (f : FiniteFp) : (f.toVal : R) ≤ (largestFiniteFloat.toVal : R) := by
  by_cases h : f.s
  · -- Negative case
    exact finite_neg_le_largest f h
  · -- Positive case (works for both normal and subnormal)
    have h_pos : f.s = false := by simp at h; exact h
    exact finite_pos_le_largest f h_pos

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

def toVal? {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : Fp) : Option R :=
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
