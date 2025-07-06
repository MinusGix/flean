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
    have : ¬isNormal 0 := by simp [isNormal]
    norm_num [this] at vf
    have := isSubnormal.zero_iff.mp vf.right.right
    simp [this, h]
  · intro h
    rw [eq_def, eq_def] at h
    norm_num at h
    cases' h with h1 h1 <;> simp [h1]


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

@[simp]
theorem toVal_isZero [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x : FiniteFp} : x.isZero → toVal x = (0 : R) := by
  intro h
  simp_all [isZero, toVal]

end toVal

@[reducible]
def is_mag_lt (x y : FiniteFp) : Prop :=
  if x.e = y.e then x.m < y.m
  else if x.e > y.e then x.m * 2^((x.e - y.e).natAbs) < y.m
  else x.m < y.m * 2^((y.e - x.e).natAbs)

@[reducible]
def is_lt (x y : FiniteFp) : Prop :=
  (x.s ∧ !y.s) ∨
  (!x.s ∧ !y.s ∧ x.is_mag_lt y) ∨
  (x.s ∧ y.s ∧ y.is_mag_lt x)

instance : LT FiniteFp := ⟨is_lt⟩

@[reducible]
def is_mag_le (x y : FiniteFp) : Prop :=
  if x.e = y.e then x.m ≤ y.m
  else if x.e > y.e then x.m * 2^((x.e - y.e).natAbs) ≤ y.m
  else x.m ≤ y.m * 2^((y.e - x.e).natAbs)

theorem is_mag_le_refl (x : FiniteFp) : is_mag_le x x := by
  simp [is_mag_le]

@[reducible]
def is_le (x y : FiniteFp) : Prop := x < y ∨ x = y

theorem is_mag_lt_imp_is_mag_le {x y : FiniteFp} : x.is_mag_lt y → x.is_mag_le y := by
  unfold is_mag_lt is_mag_le
  intro h
  split_ifs at h with h1 h2
  · simp [h1, le_of_lt h]
  · simp [h1, h2, le_of_lt h]
  · simp [h1, h2, le_of_lt h]

instance : LE FiniteFp := ⟨is_le⟩

theorem le_def (x y : FiniteFp) : x ≤ y ↔ (x < y ∨ x = y) := by rfl

theorem lt_def (x y : FiniteFp) : x < y ↔ (x.s ∧ !y.s) ∨
  (!x.s ∧ !y.s ∧ x.is_mag_lt y) ∨
  (x.s ∧ y.s ∧ y.is_mag_lt x) := by rfl

theorem is_lt_imp_is_le {x y : FiniteFp} : x < y → x ≤ y := by
  rw [lt_def, le_def, lt_def, eq_def]
  intro h
  simp_all

theorem lt_imp_ne {x y : FiniteFp} : x < y → x ≠ y := by
  rw [lt_def]
  intro h
  norm_num
  rw [eq_def]
  intro hn
  simp_all [is_mag_lt]

theorem mag_lt_disjoint {x y : FiniteFp} : x.is_mag_lt y → ¬y.is_mag_lt x := by
  unfold is_mag_lt
  intro h
  split_ifs at h
  · simp_all [le_of_lt h]
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem zero_le_zero : (0 : FiniteFp) ≤ 0 := by
  simp only [zero_def, le_def, or_true]

theorem neg_zero_le_zero : (-0 : FiniteFp) ≤ 0 := by
  simp only [zero_def, neg_def, Bool.not_false, le_def, lt_def, and_self, Bool.not_true,
    Bool.false_eq_true, true_and, false_and, and_false, or_self, or_false, mk.injEq,
    Bool.true_eq_false, and_true]

theorem not_zero_le_neg_zero : ¬(0 : FiniteFp) ≤ (-0 : FiniteFp) := by
  simp only [zero_def, neg_def, Bool.not_false, le_def, lt_def, Bool.false_eq_true, Bool.not_true,
    and_self, false_and, and_false, true_and, or_self, mk.injEq, and_true, not_false_eq_true]

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

theorem mag_lt_significand_lt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {j k : FiniteFp} : (j.is_mag_lt k) ↔ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) < (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) := by
  constructor
  · intro h
    unfold is_mag_lt at h
    split_ifs at h with h1 h2
    · rw [h1]
      apply (mul_lt_mul_iff_of_pos_right ?_).mpr
      assumption_mod_cast
      linearize
    · --rw [← zpow_natAbs_nonneg_eq_zpow]
      apply (mul_inv_lt_iff₀ ?_).mp -- why is there mul_le_mul_of_mul_div_le but no lt version and we have to do this rigmarole?
      rw [← inv_zpow, inv_zpow', mul_assoc, ← zpow_add₀]
      ring_nf
      rw [← zpow_natAbs_nonneg_eq_zpow]
      exact_mod_cast h
      norm_num
      linarith
      norm_num
      linearize
    · rw [mul_comm]
      apply (lt_inv_mul_iff₀ ?_).mp
      rw [mul_comm, mul_assoc, ← inv_zpow, inv_zpow', ← zpow_add₀]
      ring_nf
      rw [← zpow_natAbs_nonneg_eq_zpow]
      exact_mod_cast h
      norm_num
      linarith
      norm_num
      linearize
  · intro h
    unfold is_mag_lt
    split_ifs with h1 h2
    · rw [h1] at h
      apply (Nat.cast_lt (α := R)).mp
      apply (mul_lt_mul_right ?_).mp
      exact h
      linearize
    · apply (Nat.cast_lt (α := R)).mp
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [zpow_natAbs_nonneg_eq_zpow]
      norm_num
      have h' : (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) / (2 : R)^(k.e - ↑FloatFormat.prec + 1) < ↑k.m := by
        rw [div_eq_mul_inv]
        apply (mul_inv_lt_iff₀ ?_).mpr
        trivial
        linearize
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      ring_nf at h'
      trivial
      norm_num
      norm_num
      linarith
    · norm_num at h2
      have h' : (j.m : R) < (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) / (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
        apply (lt_div_iff₀ ?_).mpr
        trivial
        linearize
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      ring_nf at h'
      rw [← zpow_natAbs_nonneg_eq_zpow] at h'
      exact_mod_cast h'
      norm_num
      linarith
      norm_num



theorem le_toVal_le (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x ≤ y → x.toVal (R := R) ≤ y.toVal (R := R) := by
  have hj : (j : FiniteFp) → 0 ≤ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
    intro j
    apply mul_nonneg
    linarith
    linearize
  intro h
  rw [le_def, lt_def] at h
  unfold toVal sign'
  rw [FloatFormat.radix_val_eq_two]
  rcases h with ⟨h1, h2⟩ | h3
  · simp_all
    have hx := hj x
    have hy := hj y
    linarith
  · rename_i h4
    cases' h4 with h1 h1
    · simp_all
      apply le_of_lt
      apply mag_lt_significand_lt.mp h1.right.right
    · simp_all
      apply le_of_lt
      apply mag_lt_significand_lt.mp h1.right.right
  · simp_all

/-- The order on floats is the same as the order on their values
    This allows easier proofs for various properties. -/
theorem toVal_le (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {x y : FiniteFp} : x.toVal (R := R) ≤ y.toVal (R := R) → (¬x.isZero ∨ ¬y.isZero) → x ≤ y := by
  have hj : (j : FiniteFp) → 0 ≤ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
    intro j
    apply mul_nonneg
    linarith
    linearize
  intro hv hnz
  have ho : (x y : FiniteFp) → x.e > y.e → ↑x.m * (2 : R) ^ (x.e - ↑FloatFormat.prec + 1) ≤ ↑y.m * (2 : R) ^ (y.e - ↑FloatFormat.prec + 1) → x.m * 2 ^ (x.e - y.e).natAbs < y.m := by
    intro x y hxy hv
    -- TOOD: I think I could merge hv and y_m too large into one calc
    have hv : ↑x.m * (2 : R) ^ (x.e - y.e).natAbs ≤ ↑y.m := by
      rw [← mul_inv_le_iff₀ (by linearize), mul_assoc, ← inv_zpow, inv_zpow', ← zpow_add₀ (by norm_num)] at hv
      ring_nf at hv
      rw [← zpow_natAbs_nonneg_eq_zpow (by linarith) (by linarith)] at hv
      exact hv
    apply lt_of_le_of_ne (by exact_mod_cast hv)
    intro heq
    have := valid_min_exp_lt_imp_isNormal (by linarith [y.valid_min_exp])
    unfold isNormal at this
    have yvf := y.valid.right.right.left
    have y_m_too_large : 2^(FloatFormat.prec) ≤ y.m := by
      calc 2^FloatFormat.prec
        _ = 2^(FloatFormat.prec - 1 + 1) := by rw[Nat.sub_add_cancel (by fomega)]
        _ = 2^(FloatFormat.prec - 1) * 2 := by rw [Nat.pow_add_one]
        _ ≤ x.m * 2 := by omega
        _ ≤ x.m * 2^((x.e - y.e).natAbs) := by
          gcongr
          apply le_self_pow₀ (by norm_num) (by omega)
        _ = y.m := by omega
    omega -- contradiction

  have hol : (x y : FiniteFp) → x.m * (2 : R)^(x.e - ↑FloatFormat.prec + 1) ≤ y.m * (2 : R)^(y.e - ↑FloatFormat.prec + 1) → x.is_mag_lt y ∨ x.e = y.e ∧ x.m = y.m := by
    intro x y hv
    rw [is_mag_lt]
    split_ifs with he he1
    · rw [he] at hv
      rw [mul_le_mul_right] at hv
      norm_num [he]
      apply lt_or_eq_of_le
      assumption_mod_cast
      linearize
    · left
      apply ho x y he1 hv
    · norm_num at he1
      have he1 := lt_of_le_of_ne he1 he
      left
      have hv : ↑x.m ≤ ↑y.m * (2 : R) ^ (y.e - x.e).natAbs := by
        rw [← le_mul_inv_iff₀ (by linearize), mul_assoc, ← inv_zpow, inv_zpow', ← zpow_add₀ (by norm_num)] at hv
        ring_nf at hv
        rw [← zpow_natAbs_nonneg_eq_zpow (by norm_num) (by linarith)] at hv
        exact hv
      apply lt_of_le_of_ne (by exact_mod_cast hv)

      intro heq
      have := x.valid.right.right.left
      have is_normal_y : isNormal y.m := valid_min_exp_lt_imp_isNormal (by linarith [x.valid_min_exp])
      have xm_too_large : 2^FloatFormat.prec ≤ x.m := by
        calc 2^FloatFormat.prec
          _ = 2^(FloatFormat.prec - 1 + 1) := by rw[Nat.sub_add_cancel (by fomega)]
          _ = 2^(FloatFormat.prec - 1) * 2 := by rw [Nat.pow_add_one]
          _ ≤ y.m * 2 := by omega
          _ ≤ y.m * 2^((y.e - x.e).natAbs) := by
            gcongr
            apply le_self_pow₀ (by norm_num) (by omega)
          _ = x.m := by omega
      omega

  unfold isZero at hnz
  unfold toVal sign' at hv
  norm_num at hv
  rw [le_def, lt_def, eq_def]
  rw [FloatFormat.radix_val_eq_two] at hv
  split_ifs at hv with h1 h2 h3
  · norm_num [h1, h2] at hv ⊢
    rw [eq_comm (a := x.e), eq_comm (a := x.m)] -- why does apply consider Or/And order relevant?
    apply hol y x hv
  · norm_num [h1, h2] at hv ⊢
  · norm_num [h1, h3] at hv ⊢
    have hx := hj x
    have hy := hj y
    have hn : 0 = ↑x.m * (2 : R) ^ (x.e - ↑FloatFormat.prec + 1) := by linarith
    have hn : 0 = ↑y.m * (2 : R) ^ (y.e - ↑FloatFormat.prec + 1) := by linarith
    simp_all [zpow_ne_zero]
  · norm_num [h1, h3] at hv ⊢
    apply hol x y hv

/-- toVal_le but where you handle the case where the values are zero, proving it manually, since 0 and -0 are not necessarily distinguished in R -/
theorem toVal_le_handle (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {x y : FiniteFp} : x.toVal (R := R) ≤ y.toVal (R := R) → ((x.isZero ∧ y.isZero) → x ≤ y) → x ≤ y := by
  intro hxy
  intro hnz
  if hz : x.isZero ∧ y.isZero then
    apply hnz hz
  else
    apply toVal_le R hxy
    rw [not_and_or] at hz
    exact hz



instance : Preorder FiniteFp := {
  le_refl := by simp [le_def]
  le_trans := by
    intro a b c hab hbc
    have hab := le_toVal_le ℚ hab
    have hbc := le_toVal_le ℚ hbc
    apply toVal_le_handle ℚ (by linarith)
    intro hz
    rw [isZero_iff, isZero_iff] at hz
    norm_num at hz
    norm_num
    rcases hz with ⟨h1 | h2, h3 | h4⟩
    · simp [le_def, h1, h3]
    · have := not_zero_le_neg_zero
      rename_i ha hb
      rw [h1] at ha
      rw [h4] at hb
      simp_all [le_def, lt_def, zero_def, neg_def, is_mag_lt, toVal, sign', FloatFormat.radix_val_eq_two]
      aesop
    · simp [neg_zero_le_zero, h2, h3]
    · simp [le_def, h2, h4]
  lt := fun a b => a < b
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro ha
      have hn := lt_imp_ne ha
      rw [le_def, lt_def, le_def, lt_def]
      split_ands
      · left
        rw [lt_def] at ha
        simp_all
      · intro hv
        rw [lt_def] at ha
        have hv := Or.resolve_right hv hn
        cases' ha
        <;> cases' hv
        · simp_all
        · simp_all
        · simp_all
        · norm_num at hn
          rw [eq_def] at hn
          rw [is_mag_lt] at *
          simp_all
          grind
    · sorry




    -- constructor
    -- · intro h
    --   rw [lt_def] at h
    --   rw [le_def', le_def']
    --   split_ands
    --   · rcases h with h1 | h2 | h3
    --     · simp_all
    --     · grind
    --     · grind
    --   · rcases h with h1 | h2 | h3
    --     · norm_num at h1
    --       rw [h1.left, h1.right]
    --       sorry -- here
    --     · grind
    --     · grind
    -- · intro hab
    --   rw [le_def', le_def'] at hab
    --   obtain ⟨hab, hba⟩ := hab
    --   rw [lt_def]
    --   rcases hab with h1 | h2 | h3
    --   · grind
    --   · grind
    --   · sorry
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
