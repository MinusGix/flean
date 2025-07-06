import Flean.Defs

namespace FiniteFp

variable [FloatFormat]

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

def toRat (x : FiniteFp) : ℚ := x.toVal

noncomputable
def toReal (x : FiniteFp) : ℝ := x.toVal

end toVal

end FiniteFp

namespace Fp

variable [FloatFormat]

def toVal? {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : Fp) : Option R :=
  match x with
  | .finite x => some (FiniteFp.toVal x)
  | .infinite _ => none
  | .NaN => none

def toRat? (x : Fp) : Option ℚ := toVal? x

noncomputable
def toReal? (x : Fp) : Option ℝ := toVal? x

end Fp
