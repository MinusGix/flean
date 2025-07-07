import Flean.Defs

namespace FiniteFp

variable [FloatFormat]

section toVal

variable {R : Type*}

-- TODO: is there a way to make this default to ℚ? That's the most natural type to represent any floating point number.
def toVal [Field R] (x : FiniteFp) : R :=
  x.sign' * x.m * (FloatFormat.radix.val : R)^(x.e - FloatFormat.prec + 1)

def toVal_mag [Field R] (x : FiniteFp) : R := x.m * (FloatFormat.radix.val : R)^(x.e - FloatFormat.prec + 1)

theorem toVal_mag_nonneg [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : FiniteFp) : 0 ≤ toVal_mag x (R := R):= by
  unfold toVal_mag
  rw [FloatFormat.radix_val_eq_two]
  apply mul_nonneg (by norm_num) (by linearize)

theorem toVal_mag_nonneg' (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : FiniteFp) : 0 ≤ x.m * (2 : R)^(x.e - FloatFormat.prec + 1) := by
  rw [← Int.cast_two, ← FloatFormat.radix_val_eq_two]
  change 0 ≤ toVal_mag x (R := R)
  apply toVal_mag_nonneg

theorem toVal_eq_sign_mul_mag [Field R] (x : FiniteFp) : toVal x (R := R) = x.sign' * toVal_mag x := by
  unfold toVal sign' toVal_mag
  norm_num


theorem toVal_mag_toVal_abs [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : FiniteFp) : toVal_mag x = |toVal x (R := R)| := by
  rw [toVal_eq_sign_mul_mag]
  rw [abs_mul, sign', abs_ite]
  simp
  rw [abs_of_nonneg (toVal_mag_nonneg x)]


@[simp]
theorem toVal_zero [Field R] : toVal (0 : FiniteFp) = (0 : R) := by
  delta toVal sign'
  norm_num
  simp_all only [reduceCtorEq, ↓reduceIte, mul_eq_zero]
  unfold_projs
  norm_num

theorem toVal_mag_zero [Field R] : toVal_mag (0 : FiniteFp) = (0 : R) := by
  simp [toVal_mag, zero_def]

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

theorem toVal_mag_one [Field R] [LinearOrder R] [IsStrictOrderedRing R] : toVal_mag (1 : FiniteFp) = (1 : R) := by
  rw [toVal_mag_toVal_abs, toVal_one, abs_one]

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

theorem toVal_mag_pos [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : FiniteFp) (hm : 0 < x.m) : (0 : R) < toVal_mag x := by
  unfold toVal_mag
  rw [FloatFormat.radix_val_eq_two]
  apply mul_pos (by assumption_mod_cast) (by (norm_num; linearize))


-- There can't be a toVal_nonneg_iff in full generality because -0 ends up >= 0

@[simp]
theorem toVal_isZero [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x : FiniteFp} : x.isZero → toVal x = (0 : R) := by
  intro h
  simp_all [isZero, toVal]

/-- If two finite floats have the same sign and the same value, then they are equal
    The sign condition is effectively for keeping out zeros, because `toVal 0 = 0` and `toVal (-0) = 0`.
    They are the only two finite floats without a unique representation. -/
theorem eq_of_toVal_eq [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} (h_sign : x.s = y.s) : x.toVal (R := R) = y.toVal (R := R) → x = y := by
  intro hv
  unfold toVal sign' at hv
  rw [eq_def]
  rw [FloatFormat.radix_val_eq_two, h_sign, mul_assoc, mul_assoc, mul_eq_mul_left_iff] at hv
  have hv := hv.resolve_right (by split_ifs <;> linarith)
  have h_eq : (x.m : R) * 2 ^ x.e = (y.m : R) * 2 ^ y.e := by
    rw [zpow_add_one₀, zpow_add_one₀, zpow_sub₀, zpow_sub₀] at hv
    rw [← mul_assoc, ← mul_assoc, ← mul_div_assoc, ← mul_div_assoc] at hv
    rw [mul_eq_mul_right_iff] at hv
    rw [div_eq_inv_mul, div_eq_inv_mul] at hv
    rw [mul_eq_mul_left_iff] at hv
    norm_num at hv
    trivial
    all_goals norm_num
  have he_eq : x.e = y.e := by
    have ha : (x y : FiniteFp) → x.e < y.e →  ↑x.m * 2 ^ x.e = ↑y.m * (2 : R) ^ y.e → False := by
      intro x y h_lt h_eq
      have hx_re : x.m = y.m * (2 : R)^(y.e - x.e) := by
        rw [zpow_sub₀, ← mul_div_assoc, div_eq_inv_mul, mul_comm]
        symm
        apply (mul_inv_eq_iff_eq_mul₀ ?_).mpr
        symm
        exact h_eq
        linearize
        norm_num
      have hx_re' : x.m = y.m * 2^((y.e - x.e).natAbs) := by
        rw [← zpow_natAbs_nonneg_eq_zpow] at hx_re
        exact_mod_cast hx_re
        norm_num
        linarith
      have hx_too_large : 2^FloatFormat.prec ≤ x.m := by
        have hy_normal : _root_.isNormal y.m := by
          apply valid_min_exp_lt_imp_isNormal
          linarith [x.valid.left]
        calc 2^FloatFormat.prec
          _ = 2^(FloatFormat.prec - 1 + 1) := by rw [Nat.sub_add_cancel (by fomega)]
          _ = 2^(FloatFormat.prec - 1) * 2 := by rw [Nat.pow_add_one]
          _ ≤ y.m * 2 := by omega
          _ ≤ y.m * 2^((y.e - x.e).natAbs) := by
            gcongr
            apply le_self_pow₀ (by norm_num) (by omega)
          _ = x.m := by omega
      linarith [x.valid.right.right.left]

    rcases lt_trichotomy x.e y.e with h_lt | h_eq | h_gt
    · exfalso
      apply ha x y h_lt h_eq
    · trivial
    · exfalso
      apply ha y x h_gt h_eq.symm

  have hm : x.m = y.m := by
    rw [he_eq, mul_eq_mul_right_iff] at h_eq
    exact_mod_cast Or.resolve_right h_eq (by simp [zpow_ne_zero])

  split_ands <;> trivial

/-- If two finite floats have the same value, then they have the same sign as long as they are non-zero. -/
theorem sign_eq_of_toVal_eq [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} (hnz : ¬x.isZero ∨ ¬y.isZero) (hv : x.toVal (R := R) = y.toVal (R := R)) : x.s = y.s := by
  by_contra hs
  unfold isZero at hnz
  cases' hnz with xnz ynz
  · have hxm_pos : 0 < toVal_mag x (R := R):= by
      apply toVal_mag_pos
      omega
    rw [toVal_mag, FloatFormat.radix_val_eq_two] at hxm_pos
    norm_num at hxm_pos
    if hx : x.s = true then
      have hy : y.s = false := by grind
      simp [toVal, sign', hx, hy, FloatFormat.radix_val_eq_two] at hv
      have hj := toVal_mag_nonneg' R y
      linarith
    else
      have hy : y.s = true := by grind
      simp [toVal, sign', hx, hy, FloatFormat.radix_val_eq_two] at hv
      have hj := toVal_mag_nonneg' R y
      linarith
  · have hym_pos : 0 < toVal_mag y (R := R):= by
      apply toVal_mag_pos
      omega
    rw [toVal_mag, FloatFormat.radix_val_eq_two] at hym_pos
    norm_num at hym_pos
    if hx : x.s = true then
      have hy : y.s = false := by grind
      simp [toVal, sign', hx, hy, FloatFormat.radix_val_eq_two] at hv
      have hj := toVal_mag_nonneg' R x
      linarith
    else
      have hy : y.s = true := by grind
      simp [toVal, sign', hx, hy, FloatFormat.radix_val_eq_two] at hv
      have hj := toVal_mag_nonneg' R x
      linarith

/-- Version of `eq_of_toVal_eq` that simply requires that the inputs are non-zero -/
theorem eq_of_toVal_eq' [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} (hnz : ¬x.isZero ∨ ¬y.isZero) : x.toVal (R := R) = y.toVal (R := R) → x = y := by
  intro hv
  apply eq_of_toVal_eq ?_ hv
  -- Now we have to prove that the signs are equal
  -- unfold isZero at xnz ynz
  unfold toVal sign' at hv
  rw [FloatFormat.radix_val_eq_two] at hv
  apply sign_eq_of_toVal_eq hnz hv

theorem imp_toVal_eq [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x = y → x.toVal (R := R) = y.toVal := by
  intro hxy
  unfold toVal sign'
  rw [FloatFormat.radix_val_eq_two]
  rw [eq_def] at hxy
  simp_all

/-- toVal is injective, except for 0 and -0 -/
theorem imp_toVal_ne [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x ≠ y → (¬x.isZero ∨ ¬y.isZero) → x.toVal (R := R) ≠ y.toVal := by
  intro hxy hnz
  norm_num at hxy
  rw [eq_def, not_and_or, not_and_or] at hxy
  intro hv
  have := eq_of_toVal_eq' hnz hv
  rw [this] at hxy
  grind

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
