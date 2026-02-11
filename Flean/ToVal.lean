import Flean.Defs
import Flean.BoundedSymm

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
  -- Goal: 2 ^ (FloatFormat.prec.toNat - 1) * 2 ^ (-FloatFormat.prec + 1) = 1
  -- Convert nat pow to zpow
  rw [← zpow_natCast (G := R) 2 (FloatFormat.prec.toNat - 1)]
  -- Now both are zpow, combine exponents
  rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
  -- Simplify the exponent to 0
  have hprec := FloatFormat.valid_prec
  have h_prec_nat : (FloatFormat.prec.toNat : ℤ) = FloatFormat.prec :=
    Int.toNat_of_nonneg (by omega : 0 ≤ FloatFormat.prec)
  have h_toNat_ge : 1 ≤ FloatFormat.prec.toNat := by
    have : 2 ≤ FloatFormat.prec.toNat := (Int.le_toNat (by omega)).mpr (by omega)
    omega
  have h_exp_zero : (↑(FloatFormat.prec.toNat - 1) : ℤ) + (-FloatFormat.prec + 1) = 0 :=
    calc (↑(FloatFormat.prec.toNat - 1) : ℤ) + (-FloatFormat.prec + 1)
        = (FloatFormat.prec.toNat : ℤ) - 1 + (-FloatFormat.prec + 1) := by rw [Nat.cast_sub h_toNat_ge]; norm_num
      _ = FloatFormat.prec - 1 + (-FloatFormat.prec + 1) := by rw [h_prec_nat]
      _ = 0 := by ring
  simp only [h_exp_zero, add_zero, zpow_zero, mul_one]

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
    exact hv.resolve_right (zpow_ne_zero _ (by norm_num : (2 : R) ≠ 0))
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
      have hx_too_large : 2^FloatFormat.prec.toNat ≤ x.m := by
        have hy_normal : _root_.isNormal y.m := by
          apply valid_min_exp_lt_imp_isNormal
          linarith [x.valid.left]
        have hprec := FloatFormat.valid_prec
        calc 2^FloatFormat.prec.toNat
          _ = 2^((FloatFormat.prec - 1).toNat + 1) := by congr 1; omega
          _ = 2^(FloatFormat.prec - 1).toNat * 2 := by rw [Nat.pow_add_one]
          _ ≤ y.m * 2 := by
              have := hy_normal.left
              omega
          _ ≤ y.m * 2^((y.e - x.e).natAbs) := by
            gcongr
            apply le_self_pow₀ (by norm_num) (by omega)
          _ = x.m := by omega
      have := x.valid.right.right.left
      omega

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

/-- toVal is injective on non-negative-zero floats.
    The hypothesis excludes negative zero, which is the only case where
    two distinct floats can have the same toVal (since (+0).toVal = (-0).toVal = 0). -/
theorem toVal_injective [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp}
    (hx : x.s = false ∨ 0 < x.m) (hy : y.s = false ∨ 0 < y.m)
    (hv : x.toVal (R := R) = y.toVal (R := R)) : x = y := by
  by_cases hxm : 0 < x.m
  · -- x is nonzero, so ¬x.isZero
    exact eq_of_toVal_eq' (Or.inl (by unfold isZero; omega)) hv
  · by_cases hym : 0 < y.m
    · -- y is nonzero, so ¬y.isZero
      exact eq_of_toVal_eq' (Or.inr (by unfold isZero; omega)) hv
    · -- Both have m = 0
      push_neg at hxm hym
      have hxm0 : x.m = 0 := by omega
      have hym0 : y.m = 0 := by omega
      -- From hypotheses: s = false ∨ 0 < 0, so s = false
      have hxs : x.s = false := by rcases hx with hs | hm <;> [exact hs; omega]
      have hys : y.s = false := by rcases hy with hs | hm <;> [exact hs; omega]
      -- From validity: m = 0 → not normal → subnormal → e = min_exp
      have hxe : x.e = FloatFormat.min_exp := by
        have := x.valid.2.2.2
        rw [hxm0] at this
        exact isSubnormal.zero_iff.mp (this.resolve_left (by simp [_root_.isNormal]))
      have hye : y.e = FloatFormat.min_exp := by
        have := y.valid.2.2.2
        rw [hym0] at this
        exact isSubnormal.zero_iff.mp (this.resolve_left (by simp [_root_.isNormal]))
      rw [eq_def]
      exact ⟨by rw [hxs, hys], by rw [hxe, hye], by rw [hxm0, hym0]⟩

/-! ### Simplified toVal expressions -/

/-- For positive sign, `toVal` simplifies to `m * 2^(e - prec + 1)`. -/
theorem toVal_pos_eq [Field R] (x : FiniteFp) (hs : x.s = false) :
    toVal x (R := R) = (x.m : R) * (2 : R) ^ (x.e - FloatFormat.prec + 1) := by
  unfold toVal sign'
  rw [FloatFormat.radix_val_eq_two]
  simp [hs]

/-! ### Binade bounds -/

/-- Every positive finite float satisfies `toVal < 2^(e + 1)`. -/
theorem toVal_lt_zpow_succ [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (x : FiniteFp) (hs : x.s = false) :
    toVal x (R := R) < (2 : R) ^ (x.e + 1) := by
  rw [toVal_pos_eq x hs]
  calc (x.m : R) * (2 : R) ^ (x.e - FloatFormat.prec + 1)
      < (2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ (x.e - FloatFormat.prec + 1) := by
        exact mul_lt_mul_of_pos_right (by exact_mod_cast x.valid.2.2.1) (two_zpow_pos' _)
    _ = (2 : R) ^ (x.e + 1) := by
        rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, two_zpow_mul]
        congr 1; rw [FloatFormat.prec_toNat_eq]; ring

/-- A normal positive float satisfies `2^e ≤ toVal`. -/
theorem toVal_normal_lower [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (x : FiniteFp) (hs : x.s = false) (hn : _root_.isNormal x.m) :
    (2 : R) ^ x.e ≤ toVal x (R := R) := by
  rw [toVal_pos_eq x hs]
  calc (2 : R) ^ x.e
      = (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ (x.e - FloatFormat.prec + 1) := by
        rw [two_zpow_mul]; congr 1; ring
    _ ≤ (x.m : R) * (2 : R) ^ (x.e - FloatFormat.prec + 1) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (two_zpow_pos' _))
        calc (2 : R) ^ (FloatFormat.prec - 1)
            = (2 : R) ^ (FloatFormat.prec - 1).toNat := FloatFormat.pow_prec_sub_one_nat_int.symm
          _ ≤ (x.m : R) := by exact_mod_cast hn.1

def toRat (x : FiniteFp) : ℚ := x.toVal

noncomputable
def toReal (x : FiniteFp) : ℝ := x.toVal

end toVal

end FiniteFp

/-! ## Constructing a FiniteFp with a given value -/

section Construction

variable [FloatFormat]

/-- A positive integer `mag` with `0 < mag < 2^prec` at a valid exponent `e_base` in
    `[min_exp - prec + 1, max_exp - prec + 1]` is the value of some valid `FiniteFp`.

    Handles normalization: if `mag ≥ 2^(prec-1)` it's normal; otherwise we either
    left-shift to normalize or represent as subnormal at `min_exp`.
    Proof by strong induction on the distance from `e_base` to the minimum. -/
theorem exists_finiteFp_of_nat_mul_zpow {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (mag : ℕ) (e_base : ℤ)
    (hmag_pos : 0 < mag) (hmag_bound : mag < 2 ^ FloatFormat.prec.toNat)
    (he_lo : e_base ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_hi : e_base + FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, f.s = false ∧ (f.toVal : R) = (mag : R) * (2 : R) ^ e_base := by
  suffices h : ∀ (n : ℕ) (mag : ℕ) (e_base : ℤ),
      (e_base - (FloatFormat.min_exp - FloatFormat.prec + 1)).toNat = n →
      0 < mag → mag < 2 ^ FloatFormat.prec.toNat →
      e_base ≥ FloatFormat.min_exp - FloatFormat.prec + 1 →
      e_base + FloatFormat.prec - 1 ≤ FloatFormat.max_exp →
      ∃ f : FiniteFp, f.s = false ∧ (f.toVal : R) = (mag : R) * (2 : R) ^ e_base by
    exact h _ mag e_base rfl hmag_pos hmag_bound he_lo he_hi
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro mag e_base hn hmag_pos hmag_bound he_lo he_hi
    have hprec := FloatFormat.valid_prec
    set e_stored := e_base + FloatFormat.prec - 1 with e_stored_def
    by_cases hmag_normal : 2 ^ (FloatFormat.prec - 1).toNat ≤ mag
    · -- Case 1: mag ≥ 2^(prec-1) — already normal
      refine ⟨⟨false, e_stored, mag, ?_⟩, rfl, ?_⟩
      · refine ⟨by omega, by omega, hmag_bound, Or.inl ⟨hmag_normal, hmag_bound⟩⟩
      · show (⟨false, e_stored, mag, _⟩ : FiniteFp).toVal (R := R) = _
        unfold FiniteFp.toVal FiniteFp.sign'
        rw [FloatFormat.radix_val_eq_two]; simp; omega
    · -- Case 2: mag < 2^(prec-1) — needs normalization or subnormal
      push_neg at hmag_normal
      by_cases he_min : e_stored = FloatFormat.min_exp
      · -- Case 2a: Already at minimum exponent — subnormal
        refine ⟨⟨false, FloatFormat.min_exp, mag, ?_⟩, rfl, ?_⟩
        · refine ⟨le_refl _, FloatFormat.exp_order_le, ?_, Or.inr ⟨rfl, by omega⟩⟩
          calc mag < 2 ^ (FloatFormat.prec - 1).toNat := hmag_normal
            _ < 2 ^ FloatFormat.prec.toNat := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
        · show (⟨false, FloatFormat.min_exp, mag, _⟩ : FiniteFp).toVal (R := R) = _
          unfold FiniteFp.toVal FiniteFp.sign'
          rw [FloatFormat.radix_val_eq_two]; simp; omega
      · -- Case 2b: e_stored > min_exp — double mag and recurse
        have he_gt : e_stored > FloatFormat.min_exp := by omega
        have he_base_gt : e_base > FloatFormat.min_exp - FloatFormat.prec + 1 := by omega
        have h2mag_bound : 2 * mag < 2 ^ FloatFormat.prec.toNat := by
          have : 2 * 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ FloatFormat.prec.toNat := by
            rw [← pow_succ']; congr 1; omega
          omega
        have hmeasure : (e_base - 1 - (FloatFormat.min_exp - FloatFormat.prec + 1)).toNat < n := by
          rw [← hn]; omega
        obtain ⟨f, hfs, hfv⟩ := ih _ hmeasure (2 * mag) (e_base - 1) rfl
          (by omega) h2mag_bound (by omega) (by omega)
        refine ⟨f, hfs, ?_⟩
        rw [hfv]; push_cast
        rw [show (2 : R) * (mag : R) * (2 : R) ^ (e_base - 1) =
            (mag : R) * ((2 : R) ^ (1 : ℤ) * (2 : R) ^ (e_base - 1)) from by ring]
        rw [two_zpow_mul]; norm_num

end Construction

-- namespace InfFp

-- variable [FloatFormat]
-- variable {R : Type*} [Field R]

-- def toVal? (x : InfFp) : Option R :=
--   match x with
--   | .finite x => some (FiniteFp.toVal x)
--   | .infinite _ => none

-- def toRat? (x : InfFp) : Option ℚ := toVal? x

-- abbrev Extended (R : Type*) := WithBot (WithTop R)

-- def toVal (x : InfFp) : Extended R :=
--   match x with
--   | .finite x => FiniteFp.toVal (R := R) x
--   | .infinite b => if b then ⊤ else ⊥

-- def toVal_mag (x : InfFp) : Extended R :=
--   match x with
--   | .finite x => FiniteFp.toVal_mag (R := R) x
--   | .infinite _ => ⊤

-- theorem toVal_mag_nonneg [LinearOrder R] [IsStrictOrderedRing R] [BoundedOrder (Extended R)] (x : InfFp) : 0 ≤ toVal_mag (R := R) x :=
--   match x with
--   | .finite x => by simp [toVal_mag, FiniteFp.toVal_mag_nonneg x]
--   | .infinite b => by simp [toVal_mag]

-- TODO: this needs enough of a notion of how R and Extended R are related to make sense
-- theorem toVal_eq_sign_mul_mag [LinearOrder R] [IsStrictOrderedRing R] [Neg (Extended R)] [BoundedSymm (Extended R)]
-- -- [Ring (Extended R)] [LinearOrder (Extended R)] [IsStrictOrderedRing (Extended R)]
-- (x : InfFp) : toVal (R := R) x = (sign' (R := (R)) x) * (toVal_mag (R := R) x) := by
--   -- simp [FiniteFp.toVal_eq_sign_mul_mag, toVal, toVal_mag, sign', FiniteFp.sign']
--   unfold toVal_mag toVal sign'
--   match x with
--   | finite f =>
--     norm_num
--     rw [FiniteFp.toVal_eq_sign_mul_mag]
--     push_cast
--     rfl
--   | infinite b =>
--     norm_num
--     split_ifs
--     norm_num
--     have j := BoundedSymm.top_eq_neg_bot (R := Extended R)
--     rw [j]
--     norm_num
--     symm

    -- apply WithBot.coe_add_eq_bot_iff.mpr
    -- rw [WithBot.coe_one]
    -- rw [← WithBot.coe_top, ← WithBot.coe_mul]
    -- rw [j]
    -- rw [← WithBot.coe_add]
    -- rw [WithBot.coe_add]





    -- have h : (-(1 : WithTop R)) = 0 - 1 := by simp_all only [Bool.not_eq_true, zero_sub]
    -- rw [h]

    -- rw [← WithBot.coe_add]




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
