import Flean.StorageFormats.FromFp
import Flean.StorageFormats.Conversion
import Flean.StorageFormats.RoundRNEVerify
import Flean.Operations.RoundIntSig

/-!
# Correctness of fromFp

Links `StorageFp.fromFp` to the canonical rounding infrastructure by showing
that its output value equals the value produced by `roundIntSigM` (and hence
by `RMode.round`) in the target format.

## Strategy

1. Show `FiniteFp.toVal = intSigVal` (connects source value representations).
2. Show `fromFp` agrees with `roundIntSigM` at the value level when both
   produce finite results.
3. Use `roundIntSigM_correct` (via `RoundIntSigMSound`) to conclude that
   `fromFp` computes the correctly-rounded value.
-/

namespace StorageFp

/-!
## Source value = intSigVal

The real value represented by a `FiniteFp` is `sign' * m * 2^(e - prec + 1)`,
which equals `intSigVal fp.s fp.m (fp.e - prec + 1)` for nonzero `m`.
-/

section toVal_intSigVal

variable [FloatFormat] {R : Type*} [Field R]

/-- `FiniteFp.toVal` agrees with `intSigVal` for nonzero significands. -/
theorem finiteFp_toVal_eq_intSigVal (fp : FiniteFp) (_hm : fp.m ≠ 0) :
    fp.toVal (R := R) = intSigVal (R := R) fp.s fp.m (fp.e - FloatFormat.prec + 1) := by
  unfold FiniteFp.toVal FiniteFp.sign' intSigVal
  rw [FloatFormat.radix_val_eq_two]
  cases fp.s <;> simp

/-- `FiniteFp.toVal` agrees with `intSigVal` even for zero significands
    (both sides are zero). -/
theorem finiteFp_toVal_eq_intSigVal' (fp : FiniteFp) :
    fp.toVal (R := R) = intSigVal (R := R) fp.s fp.m (fp.e - FloatFormat.prec + 1) := by
  unfold FiniteFp.toVal FiniteFp.sign' intSigVal
  rw [FloatFormat.radix_val_eq_two]
  cases fp.s <;> simp

end toVal_intSigVal

/-!
## Field extraction for `ofFields`

Show that `ofFields f s e m` has the expected sign, exponent, and mantissa fields,
provided the field values are in range.
-/

section ofFields_fields

variable {f : StorageFormat}

-- Helper: the zero-extended allOnes mask has the expected toNat
private theorem zeroExtend_allOnes_toNat (n m : Nat) (h : n ≤ m) :
    ((BitVec.allOnes n).zeroExtend m).toNat = 2 ^ n - 1 := by
  simp [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_allOnes]
  apply Nat.mod_eq_of_lt
  have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h
  have := Nat.two_pow_pos n; omega

private theorem manBits_le_bitSize (f : StorageFormat) : f.manBits ≤ f.bitSize := by
  unfold StorageFormat.bitSize; omega

private theorem expBits_le_bitSize (f : StorageFormat) : f.expBits ≤ f.bitSize := by
  unfold StorageFormat.bitSize; omega

-- The packed value fits in bitSize bits
private theorem packed_lt (f : StorageFormat) (s : Bool) (e m : Nat)
    (hm : m < 2 ^ f.manBits) (he : e < 2 ^ f.expBits) :
    (if s = true ∧ f.hasSigned = true then 1 else 0) * 2 ^ (f.expBits + f.manBits) +
      e * 2 ^ f.manBits + m < 2 ^ f.bitSize := by
  have hmB := Nat.two_pow_pos f.manBits
  have hem : e * 2 ^ f.manBits + m < 2 ^ (f.expBits + f.manBits) := by
    have h1 : e * 2 ^ f.manBits + m < (e + 1) * 2 ^ f.manBits := by nlinarith
    have h2 : (e + 1) * 2 ^ f.manBits ≤ 2 ^ f.expBits * 2 ^ f.manBits :=
      Nat.mul_le_mul_right _ (by omega)
    rw [← Nat.pow_add] at h2; linarith
  rcases Bool.eq_false_or_eq_true f.hasSigned with hsig | hsig
  · -- Signed: sign part ≤ 1, packed < 2 * 2^(eB+mB) = 2^(eB+mB+1) = 2^bitSize
    have hsign : (if s = true ∧ f.hasSigned = true then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hle := Nat.mul_le_mul_right (2 ^ (f.expBits + f.manBits)) hsign
    have hbs : f.bitSize = 1 + f.expBits + f.manBits := by
      unfold StorageFormat.bitSize; simp [hsig]
    calc (if s = true ∧ f.hasSigned = true then 1 else 0) * 2 ^ (f.expBits + f.manBits) +
          e * 2 ^ f.manBits + m
        < 2 ^ (f.expBits + f.manBits) + 2 ^ (f.expBits + f.manBits) := by linarith
      _ = 2 ^ (f.expBits + f.manBits + 1) := by rw [pow_succ]; ring
      _ = 2 ^ f.bitSize := by congr 1; omega
  · -- Unsigned: sign part is 0, packed = e * 2^mB + m < 2^(eB+mB) = 2^bitSize
    have hbs : f.bitSize = f.expBits + f.manBits := by unfold StorageFormat.bitSize; simp [hsig]
    simp [hsig]; rw [hbs]; linarith

-- Extracting the low mB bits from packed gives m
private theorem packed_mod_man (a b c m mB : Nat) (hm : m < 2 ^ mB) :
    (a * 2 ^ (b + mB) + c * 2 ^ mB + m) % 2 ^ mB = m := by
  rw [show a * 2 ^ (b + mB) + c * 2 ^ mB + m = 2 ^ mB * (a * 2 ^ b + c) + m from by ring]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hm]

-- Dividing packed by 2^mB strips off the mantissa
private theorem packed_div_manBits (a e m mB eB : Nat) (hm : m < 2 ^ mB) :
    (a * 2 ^ (eB + mB) + e * 2 ^ mB + m) / 2 ^ mB = a * 2 ^ eB + e := by
  rw [show a * 2 ^ (eB + mB) + e * 2 ^ mB + m = 2 ^ mB * (a * 2 ^ eB + e) + m from by ring]
  rw [Nat.mul_add_div (Nat.two_pow_pos mB), Nat.div_eq_of_lt hm, Nat.add_zero]

/-- The mantissa field of `ofFields f s e m` is `m` when `m` and `e` are in range. -/
theorem ofFields_man (s : Bool) (e m : ℕ)
    (hm : m < 2 ^ f.manBits) (_he : e < 2 ^ f.expBits) :
    (ofFields f s e m).man = m := by
  unfold man ofFields
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [zeroExtend_allOnes_toNat f.manBits f.bitSize (manBits_le_bitSize f)]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (manBits_le_bitSize f))]
  split_ifs
  · exact packed_mod_man 1 f.expBits e m f.manBits hm
  · exact packed_mod_man 0 f.expBits e m f.manBits hm

/-- The exponent field of `ofFields f s e m` is `e` when `m` and `e` are in range. -/
theorem ofFields_exp (s : Bool) (e m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : e < 2 ^ f.expBits) :
    (ofFields f s e m).exp = e := by
  unfold exp ofFields
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
             Nat.shiftRight_eq_div_pow]
  rw [zeroExtend_allOnes_toNat f.expBits f.bitSize (expBits_le_bitSize f)]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod,
      Nat.mod_eq_of_lt (packed_lt f s e m hm he)]
  split_ifs
  · rw [packed_div_manBits 1 e m f.manBits f.expBits hm]
    rw [show 1 * 2 ^ f.expBits + e = 2 ^ f.expBits * 1 + e from by ring]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt he]
  · rw [packed_div_manBits 0 e m f.manBits f.expBits hm]
    simp [Nat.mod_eq_of_lt he]

/-- The sign of `ofFields f s e m` is `s` (for signed formats). -/
theorem ofFields_sign (s : Bool) (e m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : e < 2 ^ f.expBits)
    (hsigned : f.hasSigned = true) :
    (ofFields f s e m).sign = s := by
  unfold sign ofFields
  simp only [hsigned, ite_true]
  have hbs : f.bitSize = 1 + f.expBits + f.manBits := by
    unfold StorageFormat.bitSize; rw [hsigned]; simp
  show (BitVec.ofNat f.bitSize _).getMsbD 0 = s
  simp only [BitVec.getMsbD, BitVec.getLsbD_ofNat, hbs]
  simp only [show 1 + f.expBits + f.manBits - 1 - 0 = f.expBits + f.manBits from by omega,
             show f.expBits + f.manBits < 1 + f.expBits + f.manBits from by omega]
  simp only [decide_true, Bool.true_and]
  have hlow : e * 2 ^ f.manBits + m < 2 ^ (f.expBits + f.manBits) := by
    have h1 : e * 2 ^ f.manBits + m < (e + 1) * 2 ^ f.manBits := by nlinarith [Nat.two_pow_pos f.manBits]
    have h2 : (e + 1) * 2 ^ f.manBits ≤ 2 ^ f.expBits * 2 ^ f.manBits :=
      Nat.mul_le_mul_right _ (by omega)
    rw [← Nat.pow_add] at h2; linarith
  cases s <;> simp
  · exact Nat.testBit_lt_two_pow hlow
  · rw [show 2 ^ (f.expBits + f.manBits) + e * 2 ^ f.manBits + m =
        2 ^ (f.expBits + f.manBits) + (e * 2 ^ f.manBits + m) from by ring]
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlow]; rfl

end ofFields_fields

/-!
## Value of `ofFields`

Express `(ofFields f s e m).toVal` in terms of the field values, for both
normal (e > 0) and subnormal (e = 0) cases.
-/

section ofFields_toVal

variable {f : StorageFormat} {R : Type*} [Field R]

/-- `isExpZero` for `ofFields` reduces to whether `e = 0`. -/
theorem ofFields_isExpZero (s : Bool) (e m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : e < 2 ^ f.expBits) :
    (ofFields f s e m).isExpZero ↔ e = 0 := by
  unfold isExpZero; rw [ofFields_exp s e m hm he]

/-- The effective significand of `ofFields` when the exponent is zero (subnormal). -/
theorem ofFields_effectiveSignificand_zero (s : Bool) (m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : (0 : ℕ) < 2 ^ f.expBits) :
    (ofFields f s 0 m).effectiveSignificand = m := by
  unfold effectiveSignificand
  have : (ofFields f s 0 m).isExpZero := (ofFields_isExpZero s 0 m hm he).mpr rfl
  rw [if_pos this]; exact ofFields_man s 0 m hm he

/-- The effective significand of `ofFields` when the exponent is nonzero (normal). -/
theorem ofFields_effectiveSignificand_pos (s : Bool) (e m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : e < 2 ^ f.expBits) (he0 : 0 < e) :
    (ofFields f s e m).effectiveSignificand = 2 ^ f.manBits + m := by
  unfold effectiveSignificand
  have : ¬(ofFields f s e m).isExpZero := by
    rw [ofFields_isExpZero s e m hm he]; omega
  rw [if_neg this]; congr 1; exact ofFields_man s e m hm he

/-- The unbiased exponent of `ofFields` when the exponent is zero. -/
theorem ofFields_unbiasedExp_zero (s : Bool) (m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : (0 : ℕ) < 2 ^ f.expBits) :
    (ofFields f s 0 m).unbiasedExp = 1 - (f.bias : ℤ) := by
  unfold unbiasedExp
  have : (ofFields f s 0 m).isExpZero := (ofFields_isExpZero s 0 m hm he).mpr rfl
  rw [if_pos this]

/-- The unbiased exponent of `ofFields` when the exponent is nonzero. -/
theorem ofFields_unbiasedExp_pos (s : Bool) (e m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : e < 2 ^ f.expBits) (he0 : 0 < e) :
    (ofFields f s e m).unbiasedExp = (e : ℤ) - (f.bias : ℤ) := by
  unfold unbiasedExp
  have : ¬(ofFields f s e m).isExpZero := by
    rw [ofFields_isExpZero s e m hm he]; omega
  rw [if_neg this]; congr 1; exact_mod_cast ofFields_exp s e m hm he

/-- Value of a subnormal `ofFields` encoding:
    `toVal = intSigVal s m (1 - bias - manBits)`. -/
theorem ofFields_toVal_subnormal (s : Bool) (m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : (0 : ℕ) < 2 ^ f.expBits)
    (hsigned : f.hasSigned = true) :
    (ofFields f s 0 m).toVal (R := R) =
    intSigVal (R := R) s m (1 - (f.bias : ℤ) - (f.manBits : ℤ)) := by
  unfold toVal intSigVal signVal
  rw [ofFields_effectiveSignificand_zero s m hm he,
      ofFields_unbiasedExp_zero s m hm he,
      ofFields_sign s 0 m hm he hsigned]
  cases s <;> simp

/-- Value of a normal `ofFields` encoding:
    `toVal = intSigVal s (2^manBits + m) (e - bias - manBits)`. -/
theorem ofFields_toVal_normal (s : Bool) (e m : ℕ)
    (hm : m < 2 ^ f.manBits) (he : e < 2 ^ f.expBits) (he0 : 0 < e)
    (hsigned : f.hasSigned = true) :
    (ofFields f s e m).toVal (R := R) =
    intSigVal (R := R) s (2 ^ f.manBits + m) ((e : ℤ) - (f.bias : ℤ) - (f.manBits : ℤ)) := by
  unfold toVal intSigVal signVal
  rw [ofFields_effectiveSignificand_pos s e m hm he he0,
      ofFields_unbiasedExp_pos s e m hm he he0,
      ofFields_sign s e m hm he hsigned]
  cases s <;> simp

-- Unified: both normal and subnormal encode `intSigVal s final_m final_e_ulp`
-- Normal case: exp_field = (final_e_ulp + manBits + bias).toNat, man_field = final_m - 2^manBits
-- => toVal = intSigVal s (2^manBits + man_field) (exp_field - bias - manBits)
--         = intSigVal s final_m (final_e_ulp + manBits + bias - bias - manBits)
--         = intSigVal s final_m final_e_ulp

/-- The normal encoding `ofFields f s exp_field (final_m - 2^manBits)` has value
    `intSigVal s final_m final_e_ulp` when `exp_field = (final_e_ulp + manBits + bias).toNat`
    and `2^manBits ≤ final_m < 2^(manBits+1)`. -/
theorem ofFields_normal_intSigVal (s : Bool) (final_m : ℕ) (final_e_ulp : ℤ)
    (hm_lo : 2 ^ f.manBits ≤ final_m) (hm_hi : final_m < 2 ^ (f.manBits + 1))
    (he_pos : 0 < (final_e_ulp + (f.manBits : ℤ) + (f.bias : ℤ)).toNat)
    (he_lt : (final_e_ulp + (f.manBits : ℤ) + (f.bias : ℤ)).toNat < 2 ^ f.expBits)
    (he_nonneg : 0 ≤ final_e_ulp + (f.manBits : ℤ) + (f.bias : ℤ))
    (hsigned : f.hasSigned = true) :
    (ofFields f s (final_e_ulp + (f.manBits : ℤ) + (f.bias : ℤ)).toNat
      (final_m - 2 ^ f.manBits)).toVal (R := R) =
    intSigVal (R := R) s final_m final_e_ulp := by
  have hman : final_m - 2 ^ f.manBits < 2 ^ f.manBits := by omega
  rw [ofFields_toVal_normal s _ _ hman he_lt he_pos hsigned]
  congr 1
  · omega
  · rw [Int.toNat_of_nonneg he_nonneg]; ring

/-- The subnormal encoding `ofFields f s 0 final_m` has value
    `intSigVal s final_m (1 - bias - manBits)`. -/
theorem ofFields_subnormal_intSigVal (s : Bool) (final_m : ℕ)
    (hm : final_m < 2 ^ f.manBits)
    (he : (0 : ℕ) < 2 ^ f.expBits)
    (hsigned : f.hasSigned = true) :
    (ofFields f s 0 final_m).toVal (R := R) =
    intSigVal (R := R) s final_m (1 - (f.bias : ℤ) - (f.manBits : ℤ)) :=
  ofFields_toVal_subnormal s final_m hm he hsigned

end ofFields_toVal

/-!
## `fromFp` encoding value

Show that both the normal and subnormal encoding branches of `fromFp` produce
the value `intSigVal sign final_m final_e_ulp`, where `final_m` and `final_e_ulp`
are the post-carry-adjustment values computed in `fromFp`.

The key property: `final_m * 2^final_e_ulp = rounded_m * 2^e_ulp` holds because
the carry adjustment divides `m` by 2 and increments the exponent.
-/

section fromFp_value

variable {R : Type*} [Field R]

/-- When an even natural `m` is divided by 2 and the exponent is incremented,
    the `intSigVal` is preserved. -/
theorem intSigVal_div2_succ [CharZero R] (sign : Bool) (m : ℕ) (e : ℤ)
    (heven : 2 ∣ m) :
    intSigVal (R := R) sign (m / 2) (e + 1) =
    intSigVal (R := R) sign m e := by
  unfold intSigVal
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  have hdiv : (↑(m / 2) : R) = (↑m : R) / 2 := by
    rw [Nat.cast_div heven h2]; push_cast; ring
  rw [hdiv, zpow_add₀ h2, zpow_one]
  have cancel : ∀ (x : R), x / 2 * (2 ^ e * 2) = x * 2 ^ e := by
    intro x; rw [mul_comm (2 ^ e) 2, ← mul_assoc, div_mul_cancel₀ _ h2]
  cases sign <;> simp [cancel]

end fromFp_value

end StorageFp
