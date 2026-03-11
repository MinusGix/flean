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

/-- `FiniteFp.toVal` agrees with `intSigVal` (works for both zero and nonzero significands). -/
theorem finiteFp_toVal_eq_intSigVal (fp : FiniteFp) :
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

/-- Left-shifting the significand and decrementing the exponent preserves `intSigVal`. -/
theorem intSigVal_mul_pow2 [CharZero R] (sign : Bool) (m k : ℕ) (e : ℤ) :
    intSigVal (R := R) sign (m * 2 ^ k) (e - (k : ℤ)) =
    intSigVal (R := R) sign m e := by
  unfold intSigVal
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  push_cast
  rw [zpow_sub₀ h2, zpow_natCast]
  cases sign <;> simp <;> field_simp

/-- `roundRNE` bound: if `mag < 2^(k + shift)`, then `roundRNE mag shift ≤ 2^k`. -/
theorem roundRNE_bound (mag shift k : ℕ) (h : mag < 2 ^ (k + shift)) :
    roundRNE mag shift ≤ 2 ^ k := by
  have hq : mag / 2 ^ shift < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)]; rwa [← Nat.pow_add]
  have := roundRNE_le mag shift; omega

-- Bridge: Nat.log 2 = Nat.log2 (so fromFp and roundIntSig use the same MSB)
theorem nat_log2_eq_log_two (m : ℕ) : Nat.log 2 m = Nat.log2 m :=
  Nat.log2_eq_log_two.symm

/-- `roundRNE` matches `roundIntSigM`'s rounding step when `shouldRoundUp`
    implements `policyShouldRoundUp .nearestEven`. -/
theorem roundRNE_eq_shouldRoundUp [ff : FloatFormat] [inst_exec : RModeExec]
    (mag shift : ℕ) (hshift : 0 < shift) (sign : Bool)
    (h_rne : ∀ s q r sh,
      RModeExec.shouldRoundUp s q r sh =
      policyShouldRoundUp .nearestEven s q r sh) :
    roundRNE mag shift =
    (if RModeExec.shouldRoundUp sign (mag / 2 ^ shift) (mag % 2 ^ shift) shift
     then mag / 2 ^ shift + 1
     else mag / 2 ^ shift) := by
  rw [roundRNE_eq_policyShouldRoundUp mag shift hshift]
  simp only
  rw [h_rne sign, ← policyShouldRoundUp_nearestEven_sign_indep false sign]

end fromFp_value

/-!
## Parameter correspondence

Show that `fromFp`'s parameters (from `StorageFormat`) match `roundIntSig`'s
parameters (from `FloatFormat`) when using `f.toFloatFormat`.
-/

section parameter_correspondence

variable (f : StorageFormat) (h_prec : f.manBits ≥ 1) (h_bias : f.bias ≥ 1)
    (h_exp : f.maxExpField > f.bias)

-- In the target FloatFormat:
-- prec = manBits + 1
-- min_exp = 1 - bias
-- max_exp = maxExpField - bias

theorem target_prec_eq :
    @FloatFormat.prec (f.toFloatFormat h_prec h_bias h_exp) = (f.manBits : ℤ) + 1 := rfl

theorem target_min_exp_eq :
    @FloatFormat.min_exp (f.toFloatFormat h_prec h_bias h_exp) = 1 - (f.bias : ℤ) := rfl

theorem target_max_exp_eq :
    @FloatFormat.max_exp (f.toFloatFormat h_prec h_bias h_exp) = (f.maxExpField : ℤ) - (f.bias : ℤ) := rfl

-- e_ulp_subnormal in fromFp = min_exp - prec + 1 in roundIntSig
theorem e_ulp_subnormal_eq :
    1 - (f.bias : ℤ) - (f.manBits : ℤ) =
    @FloatFormat.min_exp (f.toFloatFormat h_prec h_bias h_exp) -
    @FloatFormat.prec (f.toFloatFormat h_prec h_bias h_exp) + 1 := by
  simp [target_prec_eq, target_min_exp_eq]; ring

-- e_ulp_normal in fromFp = e_base + bits - prec in roundIntSig
-- (when using Nat.log 2 = Nat.log2)
theorem e_ulp_normal_eq (e_base : ℤ) (mag : ℕ) :
    e_base + (Nat.log 2 mag : ℤ) - (f.manBits : ℤ) =
    e_base + ((Nat.log2 mag + 1 : ℕ) : ℤ) -
    @FloatFormat.prec (f.toFloatFormat h_prec h_bias h_exp) := by
  simp [target_prec_eq, nat_log2_eq_log_two]; ring

end parameter_correspondence

/-!
## Correctness of `fromFp`: output value = `intSigVal`

When `fromFp` produces a non-overflowing result, its value equals
`intSigVal sign m_final e_ulp_final` where `(m_final, e_ulp_final, false)`
is the output of `roundSigCore`.

The proof strategy:
1. `fromFp` calls `roundSigCore` and (when no overflow) passes the result to
   `encodeRounded`.
2. `encodeRounded` produces `ofFields` (subnormal or normal encoding).
3. `ofFields.toVal = intSigVal` by the existing encoding lemmas.
4. For the subnormal case, we need `e_ulp_final = 1 - bias - manBits`,
   which follows from the structure of `roundSigCore`: if the normal branch
   had dominated the max, the significand would be ≥ 2^(prec-1).
-/

section main_theorem

variable [inst : FloatFormat] {R : Type*} [Field R]

omit inst in
/-- In the exact branch of `roundSigCore`, the left-shifted significand is < 2^prec. -/
private theorem exact_shift_lt (mag bits prec : ℕ) (shift : ℤ)
    (hmag_lt : mag < 2 ^ bits) (h_shift_le : shift ≤ 0)
    (h_shift_ge : shift ≥ ↑bits - ↑prec) :
    mag * 2 ^ (-shift).toNat < 2 ^ prec := by
  have h_nn : 0 ≤ -shift := by omega
  have hk_cast : ↑((-shift).toNat) = -shift := Int.toNat_of_nonneg h_nn
  have hsum : bits + (-shift).toNat ≤ prec := by omega
  calc mag * 2 ^ (-shift).toNat
      < 2 ^ bits * 2 ^ (-shift).toNat :=
        Nat.mul_lt_mul_of_pos_right hmag_lt (Nat.two_pow_pos _)
    _ = 2 ^ (bits + (-shift).toNat) := by rw [← Nat.pow_add]
    _ ≤ 2 ^ prec := Nat.pow_le_pow_right (by norm_num) hsum

omit inst in
/-- In the rounding branch of `roundSigCore`, the right-shifted significand is < 2^prec. -/
private theorem round_shift_lt (mag bits prec : ℕ) (shift : ℤ)
    (hmag_lt : mag < 2 ^ bits) (h_shift_gt : shift > 0)
    (h_shift_ge : shift ≥ ↑bits - ↑prec) :
    mag / 2 ^ shift.toNat < 2 ^ prec := by
  have h_nn : 0 ≤ shift := by omega
  have hk_cast : (↑shift.toNat : ℤ) = shift := Int.toNat_of_nonneg h_nn
  have hle : bits ≤ prec + shift.toNat := by omega
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  calc mag < 2 ^ bits := hmag_lt
    _ ≤ 2 ^ (prec + shift.toNat) := Nat.pow_le_pow_right (by norm_num) hle
    _ = 2 ^ prec * 2 ^ shift.toNat := by rw [← Nat.pow_add]

omit inst in
-- When mag ≥ 2^(bits-1) and we multiply by 2^(prec-bits), result ≥ 2^(prec-1).
private theorem mul_pow2_ge_of_log2 {mag bits_nat prec : ℕ}
    (hmag_ge : 2 ^ (bits_nat - 1) ≤ mag) (hbits_le : bits_nat ≤ prec)
    (hbits_pos : bits_nat ≥ 1) :
    mag * 2 ^ (prec - bits_nat) ≥ 2 ^ (prec - 1) := by
  have hsum : bits_nat - 1 + (prec - bits_nat) = prec - 1 := by omega
  calc 2 ^ (prec - 1)
      = 2 ^ (bits_nat - 1 + (prec - bits_nat)) := by rw [hsum]
    _ = 2 ^ (bits_nat - 1) * 2 ^ (prec - bits_nat) := by rw [Nat.pow_add]
    _ ≤ mag * 2 ^ (prec - bits_nat) := Nat.mul_le_mul_right _ hmag_ge

omit inst in
-- When mag ≥ 2^(bits-1) and bits > prec, then mag/2^(bits-prec) ≥ 2^(prec-1).
private theorem div_pow2_ge_of_log2 {mag bits_nat prec : ℕ}
    (hmag_ge : 2 ^ (bits_nat - 1) ≤ mag) (hbits_gt : bits_nat > prec) (hprec : prec ≥ 1) :
    mag / 2 ^ (bits_nat - prec) ≥ 2 ^ (prec - 1) := by
  have hexp_sum : prec - 1 + (bits_nat - prec) = bits_nat - 1 := by omega
  have hmul_le : 2 ^ (prec - 1) * 2 ^ (bits_nat - prec) ≤ mag := by
    calc 2 ^ (prec - 1) * 2 ^ (bits_nat - prec)
        = 2 ^ (prec - 1 + (bits_nat - prec)) := by rw [Nat.pow_add]
      _ = 2 ^ (bits_nat - 1) := by rw [hexp_sum]
      _ ≤ mag := hmag_ge
  exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr hmul_le

omit inst in
/-- In the exact branch with ℤ shift, the left-shifted significand is ≥ 2^(prec-1). -/
private theorem exact_shift_ge (mag bits prec : ℕ) (shift : ℤ)
    (hmag_ge : 2 ^ (bits - 1) ≤ mag) (h_shift_le : shift ≤ 0)
    (h_shift_eq : shift = ↑bits - ↑prec) (hbits_pos : bits ≥ 1) :
    mag * 2 ^ (-shift).toNat ≥ 2 ^ (prec - 1) := by
  have hk_cast : (↑((-shift).toNat) : ℤ) = -shift := Int.toNat_of_nonneg (by omega)
  have hk_eq : (-shift).toNat = prec - bits := by omega
  rw [hk_eq]
  exact mul_pow2_ge_of_log2 hmag_ge (by omega) hbits_pos

omit inst in
/-- In the rounding branch with ℤ shift, the right-shifted significand is ≥ 2^(prec-1). -/
private theorem round_shift_ge (mag bits prec : ℕ) (shift : ℤ)
    (hmag_ge : 2 ^ (bits - 1) ≤ mag) (h_shift_gt : shift > 0)
    (h_shift_eq : shift = ↑bits - ↑prec) (hprec : prec ≥ 1) :
    mag / 2 ^ shift.toNat ≥ 2 ^ (prec - 1) := by
  have hk_cast : (↑shift.toNat : ℤ) = shift := Int.toNat_of_nonneg (by omega)
  have hk_eq : shift.toNat = bits - prec := by omega
  rw [hk_eq]
  exact div_pow2_ge_of_log2 hmag_ge (by omega) hprec

omit inst in
/-- When `roundSigCore` produces a nonzero subnormal-sized significand (< 2^(prec-1)),
    the ULP exponent must equal the subnormal minimum: `min_exp - prec + 1`.

    Core argument: if the normal branch had dominated the max, the significand
    would be ≥ 2^(prec-1), contradicting the hypothesis. -/
private theorem roundSigCore_subnormal_e_ulp
    (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (prec : ℕ) (min_exp max_exp : ℤ)
    (shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool)
    (hprec : prec ≥ 2) (hmag : mag ≠ 0)
    (hov : (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).2.2 = false)
    (hm_sub : (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).1 < 2 ^ (prec - 1))
    (hm_pos : (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).1 ≠ 0) :
    (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).2.1 =
    min_exp - ↑prec + 1 := by
  have hmag_ge : 2 ^ (Nat.log2 mag + 1 - 1) ≤ mag := Nat.log2_self_le hmag
  -- Unfold roundSigCore, reduce let-bindings
  unfold roundSigCore at hov hm_sub hm_pos ⊢
  simp only at hov hm_sub hm_pos ⊢
  -- Case split on the max (subnormal vs normal e_ulp)
  by_cases h_max : e_base + ↑(Nat.log2 mag + 1) - ↑prec ≤ min_exp - ↑prec + 1
  · -- Subnormal: e_ulp = min_exp - prec + 1
    simp only [show max (e_base + ↑(Nat.log2 mag + 1) - ↑prec) (min_exp - ↑prec + 1) =
      min_exp - ↑prec + 1 from max_eq_right h_max] at hov hm_sub hm_pos ⊢
    split_ifs at hov hm_sub hm_pos ⊢ <;> (try exact absurd rfl hov) <;>
      simp only [not_le, not_lt] at *
    all_goals (
      first
      | omega
      | (push_cast at *; omega)
      | (have h2prec : 2 ^ prec = 2 * 2 ^ (prec - 1) := by
           conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one,
             Nat.sub_add_cancel (by omega : prec ≥ 1)]
         omega)
      | (have h2prec : 2 ^ prec = 2 * 2 ^ (prec - 1) := by
           conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one,
             Nat.sub_add_cancel (by omega : prec ≥ 1)]
         push_cast at *; omega))
  · -- Normal: e_ulp = e_base + bits - prec.
    -- In this case, the result's significand ≥ 2^(prec-1), contradicting hm_sub.
    push_neg at h_max
    simp only [show max (e_base + ↑(Nat.log2 mag + 1) - ↑prec) (min_exp - ↑prec + 1) =
      e_base + ↑(Nat.log2 mag + 1) - ↑prec from max_eq_left (le_of_lt h_max)]
      at hov hm_sub hm_pos ⊢
    -- Simplify shift: e_base + bits - prec - e_base = bits - prec
    simp only [show e_base + ↑(Nat.log2 mag + 1) - ↑prec - e_base =
      ↑(Nat.log2 mag + 1) - ↑prec from by ring] at hov hm_sub hm_pos ⊢
    have h2prec : 2 ^ prec = 2 * 2 ^ (prec - 1) := by
      conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : prec ≥ 1)]
    have hprec1_pos : 2 ^ (prec - 1) ≥ 1 := Nat.one_le_two_pow
    split_ifs at hov hm_sub hm_pos ⊢ <;> (try exact absurd rfl hov)
    all_goals simp only [not_le, not_lt] at *
    all_goals (
      first
      | omega
      | -- Exact: significand = mag * 2^k ≥ 2^(prec-1)
        (have := exact_shift_ge mag (Nat.log2 mag + 1) prec
            (↑(Nat.log2 mag + 1) - ↑prec) hmag_ge (by omega) rfl (by omega)
         omega)
      | -- Rounding: significand ≥ mag / 2^k ≥ 2^(prec-1)
        (have := round_shift_ge mag (Nat.log2 mag + 1) prec
            (↑(Nat.log2 mag + 1) - ↑prec) hmag_ge (by omega) rfl (by omega)
         omega))

omit inst in
/-- `roundSigCore` output significand is bounded by `2^prec`. -/
private theorem roundSigCore_m_bound
    (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (prec : ℕ) (min_exp max_exp : ℤ)
    (shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool)
    (hmag : mag ≠ 0) (hprec : prec ≥ 1)
    (hov : (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).2.2 = false) :
    (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).1 < 2 ^ prec := by
  have hmag_lt : mag < 2 ^ (Nat.log2 mag + 1) :=
    (Nat.log2_lt hmag).mp (Nat.lt_succ_of_le (le_refl _))
  have h2prec : 2 ^ prec = 2 * 2 ^ (prec - 1) := by
    conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one,
      Nat.sub_add_cancel (by omega : prec ≥ 1)]
  have hprec1_pos : 2 ^ (prec - 1) ≥ 1 := Nat.one_le_two_pow
  unfold roundSigCore at hov ⊢
  simp only at hov ⊢
  -- Resolve the max before split_ifs so shift expressions become concrete.
  by_cases h_max : e_base + ↑(Nat.log2 mag + 1) - ↑prec ≤ min_exp - ↑prec + 1
  · -- Subnormal: e_ulp = min_exp - prec + 1
    simp only [show max (e_base + ↑(Nat.log2 mag + 1) - ↑prec) (min_exp - ↑prec + 1) =
      min_exp - ↑prec + 1 from max_eq_right h_max] at hov ⊢
    have h_shift_ge : min_exp - ↑prec + 1 - e_base ≥ ↑(Nat.log2 mag + 1) - ↑prec := by omega
    split_ifs at hov ⊢ <;> (try exact absurd rfl hov) <;>
      simp only [not_le, not_lt] at *
    all_goals (
      first
      | omega
      | (have := exact_shift_lt mag (Nat.log2 mag + 1) prec
            (min_exp - ↑prec + 1 - e_base) hmag_lt (by omega) h_shift_ge
         omega)
      | (have := round_shift_lt mag (Nat.log2 mag + 1) prec
            (min_exp - ↑prec + 1 - e_base) hmag_lt (by omega) h_shift_ge
         omega))
  · -- Normal: e_ulp = e_base + bits - prec
    push_neg at h_max
    simp only [show max (e_base + ↑(Nat.log2 mag + 1) - ↑prec) (min_exp - ↑prec + 1) =
      e_base + ↑(Nat.log2 mag + 1) - ↑prec from max_eq_left (le_of_lt h_max)] at hov ⊢
    simp only [show e_base + ↑(Nat.log2 mag + 1) - ↑prec - e_base =
      ↑(Nat.log2 mag + 1) - ↑prec from by ring] at hov ⊢
    have h_shift_ge : (↑(Nat.log2 mag + 1) : ℤ) - ↑prec ≥ ↑(Nat.log2 mag + 1) - ↑prec := le_refl _
    split_ifs at hov ⊢ <;> (try exact absurd rfl hov) <;>
      simp only [not_le, not_lt] at *
    all_goals (
      first
      | omega
      | (have := exact_shift_lt mag (Nat.log2 mag + 1) prec
            (↑(Nat.log2 mag + 1) - ↑prec) hmag_lt (by omega) h_shift_ge
         omega)
      | (have := round_shift_lt mag (Nat.log2 mag + 1) prec
            (↑(Nat.log2 mag + 1) - ↑prec) hmag_lt (by omega) h_shift_ge
         omega))

omit inst in
/-- `roundSigCore` output ULP exponent is ≥ `min_exp - prec + 1`. -/
private theorem roundSigCore_e_ulp_ge
    (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (prec : ℕ) (min_exp max_exp : ℤ)
    (shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool)
    (hov : (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).2.2 = false) :
    (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).2.1 ≥
    min_exp - ↑prec + 1 := by
  unfold roundSigCore at hov ⊢
  simp only at hov ⊢
  split_ifs at hov ⊢ <;> (try exact absurd rfl hov) <;>
    simp only [not_le, not_lt] at * <;> omega

omit inst in
/-- When `roundSigCore` does not overflow, the stored exponent ≤ `max_exp`. -/
private theorem roundSigCore_e_stored_le
    (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (prec : ℕ) (min_exp max_exp : ℤ)
    (shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool)
    (hov : (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).2.2 = false) :
    (roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp).2.1 + ↑prec - 1 ≤
    max_exp := by
  unfold roundSigCore at hov ⊢
  simp only at hov ⊢
  split_ifs at hov ⊢ <;> (try exact absurd rfl hov) <;>
    simp only [not_le, not_lt] at * <;> omega

omit inst in
/-- `encodeRounded` with a subnormal result produces `intSigVal`. -/
private theorem encodeRounded_toVal_subnormal
    {f : StorageFormat} (policy : StorageOverflowPolicy) (sign : Bool)
    (m : ℕ) (e_ulp : ℤ)
    (hm_pos : m ≠ 0) (hm_sub : m < 2 ^ f.manBits)
    (he_ulp : e_ulp = 1 - (f.bias : ℤ) - (f.manBits : ℤ))
    (hsigned : f.hasSigned = true) :
    (encodeRounded f policy sign m e_ulp).toVal (R := R) =
    intSigVal (R := R) sign m e_ulp := by
  unfold encodeRounded
  simp only [show ¬(m = 0) from hm_pos, ↓reduceIte, hm_sub]
  rw [ofFields_toVal_subnormal sign m hm_sub (Nat.two_pow_pos _) hsigned, he_ulp]

omit inst in
/-- `encodeRounded` with a normal result produces `intSigVal`. -/
private theorem encodeRounded_toVal_normal
    {f : StorageFormat} (policy : StorageOverflowPolicy) (sign : Bool)
    (m : ℕ) (e_ulp : ℤ)
    (hm_lo : 2 ^ f.manBits ≤ m) (hm_hi : m < 2 ^ (f.manBits + 1))
    (he_nonneg : 0 ≤ e_ulp + (f.manBits : ℤ) + (f.bias : ℤ))
    (he_pos : 0 < (e_ulp + (f.manBits : ℤ) + (f.bias : ℤ)).toNat)
    (he_lt : (e_ulp + (f.manBits : ℤ) + (f.bias : ℤ)).toNat < 2 ^ f.expBits)
    (h_no_nan : f.maxManFieldAtMaxExp ≥ 2 ^ f.manBits - 1)
    (hsigned : f.hasSigned = true) :
    (encodeRounded f policy sign m e_ulp).toVal (R := R) =
    intSigVal (R := R) sign m e_ulp := by
  unfold encodeRounded
  have hm_ne : m ≠ 0 := by omega
  have hm_not_sub : ¬(m < 2 ^ f.manBits) := by omega
  simp only [hm_ne, ↓reduceIte, hm_not_sub]
  -- NaN exclusion doesn't fire: man_field ≤ maxManFieldAtMaxExp
  have hman_field : ¬(m - 2 ^ f.manBits > f.maxManFieldAtMaxExp) := by omega
  -- The && condition: even if exp matches, man doesn't exceed
  split_ifs with h_nan
  · simp [Bool.and_eq_true, decide_eq_true_eq] at h_nan; omega
  · exact ofFields_normal_intSigVal sign m e_ulp hm_lo hm_hi he_pos he_lt he_nonneg hsigned

/-- When `fromFp` does not overflow, its output value equals `intSigVal sign m_final e_ulp_final`
    where `(m_final, e_ulp_final, false) = roundSigCore ...`.

    This is the core correctness theorem for `fromFp`, independent of `roundIntSigM`. -/
theorem fromFp_val_eq_intSigVal
    (f : StorageFormat) (policy : StorageOverflowPolicy) (fp : FiniteFp)
    (hsigned : f.hasSigned = true)
    (h_prec : f.manBits ≥ 1)
    (hm : fp.m ≠ 0)
    (h_no_ov : (roundSigCore fp.s fp.m (fp.e - inst.prec + 1) (f.manBits + 1)
        (1 - (f.bias : ℤ)) ((f.maxExpField : ℤ) - (f.bias : ℤ)) rneRoundUp).2.2 = false)
    (h_no_nan : f.maxManFieldAtMaxExp ≥ 2 ^ f.manBits - 1) :
    let rc := roundSigCore fp.s fp.m (fp.e - inst.prec + 1) (f.manBits + 1)
        (1 - (f.bias : ℤ)) ((f.maxExpField : ℤ) - (f.bias : ℤ)) rneRoundUp
    (fromFp f policy (Fp.finite fp)).toVal (R := R) =
    intSigVal (R := R) fp.s rc.1 rc.2.1 := by
  -- Abbreviate roundSigCore output
  set rc := roundSigCore fp.s fp.m (fp.e - inst.prec + 1) (f.manBits + 1)
      (1 - (f.bias : ℤ)) ((f.maxExpField : ℤ) - (f.bias : ℤ)) rneRoundUp with hrc_def
  set m_final := rc.1
  set e_ulp_final := rc.2.1
  -- fromFp with nonzero mag and no overflow = encodeRounded
  have h_fromFp : fromFp f policy (Fp.finite fp) =
      encodeRounded f policy fp.s m_final e_ulp_final := by
    unfold fromFp
    simp only [show ¬(fp.m = 0) from hm, ↓reduceIte]
    show (match rc with | (m, e, ov) => if ov then applyOverflow f policy fp.s
        else encodeRounded f policy fp.s m e) =
      encodeRounded f policy fp.s m_final e_ulp_final
    obtain ⟨m, e, ov⟩ := rc
    simp only [m_final, e_ulp_final] at h_no_ov ⊢
    simp [h_no_ov]
  rw [h_fromFp]
  -- Properties of roundSigCore output (all provable by unfolding)
  have hm_bound : m_final < 2 ^ (f.manBits + 1) :=
    roundSigCore_m_bound fp.s fp.m _ _ _ _ rneRoundUp hm (by omega) h_no_ov
  have he_ge : e_ulp_final ≥ 1 - (f.bias : ℤ) - (f.manBits : ℤ) := by
    have := roundSigCore_e_ulp_ge fp.s fp.m _ _ _ _ rneRoundUp h_no_ov
    convert this using 1; push_cast; ring
  have he_stored_le : e_ulp_final + (f.manBits : ℤ) ≤ (f.maxExpField : ℤ) - (f.bias : ℤ) := by
    have := roundSigCore_e_stored_le fp.s fp.m _ _ _ _ rneRoundUp h_no_ov
    -- e_stored = e_ulp + prec - 1 = e_ulp + (manBits+1) - 1 = e_ulp + manBits
    convert this using 1; push_cast; ring
  have he_exp_lt : (e_ulp_final + (f.manBits : ℤ) + (f.bias : ℤ)).toNat < 2 ^ f.expBits := by
    -- maxExpField < 2^expBits, and e_stored + bias ≤ maxExpField
    have : f.maxExpField < 2 ^ f.expBits := by
      unfold StorageFormat.maxExpField
      have := Nat.two_pow_pos f.expBits
      split_ifs <;> omega
    omega
  -- Case split on zero, subnormal, normal
  by_cases hm_zero : m_final = 0
  · -- Zero: both sides are 0
    show (encodeRounded f policy fp.s m_final e_ulp_final).toVal (R := R) =
         intSigVal (R := R) fp.s m_final e_ulp_final
    rw [hm_zero]
    have intSigVal_zero : intSigVal (R := R) fp.s 0 e_ulp_final = 0 := by
      unfold intSigVal; simp
    rw [intSigVal_zero]
    unfold encodeRounded
    simp only [↓reduceIte]
    -- For signed format, negZero = ofFields f true 0 0
    -- since bitSize - 1 = expBits + manBits
    have hbs : f.bitSize = 1 + f.expBits + f.manBits := by
      unfold StorageFormat.bitSize; rw [hsigned]; simp
    have negZero_eq : negZero f = ofFields f true 0 0 := by
      unfold negZero ofFields; simp [hsigned, hbs]
      show BitVec.ofNat f.bitSize (2 ^ (1 + f.expBits + f.manBits - 1)) =
           BitVec.ofNat f.bitSize (2 ^ (f.expBits + f.manBits))
      congr 2; omega
    cases fp.s
    · exact zero_toVal f
    · simp only [ite_true, negZero_eq,
        ofFields_toVal_subnormal true 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _) hsigned]
      unfold intSigVal; simp
  · by_cases hm_sub : m_final < 2 ^ f.manBits
    · -- Subnormal
      have he_sub : e_ulp_final = 1 - (f.bias : ℤ) - (f.manBits : ℤ) := by
        have := roundSigCore_subnormal_e_ulp fp.s fp.m (fp.e - inst.prec + 1)
          (f.manBits + 1) (1 - (f.bias : ℤ)) ((f.maxExpField : ℤ) - (f.bias : ℤ))
          rneRoundUp (by omega) hm h_no_ov hm_sub hm_zero
        convert this using 1; push_cast; ring
      exact encodeRounded_toVal_subnormal policy fp.s m_final e_ulp_final
        hm_zero hm_sub he_sub hsigned
    · -- Normal
      push_neg at hm_sub
      have he_nonneg : 0 ≤ e_ulp_final + (f.manBits : ℤ) + (f.bias : ℤ) := by omega
      have he_pos : 0 < (e_ulp_final + (f.manBits : ℤ) + (f.bias : ℤ)).toNat := by omega
      exact encodeRounded_toVal_normal policy fp.s m_final e_ulp_final
        hm_sub hm_bound he_nonneg he_pos he_exp_lt h_no_nan hsigned

end main_theorem

end StorageFp
