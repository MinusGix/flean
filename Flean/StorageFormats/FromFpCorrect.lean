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

end StorageFp
