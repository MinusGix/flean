import Flean.IntegerEquivalence.Basic

/-! # FP ↔ Integer equivalence: literal XOR / AND forms for `fpNeg` / `fpAbs`

Phase 1 closure (literal bit-twiddle forms) of the FP ↔ Integer equivalence area.

`Basic.lean` shipped the `setSign`/`signFlip`/`signClear` workhorses with
their `Fp`-level bridges (`ofBits_signFlip_eq_neg`, `ofBits_signClear_eq_fpAbs`).
This file ships the *literal* hardware-targetable forms:

* `fpNeg b = ofBits ⟨b.b ^^^ signMask⟩`  — single XOR instruction.
* `fpAbs b = ofBits ⟨b.b &&& ~~~signMask⟩` — single AND instruction.

`signMask : BitVec bitSize` has only the top bit (sign bit) set.

These are pure reformulations of `signFlip`/`signClear` at the explicit
BitVec-operation level — no new applications, just the literal encoding
that downstream codegen / SIMD targeting can recognize. -/

namespace Fp.FloatBits

variable [FloatFormat]

/-- Bit-level sign mask: a `BitVec FloatFormat.bitSize` with only the top
(sign) bit set. Constructed via `mk'` to align with the encoding format. -/
def signMask : BitVec FloatFormat.bitSize :=
  (FloatBits.mk' (BitVec.ofBool true)
    (0 : BitVec FloatFormat.exponentBits)
    (0 : BitVec FloatFormat.significandBits)).b

/-- Generic helper: XOR commutes with the `BitVec.cast` from the
`signBits + expBits + sigBits` shape to `bitSize`. -/
private theorem cast_xor_distrib
    (x y : BitVec (FloatFormat.signBits + FloatFormat.exponentBits
      + FloatFormat.significandBits)) :
    BitVec.cast FloatFormat.bitSize_eq.symm x ^^^
        BitVec.cast FloatFormat.bitSize_eq.symm y
      = BitVec.cast FloatFormat.bitSize_eq.symm (x ^^^ y) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_cast]

/-- `signFlip` at the literal BitVec level: XOR with `signMask`. -/
theorem signFlip_b_eq_xor_signMask (b : FloatBits) :
    (signFlip b).b = b.b ^^^ signMask := by
  -- Express b in canonical mk' form, with sign as ofBool b.sign.
  have hsign_form : b.toBitsTriple.sign = BitVec.ofBool b.sign := by
    unfold FloatBits.sign
    rcases BitVec.one_or b.toBitsTriple.sign with h | h
    · rw [h]; rfl
    · rw [h]; rfl
  have hb : b = mk' (BitVec.ofBool b.sign) b.toBitsTriple.exponent
              b.toBitsTriple.significand := by
    rw [← hsign_form]
    exact appendToBitsTriple_eq b.toBitsTriple b rfl
  -- Unfold signFlip = setSign (!b.sign) b on LHS.
  unfold signFlip setSign
  -- Both LHS and RHS are now `mk' _ E T .b` form. Use mk' = cast (s ++ E ++ T).
  show (mk' (BitVec.ofBool !b.sign) b.toBitsTriple.exponent
            b.toBitsTriple.significand).b
        = b.b ^^^ signMask
  -- Express RHS via the canonical b form.
  conv_rhs => rw [hb]
  unfold mk' signMask
  simp only []
  unfold mk'
  simp only []
  -- Goal: cast h ((ofBool !b.sign) ++ E ++ T)
  --     = cast h ((ofBool b.sign) ++ E ++ T) ^^^ cast h ((ofBool true) ++ 0 ++ 0)
  rw [cast_xor_distrib]
  congr 1
  -- Goal: (ofBool !b.sign) ++ E ++ T = ((ofBool b.sign) ++ E ++ T) ^^^
  --                                    ((ofBool true) ++ 0 ++ 0)
  apply BitVec.eq_of_getElem_eq
  intro i hi
  -- Normalize sigBits ↔ prec.toNat - 1.
  have hsb_eq : FloatFormat.significandBits = FloatFormat.prec.toNat - 1 := by
    rw [FloatFormat.significandBits_eq]
    exact FloatFormat.prec_sub_one_toNat_eq_toNat_sub
  rw [hsb_eq] at hi
  simp only [BitVec.getElem_xor, BitVec.getElem_append]
  by_cases h1 : i < FloatFormat.prec.toNat - 1
  · simp [h1]
  · push_neg at h1
    by_cases h2 : i - (FloatFormat.prec.toNat - 1) < FloatFormat.exponentBits
    · simp [h2, Nat.not_lt.mpr h1]
    · push_neg at h2
      -- Top sign bit. h1 + h2 + hi pin i to the top.
      have hsb_one : FloatFormat.signBits = 1 := rfl
      have h_eq : i - (FloatFormat.prec.toNat - 1) - FloatFormat.exponentBits = 0 := by
        omega
      simp [Nat.not_lt.mpr h1, Nat.not_lt.mpr h2, h_eq]

/-- Generic helper: AND distributes over `BitVec.cast`. -/
private theorem cast_and_distrib
    (x y : BitVec (FloatFormat.signBits + FloatFormat.exponentBits
      + FloatFormat.significandBits)) :
    BitVec.cast FloatFormat.bitSize_eq.symm x &&&
        BitVec.cast FloatFormat.bitSize_eq.symm y
      = BitVec.cast FloatFormat.bitSize_eq.symm (x &&& y) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_cast]

/-- Generic helper: complement distributes over `BitVec.cast`. -/
private theorem cast_not_distrib
    (x : BitVec (FloatFormat.signBits + FloatFormat.exponentBits
      + FloatFormat.significandBits)) :
    ~~~ BitVec.cast FloatFormat.bitSize_eq.symm x
      = BitVec.cast FloatFormat.bitSize_eq.symm (~~~ x) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_cast]

/-- `signClear` at the literal BitVec level: AND with `~~~signMask`. -/
theorem signClear_b_eq_and_not_signMask (b : FloatBits) :
    (signClear b).b = b.b &&& (~~~ signMask) := by
  have hsign_form : b.toBitsTriple.sign = BitVec.ofBool b.sign := by
    unfold FloatBits.sign
    rcases BitVec.one_or b.toBitsTriple.sign with h | h
    · rw [h]; rfl
    · rw [h]; rfl
  have hb : b = mk' (BitVec.ofBool b.sign) b.toBitsTriple.exponent
              b.toBitsTriple.significand := by
    rw [← hsign_form]
    exact appendToBitsTriple_eq b.toBitsTriple b rfl
  unfold signClear setSign
  show (mk' (BitVec.ofBool false) b.toBitsTriple.exponent
            b.toBitsTriple.significand).b
        = b.b &&& (~~~ signMask)
  conv_rhs => rw [hb]
  unfold mk' signMask
  simp only []
  unfold mk'
  simp only []
  rw [cast_not_distrib, cast_and_distrib]
  congr 1
  -- Goal: (ofBool false) ++ E ++ T = ((ofBool b.sign) ++ E ++ T) &&&
  --                                  ~~~((ofBool true) ++ 0 ++ 0)
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hsb_eq : FloatFormat.significandBits = FloatFormat.prec.toNat - 1 := by
    rw [FloatFormat.significandBits_eq]
    exact FloatFormat.prec_sub_one_toNat_eq_toNat_sub
  rw [hsb_eq] at hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_append]
  by_cases h1 : i < FloatFormat.prec.toNat - 1
  · simp [h1]
  · push_neg at h1
    by_cases h2 : i - (FloatFormat.prec.toNat - 1) < FloatFormat.exponentBits
    · simp [h2, Nat.not_lt.mpr h1]
    · push_neg at h2
      have hsb_one : FloatFormat.signBits = 1 := rfl
      have h_eq : i - (FloatFormat.prec.toNat - 1) - FloatFormat.exponentBits = 0 := by
        omega
      simp [Nat.not_lt.mpr h1, Nat.not_lt.mpr h2, h_eq]

end Fp.FloatBits

/-! ## Headlines: literal XOR / AND ↔ `Fp.neg` / `Fp.fpAbs` -/

namespace Fp

/-- **`fpNeg` as a literal XOR with `signMask`.** For non-NaN inputs,
the FP negation operation is implemented at the bit level by a single XOR
with the sign mask. -/
theorem ofBits_xor_signMask_eq_neg [StdFloatFormat] (b : FloatBits)
    (hn : ¬b.isNaN) :
    ofBits ⟨b.b ^^^ FloatBits.signMask⟩ = -(ofBits b) := by
  have h_form : (⟨b.b ^^^ FloatBits.signMask⟩ : FloatBits) = FloatBits.signFlip b :=
    ((FloatBits.ext1 (FloatBits.signFlip b) (b.b ^^^ FloatBits.signMask)).mpr
      (FloatBits.signFlip_b_eq_xor_signMask b)).symm
  rw [h_form]
  exact ofBits_signFlip_eq_neg b hn

/-- **`fpAbs` as a literal AND with `~~~signMask`.** For non-NaN inputs,
the FP absolute-value operation is implemented at the bit level by a
single AND with the magnitude mask (sign bit cleared). -/
theorem ofBits_and_not_signMask_eq_fpAbs [StdFloatFormat] (b : FloatBits)
    (hn : ¬b.isNaN) :
    ofBits ⟨b.b &&& (~~~ FloatBits.signMask)⟩ = Fp.fpAbs (ofBits b) := by
  have h_form : (⟨b.b &&& (~~~ FloatBits.signMask)⟩ : FloatBits)
        = FloatBits.signClear b :=
    ((FloatBits.ext1 (FloatBits.signClear b) (b.b &&& (~~~ FloatBits.signMask))).mpr
      (FloatBits.signClear_b_eq_and_not_signMask b)).symm
  rw [h_form]
  exact ofBits_signClear_eq_fpAbs b hn

end Fp
