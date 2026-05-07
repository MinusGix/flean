import Flean.Encoding.Conversion
import Flean.MinMax

/-! # FP ↔ Integer equivalence: sign-bit operations

Phase 1 of the FP ↔ Integer equivalence area
(see `.claude/notes/fp-integer-equivalence.md`).

This file proves that several `Fp` sign-bit operations correspond to flipping or
replacing the sign bit in the encoded `FloatBits` representation, modulo the
NaN carve-out (NaN payloads collapse to a single `Fp.NaN` at the abstract
level).

The workhorse is `FloatBits.setSign : Bool → FloatBits → FloatBits` (replace the
sign bit) at the bit level, and `Fp.withSign : Bool → Fp → Fp` at the abstract
level. The generic bridge `ofBits_setSign_eq_withSign` is then specialized to:

* `Neg.neg : Fp → Fp`             ↔  `signFlip` (XOR sign bit)
* `Fp.fpAbs : Fp → Fp`            ↔  `signClear` (clear sign bit)
* `Fp.copySign : Fp → Fp → Fp`    ↔  `copySign` (paste sign of `b₂` onto `b₁`)
-/

/-! ## One-bit XOR utilities -/

private theorem BitVec.xor_one_beq_one (x : BitVec 1) :
    ((x ^^^ 1) == 1) = !(x == 1) := by
  rcases BitVec.one_or x with h | h <;> subst h <;> decide

private theorem BitVec.xor_one_toNat_beq_one (x : BitVec 1) :
    ((x ^^^ 1).toNat == 1) = !(x.toNat == 1) := by
  rcases BitVec.one_or x with h | h <;> subst h <;> decide

namespace Fp

/-! ## `Fp.withSign`: replace the sign of an `Fp` (NaN-fixed)

These declarations require only `[FloatFormat]`. -/

section WithSign
variable [FloatFormat]

/-- Replace the sign of an `Fp` with the given boolean. NaN is left unchanged. -/
def withSign (s : Bool) (x : Fp) : Fp :=
  match x with
  | .finite f => .finite ⟨s, f.e, f.m, f.valid⟩
  | .infinite _ => .infinite s
  | .NaN => .NaN

@[simp] theorem withSign_finite (s : Bool) (f : FiniteFp) :
    Fp.withSign s (.finite f) = .finite ⟨s, f.e, f.m, f.valid⟩ := rfl

@[simp] theorem withSign_infinite (s b : Bool) :
    Fp.withSign s (.infinite b) = .infinite s := rfl

@[simp] theorem withSign_NaN (s : Bool) : Fp.withSign s .NaN = .NaN := rfl

theorem withSign_neg_sign (x : Fp) : Fp.withSign (!x.sign) x = -x := by
  cases x with
  | finite f =>
    simp only [withSign_finite, Fp.sign, FiniteFp.sign]
    rfl
  | infinite b => rfl
  | NaN => rfl

theorem withSign_false_eq_fpAbs (x : Fp) :
    Fp.withSign false x = Fp.fpAbs x := by
  cases x <;> rfl

/-- `copySign x y`: produce a copy of `x` with its sign replaced by `y.sign`.
NaN values of `x` are passed through unchanged (we do not consult `y`). -/
def copySign (x y : Fp) : Fp := Fp.withSign y.sign x

end WithSign

/-! ## `FloatBits.setSign`: bit-level workhorse

These declarations require only `[FloatFormat]`. -/

namespace FloatBits

section SetSign
variable [FloatFormat]

/-- Replace the sign bit of a `FloatBits` with the given boolean. -/
def setSign (s : Bool) (b : FloatBits) : FloatBits :=
  FloatBits.mk' (BitVec.ofBool s) b.toBitsTriple.exponent b.toBitsTriple.significand

@[simp] theorem setSign_sign_bv (s : Bool) (b : FloatBits) :
    (setSign s b).toBitsTriple.sign = BitVec.ofBool s :=
  construct_sign_eq_BitsTriple _ _ _

@[simp] theorem setSign_exponent_bv (s : Bool) (b : FloatBits) :
    (setSign s b).toBitsTriple.exponent = b.toBitsTriple.exponent :=
  construct_exponent_eq_BitsTriple _ _ _

@[simp] theorem setSign_significand_bv (s : Bool) (b : FloatBits) :
    (setSign s b).toBitsTriple.significand = b.toBitsTriple.significand :=
  construct_significand_eq_BitsTriple _ _ _

@[simp] theorem setSign_isExponentAllOnes (s : Bool) (b : FloatBits) :
    (setSign s b).isExponentAllOnes ↔ b.isExponentAllOnes := by
  unfold isExponentAllOnes; rw [setSign_exponent_bv]

@[simp] theorem setSign_isTSignificandZero (s : Bool) (b : FloatBits) :
    (setSign s b).isTSignificandZero ↔ b.isTSignificandZero := by
  unfold isTSignificandZero; rw [setSign_significand_bv]

@[simp] theorem setSign_isNaN (s : Bool) (b : FloatBits) :
    (setSign s b).isNaN ↔ b.isNaN := by
  unfold isNaN
  exact and_congr (setSign_isExponentAllOnes s b)
    (not_congr (setSign_isTSignificandZero s b))

@[simp] theorem setSign_isInfinite (s : Bool) (b : FloatBits) :
    (setSign s b).isInfinite ↔ b.isInfinite := by
  unfold isInfinite
  exact and_congr (setSign_isExponentAllOnes s b) (setSign_isTSignificandZero s b)

@[simp] theorem setSign_isFinite (s : Bool) (b : FloatBits) :
    (setSign s b).isFinite ↔ b.isFinite := by
  unfold isFinite
  exact and_congr (not_congr (setSign_isNaN s b))
    (not_congr (setSign_isInfinite s b))

theorem setSign_sign (s : Bool) (b : FloatBits) :
    (setSign s b).sign = s := by
  unfold sign
  rw [setSign_sign_bv, BitVec.ofBool_beq_one]

theorem setSign_FpExponent (s : Bool) (b : FloatBits) :
    (setSign s b).FpExponent = b.FpExponent := by
  rw [FpExponent_def, FpExponent_def, setSign_exponent_bv]

theorem setSign_FpSignificand (s : Bool) (b : FloatBits) :
    (setSign s b).FpSignificand = b.FpSignificand := by
  rw [FpSignificand_def, FpSignificand_def,
    setSign_exponent_bv, setSign_significand_bv]

/-! ### `signFlip`, `signClear`, `copySign` as specialized `setSign` -/

/-- Flip the sign bit (XOR with 1). -/
def signFlip (b : FloatBits) : FloatBits := setSign (!b.sign) b

/-- Clear the sign bit (set to `false`/positive). -/
def signClear (b : FloatBits) : FloatBits := setSign false b

/-- Copy the sign of `b₂` onto `b₁`. -/
def copySign (b₁ b₂ : FloatBits) : FloatBits := setSign b₂.sign b₁

theorem signFlip_def (b : FloatBits) : signFlip b = setSign (!b.sign) b := rfl
theorem signClear_def (b : FloatBits) : signClear b = setSign false b := rfl
theorem copySign_def (b₁ b₂ : FloatBits) : copySign b₁ b₂ = setSign b₂.sign b₁ := rfl

end SetSign
end FloatBits

end Fp

/-! ## Bridges to `ofBits` (require `[StdFloatFormat]`) -/

namespace Fp

/-- Decoding the bit-level sign agrees with the abstract sign for non-NaN inputs. -/
theorem ofBits_sign [StdFloatFormat] (b : FloatBits) (hn : ¬b.isNaN) :
    (ofBits b).sign = b.sign := by
  by_cases hi : b.isInfinite
  · have h1 : ofBits b = Fp.infinite b.sign := by
      unfold ofBits; rw [dif_neg hn, dif_pos hi]
    rw [h1]; rfl
  · have hf : b.isFinite := FloatBits.notNaN_notInfinite b hn hi
    have h1 : ofBits b =
        Fp.finite ⟨b.toBitsTriple.sign.toNat == 1,
                   b.FpExponent, b.FpSignificand,
                   FloatBits.isFinite_validFloatVal hf⟩ := by
      unfold ofBits; rw [dif_neg hn, dif_neg hi]
    rw [h1]
    show (b.toBitsTriple.sign.toNat == 1) = b.sign
    unfold FloatBits.sign
    rcases BitVec.one_or b.toBitsTriple.sign with hb | hb <;> rw [hb] <;> decide

/-- Generic bridge: replacing the sign bit on `FloatBits` corresponds to
`Fp.withSign` after decoding, for any non-NaN input. -/
theorem ofBits_setSign_eq_withSign [StdFloatFormat] (s : Bool) (b : FloatBits)
    (hn : ¬b.isNaN) :
    ofBits (FloatBits.setSign s b) = Fp.withSign s (ofBits b) := by
  have hns : ¬(FloatBits.setSign s b).isNaN :=
    fun h => hn ((FloatBits.setSign_isNaN s b).mp h)
  by_cases hi : b.isInfinite
  · have his : (FloatBits.setSign s b).isInfinite :=
      (FloatBits.setSign_isInfinite s b).mpr hi
    have hLHS : ofBits (FloatBits.setSign s b)
        = Fp.infinite (FloatBits.setSign s b).sign := by
      unfold ofBits; rw [dif_neg hns, dif_pos his]
    have hRHS : ofBits b = Fp.infinite b.sign := by
      unfold ofBits; rw [dif_neg hn, dif_pos hi]
    rw [hLHS, hRHS, FloatBits.setSign_sign]
    rfl
  · have hf : b.isFinite := FloatBits.notNaN_notInfinite b hn hi
    have his : ¬(FloatBits.setSign s b).isInfinite :=
      fun h => hi ((FloatBits.setSign_isInfinite s b).mp h)
    have hfs : (FloatBits.setSign s b).isFinite := by
      rw [FloatBits.setSign_isFinite]; exact hf
    have hLHS : ofBits (FloatBits.setSign s b) =
        Fp.finite ⟨(FloatBits.setSign s b).toBitsTriple.sign.toNat == 1,
                   (FloatBits.setSign s b).FpExponent,
                   (FloatBits.setSign s b).FpSignificand,
                   FloatBits.isFinite_validFloatVal hfs⟩ := by
      unfold ofBits; rw [dif_neg hns, dif_neg his]
    have hRHS : ofBits b =
        Fp.finite ⟨b.toBitsTriple.sign.toNat == 1,
                   b.FpExponent, b.FpSignificand,
                   FloatBits.isFinite_validFloatVal hf⟩ := by
      unfold ofBits; rw [dif_neg hn, dif_neg hi]
    rw [hLHS, hRHS, Fp.withSign_finite]
    congr 1
    apply (FiniteFp.eq_def _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · simp only [FloatBits.setSign_sign_bv]
      cases s <;> decide
    · exact FloatBits.setSign_FpExponent s b
    · exact FloatBits.setSign_FpSignificand s b

/-- `signFlip` at the bit level corresponds to `Neg.neg` at the `Fp` level
(modulo NaN). -/
theorem ofBits_signFlip_eq_neg [StdFloatFormat] (b : FloatBits) (hn : ¬b.isNaN) :
    ofBits (FloatBits.signFlip b) = -(ofBits b) := by
  rw [FloatBits.signFlip_def, ofBits_setSign_eq_withSign _ b hn,
    ← ofBits_sign b hn, Fp.withSign_neg_sign]

/-- `signClear` at the bit level corresponds to `Fp.fpAbs` (modulo NaN). -/
theorem ofBits_signClear_eq_fpAbs [StdFloatFormat] (b : FloatBits) (hn : ¬b.isNaN) :
    ofBits (FloatBits.signClear b) = Fp.fpAbs (ofBits b) := by
  rw [FloatBits.signClear_def, ofBits_setSign_eq_withSign false b hn,
    Fp.withSign_false_eq_fpAbs]

/-- `copySign` at the bit level corresponds to `Fp.copySign` (modulo NaN on
both sides). -/
theorem ofBits_copySign_eq_copySign [StdFloatFormat] (b₁ b₂ : FloatBits)
    (hn1 : ¬b₁.isNaN) (hn2 : ¬b₂.isNaN) :
    ofBits (FloatBits.copySign b₁ b₂) = Fp.copySign (ofBits b₁) (ofBits b₂) := by
  unfold Fp.copySign
  rw [FloatBits.copySign_def, ofBits_setSign_eq_withSign _ b₁ hn1,
    ofBits_sign b₂ hn2]

end Fp
