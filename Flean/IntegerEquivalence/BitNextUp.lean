import Flean.IntegerEquivalence.Successor
import Flean.IntegerEquivalence.Compare

/-! # FP ↔ Integer equivalence: bit-level `nextUp` (within-binade)

Phase 1.6 of the FP ↔ Integer equivalence area.

The bit-level statement of `nextUp`: incrementing the trailing significand
field by 1 (when it doesn't carry into the exponent) gives the bit pattern
of the FP successor. Combined with the value-level
`nextUp_finite_eq_successorPos` bridge, this is the headline integer-
pipeline result: "FP nextUp = bit pattern + 1" for the within-binade case.

Cross-binade (T = allOnes wraps), subnormal→normal transition, saturation,
and the negative-input cases are natural follow-ups.
-/

namespace Fp.FloatBits

variable [FloatFormat]

/-- **Bit-level within-binade successor.** Increment the trailing significand
field; keep sign and exponent. Caller must ensure `T + 1` doesn't carry
(i.e., `T + 1 < 2^sigBits` as a Nat); without this hypothesis the BitVec
wraps and the result corresponds to the cross-binade case instead. -/
def bitNextUpWithin (b : FloatBits) : FloatBits :=
  FloatBits.mk' b.toBitsTriple.sign b.toBitsTriple.exponent
    (b.toBitsTriple.significand + 1)

@[simp] theorem bitNextUpWithin_sign_bv (b : FloatBits) :
    (bitNextUpWithin b).toBitsTriple.sign = b.toBitsTriple.sign :=
  construct_sign_eq_BitsTriple _ _ _

@[simp] theorem bitNextUpWithin_exponent_bv (b : FloatBits) :
    (bitNextUpWithin b).toBitsTriple.exponent = b.toBitsTriple.exponent :=
  construct_exponent_eq_BitsTriple _ _ _

@[simp] theorem bitNextUpWithin_significand_bv (b : FloatBits) :
    (bitNextUpWithin b).toBitsTriple.significand = b.toBitsTriple.significand + 1 :=
  construct_significand_eq_BitsTriple _ _ _

@[simp] theorem bitNextUpWithin_sign (b : FloatBits) :
    (bitNextUpWithin b).sign = b.sign := by
  unfold FloatBits.sign; rw [bitNextUpWithin_sign_bv]

/-- `bitNextUpWithin` preserves `isFinite` (E is unchanged). -/
theorem bitNextUpWithin_isFinite (b : FloatBits) (hf : b.isFinite) :
    (bitNextUpWithin b).isFinite := by
  obtain ⟨hni, hii⟩ := hf
  -- ¬b.isExponentAllOnes (else b would be NaN or Inf).
  have hb_E_not_max : ¬b.isExponentAllOnes := by
    intro hE_b
    by_cases hT0 : b.toBitsTriple.significand = 0
    · exact hii ⟨hE_b, by unfold FloatBits.isTSignificandZero; exact hT0⟩
    · exact hni ⟨hE_b, by unfold FloatBits.isTSignificandZero; exact hT0⟩
  -- New b's E is the same, so also ≠ allOnes.
  have hb'_E_not_max : ¬(bitNextUpWithin b).isExponentAllOnes := by
    intro hE'
    apply hb_E_not_max
    unfold FloatBits.isExponentAllOnes at hE' ⊢
    rwa [bitNextUpWithin_exponent_bv] at hE'
  refine ⟨?_, ?_⟩
  · intro ⟨hE, _⟩; exact hb'_E_not_max hE
  · intro ⟨hE, _⟩; exact hb'_E_not_max hE

/-- Within-binade BitVec increment: `(T + 1).toNat = T.toNat + 1` when there
is no carry. -/
private theorem T_plus_one_toNat (b : FloatBits)
    (hT_lt : b.toBitsTriple.significand.toNat + 1 < 2 ^ FloatFormat.significandBits) :
    (b.toBitsTriple.significand + 1).toNat = b.toBitsTriple.significand.toNat + 1 := by
  rw [BitVec.toNat_add]
  -- Goal: (T.toNat + (1 : BitVec _).toNat) % 2^sigBits = T.toNat + 1
  have h_one : (1 : BitVec FloatFormat.significandBits).toNat = 1 := by
    have hsbp := FloatFormat.significandBits_pos
    have hpow : 1 < 2 ^ FloatFormat.significandBits := by
      calc 1 = 2 ^ 0 := by norm_num
        _ < 2 ^ FloatFormat.significandBits :=
            Nat.pow_lt_pow_right (by norm_num) hsbp
    show BitVec.toNat 1 = 1
    simp
  rw [h_one]
  exact Nat.mod_eq_of_lt hT_lt

/-- For `b` with `T + 1` not at carry, the bit-level `bitNextUpWithin`'s
exponent is unchanged. -/
@[simp] theorem bitNextUpWithin_FpExponent {b : FloatBits} :
    (bitNextUpWithin b).FpExponent = b.FpExponent := by
  rw [FloatBits.FpExponent_def, FloatBits.FpExponent_def, bitNextUpWithin_exponent_bv]

/-- For `b` with `T + 1` not at carry, the bit-level `bitNextUpWithin`'s
decoded significand bumps by 1. -/
theorem bitNextUpWithin_FpSignificand (b : FloatBits)
    (hT_lt : b.toBitsTriple.significand.toNat + 1 < 2 ^ FloatFormat.significandBits) :
    (bitNextUpWithin b).FpSignificand = b.FpSignificand + 1 := by
  rw [FloatBits.FpSignificand_def, FloatBits.FpSignificand_def,
      bitNextUpWithin_significand_bv, bitNextUpWithin_exponent_bv]
  by_cases hE : b.toBitsTriple.exponent = 0
  · rw [if_pos hE, if_pos hE, T_plus_one_toNat b hT_lt]
  · rw [if_neg hE, if_neg hE]
    rw [BitVec.toNat_append, BitVec.toNat_append, T_plus_one_toNat b hT_lt]
    have hT_lt' : b.toBitsTriple.significand.toNat <
        2 ^ FloatFormat.significandBits := b.toBitsTriple.significand.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt hT_lt,
        ← Nat.shiftLeft_add_eq_or_of_lt hT_lt']
    ring

end Fp.FloatBits

namespace Fp

/-- **Bit-level within-binade `nextUp` bridge.** For finite positive `b` with
`T + 1 < 2^sigBits` (no carry into E) and a normal-range result mantissa,
decoding the bit-level within-binade increment matches `successorPos` of
the decoded FiniteFp.

Combined with `FiniteFp.nextUp_finite_eq_successorPos`, this gives
`nextUp (Fp.finite (decoded b)) = ofBits (bitNextUpWithin b)` —
the headline "FP nextUp = bit pattern increment" identity for the
within-binade case. -/
theorem ofBits_bitNextUpWithin_eq_successorPos_within
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite)
    (hT_lt : b.toBitsTriple.significand.toNat + 1 < 2 ^ FloatFormat.significandBits)
    (hres_m : b.FpSignificand + 1 < 2 ^ FloatFormat.prec.toNat) :
    let f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal hf⟩
    ofBits (FloatBits.bitNextUpWithin b) = FiniteFp.successorPos f_b := by
  simp only
  -- successorPos's within-binade case fires
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf⟩ with hf_b_def
  have hsmax : f_b.m + 1 < 2 ^ FloatFormat.prec.toNat := hres_m
  unfold FiniteFp.successorPos
  rw [dif_pos hsmax]
  -- Goal: ofBits (bitNextUpWithin b) = Fp.finite ⟨false, f_b.e, f_b.m + 1, _⟩.
  -- Decode the LHS using ofBits_eq_finite_of_isFinite.
  have hf' : (FloatBits.bitNextUpWithin b).isFinite :=
    FloatBits.bitNextUpWithin_isFinite b hf
  rw [ofBits_eq_finite_of_isFinite (FloatBits.bitNextUpWithin b) hf']
  -- Both sides Fp.finite ⟨..., ..., ..., _⟩ — match the FiniteFp.
  congr 1
  apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · show (FloatBits.bitNextUpWithin b).sign = false
    rw [FloatBits.bitNextUpWithin_sign]; exact hs
  · show (FloatBits.bitNextUpWithin b).FpExponent = f_b.e
    rw [FloatBits.bitNextUpWithin_FpExponent]
  · show (FloatBits.bitNextUpWithin b).FpSignificand = f_b.m + 1
    rw [FloatBits.bitNextUpWithin_FpSignificand b hT_lt]

/-- **Headline identity (within-binade, positive)**: bit-level within-binade
increment matches `nextUp` exactly. Composes the value-level
`nextUp_finite_eq_successorPos` with the bit-level `successorPos` bridge. -/
theorem nextUp_ofBits_eq_ofBits_bitNextUpWithin
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite)
    (hT_lt : b.toBitsTriple.significand.toNat + 1 < 2 ^ FloatFormat.significandBits)
    (hres_m : b.FpSignificand + 1 < 2 ^ FloatFormat.prec.toNat) :
    nextUp (ofBits b) = ofBits (FloatBits.bitNextUpWithin b) := by
  rw [ofBits_eq_finite_of_isFinite b hf]
  rw [FiniteFp.nextUp_finite_eq_successorPos _ hs]
  exact (ofBits_bitNextUpWithin_eq_successorPos_within b hs hf hT_lt hres_m).symm

end Fp
