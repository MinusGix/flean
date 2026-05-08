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

/-! ## Cross-binade case (T = allOnes)

When `T = allOnes`, the BitVec increment wraps `T → 0` and carries into the
exponent. The structural form is `bitNextUpCross b := mk' s (E+1) 0`. Three
sub-cases by the original bit pattern:

1. *Subnormal-to-normal* (E = 0, T = allOnes): smallest normal output. At
   the value level this is the within-binade case of `successorPos`.
2. *Normal cross-binade* (E ∈ [1, allOnes - 2], T = allOnes): standard
   cross-binade in `successorPos`. Result: same form `⟨false, e+1, 2^(prec-1)⟩`.
3. *Saturation* (E = allOnes - 1, T = allOnes): result encoding is `+∞`.

Each case decodes differently, so they're shipped as separate theorems. -/

namespace Fp.FloatBits

variable [FloatFormat]

/-- **Bit-level cross-binade successor.** When `T + 1` carries into the
exponent: increment `E`, reset `T` to 0. -/
def bitNextUpCross (b : FloatBits) : FloatBits :=
  FloatBits.mk' b.toBitsTriple.sign (b.toBitsTriple.exponent + 1) 0

@[simp] theorem bitNextUpCross_sign_bv (b : FloatBits) :
    (bitNextUpCross b).toBitsTriple.sign = b.toBitsTriple.sign :=
  construct_sign_eq_BitsTriple _ _ _

@[simp] theorem bitNextUpCross_exponent_bv (b : FloatBits) :
    (bitNextUpCross b).toBitsTriple.exponent = b.toBitsTriple.exponent + 1 :=
  construct_exponent_eq_BitsTriple _ _ _

@[simp] theorem bitNextUpCross_significand_bv (b : FloatBits) :
    (bitNextUpCross b).toBitsTriple.significand = 0 :=
  construct_significand_eq_BitsTriple _ _ _

@[simp] theorem bitNextUpCross_sign (b : FloatBits) :
    (bitNextUpCross b).sign = b.sign := by
  unfold FloatBits.sign; rw [bitNextUpCross_sign_bv]

/-! ### Saturation case: result is `+∞` -/

/-- When `E + 1 = allOnes` (i.e., `b` was at the saturated normal max), the
cross-binade incrementer's bit pattern is the `+∞` encoding. -/
theorem bitNextUpCross_isInfinite_of_E_succ_max (b : FloatBits)
    (hE_succ_max : b.toBitsTriple.exponent + 1 = BitVec.allOnes FloatFormat.exponentBits) :
    (bitNextUpCross b).isInfinite := by
  refine ⟨?_, ?_⟩
  · unfold FloatBits.isExponentAllOnes
    rw [bitNextUpCross_exponent_bv]; exact hE_succ_max
  · unfold FloatBits.isTSignificandZero
    rw [bitNextUpCross_significand_bv]

end Fp.FloatBits

namespace Fp

/-- The cross-binade bit pattern with saturated exponent decodes to `+∞`. -/
theorem ofBits_bitNextUpCross_eq_pos_inf_of_saturated [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false)
    (hE_succ_max : b.toBitsTriple.exponent + 1 = BitVec.allOnes FloatFormat.exponentBits) :
    ofBits (FloatBits.bitNextUpCross b) = Fp.infinite false := by
  have hii : (FloatBits.bitNextUpCross b).isInfinite :=
    FloatBits.bitNextUpCross_isInfinite_of_E_succ_max b hE_succ_max
  unfold ofBits
  have hni : ¬(FloatBits.bitNextUpCross b).isNaN := fun ⟨_, hT⟩ => hT hii.2
  rw [dif_neg hni, dif_pos hii]
  rw [FloatBits.bitNextUpCross_sign, hs]

end Fp

/-! ### Normal cross-binade case (E ≠ 0, E + 1 ≠ allOnes) -/

namespace Fp.FloatBits

variable [StdFloatFormat]

/-- BitVec increment without wrap: `(E + 1).toNat = E.toNat + 1` when
`E ≠ allOnes`. -/
private theorem E_plus_one_toNat (b : FloatBits)
    (hE_lt : b.toBitsTriple.exponent.toNat + 1 < 2 ^ FloatFormat.exponentBits) :
    (b.toBitsTriple.exponent + 1).toNat = b.toBitsTriple.exponent.toNat + 1 := by
  rw [BitVec.toNat_add]
  have h_one : (1 : BitVec FloatFormat.exponentBits).toNat = 1 := by
    have hpos := FloatFormat.exponentBits_pos
    have hpow : 1 < 2 ^ FloatFormat.exponentBits := by
      calc 1 = 2 ^ 0 := by norm_num
        _ < 2 ^ FloatFormat.exponentBits :=
            Nat.pow_lt_pow_right (by norm_num) hpos
    show BitVec.toNat 1 = 1
    simp
  rw [h_one]
  exact Nat.mod_eq_of_lt hE_lt

/-- For bit-normal `b` (`E ≠ 0`) with `E + 1 ≠ allOnes`, the cross-binade
incrementer's decoded exponent is `b.FpExponent + 1`. -/
theorem bitNextUpCross_FpExponent_of_normal (b : FloatBits)
    (hE_nz : b.toBitsTriple.exponent ≠ 0)
    (hE_succ_lt : b.toBitsTriple.exponent.toNat + 1 < 2 ^ FloatFormat.exponentBits) :
    (bitNextUpCross b).FpExponent = b.FpExponent + 1 := by
  rw [FloatBits.FpExponent_def, FloatBits.FpExponent_def, bitNextUpCross_exponent_bv]
  -- New E = E + 1 ≠ 0 (since (E+1).toNat ≥ 1)
  have hE_succ_nz : b.toBitsTriple.exponent + 1 ≠ 0 := by
    intro hE_eq
    have h := congrArg BitVec.toNat hE_eq
    rw [E_plus_one_toNat b hE_succ_lt] at h
    simp at h
  rw [if_neg hE_succ_nz, if_neg hE_nz]
  rw [E_plus_one_toNat b hE_succ_lt]
  push_cast; ring

/-- For bit-normal `b` (`E ≠ 0`) with `E + 1 ≠ allOnes`, the cross-binade
incrementer's decoded significand is `2^(prec-1).toNat` (smallest normal). -/
theorem bitNextUpCross_FpSignificand_of_normal (b : FloatBits)
    (hE_succ_lt : b.toBitsTriple.exponent.toNat + 1 < 2 ^ FloatFormat.exponentBits) :
    (bitNextUpCross b).FpSignificand = 2 ^ (FloatFormat.prec - 1).toNat := by
  rw [FloatBits.FpSignificand_def, bitNextUpCross_exponent_bv,
      bitNextUpCross_significand_bv]
  have hE_succ_nz : b.toBitsTriple.exponent + 1 ≠ 0 := by
    intro hE_eq
    have h := congrArg BitVec.toNat hE_eq
    rw [E_plus_one_toNat b hE_succ_lt] at h
    simp at h
  rw [if_neg hE_succ_nz]
  -- Goal: ((BitVec.ofBool true) ++ (0 : BitVec sigBits)).toNat = 2^(prec-1).toNat
  rw [BitVec.toNat_append]
  show 1 <<< FloatFormat.significandBits ||| 0 = 2 ^ (FloatFormat.prec - 1).toNat
  simp [Nat.shiftLeft_eq]

/-- `bitNextUpCross b` is finite when `E + 1 ≠ allOnes` (and stays finite). -/
theorem bitNextUpCross_isFinite_of_E_succ_lt (b : FloatBits)
    (hE_succ_not_max : b.toBitsTriple.exponent + 1 ≠ BitVec.allOnes FloatFormat.exponentBits) :
    (bitNextUpCross b).isFinite := by
  refine ⟨?_, ?_⟩
  · intro ⟨hE, _⟩
    apply hE_succ_not_max
    unfold FloatBits.isExponentAllOnes at hE
    rwa [bitNextUpCross_exponent_bv] at hE
  · intro ⟨hE, _⟩
    apply hE_succ_not_max
    unfold FloatBits.isExponentAllOnes at hE
    rwa [bitNextUpCross_exponent_bv] at hE

end Fp.FloatBits

namespace Fp

/-- **Normal cross-binade bit-level bridge.** For finite positive `b` with
`T = allOnes` (so `T + 1` BitVec-wraps to 0) and `E + 1 ≠ allOnes` (no
saturation) and `E ≠ 0` (b is bit-normal), the decoded cross-binade
incrementer matches `successorPos` of the decoded FiniteFp.

The result-side hypothesis: `f_b.m + 1 = 2^prec` (cross-binade trigger
in `successorPos`) and `f_b.e + 1 ≤ max_exp` (no saturation in `successorPos`). -/
theorem ofBits_bitNextUpCross_eq_successorPos_normal_cross
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite)
    (hE_nz : b.toBitsTriple.exponent ≠ 0)
    (hE_succ_lt : b.toBitsTriple.exponent.toNat + 1 < 2 ^ FloatFormat.exponentBits)
    (hE_succ_not_max : b.toBitsTriple.exponent + 1 ≠ BitVec.allOnes FloatFormat.exponentBits)
    (hT_max : b.FpSignificand + 1 = 2 ^ FloatFormat.prec.toNat)
    (he_lt : b.FpExponent + 1 ≤ FloatFormat.max_exp) :
    let f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal hf⟩
    ofBits (FloatBits.bitNextUpCross b) = FiniteFp.successorPos f_b := by
  simp only
  -- successorPos hits cross-binade
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf⟩
  unfold FiniteFp.successorPos
  have hsmax_neg : ¬(f_b.m + 1 < 2 ^ FloatFormat.prec.toNat) := by
    show ¬(b.FpSignificand + 1 < 2 ^ FloatFormat.prec.toNat)
    omega
  rw [dif_neg hsmax_neg, dif_pos he_lt]
  -- Decode bitNextUpCross b
  have hf' : (FloatBits.bitNextUpCross b).isFinite :=
    FloatBits.bitNextUpCross_isFinite_of_E_succ_lt b hE_succ_not_max
  rw [ofBits_eq_finite_of_isFinite (FloatBits.bitNextUpCross b) hf']
  congr 1
  apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · show (FloatBits.bitNextUpCross b).sign = false
    rw [FloatBits.bitNextUpCross_sign]; exact hs
  · show (FloatBits.bitNextUpCross b).FpExponent = f_b.e + 1
    rw [FloatBits.bitNextUpCross_FpExponent_of_normal b hE_nz hE_succ_lt]
  · show (FloatBits.bitNextUpCross b).FpSignificand = 2 ^ (FloatFormat.prec - 1).toNat
    exact FloatBits.bitNextUpCross_FpSignificand_of_normal b hE_succ_lt

end Fp

/-! ### Subnormal-to-normal transition (E = 0, T = allOnes) -/

namespace Fp.FloatBits

variable [StdFloatFormat]

/-- For subnormal `b` (`E = 0`), the cross-binade incrementer produces
`E_new = 1`, which decodes to FpExponent = `min_exp` (using the std format
identity `1 - bias = min_exp`). -/
theorem bitNextUpCross_FpExponent_of_subnormal (b : FloatBits)
    (hE_zero : b.toBitsTriple.exponent = 0) :
    (bitNextUpCross b).FpExponent = FloatFormat.min_exp := by
  rw [FloatBits.FpExponent_def, bitNextUpCross_exponent_bv, hE_zero]
  -- E + 1 = 0 + 1 = 1 (BitVec), ≠ 0
  have h_one_ne : (0 : BitVec FloatFormat.exponentBits) + 1 ≠ 0 := by
    intro h
    have hcast := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at hcast
    have h_one : (1 : BitVec FloatFormat.exponentBits).toNat = 1 := by
      have hpos := FloatFormat.exponentBits_pos
      have hpow : 1 < 2 ^ FloatFormat.exponentBits :=
        calc 1 = 2 ^ 0 := by norm_num
          _ < 2 ^ FloatFormat.exponentBits :=
              Nat.pow_lt_pow_right (by norm_num) hpos
      show BitVec.toNat 1 = 1
      simp
    rw [h_one] at hcast
    simp at hcast
  rw [if_neg h_one_ne]
  -- ((0 : BitVec n) + 1).toNat = 1
  have h_succ_zero_toNat : ((0 : BitVec FloatFormat.exponentBits) + 1).toNat = 1 := by
    rw [BitVec.toNat_add]
    have h_one : (1 : BitVec FloatFormat.exponentBits).toNat = 1 := by
      have hpos := FloatFormat.exponentBits_pos
      have hpow : 1 < 2 ^ FloatFormat.exponentBits :=
        calc 1 = 2 ^ 0 := by norm_num
          _ < 2 ^ FloatFormat.exponentBits :=
              Nat.pow_lt_pow_right (by norm_num) hpos
      show BitVec.toNat 1 = 1
      simp
    rw [h_one]
    have hpos := FloatFormat.exponentBits_pos
    have hpow : (1 : ℕ) < 2 ^ FloatFormat.exponentBits :=
      calc 1 = 2 ^ 0 := by norm_num
        _ < 2 ^ FloatFormat.exponentBits :=
            Nat.pow_lt_pow_right (by norm_num) hpos
    -- (0 + 1) % 2^expBits = 1 since 1 < 2^expBits
    show (0 + 1) % 2 ^ FloatFormat.exponentBits = 1
    exact Nat.mod_eq_of_lt hpow
  show ((0 : BitVec FloatFormat.exponentBits) + 1).toNat - (FloatFormat.exponentBias : ℤ) = FloatFormat.min_exp
  rw [h_succ_zero_toNat]
  -- 1 - bias = min_exp: std format identity
  have hstd := StdFloatFormat.st
  unfold FloatFormat.isStandardExpRange at hstd
  unfold FloatFormat.exponentBias
  push_cast; linarith

/-- For subnormal `b` (`E = 0`), the cross-binade incrementer's decoded
significand is `2^(prec-1).toNat` (smallest normal). -/
theorem bitNextUpCross_FpSignificand_of_subnormal (b : FloatBits)
    (hE_zero : b.toBitsTriple.exponent = 0) :
    (bitNextUpCross b).FpSignificand = 2 ^ (FloatFormat.prec - 1).toNat := by
  rw [FloatBits.FpSignificand_def, bitNextUpCross_exponent_bv,
      bitNextUpCross_significand_bv, hE_zero]
  have h_one_ne : (0 : BitVec FloatFormat.exponentBits) + 1 ≠ 0 := by
    intro h
    have hcast := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at hcast
    have h_one : (1 : BitVec FloatFormat.exponentBits).toNat = 1 := by
      have hpos := FloatFormat.exponentBits_pos
      have hpow : 1 < 2 ^ FloatFormat.exponentBits :=
        calc 1 = 2 ^ 0 := by norm_num
          _ < 2 ^ FloatFormat.exponentBits :=
              Nat.pow_lt_pow_right (by norm_num) hpos
      show BitVec.toNat 1 = 1
      simp
    rw [h_one] at hcast
    simp at hcast
  rw [if_neg h_one_ne]
  rw [BitVec.toNat_append]
  show 1 <<< FloatFormat.significandBits ||| 0 = 2 ^ (FloatFormat.prec - 1).toNat
  simp [Nat.shiftLeft_eq]

/-- For subnormal `b` (`E = 0`), `bitNextUpCross b` is finite (E + 1 = 1 ≠ allOnes
since allOnes requires `2^exponentBits - 1 ≥ 3`, but 1 < 3). -/
theorem bitNextUpCross_isFinite_of_subnormal (b : FloatBits)
    (hE_zero : b.toBitsTriple.exponent = 0) :
    (bitNextUpCross b).isFinite := by
  -- E + 1 = 1 ≠ allOnes (since allOnes.toNat = 2^expBits - 1 ≥ 1 with strict for std formats)
  have h_succ_ne_max : b.toBitsTriple.exponent + 1 ≠ BitVec.allOnes FloatFormat.exponentBits := by
    intro h
    rw [hE_zero] at h
    have hcast := congrArg BitVec.toNat h
    rw [BitVec.toNat_allOnes] at hcast
    -- (0 + 1).toNat = 1, but should equal 2^expBits - 1.
    have h_succ : ((0 : BitVec FloatFormat.exponentBits) + 1).toNat = 1 := by
      rw [BitVec.toNat_add]
      have h_one : (1 : BitVec FloatFormat.exponentBits).toNat = 1 := by
        have hpos := FloatFormat.exponentBits_pos
        have hpow : 1 < 2 ^ FloatFormat.exponentBits :=
          calc 1 = 2 ^ 0 := by norm_num
            _ < 2 ^ FloatFormat.exponentBits :=
                Nat.pow_lt_pow_right (by norm_num) hpos
        show BitVec.toNat 1 = 1
        simp
      rw [h_one]
      have hpos := FloatFormat.exponentBits_pos
      have hpow : (1 : ℕ) < 2 ^ FloatFormat.exponentBits :=
        calc 1 = 2 ^ 0 := by norm_num
          _ < 2 ^ FloatFormat.exponentBits :=
              Nat.pow_lt_pow_right (by norm_num) hpos
      show (0 + 1) % 2 ^ FloatFormat.exponentBits = 1
      exact Nat.mod_eq_of_lt hpow
    rw [h_succ] at hcast
    -- For std format, 2^expBits = 2 * 2^exp_pow ≥ 2*1 = 2... but allOnes.toNat = 2*2^exp_pow - 1.
    -- For exp_pow ≥ 1: allOnes.toNat ≥ 3. So 1 ≠ allOnes.toNat.
    have h_expB := StdFloatFormat.exponentBits_def
    have h_pow_pos := StdFloatFormat.exp_pow_pos
    have h2 : (2 : ℕ) ^ FloatFormat.exponentBits ≥ 4 := by
      rw [h_expB]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (StdFloatFormat.exp_pow + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact bitNextUpCross_isFinite_of_E_succ_lt b h_succ_ne_max

end Fp.FloatBits

namespace Fp

/-- **Subnormal-to-normal bit-level bridge.** For finite positive `b` with
`E = 0` (subnormal) and `T = allOnes` (so `T + 1` BitVec-wraps), the
cross-binade increment produces the smallest normal at `min_exp`, matching
`successorPos`'s within-binade case where `f_b.m + 1 = 2^(prec-1)`. -/
theorem ofBits_bitNextUpCross_eq_successorPos_sub_to_norm
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite)
    (hE_zero : b.toBitsTriple.exponent = 0)
    (hT_max : b.FpSignificand + 1 = 2 ^ (FloatFormat.prec - 1).toNat) :
    let f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal hf⟩
    ofBits (FloatBits.bitNextUpCross b) = FiniteFp.successorPos f_b := by
  simp only
  -- successorPos hits within-binade (m + 1 = 2^(prec-1) < 2^prec)
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf⟩
  have hsmax : f_b.m + 1 < 2 ^ FloatFormat.prec.toNat := by
    show b.FpSignificand + 1 < 2 ^ FloatFormat.prec.toNat
    rw [hT_max]
    exact FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
  unfold FiniteFp.successorPos
  rw [dif_pos hsmax]
  -- f_b.e = b.FpExponent = min_exp (since E = 0)
  have hfe : f_b.e = FloatFormat.min_exp := by
    show b.FpExponent = FloatFormat.min_exp
    rw [FloatBits.FpExponent_def, if_pos hE_zero]
  -- Decode bitNextUpCross b
  have hf' : (FloatBits.bitNextUpCross b).isFinite :=
    FloatBits.bitNextUpCross_isFinite_of_subnormal b hE_zero
  rw [ofBits_eq_finite_of_isFinite (FloatBits.bitNextUpCross b) hf']
  congr 1
  apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · show (FloatBits.bitNextUpCross b).sign = false
    rw [FloatBits.bitNextUpCross_sign]; exact hs
  · show (FloatBits.bitNextUpCross b).FpExponent = f_b.e
    rw [FloatBits.bitNextUpCross_FpExponent_of_subnormal b hE_zero, hfe]
  · show (FloatBits.bitNextUpCross b).FpSignificand = f_b.m + 1
    rw [FloatBits.bitNextUpCross_FpSignificand_of_subnormal b hE_zero]
    show 2 ^ (FloatFormat.prec - 1).toNat = b.FpSignificand + 1
    exact hT_max.symm

/-! ### Headline cross-binade identities

These compose the structural cross-binade bridges with the value-level
`nextUp_finite_eq_successorPos`. -/

/-- Headline identity for the **cross-binade subnormal-to-normal** case. -/
theorem nextUp_ofBits_eq_ofBits_bitNextUpCross_sub_to_norm
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite)
    (hE_zero : b.toBitsTriple.exponent = 0)
    (hT_max : b.FpSignificand + 1 = 2 ^ (FloatFormat.prec - 1).toNat) :
    nextUp (ofBits b) = ofBits (FloatBits.bitNextUpCross b) := by
  rw [ofBits_eq_finite_of_isFinite b hf]
  rw [FiniteFp.nextUp_finite_eq_successorPos _ hs]
  exact (ofBits_bitNextUpCross_eq_successorPos_sub_to_norm b hs hf hE_zero hT_max).symm

/-- Headline identity for the **cross-binade normal** case. -/
theorem nextUp_ofBits_eq_ofBits_bitNextUpCross_normal_cross
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite)
    (hE_nz : b.toBitsTriple.exponent ≠ 0)
    (hE_succ_lt : b.toBitsTriple.exponent.toNat + 1 < 2 ^ FloatFormat.exponentBits)
    (hE_succ_not_max : b.toBitsTriple.exponent + 1 ≠ BitVec.allOnes FloatFormat.exponentBits)
    (hT_max : b.FpSignificand + 1 = 2 ^ FloatFormat.prec.toNat)
    (he_lt : b.FpExponent + 1 ≤ FloatFormat.max_exp) :
    nextUp (ofBits b) = ofBits (FloatBits.bitNextUpCross b) := by
  rw [ofBits_eq_finite_of_isFinite b hf]
  rw [FiniteFp.nextUp_finite_eq_successorPos _ hs]
  exact (ofBits_bitNextUpCross_eq_successorPos_normal_cross b hs hf hE_nz hE_succ_lt
    hE_succ_not_max hT_max he_lt).symm

/-- Headline identity for the **cross-binade saturated** case. When `b` is
the encoding of `largestFiniteFloat`, both sides are `+∞`. -/
theorem nextUp_ofBits_eq_ofBits_bitNextUpCross_saturated
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite)
    (hE_succ_max : b.toBitsTriple.exponent + 1 = BitVec.allOnes FloatFormat.exponentBits)
    (hT_max : b.FpSignificand + 1 = 2 ^ FloatFormat.prec.toNat)
    (h_e_eq_max : b.FpExponent = FloatFormat.max_exp) :
    nextUp (ofBits b) = ofBits (FloatBits.bitNextUpCross b) := by
  -- LHS: nextUp (ofBits b) = nextUp (Fp.finite f_b) = nextUp (Fp.finite largestFiniteFloat) = +∞
  rw [ofBits_eq_finite_of_isFinite b hf]
  -- f_b = largestFiniteFloat
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf⟩ with hf_b_def
  have hf_b_eq : f_b = FiniteFp.largestFiniteFloat := by
    apply (FiniteFp.eq_def _ _).mpr
    refine ⟨hs, h_e_eq_max, ?_⟩
    show b.FpSignificand = 2^FloatFormat.prec.toNat - 1
    have hpos : 0 < (2 : ℕ) ^ FloatFormat.prec.toNat := Nat.two_pow_pos _
    omega
  rw [hf_b_eq, nextUp_largestFiniteFloat]
  -- RHS: ofBits (bitNextUpCross b) = +∞ from saturation
  exact (ofBits_bitNextUpCross_eq_pos_inf_of_saturated b hs hE_succ_max).symm

end Fp

/-! ## Master positive-input bit-level successor

The unifier `bitNextUpPos b` automatically dispatches between
`bitNextUpWithin` (T + 1 doesn't carry) and `bitNextUpCross` (T = allOnes
wraps, E increments). The master bridge `ofBits_bitNextUpPos_eq_successorPos`
takes only basic positive-finite hypotheses; the within/cross branch
dispatch happens internally. -/

namespace Fp.FloatBits

variable [StdFloatFormat]

/-- **Master positive-input bit-level successor.** Dispatches between
within-binade and cross-binade based on whether `T + 1` carries. -/
def bitNextUpPos (b : FloatBits) : FloatBits :=
  if b.toBitsTriple.significand + 1 = 0 then bitNextUpCross b
  else bitNextUpWithin b

/-- For finite positive `b`, deriving `T.toNat + 1 < 2^sigBits` from
`T + 1 ≠ 0` (BitVec). -/
private theorem T_succ_lt_of_T_succ_ne_zero (b : FloatBits)
    (hT_succ_ne : b.toBitsTriple.significand + 1 ≠ 0) :
    b.toBitsTriple.significand.toNat + 1 < 2 ^ FloatFormat.significandBits := by
  have hT_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b.toBitsTriple.significand.isLt
  -- T.toNat + 1 ≤ 2^sigBits, with strict iff T+1 ≠ 0 BitVec
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hT_lt) with h | h
  · exact h
  · exfalso
    apply hT_succ_ne
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    show (b.toBitsTriple.significand.toNat + (1 : BitVec _).toNat)
        % 2 ^ FloatFormat.significandBits = (0 : BitVec _).toNat
    have h_one : (1 : BitVec FloatFormat.significandBits).toNat = 1 := by
      have hsb := FloatFormat.significandBits_pos
      have hpow : 1 < 2 ^ FloatFormat.significandBits :=
        calc 1 = 2 ^ 0 := by norm_num
          _ < 2 ^ FloatFormat.significandBits :=
              Nat.pow_lt_pow_right (by norm_num) hsb
      show BitVec.toNat 1 = 1
      simp
    rw [h_one]
    -- h : T.toNat + 1 = 2^sigBits (from Nat.succ_le_of_lt + Nat.lt_or_eq_of_le)
    have h' : b.toBitsTriple.significand.toNat + 1 = 2 ^ FloatFormat.significandBits := h
    rw [h', Nat.mod_self]
    show (0 : ℕ) = (0 : BitVec FloatFormat.significandBits).toNat
    simp

/-- For finite positive `b` and within-binade case (T + 1 ≠ 0),
the result-mantissa is in normal range (` < 2^prec`). -/
private theorem FpSignificand_succ_lt_prec_of_within (b : FloatBits)
    (hT_succ_lt : b.toBitsTriple.significand.toNat + 1 < 2 ^ FloatFormat.significandBits) :
    b.FpSignificand + 1 < 2 ^ FloatFormat.prec.toNat := by
  rw [FloatBits.FpSignificand_def]
  have h_one_plus : 1 + FloatFormat.significandBits = FloatFormat.prec.toNat :=
    FloatFormat.one_plus_significandBits
  have h_two_prec : (2 : ℕ) ^ FloatFormat.prec.toNat
        = 2 * 2 ^ FloatFormat.significandBits := by
    rw [← h_one_plus]; ring
  by_cases hE : b.toBitsTriple.exponent = 0
  · rw [if_pos hE]
    -- FpSignificand = T.toNat, T.toNat + 1 < 2^sigBits ≤ 2^prec
    have h_le : 2 ^ FloatFormat.significandBits ≤ 2 ^ FloatFormat.prec.toNat := by
      rw [h_two_prec]; omega
    omega
  · rw [if_neg hE]
    -- FpSignificand = (1 ++ T).toNat = 2^sigBits + T.toNat
    rw [BitVec.toNat_append]
    have hT_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
      b.toBitsTriple.significand.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt hT_lt, Nat.shiftLeft_eq]
    show ((BitVec.ofBool true).toNat * 2 ^ FloatFormat.significandBits
          + b.toBitsTriple.significand.toNat) + 1 < 2 ^ FloatFormat.prec.toNat
    have hbool : (BitVec.ofBool true).toNat = 1 := by simp
    rw [hbool, h_two_prec]
    omega

end Fp.FloatBits

namespace Fp

/-- **Master positive-input bit-level bridge.** For finite positive `b`,
the bit-level master successor `bitNextUpPos` matches `successorPos` of
the decoded FiniteFp. Auto-dispatches between within-binade, normal
cross-binade, subnormal-to-normal, and saturation cases. -/
theorem ofBits_bitNextUpPos_eq_successorPos
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite) :
    let f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal hf⟩
    ofBits (FloatBits.bitNextUpPos b) = FiniteFp.successorPos f_b := by
  simp only
  unfold FloatBits.bitNextUpPos
  by_cases hT_max : b.toBitsTriple.significand + 1 = 0
  · -- Cross-binade case: T = allOnes.
    rw [if_pos hT_max]
    -- T.toNat + 1 = 2^sigBits (since T + 1 = 0 BitVec).
    -- Equivalent: T = allOnes, T.toNat = 2^sigBits - 1.
    have hT_eq_allOnes : b.toBitsTriple.significand
          = BitVec.allOnes FloatFormat.significandBits := by
      have hT_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
        b.toBitsTriple.significand.isLt
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_allOnes]
      have hcast := congrArg BitVec.toNat hT_max
      rw [BitVec.toNat_add] at hcast
      have h_one : (1 : BitVec FloatFormat.significandBits).toNat = 1 := by
        have hsb := FloatFormat.significandBits_pos
        have hpow : 1 < 2 ^ FloatFormat.significandBits :=
          calc 1 = 2 ^ 0 := by norm_num
            _ < 2 ^ FloatFormat.significandBits :=
                Nat.pow_lt_pow_right (by norm_num) hsb
        show BitVec.toNat 1 = 1
        simp
      rw [h_one] at hcast
      have h_zero_toNat : (0 : BitVec FloatFormat.significandBits).toNat = 0 := by simp
      rw [h_zero_toNat] at hcast
      -- hcast : (T.toNat + 1) % 2^sigBits = 0
      have hpow_pos : 0 < (2 : ℕ) ^ FloatFormat.significandBits := Nat.two_pow_pos _
      have hT_succ_le : b.toBitsTriple.significand.toNat + 1 ≤ 2 ^ FloatFormat.significandBits := by
        omega
      rcases Nat.lt_or_eq_of_le hT_succ_le with hlt | heq
      · exfalso
        rw [Nat.mod_eq_of_lt hlt] at hcast
        omega
      · omega
    have hT_succ_eq_pow : b.toBitsTriple.significand.toNat + 1
          = 2 ^ FloatFormat.significandBits := by
      have h := congrArg BitVec.toNat hT_eq_allOnes
      rw [BitVec.toNat_allOnes] at h
      have hpow_pos : 0 < (2 : ℕ) ^ FloatFormat.significandBits := Nat.two_pow_pos _
      omega
    by_cases hE_zero : b.toBitsTriple.exponent = 0
    · -- Subnormal-to-normal case
      apply ofBits_bitNextUpCross_eq_successorPos_sub_to_norm b hs hf hE_zero
      -- Need: b.FpSignificand + 1 = 2^(prec-1).toNat
      rw [FloatBits.FpSignificand_def, if_pos hE_zero,
          ← FloatFormat.significandBits_eq]
      omega
    · -- E ≠ 0: normal cross-binade or saturation
      by_cases hE_succ_max : b.toBitsTriple.exponent + 1 = BitVec.allOnes FloatFormat.exponentBits
      · -- Saturation
        rw [ofBits_bitNextUpCross_eq_pos_inf_of_saturated b hs hE_succ_max]
        -- Show successorPos f_b = +∞: f_b is largestFiniteFloat
        -- FpSignificand = 2^prec - 1 (since E ≠ 0 and T = allOnes)
        have hFpSig_eq : b.FpSignificand = 2 ^ FloatFormat.prec.toNat - 1 := by
          rw [FloatBits.FpSignificand_def, if_neg hE_zero]
          rw [BitVec.toNat_append]
          have hT_lt : b.toBitsTriple.significand.toNat <
              2 ^ FloatFormat.significandBits := b.toBitsTriple.significand.isLt
          rw [← Nat.shiftLeft_add_eq_or_of_lt hT_lt, Nat.shiftLeft_eq]
          show (BitVec.ofBool true).toNat * 2 ^ FloatFormat.significandBits
              + b.toBitsTriple.significand.toNat = 2 ^ FloatFormat.prec.toNat - 1
          have hbool : (BitVec.ofBool true).toNat = 1 := by simp
          have h_two_prec : (2 : ℕ) ^ FloatFormat.prec.toNat
                = 2 * 2 ^ FloatFormat.significandBits := by
            rw [← FloatFormat.one_plus_significandBits]; ring
          rw [hbool]; omega
        -- f_b.e = max_exp (from E + 1 = allOnes)
        have hFpExp_eq : b.FpExponent = FloatFormat.max_exp := by
          rw [FloatBits.FpExponent_def, if_neg hE_zero]
          have hE_eq : b.toBitsTriple.exponent.toNat = (BitVec.allOnes FloatFormat.exponentBits).toNat - 1 := by
            have hcast := congrArg BitVec.toNat hE_succ_max
            rw [BitVec.toNat_add] at hcast
            rw [BitVec.toNat_allOnes] at hcast
            have h_one : (1 : BitVec FloatFormat.exponentBits).toNat = 1 := by
              have hpos := FloatFormat.exponentBits_pos
              have hpow : 1 < 2 ^ FloatFormat.exponentBits :=
                calc 1 = 2 ^ 0 := by norm_num
                  _ < 2 ^ FloatFormat.exponentBits :=
                      Nat.pow_lt_pow_right (by norm_num) hpos
              show BitVec.toNat 1 = 1; simp
            rw [h_one] at hcast
            rw [BitVec.toNat_allOnes]
            -- hcast: (E.toNat + 1) % 2^expBits = 2^expBits - 1
            have hE_lt : b.toBitsTriple.exponent.toNat < 2 ^ FloatFormat.exponentBits :=
              b.toBitsTriple.exponent.isLt
            -- E.toNat + 1 ≤ 2^expBits, so mod is just E.toNat + 1 if < 2^expBits, else 0.
            by_cases hE_eq_max : b.toBitsTriple.exponent.toNat + 1 = 2 ^ FloatFormat.exponentBits
            · -- E = allOnes: contradiction with finite (since E = allOnes ⇒ NaN/Inf)
              exfalso
              apply hf.2
              refine ⟨?_, ?_⟩
              · unfold FloatBits.isExponentAllOnes
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_allOnes]
                omega
              · -- T = 0? But T = allOnes from hT_max
                exfalso; apply hf.1
                refine ⟨?_, ?_⟩
                · unfold FloatBits.isExponentAllOnes
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_allOnes]
                  omega
                · unfold FloatBits.isTSignificandZero
                  intro hT_eq_zero
                  -- T = 0 contradicts hT_max (T = allOnes)
                  have hT_zero_toNat : b.toBitsTriple.significand.toNat = 0 := by
                    rw [hT_eq_zero]
                    simp
                  have hsb := FloatFormat.significandBits_pos
                  have hpow_lt : 1 < 2 ^ FloatFormat.significandBits :=
                    calc 1 = 2 ^ 0 := by norm_num
                      _ < 2 ^ FloatFormat.significandBits :=
                          Nat.pow_lt_pow_right (by norm_num) hsb
                  omega
            · have hE_lt_pow : b.toBitsTriple.exponent.toNat + 1 < 2 ^ FloatFormat.exponentBits := by
                omega
              rw [Nat.mod_eq_of_lt hE_lt_pow] at hcast
              omega
          show (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias = FloatFormat.max_exp
          rw [hE_eq]
          rw [BitVec.toNat_allOnes]
          -- (2^expBits - 1 - 1) - bias = max_exp
          have hstd := StdFloatFormat.st
          unfold FloatFormat.isStandardExpRange at hstd
          unfold FloatFormat.exponentBias
          have h_expB := StdFloatFormat.exponentBits_def
          have h_pow_pos := StdFloatFormat.exp_pow_pos
          have h_max_def := StdFloatFormat.max_exp_def
          have h2 : (2 : ℕ) ^ (StdFloatFormat.exp_pow + 1)
                = 2 * 2 ^ StdFloatFormat.exp_pow := by ring
          have h2_pos : 0 < (2 : ℕ) ^ StdFloatFormat.exp_pow := Nat.two_pow_pos _
          rw [h_expB, h_max_def]
          rw [h2]
          have h2_int : ((2 * 2 ^ StdFloatFormat.exp_pow - 1 - 1 : ℕ) : ℤ)
                = 2 * (2 : ℤ) ^ StdFloatFormat.exp_pow - 2 := by
            have h_pow_pos : 1 ≤ (2 : ℕ) ^ StdFloatFormat.exp_pow := Nat.one_le_two_pow
            have h_pos : 2 ≤ 2 * (2 : ℕ) ^ StdFloatFormat.exp_pow := by omega
            rw [show (2 * 2 ^ StdFloatFormat.exp_pow - 1 - 1 : ℕ)
                  = 2 * 2 ^ StdFloatFormat.exp_pow - 2 from by omega]
            push_cast [Nat.cast_sub h_pos]
            ring
          rw [h2_int]
          ring
        set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
          FloatBits.isFinite_validFloatVal hf⟩
        have hf_b_eq : f_b = FiniteFp.largestFiniteFloat := by
          apply (FiniteFp.eq_def _ _).mpr
          refine ⟨hs, hFpExp_eq, hFpSig_eq⟩
        rw [hf_b_eq]
        unfold FiniteFp.successorPos
        have hsmax_neg : ¬(FiniteFp.largestFiniteFloat.m + 1 < 2 ^ FloatFormat.prec.toNat) := by
          show ¬(2^FloatFormat.prec.toNat - 1 + 1 < 2 ^ FloatFormat.prec.toNat)
          have hpos : 0 < (2 : ℕ) ^ FloatFormat.prec.toNat := Nat.two_pow_pos _
          omega
        have hemax_neg : ¬(FiniteFp.largestFiniteFloat.e + 1 ≤ FloatFormat.max_exp) := by
          show ¬(FloatFormat.max_exp + 1 ≤ FloatFormat.max_exp)
          omega
        rw [dif_neg hsmax_neg, dif_neg hemax_neg]
      · -- Normal cross-binade
        have hE_succ_lt : b.toBitsTriple.exponent.toNat + 1 < 2 ^ FloatFormat.exponentBits := by
          have hE_lt : b.toBitsTriple.exponent.toNat < 2 ^ FloatFormat.exponentBits :=
            b.toBitsTriple.exponent.isLt
          by_contra h_neg
          push_neg at h_neg
          have hE_eq_pow : b.toBitsTriple.exponent.toNat + 1 = 2 ^ FloatFormat.exponentBits := by omega
          -- E.toNat = 2^expBits - 1 = allOnes.toNat ⇒ E = allOnes ⇒ b not finite (b.isExponentAllOnes)
          exfalso
          apply hf.1
          refine ⟨?_, ?_⟩
          · unfold FloatBits.isExponentAllOnes
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_allOnes]
            omega
          · unfold FloatBits.isTSignificandZero
            -- T ≠ 0 since T = allOnes (from hT_succ_eq_pow)
            intro hT_eq_zero
            have hT_zero_toNat : b.toBitsTriple.significand.toNat = 0 := by
              rw [hT_eq_zero]; simp
            have hsb := FloatFormat.significandBits_pos
            have hpow_lt : 1 < 2 ^ FloatFormat.significandBits :=
              calc 1 = 2 ^ 0 := by norm_num
                _ < 2 ^ FloatFormat.significandBits :=
                    Nat.pow_lt_pow_right (by norm_num) hsb
            omega
        have hres_m : b.FpSignificand + 1 = 2 ^ FloatFormat.prec.toNat := by
          rw [FloatBits.FpSignificand_def, if_neg hE_zero]
          rw [BitVec.toNat_append]
          have hT_lt : b.toBitsTriple.significand.toNat <
              2 ^ FloatFormat.significandBits := b.toBitsTriple.significand.isLt
          rw [← Nat.shiftLeft_add_eq_or_of_lt hT_lt, Nat.shiftLeft_eq]
          show (BitVec.ofBool true).toNat * 2 ^ FloatFormat.significandBits
              + b.toBitsTriple.significand.toNat + 1 = 2 ^ FloatFormat.prec.toNat
          have hbool : (BitVec.ofBool true).toNat = 1 := by simp
          have h_two_prec : (2 : ℕ) ^ FloatFormat.prec.toNat
                = 2 * 2 ^ FloatFormat.significandBits := by
            rw [← FloatFormat.one_plus_significandBits]; ring
          rw [hbool]; omega
        have he_lt : b.FpExponent + 1 ≤ FloatFormat.max_exp := by
          rw [FloatBits.FpExponent_def, if_neg hE_zero]
          -- E + 1 ≠ allOnes ⇒ (E+1).toNat ≤ allOnes.toNat - 1 = 2^expBits - 2 ⇒ E.toNat ≤ 2^expBits - 3.
          -- Or simpler: f_b.e + 1 = (E.toNat + 1) - bias ≤ ?
          -- Actually use that for std: f_b.e ≤ max_exp - 1 in this case.
          -- Specifically, (E+1).toNat ≠ allOnes.toNat.
          -- Use bit-level reasoning.
          have hE_succ_toNat : (b.toBitsTriple.exponent + 1).toNat
                = b.toBitsTriple.exponent.toNat + 1 := by
            rw [BitVec.toNat_add]
            have h_one : (1 : BitVec FloatFormat.exponentBits).toNat = 1 := by
              have hpos := FloatFormat.exponentBits_pos
              have hpow : 1 < 2 ^ FloatFormat.exponentBits :=
                calc 1 = 2 ^ 0 := by norm_num
                  _ < 2 ^ FloatFormat.exponentBits :=
                      Nat.pow_lt_pow_right (by norm_num) hpos
              show BitVec.toNat 1 = 1; simp
            rw [h_one]
            exact Nat.mod_eq_of_lt hE_succ_lt
          -- (E+1).toNat ≠ 2^expBits - 1
          have hcast : ¬((b.toBitsTriple.exponent + 1).toNat
                = (BitVec.allOnes FloatFormat.exponentBits).toNat) := by
            intro hh
            apply hE_succ_max
            exact BitVec.eq_of_toNat_eq hh
          rw [BitVec.toNat_allOnes] at hcast
          rw [hE_succ_toNat] at hcast
          show (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias + 1 ≤ FloatFormat.max_exp
          have h_max_def := StdFloatFormat.max_exp_def
          have h_expB := StdFloatFormat.exponentBits_def
          have hE_lt : b.toBitsTriple.exponent.toNat < 2 ^ FloatFormat.exponentBits :=
            b.toBitsTriple.exponent.isLt
          -- E.toNat + 1 ≠ 2^expBits - 1 and E.toNat + 1 < 2^expBits ⇒ E.toNat + 1 ≤ 2^expBits - 2
          have hE_le : b.toBitsTriple.exponent.toNat + 1 ≤ 2 ^ FloatFormat.exponentBits - 2 := by
            omega
          unfold FloatFormat.exponentBias
          have h_pow_pos := StdFloatFormat.exp_pow_pos
          have h2 : (2 : ℕ) ^ FloatFormat.exponentBits = 2 * 2 ^ StdFloatFormat.exp_pow := by
            rw [h_expB]; ring
          rw [h2] at hE_le
          have h2_pos : 1 ≤ (2 : ℕ) ^ StdFloatFormat.exp_pow := Nat.one_le_two_pow
          have hle_int : (b.toBitsTriple.exponent.toNat : ℤ) + 1
                ≤ 2 * (2 : ℤ) ^ StdFloatFormat.exp_pow - 2 := by
            -- hE_le : T.E.toNat + 1 ≤ 2 * 2^exp_pow - 2 (in ℕ)
            have h_pow_pos : 1 ≤ (2 : ℕ) ^ StdFloatFormat.exp_pow := Nat.one_le_two_pow
            have h2_pos : 2 ≤ 2 * (2 : ℕ) ^ StdFloatFormat.exp_pow := by omega
            have h_cast_int : ((2 * 2 ^ StdFloatFormat.exp_pow - 2 : ℕ) : ℤ)
                  = 2 * (2 : ℤ) ^ StdFloatFormat.exp_pow - 2 := by
              push_cast [Nat.cast_sub h2_pos]; ring
            zify at hE_le
            omega
          rw [h_max_def]
          linarith [hle_int]
        apply ofBits_bitNextUpCross_eq_successorPos_normal_cross b hs hf hE_zero
          hE_succ_lt hE_succ_max hres_m he_lt
  · -- Within-binade case: T + 1 ≠ 0
    rw [if_neg hT_max]
    have hT_succ_lt := FloatBits.T_succ_lt_of_T_succ_ne_zero b hT_max
    apply ofBits_bitNextUpWithin_eq_successorPos_within b hs hf hT_succ_lt
    exact FloatBits.FpSignificand_succ_lt_prec_of_within b hT_succ_lt

/-- **Headline master identity (positive)**: for finite positive `b`,
`nextUp` agrees with the bit-level master successor. -/
theorem nextUp_ofBits_eq_ofBits_bitNextUpPos
    [StdFloatFormat]
    (b : FloatBits) (hs : b.sign = false) (hf : b.isFinite) :
    nextUp (ofBits b) = ofBits (FloatBits.bitNextUpPos b) := by
  rw [ofBits_eq_finite_of_isFinite b hf]
  rw [FiniteFp.nextUp_finite_eq_successorPos _ hs]
  exact (ofBits_bitNextUpPos_eq_successorPos b hs hf).symm

end Fp

