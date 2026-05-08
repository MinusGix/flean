import Flean.IntegerEquivalence.MulPow2
import Flean.Operations.DivPow2

/-! # FP ↔ Integer equivalence: power-of-2 division ↔ exponent shift

Phase 1 of the FP ↔ Integer equivalence area
(see `.claude/notes/fp-integer-equivalence.md`).

This file proves the bit-level statement of `fpDiv_pow2_eq_exponent_sub`:
dividing a normal FP number by `2^k` (when the result stays in normal
range) is exactly a downward shift of the biased exponent — same sign bit,
same trailing significand, biased exponent shifted by `-k`.

The workhorse `FloatBits.setBiasedExponent` is shared with the `Mul` side
(see `Flean/IntegerEquivalence/MulPow2.lean`); this file only adds the
`Div`-flavored bridge.
-/

namespace Fp

/-! ## Bridge: `setBiasedExponent` (bit-level) ↔ `fpDiv ... pow2Float k` (value-level)

For a normal `b` and a normal-range new biased exponent `E` that corresponds to
*subtracting* `k` from `b`'s biased exponent, decoding `setBiasedExponent E b`
agrees with dividing `ofBits b` by `pow2Float k`. -/

/-- `b.FpExponent` for a bit-level normal `b` equals `b.toBitsTriple.exponent.toNat
- exponentBias`. -/
private theorem FpExponent_of_normal' [FloatFormat] (b : FloatBits)
    (hn : b.toBitsTriple.exponent ≠ 0) :
    b.FpExponent = (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias := by
  rw [FloatBits.FpExponent_def, if_neg hn]

/-- A bit-level normal `b` has `FpSignificand` in the value-level normal range. -/
private theorem isNormal_FpSignificand_of_isNormal' [StdFloatFormat] {b : FloatBits}
    (hn : b.isNormal) :
    _root_.isNormal b.FpSignificand := by
  refine ⟨?_, ?_⟩
  · rw [FloatBits.FpSignificand_def, if_neg hn.1]
    have hmsb : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).msb = true := by
      simp [BitVec.msb, BitVec.getMsbD, BitVec.ofBool_true, BitVec.getLsbD_append]
    have hge := BitVec.toNat_ge_of_msb_true hmsb
    have h_eq : 1 + FloatFormat.significandBits - 1 = FloatFormat.significandBits := by
      have := FloatFormat.significandBits_pos; omega
    rw [h_eq] at hge
    exact hge
  · rw [FloatBits.FpSignificand_def, if_neg hn.1]
    have h_lt := ((BitVec.ofBool true) ++ b.toBitsTriple.significand).isLt
    exact h_lt.trans_eq (congr_arg (2 ^ ·) FloatFormat.one_plus_significandBits)

/-- The structural form of `b`'s value when `b` is bit-level normal: it decodes
to a `FiniteFp` with explicit fields. -/
private theorem ofBits_eq_of_normal' [StdFloatFormat] (b : FloatBits)
    (hn : b.isNormal) (hf : b.isFinite) :
    ofBits b = Fp.finite ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal hf⟩ := by
  have hni : ¬b.isNaN := fun ⟨h, _⟩ => hn.2 h
  have hii : ¬b.isInfinite := fun ⟨h, _⟩ => hn.2 h
  have h_step : ofBits b
      = Fp.finite ⟨b.toBitsTriple.sign.toNat == 1, b.FpExponent, b.FpSignificand,
          FloatBits.isFinite_validFloatVal hf⟩ := by
    unfold ofBits; rw [dif_neg hni, dif_neg hii]
  rw [h_step]
  congr 1
  apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, rfl, rfl⟩
  show (b.toBitsTriple.sign.toNat == 1) = b.sign
  unfold FloatBits.sign
  rcases BitVec.one_or b.toBitsTriple.sign with h | h <;> rw [h] <;> rfl

/-- **Bit-level statement of `fpDiv_pow2_eq_exponent_sub`.**

For a bit-level normal `FloatBits` `b` and a new biased exponent `E` that is
also normal-range and corresponds to bumping `b`'s biased exponent *down* by
`k`, decoding `setBiasedExponent E b` agrees with dividing `ofBits b` by
`pow2Float k`.

The "result is normal" hypothesis is split into:
* `hn_b : b.isNormal` (input is normal),
* `hE_nz` and `hE_not_allOnes` (new biased exponent is normal-range).
-/
theorem ofBits_setBiasedExponent_eq_fpDiv_pow2
    [StdFloatFormat] {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeIdem R]
    (b : FloatBits) (k : ℤ) (E : BitVec FloatFormat.exponentBits)
    (hn_b : b.isNormal)
    (hE_nz : E ≠ 0)
    (hE_not_allOnes : E ≠ BitVec.allOnes FloatFormat.exponentBits)
    (hE_diff : (E.toNat : ℤ) = b.toBitsTriple.exponent.toNat - k)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp) :
    ofBits (FloatBits.setBiasedExponent E b)
      = fpDiv (ofBits b) (Fp.finite (pow2Float k hk_lo hk_hi)) := by
  -- Decode b into a normal FiniteFp
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn_b.2 h) (fun ⟨h, _⟩ => hn_b.2 h)
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b⟩ with hf_b_def
  have hofBits_b : ofBits b = Fp.finite f_b := ofBits_eq_of_normal' b hn_b hf_b
  -- f_b is value-level normal (so we can use fpDiv_pow2_normal_eq)
  have hf_b_normal : _root_.isNormal f_b.m := isNormal_FpSignificand_of_isNormal' hn_b
  -- The shifted FloatBits is also bit-level normal (and finite)
  have hn_new : (FloatBits.setBiasedExponent E b).isNormal :=
    FloatBits.setBiasedExponent_isNormal E b hE_nz hE_not_allOnes
  set b' := FloatBits.setBiasedExponent E b with hb'_def
  have hf_b' : b'.isFinite :=
    FloatBits.setBiasedExponent_isFinite E b hE_not_allOnes
  have hofBits_b' : ofBits b' = Fp.finite ⟨b'.sign, b'.FpExponent, b'.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b'⟩ :=
    ofBits_eq_of_normal' b' hn_new hf_b'
  -- Compute b'.sign, b'.FpExponent, b'.FpSignificand from b
  have hb'_sign : b'.sign = b.sign := FloatBits.setBiasedExponent_sign E b
  have hb'_FpExp : b'.FpExponent = f_b.e - k := by
    rw [FloatBits.setBiasedExponent_FpExponent_of_E_nz E b hE_nz]
    show (E.toNat : ℤ) - FloatFormat.exponentBias = f_b.e - k
    rw [hE_diff]
    show (b.toBitsTriple.exponent.toNat : ℤ) - k - FloatFormat.exponentBias = f_b.e - k
    have : f_b.e = (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias :=
      FpExponent_of_normal' b hn_b.1
    linarith
  have hb'_FpSig : b'.FpSignificand = f_b.m :=
    FloatBits.setBiasedExponent_FpSignificand_of_normal E b hn_b.1 hE_nz
  -- Result-side preconditions for fpDiv_pow2_normal_eq, derived from b' being finite
  have hvalid_b' : IsValidFiniteVal b'.FpExponent b'.FpSignificand :=
    FloatBits.isFinite_validFloatVal hf_b'
  have hres_lo : FloatFormat.min_exp ≤ f_b.e - k := hb'_FpExp ▸ hvalid_b'.1
  have hres_hi : f_b.e - k ≤ FloatFormat.max_exp := hb'_FpExp ▸ hvalid_b'.2.1
  -- Apply structural fpDiv_pow2 theorem
  have hfpDiv_eq :
      f_b / pow2Float k hk_lo hk_hi
        = (Fp.finite ⟨f_b.s, f_b.e - k, f_b.m,
            isValidFiniteVal_shift_normal (k := -k) hf_b_normal
              (by linarith) (by linarith)⟩ : Fp) :=
    fpDiv_pow2_normal_eq (R := R) f_b k hf_b_normal hk_lo hk_hi hres_lo hres_hi
  -- Combine: LHS decode + RHS via Fp-level div + structural theorem
  rw [hofBits_b, ← div_eq_fpDiv, hfpDiv_eq, hofBits_b']
  -- Goal: Fp.finite ⟨b'.sign, b'.FpExponent, b'.FpSignificand, _⟩
  --     = Fp.finite ⟨f_b.s, f_b.e - k, f_b.m, _⟩
  congr 1
  apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · show b'.sign = f_b.s
    rw [hb'_sign]
  · exact hb'_FpExp
  · exact hb'_FpSig

end Fp
