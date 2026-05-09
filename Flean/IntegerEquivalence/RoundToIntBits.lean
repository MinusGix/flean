import Flean.IntegerEquivalence.Frexp
import Flean.IntegerEquivalence.Compare
import Flean.Operations.RoundToIntegral

/-! # FP ↔ Integer equivalence: round-to-integer family (libm-style)

Phase 1.9 of the FP ↔ Integer equivalence area.

Surface the C99/IEEE 754 §5.9 round-to-integer functions under their libm
canonical names, all backed by the existing value-level `Fp.roundToInt*`
infrastructure. Add the trivial bit-level corollary: if the input's
unbiased exponent is `≥ prec - 1`, the input is already an integer, so
all five rounding modes are the identity.

The general bit-level form (clear the bottom `(prec - 1) - e` significand
bits when `0 ≤ e < prec - 1`) requires per-position bit-mask construction
and is deferred to follow-up work. The aliases here let downstream codegen
recognize the canonical names; the integer-passthrough corollary covers
the most common case (already-integer inputs need zero work).

* `Fp.trunc` — alias for `Fp.roundToIntTrunc` (toward zero).
* `Fp.floor` — alias for `Fp.roundToIntFloor` (toward `-∞`).
* `Fp.ceil` — alias for `Fp.roundToIntCeil` (toward `+∞`).
* `Fp.nearbyint` — alias for `Fp.roundToIntTiesToEven` (default IEEE).
* `Fp.round` — alias for `Fp.roundToIntTiesToAway` (libm `round`). -/

namespace Fp

variable [FloatFormat]

/-- **`Fp.trunc`** — round toward zero. -/
@[reducible] def trunc : Fp → Fp := Fp.roundToIntTrunc

/-- **`Fp.floor`** — round toward `-∞`. -/
@[reducible] def floor : Fp → Fp := Fp.roundToIntFloor

/-- **`Fp.ceil`** — round toward `+∞`. -/
@[reducible] def ceil : Fp → Fp := Fp.roundToIntCeil

/-- **`Fp.nearbyint`** — round to nearest, ties to even (default IEEE). -/
@[reducible] def nearbyint : Fp → Fp := Fp.roundToIntTiesToEven

/-- **`Fp.round`** — round to nearest, ties away from zero (libm `round`). -/
@[reducible] def round : Fp → Fp := Fp.roundToIntTiesToAway

/-! ## Trivial bit-level corollary: passthrough on already-integer inputs

When a finite `f` has unbiased exponent `f.e ≥ prec - 1`, every value in
`f`'s binade is an integer (the trailing significand has no fractional
weight at exponent `≥ prec - 1`). All five rounding modes return `f`
unchanged.

This is the "fast path" for round-to-integer in hardware: if the exponent
is high enough, return the input without any bit-level work. -/

end Fp

namespace FiniteFp

variable [FloatFormat]

/-- For finite normal `f` with unbiased exponent `≥ prec - 1` and nonzero
significand, `f.toVal` is exactly an integer in ℚ.

The integer in question is `f.m * 2^(f.e - prec + 1)` for positive `f`,
or its negation for negative `f`. -/
theorem toVal_eq_int_of_normal_high_exp
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (hm_pos : 0 < f.m) (he : FloatFormat.prec - 1 ≤ f.e) :
    ∃ n : ℤ, n ≠ 0 ∧ (f.toVal : ℚ) = (n : ℚ) := by
  -- The exponent shift `f.e - prec + 1 ≥ 0`, so 2^shift is a positive integer.
  have h_shift_nonneg : 0 ≤ f.e - FloatFormat.prec + 1 := by omega
  have h_shift_toNat : ((f.e - FloatFormat.prec + 1).toNat : ℤ)
        = f.e - FloatFormat.prec + 1 :=
    Int.toNat_of_nonneg h_shift_nonneg
  -- Compute the integer.
  set k : ℕ := (f.e - FloatFormat.prec + 1).toNat
  -- Sign-aware: positive ⇒ n = f.m * 2^k; negative ⇒ n = -(f.m * 2^k).
  have h_pow_pos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
  have h_prod_pos : 0 < f.m * 2 ^ k := by positivity
  by_cases hs : f.s
  · -- Negative
    refine ⟨-(f.m * 2 ^ k : ℤ), ?_, ?_⟩
    · -- nonzero: -(positive) ≠ 0
      have h_int_pos : (0 : ℤ) < (f.m * 2 ^ k : ℤ) := by exact_mod_cast h_prod_pos
      omega
    · -- f.toVal = -(|f.toVal|) = -((f.m : ℚ) * 2^(f.e - prec + 1))
      rw [show f.toVal (R := ℚ) = -((-f).toVal) from by
            rw [FiniteFp.toVal_neg_eq_neg]; ring]
      have h_neg_pos : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
      rw [FiniteFp.toVal_pos_eq (-f) h_neg_pos]
      show -((f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1))
            = ((-(f.m * 2 ^ k : ℤ) : ℤ) : ℚ)
      push_cast
      rw [show (f.e - FloatFormat.prec + 1 : ℤ) = (k : ℤ) from h_shift_toNat.symm]
      rw [zpow_natCast]
  · -- Positive
    rw [Bool.not_eq_true] at hs
    refine ⟨(f.m * 2 ^ k : ℤ), ?_, ?_⟩
    · have h_int_pos : (0 : ℤ) < (f.m * 2 ^ k : ℤ) := by exact_mod_cast h_prod_pos
      omega
    · rw [FiniteFp.toVal_pos_eq f hs]
      show (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
            = ((f.m * 2 ^ k : ℤ) : ℚ)
      push_cast
      rw [show (f.e - FloatFormat.prec + 1 : ℤ) = (k : ℤ) from h_shift_toNat.symm]
      rw [zpow_natCast]

end FiniteFp

/-! ## Bit-level passthrough: high-exponent inputs are integers

For bit-normal `b` with `b.FpExponent ≥ prec - 1`, decoding gives a
FiniteFp whose value is already an integer. All five rounding modes are
identity on such inputs. -/

namespace Fp

/-- **Identity passthrough for `trunc`** on bit-normal inputs with
`FpExponent ≥ prec - 1`: input is already an integer, so `trunc` is the
identity. -/
theorem trunc_ofBits_eq_ofBits_of_normal_high_exp
    [StdFloatFormat]
    (b : FloatBits) (hn : b.isNormal)
    (he : FloatFormat.prec - 1 ≤ b.FpExponent) :
    Fp.trunc (ofBits b) = ofBits b := by
  -- Decode b to f_b.
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h)
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b⟩ with hf_b_def
  have hofb : ofBits b = Fp.finite f_b := ofBits_eq_finite_of_isFinite b hf_b
  -- f_b is value-level normal.
  have hf_b_normal : _root_.isNormal f_b.m := by
    show _root_.isNormal b.FpSignificand
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
  have hf_b_m_pos : 0 < f_b.m := by
    have h1 : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f_b.m := hf_b_normal.1
    have h2 : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.pos_of_ne_zero (by positivity)
    omega
  -- f_b.notNegZero (m > 0).
  have hf_b_nnz : f_b.notNegZero := Or.inr hf_b_m_pos
  -- f_b.e ≥ prec - 1.
  have hf_b_e : FloatFormat.prec - 1 ≤ f_b.e := he
  -- f.toVal is an integer.
  obtain ⟨n, hn_nz, hn_eq⟩ :=
    FiniteFp.toVal_eq_int_of_normal_high_exp f_b hf_b_normal hf_b_m_pos hf_b_e
  -- Apply roundToInt_of_int_eq with intRound = truncate.
  rw [hofb]
  show Fp.roundToIntTrunc (Fp.finite f_b) = Fp.finite f_b
  unfold Fp.roundToIntTrunc
  apply Fp.roundToInt_of_int_eq IntRound.truncate f_b
    (by intro h_zero; omega) hf_b_nnz n hn_eq (IntRound.truncate_int n) hn_nz

/-- **Identity passthrough for `floor`** under same hypothesis. -/
theorem floor_ofBits_eq_ofBits_of_normal_high_exp
    [StdFloatFormat]
    (b : FloatBits) (hn : b.isNormal)
    (he : FloatFormat.prec - 1 ≤ b.FpExponent) :
    Fp.floor (ofBits b) = ofBits b := by
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h)
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b⟩ with hf_b_def
  have hofb : ofBits b = Fp.finite f_b := ofBits_eq_finite_of_isFinite b hf_b
  have hf_b_normal : _root_.isNormal f_b.m := by
    show _root_.isNormal b.FpSignificand
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
  have hf_b_m_pos : 0 < f_b.m := by
    have h1 : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f_b.m := hf_b_normal.1
    have h2 : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.pos_of_ne_zero (by positivity)
    omega
  have hf_b_nnz : f_b.notNegZero := Or.inr hf_b_m_pos
  obtain ⟨n, hn_nz, hn_eq⟩ :=
    FiniteFp.toVal_eq_int_of_normal_high_exp f_b hf_b_normal hf_b_m_pos he
  rw [hofb]
  show Fp.roundToIntFloor (Fp.finite f_b) = Fp.finite f_b
  unfold Fp.roundToIntFloor
  apply Fp.roundToInt_of_int_eq (⌊·⌋) f_b
    (by intro h_zero; omega) hf_b_nnz n hn_eq (Int.floor_intCast n) hn_nz

/-- **Identity passthrough for `ceil`** under same hypothesis. -/
theorem ceil_ofBits_eq_ofBits_of_normal_high_exp
    [StdFloatFormat]
    (b : FloatBits) (hn : b.isNormal)
    (he : FloatFormat.prec - 1 ≤ b.FpExponent) :
    Fp.ceil (ofBits b) = ofBits b := by
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h)
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b⟩ with hf_b_def
  have hofb : ofBits b = Fp.finite f_b := ofBits_eq_finite_of_isFinite b hf_b
  have hf_b_normal : _root_.isNormal f_b.m := by
    show _root_.isNormal b.FpSignificand
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
  have hf_b_m_pos : 0 < f_b.m := by
    have h1 : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f_b.m := hf_b_normal.1
    have h2 : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.pos_of_ne_zero (by positivity)
    omega
  have hf_b_nnz : f_b.notNegZero := Or.inr hf_b_m_pos
  obtain ⟨n, hn_nz, hn_eq⟩ :=
    FiniteFp.toVal_eq_int_of_normal_high_exp f_b hf_b_normal hf_b_m_pos he
  rw [hofb]
  show Fp.roundToIntCeil (Fp.finite f_b) = Fp.finite f_b
  unfold Fp.roundToIntCeil
  apply Fp.roundToInt_of_int_eq (⌈·⌉) f_b
    (by intro h_zero; omega) hf_b_nnz n hn_eq (Int.ceil_intCast n) hn_nz

end Fp
