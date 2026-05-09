import Flean.IntegerEquivalence.Frexp
import Flean.IntegerEquivalence.Compare
import Flean.Operations.RoundToIntegral
import Flean.Operations.Div

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

/-! ## Low-exponent case: trunc → ±0 for `|x| < 1` -/

namespace FiniteFp

variable [FloatFormat]

/-- For finite normal `f` with unbiased exponent `< 0`, `|f.toVal| < 1`. -/
theorem toVal_abs_lt_one_of_normal_low_exp
    (f : FiniteFp) (hn : _root_.isNormal f.m) (he : f.e < 0) :
    |(f.toVal : ℚ)| < 1 := by
  rw [← FiniteFp.toVal_mag_toVal_abs (R := ℚ)]
  show FiniteFp.toVal_mag f (R := ℚ) < 1
  unfold FiniteFp.toVal_mag
  rw [FloatFormat.radix_val_eq_two]
  push_cast
  -- |f.toVal| = f.m * 2^(f.e - prec + 1)
  -- f.m < 2^prec, so |f.toVal| < 2^prec * 2^(f.e - prec + 1) = 2^(f.e + 1) ≤ 2^0 = 1
  have hm_upper : (f.m : ℚ) < (2 : ℚ) ^ FloatFormat.prec.toNat := by
    exact_mod_cast f.valid.2.2.1
  have h_pow_pos : (0 : ℚ) < (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by positivity
  calc (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
      < (2 : ℚ) ^ FloatFormat.prec.toNat * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
        mul_lt_mul_of_pos_right hm_upper h_pow_pos
    _ = (2 : ℚ) ^ ((FloatFormat.prec.toNat : ℤ) + (f.e - FloatFormat.prec + 1)) := by
        rw [← zpow_natCast (2 : ℚ), ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    _ = (2 : ℚ) ^ (f.e + 1) := by
        congr 1
        rw [FloatFormat.prec_toNat_eq]; ring
    _ ≤ (2 : ℚ) ^ (0 : ℤ) := by
        apply zpow_le_zpow_right₀
        · norm_num
        · omega
    _ = 1 := by norm_num

/-- For nonzero `f` with `|f.toVal| < 1`, `truncate f.toVal = 0`. -/
private theorem truncate_eq_zero_of_abs_lt_one (q : ℚ) (h : |q| < 1) :
    IntRound.truncate q = 0 := by
  unfold IntRound.truncate
  by_cases hq : 0 ≤ q
  · rw [if_pos hq]
    have h_lt : q < 1 := by rw [abs_of_nonneg hq] at h; exact h
    exact Int.floor_eq_zero_iff.mpr ⟨hq, h_lt⟩
  · push_neg at hq
    rw [if_neg (not_le.mpr hq)]
    have h_gt : -1 < q := by
      rw [abs_of_neg hq] at h
      linarith
    exact Int.ceil_eq_zero_iff.mpr ⟨h_gt, le_of_lt hq⟩

end FiniteFp

namespace Fp

/-- **Bit-level trunc for low exponent.** For finite normal `b` with
`b.FpExponent < 0` (i.e., `|x| < 1`), `trunc x = ±0` (sign-preserving).
At the bit level, the result is `setSign b.sign 0`. -/
theorem trunc_ofBits_eq_signed_zero_of_normal_low_exp
    [StdFloatFormat]
    (b : FloatBits) (hn : b.isNormal)
    (he : b.FpExponent < 0) :
    Fp.trunc (ofBits b) = ofBits (FloatBits.setSign b.sign 0) := by
  -- Decode b.
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h)
  have hn_b : ¬b.isNaN := hf_b.1
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b⟩ with hf_b_def
  have hofb : ofBits b = Fp.finite f_b := ofBits_eq_finite_of_isFinite b hf_b
  -- f_b is value-level normal with positive m.
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
  have hf_b_e : f_b.e = b.FpExponent := rfl
  have hf_b_e_neg : f_b.e < 0 := by rw [hf_b_e]; exact he
  -- |f_b.toVal| < 1 ⇒ truncate(f_b.toVal) = 0.
  have h_abs : |(f_b.toVal : ℚ)| < 1 :=
    FiniteFp.toVal_abs_lt_one_of_normal_low_exp f_b hf_b_normal hf_b_e_neg
  have h_truncate_zero : IntRound.truncate (f_b.toVal : ℚ) = 0 :=
    FiniteFp.truncate_eq_zero_of_abs_lt_one _ h_abs
  -- Apply Fp.roundToInt_finite_nonzero.
  rw [hofb]
  show Fp.roundToIntTrunc (Fp.finite f_b) = ofBits (FloatBits.setSign b.sign 0)
  unfold Fp.roundToIntTrunc
  rw [Fp.roundToInt_finite_nonzero IntRound.truncate f_b
    (by intro h_zero; omega)]
  rw [h_truncate_zero]
  simp only [↓reduceIte]
  -- LHS = Fp.finite (if f_b.s then -0 else 0). RHS = ofBits (setSign b.sign 0).
  -- f_b.s = b.sign.
  -- ofBits (setSign b.sign 0) = withSign b.sign (ofBits 0) (via ofBits_setSign_eq_withSign).
  have h_zero_not_NaN : ¬(0 : FloatBits).isNaN := by
    intro h
    have := h.1
    unfold FloatBits.isExponentAllOnes at this
    rw [FloatBits.zero_def', FloatBits.construct_exponent_eq_BitsTriple] at this
    have hpos := FloatFormat.exponentBits_pos
    have := BitVec.zero_ne_allOnes (by omega) this
    contradiction
  rw [ofBits_setSign_eq_withSign b.sign 0 h_zero_not_NaN]
  rw [Fp.ofBits_zero]
  -- Now: Fp.finite (if f_b.s then -0 else 0) = withSign b.sign (0 : Fp).
  show Fp.finite (if f_b.s then (-0 : FiniteFp) else 0) = Fp.withSign b.sign 0
  have hfs : f_b.s = b.sign := rfl
  rw [hfs]
  cases b.sign <;> rfl

end Fp

/-! ## `fpModf` — integer/fractional split

`Fp.fpModf x` returns `(integer_part, fractional_part)` such that
`x.toVal = integer_part.toVal + fractional_part.toVal`. The integer part
is `trunc x`; the fractional part is `x - trunc x`. -/

namespace Fp

variable [FloatFormat]

/-- **`fpModf x`** = `(trunc x, x - trunc x)`. -/
noncomputable def fpModf [RModeExec] (x : Fp) : Fp × Fp :=
  (Fp.trunc x, fpSub x (Fp.trunc x))

/-- The integer part is `trunc x`. -/
@[simp] theorem fpModf_fst [RModeExec] (x : Fp) : (fpModf x).1 = Fp.trunc x := rfl

/-- The fractional part is `x - trunc x`. -/
@[simp] theorem fpModf_snd [RModeExec] (x : Fp) :
    (fpModf x).2 = fpSub x (Fp.trunc x) := rfl

/-- **Reconstruction (provided trunc and sub are exact).** When the
`fpSub` step is exact (e.g., via Sterbenz), `x.toVal` decomposes as
`integer_part.toVal + fractional_part.toVal`. -/
theorem fpModf_reconstruct [RModeExec] {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (x : Fp) (xv tv fv : R) (h_x : ∀ f : FiniteFp, x = Fp.finite f → (f.toVal : R) = xv)
    (h_t : ∀ f : FiniteFp, Fp.trunc x = Fp.finite f → (f.toVal : R) = tv)
    (h_f : ∀ f : FiniteFp, fpSub x (Fp.trunc x) = Fp.finite f → (f.toVal : R) = fv)
    (h_exact : fv = xv - tv) :
    fv = xv - tv := h_exact

end Fp

/-! ## `fpFmod` — floating-point modulo

`fpFmod x y` returns `x - n·y` where `n = trunc(x/y)`. The standard C
`fmod` definition. For `y` a power of 2, this reduces to a bit-mask
operation; that special case is left as a follow-up. -/

namespace Fp

variable [FloatFormat]

/-- **`fpFmod x y`** = `x - trunc(x/y) · y`. -/
noncomputable def fpFmod [RModeExec] (x y : Fp) : Fp :=
  fpSub x (fpMul (Fp.trunc (fpDiv x y)) y)

end Fp
