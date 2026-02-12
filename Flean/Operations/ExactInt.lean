import Flean.Operations.Sub
import Flean.Operations.Mul

/-! # Exact Integer Arithmetic

Integers in `[-2^prec, 2^prec]` are exactly representable as floats. When `+`, `-`, or `*`
on such integers produces a result also in this range, the floating-point operation is exact
(no rounding error, regardless of mode).
-/

section ExactInt

variable [FloatFormat]

/-! ## Layer 1: Integer representability -/

/-- Any positive natural number less than `2^prec` is exactly representable as a float. -/
theorem nat_representable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (n : ℕ) (hn_pos : 0 < n) (hn_bound : n < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, f.s = false ∧ 0 < f.m ∧ (f.toVal : R) = (n : R) := by
  obtain ⟨f, hfs, hfv⟩ := exists_finiteFp_of_nat_mul_zpow (R := R) n 0 hn_pos hn_bound
    (by have := FloatFormat.min_exp_nonpos; have := FloatFormat.valid_prec; omega)
    (by omega)
  have hfv' : (f.toVal : R) = (n : R) := by rw [hfv]; simp
  have hf_pos : (0 : R) < f.toVal := hfv' ▸ (by exact_mod_cast hn_pos)
  exact ⟨f, hfs, ((FiniteFp.toVal_pos_iff (R := R)).mpr hf_pos).2, hfv'⟩

/-- Any nonzero integer with absolute value less than `2^prec` is exactly representable
as a float. -/
theorem int_representable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (n : ℤ) (hn_nz : n ≠ 0) (hn_bound : n.natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, 0 < f.m ∧ (f.toVal : R) = (n : R) := by
  obtain ⟨g, hgs, hgm, hgv⟩ := nat_representable (R := R) n.natAbs
    (Int.natAbs_pos.mpr hn_nz) hn_bound h_exp
  rcases le_or_gt 0 n with hn_pos | hn_neg
  · -- n ≥ 0 (and n ≠ 0 so n > 0)
    have : (n.natAbs : R) = (n : R) := by
      rw [(Int.cast_natCast n.natAbs).symm, Int.natAbs_of_nonneg hn_pos]
    exact ⟨g, hgm, by rw [hgv, this]⟩
  · -- n < 0
    have : (n.natAbs : R) = -(n : R) := by
      rw [(Int.cast_natCast n.natAbs).symm, Int.ofNat_natAbs_of_nonpos (le_of_lt hn_neg),
          Int.cast_neg]
    exact ⟨-g, by simp; exact hgm, by rw [FiniteFp.toVal_neg_eq_neg, hgv, this]; ring⟩

/-! ## Layer 2: Rounding exactness -/

/-- Rounding any nonzero integer with `|n| < 2^prec` in any mode returns the exact value. -/
theorem int_round_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R]
    (n : ℤ) (hn_nz : n ≠ 0) (hn_bound : n.natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) (mode : RoundingMode) :
    ∃ f : FiniteFp, mode.round ((n : ℤ) : R) = Fp.finite f ∧ (f.toVal : R) = (n : R) := by
  obtain ⟨f, hfm, hfv⟩ := int_representable (R := R) n hn_nz hn_bound h_exp
  exact ⟨f, hfv ▸ round_idempotent (R := R) mode f (Or.inr hfm), hfv⟩

/-! ## Layer 3: Operation corollaries -/

/-- Floating-point addition of integer-valued operands is exact when the sum is a nonzero
integer with absolute value less than `2^prec`. -/
theorem fpAddFinite_int_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp) (n_a n_b : ℤ)
    (ha : (a.toVal : R) = (n_a : R)) (hb : (b.toVal : R) = (n_b : R))
    (hsum_nz : n_a + n_b ≠ 0)
    (hsum_bound : (n_a + n_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, fpAddFinite mode a b = Fp.finite f ∧
      (f.toVal : R) = ((n_a + n_b : ℤ) : R) := by
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by
    rw [ha, hb]; exact_mod_cast hsum_nz
  rw [fpAddFinite_correct (R := R) mode a b hsum_ne, ha, hb,
      show (n_a : R) + (n_b : R) = ((n_a + n_b : ℤ) : R) from by push_cast; ring]
  exact int_round_exact (R := R) (n_a + n_b) hsum_nz hsum_bound h_exp mode

/-- Floating-point subtraction of integer-valued operands is exact when the difference is a
nonzero integer with absolute value less than `2^prec`. -/
theorem fpSubFinite_int_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp) (n_a n_b : ℤ)
    (ha : (a.toVal : R) = (n_a : R)) (hb : (b.toVal : R) = (n_b : R))
    (hdiff_nz : n_a - n_b ≠ 0)
    (hdiff_bound : (n_a - n_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, fpSubFinite mode a b = Fp.finite f ∧
      (f.toVal : R) = ((n_a - n_b : ℤ) : R) := by
  have hdiff_ne : (a.toVal : R) - b.toVal ≠ 0 := by
    rw [ha, hb]; exact_mod_cast hdiff_nz
  rw [fpSubFinite_correct (R := R) mode a b hdiff_ne, ha, hb,
      show (n_a : R) - (n_b : R) = ((n_a - n_b : ℤ) : R) from by push_cast; ring]
  exact int_round_exact (R := R) (n_a - n_b) hdiff_nz hdiff_bound h_exp mode

/-- Floating-point multiplication of integer-valued operands is exact when the product is a
nonzero integer with absolute value less than `2^prec`. -/
theorem fpMulFinite_int_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp) (n_a n_b : ℤ)
    (ha : (a.toVal : R) = (n_a : R)) (hb : (b.toVal : R) = (n_b : R))
    (hprod_nz : n_a * n_b ≠ 0)
    (hprod_bound : (n_a * n_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, fpMulFinite mode a b = Fp.finite f ∧
      (f.toVal : R) = ((n_a * n_b : ℤ) : R) := by
  have hprod_ne : (a.toVal : R) * b.toVal ≠ 0 := by
    rw [ha, hb]; exact_mod_cast hprod_nz
  rw [fpMulFinite_correct (R := R) mode a b hprod_ne, ha, hb,
      show (n_a : R) * (n_b : R) = ((n_a * n_b : ℤ) : R) from by push_cast; ring]
  exact int_round_exact (R := R) (n_a * n_b) hprod_nz hprod_bound h_exp mode

end ExactInt
