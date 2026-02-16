import Flean.Operations.Mul

/-! # Exact Multiplication by a Power of Two

Multiplying a float by a power of 2 only shifts the exponent — the significand is unchanged.
If the resulting exponent is in range, the result is exactly representable with no rounding error.
-/

section MulPow2

variable [FloatFormat]

/-! ## Power-of-two float construction -/

/-- A floating-point number representing exactly `2^k`, constructed as a normal float
with the minimum normal significand `2^(prec-1)` at exponent `k`. -/
def pow2Float (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp) :
    FiniteFp :=
  ⟨false, k, 2 ^ (FloatFormat.prec - 1).toNat,
    ⟨hk_lo, hk_hi, FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec, Or.inl isNormal.sig_msb⟩⟩

/-- The value of `pow2Float k` is exactly `2^k`. -/
theorem pow2Float_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp) :
    (pow2Float k hk_lo hk_hi).toVal (R := R) = (2 : R) ^ k := by
  rw [FiniteFp.toVal_pos_eq _ (by rfl)]
  simp only [pow2Float]
  push_cast
  rw [← zpow_natCast (2 : R) (FloatFormat.prec - 1).toNat,
      FloatFormat.prec_sub_one_toNat_eq, two_zpow_mul]
  congr 1; ring

/-- The significand of `pow2Float` is positive. -/
theorem pow2Float_m_pos (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ k)
    (hk_hi : k ≤ FloatFormat.max_exp) :
    0 < (pow2Float k hk_lo hk_hi).m := by
  simp [pow2Float]

/-! ## Representability of power-of-two scaling -/

/-- Scaling a positive float by `2^k` is exactly representable when the exponent stays in range. -/
theorem mul_pow2_representable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : FiniteFp) (k : ℤ) (hf_nz : 0 < f.m) (hfs : f.s = false)
    (he_lo : f.e + k ≥ FloatFormat.min_exp) (he_hi : f.e + k ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp, g.s = false ∧ (g.toVal : R) = (f.toVal : R) * (2 : R) ^ k := by
  rw [FiniteFp.toVal_pos_eq f hfs]
  -- f.toVal * 2^k = f.m * 2^(f.e - prec + 1 + k)
  have hexp : (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) * (2 : R) ^ k =
      (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1 + k) := by
    rw [mul_assoc, two_zpow_mul]
  rw [hexp]
  exact exists_finiteFp_of_nat_mul_zpow (R := R) f.m (f.e - FloatFormat.prec + 1 + k)
    hf_nz f.valid.2.2.1
    (by omega) (by omega)

/-! ## Main exactness theorem -/

/-- Multiplying any nonzero finite float by `pow2Float k` produces an exact result
for the contextual rounding policy, provided the result exponent stays in range. -/
theorem fpMulFinite_pow2_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]
    (f : FiniteFp) (k : ℤ) (hf_nz : 0 < f.m)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp)
    (he_lo : f.e + k ≥ FloatFormat.min_exp) (he_hi : f.e + k ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp,
      f * pow2Float k hk_lo hk_hi = g ∧
        (g.toVal : R) = (f.toVal : R) * (2 : R) ^ k := by
  -- Product is nonzero because both operands are nonzero
  have hf_toVal_ne : (f.toVal : R) ≠ 0 := by
    intro h
    have := (FiniteFp.toVal_significand_zero_iff (R := R)).mpr h
    omega
  have hp_toVal_pos : (0 : R) < (pow2Float k hk_lo hk_hi).toVal := by
    rw [pow2Float_toVal]; exact two_zpow_pos' k
  have hprod_ne : (f.toVal : R) * (pow2Float k hk_lo hk_hi).toVal ≠ 0 :=
    mul_ne_zero hf_toVal_ne (ne_of_gt hp_toVal_pos)
  have hmul_corr : f * pow2Float k hk_lo hk_hi =
      ○((f.toVal : R) * (pow2Float k hk_lo hk_hi).toVal) := by
    simpa [mul_finite_eq_fpMulFinite, mul_eq_fpMul, fpMul] using
      (fpMulFinite_correct (R := R) f (pow2Float k hk_lo hk_hi) hprod_ne)
  by_cases hfs : f.s = false
  · -- Positive f
    obtain ⟨g, hgs, hgv⟩ := mul_pow2_representable (R := R) f k hf_nz hfs he_lo he_hi
    refine ⟨g, ?_, hgv⟩
    calc
      f * pow2Float k hk_lo hk_hi
          = ○((f.toVal : R) * (pow2Float k hk_lo hk_hi).toVal) := hmul_corr
      _ = ○((f.toVal : R) * (2 : R) ^ k) := by rw [pow2Float_toVal]
      _ = ○(g.toVal (R := R)) := by rw [hgv]
      _ = g := RModeIdem.round_idempotent (R := R) g (Or.inl hgs)
  · -- Negative f: work with -f which is positive
    have hfs_true : f.s = true := by revert hfs; cases f.s <;> simp
    obtain ⟨g, hgs, hgv⟩ := mul_pow2_representable (R := R) (-f) k
      (by simp; exact hf_nz) (by simp [hfs_true]) (by simp; exact he_lo) (by simp; exact he_hi)
    have hnf_pos : (0 : R) < (-f).toVal :=
      FiniteFp.toVal_pos (-f) (by simp [hfs_true]) (by simp; exact hf_nz)
    have hg_pos : (0 : R) < g.toVal := by
      rw [hgv]; exact mul_pos hnf_pos (two_zpow_pos' k)
    have hgm : 0 < g.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hg_pos).2
    have hgv_neg : g.toVal (R := R) = -(f.toVal * (2 : R) ^ k) := by
      rw [hgv, FiniteFp.toVal_neg_eq_neg]; ring
    have hng_val : (-g).toVal (R := R) = (f.toVal : R) * (2 : R) ^ k := by
      rw [FiniteFp.toVal_neg_eq_neg, hgv_neg]
      ring
    refine ⟨-g, ?_, hng_val⟩
    calc
      f * pow2Float k hk_lo hk_hi
          = ○((f.toVal : R) * (pow2Float k hk_lo hk_hi).toVal) := hmul_corr
      _ = ○((f.toVal : R) * (2 : R) ^ k) := by rw [pow2Float_toVal]
      _ = ○((-g).toVal (R := R)) := by rw [hng_val]
      _ = -g := RModeIdem.round_idempotent (R := R) (-g) (Or.inr (by simpa using hgm))

/-! ## Full fpMul wrapper -/

/-- Lifting `fpMulFinite_pow2_exact` to the full `fpMul` operation. -/
theorem fpMul_pow2_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]
    (f : FiniteFp) (k : ℤ) (hf_nz : 0 < f.m)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp)
    (he_lo : f.e + k ≥ FloatFormat.min_exp) (he_hi : f.e + k ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp,
      f * pow2Float k hk_lo hk_hi = g ∧
        (g.toVal : R) = (f.toVal : R) * (2 : R) ^ k := by
  exact fpMulFinite_pow2_exact (R := R) f k hf_nz hk_lo hk_hi he_lo he_hi

end MulPow2
