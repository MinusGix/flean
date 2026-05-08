import Flean.Operations.MulPow2
import Flean.Operations.Div

/-! # Exact Division by a Power of Two

Dividing a float by a power of 2 only shifts the exponent — the significand is unchanged.
If the resulting exponent is in range, the result is exactly representable with no rounding error.

The key reduction is `x / 2^k = x * 2^(-k)`, which lets us reuse `mul_pow2_representable`.
-/

section DivPow2

variable [FloatFormat]

/-- Dividing any nonzero finite float by `pow2Float k` produces an exact result
for the contextual rounding policy, provided the result exponent stays in range. -/
theorem fpDivFinite_pow2_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]
    (f : FiniteFp) (k : ℤ) (hf_nz : 0 < f.m)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp)
    (he_lo : f.e - k ≥ FloatFormat.min_exp) (he_hi : f.e - k ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp,
      f / pow2Float k hk_lo hk_hi = g ∧
        (g.toVal : R) = (f.toVal : R) / (2 : R) ^ k := by
  -- Key reduction: x / 2^k = x * 2^(-k)
  have hdiv_eq : ∀ (x : R), x / (2 : R) ^ k = x * (2 : R) ^ (-k) := fun x => by
    rw [zpow_neg, div_eq_mul_inv]
  -- Nonzero conditions
  have hb_nz : (pow2Float k hk_lo hk_hi).m ≠ 0 := (pow2Float_m_pos k hk_lo hk_hi).ne'
  have hpow2_m : (pow2Float k hk_lo hk_hi).m = 2 ^ (FloatFormat.prec - 1).toNat := by
    rfl
  have hshift_ge : (FloatFormat.prec - 1).toNat ≤ divShift := by
    rw [divShift, FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
    omega
  have hpow_dvd : 2 ^ (FloatFormat.prec - 1).toNat ∣ 2 ^ divShift := by
    refine ⟨2 ^ (divShift - (FloatFormat.prec - 1).toNat), ?_⟩
    calc
      2 ^ divShift
          = 2 ^ ((FloatFormat.prec - 1).toNat + (divShift - (FloatFormat.prec - 1).toNat)) := by
              rw [Nat.add_sub_of_le hshift_ge]
      _ = 2 ^ (FloatFormat.prec - 1).toNat * 2 ^ (divShift - (FloatFormat.prec - 1).toNat) := by
            rw [Nat.pow_add]
  have hscaled_dvd : 2 ^ (FloatFormat.prec - 1).toNat ∣ f.m * 2 ^ divShift :=
    dvd_mul_of_dvd_right hpow_dvd f.m
  have hexact : (f.m * 2 ^ divShift) % (pow2Float k hk_lo hk_hi).m = 0 := by
    rw [hpow2_m]
    exact Nat.mod_eq_zero_of_dvd hscaled_dvd
  have hf_ne : (f.toVal : R) ≠ 0 := by
    intro h; have := (FiniteFp.toVal_significand_zero_iff (R := R)).mpr h; omega
  have hquot_ne : (f.toVal : R) / (pow2Float k hk_lo hk_hi).toVal ≠ 0 := by
    rw [pow2Float_toVal]; exact div_ne_zero hf_ne (zpow_ne_zero _ (by norm_num))
  have hdiv_corr := fpDivFinite_correct_exact (R := R) f (pow2Float k hk_lo hk_hi) hb_nz hquot_ne hexact
  simp only [div_finite_eq_fpDivFinite, div_eq_fpDiv, fpDiv,
    (pow2Float_m_pos k hk_lo hk_hi).ne', ite_false] at hdiv_corr
  -- hdiv_corr : fpDivFinite f (pow2Float k hk_lo hk_hi) = ○(...)
  by_cases hfs : f.s = false
  · -- Positive f: mul_pow2_representable gives exact representative
    obtain ⟨g, hgs, hgv⟩ := mul_pow2_representable (R := R) f (-k) hf_nz hfs
      (by omega) (by omega)
    refine ⟨g, ?_, by rw [hgv, ← hdiv_eq]⟩
    simp only [div_finite_eq_fpDivFinite] at ⊢
    rw [hdiv_corr, pow2Float_toVal, hdiv_eq,
        show (f.toVal : R) * (2 : R) ^ (-k) = g.toVal from hgv.symm]
    exact RModeIdem.round_idempotent (R := R) g (Or.inl hgs)
  · -- Negative f: use -f which is positive
    have hfs_true : f.s = true := by revert hfs; cases f.s <;> simp
    obtain ⟨g, hgs, hgv⟩ := mul_pow2_representable (R := R) (-f) (-k)
      (by simp; exact hf_nz) (by simp [hfs_true]) (by simp; omega) (by simp; omega)
    have hnf_pos : (0 : R) < (-f).toVal :=
      FiniteFp.toVal_pos (-f) (by simp [hfs_true]) (by simp; exact hf_nz)
    have hg_pos : (0 : R) < g.toVal := by
      rw [hgv]; exact mul_pos hnf_pos (by positivity)
    have hgm : 0 < g.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hg_pos).2
    have hgv_neg : g.toVal (R := R) = -(f.toVal / (2 : R) ^ k) := by
      rw [hgv, FiniteFp.toVal_neg_eq_neg, neg_mul, ← hdiv_eq]
    have hng_val : (-g).toVal (R := R) = (f.toVal : R) / (2 : R) ^ k := by
      rw [FiniteFp.toVal_neg_eq_neg, hgv_neg]
      ring
    refine ⟨-g, ?_, hng_val⟩
    simp only [div_finite_eq_fpDivFinite] at ⊢
    rw [hdiv_corr, pow2Float_toVal, ← hng_val]
    exact RModeIdem.round_idempotent (R := R) (-g) (Or.inr (by simpa using hgm))

/-- Lifting `fpDivFinite_pow2_exact` to the full `fpDiv` operation. -/
theorem fpDiv_pow2_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]
    (f : FiniteFp) (k : ℤ) (hf_nz : 0 < f.m)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp)
    (he_lo : f.e - k ≥ FloatFormat.min_exp) (he_hi : f.e - k ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp,
      f / pow2Float k hk_lo hk_hi = g ∧
        (g.toVal : R) = (f.toVal : R) / (2 : R) ^ k := by
  exact fpDivFinite_pow2_exact (R := R) f k hf_nz hk_lo hk_hi he_lo he_hi

/-! ## Structural exactness: explicit `⟨s, e-k, m⟩` form

Mirror of `fpMul_pow2_normal_eq`. When `f` is normal and the *shifted-down*
exponent stays in normal range, dividing `f` by `pow2Float k` yields exactly
the FiniteFp with the same sign and significand and exponent shifted by `-k`.
This is the value-level statement of "FP divide by `2^k` is exactly an
exponent shift". -/

/-- **Structural** `fpDiv`-by-power-of-2 exactness: when `f` is normal and
the result exponent `f.e - k` stays in normal range, the quotient equals the
explicit FiniteFp with the same sign and significand and exponent shifted by
`-k`. -/
theorem fpDiv_pow2_normal_eq {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeIdem R]
    (f : FiniteFp) (k : ℤ) (hf_normal : _root_.isNormal f.m)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp)
    (hres_lo : FloatFormat.min_exp ≤ f.e - k)
    (hres_hi : f.e - k ≤ FloatFormat.max_exp) :
    f / pow2Float k hk_lo hk_hi =
      (Fp.finite ⟨f.s, f.e - k, f.m,
        isValidFiniteVal_shift_normal (k := -k) hf_normal
          (by linarith) (by linarith)⟩ : Fp) := by
  set f' : FiniteFp := ⟨f.s, f.e - k, f.m,
    isValidFiniteVal_shift_normal (k := -k) hf_normal
      (by linarith) (by linarith)⟩ with hf'_def
  have hf_nz : 0 < f.m := by
    have h1 : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f.m := hf_normal.1
    have h2 : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.pos_of_ne_zero (by positivity)
    omega
  obtain ⟨g, hgM, hgV⟩ := fpDivFinite_pow2_exact (R := R) f k hf_nz hk_lo hk_hi
    hres_lo hres_hi
  -- f'.toVal = f.toVal / 2^k
  have htwo_ne : (2 : R) ≠ 0 := by norm_num
  have hzpow_ne : (2 : R) ^ k ≠ 0 := zpow_ne_zero _ htwo_ne
  have hf'_toVal : (f'.toVal : R) = (f.toVal : R) / (2 : R) ^ k := by
    by_cases hs : f.s = false
    · have hf's : f'.s = false := hs
      rw [FiniteFp.toVal_pos_eq f' hf's, FiniteFp.toVal_pos_eq f hs]
      show (f.m : R) * (2 : R) ^ (f.e - k - FloatFormat.prec + 1)
          = (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) / (2 : R) ^ k
      rw [show (f.e - k - FloatFormat.prec + 1 : ℤ)
            = (f.e - FloatFormat.prec + 1) + (-k) from by ring,
          zpow_add₀ htwo_ne, zpow_neg]
      field_simp
    · have hfs_t : f.s = true := by cases h : f.s <;> simp_all
      have hf's_t : f'.s = true := hfs_t
      have hnf_pos : (-f).s = false := by simp [hfs_t]
      have hnf'_pos : (-f').s = false := by simp [hf's_t]
      rw [show f'.toVal (R := R) = -((-f').toVal)
            from by rw [FiniteFp.toVal_neg_eq_neg]; ring,
          show f.toVal (R := R) = -((-f).toVal)
            from by rw [FiniteFp.toVal_neg_eq_neg]; ring,
          FiniteFp.toVal_pos_eq (-f') hnf'_pos,
          FiniteFp.toVal_pos_eq (-f) hnf_pos]
      show -((f.m : R) * (2 : R) ^ (f.e - k - FloatFormat.prec + 1))
          = -((f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)) / (2 : R) ^ k
      rw [show (f.e - k - FloatFormat.prec + 1 : ℤ)
            = (f.e - FloatFormat.prec + 1) + (-k) from by ring,
          zpow_add₀ htwo_ne, zpow_neg]
      field_simp
  have hf'_eq_g : f' = g := by
    apply FiniteFp.eq_of_toVal_eq' (R := R) (Or.inl ?_) (hf'_toVal.trans hgV.symm)
    show f'.m ≠ 0
    show f.m ≠ 0
    omega
  -- LHS is `Fp.finite f / Fp.finite (pow2Float k) : Fp`. Reduce to `fpDivFinite`.
  have hb_nz : (pow2Float k hk_lo hk_hi).m ≠ 0 :=
    (pow2Float_m_pos k hk_lo hk_hi).ne'
  rw [fpDiv_finite_finite f (pow2Float k hk_lo hk_hi) hb_nz,
      ← div_finite_eq_fpDivFinite, hgM]
  exact congr_arg Fp.finite hf'_eq_g.symm

end DivPow2
