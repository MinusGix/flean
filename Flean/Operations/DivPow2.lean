import Flean.Operations.MulPow2
import Flean.Operations.Div

/-! # Exact Division by a Power of Two

Dividing a float by a power of 2 only shifts the exponent — the significand is unchanged.
If the resulting exponent is in range, the result is exactly representable with no rounding error.

The key reduction is `x / 2^k = x * 2^(-k)`, which lets us reuse `mul_pow2_representable`.
-/

section DivPow2

variable [FloatFormat]

/-- Dividing any nonzero finite float by `pow2Float k` produces an exact result (no rounding
error) for every rounding mode, provided the result exponent stays in range. -/
theorem fpDivFinite_pow2_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R]
    (f : FiniteFp) (k : ℤ) (hf_nz : 0 < f.m)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp)
    (he_lo : f.e - k ≥ FloatFormat.min_exp) (he_hi : f.e - k ≤ FloatFormat.max_exp) :
    ∀ mode, ∃ g : FiniteFp,
      fpDivFinite mode f (pow2Float k hk_lo hk_hi) = Fp.finite g ∧
        (g.toVal : R) = (f.toVal : R) / (2 : R) ^ k := by
  -- Key reduction: x / 2^k = x * 2^(-k)
  have hdiv_eq : ∀ (x : R), x / (2 : R) ^ k = x * (2 : R) ^ (-k) := fun x => by
    rw [zpow_neg, div_eq_mul_inv]
  -- Nonzero conditions
  have hb_nz : (pow2Float k hk_lo hk_hi).m ≠ 0 := (pow2Float_m_pos k hk_lo hk_hi).ne'
  have hf_ne : (f.toVal : R) ≠ 0 := by
    intro h; have := (FiniteFp.toVal_significand_zero_iff (R := R)).mpr h; omega
  have hquot_ne : (f.toVal : R) / (pow2Float k hk_lo hk_hi).toVal ≠ 0 := by
    rw [pow2Float_toVal]; exact div_ne_zero hf_ne (zpow_ne_zero _ (by norm_num))
  by_cases hfs : f.s = false
  · -- Positive f: mul_pow2_representable gives exact representative
    obtain ⟨g, hgs, hgv⟩ := mul_pow2_representable (R := R) f (-k) hf_nz hfs
      (by omega) (by omega)
    intro mode; refine ⟨g, ?_, by rw [hgv, ← hdiv_eq]⟩
    rw [fpDivFinite_correct (R := R) mode f _ hb_nz hquot_ne, pow2Float_toVal, hdiv_eq,
        show (f.toVal : R) * (2 : R) ^ (-k) = g.toVal from hgv.symm]
    exact round_idempotent (R := R) mode g (Or.inl hgs)
  · -- Negative f: use -f which is positive
    have hfs_true : f.s = true := by revert hfs; cases f.s <;> simp
    obtain ⟨g, hgs, hgv⟩ := mul_pow2_representable (R := R) (-f) (-k)
      (by simp; exact hf_nz) (by simp [hfs_true]) (by simp; omega) (by simp; omega)
    have hnf_pos : (0 : R) < (-f).toVal :=
      FiniteFp.toVal_pos (-f) (by simp [hfs_true]) (by simp; exact hf_nz)
    have hg_pos : (0 : R) < g.toVal := by
      rw [hgv]; exact mul_pos hnf_pos (two_zpow_pos' (-k))
    have hgm : 0 < g.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hg_pos).2
    have hgv_neg : g.toVal (R := R) = -(f.toVal / (2 : R) ^ k) := by
      rw [hgv, FiniteFp.toVal_neg_eq_neg, neg_mul, ← hdiv_eq]
    intro mode
    obtain ⟨hrnd, hval⟩ := round_neg_exact (R := R) mode _ g hgs hgm hgv_neg
    exact ⟨-g,
      by rw [fpDivFinite_correct (R := R) mode f _ hb_nz hquot_ne, pow2Float_toVal]; exact hrnd,
      hval⟩

/-- Lifting `fpDivFinite_pow2_exact` to the full `fpDiv` operation. -/
theorem fpDiv_pow2_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R]
    (f : FiniteFp) (k : ℤ) (hf_nz : 0 < f.m)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp)
    (he_lo : f.e - k ≥ FloatFormat.min_exp) (he_hi : f.e - k ≤ FloatFormat.max_exp) :
    ∀ mode, ∃ g : FiniteFp,
      fpDiv mode (.finite f) (.finite (pow2Float k hk_lo hk_hi)) = Fp.finite g ∧
        (g.toVal : R) = (f.toVal : R) / (2 : R) ^ k := by
  intro mode
  simp only [fpDiv]
  rw [if_neg (pow2Float_m_pos k hk_lo hk_hi).ne']
  exact fpDivFinite_pow2_exact (R := R) f k hf_nz hk_lo hk_hi he_lo he_hi mode

end DivPow2
