import Flean.Operations.MulErrorRepresentable

/-! # TwoProduct: Error-Free Transformation for Multiplication

TwoProduct recovers the exact rounding error of floating-point multiplication.
Given `p = fl(a × b)`, the FMA computes `e = fma(a, b, -p)` such that
`p + e = a × b` exactly. This is the multiplicative analogue of TwoSum and a
foundational building block for compensated dot products and double-double arithmetic.

The key condition `fmaProdE a b ≥ min_exp` prevents severe underflow: without it,
the product can lose more than prec bits during subnormal rounding, making the
error unrepresentable.
-/

section TwoProduct

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- **TwoProduct correctness**.

For any two nonzero finite floats whose product doesn't severely underflow
(`fmaProdE a b ≥ min_exp`), the FMA-based error recovery `e = fma(a, b, -p)`
satisfies `p + e = a × b` exactly. The theorem states both that `fpFMAFinite`
produces a finite float `e` and that the error-free identity holds. -/
theorem twoProduct_exact (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (p : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hp : a * b = p)
    (hno_underflow : fmaProdE a b ≥ FloatFormat.min_exp) :
    ∃ e : FiniteFp,
      fpFMAFinite a b (-p) = e ∧
        (p.toVal : R) + e.toVal = a.toVal * b.toVal := by
  by_cases herr : (a.toVal : R) * b.toVal - p.toVal = 0
  · -- Exact multiplication: error is zero, FMA produces signed zero
    have hfma_sum_zero : (a.toVal : R) * b.toVal + (-p).toVal = 0 := by
      rw [FiniteFp.toVal_neg_eq_neg]; linarith [sub_eq_zero.mp herr]
    have hexact := fpFMAFinite_exact_sum R a b (-p)
    rw [hfma_sum_zero] at hexact
    set ebase := fmaEMin a b (-p) - prec + 1
    have hisum_zero : fmaAlignedSumInt a b (-p) = 0 := by
      have h2ne : (2 : R) ^ ebase ≠ 0 := zpow_ne_zero _ (by norm_num)
      have : (fmaAlignedSumInt a b (-p) : R) = 0 := by
        exact_mod_cast (mul_eq_zero.mp hexact.symm).resolve_right h2ne
      exact_mod_cast this
    have hfma := fpFMAFinite_exact_cancel_sign a b (-p) hisum_zero
    set fz : FiniteFp :=
      ⟨exactCancelSign (a.s ^^ b.s) (-p).s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
    exact ⟨fz, hfma, by
      rw [show (fz.toVal : R) = 0 from FiniteFp.toVal_isZero rfl]; linarith⟩
  · -- Nonzero error: FMA computes the representable error
    obtain ⟨e, he_valid, he_val⟩ :=
      mul_error_representable (R := R) a b ha_nz hb_nz p hp hno_underflow herr
    have hfma_corr : fpFMAFinite a b (-p) = ○((a.toVal : R) * b.toVal - p.toVal) := by
      have := fpFMAFinite_correct (R := R) a b (-p)
        (by rw [FiniteFp.toVal_neg_eq_neg, ← sub_eq_add_neg]; exact herr)
      rwa [FiniteFp.toVal_neg_eq_neg, ← sub_eq_add_neg] at this
    have hfma_eq : fpFMAFinite a b (-p) = e := by
      rw [hfma_corr, ← he_val, RModeIdem.round_idempotent (R := R) e he_valid]
    exact ⟨e, hfma_eq, by rw [he_val]; ring⟩

end TwoProduct
