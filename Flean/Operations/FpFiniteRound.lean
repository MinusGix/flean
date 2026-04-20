import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Operations.FMA

/-!
# Unified rounding witnesses for `fpAddFinite` / `fpMulFinite`

Zero-case helpers for tag preservation. See
`.claude/notes/tag-framework-phase1-design.md` §1.6 and §3.2.

The correctness lemmas `fpAddFinite_correct` / `fpMulFinite_correct`
only apply when the real sum / product is nonzero; the zero case must
be handled separately. These helpers unify both cases:

  `∃ g, round (real-op) = Fp.finite g ∧ g.toVal = f.toVal`

The `g`-witness may differ from `f` only in sign bit (signed zero vs
positive zero), but their `toVal`s agree in `R`. Downstream tag
preservations (e.g. `IsNonneg.fpAdd`) can consume this and reduce to
"round preserves tag" reasoning without case-splitting.

Requires `RModeZero` (`round 0 = Fp.finite 0`), which is satisfied by
all rounding modes in `Flean/Rounding/PolicyInstances.lean`.
-/

section FpFiniteRound

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

local notation "prec" => FloatFormat.prec

/-! ## `fpAddFinite` unified witness -/

/-- When `fpAddFinite x y` is finite, there is a finite float `g` such
that rounding `x.toVal + y.toVal` yields `Fp.finite g` with
`g.toVal = f.toVal`.

In the nonzero-sum case, `g = f`. In the zero-sum case, `f` may be a
signed zero (e.g. `-0`); we choose `g = (0 : FiniteFp)` and appeal to
both having `toVal = 0`. -/
theorem fpAddFinite_round_witness
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeZero R]
    (x y : FiniteFp) {f : FiniteFp}
    (hf : fpAddFinite x y = Fp.finite f) :
    ∃ g : FiniteFp,
      (RMode.round ((x.toVal : R) + y.toVal) : Fp) = Fp.finite g ∧
      (g.toVal : R) = f.toVal := by
  by_cases hsum : (x.toVal : R) + y.toVal = 0
  · -- Zero-sum case.  Derive `addAlignedSumInt x y = 0` from the exact
    -- representation, then use `fpAddFinite_exact_cancel_sign`.
    have hexact := fpAddFinite_exact_sum R x y
    rw [hsum] at hexact
    have h2_pos : (0 : R) < (2 : R) ^ (min x.e y.e - prec + 1) := by
      have : (0 : R) < (2 : R) := by norm_num
      positivity
    have h2_ne : (2 : R) ^ (min x.e y.e - prec + 1) ≠ 0 := ne_of_gt h2_pos
    have h_int_cast_zero : ((addAlignedSumInt x y : ℤ) : R) = 0 := by
      have h_prod_zero : ((addAlignedSumInt x y : ℤ) : R) *
          (2 : R) ^ (min x.e y.e - prec + 1) = 0 := hexact.symm
      exact (mul_eq_zero.mp h_prod_zero).resolve_right h2_ne
    have hsum_int_zero : addAlignedSumInt x y = 0 := by exact_mod_cast h_int_cast_zero
    have hcancel := fpAddFinite_exact_cancel_sign x y hsum_int_zero
    rw [hcancel] at hf
    have hf_eq : f = ⟨exactCancelSign x.s y.s, FloatFormat.min_exp, 0,
                      IsValidFiniteVal.zero⟩ :=
      (Fp.finite.inj hf).symm
    have hfm : f.m = 0 := by rw [hf_eq]
    have hf_toVal : (f.toVal : R) = 0 :=
      (FiniteFp.toVal_significand_zero_iff (R := R)).mp hfm
    refine ⟨(0 : FiniteFp), ?_, ?_⟩
    · rw [hsum]; exact RModeZero.round_zero
    · rw [FiniteFp.toVal_zero, hf_toVal]
  · -- Nonzero-sum case.  Use `fpAddFinite_correct`.
    have hcorr := fpAddFinite_correct (R := R) x y hsum
    simp only [add_eq_fpAdd, fpAdd_coe_coe] at hcorr
    rw [hcorr] at hf
    exact ⟨f, hf, rfl⟩

/-! ## `fpMulFinite` unified witness -/

/-- When `fpMulFinite x y` is finite, there is a finite float `g` such
that rounding `x.toVal * y.toVal` yields `Fp.finite g` with
`g.toVal = f.toVal`.

Structure parallels `fpAddFinite_round_witness`.  The zero-product case
is reached when either operand has significand zero; the result is a
signed-zero float with `toVal = 0`. -/
theorem fpMulFinite_round_witness
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeZero R]
    (x y : FiniteFp) {f : FiniteFp}
    (hf : fpMulFinite x y = Fp.finite f) :
    ∃ g : FiniteFp,
      (RMode.round ((x.toVal : R) * y.toVal) : Fp) = Fp.finite g ∧
      (g.toVal : R) = f.toVal := by
  by_cases hprod : (x.toVal : R) * y.toVal = 0
  · -- Zero-product case: one operand has significand zero.
    have hmag_zero : x.m * y.m = 0 := by
      rcases mul_eq_zero.mp hprod with hx0 | hy0
      · rw [(FiniteFp.toVal_significand_zero_iff (R := R)).mpr hx0, zero_mul]
      · rw [(FiniteFp.toVal_significand_zero_iff (R := R)).mpr hy0, mul_zero]
    -- fpMulFinite's zero-magnitude branch returns a signed-zero float.
    have hf' : roundIntSigM (x.s ^^ y.s) (x.m * y.m)
        (x.e + y.e - 2 * FloatFormat.prec + 2) = Fp.finite f := hf
    rw [hmag_zero] at hf'
    -- Extract f.m = 0 from the `mag = 0` branch of roundIntSigM.
    have hfm : f.m = 0 := by
      unfold roundIntSigM at hf'
      simp only at hf'
      have : f = (if (x.s ^^ y.s) then (-0 : FiniteFp) else (0 : FiniteFp)) :=
        (Fp.finite.inj hf').symm
      rw [this]
      cases (x.s ^^ y.s) <;> simp [FiniteFp.neg_def]
    have hf_toVal : (f.toVal : R) = 0 :=
      (FiniteFp.toVal_significand_zero_iff (R := R)).mp hfm
    refine ⟨(0 : FiniteFp), ?_, ?_⟩
    · rw [hprod]; exact RModeZero.round_zero
    · rw [FiniteFp.toVal_zero, hf_toVal]
  · -- Nonzero-product case: use `fpMulFinite_correct`.
    have hcorr := fpMulFinite_correct (R := R) x y hprod
    simp only [mul_eq_fpMul, fpMul_coe_coe] at hcorr
    rw [hcorr] at hf
    exact ⟨f, hf, rfl⟩

/-! ## `fpFMAFinite` unified witness -/

/-- When `fpFMAFinite a b c` is finite, there is a finite float `g`
such that rounding `a.toVal * b.toVal + c.toVal` yields `Fp.finite g`
with `g.toVal = f.toVal`.

Structure parallels `fpAddFinite_round_witness`.  The zero-sum case
(`a*b + c = 0`) is reached when the aligned integer sum cancels; the
result is a signed-zero float with `toVal = 0`. -/
theorem fpFMAFinite_round_witness
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeZero R]
    (a b c : FiniteFp) {f : FiniteFp}
    (hf : fpFMAFinite a b c = Fp.finite f) :
    ∃ g : FiniteFp,
      (RMode.round ((a.toVal : R) * b.toVal + c.toVal) : Fp) = Fp.finite g ∧
      (g.toVal : R) = f.toVal := by
  by_cases hsum : (a.toVal : R) * b.toVal + c.toVal = 0
  · -- Zero-sum case: derive `fmaAlignedSumInt = 0`, then use
    -- `fpFMAFinite_exact_cancel_sign`.
    have hexact := fpFMAFinite_exact_sum R a b c
    rw [hsum] at hexact
    have h2_pos : (0 : R) < (2 : R) ^ (fmaEMin a b c - prec + 1) := by positivity
    have h2_ne : (2 : R) ^ (fmaEMin a b c - prec + 1) ≠ 0 := ne_of_gt h2_pos
    have h_int_cast_zero : ((fmaAlignedSumInt a b c : ℤ) : R) = 0 := by
      have h_prod_zero : ((fmaAlignedSumInt a b c : ℤ) : R) *
          (2 : R) ^ (fmaEMin a b c - prec + 1) = 0 := hexact.symm
      exact (mul_eq_zero.mp h_prod_zero).resolve_right h2_ne
    have hsum_int_zero : fmaAlignedSumInt a b c = 0 := by
      exact_mod_cast h_int_cast_zero
    have hcancel := fpFMAFinite_exact_cancel_sign a b c hsum_int_zero
    rw [hcancel] at hf
    have hf_eq : f = ⟨exactCancelSign (a.s ^^ b.s) c.s, FloatFormat.min_exp, 0,
                      IsValidFiniteVal.zero⟩ :=
      (Fp.finite.inj hf).symm
    have hfm : f.m = 0 := by rw [hf_eq]
    have hf_toVal : (f.toVal : R) = 0 :=
      (FiniteFp.toVal_significand_zero_iff (R := R)).mp hfm
    refine ⟨(0 : FiniteFp), ?_, ?_⟩
    · rw [hsum]; exact RModeZero.round_zero
    · rw [FiniteFp.toVal_zero, hf_toVal]
  · -- Nonzero-sum case: use `fpFMAFinite_correct`.
    have hcorr := fpFMAFinite_correct (R := R) a b c hsum
    rw [hcorr] at hf
    exact ⟨f, hf, rfl⟩

end FpFiniteRound
