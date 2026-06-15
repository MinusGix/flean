import Flean.Operations.ExactInt
import Flean.Operations.Add

/-! # Zero-admitting exact integer arithmetic

The per-op lemmas in `ExactInt.lean` require the *result* to be a nonzero integer. But the
zero result is exactly the case we most want to admit (cancellation in a sum, a zero weight
or input): `round 0 = 0` is exact, so the `≠ 0` hypothesis is needless.

These `_int_exact0` variants drop it. When the integer result is `0`, the op lands on a
finite signed zero (add: the exact-cancellation branch of `fpAddFinite`; mul:
`roundIntSigM _ 0 _ = Fp.finite (signed 0)`); otherwise they delegate to the nonzero
lemmas. Subtraction reduces to addition of a negation (`fpSubFinite a b = a + (-b)`).
-/

section ExactIntZero

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

/-- Zero-admitting exact addition: integer-valued operands with a representable integer sum
(possibly `0`) add exactly. -/
theorem fpAddFinite_int_exact0 (a b : FiniteFp) (n_a n_b : ℤ)
    (ha : (a.toVal : R) = (n_a : R)) (hb : (b.toVal : R) = (n_b : R))
    (hsum_bound : (n_a + n_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, a + b = f ∧ (f.toVal : R) = ((n_a + n_b : ℤ) : R) := by
  by_cases hnz : n_a + n_b = 0
  · -- exact cancellation: the sum is zero
    have hsum0 : (a.toVal : R) + b.toVal = 0 := by
      rw [ha, hb, ← Int.cast_add, hnz, Int.cast_zero]
    have hexact := fpAddFinite_exact_sum R a b
    have hzeroint : addAlignedSumInt a b = 0 := by
      have h2 : (2 : R) ^ (min a.e b.e - FloatFormat.prec + 1) ≠ 0 := by positivity
      rw [hsum0] at hexact
      have hcast : ((addAlignedSumInt a b : ℤ) : R) = 0 := by
        rcases mul_eq_zero.mp hexact.symm with h | h
        · exact h
        · exact absurd h h2
      exact_mod_cast hcast
    refine ⟨⟨exactCancelSign a.s b.s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩, ?_, ?_⟩
    · rw [add_finite_eq_fpAddFinite, fpAddFinite_exact_cancel_sign a b hzeroint]
    · rw [hnz, Int.cast_zero]
      exact (FiniteFp.toVal_significand_zero_iff (R := R)).mp rfl
  · exact fpAddFinite_int_exact a b n_a n_b ha hb hnz hsum_bound h_exp

/-- Zero-admitting exact multiplication: integer-valued operands with a representable
integer product (possibly `0`) multiply exactly. -/
theorem fpMulFinite_int_exact0 (a b : FiniteFp) (n_a n_b : ℤ)
    (ha : (a.toVal : R) = (n_a : R)) (hb : (b.toVal : R) = (n_b : R))
    (hprod_bound : (n_a * n_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, a * b = f ∧ (f.toVal : R) = ((n_a * n_b : ℤ) : R) := by
  by_cases hnz : n_a * n_b = 0
  · -- product is zero: at least one operand has zero significand
    have hprod0 : (a.toVal : R) * b.toVal = 0 := by
      rw [ha, hb, ← Int.cast_mul, hnz, Int.cast_zero]
    have hm0 : a.m * b.m = 0 := by
      rcases mul_eq_zero.mp hprod0 with h | h
      · simp [(FiniteFp.toVal_significand_zero_iff (R := R)).mpr h]
      · simp [(FiniteFp.toVal_significand_zero_iff (R := R)).mpr h]
    refine ⟨(if (a.s ^^ b.s) then -0 else 0 : FiniteFp), ?_, ?_⟩
    · rw [mul_finite_eq_fpMulFinite]
      simp only [fpMulFinite, roundIntSigM, show a.m * b.m = 0 from hm0, ↓reduceDIte]
    · rw [hnz, Int.cast_zero]
      split <;> simp [FiniteFp.toVal_zero]
  · exact fpMulFinite_int_exact a b n_a n_b ha hb hnz hprod_bound h_exp

/-- Zero-admitting exact subtraction, via `fpSubFinite a b = a + (-b)`. -/
theorem fpSubFinite_int_exact0 (a b : FiniteFp) (n_a n_b : ℤ)
    (ha : (a.toVal : R) = (n_a : R)) (hb : (b.toVal : R) = (n_b : R))
    (hdiff_bound : (n_a - n_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, a - b = f ∧ (f.toVal : R) = ((n_a - n_b : ℤ) : R) := by
  have hbneg : ((-b).toVal : R) = ((-n_b : ℤ) : R) := by
    rw [FiniteFp.toVal_neg_eq_neg, hb, Int.cast_neg]
  have hbound' : (n_a + -n_b).natAbs < 2 ^ FloatFormat.prec.toNat := by
    rwa [show n_a + -n_b = n_a - n_b from by ring]
  obtain ⟨f, hf_eq, hf_val⟩ :=
    fpAddFinite_int_exact0 (R := R) a (-b) n_a (-n_b) ha hbneg hbound' h_exp
  refine ⟨f, ?_, ?_⟩
  · rw [sub_finite_eq_fpSubFinite, fpSubFinite]; exact hf_eq
  · rw [hf_val, sub_eq_add_neg]

end ExactIntZero
