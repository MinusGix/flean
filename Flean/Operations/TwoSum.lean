import Flean.Operations.AddErrorRepresentable

/-! # 2Sum: Error-Free Transformation

For any two nonzero finite floats, the rounding error of their sum is exactly
representable, and the error-free identity `s + t = a + b` holds — regardless
of sign, ordering, or whether the sum cancels to zero.
-/

section TwoSum

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- **2Sum correctness** for arbitrary-sign floats.

For any two nonzero finite floats, the error-free identity
`s + t = a + b` holds without any ordering or sign requirement. -/
theorem twoSum_exact (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (s_fp.toVal : R) + t_fp.toVal = a.toVal + b.toVal := by
  -- Exact cancellation: a.toVal + b.toVal = 0 → s_fp is a zero, t = 0 works
  by_cases hsum_ne : (a.toVal : R) + b.toVal = 0
  · have hexact := fpAddFinite_exact_sum R a b
    have hisum_zero : addAlignedSumInt a b = 0 := by
      have h0 : ((addAlignedSumInt a b : ℤ) : R) * (2:R) ^ (min a.e b.e - prec + 1) = 0 := by
        rw [← hexact]; exact hsum_ne
      rcases mul_eq_zero.mp h0 with h | h
      · exact_mod_cast h
      · exact absurd h (ne_of_gt (zpow_pos (by norm_num) _))
    have hcancel := fpAddFinite_exact_cancel_sign a b hisum_zero
    simp only [add_finite_eq_fpAddFinite] at hs
    rw [hcancel] at hs
    have hs_eq := (Fp.finite.inj hs).symm
    have hs_zero : s_fp.toVal (R := R) = 0 :=
      FiniteFp.toVal_isZero (by rw [hs_eq])
    exact ⟨0, by
      rw [hs_zero, show (0 : FiniteFp).toVal (R := R) = 0 from FiniteFp.toVal_isZero rfl]
      linarith⟩
  · -- Nonzero sum: delegate to add_error_representable_general
    rcases le_or_gt |b.toVal (R := R)| |a.toVal| with hab | hab
    · obtain ⟨t, _, ht⟩ := add_error_representable_general (R := R) a b
        ha_nz hb_nz hab hsum_ne s_fp hs
      exact ⟨t, by linarith⟩
    · have hs' : b + a = s_fp := by
        simp only [add_finite_eq_fpAddFinite] at hs ⊢; rw [fpAddFinite_comm]; exact hs
      obtain ⟨t, _, ht⟩ := add_error_representable_general (R := R) b a
        hb_nz ha_nz (le_of_lt hab) (by rwa [add_comm]) s_fp hs'
      exact ⟨t, by rw [ht]; ring⟩

end TwoSum
