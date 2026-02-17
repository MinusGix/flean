import Flean.Operations.Fast2Sum
import Flean.Operations.AddErrorRepresentable

/-! # 2Sum: Ordering-Free Error-Free Transformation

The Fast2Sum algorithm requires `|b| ≤ |a|` as a precondition. 2Sum removes this
ordering requirement: for any two positive finite floats, the rounding error of their
sum is exactly representable, and the error-free identity `s + t = a + b` holds.

The proofs reduce to Fast2Sum via case-splitting on `a.toVal ≤ b.toVal` and using
commutativity of floating-point addition (`fpAddFinite_comm`).
-/

section TwoSum

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- The rounding error of a nearest-mode addition of positive floats is representable,
without any ordering precondition on `a` and `b`. -/
theorem add_error_representable_unordered (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (t_fp.s = false ∨ 0 < t_fp.m) ∧
        (t_fp.toVal : R) = (a.toVal : R) + b.toVal - s_fp.toVal := by
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by
    have := FiniteFp.toVal_pos a ha ha_nz (R := R)
    have := FiniteFp.toVal_pos b hb hb_nz (R := R)
    linarith
  rcases le_or_gt (b.toVal : R) (a.toVal : R) with hab | hab
  · exact add_error_representable (R := R) a b ha hb ha_nz hb_nz hab hsum_ne s_fp hs
  · have hs' : b + a = s_fp := by
      simp only [add_finite_eq_fpAddFinite] at hs ⊢; rw [fpAddFinite_comm]; exact hs
    obtain ⟨t_fp, ht_valid, ht_val⟩ :=
      add_error_representable (R := R) b a hb ha hb_nz ha_nz (le_of_lt hab)
        (by rwa [add_comm]) s_fp hs'
    exact ⟨t_fp, ht_valid, by rw [ht_val]; ring⟩

/-- **2Sum correctness** for positive floats.

For any two positive nonzero finite floats, the Fast2Sum error-free identity
`s + t = a + b` holds without requiring `b ≤ a`. -/
theorem twoSum_pos_exact (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (s_fp.toVal : R) + t_fp.toVal = a.toVal + b.toVal := by
  rcases le_or_gt (b.toVal : R) (a.toVal : R) with hab | hab
  · obtain ⟨_, _, _, ht⟩ :=
      fast2Sum_pos_exact (R := R) a b ha hb ha_nz hb_nz hab s_fp hs
    exact ⟨_, ht.2⟩
  · have hs' : b + a = s_fp := by
      simp only [add_finite_eq_fpAddFinite] at hs ⊢; rw [fpAddFinite_comm]; exact hs
    obtain ⟨_, _, _, ht⟩ :=
      fast2Sum_pos_exact (R := R) b a hb ha hb_nz ha_nz (le_of_lt hab) s_fp hs'
    exact ⟨_, by rw [ht.2]; ring⟩

/-- **2Sum correctness** for negative floats.

Reduces to `twoSum_pos_exact` on `(-a, -b)` using rounding negation symmetry. -/
theorem twoSum_neg_exact (a b : FiniteFp)
    (ha : a.s = true) (hb : b.s = true)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (s_fp.toVal : R) + t_fp.toVal = a.toVal + b.toVal := by
  -- (-a) and (-b) are positive
  have hna : (-a).s = false := by simp [FiniteFp.neg_def, ha]
  have hnb : (-b).s = false := by simp [FiniteFp.neg_def, hb]
  have hna_nz : 0 < (-a).m := by simp; exact ha_nz
  have hnb_nz : 0 < (-b).m := by simp; exact hb_nz
  -- Sum is nonzero (both negative nonzero → sum negative)
  have ha_neg : (a.toVal : R) < 0 := by
    have := FiniteFp.toVal_pos (-a) hna hna_nz (R := R)
    rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
  have hb_neg : (b.toVal : R) < 0 := by
    have := FiniteFp.toVal_pos (-b) hnb hnb_nz (R := R)
    rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by linarith
  -- Key: (-a) + (-b) = -s_fp via rounding negation symmetry
  have hs_corr : (s_fp : Fp) = ○((a.toVal : R) + b.toVal) := by
    have := fpAddFinite_correct (R := R) a b hsum_ne
    simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at this hs
    rw [this] at hs; exact hs.symm
  have hns_sum_ne : ((-a).toVal : R) + (-b).toVal ≠ 0 := by
    simp [FiniteFp.toVal_neg_eq_neg]; linarith
  have hns_eq : (-a) + (-b) = (-s_fp : FiniteFp) := by
    have hns_corr := fpAddFinite_correct (R := R) (-a) (-b) hns_sum_ne
    simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at hns_corr ⊢
    rw [hns_corr, FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg,
        show (-(a.toVal : R) + -b.toVal) = -(a.toVal + b.toVal) from by ring,
        RModeConj.round_neg _ hsum_ne, ← hs_corr, Fp.neg_finite]
  -- Apply twoSum_pos_exact to (-a, -b) with sum -s_fp
  obtain ⟨t', ht'⟩ := twoSum_pos_exact (R := R) (-a) (-b) hna hnb hna_nz hnb_nz (-s_fp) hns_eq
  -- t' satisfies: (-s_fp).toVal + t'.toVal = (-a).toVal + (-b).toVal
  -- i.e.: -s_fp.toVal + t'.toVal = -(a.toVal + b.toVal)
  -- So: s_fp.toVal + (-t').toVal = a.toVal + b.toVal
  exact ⟨-t', by
    rw [FiniteFp.toVal_neg_eq_neg]
    have := ht'
    rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg] at this
    linarith⟩

/-- **2Sum correctness** for same-sign floats.

For any two nonzero finite floats with the same sign, the error-free identity
`s + t = a + b` holds without any ordering or sign-polarity requirement. -/
theorem twoSum_same_sign_exact (a b : FiniteFp)
    (hsign : a.s = b.s)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (s_fp.toVal : R) + t_fp.toVal = a.toVal + b.toVal := by
  rcases Bool.eq_false_or_eq_true a.s with ha | ha
  · exact twoSum_neg_exact (R := R) a b ha (hsign ▸ ha) ha_nz hb_nz s_fp hs
  · exact twoSum_pos_exact (R := R) a b ha (hsign ▸ ha) ha_nz hb_nz s_fp hs


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
    simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at hs
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
