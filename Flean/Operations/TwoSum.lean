import Flean.Operations.Fast2Sum

/-! # 2Sum: Ordering-Free Error-Free Transformation

The Fast2Sum algorithm requires `|b| ≤ |a|` as a precondition. 2Sum removes this
ordering requirement: for any two positive finite floats, the rounding error of their
sum is exactly representable, and the error-free identity `s + t = a + b` holds.

The proofs reduce to Fast2Sum via case-splitting on `a.toVal ≤ b.toVal` and using
commutativity of floating-point addition (`fpAddFinite_comm`).
-/

section TwoSum

variable [FloatFormat]
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

end TwoSum
