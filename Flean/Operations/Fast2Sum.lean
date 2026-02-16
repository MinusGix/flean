import Flean.Operations.AddErrorRepresentable

/-! # Fast2Sum — Error-Free Transformation

Fast2Sum (Dekker 1971) recovers the exact rounding error of floating-point addition.
Given `|a| ≥ |b|`, it computes `s = fl(a+b)` and `t` such that `s + t = a + b` exactly.
This is the foundational building block for compensated summation, double-double arithmetic,
and verified numerical algorithms.

We target **round-to-nearest** modes (TiesToEven, TiesAwayFromZero) where the algorithm
is classically proven correct.
-/

section Fast2Sum

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Sterbenz conditions for `s - a`

For positive same-sign operands with `a ≥ b`, the rounded sum `s` satisfies
`a ≤ s ≤ 2a`, so Sterbenz applies to `s - a`. -/

/-- Sterbenz conditions hold for `(s_fp, a)` when `a, b` are positive with `a ≥ b`. -/
theorem sterbenz_sub_sa (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (_hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeMono R] [RModeIdem R]
    (hs : a + b = s_fp) :
    ∃ z_fp : FiniteFp,
      s_fp - a = z_fp ∧
        z_fp.toVal (R := R) = s_fp.toVal - a.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hs_ge_a := round_sum_ge_left (R := R) a b ha hb ha_nz hsum_ne s_fp hs
  have hs_le_2a := round_sum_le_double (R := R) a b ha hb ha_nz hab hsum_ne s_fp hs
  have hs_s : s_fp.s = false :=
    ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).1
  have hs_m : 0 < s_fp.m :=
    ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).2
  obtain ⟨z_fp, hz_sub, hz_repr⟩ :=
    sterbenz (R := R) s_fp a hs_s ha hs_m ha_nz (by linarith) hs_le_2a
  exact ⟨z_fp, hz_sub, by simpa [Fp.Represents] using hz_repr⟩

/-! ## Subtraction of equal-valued floats yields finite zero -/

omit [FloorRing R] in
/-- When `a.toVal = b.toVal`, `fpSubFinite` returns a finite zero. -/
theorem fpSubFinite_zero_of_eq_toVal [RModeExec] (a b : FiniteFp)
    (heq : (a.toVal : R) = b.toVal) :
    ∃ f : FiniteFp, a - b = f ∧
      f.toVal (R := R) = 0 := by
  -- fpSubFinite = fpAddFinite a (-b)
  -- The exact sum a + (-b) = a - b = 0
  -- So the integer sum in fpAddFinite is 0, taking the zero branch
  have hexact := fpAddFinite_exact_sum R a (-b)
  rw [FiniteFp.toVal_neg_eq_neg] at hexact
  have hdiff_zero : (a.toVal : R) - b.toVal = 0 := sub_eq_zero.mpr heq
  set isum := addAlignedSumInt a (-b) with isum_def
  set e_base := min a.e (-b).e - prec + 1
  have hisum_zero : (isum : R) = 0 := by
    have h2ne : (2 : R) ^ e_base ≠ 0 := zpow_ne_zero _ (by norm_num)
    have : (isum : R) * (2 : R) ^ e_base = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right h2ne
  have hisum_int_zero : isum = 0 := by exact_mod_cast hisum_zero
  -- The integer sum in fpAddFinite is exactly addAlignedSumInt
  have hkey : condNeg a.s (a.m : ℤ) * 2 ^ (a.e - min a.e (-b).e).toNat +
      condNeg (-b).s ((-b).m : ℤ) * 2 ^ ((-b).e - min a.e (-b).e).toNat = 0 := by
    exact hisum_int_zero
  have hkey' : condNeg a.s (a.m : ℤ) * 2 ^ (a.e - min a.e b.e).toNat +
      condNeg (!b.s) (b.m : ℤ) * 2 ^ (b.e - min a.e b.e).toNat = 0 := by
    simpa [FiniteFp.neg_def] using hkey
  -- fpSubFinite unfolds to fpAddFinite which checks if the integer sum is 0
  let fz : FiniteFp := ⟨exactCancelSign a.s (!b.s), FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  refine ⟨fz, ?_, FiniteFp.toVal_isZero rfl⟩
  simp [fpSubFinite, fpAddFinite, hkey', fz, exactCancelSign, FiniteFp.neg_def]

/-! ## Main theorem (positive case) -/

/-- **Fast2Sum correctness** for the positive same-sign case.

When `a, b ≥ 0` with `a ≥ b` and both nonzero, the Fast2Sum algorithm produces
exact error recovery for round-to-nearest modes. -/
theorem fast2Sum_pos_exact (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (hs : a + b = s_fp) :
    ∃ z_fp t_fp : FiniteFp,
      s_fp - a = z_fp ∧
        b - z_fp = t_fp ∧
          (s_fp.toVal : R) + t_fp.toVal = a.toVal + b.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by linarith
  -- Step 1: z = s - a is exact by Sterbenz
  obtain ⟨z_fp, hz_eq, hz_val⟩ :=
    sterbenz_sub_sa (R := R) a b ha hb ha_nz hb_nz hab hsum_ne s_fp hs
  -- Step 2: b - z is exact
  -- b.toVal - z_fp.toVal = b.toVal - (s.toVal - a.toVal) = (a + b) - s
  suffices h_bz : ∃ t_fp : FiniteFp,
      b - z_fp = t_fp ∧
        (t_fp.toVal : R) = b.toVal - z_fp.toVal by
    obtain ⟨t_fp, ht_eq, ht_val⟩ := h_bz
    exact ⟨z_fp, t_fp, hz_eq, ht_eq, by rw [ht_val, hz_val]; ring⟩
  by_cases htz : (b.toVal : R) - z_fp.toVal = 0
  · -- Zero error: addition was exact, b = z in value
    have hbeq : (b.toVal : R) = z_fp.toVal := sub_eq_zero.mp htz
    obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) b z_fp hbeq
    exact ⟨f, hf_eq, by rw [hf_val, htz]⟩
  · -- Nonzero error: the error is representable
    obtain ⟨err_fp, herr_valid, herr_val⟩ :=
      add_error_representable (R := R) a b ha hb ha_nz hb_nz hab hsum_ne s_fp hs
    have hbz_val : (b.toVal : R) - z_fp.toVal = err_fp.toVal := by
      rw [hz_val, herr_val]; ring
    have hsub_eq : b - z_fp = err_fp := by
      have hsub_corr := fpSubFinite_correct (R := R) b z_fp htz
      simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe] at hsub_corr ⊢
      rw [hsub_corr, hbz_val,
          RModeIdem.round_idempotent (R := R) err_fp herr_valid]
    exact ⟨err_fp, hsub_eq, hbz_val.symm⟩

end Fast2Sum
