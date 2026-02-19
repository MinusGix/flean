import Flean.Rounding.Rounding
import Flean.Rounding.ModeClass
import Flean.Rounding.PolicyInstances
import Flean.Rounding.GridInstance
import Flean.ToVal
import Flean.Operations.AddErrorRepresentable
import Flean.Operations.Sub

/-! # RModeSplit — Positive-case split proofs

Proves that `s − bv` and `b − bv` are representable when both operands
are positive, using Sterbenz and grid arguments. -/

section SplitPositive

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

theorem split_s_sub_bv_sterbenz
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = s.toVal - bv.toVal := by
  -- Link ○(a+b) to fpAddFinite
  have hs_fp : (a : Fp) + b = Fp.finite s := by
    have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
    simp only [add_finite_eq_fpAddFinite] at hcorr
    exact hcorr.trans hs
  -- s ≥ a, s ≤ 2a
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hs_ge_a := round_sum_ge_left (R := R) a b ha hb ha_nz hsum_ne s hs_fp
  have hs_le_2a := round_sum_le_double (R := R) a b ha hb ha_nz hab hsum_ne s hs_fp
  -- s positive
  have hs_pos : (0 : R) < s.toVal := lt_of_lt_of_le ha_pos hs_ge_a
  have hs_s : s.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).1
  have hs_nz : 0 < s.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).2
  -- Sterbenz conditions: a/2 ≤ s and s ≤ 2a
  have h_lb : a.toVal (R := R) / 2 ≤ s.toVal := by linarith
  have h_ub : s.toVal (R := R) ≤ 2 * a.toVal := hs_le_2a
  -- Apply Sterbenz to (s, a)
  obtain ⟨f_diff, hf_eq, hf_repr⟩ := sterbenz (R := R) s a hs_s ha hs_nz ha_nz h_lb h_ub
  -- f_diff.toVal = s.toVal - a.toVal
  rw [Fp.Represents] at hf_repr
  -- Link to bv: round(s.toVal - a.toVal) = bv, but also = f_diff (by idempotence)
  by_cases hdiff_zero : (s.toVal : R) - a.toVal = 0
  · -- s = a: bv is a zero, s - bv = a
    have hbv_zero : bv.toVal (R := R) = 0 := by
      have : ○((s.toVal : R) - a.toVal) = ○(0 : R) := by rw [hdiff_zero]
      rw [this, RModeZero.round_zero] at hbv
      exact FiniteFp.toVal_isZero (by exact (Fp.finite.inj hbv).symm ▸ rfl)
    exact ⟨a, Or.inl ha, by rw [hbv_zero, sub_zero]; linarith⟩
  · -- s ≠ a: use fpSubFinite_correct + Sterbenz
    have hbv_eq : (Fp.finite bv : Fp) = Fp.finite f_diff := by
      have hsub_corr := fpSubFinite_correct (R := R) s a hdiff_zero
      simp only [sub_finite_eq_fpSubFinite, fpSubFinite] at hsub_corr hf_eq
      calc Fp.finite bv = ○((s.toVal : R) - a.toVal) := hbv.symm
        _ = s + (-a) := hsub_corr.symm
        _ = Fp.finite f_diff := hf_eq
    have hbv_is_f : bv = f_diff := Fp.finite.inj hbv_eq
    rw [hbv_is_f, hf_repr]
    exact ⟨a, Or.inl ha, by ring⟩

/-- For positive a, b with a ≥ b, bv = s − a (exact), so
    b − bv = (a + b) − s, which is representable by add_error_representable. -/
theorem split_b_sub_bv_sterbenz
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = b.toVal - bv.toVal := by
  -- First establish bv.toVal = s.toVal - a.toVal (by Sterbenz, same as s_sub_bv)
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hs_fp : (a : Fp) + b = Fp.finite s := by
    have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
    simp only [add_finite_eq_fpAddFinite] at hcorr
    exact hcorr.trans hs
  have hs_ge_a := round_sum_ge_left (R := R) a b ha hb ha_nz hsum_ne s hs_fp
  have hs_le_2a := round_sum_le_double (R := R) a b ha hb ha_nz hab hsum_ne s hs_fp
  have hs_pos : (0 : R) < s.toVal := lt_of_lt_of_le ha_pos hs_ge_a
  have hs_s : s.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).1
  have hs_nz : 0 < s.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).2
  obtain ⟨f_diff, hf_eq, hf_repr⟩ := sterbenz (R := R) s a hs_s ha hs_nz ha_nz
    (by linarith : a.toVal (R := R) / 2 ≤ s.toVal) hs_le_2a
  rw [Fp.Represents] at hf_repr
  -- bv.toVal = s.toVal - a.toVal
  have hbv_val : bv.toVal (R := R) = s.toVal - a.toVal := by
    by_cases hdiff_zero : (s.toVal : R) - a.toVal = 0
    · have : ○((s.toVal : R) - a.toVal) = ○(0 : R) := by rw [hdiff_zero]
      rw [this, RModeZero.round_zero] at hbv
      have hbv0 : bv = (0 : FiniteFp) := (Fp.finite.inj hbv).symm
      rw [hbv0, FiniteFp.toVal_isZero (R := R) rfl, hdiff_zero]
    · have hsub_corr := fpSubFinite_correct (R := R) s a hdiff_zero
      simp only [sub_finite_eq_fpSubFinite, fpSubFinite] at hsub_corr hf_eq
      have hbv_is_f : bv = f_diff := Fp.finite.inj
        (hbv.symm.trans (hsub_corr.symm.trans hf_eq))
      rw [hbv_is_f, hf_repr]
  -- b - bv = b - (s - a) = (a + b) - s = rounding error
  -- Use add_error_representable_general for the error
  by_cases herr_zero : (a.toVal : R) + b.toVal - s.toVal = 0
  · -- Error is zero: b - bv = 0
    have hval : (b.toVal : R) - bv.toVal = 0 := by rw [hbv_val]; linarith
    exact ⟨0, Or.inl rfl, by
      rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hval.symm⟩
  · -- Nonzero error: delegate to add_error_representable_general
    have hab_abs : |b.toVal (R := R)| ≤ |a.toVal| := by
      rw [abs_of_pos (FiniteFp.toVal_pos b hb hb_nz),
          abs_of_pos ha_pos]; exact hab
    obtain ⟨t_fp, ht_valid, ht_val⟩ := add_error_representable_general (R := R)
      a b ha_nz hb_nz hab_abs hsum_ne s hs_fp
    exact ⟨t_fp, ht_valid, by rw [ht_val, hbv_val]; ring⟩

/-! ### Key bounds for the grid case: s ≥ 2a and bv ≥ s/2

When `b > a > 0`, the rounded sum `s = round(a+b)` satisfies `s ≥ 2a`.
This follows because `b ≥ a + ulp(a)` (FP successor), so `a + b > 2a`,
and since `2a` is representable, `round(a+b) ≥ 2a` by monotonicity.

Consequently `s - a ≥ s/2`, and `bv = round(s-a) ≥ s/2` (since `s/2` is FP
and acts as a lower bound). This ensures `s - bv ≤ bv < 2^(bv.e + 1)`,
giving the coefficient bound needed for representability. -/

/-- When `b > a > 0` (both FP), the rounded sum satisfies `s ≥ 2a`.
    Key sub-theorem for the grid analysis. -/
theorem round_sum_ge_two_a
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (a.toVal : R) < b.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s) :
    2 * (a.toVal : R) ≤ s.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hab_ge : 2 * (a.toVal : R) ≤ a.toVal + b.toVal := by linarith
  by_cases he : a.e + 1 ≤ FloatFormat.max_exp
  · -- Case 1: 2a representable via exponent shift
    obtain ⟨d, hds, hdv⟩ := mul_pow2_representable (R := R) a 1 ha_nz ha
      (by have := a.valid.1; omega) he
    have hdv' : (d.toVal : R) = 2 * a.toVal := by rw [hdv, zpow_one]; ring
    have hmono : ○(d.toVal (R := R)) ≤ ○((a.toVal : R) + b.toVal) :=
      RModeMono.round_mono (R := R) (by rw [hdv']; exact hab_ge)
    have hround_d := RModeIdem.round_idempotent (R := R) d (Or.inl hds)
    rw [hround_d, hs] at hmono
    linarith [FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff d s).mp hmono)]
  · -- Case 2: a.e = max_exp
    push_neg at he
    have ha_e_eq : a.e = FloatFormat.max_exp := le_antisymm a.valid.2.1 (by omega)
    by_cases ha_normal : _root_.isNormal a.m
    · -- Normal at max_exp: a+b overflows, contradicting hs
      have ha_lower := FiniteFp.toVal_normal_lower (R := R) a ha ha_normal
      have h2e : (2 : R) ^ FloatFormat.max_exp ≤ a.toVal := by rwa [ha_e_eq] at ha_lower
      have hab_overflow : FloatFormat.overflowThreshold R ≤ (a.toVal : R) + b.toVal :=
        le_of_lt (calc
          FloatFormat.overflowThreshold R
            < (2 : R) ^ (FloatFormat.max_exp + 1) :=
              FloatFormat.overflowThreshold_lt_zpow_max_exp_succ
          _ = 2 * (2 : R) ^ FloatFormat.max_exp := by
              rw [zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]; ring
          _ ≤ 2 * a.toVal := by linarith
          _ ≤ a.toVal + b.toVal := hab_ge)
      rw [RModeNearest.overflow_pos_inf (R := R) _ hab_overflow] at hs; simp at hs
    · -- Subnormal at max_exp: 2*a.m < 2^prec, so 2a representable
      have hsub := a.isNormal_or_isSubnormal.resolve_left ha_normal
      have hm_sub : a.m < 2 ^ (prec - 1).toNat := by omega
      have hprec := FloatFormat.valid_prec
      have h2m_bound : 2 * a.m < 2 ^ precNat := by
        calc 2 * a.m < 2 * 2 ^ (prec - 1).toNat := by omega
          _ = 2 ^ precNat := by
            rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
            rw [show 2 * 2 ^ (precNat - 1) = 2 ^ (precNat - 1 + 1) from by ring]
            congr 1; omega
      have h2a_eq : 2 * (a.toVal : R) = (2 * a.m : R) * (2 : R) ^ (a.e - prec + 1) := by
        rw [FiniteFp.toVal_pos_eq a ha]; ring
      obtain ⟨d, hds, hdv⟩ := exists_finiteFp_of_nat_mul_zpow (R := R) (2 * a.m)
        (a.e - prec + 1) (by omega) h2m_bound (by omega) (by omega)
      have hdv' : (d.toVal : R) = 2 * a.toVal := by
        rw [hdv, h2a_eq]; push_cast; ring
      have hmono : ○(d.toVal (R := R)) ≤ ○((a.toVal : R) + b.toVal) :=
        RModeMono.round_mono (R := R) (by rw [hdv']; exact hab_ge)
      have hround_d := RModeIdem.round_idempotent (R := R) d (Or.inl hds)
      rw [hround_d, hs] at hmono
      linarith [FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff d s).mp hmono)]

/-- When `s ≥ 2a` and `bv = round(s − a)`, we have `bv ≥ s/2`.
    From `s ≥ 2a`: `s − a ≥ s/2`. Since `s/2` is FP (or subnormal
    edge case), monotonicity gives `round(s−a) ≥ s/2`. -/
theorem bv_ge_half_s
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (a s : FiniteFp)
    (ha : a.s = false) (ha_nz : 0 < a.m)
    (hs_pos : (0 : R) < s.toVal)
    (hs_ge_2a : 2 * (a.toVal : R) ≤ s.toVal)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    (s.toVal : R) ≤ 2 * bv.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hs_s : s.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).1
  have hs_nz : 0 < s.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).2
  have hsa_ge : s.toVal (R := R) / 2 ≤ s.toVal - a.toVal := by linarith
  by_cases he : s.e - 1 ≥ FloatFormat.min_exp
  · -- Normal case: s/2 representable via exponent shift
    obtain ⟨d, hds, hdv⟩ := mul_pow2_representable (R := R) s (-1) hs_nz hs_s
      (by omega) (by have := s.valid.2.1; omega)
    have hdv' : (d.toVal : R) = s.toVal / 2 := by
      rw [hdv, zpow_neg_one]; ring
    have hmono : ○(d.toVal (R := R)) ≤ ○((s.toVal : R) - a.toVal) :=
      RModeMono.round_mono (R := R) (by rw [hdv']; linarith)
    have hround_d := RModeIdem.round_idempotent (R := R) d (Or.inl hds)
    rw [hround_d, hbv] at hmono
    have hle := FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff d bv).mp hmono)
    linarith
  · -- Subnormal case: s.e = min_exp, s - a is exact
    push_neg at he
    have hs_e : s.e = FloatFormat.min_exp := le_antisymm (by omega) s.valid.1
    -- a is also subnormal: if normal, a.toVal ≥ 2^min_exp, contradicting s < 2^(min_exp+1)
    have ha_sub : isSubnormal a.e a.m := by
      by_contra h_not_sub
      have ha_normal := a.isNormal_or_isSubnormal.resolve_right h_not_sub
      have ha_ge := FiniteFp.toVal_normal_lower (R := R) a ha ha_normal
      have hs_lt := FiniteFp.toVal_lt_zpow_succ (R := R) s hs_s
      rw [hs_e] at hs_lt
      have : (2 : R) ^ (FloatFormat.min_exp + 1) ≤ s.toVal := calc
        (2 : R) ^ (FloatFormat.min_exp + 1)
          = 2 * (2 : R) ^ FloatFormat.min_exp := by
            rw [zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]; ring
        _ ≤ 2 * a.toVal := by
            linarith [two_zpow_mono (R := R) (show FloatFormat.min_exp ≤ a.e from a.valid.1)]
        _ ≤ s.toVal := hs_ge_2a
      linarith
    have ha_e : a.e = FloatFormat.min_exp := ha_sub.1
    -- s - a = (s.m - a.m) * 2^(min_exp - prec + 1), exact on subnormal grid
    have hsm_gt_am : a.m < s.m := by
      have h1 := FiniteFp.toVal_pos_eq (R := R) s hs_s
      have h2 := FiniteFp.toVal_pos_eq (R := R) a ha
      rw [hs_e] at h1; rw [ha_e] at h2
      rw [h1, h2] at hs_ge_2a
      have hbase_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - prec + 1) := by positivity
      -- Cancel the positive base factor: 2 * (a.m * base) ≤ s.m * base → 2 * a.m ≤ s.m
      have h2a_le : 2 * (a.m : R) ≤ (s.m : R) := by
        by_contra hlt; push_neg at hlt
        have : (s.m : R) * (2 : R) ^ (FloatFormat.min_exp - prec + 1) <
            2 * ((a.m : R) * (2 : R) ^ (FloatFormat.min_exp - prec + 1)) := by nlinarith
        linarith
      have : (0 : R) < (a.m : R) := Nat.cast_pos.mpr ha_nz
      exact_mod_cast show (a.m : R) < (s.m : R) by nlinarith
    have hdiff_pos : 0 < s.m - a.m := by omega
    have hdiff_bound : s.m - a.m < 2 ^ precNat := by
      have := s.valid.2.2.1; omega
    obtain ⟨d, hds, hdv⟩ := exists_finiteFp_of_nat_mul_zpow (R := R) (s.m - a.m)
      (FloatFormat.min_exp - prec + 1) hdiff_pos hdiff_bound (by omega)
      (by have := FloatFormat.exp_order; omega)
    have hdv' : (d.toVal : R) = s.toVal - a.toVal := by
      rw [hdv, FiniteFp.toVal_pos_eq s hs_s, FiniteFp.toVal_pos_eq a ha, hs_e, ha_e]
      push_cast
      rw [show (↑(s.m - a.m) : R) = (↑s.m : R) - ↑a.m from by exact_mod_cast Nat.cast_sub (le_of_lt hsm_gt_am)]
      ring
    have hround_d := RModeIdem.round_idempotent (R := R) d (Or.inl hds)
    rw [hdv'] at hround_d
    rw [hround_d] at hbv
    have hbv_eq : (bv.toVal : R) = s.toVal - a.toVal := by
      have := Fp.finite.inj hbv; rw [← this]; exact hdv'
    linarith

/-- When `bv ≤ s` (which holds since `s − a < s` and `s` is FP),
    `round(s − a) ≤ s`. -/
theorem bv_le_s
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (a s : FiniteFp)
    (ha_pos : (0 : R) < a.toVal)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    (bv.toVal : R) ≤ s.toVal := by
  -- s - a < s (since a > 0), so round(s - a) ≤ round(s) = s
  have hle : (s.toVal : R) - a.toVal ≤ s.toVal := by linarith
  -- Need s to be idempotent: either s.s = false or s.m > 0
  -- We don't assume sign of s, so case split on s.m
  by_cases hs_m : s.m = 0
  · -- s is a zero: s.toVal = 0, contradicts a > 0 and round producing finite bv
    -- Actually: s.toVal = 0 and a > 0, so s - a < 0. round(s-a) = bv (finite).
    -- round(s-a) ≤ round(0) = 0. So bv.toVal ≤ 0 ≤ s.toVal.
    have hs_zero : s.toVal (R := R) = 0 := FiniteFp.toVal_isZero (show s.isZero from hs_m)
    rw [hs_zero]
    have hsa_neg : (s.toVal : R) - a.toVal ≤ 0 := by rw [hs_zero]; linarith
    have hmono := RModeMono.round_mono (R := R) hsa_neg
    rw [RModeZero.round_zero, hbv] at hmono
    exact le_trans (FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff bv 0).mp hmono))
      (le_of_eq (FiniteFp.toVal_isZero (R := R) (show (0 : FiniteFp).isZero from rfl)))
  · -- s has nonzero significand: idempotent
    have hs_nz : 0 < s.m := by omega
    have hround_s := RModeIdem.round_idempotent (R := R) s (Or.inr hs_nz)
    have hmono := RModeMono.round_mono (R := R) hle
    rw [hround_s, hbv] at hmono
    exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff bv s).mp hmono)

/-- For positive a, b with b > a (general case via native grid analysis).

The proof uses the native grids of `s` and `bv` (not the fine grid `g`).
Since `bv ≥ s/2`, we have `s − bv ≤ bv < 2^(bv.e + 1)`, so the
coefficient on grid `bv.e − prec + 1` is `< 2^prec`. -/
theorem split_s_sub_bv_grid
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeGrid R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (a.toVal : R) < b.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = s.toVal - bv.toVal := by
  -- Trivial case
  by_cases hval : (s.toVal : R) - bv.toVal = 0
  · exact ⟨0, Or.inl rfl, by rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hval.symm⟩
  -- Establish key bounds
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hs_ge_2a := round_sum_ge_two_a (R := R) a b s ha hb ha_nz hb_nz hab hsum_ne hs
  have hs_pos : (0 : R) < s.toVal := by linarith
  have hbv_ge := bv_ge_half_s (R := R) a s ha ha_nz hs_pos hs_ge_2a bv hbv
  have hbv_le := bv_le_s (R := R) a s ha_pos bv hbv
  -- bv is positive (since s/2 > 0)
  have hbv_pos : (0 : R) < bv.toVal := by linarith
  have hbv_s : bv.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr hbv_pos).1
  have hbv_nz : 0 < bv.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hbv_pos).2
  -- s − bv ≤ bv (from s ≤ 2bv) and s − bv ≥ 0 (from bv ≤ s)
  have hsbv_nonneg : (0 : R) ≤ s.toVal - bv.toVal := by linarith
  have hsbv_le_bv : (s.toVal : R) - bv.toVal ≤ bv.toVal := by linarith
  -- bv.e ≤ s.e (from bv ≤ s)
  have hs_s : s.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).1
  have hs_nz : 0 < s.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).2
  have hbv_e_le : bv.e ≤ s.e := by
    rcases bv.isNormal_or_isSubnormal with hn | hsub
    · -- Normal bv: bv.toVal ≥ 2^bv.e. If bv.e > s.e then bv > s, contradiction.
      by_contra h; push_neg at h
      have := FiniteFp.toVal_normal_lower (R := R) bv hbv_s hn
      have := FiniteFp.toVal_lt_zpow_succ (R := R) s hs_s
      linarith [two_zpow_mono (R := R) (show s.e + 1 ≤ bv.e from by omega)]
    · -- Subnormal bv: bv.e = min_exp ≤ s.e
      exact le_trans (le_of_eq hsub.1) s.valid.1
  -- Grid setup: g = bv.e - prec + 1
  set g := bv.e - prec + 1 with g_def
  -- Get integer coefficients on grid g
  obtain ⟨ns, hns⟩ := FiniteFp.toVal_int_mul_zpow (R := R) s hs_s g (by omega)
  obtain ⟨nbv, hnbv⟩ := FiniteFp.toVal_int_mul_zpow (R := R) bv hbv_s g (le_refl _)
  -- s - bv = (ns - nbv) * 2^g
  have hg_pos : (0 : R) < (2 : R) ^ g := by positivity
  have hdiff_eq : (s.toVal : R) - bv.toVal = ((ns - nbv : ℤ) : R) * (2 : R) ^ g := by
    rw [hns, hnbv]; push_cast; ring
  -- ns - nbv > 0 (from hval : s - bv ≠ 0)
  have hcoeff_pos : 0 < ns - nbv := by
    by_contra h; push_neg at h
    have : (s.toVal : R) - bv.toVal ≤ 0 := by
      rw [hdiff_eq]; exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) (le_of_lt hg_pos)
    exact hval (le_antisymm this hsbv_nonneg)
  -- ns - nbv < 2^prec (from s - bv ≤ bv < 2^(bv.e + 1) = 2^prec * 2^g)
  have hbv_lt := FiniteFp.toVal_lt_zpow_succ (R := R) bv hbv_s
  have hcoeff_bound : ns - nbv < (2 : ℤ) ^ precNat := by
    have h1 : ((ns - nbv : ℤ) : R) * (2 : R) ^ g < (2 : R) ^ (bv.e + 1) := by
      rw [← hdiff_eq]; linarith
    have hprec_eq : (bv.e + 1 : ℤ) = ↑precNat + g := by
      rw [g_def]; have := FloatFormat.valid_prec; omega
    rw [hprec_eq] at h1
    have h2 : (2 : R) ^ (↑precNat + g) = (2 : R) ^ precNat * (2 : R) ^ g := by
      rw [zpow_add₀ (by norm_num : (2 : R) ≠ 0), zpow_natCast]
    rw [h2] at h1
    have h3 : ((ns - nbv : ℤ) : R) < (2 : R) ^ precNat := by
      nlinarith [hg_pos.le]
    exact_mod_cast h3
  have hcoeff_ne : ns - nbv ≠ 0 := by omega
  have hcoeff_natAbs : (ns - nbv).natAbs < 2 ^ precNat := by
    exact_mod_cast show (↑(ns - nbv).natAbs : ℤ) < (2 : ℤ) ^ precNat from by
      rw [Int.natAbs_of_nonneg (le_of_lt hcoeff_pos)]; exact hcoeff_bound
  -- Construct the FiniteFp
  obtain ⟨f, hf_valid, hfv⟩ := exists_finiteFp_of_int_mul_zpow (R := R) (ns - nbv) g
    hcoeff_ne hcoeff_natAbs (by rw [g_def]; have := bv.valid.1; omega)
    (by rw [g_def]; have := bv.valid.2.1; omega)
  exact ⟨f, hf_valid, by rw [hfv, ← hdiff_eq]⟩

/-- For positive a, b with b > a, `b − bv` is representable.

Uses the native grid of `min(b.e, bv.e)`. Since `b/2 ≤ bv ≤ 2b`, the
exponents satisfy `bv.e ≥ b.e - 1`, and the coefficient of `b - bv` on
the common grid is bounded by `2^prec` in both cases:
- `bv.e ≥ b.e`: `|b - bv| ≤ b < 2^(b.e+1)`, grid step `2^(b.e-p+1)`, coeff `< 2^p`
- `bv.e = b.e - 1`: `b - bv ≤ b/2 < 2^b.e`, grid step `2^(b.e-p)`, coeff `< 2^p` -/
theorem split_b_sub_bv_grid
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeGrid R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (a.toVal : R) < b.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = b.toVal - bv.toVal := by
  -- Step 0: Basic positivity
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  -- Step 1: Get s as Fp.finite from correctness
  have hs_fp : (a : Fp) + b = Fp.finite s := by
    have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
    simp only [add_finite_eq_fpAddFinite] at hcorr
    exact hcorr.trans hs
  -- Step 2: s ≥ b (from monotonicity + idempotence, since a+b > b)
  have hs_ge_b : (b.toVal : R) ≤ s.toVal := by
    have hab_sum : (b.toVal : R) ≤ a.toVal + b.toVal := by linarith
    have hmono : ○(b.toVal (R := R)) ≤ ○((a.toVal : R) + b.toVal) :=
      RModeMono.round_mono (R := R) hab_sum
    have hround_b := RModeIdem.round_idempotent (R := R) b (Or.inl hb)
    rw [hround_b, hs] at hmono
    exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff b s).mp hmono)
  -- Step 3: s ≤ 2b (swap a,b in round_sum_le_double)
  have hs_le_2b : (s.toVal : R) ≤ 2 * b.toVal := by
    have hba_fp : (b : Fp) + a = Fp.finite s := by
      rw [show (b : Fp) + a = fpAdd b a from rfl, show fpAdd (↑b) (↑a) = fpAddFinite b a from rfl,
          fpAddFinite_comm, show fpAddFinite a b = fpAdd (↑a) (↑b) from rfl,
          show fpAdd (↑a) (↑b) = (a : Fp) + b from rfl]
      exact hs_fp
    have hsum_ne' : (b.toVal : R) + a.toVal ≠ 0 := by rw [add_comm]; exact hsum_ne
    exact round_sum_le_double (R := R) b a hb ha hb_nz (le_of_lt hab) hsum_ne' s hba_fp
  have hs_pos : (0 : R) < s.toVal := lt_of_lt_of_le hb_pos hs_ge_b
  have hs_s : s.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).1
  have hs_nz : 0 < s.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).2
  -- Step 4: bv bounds from existing lemmas
  have hs_ge_2a : 2 * (a.toVal : R) ≤ s.toVal :=
    round_sum_ge_two_a (R := R) a b s ha hb ha_nz hb_nz hab hsum_ne hs
  have hbv_le_s : bv.toVal (R := R) ≤ s.toVal :=
    bv_le_s (R := R) a s ha_pos bv hbv
  have hbv_ge_half_s : s.toVal (R := R) ≤ 2 * bv.toVal :=
    bv_ge_half_s (R := R) a s ha ha_nz hs_pos hs_ge_2a bv hbv
  -- Step 5: Combined bounds: b/2 ≤ bv ≤ 2b
  have hbv_ge_half_b : (b.toVal : R) ≤ 2 * bv.toVal := by linarith
  have hbv_le_2b : (bv.toVal : R) ≤ 2 * b.toVal := by linarith
  have hbv_pos : (0 : R) < bv.toVal := by linarith
  have hbv_s : bv.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr hbv_pos).1
  have hbv_nz : 0 < bv.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hbv_pos).2
  -- Step 6: Handle zero difference
  by_cases hdiff_zero : (b.toVal : R) - bv.toVal = 0
  · exact ⟨0, Or.inl rfl, by rw [FiniteFp.toVal_isZero (R := R) rfl]; linarith⟩
  -- Step 7: Grid coefficients on min(b.e, bv.e) grid
  set g := min b.e bv.e - prec + 1 with g_def
  obtain ⟨nb, hnb⟩ := FiniteFp.toVal_int_mul_zpow (R := R) b hb g (by omega)
  obtain ⟨nbv, hnbv⟩ := FiniteFp.toVal_int_mul_zpow (R := R) bv hbv_s g (by omega)
  -- Step 8: Difference on grid
  have hdiff_eq : (b.toVal : R) - bv.toVal = ((nb - nbv : ℤ) : R) * (2 : R) ^ g := by
    rw [hnb, hnbv]; push_cast; ring
  -- Step 9: Nonzero coefficient
  have hcoeff_ne : nb - nbv ≠ 0 := by
    intro h; apply hdiff_zero; rw [hdiff_eq, h]; simp
  -- Step 10: Coefficient bound |nb - nbv| < 2^prec
  -- Need |b - bv| < 2^(min(b.e, bv.e) + 1) = 2^precNat * 2^g
  have hg_pos : (0 : R) < (2 : R) ^ g := by positivity
  have hcoeff_bound : (nb - nbv).natAbs < 2 ^ precNat := by
    -- First establish bv.e ≥ b.e - 1 (from bv ≥ b/2 > 0)
    -- Proof: bv ≥ b/2 > 0 and bv < 2^(bv.e+1), so 2^(bv.e+1) > b/2.
    -- Also b < 2^(b.e+1), so b/2 < 2^b.e. If bv.e+1 ≤ b.e-1 then
    -- 2^(bv.e+1) ≤ 2^(b.e-1) < b/2 ... wait, we need the reverse.
    -- From bv.toVal < 2^(bv.e+1) and bv ≥ b/2: b/2 ≤ bv < 2^(bv.e+1).
    -- So b < 2 * 2^(bv.e+1) = 2^(bv.e+2). But b > 0 and b < 2^(b.e+1).
    -- We need b.e - 1 ≤ bv.e, i.e., bv.e + 2 > b.e, i.e., 2^(bv.e+2) > 2^b.e.
    have hbv_e_ge : b.e - 1 ≤ bv.e := by
      by_contra h; push_neg at h
      -- bv.e ≤ b.e - 2, so bv.e + 1 ≤ b.e - 1
      have hbv_lt := FiniteFp.toVal_lt_zpow_succ (R := R) bv hbv_s
      -- bv < 2^(bv.e+1) ≤ 2^(b.e-1) (since bv.e+1 ≤ b.e-1)
      have h2 : (2 : R) ^ (bv.e + 1) ≤ (2 : R) ^ (b.e - 1) :=
        two_zpow_mono (R := R) (by omega)
      -- So bv < 2^(b.e-1), hence 2*bv < 2^b.e
      have hbv_small : 2 * bv.toVal (R := R) < (2 : R) ^ b.e := by
        calc 2 * bv.toVal < 2 * (2 : R) ^ (bv.e + 1) := by linarith
          _ ≤ 2 * (2 : R) ^ (b.e - 1) := by linarith [two_zpow_mono (R := R) (show bv.e + 1 ≤ b.e - 1 from by omega)]
          _ = (2 : R) ^ b.e := by rw [show b.e = b.e - 1 + 1 from by omega,
              zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]; ring
      -- But b ≤ 2*bv (from hbv_ge_half_b) and b.toVal > 0
      -- Need b > 2^b.e or b ≥ 2^b.e... not directly available.
      -- Actually: b ≤ 2*bv < 2^b.e. But also b > 0. No contradiction yet.
      -- Wait: for normal b, b ≥ 2^b.e. For subnormal b, b.e = min_exp.
      -- If b is subnormal: b.e = min_exp, bv.e ≥ min_exp = b.e, so bv.e ≥ b.e,
      -- contradicting bv.e ≤ b.e - 2.
      -- So b must be normal: b ≥ 2^b.e. But b ≤ 2*bv < 2^b.e. Contradiction!
      rcases b.isNormal_or_isSubnormal with hbn | hbs
      · -- b normal: b.toVal ≥ 2^b.e
        have hb_ge := FiniteFp.toVal_normal_lower (R := R) b hb hbn
        linarith
      · -- b subnormal: b.e = min_exp, bv.e ≥ min_exp = b.e, contradiction
        have hbe_eq : b.e = FloatFormat.min_exp := hbs.1
        have : bv.e ≥ FloatFormat.min_exp := bv.valid.1
        omega
    -- Show |b - bv| < 2^(min(b.e, bv.e) + 1)
    have h_diff_lt : |(b.toVal (R := R) - bv.toVal)| < (2 : R) ^ (min b.e bv.e + 1) := by
      rcases le_or_gt b.e bv.e with hbe | hbe
      · -- bv.e ≥ b.e: min = b.e. |b - bv| ≤ b < 2^(b.e+1)
        rw [min_eq_left hbe]
        have : |b.toVal (R := R) - bv.toVal| ≤ b.toVal := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith [FiniteFp.toVal_lt_zpow_succ (R := R) b hb]
      · -- bv.e < b.e: min = bv.e, bv.e = b.e - 1 (from hbv_e_ge)
        -- Since bv.e < b.e and bv.e ≥ b.e - 1: bv.e = b.e - 1
        have hbve : bv.e = b.e - 1 := by omega
        rw [min_eq_right (le_of_lt hbe)]
        -- b - bv ≤ b/2 (from bv ≥ b/2) and bv - b ≤ 0 (bv < 2^(bv.e+1) = 2^b.e ≤ b)
        -- So |b - bv| = b - bv ≤ b/2 < 2^(b.e+1)/2 = 2^b.e = 2^(bv.e+1)
        have hbv_lt_b : bv.toVal (R := R) ≤ b.toVal := by
          have hbv_lt_zpow := FiniteFp.toVal_lt_zpow_succ (R := R) bv hbv_s
          rw [hbve, show b.e - 1 + 1 = b.e from by omega] at hbv_lt_zpow
          have hb_ge : (2 : R) ^ b.e ≤ b.toVal := by
            -- b must be normal: if subnormal, b.e = min_exp ≤ bv.e, contradicting hbe
            rcases b.isNormal_or_isSubnormal with hbn | hbs
            · exact FiniteFp.toVal_normal_lower (R := R) b hb hbn
            · exfalso; have := bv.valid.1; omega
          linarith
        have habs : |b.toVal (R := R) - bv.toVal| = b.toVal - bv.toVal := by
          rw [abs_of_nonneg]; linarith
        rw [habs, hbve]
        have hbe_simp : b.e - 1 + 1 = b.e := by omega
        calc b.toVal - bv.toVal ≤ b.toVal / 2 := by linarith  -- from bv ≥ b/2
          _ < (2 : R) ^ (b.e + 1) / 2 := by
              linarith [FiniteFp.toVal_lt_zpow_succ (R := R) b hb]
          _ = (2 : R) ^ b.e := by
              rw [zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]; ring
          _ = (2 : R) ^ (b.e - 1 + 1) := by rw [hbe_simp]
    -- From |diff| < 2^(min + 1) = 2^precNat * 2^g, cancel 2^g
    have hprec_eq : min b.e bv.e + 1 = ↑precNat + g := by
      simp [g_def]; have := FloatFormat.valid_prec; omega
    rw [hprec_eq] at h_diff_lt
    have h2 : (2 : R) ^ (↑precNat + g) = (2 : R) ^ precNat * (2 : R) ^ g := by
      rw [zpow_add₀ (by norm_num : (2 : R) ≠ 0), zpow_natCast]
    rw [h2] at h_diff_lt
    rw [hdiff_eq, abs_mul, abs_of_pos hg_pos] at h_diff_lt
    have h_abs_lt : |((nb - nbv : ℤ) : R)| < (2 : R) ^ precNat := by
      nlinarith [hg_pos.le]
    have h_abs_int : |(nb - nbv : ℤ)| < (2 : ℤ) ^ precNat := by exact_mod_cast h_abs_lt
    exact_mod_cast show (↑(nb - nbv).natAbs : ℤ) < (2 : ℤ) ^ precNat from by
      simp only [Int.natCast_natAbs]; linarith [abs_nonneg (nb - nbv : ℤ)]
  -- Step 11: Grid bounds for exists_finiteFp_of_int_mul_zpow
  have hg_lo : g ≥ FloatFormat.min_exp - prec + 1 := by
    simp [g_def]; constructor <;> (have := b.valid.1; have := bv.valid.1; omega)
  have hg_hi : g + prec - 1 ≤ FloatFormat.max_exp := by
    simp [g_def]; have := b.valid.2.1; have := bv.valid.2.1; omega
  -- Step 12: Construct float
  obtain ⟨f, hf_valid, hfv⟩ := exists_finiteFp_of_int_mul_zpow (R := R) (nb - nbv) g
    hcoeff_ne hcoeff_bound hg_lo hg_hi
  exact ⟨f, hf_valid, by rw [hfv, ← hdiff_eq]⟩

/-- Positive-case split_s_sub_bv: combines Sterbenz and grid cases. -/
theorem split_s_sub_bv_pos
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeGrid R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = s.toVal - bv.toVal := by
  rcases le_or_gt (b.toVal (R := R)) a.toVal with hab | hab
  · exact split_s_sub_bv_sterbenz a b s ha hb ha_nz hb_nz hab hsum_ne hs bv hbv
  · exact split_s_sub_bv_grid a b s ha hb ha_nz hb_nz hab hsum_ne hs bv hbv

/-- Positive-case split_b_sub_bv: combines Sterbenz and grid cases. -/
theorem split_b_sub_bv_pos
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeGrid R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = b.toVal - bv.toVal := by
  rcases le_or_gt (b.toVal (R := R)) a.toVal with hab | hab
  · exact split_b_sub_bv_sterbenz a b s ha hb ha_nz hb_nz hab hsum_ne hs bv hbv
  · exact split_b_sub_bv_grid a b s ha hb ha_nz hb_nz hab hsum_ne hs bv hbv

end SplitPositive
