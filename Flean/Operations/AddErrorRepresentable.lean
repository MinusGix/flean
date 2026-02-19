import Flean.Operations.Sterbenz
import Flean.Operations.MulPow2

/-! # Addition Error Representability

The rounding error of floating-point addition is exactly representable as a float.
This is the core mathematical fact underlying error-free transformations (2Sum, Fast2Sum).

## Key results

- `round_sum_ge_left`: rounded sum of positive values ≥ the larger operand
- `round_sum_le_double`: rounded sum of positive values with `a ≥ b` is ≤ 2a
- `add_error_representable`: the rounding error `(a + b) - fl(a + b)` is representable
-/

section AddErrorRepresentable

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Rounded sum bounds -/

/-- The rounded sum of positive values is at least as large as the larger operand. -/
theorem round_sum_ge_left (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false) (_ha_nz : 0 < a.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeMono R] [RModeIdem R]
    (hs : a + b = s_fp) :
    (a.toVal : R) ≤ s_fp.toVal := by
  have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
  simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at hs hcorr
  have hs_round := hcorr.symm.trans hs
  have hb_nonneg : (0 : R) ≤ b.toVal := by
    rw [FiniteFp.toVal_pos_eq b hb]; positivity
  have hmono : ○(a.toVal (R := R)) ≤ ○(a.toVal + b.toVal) :=
    RModeMono.round_mono (R := R) (le_add_of_nonneg_right hb_nonneg)
  have hround_a : ○(a.toVal (R := R)) = a :=
    RModeIdem.round_idempotent (R := R) a (Or.inl ha)
  rw [hround_a] at hmono; rw [hs_round] at hmono
  exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff a s_fp).mp hmono)

/-- The rounded sum of positive values with `a ≥ b` is at most `2a`. -/
theorem round_sum_le_double (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false) (ha_nz : 0 < a.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeMono R] [RModeIdem R]
    (hs : a + b = s_fp) :
    (s_fp.toVal : R) ≤ 2 * a.toVal := by
  have hs_orig := hs
  have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
  simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at hs hcorr
  have hs_round := hcorr.symm.trans hs
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hab_le : (a.toVal : R) + b.toVal ≤ 2 * a.toVal := by linarith
  by_cases he : a.e + 1 ≤ FloatFormat.max_exp
  · -- Case 1: 2a representable via exponent shift
    obtain ⟨d, hds, hdv⟩ := mul_pow2_representable (R := R) a 1 ha_nz ha
      (by have := a.valid.1; omega) he
    have hdv' : (d.toVal : R) = 2 * a.toVal := by rw [hdv, zpow_one]; ring
    have hmono : ○((a.toVal : R) + b.toVal) ≤ ○(d.toVal (R := R)) :=
      RModeMono.round_mono (R := R) (by rw [hdv']; exact hab_le)
    have hround_d := RModeIdem.round_idempotent (R := R) d (Or.inl hds)
    rw [hround_d] at hmono; rw [hs_round] at hmono
    linarith [FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff s_fp d).mp hmono)]
  · -- Case 2: a.e = max_exp
    push_neg at he
    have ha_e_eq : a.e = FloatFormat.max_exp := le_antisymm a.valid.2.1 (by omega)
    have hs_s : s_fp.s = false := by
      have hs_ge := round_sum_ge_left (R := R) a b ha hb ha_nz hsum_ne s_fp hs_orig
      exact ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).1
    have hs_bound : s_fp.toVal (R := R) < (2 : R) ^ (FloatFormat.max_exp + 1) :=
      calc s_fp.toVal (R := R) < (2 : R) ^ (s_fp.e + 1) :=
            FiniteFp.toVal_lt_zpow_succ s_fp hs_s
        _ ≤ (2 : R) ^ (FloatFormat.max_exp + 1) :=
            zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2) (by linarith [s_fp.valid.2.1])
    by_cases ha_normal : _root_.isNormal a.m
    · -- a is normal at max_exp: 2a ≥ 2^(max_exp+1)
      have ha_lower := FiniteFp.toVal_normal_lower (R := R) a ha ha_normal
      have : (2 : R) ^ FloatFormat.max_exp ≤ a.toVal := by rwa [ha_e_eq] at ha_lower
      have : 2 * (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ (FloatFormat.max_exp + 1) :=
        by rw [mul_comm, ← zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]
      linarith
    · -- a is subnormal: min_exp = max_exp, 2*a.m < 2^prec, so 2a representable
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
      have hmono : ○((a.toVal : R) + b.toVal) ≤ ○(d.toVal (R := R)) :=
        RModeMono.round_mono (R := R) (by rw [hdv']; exact hab_le)
      rw [RModeIdem.round_idempotent (R := R) d (Or.inl hds)] at hmono; rw [hs_round] at hmono
      linarith [FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff s_fp d).mp hmono)]

/-! ## Error representability -/

/-- For positive x in normal range, any nearest-mode finite result f satisfies
    `f.toVal ≤ 2x − pred.toVal`, where pred is the floor (roundDown) of x.
    This encodes that nearest rounding never overshoots the "reflected predecessor"
    bound, i.e., the result + pred ≤ 2x. -/
private theorem nearest_round_le_two_x_sub_pred
    [RMode R] [RModeNearest R]
    (x : R) (hxpos : 0 < x) (hx : isNormalRange x)
    (f : FiniteFp) (hf : ○x = f) :
    (f.toVal : R) ≤ 2 * x - (findPredecessorPos x hxpos).toVal := by
  exact RModeNearest.round_le_two_x_sub_pred (R := R) x hxpos hx f hf

/-- For positive x in normal range, any nearest-mode finite result f satisfies
    `2x − succ.toVal ≤ f.toVal`, where succ is the ceiling (roundUp) of x.
    This is the dual of `nearest_round_le_two_x_sub_pred`. -/
private theorem nearest_round_ge_two_x_sub_succ
    [RMode R] [RModeNearest R]
    (x : R) (hxpos : 0 < x) (hx : isNormalRange x)
    (f : FiniteFp) (hf : ○x = f) (succ : FiniteFp)
    (hsucc : findSuccessorPos x hxpos = Fp.finite succ) :
    (2 * x - succ.toVal : R) ≤ f.toVal :=
  RModeNearest.round_ge_two_x_sub_succ (R := R) x hxpos hx f succ hf hsucc

/-- The rounding error of a nearest-mode addition of positive floats with `|b| ≤ |a|`
is representable as a float. -/
theorem add_error_representable (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (t_fp.s = false ∨ 0 < t_fp.m) ∧
        (t_fp.toVal : R) = (a.toVal : R) + b.toVal - s_fp.toVal := by
  -- Step A: Handle error = 0
  by_cases herr : (a.toVal : R) + b.toVal - s_fp.toVal = 0
  · exact ⟨0, Or.inl rfl, by
      rw [show (0 : FiniteFp).toVal (R := R) = 0 from FiniteFp.toVal_isZero rfl]; linarith⟩
  -- Step B: Basic facts
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hval_pos : (0 : R) < a.toVal + b.toVal := by linarith
  have hsum_round : a + b =
      RMode.round ((a.toVal : R) + b.toVal) := by
    simpa using (fpAddFinite_correct (R := R) a b hsum_ne)
  have hs_correct : RMode.round ((a.toVal : R) + b.toVal) = s_fp := by
    rw [← hsum_round]
    exact hs
  have hs_ge_a := round_sum_ge_left (R := R) a b ha hb ha_nz hsum_ne s_fp hs
  have hs_s : s_fp.s = false :=
    ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).1
  -- Step B': Prove a is normal (subnormal sums are exact → error = 0)
  have ha_normal : _root_.isNormal a.m := by
    by_contra h_not_normal
    have ha_sub := a.isNormal_or_isSubnormal.resolve_left h_not_normal
    -- b is also subnormal (since b.toVal ≤ a.toVal < 2^min_exp)
    have hb_not_normal : ¬_root_.isNormal b.m := by
      intro hb_norm
      linarith [FiniteFp.toVal_subnormal_lt (R := R) a ha ha_sub,
                FiniteFp.toVal_normal_lower (R := R) b hb hb_norm,
                two_zpow_mono (R := R) b.valid.1]
    have hb_sub := b.isNormal_or_isSubnormal.resolve_left hb_not_normal
    -- Subnormal significands are < 2^(prec-1), so sum < 2^prec
    have hfit : a.m + b.m < 2 ^ precNat := by
      have := ha_sub.2; have := hb_sub.2
      rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub] at *
      have : 0 < precNat := by have := FloatFormat.valid_prec; omega
      have : 2 ^ (precNat - 1) + 2 ^ (precNat - 1) = 2 ^ precNat := by
        set k := precNat - 1; rw [show precNat = k + 1 from by omega, pow_succ]; omega
      omega
    obtain ⟨g, _, hg_exact⟩ := subnormal_sum_exact (R := R) a b ha hb hb_nz.ne' ha_sub hb_sub hfit
    have hgv : (g.toVal : R) = a.toVal + b.toVal := by
      simpa [Fp.Represents] using hg_exact.2
    have hround_g : ○((a.toVal : R) + b.toVal) = g := by
      simpa using hg_exact.1
    have : s_fp = g := Fp.finite.inj (hs_correct.symm.trans hround_g)
    exact absurd (show (a.toVal : R) + b.toVal - s_fp.toVal = 0 by
      rw [this, hgv]; ring) herr
  -- Step C: isNormalRange(a+b)
  have hNR : isNormalRange ((a.toVal : R) + b.toVal) := by
    constructor
    · calc (2 : R) ^ FloatFormat.min_exp
          ≤ (2 : R) ^ a.e := two_zpow_mono (R := R) a.valid.1
        _ ≤ a.toVal := FiniteFp.toVal_normal_lower (R := R) a ha ha_normal
        _ ≤ a.toVal + b.toVal := le_add_of_nonneg_right (le_of_lt hb_pos)
    · by_contra h_high; push_neg at h_high
      have h_ot_le : FloatFormat.overflowThreshold R ≤ (a.toVal : R) + b.toVal :=
        le_of_lt (lt_of_lt_of_le FloatFormat.overflowThreshold_lt_zpow_max_exp_succ h_high)
      have hround_inf : ○((a.toVal : R) + b.toVal) = Fp.infinite false :=
        RModeNearest.overflow_pos_inf (R := R) _ h_ot_le
      exact absurd (hs_correct.symm.trans hround_inf) (by simp)
  -- Step D: Error bound |error| ≤ b via helper + roundDown ≥ a
  set pred := findPredecessorPos ((a.toVal : R) + b.toVal) hval_pos with pred_def
  have hhelper := nearest_round_le_two_x_sub_pred (R := R) _ hval_pos hNR s_fp hs_correct
  have hD_eq : roundDown ((a.toVal : R) + b.toVal) = Fp.finite pred := by
    unfold roundDown; rw [findPredecessor_pos_eq _ hval_pos]
  have hpred_ge_a : (a.toVal : R) ≤ pred.toVal :=
    FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff a pred).mp
      (hD_eq ▸ roundDown_ge_of_fp_le _ a (Or.inl ha) (le_add_of_nonneg_right (le_of_lt hb_pos))))
  have herr_le_b : (a.toVal : R) + b.toVal - s_fp.toVal ≤ b.toVal := by linarith
  have herr_ge_neg_b : -(b.toVal : R) ≤ (a.toVal : R) + b.toVal - s_fp.toVal := by linarith
  -- Step E: Express error = r * 2^e₀ as integer × power of 2
  set e_min := min a.e b.e with e_min_def
  set e₀ := e_min - prec + 1 with e₀_def
  have hexact := fpAddFinite_exact_sum R a b
  set isum := addAlignedSumInt a b with isum_def
  -- s_fp.e ≥ e_min
  have ha_e_le_s : a.e ≤ s_fp.e := by
    by_contra h; push_neg at h
    linarith [FiniteFp.toVal_normal_lower (R := R) a ha ha_normal,
              FiniteFp.toVal_lt_zpow_succ (R := R) s_fp hs_s,
              two_zpow_mono (R := R) (show s_fp.e + 1 ≤ a.e by omega)]
  have he_min_le_s : e_min ≤ s_fp.e := le_trans (min_le_left _ _) ha_e_le_s
  -- Factor s_fp.toVal as integer * 2^e₀
  set k := (s_fp.e - e_min).toNat with k_def
  have hk_eq : (k : ℤ) = s_fp.e - e_min := Int.toNat_of_nonneg (by omega)
  have hs_toVal : (s_fp.toVal : R) = ((s_fp.m : ℤ) * 2 ^ k : ℤ) * (2 : R) ^ e₀ := by
    rw [FiniteFp.toVal_factor_zpow (R := R) s_fp hs_s e₀,
        show s_fp.e - prec + 1 - e₀ = s_fp.e - e_min from by omega,
        show (s_fp.e - e_min : ℤ) = ↑k from hk_eq.symm, zpow_natCast]
    push_cast; ring
  -- Define integer error
  set r := isum - (s_fp.m : ℤ) * 2 ^ k with r_def
  have herr_eq : (a.toVal : R) + b.toVal - s_fp.toVal = (r : R) * (2 : R) ^ e₀ := by
    rw [hexact, hs_toVal, r_def]; push_cast; ring
  have hr_ne : r ≠ 0 := by
    intro h; apply herr; rw [herr_eq, h, Int.cast_zero, zero_mul]
  -- Step F: Bound |r| < 2^prec
  have he₀_pos : (0 : R) < (2 : R) ^ e₀ := zpow_pos (by norm_num) _
  -- |error| ≤ b.toVal, and b.toVal = b.m * 2^(b.e - e_min) * 2^e₀
  have hb_e_ge : b.e ≥ e_min := min_le_right a.e b.e
  have hb_factor : (b.toVal : R) = (b.m : R) * (2 : R) ^ ((b.e - e_min : ℤ)) * (2 : R) ^ e₀ := by
    rw [FiniteFp.toVal_factor_zpow (R := R) b hb e₀, show b.e - prec + 1 - e₀ = b.e - e_min from by omega]
  have hr_abs_le : |(r : R)| ≤ (b.m : R) * (2 : R) ^ (b.e - e_min : ℤ) := by
    have herr_abs : |(a.toVal + b.toVal - s_fp.toVal : R)| ≤ b.toVal :=
      abs_le.mpr ⟨herr_ge_neg_b, herr_le_b⟩
    rw [herr_eq, abs_mul, abs_of_pos he₀_pos] at herr_abs
    rw [hb_factor] at herr_abs
    -- herr_abs : |↑r| * 2^e₀ ≤ ↑b.m * 2^(b.e - e_min) * 2^e₀
    exact le_of_mul_le_mul_of_pos_right herr_abs he₀_pos
  -- Bound b.m * 2^(b.e - e_min) < 2^prec (works in both min cases)
  have hbm_shifted_lt : (b.m : R) * (2 : R) ^ (b.e - e_min : ℤ) < (2 : R) ^ precNat := by
    rcases le_or_gt b.e a.e with hba | hab_e
    · -- b.e ≤ a.e: e_min = b.e, shift = 0
      have : e_min = b.e := min_eq_right hba
      rw [this, sub_self, zpow_zero, mul_one]
      exact_mod_cast b.valid.2.2.1
    · -- a.e < b.e: e_min = a.e, shift = b.e - a.e
      have he : e_min = a.e := min_eq_left (le_of_lt hab_e)
      rw [he]
      -- From b.toVal ≤ a.toVal and zpow factoring
      have hle_R : (b.m : R) * (2:R) ^ (b.e - prec + 1) ≤ (a.m : R) * (2:R) ^ (a.e - prec + 1) := by
        rw [← FiniteFp.toVal_pos_eq a ha, ← FiniteFp.toVal_pos_eq b hb]; exact hab
      have hd_pos : (0 : R) < (2:R) ^ (a.e - prec + 1) := zpow_pos (by norm_num) _
      -- Factor: b.m * 2^(b.e-prec+1) = b.m * 2^(b.e-a.e) * 2^(a.e-prec+1)
      have hfactor : (b.m : R) * (2:R)^(b.e - prec + 1)
          = (b.m : R) * (2:R)^(b.e - a.e : ℤ) * (2:R)^(a.e - prec + 1) := by
        rw [show (b.e - prec + 1 : ℤ) = (b.e - a.e) + (a.e - prec + 1) from by omega,
            zpow_add₀ (by norm_num : (2:R) ≠ 0), mul_assoc]
      rw [hfactor] at hle_R
      have : (b.m : R) * (2:R) ^ (b.e - a.e : ℤ) ≤ (a.m : R) :=
        le_of_mul_le_mul_of_pos_right hle_R hd_pos
      calc (b.m : R) * (2:R) ^ (b.e - a.e : ℤ)
          ≤ (a.m : R) := this
        _ < (2 : R) ^ precNat := by exact_mod_cast a.valid.2.2.1
  -- Convert to natAbs bound
  have hr_natAbs_lt : r.natAbs < 2 ^ precNat := by
    have h1 : |(r : R)| < (2 : R) ^ precNat := lt_of_le_of_lt hr_abs_le hbm_shifted_lt
    have h2 : (r.natAbs : R) < (2 : R) ^ precNat := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact h1
    exact_mod_cast h2
  -- Step G: Construct the float
  have he_lo : e₀ ≥ FloatFormat.min_exp - prec + 1 := by
    simp only [e₀_def, e_min_def]; have := le_min a.valid.1 b.valid.1; omega
  have he_hi : e₀ + prec - 1 ≤ FloatFormat.max_exp := by
    simp only [e₀_def, e_min_def]; have := min_le_left a.e b.e; have := a.valid.2.1; omega
  obtain ⟨f, hf_valid, hfv⟩ := exists_finiteFp_of_int_mul_zpow (R := R) r e₀
    hr_ne hr_natAbs_lt he_lo he_hi
  exact ⟨f, hf_valid, by rw [hfv, herr_eq]⟩

/-! ## Mixed-sign error representability -/

/-- The rounding error of a nearest-mode addition of mixed-sign floats
(a > 0, b < 0) with |b| ≤ a is representable as a float. -/
private theorem add_error_representable_mixed (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = true)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : |b.toVal (R := R)| ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (t_fp.s = false ∨ 0 < t_fp.m) ∧
        (t_fp.toVal : R) = (a.toVal : R) + b.toVal - s_fp.toVal := by
  -- Step A: Handle error = 0
  by_cases herr : (a.toVal : R) + b.toVal - s_fp.toVal = 0
  · exact ⟨0, Or.inl rfl, by
      rw [show (0 : FiniteFp).toVal (R := R) = 0 from FiniteFp.toVal_isZero rfl]; linarith⟩
  -- Step B: Basic facts
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_neg : (b.toVal : R) < 0 := by
    have := FiniteFp.toVal_pos (-b) (by simp [FiniteFp.neg_def, hb]) (by simp; exact hb_nz) (R := R)
    rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
  have habs_b : |b.toVal (R := R)| = -b.toVal := abs_of_neg hb_neg
  have hval_pos : (0 : R) < a.toVal + b.toVal := by
    have : -b.toVal ≤ (a.toVal : R) := habs_b ▸ hab
    rcases eq_or_lt_of_le (by linarith : (0 : R) ≤ a.toVal + b.toVal) with h | h
    · exact absurd (by linarith : (a.toVal : R) + b.toVal = 0) hsum_ne
    · exact h
  have hsum_round : a + b =
      RMode.round ((a.toVal : R) + b.toVal) := by
    simpa using (fpAddFinite_correct (R := R) a b hsum_ne)
  have hs_correct : RMode.round ((a.toVal : R) + b.toVal) = s_fp := by
    rw [← hsum_round]; exact hs
  -- Step B': Binade shortcut: if a+b < 2^min(a.e, b.e), the sum is exactly representable
  -- (because isum < 2^(prec-1) < 2^prec on the shared grid)
  rcases le_or_gt ((2 : R) ^ (min a.e b.e : ℤ)) ((a.toVal : R) + b.toVal) with
    h_binade | h_binade_lt
  swap
  · -- a+b < 2^min(a.e, b.e): the sum is exactly representable → error = 0
    exfalso; apply herr
    set e₀' := min a.e b.e - prec + 1
    have hexact' := fpAddFinite_exact_sum R a b
    set isum' := addAlignedSumInt a b
    have he₀'_pos : (0:R) < (2:R) ^ e₀' := zpow_pos (by norm_num) _
    have hisum'_pos : 0 < isum' := by
      by_contra h; push_neg at h
      have : (isum' : R) ≤ 0 := Int.cast_nonpos.mpr h
      linarith [mul_nonpos_of_nonpos_of_nonneg this (le_of_lt he₀'_pos)]
    have hisum'_bound : isum' < 2 ^ precNat := by
      suffices h : (isum' : R) < (2:R) ^ (precNat : ℤ) by
        rw [zpow_natCast] at h; exact_mod_cast h
      have h1 : (isum' : R) * (2:R) ^ e₀' < (2:R) ^ (min a.e b.e : ℤ) := by
        rw [← hexact']; exact h_binade_lt
      have h2 : (2:R) ^ (min a.e b.e : ℤ) = (2:R) ^ (prec - 1 : ℤ) * (2:R) ^ e₀' := by
        rw [← zpow_add₀ (by norm_num : (2:R) ≠ 0)]; congr 1; omega
      rw [h2] at h1
      have h3 : (isum' : R) < (2:R) ^ (prec - 1 : ℤ) :=
        lt_of_mul_lt_mul_of_nonneg_right h1 (le_of_lt he₀'_pos)
      calc (isum' : R) < (2:R) ^ (prec - 1 : ℤ) := h3
        _ ≤ (2:R) ^ (precNat : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by have := FloatFormat.valid_prec; omega)
    have hisum'_ne : isum' ≠ 0 := by omega
    have hisum'_natAbs : isum'.natAbs < 2 ^ precNat := by
      have : (isum'.natAbs : ℤ) < 2 ^ precNat := by
        rw [Int.natAbs_of_nonneg (le_of_lt hisum'_pos)]; exact_mod_cast hisum'_bound
      exact_mod_cast this
    have he₀'_lo : e₀' ≥ FloatFormat.min_exp - prec + 1 := by
      have := le_min a.valid.1 b.valid.1; omega
    have he₀'_hi : e₀' + prec - 1 ≤ FloatFormat.max_exp := by
      have := min_le_left a.e b.e; have := a.valid.2.1; omega
    obtain ⟨g, hg_valid, hgv⟩ := exists_finiteFp_of_int_mul_zpow (R := R) isum' e₀'
      hisum'_ne hisum'_natAbs he₀'_lo he₀'_hi
    have hgv' : (g.toVal : R) = a.toVal + b.toVal := by rw [hgv, hexact']
    have hround_g : ○((a.toVal : R) + b.toVal) = g :=
      RModeIdem.round_idempotent (R := R) g hg_valid ▸ (by rw [hgv'])
    have hcorr' := fpAddFinite_correct (R := R) a b hsum_ne
    simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at hs hcorr'
    have hs_eq : s_fp = g := Fp.finite.inj ((hcorr'.symm.trans hs).symm.trans hround_g)
    rw [hs_eq, hgv']; ring
  -- Step B'': s_fp.toVal ≥ 2^min(a.e, b.e) > 0 (via roundDown with a normal float reference)
  have he_valid : min a.e b.e ≥ FloatFormat.min_exp := le_min a.valid.1 b.valid.1
  have he_valid_hi : min a.e b.e ≤ FloatFormat.max_exp :=
    le_trans (min_le_left _ _) a.valid.2.1
  set g_ref : FiniteFp := ⟨false, min a.e b.e, 2^(FloatFormat.prec - 1).toNat,
    ⟨he_valid, he_valid_hi, FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec,
     Or.inl isNormal.sig_msb⟩⟩
  have hg_toVal : (g_ref.toVal : R) = (2:R) ^ (min a.e b.e : ℤ) := by
    show FiniteFp.toVal ⟨false, min a.e b.e, 2^(FloatFormat.prec - 1).toNat, _⟩ = _
    rw [FiniteFp.toVal_pos_eq _ rfl]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
        FloatFormat.prec_sub_one_toNat_eq, ← zpow_add₀ (by norm_num : (2:R) ≠ 0),
        show (prec - 1 : ℤ) + (min a.e b.e - prec + 1) = (min a.e b.e : ℤ) from by omega]
  have hg_le : (g_ref.toVal : R) ≤ (a.toVal : R) + b.toVal := hg_toVal ▸ h_binade
  have hg_rd := roundDown_ge_of_fp_le ((a.toVal : R) + b.toVal) g_ref (Or.inl rfl) hg_le
  have hrd := RModeNearest.roundDown_le_round (R := R) ((a.toVal : R) + b.toVal)
  rw [hs_correct] at hrd
  have hsfp_ge_g := Fp.le_trans hg_rd hrd
  have hsfp_ge : (g_ref.toVal : R) ≤ s_fp.toVal :=
    FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff _ _).mp hsfp_ge_g)
  have hs_pos : (0 : R) < s_fp.toVal := by
    have : (0:R) < (2:R) ^ (min a.e b.e : ℤ) := zpow_pos (by norm_num) _
    linarith [hg_toVal]
  have hs_s : s_fp.s = false :=
    ((FiniteFp.toVal_pos_iff (R := R)).mpr hs_pos).1
  -- Step C: isNormalRange(a+b)
  have h_normal_range : (2:R) ^ FloatFormat.min_exp ≤ (a.toVal : R) + b.toVal := by
    calc (2:R) ^ FloatFormat.min_exp
      ≤ (2:R) ^ (min a.e b.e : ℤ) := zpow_le_zpow_right₀ (by norm_num) he_valid
      _ ≤ _ := h_binade
  have hNR : isNormalRange ((a.toVal : R) + b.toVal) := by
    constructor
    · exact h_normal_range
    · by_contra h_high; push_neg at h_high
      have h_ot_le : FloatFormat.overflowThreshold R ≤ (a.toVal : R) + b.toVal :=
        le_of_lt (lt_of_lt_of_le FloatFormat.overflowThreshold_lt_zpow_max_exp_succ h_high)
      have hround_inf : ○((a.toVal : R) + b.toVal) = Fp.infinite false :=
        RModeNearest.overflow_pos_inf (R := R) _ h_ot_le
      exact absurd (hs_correct.symm.trans hround_inf) (by simp)
  -- Step D: Error bound |error| ≤ |b| via roundUp ≤ a + dual axiom
  -- Upper bound: round(a+b) ≤ a (monotonicity, since a+b ≤ a for b < 0)
  have hab_le_a : (a.toVal : R) + b.toVal ≤ a.toVal := by linarith
  have hs_le_a : (s_fp.toVal : R) ≤ a.toVal := by
    have hmono : ○((a.toVal : R) + b.toVal) ≤ ○(a.toVal (R := R)) :=
      RModeMono.round_mono (R := R) hab_le_a
    have hround_a : ○(a.toVal (R := R)) = a :=
      RModeIdem.round_idempotent (R := R) a (Or.inl ha)
    rw [hround_a] at hmono; rw [hs_correct] at hmono
    exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff s_fp a).mp hmono)
  -- So error ≥ (a+b) - a = b (this gives error ≥ -|b|)
  have herr_ge_b : (b.toVal : R) ≤ (a.toVal : R) + b.toVal - s_fp.toVal := by linarith
  -- Lower bound: round(a+b) ≥ 2(a+b) - a.toVal via dual axiom
  -- First, show roundUp(a+b) ≤ a
  have hUp_le_a : roundUp ((a.toVal : R) + b.toVal) ≤ Fp.finite a :=
    roundUp_le_of_fp_ge _ a (Or.inl ha) hab_le_a
  -- Extract findSuccessorPos as finite
  have hfsp_eq : findSuccessorPos ((a.toVal : R) + b.toVal) hval_pos =
      roundUp ((a.toVal : R) + b.toVal) := by
    rw [roundUp, findSuccessor_pos_eq _ hval_pos]
  -- roundUp is finite (≤ Fp.finite a)
  obtain ⟨succ, hsucc_eq⟩ : ∃ succ : FiniteFp,
      findSuccessorPos ((a.toVal : R) + b.toVal) hval_pos = Fp.finite succ := by
    match h : findSuccessorPos ((a.toVal : R) + b.toVal) hval_pos with
    | .NaN => exact absurd h (findSuccessorPos_ne_nan _ _)
    | .finite f => exact ⟨f, rfl⟩
    | .infinite false =>
      exfalso
      have hru : roundUp ((a.toVal : R) + b.toVal) = Fp.infinite false := by
        rw [← hfsp_eq, h]
      rw [hru] at hUp_le_a
      simp only [Fp.le_def] at hUp_le_a
      rcases hUp_le_a with h1 | h2
      · simp [Fp.is_total_lt] at h1
      · exact absurd h2 (by simp)
    | .infinite true => exact absurd h (findSuccessorPos_ne_neg_inf _ _)
  have hsucc_le_a : (succ.toVal : R) ≤ a.toVal := by
    have : roundUp ((a.toVal : R) + b.toVal) ≤ Fp.finite a := hUp_le_a
    rw [← hfsp_eq, hsucc_eq] at this
    exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff succ a).mp this)
  -- Apply dual axiom
  have hdual := nearest_round_ge_two_x_sub_succ (R := R)
    _ hval_pos hNR s_fp hs_correct succ hsucc_eq
  -- round(a+b) ≥ 2(a+b) - succ ≥ 2(a+b) - a
  have hs_ge : (a.toVal : R) + 2 * b.toVal ≤ s_fp.toVal := by linarith
  -- So error ≤ (a+b) - (a + 2b) = -b = |b|
  have herr_le_negb : (a.toVal : R) + b.toVal - s_fp.toVal ≤ -b.toVal := by linarith
  -- Combined: |error| ≤ |b| = -b
  -- Step E: Express error = r * 2^e₀ as integer × power of 2
  set e_min := min a.e b.e with e_min_def
  set e₀ := e_min - prec + 1 with e₀_def
  have hexact := fpAddFinite_exact_sum R a b
  set isum := addAlignedSumInt a b with isum_def
  -- s_fp.e ≥ e_min: from s_fp.toVal ≥ 2^min(a.e,b.e) and s_fp.toVal < 2^(s_fp.e+1)
  have he_min_le_s : e_min ≤ s_fp.e := by
    by_contra h; push_neg at h
    have h1 := FiniteFp.toVal_lt_zpow_succ (R := R) s_fp hs_s
    have h2 : (2:R) ^ (s_fp.e + 1) ≤ (2:R) ^ (min a.e b.e : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1:R) ≤ 2) (by omega : s_fp.e + 1 ≤ min a.e b.e)
    linarith [hg_toVal]
  -- Factor s_fp.toVal as integer * 2^e₀
  set k := (s_fp.e - e_min).toNat with k_def
  have hk_eq : (k : ℤ) = s_fp.e - e_min := Int.toNat_of_nonneg (by omega)
  have hs_toVal : (s_fp.toVal : R) = ((s_fp.m : ℤ) * 2 ^ k : ℤ) * (2 : R) ^ e₀ := by
    rw [FiniteFp.toVal_factor_zpow (R := R) s_fp hs_s e₀,
        show s_fp.e - prec + 1 - e₀ = s_fp.e - e_min from by omega,
        show (s_fp.e - e_min : ℤ) = ↑k from hk_eq.symm, zpow_natCast]
    push_cast; ring
  -- Define integer error
  set r := isum - (s_fp.m : ℤ) * 2 ^ k with r_def
  have herr_eq : (a.toVal : R) + b.toVal - s_fp.toVal = (r : R) * (2 : R) ^ e₀ := by
    rw [hexact, hs_toVal, r_def]; push_cast; ring
  have hr_ne : r ≠ 0 := by
    intro h; apply herr; rw [herr_eq, h, Int.cast_zero, zero_mul]
  -- Step F: Bound |r| < 2^prec using |error| ≤ |b| = -b
  have he₀_pos : (0 : R) < (2 : R) ^ e₀ := zpow_pos (by norm_num) _
  -- |b.toVal| = (-b).toVal = b.m * 2^(b.e - prec + 1)
  have hb_e_ge : b.e ≥ e_min := min_le_right a.e b.e
  have hb_abs_factor : -(b.toVal : R) = (b.m : R) * (2 : R) ^ ((b.e - e_min : ℤ)) * (2 : R) ^ e₀ := by
    have hnb_s : (-b).s = false := by simp [FiniteFp.neg_def, hb]
    have hfact := FiniteFp.toVal_factor_zpow (R := R) (-b) hnb_s e₀
    rw [FiniteFp.toVal_neg_eq_neg, show (-b).e = b.e from by simp [FiniteFp.neg_def],
        show (-b).m = b.m from by simp [FiniteFp.neg_def],
        show b.e - prec + 1 - e₀ = b.e - e_min from by omega] at hfact
    linarith
  have hr_abs_le : |(r : R)| ≤ (b.m : R) * (2 : R) ^ (b.e - e_min : ℤ) := by
    have herr_abs : |(a.toVal + b.toVal - s_fp.toVal : R)| ≤ -b.toVal :=
      abs_le.mpr ⟨by linarith [herr_ge_b], herr_le_negb⟩
    rw [herr_eq, abs_mul, abs_of_pos he₀_pos] at herr_abs
    rw [hb_abs_factor] at herr_abs
    exact le_of_mul_le_mul_of_pos_right herr_abs he₀_pos
  -- Bound b.m * 2^(b.e - e_min) < 2^prec (same as positive case, uses |b| ≤ a)
  have hbm_shifted_lt : (b.m : R) * (2 : R) ^ (b.e - e_min : ℤ) < (2 : R) ^ precNat := by
    rcases le_or_gt b.e a.e with hba | hab_e
    · have : e_min = b.e := min_eq_right hba
      rw [this, sub_self, zpow_zero, mul_one]
      exact_mod_cast b.valid.2.2.1
    · have he : e_min = a.e := min_eq_left (le_of_lt hab_e)
      rw [he]
      -- From |b.toVal| ≤ a.toVal: b.m * 2^(b.e-prec+1) ≤ a.m * 2^(a.e-prec+1)
      have hle_R : (b.m : R) * (2:R) ^ (b.e - prec + 1) ≤ (a.m : R) * (2:R) ^ (a.e - prec + 1) := by
        have hnb_s : (-b).s = false := by simp [FiniteFp.neg_def, hb]
        have h_abs : |b.toVal (R := R)| = (b.m : R) * (2:R) ^ (b.e - prec + 1) := by
          rw [habs_b, show -(b.toVal (R := R)) = (-b).toVal (R := R) from
            (FiniteFp.toVal_neg_eq_neg (R := R) b).symm, FiniteFp.toVal_pos_eq (-b) hnb_s]
          simp [FiniteFp.neg_def]
        rw [h_abs, FiniteFp.toVal_pos_eq a ha] at hab
        exact hab
      have hd_pos : (0 : R) < (2:R) ^ (a.e - prec + 1) := zpow_pos (by norm_num) _
      have hfactor : (b.m : R) * (2:R)^(b.e - prec + 1)
          = (b.m : R) * (2:R)^(b.e - a.e : ℤ) * (2:R)^(a.e - prec + 1) := by
        rw [show (b.e - prec + 1 : ℤ) = (b.e - a.e) + (a.e - prec + 1) from by omega,
            zpow_add₀ (by norm_num : (2:R) ≠ 0), mul_assoc]
      rw [hfactor] at hle_R
      have : (b.m : R) * (2:R) ^ (b.e - a.e : ℤ) ≤ (a.m : R) :=
        le_of_mul_le_mul_of_pos_right hle_R hd_pos
      calc (b.m : R) * (2:R) ^ (b.e - a.e : ℤ)
          ≤ (a.m : R) := this
        _ < (2 : R) ^ precNat := by exact_mod_cast a.valid.2.2.1
  -- Convert to natAbs bound
  have hr_natAbs_lt : r.natAbs < 2 ^ precNat := by
    have h1 : |(r : R)| < (2 : R) ^ precNat := lt_of_le_of_lt hr_abs_le hbm_shifted_lt
    have h2 : (r.natAbs : R) < (2 : R) ^ precNat := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact h1
    exact_mod_cast h2
  -- Step G: Construct the float
  have he_lo : e₀ ≥ FloatFormat.min_exp - prec + 1 := by
    simp only [e₀_def, e_min_def]; have := le_min a.valid.1 b.valid.1; omega
  have he_hi : e₀ + prec - 1 ≤ FloatFormat.max_exp := by
    simp only [e₀_def, e_min_def]; have := min_le_left a.e b.e; have := a.valid.2.1; omega
  obtain ⟨f, hf_valid, hfv⟩ := exists_finiteFp_of_int_mul_zpow (R := R) r e₀
    hr_ne hr_natAbs_lt he_lo he_hi
  exact ⟨f, hf_valid, by rw [hfv, herr_eq]⟩

/-! ## General error representability -/

/-- The rounding error of a nearest-mode addition is representable as a float,
for any two nonzero finite floats with `|b| ≤ |a|`, regardless of sign. -/
theorem add_error_representable_general (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : |b.toVal (R := R)| ≤ |a.toVal|)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (t_fp.s = false ∨ 0 < t_fp.m) ∧
        (t_fp.toVal : R) = (a.toVal : R) + b.toVal - s_fp.toVal := by
  -- Handle error = 0 up front (needed for negation cases where -0 breaks sign condition)
  by_cases herr : (a.toVal : R) + b.toVal - s_fp.toVal = 0
  · exact ⟨0, Or.inl rfl, by
      rw [show (0 : FiniteFp).toVal (R := R) = 0 from FiniteFp.toVal_isZero rfl]; linarith⟩
  -- Negation helper: (-a) + (-b) = -s_fp
  have neg_sum_eq :
      ∀ (hnsum_ne : ((-a).toVal : R) + (-b).toVal ≠ 0),
        (-a) + (-b) = (-s_fp : FiniteFp) := by
    intro hnsum_ne
    have hs_corr : (s_fp : Fp) = ○((a.toVal : R) + b.toVal) := by
      have := fpAddFinite_correct (R := R) a b hsum_ne
      simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at this hs
      rw [this] at hs; exact hs.symm
    have hns_corr := fpAddFinite_correct (R := R) (-a) (-b) hnsum_ne
    simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at hns_corr ⊢
    rw [hns_corr, FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg,
        show (-(a.toVal : R) + -b.toVal) = -(a.toVal + b.toVal) from by ring,
        RModeConj.round_neg _ hsum_ne, ← hs_corr, Fp.neg_finite]
  -- Negation result lifter: transforms negated-problem result to original-problem result
  have neg_lift : ∀ (t' : FiniteFp),
      (t'.s = false ∨ 0 < t'.m) →
      (t'.toVal : R) = (-a).toVal + (-b).toVal - (-s_fp).toVal →
      ∃ t_fp : FiniteFp,
        (t_fp.s = false ∨ 0 < t_fp.m) ∧
          (t_fp.toVal : R) = a.toVal + b.toVal - s_fp.toVal := by
    intro t' _ ht'_val
    have ht'_nz : 0 < t'.m := by
      by_contra h; push_neg at h; have hm0 : t'.m = 0 := by omega
      have : t'.toVal (R := R) = 0 := FiniteFp.toVal_isZero (by simp [FiniteFp.isZero, hm0])
      rw [this] at ht'_val; simp [FiniteFp.toVal_neg_eq_neg] at ht'_val
      exact herr (by linarith)
    exact ⟨-t', Or.inr (by simp; exact ht'_nz),
      by rw [FiniteFp.toVal_neg_eq_neg, ht'_val]; simp [FiniteFp.toVal_neg_eq_neg]; ring⟩
  -- Sign case split (Bool.eq_false_or_eq_true gives true ∨ false)
  rcases Bool.eq_false_or_eq_true a.s with ha_s | ha_s
  · -- a.s = true (a ≤ 0)
    have hna : (-a).s = false := by simp [FiniteFp.neg_def, ha_s]
    have hna_nz : 0 < (-a).m := by simp; exact ha_nz
    have hnsum_ne : ((-a).toVal : R) + (-b).toVal ≠ 0 := by
      rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
      intro h; exact hsum_ne (by linarith)
    have hns_eq := neg_sum_eq hnsum_ne
    rcases Bool.eq_false_or_eq_true b.s with hb_s | hb_s
    · -- Both negative → negate to both positive
      have hnb : (-b).s = false := by simp [FiniteFp.neg_def, hb_s]
      have hnb_nz : 0 < (-b).m := by simp; exact hb_nz
      have hnab : ((-b).toVal : R) ≤ (-a).toVal := by
        rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
        have ha_neg : (a.toVal : R) < 0 := by
          have := FiniteFp.toVal_pos (-a) hna hna_nz (R := R)
          rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
        have hb_neg : (b.toVal : R) < 0 := by
          have := FiniteFp.toVal_pos (-b) hnb hnb_nz (R := R)
          rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
        rwa [abs_of_neg hb_neg, abs_of_neg ha_neg] at hab
      obtain ⟨t', ht'_valid, ht'_val⟩ := add_error_representable (R := R)
        (-a) (-b) hna hnb hna_nz hnb_nz hnab hnsum_ne (-s_fp) hns_eq
      exact neg_lift t' ht'_valid ht'_val
    · -- a < 0, b > 0 → negate to mixed: (-a) pos, (-b) neg
      have hnb : (-b).s = true := by simp [FiniteFp.neg_def, hb_s]
      have hnb_nz : 0 < (-b).m := by simp; exact hb_nz
      have hnab : |(-b).toVal (R := R)| ≤ (-a).toVal := by
        simp [FiniteFp.toVal_neg_eq_neg, abs_neg]
        have ha_neg : (a.toVal : R) < 0 := by
          have := FiniteFp.toVal_pos (-a) hna hna_nz (R := R)
          rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
        rwa [abs_of_neg ha_neg] at hab
      obtain ⟨t', ht'_valid, ht'_val⟩ := add_error_representable_mixed (R := R)
        (-a) (-b) hna hnb hna_nz hnb_nz hnab hnsum_ne (-s_fp) hns_eq
      exact neg_lift t' ht'_valid ht'_val
  · -- a.s = false (a ≥ 0)
    rcases Bool.eq_false_or_eq_true b.s with hb_s | hb_s
    · -- a > 0, b < 0 → mixed sign
      have hab' : |b.toVal (R := R)| ≤ a.toVal := by
        rwa [abs_of_pos (FiniteFp.toVal_pos a ha_s ha_nz)] at hab
      exact add_error_representable_mixed (R := R) a b ha_s hb_s ha_nz hb_nz hab' hsum_ne s_fp hs
    · -- Both positive
      have hab' : (b.toVal : R) ≤ a.toVal := by
        rwa [abs_of_pos (FiniteFp.toVal_pos b hb_s hb_nz),
             abs_of_pos (FiniteFp.toVal_pos a ha_s ha_nz)] at hab
      exact add_error_representable (R := R) a b ha_s hb_s ha_nz hb_nz hab' hsum_ne s_fp hs

/-- One-sided nonzero variant of `add_error_representable_general`.

When only the left operand is known nonzero, the rounding error is still
representable. This is useful in mixed constructions where the right operand
may be an exact zero produced by earlier cancellation. -/
theorem add_error_representable_general_left_nz (a b : FiniteFp)
    (ha_nz : 0 < a.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      (t_fp.s = false ∨ 0 < t_fp.m) ∧
        (t_fp.toVal : R) = (a.toVal : R) + b.toVal - s_fp.toVal := by
  by_cases hb_nz : 0 < b.m
  · rcases le_or_gt |b.toVal (R := R)| |a.toVal| with hab | hab
    · exact add_error_representable_general (R := R) a b
        ha_nz hb_nz hab hsum_ne s_fp hs
    · have hs' : b + a = s_fp := by
        simp only [add_finite_eq_fpAddFinite] at hs ⊢
        rw [fpAddFinite_comm]
        exact hs
      obtain ⟨t, ht_valid, ht_eq⟩ := add_error_representable_general (R := R) b a
        hb_nz ha_nz (le_of_lt hab) (by rwa [add_comm]) s_fp hs'
      exact ⟨t, ht_valid, by rw [ht_eq]; ring⟩
  · have hb0 : b.toVal (R := R) = 0 := by
      exact (FiniteFp.toVal_significand_zero_iff (R := R)).mp (by omega)
    have hs_round : (s_fp : Fp) = ○((a.toVal : R) + b.toVal) :=
      hs.symm.trans (fpAddFinite_correct (R := R) a b hsum_ne)
    have hs_eq_a : (s_fp : Fp) = (a : Fp) := by
      rw [hs_round, hb0, add_zero, RModeIdem.round_idempotent (R := R) a (Or.inr ha_nz)]
    have hs_val : s_fp.toVal (R := R) = a.toVal := by
      simpa using congrArg (fun x : FiniteFp => x.toVal (R := R)) (Fp.finite.inj hs_eq_a)
    exact ⟨0, Or.inl rfl, by
      rw [show (0 : FiniteFp).toVal (R := R) = 0 from FiniteFp.toVal_isZero rfl]
      rw [hs_val, hb0]
      ring⟩

end AddErrorRepresentable
