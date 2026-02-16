import Flean.Operations.FMA

/-! # Multiplication Error Representability

The rounding error of floating-point multiplication is exactly representable as a float.
This is the core mathematical fact underlying the TwoProduct error-free transformation.

## Key results

- `fpMul_exact_of_small_sig`: products with < prec-bit significands are exact
- `mul_round_exponent_ge`: the rounded product's exponent is ≥ fmaProdE
- `mul_error_representable`: the rounding error `a*b - fl(a*b)` is representable
-/

section MulErrorRepresentable

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Helper: exact products with small significands -/

/-- When the product significand fits in prec bits and doesn't underflow,
the multiplication is exact: `p.toVal = a.toVal * b.toVal`. -/
private theorem fpMul_exact_of_small_sig (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (p : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hp : a * b = p)
    (hno_underflow : fmaProdE a b ≥ FloatFormat.min_exp)
    (hsig : a.m * b.m < 2 ^ precNat) :
    (p.toVal : R) = (a.toVal : R) * b.toVal := by
  have hprec := FloatFormat.valid_prec
  have hprod_nz : (a.toVal : R) * b.toVal ≠ 0 :=
    mul_ne_zero (FiniteFp.toVal_ne_zero_of_m_pos a ha_nz) (FiniteFp.toVal_ne_zero_of_m_pos b hb_nz)
  have hp_corr : (p : Fp) = ○((a.toVal : R) * b.toVal) := by
    have := fpMulFinite_correct (R := R) a b hprod_nz
    simp only [mul_finite_eq_fpMulFinite, mul_eq_fpMul, fpMul_coe_coe] at this hp
    rw [this] at hp; exact hp.symm
  have h_has_small : a.m < 2 ^ (prec - 1).toNat ∨ b.m < 2 ^ (prec - 1).toNat := by
    by_contra h; push_neg at h
    have hmul_ge := Nat.mul_le_mul h.1 h.2
    rw [← Nat.pow_add] at hmul_ge
    have hexp_ge : precNat ≤ (prec - 1).toNat + (prec - 1).toNat := by omega
    exact absurd hsig (not_lt.mpr (le_trans (Nat.pow_le_pow_right (by norm_num) hexp_ge) hmul_ge))
  have hfmaProdE_le : fmaProdE a b ≤ FloatFormat.max_exp := by
    rcases h_has_small with ha_small | hb_small
    · have : ¬_root_.isNormal a.m := fun hn => absurd hn.1 (not_le.mpr ha_small)
      have ha_e := (a.isNormal_or_isSubnormal.resolve_left this).1
      have := FloatFormat.min_exp_nonpos; have := b.valid.2.1
      show a.e + b.e - prec + 1 ≤ FloatFormat.max_exp; omega
    · have : ¬_root_.isNormal b.m := fun hn => absurd hn.1 (not_le.mpr hb_small)
      have hb_e := (b.isNormal_or_isSubnormal.resolve_left this).1
      have := FloatFormat.min_exp_nonpos; have := a.valid.2.1
      show a.e + b.e - prec + 1 ≤ FloatFormat.max_exp; omega
  set e_base := a.e + b.e - 2 * prec + 2
  obtain ⟨g, hgs, hgv⟩ := exists_finiteFp_of_nat_mul_zpow (R := R) (a.m * b.m) e_base
    (Nat.mul_pos ha_nz hb_nz) hsig
    (by show a.e + b.e - 2 * prec + 2 ≥ FloatFormat.min_exp - prec + 1
        simp only [fmaProdE] at hno_underflow; omega)
    (by show a.e + b.e - 2 * prec + 2 + prec - 1 ≤ FloatFormat.max_exp
        simp only [fmaProdE] at hfmaProdE_le; omega)
  have hg_pos : (0 : R) < g.toVal := by rw [hgv]; positivity
  have hexact := fpMulFinite_exact_product (R := R) a b
  cases hsign : (a.s ^^ b.s) with
  | false =>
    have hprod_eq : (a.toVal : R) * b.toVal = g.toVal := by
      rw [hexact, hsign, hgv]; unfold intSigVal; rfl
    rw [hprod_eq, RModeIdem.round_idempotent (R := R) g (Or.inl hgs)] at hp_corr
    have hpg : p = g := by simpa using hp_corr
    rw [hpg]; exact hprod_eq.symm
  | true =>
    have hprod_eq : (a.toVal : R) * b.toVal = -(g.toVal (R := R)) := by
      rw [hexact, hsign, hgv]; unfold intSigVal; simp only [ite_true, neg_mul, e_base]
    have hg_ne : (g.toVal : R) ≠ 0 := ne_of_gt hg_pos
    have hround_g := RModeIdem.round_idempotent (R := R) g (Or.inl hgs)
    have hconj := RModeConj.round_neg (g.toVal (R := R)) hg_ne
    rw [hround_g, Fp.neg_finite] at hconj
    rw [hprod_eq, hconj] at hp_corr
    have hpg : p = -g := by simpa using hp_corr
    rw [hpg, FiniteFp.toVal_neg_eq_neg]; exact hprod_eq.symm

/-! ## Rounded product exponent bound -/

/-- The rounded product's exponent is at least `fmaProdE` when the product significand
is large enough (≥ 2^prec). This ensures the FMA alignment doesn't lose precision. -/
theorem mul_round_exponent_ge (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (p : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hp : a * b = p)
    (hno_underflow : fmaProdE a b ≥ FloatFormat.min_exp)
    (hprod_large : 2 ^ precNat ≤ a.m * b.m) :
    p.e ≥ fmaProdE a b := by
  set exact_val := (a.toVal : R) * b.toVal
  set abs_exact := |exact_val|
  have hprod_nz : exact_val ≠ 0 :=
    mul_ne_zero (FiniteFp.toVal_ne_zero_of_m_pos a ha_nz) (FiniteFp.toVal_ne_zero_of_m_pos b hb_nz)
  set e_prod := a.e + b.e - 2 * prec + 2 with e_prod_def
  have hexact_prod := fpMulFinite_exact_product (R := R) a b
  have habs_eq : abs_exact = (a.m * b.m : R) * (2 : R) ^ e_prod := by
    show |exact_val| = _
    have : exact_val = intSigVal (R := R) (a.s ^^ b.s) (a.m * b.m) e_prod := hexact_prod
    rw [this, intSigVal]
    split_ifs <;> simp [abs_mul, abs_of_pos (two_zpow_pos' (R := R) _)]
  have he_prod_eq : e_prod = fmaProdE a b - prec + 1 := by
    simp [e_prod_def, fmaProdE]; ring
  -- |exact| ≥ 2^(fmaProdE+1)
  have hexact_ge : (2 : R) ^ (fmaProdE a b + 1) ≤ abs_exact := by
    rw [habs_eq]
    calc (2 : R) ^ (fmaProdE a b + 1)
        = (2 : R) ^ precNat * (2 : R) ^ e_prod := by
          rw [← zpow_natCast (2 : R) precNat, two_zpow_mul (R := R)]
          congr 1; rw [he_prod_eq]; have := FloatFormat.valid_prec; omega
      _ ≤ (a.m * b.m : R) * (2 : R) ^ e_prod := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hprod_large)
            (le_of_lt (two_zpow_pos' _))
  -- |exact| < 2^(max_exp+1) (overflow would contradict p being finite)
  have hp_corr : (p : Fp) = ○exact_val := by
    have := fpMulFinite_correct (R := R) a b hprod_nz
    simp only [mul_finite_eq_fpMulFinite, mul_eq_fpMul, fpMul_coe_coe] at this hp
    rw [this] at hp; exact hp.symm
  have hab_bound : a.m * b.m < 2 ^ (2 * precNat) := by
    have ha_lt := a.valid.2.2.1; have hb_lt := b.valid.2.2.1
    calc a.m * b.m
        < 2 ^ precNat * 2 ^ precNat := by
          exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha_lt) hb_lt (by positivity)
      _ = 2 ^ (2 * precNat) := by ring
  have hexact_upper : abs_exact < (2 : R) ^ (FloatFormat.max_exp + 1) := by
    have hexact_lt_ot : |exact_val| < FloatFormat.overflowThreshold R := by
      by_contra h; push_neg at h
      rcases le_or_gt exact_val 0 with hneg | hpos
      · have habs : -exact_val ≥ FloatFormat.overflowThreshold R := by
          rwa [abs_of_nonpos hneg] at h
        have hoverflow : ○(-exact_val) = Fp.infinite false :=
          RModeNearest.overflow_pos_inf (R := R) _ habs
        have hneg_lt : exact_val < 0 := lt_of_le_of_ne hneg hprod_nz
        have hnex_ne : -exact_val ≠ 0 := ne_of_gt (by linarith)
        have : ○exact_val = -(Fp.infinite false) := by
          rw [show exact_val = -(-exact_val) from by ring,
              RModeConj.round_neg (-exact_val) hnex_ne, hoverflow]
        rw [this] at hp_corr; simp [Fp.neg_def] at hp_corr
      · have habs : exact_val ≥ FloatFormat.overflowThreshold R := by
          rwa [abs_of_pos hpos] at h
        have : ○exact_val = Fp.infinite false :=
          RModeNearest.overflow_pos_inf (R := R) _ habs
        rw [this] at hp_corr; simp at hp_corr
    exact lt_trans hexact_lt_ot FloatFormat.overflowThreshold_lt_zpow_max_exp_succ
  -- fmaProdE + 1 ≤ max_exp
  have hfmaProdE_le : fmaProdE a b + 1 ≤ FloatFormat.max_exp := by
    by_contra h; push_neg at h
    linarith [hexact_upper, zpow_le_zpow_right₀ (show (1 : R) ≤ 2 by norm_num)
      (show FloatFormat.max_exp + 1 ≤ fmaProdE a b + 1 from by omega)]
  -- Construct f₀ with f₀.toVal = 2^(fmaProdE+1)
  have hprec_ge := FloatFormat.valid_prec
  set m₀ := 2 ^ (precNat - 1)
  have hm₀_normal : _root_.isNormal m₀ := by
    constructor
    · show 2 ^ (prec - 1).toNat ≤ m₀
      rw [show (prec - 1).toNat = precNat - 1 from by omega]
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
  set f₀ : FiniteFp :=
    ⟨false, fmaProdE a b + 1, m₀,
     ⟨by omega, hfmaProdE_le, hm₀_normal.2, Or.inl hm₀_normal⟩⟩
  have hf₀_val : (f₀.toVal : R) = (2 : R) ^ (fmaProdE a b + 1) := by
    rw [FiniteFp.toVal_pos_eq f₀ rfl]
    show (m₀ : R) * (2 : R) ^ (fmaProdE a b + 1 - prec + 1) =
      (2 : R) ^ (fmaProdE a b + 1)
    rw [show (m₀ : R) = (2 : R) ^ (precNat - 1 : ℕ) from by norm_cast]
    rw [← zpow_natCast (2 : R) (precNat - 1), two_zpow_mul (R := R)]
    congr 1
    have : ((precNat - 1 : ℕ) : ℤ) = prec - 1 := by omega
    omega
  -- |p.toVal| ≥ 2^(fmaProdE+1) via roundDown monotonicity
  have h2pos : (0 : R) < (2 : R) ^ (fmaProdE a b + 1) := two_zpow_pos' (R := R) _
  rcases le_or_gt exact_val 0 with hneg | hpos
  · -- Negative case
    have hlt : exact_val < 0 := lt_of_le_of_ne hneg hprod_nz
    have hf₀_le : (f₀.toVal : R) ≤ -exact_val := by
      rw [hf₀_val]; linarith [show abs_exact = -exact_val from abs_of_neg hlt]
    have hrd := roundDown_ge_of_fp_le (-exact_val) f₀ (Or.inl rfl) hf₀_le
    have hge := Fp.le_trans hrd (RModeNearest.roundDown_le_round (R := R) (-exact_val))
    have hconj : ○(-exact_val) = Fp.finite (-p : FiniteFp) := by
      rw [RModeConj.round_neg exact_val (ne_of_lt hlt), ← hp_corr, Fp.neg_finite]
    rw [hconj] at hge
    have hle := FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff f₀ (-p)).mp hge)
    simp only [FiniteFp.toVal_neg_eq_neg, hf₀_val] at hle
    have hnp_s : (-p).s = false := by
      apply ((FiniteFp.toVal_pos_iff (R := R)).mpr _).1
      simp only [FiniteFp.toVal_neg_eq_neg]; linarith
    have hnp_lt := FiniteFp.toVal_lt_zpow_succ (R := R) (-p) hnp_s
    simp only [FiniteFp.toVal_neg_eq_neg] at hnp_lt
    have hep : (-p : FiniteFp).e = p.e := by simp [FiniteFp.neg_def]
    rw [hep] at hnp_lt
    have h_lt : (2 : R) ^ (fmaProdE a b + 1) < (2 : R) ^ (p.e + 1) := by linarith
    linarith [(zpow_lt_zpow_iff_right₀ (show (1 : R) < 2 by norm_num)).mp h_lt]
  · -- Positive case
    have hf₀_le : (f₀.toVal : R) ≤ exact_val := by
      rw [hf₀_val]; linarith [show abs_exact = exact_val from abs_of_pos hpos]
    have hrd := roundDown_ge_of_fp_le exact_val f₀ (Or.inl rfl) hf₀_le
    have hge := Fp.le_trans hrd (RModeNearest.roundDown_le_round (R := R) exact_val)
    rw [hp_corr.symm] at hge
    have hle := FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff f₀ p).mp hge)
    rw [hf₀_val] at hle
    have hp_s : p.s = false :=
      ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).1
    have hp_lt := FiniteFp.toVal_lt_zpow_succ (R := R) p hp_s
    have h_lt : (2 : R) ^ (fmaProdE a b + 1) < (2 : R) ^ (p.e + 1) := by linarith
    linarith [(zpow_lt_zpow_iff_right₀ (show (1 : R) < 2 by norm_num)).mp h_lt]

/-! ## Main result: multiplication error representability -/

/-- The FMA-based rounding error of multiplication is exactly representable.

The exact product `a.m * b.m` has ≤ 2·prec bits. After rounding to prec bits,
the error has ≤ prec bits and fits in the float format.

The condition `fmaProdE a b ≥ min_exp` ensures the rounding shift is at most prec,
preventing severe subnormal underflow. -/
theorem mul_error_representable (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (p : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hp : a * b = p)
    (hno_underflow : fmaProdE a b ≥ FloatFormat.min_exp)
    (herr : (a.toVal : R) * b.toVal - p.toVal ≠ 0) :
    ∃ e : FiniteFp,
      (e.s = false ∨ 0 < e.m) ∧
        (e.toVal : R) = (a.toVal : R) * b.toVal - p.toVal := by
  -- Express the error via FMA exact sum: a*b + (-p) = isum * 2^ebase
  set c := (-p : FiniteFp)
  have hexact := fpFMAFinite_exact_sum R a b c
  rw [FiniteFp.toVal_neg_eq_neg, ← sub_eq_add_neg] at hexact
  set ebase := fmaEMin a b c - prec + 1 with ebase_def
  set isum := fmaAlignedSumInt a b c with isum_def
  have hisum_ne : isum ≠ 0 := by
    intro h; apply herr; rw [hexact, h, Int.cast_zero, zero_mul]
  -- Bound |isum| < 2^prec
  have hisum_bound : isum.natAbs < 2 ^ precNat := by
    -- Product significand ≥ 2^prec (otherwise exact, contradicts herr)
    have hprod_large : 2 ^ precNat ≤ a.m * b.m := by
      by_contra h; push_neg at h
      exact herr (sub_eq_zero.mpr
        (fpMul_exact_of_small_sig (R := R) a b ha_nz hb_nz p hp hno_underflow h).symm)
    set exact_val := (a.toVal : R) * b.toVal
    set abs_exact := |exact_val|
    have hprod_nz : exact_val ≠ 0 :=
      mul_ne_zero (FiniteFp.toVal_ne_zero_of_m_pos a ha_nz) (FiniteFp.toVal_ne_zero_of_m_pos b hb_nz)
    set e_prod := a.e + b.e - 2 * prec + 2 with e_prod_def
    have hexact_prod := fpMulFinite_exact_product (R := R) a b
    have habs_eq : abs_exact = (a.m * b.m : R) * (2 : R) ^ e_prod := by
      show |exact_val| = _
      have : exact_val = intSigVal (R := R) (a.s ^^ b.s) (a.m * b.m) e_prod := hexact_prod
      rw [this, intSigVal]
      split_ifs <;> simp [abs_mul, abs_of_pos (two_zpow_pos' (R := R) _)]
    have he_prod_eq : e_prod = fmaProdE a b - prec + 1 := by
      simp [e_prod_def, fmaProdE]; ring
    have hexact_lower : (2 : R) ^ (FloatFormat.min_exp + 1) ≤ abs_exact := by
      rw [habs_eq]
      have hprodE_ge : fmaProdE a b + 1 ≥ FloatFormat.min_exp + 1 := by omega
      calc (2 : R) ^ (FloatFormat.min_exp + 1)
          ≤ (2 : R) ^ (fmaProdE a b + 1) :=
            zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2) hprodE_ge
        _ = (2 : R) ^ precNat * (2 : R) ^ e_prod := by
            rw [← zpow_natCast (2 : R) precNat, two_zpow_mul (R := R)]
            congr 1; rw [he_prod_eq]
            have := FloatFormat.valid_prec; omega
        _ ≤ (a.m * b.m : R) * (2 : R) ^ e_prod := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt (two_zpow_pos' _))
            exact_mod_cast hprod_large
    have hp_corr : (p : Fp) = ○exact_val := by
      have := fpMulFinite_correct (R := R) a b hprod_nz
      simp only [mul_finite_eq_fpMulFinite, mul_eq_fpMul, fpMul_coe_coe] at this hp
      rw [this] at hp; exact hp.symm
    have hexact_lt_ot : |exact_val| < FloatFormat.overflowThreshold R := by
      by_contra h; push_neg at h
      rcases le_or_gt exact_val 0 with hneg | hpos
      · have habs : -exact_val ≥ FloatFormat.overflowThreshold R := by
          rwa [abs_of_nonpos hneg] at h
        have hoverflow : ○(-exact_val) = Fp.infinite false :=
          RModeNearest.overflow_pos_inf (R := R) _ habs
        have hneg_lt : exact_val < 0 := lt_of_le_of_ne hneg hprod_nz
        have hnex_ne : -exact_val ≠ 0 := ne_of_gt (by linarith)
        have : ○exact_val = -(Fp.infinite false) := by
          rw [show exact_val = -(-exact_val) from by ring,
              RModeConj.round_neg (-exact_val) hnex_ne, hoverflow]
        rw [this] at hp_corr; simp [Fp.neg_def] at hp_corr
      · have habs : exact_val ≥ FloatFormat.overflowThreshold R := by
          rwa [abs_of_pos hpos] at h
        have : ○exact_val = Fp.infinite false :=
          RModeNearest.overflow_pos_inf (R := R) _ habs
        rw [this] at hp_corr; simp at hp_corr
    have hexact_upper : abs_exact < (2 : R) ^ (FloatFormat.max_exp + 1) :=
      lt_trans hexact_lt_ot FloatFormat.overflowThreshold_lt_zpow_max_exp_succ
    have hNR : isNormalRange abs_exact :=
      ⟨le_trans (zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2) (by omega)) hexact_lower,
       hexact_upper⟩
    -- |exact_val| < 2^(prec + fmaProdE + 1)
    have hab_bound : a.m * b.m < 2 ^ (2 * precNat) := by
      have ha_lt := a.valid.2.2.1; have hb_lt := b.valid.2.2.1
      calc a.m * b.m
          < 2 ^ precNat * 2 ^ precNat := by
            exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha_lt) hb_lt (by positivity)
        _ = 2 ^ (2 * precNat) := by ring
    have hexact_lt_zpow : abs_exact < (2 : R) ^ (prec + fmaProdE a b + 1) := by
      rw [habs_eq]
      calc (a.m * b.m : R) * (2 : R) ^ e_prod
          < (2 : R) ^ (2 * precNat) * (2 : R) ^ e_prod := by
            exact mul_lt_mul_of_pos_right (by exact_mod_cast hab_bound) (two_zpow_pos' _)
        _ = (2 : R) ^ (prec + fmaProdE a b + 1) := by
            rw [← zpow_natCast (2 : R) (2 * precNat), two_zpow_mul (R := R)]
            congr 1; rw [he_prod_eq]; have := FloatFormat.valid_prec; omega
    -- ulp bound
    have habs_pos : 0 < abs_exact := abs_pos.mpr hprod_nz
    have hulp_le : Fp.ulp abs_exact ≤ (2 : R) ^ (fmaProdE a b + 1) := by
      rw [Fp.ulp_normal_eq abs_exact (by rw [abs_abs]; exact hNR.1)]
      apply two_zpow_mono (R := R)
      have hlog : Int.log 2 |abs_exact| < prec + fmaProdE a b + 1 := by
        rw [abs_abs, ← Int.lt_zpow_iff_log_lt (by norm_num : 1 < 2) habs_pos]
        exact_mod_cast hexact_lt_zpow
      omega
    -- |error| < ulp(|exact_val|)
    have herr_lt_ulp : |exact_val - (p.toVal : R)| < Fp.ulp abs_exact := by
      have hulp_abs : Fp.ulp abs_exact = Fp.ulp exact_val := by
        show Fp.ulp |exact_val| = Fp.ulp exact_val; unfold Fp.ulp; simp [abs_abs]
      rw [hulp_abs]
      rcases le_or_gt exact_val 0 with hneg | hpos
      · have hlt : exact_val < 0 := lt_of_le_of_ne hneg hprod_nz
        have hNR' : isNormalRange (-exact_val) := by
          rwa [show abs_exact = -exact_val from abs_of_neg hlt] at hNR
        have hconj : ○(-exact_val) = Fp.finite (-p : FiniteFp) := by
          rw [RModeConj.round_neg exact_val (ne_of_lt hlt), ← hp_corr, Fp.neg_finite]
        rcases RModeNearest.round_eq_roundDown_or_roundUp (R := R) (-exact_val) with hrd | hru
        · have h := roundDown_abs_error_lt_ulp_pos (-exact_val) hNR' (-p)
            (hrd.symm.trans hconj)
          rw [FiniteFp.toVal_neg_eq_neg, neg_sub_neg, abs_sub_comm, Fp.ulp_eq_neg] at h
          exact h
        · have h := roundUp_abs_error_lt_ulp_pos (-exact_val) hNR' (-p)
            (hru.symm.trans hconj)
          rw [FiniteFp.toVal_neg_eq_neg, neg_sub_neg, Fp.ulp_eq_neg] at h
          exact h
      · have hNR' : isNormalRange exact_val := by
          rwa [show abs_exact = exact_val from abs_of_pos hpos] at hNR
        rcases RModeNearest.round_eq_roundDown_or_roundUp (R := R) exact_val with hrd | hru
        · exact roundDown_abs_error_lt_ulp_pos exact_val hNR' p (hrd.symm.trans hp_corr.symm)
        · have h := roundUp_abs_error_lt_ulp_pos exact_val hNR' p (hru.symm.trans hp_corr.symm)
          rwa [abs_sub_comm] at h
    -- |isum| * 2^ebase < 2^(fmaProdE + 1)
    have hc_e' : c.e = p.e := by simp [c, FiniteFp.neg_def]
    have hemin_eq : fmaEMin a b c = min (fmaProdE a b) p.e := by
      simp [fmaEMin, hc_e']
    have hebase_eq : ebase = min (fmaProdE a b) p.e - prec + 1 := by
      rw [ebase_def, hemin_eq]
    have hebase_le : ebase ≤ e_prod := by
      rw [hebase_eq, he_prod_eq]; omega
    have hisum_R : (isum.natAbs : R) * (2 : R) ^ ebase < (2 : R) ^ (fmaProdE a b + 1) := by
      calc (isum.natAbs : R) * (2 : R) ^ ebase
          = |(isum : R)| * (2 : R) ^ ebase := by rw [Nat.cast_natAbs, Int.cast_abs]
        _ = |(isum : R) * (2 : R) ^ ebase| := by
            rw [abs_mul, abs_of_pos (two_zpow_pos' _)]
        _ = |exact_val - (p.toVal : R)| := by rw [hexact]
        _ < Fp.ulp abs_exact := herr_lt_ulp
        _ ≤ (2 : R) ^ (fmaProdE a b + 1) := hulp_le
    -- p.e ≥ fmaProdE → ebase = e_prod
    have hpe_ge : p.e ≥ fmaProdE a b :=
      mul_round_exponent_ge (R := R) a b ha_nz hb_nz p hp hno_underflow hprod_large
    have hebase_ge : ebase ≥ e_prod := by
      rw [hebase_eq, he_prod_eq]; omega
    have hebase_eq_eprod : ebase = e_prod := le_antisymm hebase_le hebase_ge
    -- isum.natAbs * 2^ebase < 2^(ebase + prec)
    have hexp_eq : fmaProdE a b + 1 = ebase + prec := by
      rw [hebase_eq_eprod, he_prod_eq]; have := FloatFormat.valid_prec; omega
    rw [hexp_eq] at hisum_R
    rw [show (2 : R) ^ (ebase + prec) = (2 : R) ^ prec * (2 : R) ^ ebase from by
      rw [zpow_add₀ (by norm_num : (2 : R) ≠ 0)]; ring] at hisum_R
    have hisum_R' : (isum.natAbs : R) < (2 : R) ^ prec :=
      lt_of_mul_lt_mul_of_nonneg_right hisum_R (le_of_lt (two_zpow_pos' _))
    have hprec_cast : (precNat : ℤ) = prec := by
      have := FloatFormat.valid_prec; omega
    have : (isum.natAbs : R) < (2 : R) ^ (precNat : ℕ) := by
      rw [← zpow_natCast (2 : R) precNat, hprec_cast]; exact hisum_R'
    exact_mod_cast this
  -- Exponent bounds
  have hc_e : c.e = p.e := by simp [c, FiniteFp.neg_def]
  have hemin_ge : fmaEMin a b c ≥ FloatFormat.min_exp := by
    simp only [fmaEMin, fmaProdE, hc_e]
    exact le_min hno_underflow p.valid.1
  have hemin_le : fmaEMin a b c ≤ FloatFormat.max_exp := by
    simp only [fmaEMin, fmaProdE, hc_e]
    exact le_trans (min_le_right _ _) p.valid.2.1
  have he_lo : ebase ≥ FloatFormat.min_exp - prec + 1 := by omega
  have he_hi : ebase + prec - 1 ≤ FloatFormat.max_exp := by omega
  -- Construct representative float
  obtain ⟨f, hf_valid, hfv⟩ := exists_finiteFp_of_int_mul_zpow (R := R)
    isum ebase hisum_ne hisum_bound he_lo he_hi
  exact ⟨f, hf_valid, by rw [hfv, hexact]⟩

end MulErrorRepresentable
