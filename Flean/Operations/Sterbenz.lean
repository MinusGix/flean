import Flean.Operations.Sub

/-! # Sterbenz Lemma

The Sterbenz lemma states that if two positive floating-point numbers `a` and `b` satisfy
`b/2 ≤ a ≤ 2b`, then their difference `a - b` is exactly representable — no rounding error
occurs regardless of the rounding mode.
-/

section Sterbenz

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
local notation "prec" => FloatFormat.prec
local notation "precNat" => FloatFormat.prec.toNat

/-! ## Sterbenz conditions imply exponent proximity -/

omit [FloorRing R] in
/-- Under Sterbenz conditions (b/2 ≤ a ≤ 2b, both positive), the exponents differ by at most 1. -/
theorem sterbenz_exp_proximity (a b : FiniteFp) (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (h_lb : (b.toVal : R) / 2 ≤ a.toVal)
    (h_ub : (a.toVal : R) ≤ 2 * b.toVal) :
    a.e - 1 ≤ b.e ∧ b.e - 1 ≤ a.e := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have h2ne : (2 : R) ≠ 0 := by norm_num
  have h2gt : (1 : R) < 2 := by norm_num
  have two_mul_zpow (n : ℤ) : (2 : R) * (2 : R) ^ n = (2 : R) ^ (n + 1) := by
    rw [mul_comm, ← zpow_add_one₀ h2ne]
  constructor
  · -- a.e - 1 ≤ b.e
    by_cases ha_normal : _root_.isNormal a.m
    · have : (2 : R) ^ a.e < (2 : R) ^ (b.e + 2) :=
        calc (2 : R) ^ a.e ≤ a.toVal := FiniteFp.toVal_normal_lower a ha ha_normal
          _ ≤ 2 * b.toVal := h_ub
          _ < 2 * (2 : R) ^ (b.e + 1) := by linarith [FiniteFp.toVal_lt_zpow_succ (R := R) b hb]
          _ = (2 : R) ^ ((b.e + 1) + 1) := two_mul_zpow _
          _ = (2 : R) ^ (b.e + 2) := by congr 1; ring
      linarith [(zpow_lt_zpow_iff_right₀ h2gt).mp this]
    · linarith [(a.valid.2.2.2.resolve_left ha_normal).1, b.valid.1]
  · -- b.e - 1 ≤ a.e
    by_cases hb_normal : _root_.isNormal b.m
    · have hb_div2 : (2 : R) ^ (b.e - 1) ≤ b.toVal / 2 := by
        have : (2 : R) ^ (b.e - 1) * 2 = (2 : R) ^ b.e := by
          rw [← zpow_add_one₀ h2ne]; congr 1; ring
        rw [le_div_iff₀ (by norm_num : (0 : R) < 2)]
        linarith [FiniteFp.toVal_normal_lower (R := R) b hb hb_normal]
      have : (2 : R) ^ (b.e - 1) < (2 : R) ^ (a.e + 1) :=
        calc (2 : R) ^ (b.e - 1) ≤ b.toVal / 2 := hb_div2
          _ ≤ a.toVal := h_lb
          _ < (2 : R) ^ (a.e + 1) := FiniteFp.toVal_lt_zpow_succ a ha
      linarith [(zpow_lt_zpow_iff_right₀ h2gt).mp this]
    · linarith [(b.valid.2.2.2.resolve_left hb_normal).1, a.valid.1]

/-! ## Aligned difference bound -/

def sterbenzEMin (a b : FiniteFp) : ℤ := min a.e (-b).e

/-- Aligned signed integer corresponding to `a + (-b)` at exponent `sterbenzEMin a b`. -/
def sterbenzAlignedDiffInt (a b : FiniteFp) : ℤ :=
  condNeg a.s (a.m : ℤ) * 2 ^ (a.e - sterbenzEMin a b).toNat +
    condNeg (-b).s ((-b).m : ℤ) * 2 ^ ((-b).e - sterbenzEMin a b).toNat

omit [FloorRing R] in
/-- The integer sum in `fpAddFinite` for `a + (-b)` under Sterbenz conditions has
    magnitude strictly less than `2^prec`. -/
theorem sterbenz_aligned_diff_bound (a b : FiniteFp) (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (h_lb : (b.toVal : R) / 2 ≤ a.toVal)
    (h_ub : (a.toVal : R) ≤ 2 * b.toVal)
    (h_exp : a.e - 1 ≤ b.e ∧ b.e - 1 ≤ a.e) :
    (sterbenzAlignedDiffInt a b).natAbs < 2 ^ precNat := by
  unfold sterbenzAlignedDiffInt sterbenzEMin
  simp only [FiniteFp.neg_def, ha, hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    condNeg_false, condNeg_true, Int.neg_mul]
  set e_min := min a.e b.e
  have ha_bnd := a.valid.2.2.1
  have hb_bnd := b.valid.2.2.1
  -- Helper for the shifted-exponent cases
  have sig_le_of_half_le (x y : FiniteFp) (hxs : x.s = false) (hys : y.s = false)
      (hy_nz : 0 < y.m)
      (h_half : (y.toVal : R) / 2 ≤ x.toVal) (hye_eq : y.e = x.e + 1) :
      y.m ≤ x.m := by
    have hpow_pos : (0 : R) < (2 : R) ^ (y.e - prec + 1) := by positivity
    have key : (y.m : R) * (2 : R) ^ (y.e - prec + 1) ≤
        (x.m : R) * (2 : R) ^ (y.e - prec + 1) := by
      calc (y.m : R) * (2 : R) ^ (y.e - prec + 1)
          = y.toVal := (FiniteFp.toVal_pos_eq (R := R) y hys).symm
        _ ≤ 2 * x.toVal := by linarith
        _ = 2 * ((x.m : R) * (2 : R) ^ (x.e - prec + 1)) := by
            rw [FiniteFp.toVal_pos_eq x hxs]
        _ = (x.m : R) * (2 * (2 : R) ^ (x.e - prec + 1)) := by ring
        _ = (x.m : R) * (2 : R) ^ (y.e - prec + 1) := by
            congr 1; rw [mul_comm, ← zpow_add_one₀ (by norm_num : (2:R) ≠ 0)]; congr 1; omega
    exact_mod_cast le_of_mul_le_mul_right key hpow_pos
  rcases le_or_gt a.e b.e with hae_le | hae_gt
  · -- Case a.e ≤ b.e (so e_min = a.e)
    have he_min_eq : e_min = a.e := min_eq_left hae_le
    rw [he_min_eq, show (a.e - a.e).toNat = 0 from by omega]
    simp only [pow_zero, mul_one]
    have hbe_diff : b.e - a.e = 0 ∨ b.e - a.e = 1 := by omega
    rcases hbe_diff with hd0 | hd1
    · rw [show (b.e - a.e).toNat = 0 from by omega]; simp only [pow_zero, mul_one]; omega
    · rw [show (b.e - a.e).toNat = 1 from by omega, pow_one]
      have : b.m ≤ a.m := sig_le_of_half_le a b ha hb hb_nz h_lb (by omega)
      omega
  · -- Case a.e > b.e (so e_min = b.e, a.e = b.e + 1)
    have he_min_eq : e_min = b.e := min_eq_right (le_of_lt hae_gt)
    rw [he_min_eq, show (a.e - b.e).toNat = 1 from by omega,
      show (b.e - b.e).toNat = 0 from by omega]
    simp only [pow_zero, pow_one, mul_one]
    have h_lb' : (a.toVal : R) / 2 ≤ b.toVal := by linarith
    have : a.m ≤ b.m := sig_le_of_half_le b a hb ha ha_nz h_lb' (by omega)
    omega

/-! ## Main Theorem -/

/-- **Sterbenz Lemma**: If `a` and `b` are positive finite floats with `b/2 ≤ a ≤ 2b`,
    then `a - b` is exactly representable — `fpSubFinite` returns a finite float whose
    value is the exact difference, regardless of rounding mode. -/
theorem sterbenz (a b : FiniteFp) (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (h_lb : (b.toVal : R) / 2 ≤ a.toVal)
    (h_ub : (a.toVal : R) ≤ 2 * b.toVal) :
    ∀ mode : RoundingMode, ∃ f : FiniteFp,
      fpSubFinite mode a b = Fp.finite f ∧ f.toVal (R := R) = a.toVal - b.toVal := by
  have h_exp := sterbenz_exp_proximity (R := R) a b ha hb ha_nz hb_nz h_lb h_ub
  -- Set up the aligned integer sum
  set e_min := min a.e (-b).e with e_min_def
  have hnb_e : (-b).e = b.e := by rw [FiniteFp.neg_def]
  have he_min_eq : e_min = min a.e b.e := by rw [e_min_def, hnb_e]
  set isum : ℤ := condNeg a.s (a.m : ℤ) * 2 ^ (a.e - e_min).toNat +
    condNeg (-b).s ((-b).m : ℤ) * 2 ^ ((-b).e - e_min).toNat with isum_def
  have hexact := fpAddFinite_exact_sum R a (-b)
  rw [FiniteFp.toVal_neg_eq_neg] at hexact
  set e_base := e_min - prec + 1 with e_base_def
  have hdiff_eq : (a.toVal : R) - b.toVal = (isum : R) * (2 : R) ^ e_base := by
    rw [e_base_def]; linarith
  -- Case split: is the difference zero?
  by_cases hdiff : (a.toVal : R) = b.toVal
  · -- Equal values: isum = 0, fpAddFinite returns a signed zero
    have hisum_zero : isum = 0 := by
      by_contra h
      exact absurd (sub_eq_zero.mpr hdiff)
        (by rw [hdiff_eq]; exact mul_ne_zero (Int.cast_ne_zero.mpr h) (zpow_ne_zero _ (by norm_num)))
    intro mode
    unfold fpSubFinite fpAddFinite
    simp only [e_min_def.symm, isum_def.symm, hisum_zero, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    rw [show (a.toVal : R) - b.toVal = 0 from sub_eq_zero.mpr hdiff]
    exact FiniteFp.toVal_isZero rfl
  · -- Nonzero difference: use round_idempotent
    have hsum_ne : isum ≠ 0 := by
      intro hzero; apply hdiff
      have : (a.toVal : R) - b.toVal = 0 := by rw [hdiff_eq, hzero, Int.cast_zero, zero_mul]
      linarith
    have hbound := sterbenz_aligned_diff_bound (R := R) a b ha hb ha_nz hb_nz h_lb h_ub h_exp
    set mag := isum.natAbs with mag_def
    have hmag_pos : 0 < mag := by rwa [mag_def, Int.natAbs_pos]
    have hmag_bound : mag < 2 ^ precNat := by
      have hbound' : isum.natAbs < 2 ^ precNat := by
        simpa [isum_def, sterbenzAlignedDiffInt, sterbenzEMin] using hbound
      simpa [mag_def] using hbound'
    have he_lo : e_base ≥ FloatFormat.min_exp - prec + 1 := by
      rw [e_base_def, he_min_eq]
      have : FloatFormat.min_exp ≤ min a.e b.e := le_min a.valid.1 b.valid.1
      omega
    have he_hi : e_base + prec - 1 ≤ FloatFormat.max_exp := by
      rw [e_base_def, he_min_eq]
      have : min a.e b.e ≤ FloatFormat.max_exp := le_trans (min_le_left _ _) a.valid.2.1; omega
    have hdiff_ne : (a.toVal : R) - b.toVal ≠ 0 := sub_ne_zero.mpr hdiff
    by_cases hisum_pos : 0 < isum
    · -- Positive difference
      have hmag_eq : (a.toVal : R) - b.toVal = (mag : R) * (2 : R) ^ e_base := by
        rw [hdiff_eq, mag_def]; congr 1
        rw [show (isum.natAbs : R) = ((isum.natAbs : ℤ) : R) from (Int.cast_natCast _).symm,
            Int.natAbs_of_nonneg (le_of_lt hisum_pos)]
      obtain ⟨f, hfs, hfv⟩ := exists_finiteFp_of_nat_mul_zpow (R := R) mag e_base
        hmag_pos hmag_bound he_lo he_hi
      intro mode
      refine ⟨f, ?_, by rw [hfv, hmag_eq]⟩
      rw [fpSubFinite_correct (R := R) mode a b hdiff_ne,
          show (a.toVal : R) - b.toVal = f.toVal from by rw [hfv, hmag_eq]]
      exact round_idempotent (R := R) mode f (Or.inl hfs)
    · -- Negative difference
      push_neg at hisum_pos
      have hisum_neg : isum < 0 := by omega
      have hmag_eq : (a.toVal : R) - b.toVal = -((mag : R) * (2 : R) ^ e_base) := by
        rw [hdiff_eq, mag_def]
        rw [show (isum.natAbs : R) = ((isum.natAbs : ℤ) : R) from (Int.cast_natCast _).symm,
            Int.ofNat_natAbs_of_nonpos (le_of_lt hisum_neg)]
        push_cast; ring
      obtain ⟨g, hgs, hgv⟩ := exists_finiteFp_of_nat_mul_zpow (R := R) mag e_base
        hmag_pos hmag_bound he_lo he_hi
      have hg_pos : (0 : R) < g.toVal := by rw [hgv]; positivity
      have hgm_pos : 0 < g.m := ((FiniteFp.toVal_pos_iff (R := R)).mpr hg_pos).2
      have hgv_neg : g.toVal (R := R) = -((a.toVal : R) - b.toVal) := by
        rw [hgv]; linarith [hmag_eq]
      intro mode
      obtain ⟨hrnd, hval⟩ := round_neg_exact (R := R) mode _ g hgs hgm_pos hgv_neg
      exact ⟨-g, by rw [fpSubFinite_correct (R := R) mode a b hdiff_ne]; exact hrnd, hval⟩

/-! ## Corollaries -/

/-- When `a ≠ b` in value, all rounding modes produce the same result. -/
theorem sterbenz_unique (a b : FiniteFp) (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (h_lb : (b.toVal : R) / 2 ≤ a.toVal)
    (h_ub : (a.toVal : R) ≤ 2 * b.toVal)
    (hdiff : (a.toVal : R) ≠ b.toVal) :
    ∃ f : FiniteFp, f.toVal (R := R) = a.toVal - b.toVal ∧
      ∀ mode : RoundingMode, fpSubFinite mode a b = Fp.finite f := by
  have hs := sterbenz (R := R) a b ha hb ha_nz hb_nz h_lb h_ub
  -- All modes produce finite results with the same toVal; since diff ≠ 0, the float is unique
  obtain ⟨f₀, hf₀_eq, hf₀_val⟩ := hs .Up
  refine ⟨f₀, hf₀_val, fun mode => ?_⟩
  obtain ⟨f, hf_eq, hf_val⟩ := hs mode
  rw [hf_eq]
  congr 1
  -- f and f₀ have the same toVal and the diff is nonzero, so they're equal
  have hf_nz : ¬f.isZero := by
    intro hz; rw [FiniteFp.toVal_isZero hz] at hf_val; exact absurd hf_val.symm (sub_ne_zero.mpr hdiff)
  apply FiniteFp.eq_of_toVal_eq' (R := R) (Or.inl hf_nz)
  rw [hf_val, hf₀_val]

/-- **Sterbenz for `fpSub`**: the full `Fp` subtraction also produces an exact finite result
    under Sterbenz conditions. -/
theorem sterbenz_fpSub (a b : FiniteFp) (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (h_lb : (b.toVal : R) / 2 ≤ a.toVal)
    (h_ub : (a.toVal : R) ≤ 2 * b.toVal) :
    ∀ mode : RoundingMode, ∃ f : FiniteFp,
      fpSub mode (.finite a) (.finite b) = Fp.finite f ∧
        f.toVal (R := R) = a.toVal - b.toVal := by
  intro mode
  -- fpSub on finite inputs is just fpSubFinite
  have : fpSub mode (.finite a) (.finite b) = fpSubFinite mode a b := rfl
  rw [this]
  exact sterbenz (R := R) a b ha hb ha_nz hb_nz h_lb h_ub mode

end Sterbenz
