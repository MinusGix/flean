import Flean.Rounding.Rounding
import Flean.Rounding.ModeClass
import Flean.Rounding.PolicyInstances
import Flean.ToVal

/-! # RModeGrid Instance

This file provides an instance of `RModeGrid` for any nearest rounding mode
(`RModeNearest`).

The key insight: if `x = n * 2^g` and `round(x)` is finite, the result is
also on grid `2^g`. This follows from:
- If the ULP at `x`'s binade ≤ `2^g`: the result (a multiple of ULP) is
  automatically a multiple of `2^g`.
- If the ULP > `2^g`: `x` is exactly representable, so `round(x) = x`.
-/

section GridInstance

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## RModeGrid: Rounding preserves grid alignment -/

omit [FloorRing R] in
/-- When a positive float's ULP exponent is ≥ g, its value is on grid 2^g. -/
private theorem fp_on_grid (f : FiniteFp) (hs : f.s = false)
    (g : ℤ) (hg : g ≤ f.e - prec + 1) :
    ∃ m : ℤ, f.toVal (R := R) = (m : R) * (2 : R) ^ g :=
  FiniteFp.toVal_int_mul_zpow f hs g hg

omit [FloorRing R] in
/-- A zero float is on any grid. -/
private theorem zero_on_grid (f : FiniteFp) (hm : f.m = 0)
    (g : ℤ) :
    ∃ m : ℤ, f.toVal (R := R) = (m : R) * (2 : R) ^ g :=
  ⟨0, by rw [FiniteFp.toVal_isZero (show f.isZero from hm), Int.cast_zero, zero_mul]⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- A negative float on grid g: if -f is on grid g, so is f. -/
private theorem neg_on_grid (f : FiniteFp) (g : ℤ)
    (h : ∃ m : ℤ, (-f).toVal (R := R) = (m : R) * (2 : R) ^ g) :
    ∃ m : ℤ, f.toVal (R := R) = (m : R) * (2 : R) ^ g := by
  obtain ⟨m, hm⟩ := h
  exact ⟨-m, by rw [← neg_neg (f.toVal (R := R)), ← FiniteFp.toVal_neg_eq_neg, hm]; push_cast; ring⟩

omit [FloorRing R] in
/-- Convert `(coeff : R) < (2:R)^prec` to `coeff.natAbs < 2^prec.toNat`. -/
private theorem int_natAbs_lt_of_cast_lt_zpow (coeff : ℤ) (hcoeff_pos : 0 < coeff)
    (hcoeff_lt_R : (coeff : R) < (2 : R) ^ prec) :
    coeff.natAbs < 2 ^ FloatFormat.prec.toNat := by
  have hcoeff_lt_int : coeff < (2 : ℤ) ^ FloatFormat.prec.toNat := by
    have : (2 : R) ^ prec = ((2 : ℤ) ^ FloatFormat.prec.toNat : ℤ) := by
      push_cast; rw [← zpow_natCast (2 : R), FloatFormat.prec_toNat_eq]
    rw [this] at hcoeff_lt_R
    exact_mod_cast hcoeff_lt_R
  have h_natabs_eq : (coeff.natAbs : ℤ) = coeff := Int.natAbs_of_nonneg (le_of_lt hcoeff_pos)
  have : (coeff.natAbs : ℤ) < (2 : ℤ) ^ FloatFormat.prec.toNat := by omega
  exact_mod_cast this

omit [FloorRing R] in
/-- When `n * 2^g` is positive and in binade `[2^e, 2^(e+1))` with `g > e - prec + 1`,
    then `n * 2^g` is exactly representable as a FiniteFp.
    Returns the FiniteFp, its idempotence condition, and the value equality. -/
private theorem grid_exact_representable
    (n : ℤ) (g : ℤ) (e : ℤ)
    (hn_pos : 0 < n)
    (hulp : e - prec + 1 < g)
    (hx_lt_binade : (n : R) * (2 : R) ^ g < (2 : R) ^ (e + 1))
    (he_lo : e ≥ FloatFormat.min_exp)
    (he_hi : e ≤ FloatFormat.max_exp) :
    ∃ fp_x : FiniteFp, (fp_x.s = false ∨ 0 < fp_x.m) ∧
      fp_x.toVal (R := R) = (n : R) * (2 : R) ^ g := by
  set e_ulp := e - prec + 1
  -- n < 2^(e + 1 - g): divide binade bound by 2^g
  have hn_lt : (n : R) < (2 : R) ^ (e + 1 - g) := by
    have h2g_pos := zpow_pos (by norm_num : (0 : R) < 2) g
    calc (n : R) = (n : R) * (2 : R) ^ g * ((2 : R) ^ g)⁻¹ := by
          rw [mul_inv_cancel_right₀ (ne_of_gt h2g_pos)]
      _ < (2 : R) ^ (e + 1) * ((2 : R) ^ g)⁻¹ :=
          mul_lt_mul_of_pos_right hx_lt_binade (inv_pos.mpr h2g_pos)
      _ = (2 : R) ^ (e + 1 - g) := by
          rw [← div_eq_mul_inv, ← zpow_sub₀ (by norm_num : (2 : R) ≠ 0)]
  -- coeff = n * 2^(g - e_ulp), fits in prec bits
  have hg_sub_pos : 0 < g - e_ulp := by omega
  set coeff := n * (2 : ℤ) ^ (g - e_ulp).toNat
  have hcoeff_pos : 0 < coeff := by
    apply mul_pos hn_pos; exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hcoeff_lt_R : (coeff : R) < (2 : R) ^ prec := by
    show (↑(n * (2 : ℤ) ^ (g - e_ulp).toNat) : R) < _; push_cast
    rw [← zpow_natCast (2 : R) (g - e_ulp).toNat, show ((g - e_ulp).toNat : ℤ) = g - e_ulp from
      Int.toNat_of_nonneg (by omega)]
    calc (n : R) * (2 : R) ^ (g - e_ulp)
        < (2 : R) ^ (e + 1 - g) * (2 : R) ^ (g - e_ulp) :=
          mul_lt_mul_of_pos_right hn_lt (zpow_pos (by norm_num) _)
      _ = (2 : R) ^ (e + 1 - g + (g - e_ulp)) := by rw [← two_zpow_mul]
      _ = (2 : R) ^ prec := by congr 1; simp only [e_ulp]; ring
  have hcoeff_bound := int_natAbs_lt_of_cast_lt_zpow (R := R) coeff hcoeff_pos hcoeff_lt_R
  obtain ⟨fp_x, hfp_cond, hfp_val⟩ := exists_finiteFp_of_int_mul_zpow (R := R)
    coeff e_ulp (by omega) hcoeff_bound (by omega) (by omega)
  refine ⟨fp_x, hfp_cond, ?_⟩
  rw [hfp_val]; show (↑(n * (2 : ℤ) ^ (g - e_ulp).toNat) : R) * _ = _; push_cast
  rw [← zpow_natCast (2 : R) (g - e_ulp).toNat, show ((g - e_ulp).toNat : ℤ) = g - e_ulp from
    Int.toNat_of_nonneg (by omega)]
  rw [mul_assoc, two_zpow_mul]; congr 1; simp only [e_ulp]; ring

/-- Grid preservation for roundDown of positive values. -/
private theorem roundDown_preserves_grid_pos
    [RMode R] [RModeIdem R]
    (n : ℤ) (g : ℤ)
    (hn_pos : 0 < n)
    (hg : g ≥ FloatFormat.min_exp - prec + 1)
    (hx_bound : (n : R) * (2 : R) ^ g < (2 : R) ^ (FloatFormat.max_exp + 1))
    (f : FiniteFp) (hf : roundDown ((n : R) * (2 : R) ^ g) = Fp.finite f) :
    ∃ m : ℤ, f.toVal (R := R) = (m : R) * (2 : R) ^ g := by
  -- f.s = false because roundDown of positive is non-negative
  have hx_pos : (0 : R) < (n : R) * (2 : R) ^ g := by
    apply mul_pos
    · exact_mod_cast hn_pos
    · exact zpow_pos (by norm_num) _
  have hf_sign : f.s = false := by
    have hrd : roundDown ((n : R) * (2 : R) ^ g) = Fp.finite (findPredecessorPos _ hx_pos) := by
      simp [roundDown, findPredecessor, ne_of_gt hx_pos, hx_pos]
    rw [hrd] at hf
    have := Fp.finite.inj hf; subst this
    exact findPredecessorPos_sign_false _ hx_pos
  -- Case split: is f's ULP exponent ≥ g?
  by_cases hulp : g ≤ f.e - prec + 1
  · -- ULP exponent ≥ g: f is automatically on grid g
    exact fp_on_grid f hf_sign g hulp
  · -- ULP exponent < g: x = n * 2^g is exactly representable
    push_neg at hulp -- hulp : f.e - prec + 1 < g
    -- f = roundDown(x), so f.toVal ≤ x
    have hf_eq_pred : f = findPredecessorPos _ hx_pos := by
      have hrd : roundDown ((n : R) * (2 : R) ^ g) = Fp.finite (findPredecessorPos _ hx_pos) := by
        simp [roundDown, findPredecessor, ne_of_gt hx_pos, hx_pos]
      exact Fp.finite.inj (hf.symm.trans hrd)
    have hf_le : f.toVal (R := R) ≤ (n : R) * (2 : R) ^ g := by
      rw [hf_eq_pred]
      exact findPredecessorPos_le _ hx_pos
    -- f.m > 0: x ≥ sps.toVal, so roundDown(x) ≥ roundDown(sps) ≥ sps.toVal > 0
    have hf_m_pos : 0 < f.m := by
      have hsps_pos := FiniteFp.smallestPosSubnormal_toVal_pos (R := R)
      have hx_ge_sps : FiniteFp.smallestPosSubnormal.toVal ≤ (n : R) * (2 : R) ^ g := by
        rw [FiniteFp.smallestPosSubnormal_toVal]
        calc (2 : R) ^ (FloatFormat.min_exp - prec + 1) ≤ (2 : R) ^ g := two_zpow_mono (R := R) hg
          _ = 1 * (2 : R) ^ g := (one_mul _).symm
          _ ≤ (n : R) * (2 : R) ^ g :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hn_pos) (le_of_lt (zpow_pos (by norm_num) _))
      have hsps_idem := roundDown_idempotent_nonneg (R := R)
        FiniteFp.smallestPosSubnormal (by rfl) (by norm_num [FiniteFp.smallestPosSubnormal])
      have hsps_pred : findPredecessorPos (FiniteFp.smallestPosSubnormal.toVal (R := R)) hsps_pos
          = FiniteFp.smallestPosSubnormal := by
        have : roundDown (FiniteFp.smallestPosSubnormal.toVal (R := R)) =
            Fp.finite FiniteFp.smallestPosSubnormal := hsps_idem
        simp [roundDown, findPredecessor, ne_of_gt hsps_pos, hsps_pos] at this
        exact this
      have hf_toVal_pos : (0 : R) < f.toVal := by
        rw [hf_eq_pred]
        calc (0 : R) < FiniteFp.smallestPosSubnormal.toVal := hsps_pos
          _ = (findPredecessorPos _ hsps_pos).toVal := by rw [hsps_pred]
          _ ≤ (findPredecessorPos _ hx_pos).toVal :=
            findPredecessorPos_toVal_mono hsps_pos hx_pos hx_ge_sps
      exact (FiniteFp.toVal_pos_iff (R := R)).mpr hf_toVal_pos |>.2
    -- x < 2^(f.e + 1): binade bound
    have hx_lt_binade : (n : R) * (2 : R) ^ g < (2 : R) ^ (f.e + 1) := by
      rcases eq_or_lt_of_le f.valid.2.1 with hfe_eq | hfe_lt
      · -- f.e = max_exp: directly from hx_bound
        rw [hfe_eq]; exact hx_bound
      · -- f.e < max_exp: construct FP at 2^(f.e+1), use mono for contradiction
        by_contra hge; push_neg at hge
        -- Construct an FP with value 2^(f.e + 1)
        have hfe_succ_le : f.e + 1 ≤ FloatFormat.max_exp := by omega
        obtain ⟨fp_pow, hfp_cond, hfp_val⟩ := exists_finiteFp_of_int_mul_zpow (R := R)
          ((2 : ℤ) ^ (prec - 1).toNat) (f.e - prec + 2)
          (by positivity)
          (by rw [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
              exact Nat.pow_lt_pow_right (by norm_num) (by have := FloatFormat.valid_prec; omega))
          (by have := f.valid.1; omega)
          (by omega)
        -- fp_pow.toVal = 2^(f.e + 1)
        have hfp_val_eq : fp_pow.toVal (R := R) = (2 : R) ^ (f.e + 1) := by
          rw [hfp_val]; push_cast; rw [← zpow_natCast (2 : R) (prec - 1).toNat, two_zpow_mul]
          congr 1; rw [FloatFormat.prec_sub_one_toNat_eq]; ring
        -- By idempotence, roundDown(2^(f.e+1)) = Fp.finite fp_pow
        have hfp_idem := roundDown_idempotent (R := R) fp_pow hfp_cond
        have hfp_pos : (0 : R) < fp_pow.toVal := by
          rw [hfp_val_eq]; exact zpow_pos (by norm_num) _
        -- findPredecessorPos(2^(f.e+1)) = fp_pow
        have hfp_pred : findPredecessorPos (fp_pow.toVal (R := R)) hfp_pos = fp_pow := by
          simp [roundDown, findPredecessor, ne_of_gt hfp_pos, hfp_pos] at hfp_idem
          exact hfp_idem
        -- By monotonicity: fp_pow.toVal ≤ f.toVal
        have hmono := findPredecessorPos_toVal_mono hfp_pos hx_pos (by rw [hfp_val_eq]; exact hge)
        rw [hfp_pred] at hmono
        rw [← hf_eq_pred] at hmono
        -- But f.toVal < 2^(f.e+1) = fp_pow.toVal — contradiction
        linarith [FiniteFp.toVal_lt_zpow_succ (R := R) f hf_sign, hfp_val_eq]
    -- Exact representability via grid_exact_representable
    obtain ⟨fp_x, hfp_cond, hfp_eq⟩ := grid_exact_representable (R := R) n g f.e
      hn_pos hulp hx_lt_binade (by have := f.valid.1; omega) f.valid.2.1
    have hfp_idem := roundDown_idempotent (R := R) fp_x hfp_cond
    rw [hfp_eq] at hfp_idem
    have : f = fp_x := Fp.finite.inj (hf.symm.trans hfp_idem)
    exact ⟨n, by rw [this, hfp_eq]⟩

/-- Grid preservation for roundUp of positive values. -/
private theorem roundUp_preserves_grid_pos
    [RMode R] [RModeIdem R]
    (n : ℤ) (g : ℤ)
    (hn_pos : 0 < n)
    (f : FiniteFp) (hf : roundUp ((n : R) * (2 : R) ^ g) = Fp.finite f) :
    ∃ m : ℤ, f.toVal (R := R) = (m : R) * (2 : R) ^ g := by
  have hx_pos : (0 : R) < (n : R) * (2 : R) ^ g := by
    apply mul_pos
    · exact_mod_cast hn_pos
    · exact zpow_pos (by norm_num) _
  -- f.toVal ≥ x > 0, so f.s = false and f.m > 0
  have hf_ge : (n : R) * (2 : R) ^ g ≤ f.toVal (R := R) := by
    have hru : roundUp ((n : R) * (2 : R) ^ g) = findSuccessorPos _ hx_pos := by
      simp [roundUp, findSuccessor, ne_of_gt hx_pos, hx_pos]
    rw [hru] at hf; exact findSuccessorPos_ge _ hx_pos f hf
  have hf_toVal_pos : (0 : R) < f.toVal := lt_of_lt_of_le hx_pos hf_ge
  have hf_sign : f.s = false := ((FiniteFp.toVal_pos_iff (R := R)).mpr hf_toVal_pos).1
  by_cases hulp : g ≤ f.e - prec + 1
  · exact fp_on_grid f hf_sign g hulp
  · push_neg at hulp
    -- x ≤ f.toVal < 2^(f.e + 1)
    have hx_lt_binade : (n : R) * (2 : R) ^ g < (2 : R) ^ (f.e + 1) :=
      lt_of_le_of_lt hf_ge (FiniteFp.toVal_lt_zpow_succ (R := R) f hf_sign)
    obtain ⟨fp_x, hfp_cond, hfp_eq⟩ := grid_exact_representable (R := R) n g f.e
      hn_pos hulp hx_lt_binade (by have := f.valid.1; omega) f.valid.2.1
    have hfp_idem := roundUp_idempotent (R := R) fp_x hfp_cond
    rw [hfp_eq] at hfp_idem
    have : f = fp_x := Fp.finite.inj (hf.symm.trans hfp_idem)
    exact ⟨n, by rw [this, hfp_eq]⟩

/-- **RModeGrid instance** for nearest rounding modes. -/
instance nearest_RModeGrid [RMode R] [RModeNearest R] [RModeConj R] : RModeGrid R where
  round_preserves_grid n g hg f hf := by
    -- Case 1: n = 0 → x = 0, round(0) is a zero
    by_cases hn : n = 0
    · subst hn
      simp only [Int.cast_zero, zero_mul] at hf
      have hfz : f.m = 0 := by
        have := RModeZero.round_zero (R := R)
        rw [this] at hf
        exact (Fp.finite.inj hf).symm ▸ rfl
      exact zero_on_grid f hfz g
    · -- Case 2: n > 0 or n < 0
      rcases lt_or_gt_of_ne hn with hn_neg | hn_pos
      · -- n < 0: use conjugation to reduce to positive case
        have hx_ne : (n : R) * (2 : R) ^ g ≠ 0 := by
          apply mul_ne_zero
          · exact_mod_cast hn
          · exact ne_of_gt (zpow_pos (by norm_num) _)
        have hn_neg_pos : 0 < -n := by omega
        have hx_neg : ((-n : ℤ) : R) * (2 : R) ^ g = -((n : R) * (2 : R) ^ g) := by
          push_cast; ring
        have hf_neg : ○(((-n : ℤ) : R) * (2 : R) ^ g) = Fp.finite (-f) := by
          rw [hx_neg]
          rw [RModeConj.round_neg (R := R) _ hx_ne, hf, Fp.neg_finite]
        -- Overflow bound: (-n) * 2^g < 2^(max_exp + 1)
        have hx_bound_neg : ((-n : ℤ) : R) * (2 : R) ^ g < (2 : R) ^ (FloatFormat.max_exp + 1) := by
          by_contra h_ge; push_neg at h_ge
          have h_ot := le_trans (le_of_lt FloatFormat.overflowThreshold_lt_zpow_max_exp_succ) h_ge
          rw [RModeNearest.overflow_pos_inf (R := R) _ h_ot] at hf_neg; simp at hf_neg
        rcases RModeNearest.round_eq_roundDown_or_roundUp (((-n : ℤ) : R) * (2 : R) ^ g) with hrd | hru
        · rw [hrd] at hf_neg
          exact neg_on_grid f g (roundDown_preserves_grid_pos (R := R) (-n) g hn_neg_pos hg hx_bound_neg (-f) hf_neg)
        · rw [hru] at hf_neg
          exact neg_on_grid f g (roundUp_preserves_grid_pos (R := R) (-n) g hn_neg_pos (-f) hf_neg)
      · -- n > 0: case split on roundDown or roundUp
        -- Overflow bound: n * 2^g < 2^(max_exp + 1)
        have hx_bound_pos : (n : R) * (2 : R) ^ g < (2 : R) ^ (FloatFormat.max_exp + 1) := by
          by_contra h_ge; push_neg at h_ge
          have h_ot := le_trans (le_of_lt FloatFormat.overflowThreshold_lt_zpow_max_exp_succ) h_ge
          rw [RModeNearest.overflow_pos_inf (R := R) _ h_ot] at hf; simp at hf
        rcases RModeNearest.round_eq_roundDown_or_roundUp ((n : R) * (2 : R) ^ g) with hrd | hru
        · rw [hrd] at hf
          exact roundDown_preserves_grid_pos (R := R) n g hn_pos hg hx_bound_pos f hf
        · rw [hru] at hf
          exact roundUp_preserves_grid_pos (R := R) n g hn_pos f hf

end GridInstance
