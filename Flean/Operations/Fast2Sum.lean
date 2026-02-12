import Flean.Operations.Sterbenz
import Flean.Operations.MulPow2

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

/-! ## Layer 1: Sterbenz conditions for `s - a`

For positive same-sign operands with `a ≥ b`, the rounded sum `s` satisfies
`a ≤ s ≤ 2a`, so Sterbenz applies to `s - a`. -/

/-- The rounded sum of positive values is at least as large as the larger operand. -/
theorem round_sum_ge_left (mode : RoundingMode) (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false) (_ha_nz : 0 < a.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp) (hs : fpAddFinite mode a b = Fp.finite s_fp) :
    (a.toVal : R) ≤ s_fp.toVal := by
  have hb_nonneg : (0 : R) ≤ b.toVal := by
    rw [FiniteFp.toVal_pos_eq b hb]; positivity
  have hmono : mode.round (a.toVal (R := R)) ≤ mode.round (a.toVal + b.toVal) :=
    RoundingMode.round_mono mode (le_add_of_nonneg_right hb_nonneg)
  have hround_a : mode.round (a.toVal (R := R)) = Fp.finite a :=
    round_idempotent (R := R) mode a (Or.inl ha)
  rw [fpAddFinite_correct (R := R) mode a b hsum_ne] at hs
  rw [hround_a] at hmono; rw [hs] at hmono
  exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff a s_fp).mp hmono)

/-- The rounded sum of positive values with `a ≥ b` is at most `2a`. -/
theorem round_sum_le_double (mode : RoundingMode) (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false) (ha_nz : 0 < a.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp) (hs : fpAddFinite mode a b = Fp.finite s_fp) :
    (s_fp.toVal : R) ≤ 2 * a.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hab_le : (a.toVal : R) + b.toVal ≤ 2 * a.toVal := by linarith
  rw [fpAddFinite_correct (R := R) mode a b hsum_ne] at hs
  by_cases he : a.e + 1 ≤ FloatFormat.max_exp
  · -- Case 1: 2a representable via exponent shift
    obtain ⟨d, hds, hdv⟩ := mul_pow2_representable (R := R) a 1 ha_nz ha
      (by have := a.valid.1; omega) he
    have hdv' : (d.toVal : R) = 2 * a.toVal := by rw [hdv, zpow_one]; ring
    have hmono : mode.round ((a.toVal : R) + b.toVal) ≤ mode.round (d.toVal (R := R)) :=
      RoundingMode.round_mono mode (by rw [hdv']; exact hab_le)
    have hround_d := round_idempotent (R := R) mode d (Or.inl hds)
    rw [hround_d] at hmono; rw [hs] at hmono
    linarith [FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff s_fp d).mp hmono)]
  · -- Case 2: a.e = max_exp
    push_neg at he
    have ha_e_eq : a.e = FloatFormat.max_exp := le_antisymm a.valid.2.1 (by omega)
    have hs_s : s_fp.s = false := by
      have hs_ge := round_sum_ge_left (R := R) mode a b ha hb ha_nz hsum_ne s_fp
        (by rw [fpAddFinite_correct (R := R) mode a b hsum_ne]; exact hs)
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
      have hmono : mode.round ((a.toVal : R) + b.toVal) ≤ mode.round (d.toVal (R := R)) :=
        RoundingMode.round_mono mode (by rw [hdv']; exact hab_le)
      rw [round_idempotent (R := R) mode d (Or.inl hds)] at hmono; rw [hs] at hmono
      linarith [FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff s_fp d).mp hmono)]

/-- Sterbenz conditions hold for `(s_fp, a)` when `a, b` are positive with `a ≥ b`. -/
theorem sterbenz_sub_sa (mode : RoundingMode) (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (_hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp) (hs : fpAddFinite mode a b = Fp.finite s_fp) :
    ∃ z_fp : FiniteFp,
      fpSubFinite mode s_fp a = Fp.finite z_fp ∧
        z_fp.toVal (R := R) = s_fp.toVal - a.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hs_ge_a := round_sum_ge_left (R := R) mode a b ha hb ha_nz hsum_ne s_fp hs
  have hs_le_2a := round_sum_le_double (R := R) mode a b ha hb ha_nz hab hsum_ne s_fp hs
  have hs_s : s_fp.s = false :=
    ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).1
  have hs_m : 0 < s_fp.m :=
    ((FiniteFp.toVal_pos_iff (R := R)).mpr (by linarith)).2
  exact sterbenz (R := R) s_fp a hs_s ha hs_m ha_nz (by linarith) hs_le_2a mode

/-! ## Layer 2: Subtraction of equal-valued floats yields finite zero -/

omit [FloorRing R] in
/-- When `a.toVal = b.toVal`, `fpSubFinite` returns a finite zero. -/
theorem fpSubFinite_zero_of_eq_toVal (mode : RoundingMode) (a b : FiniteFp)
    (heq : (a.toVal : R) = b.toVal) :
    ∃ f : FiniteFp, fpSubFinite mode a b = Fp.finite f ∧
      f.toVal (R := R) = 0 := by
  -- fpSubFinite = fpAddFinite mode a (-b)
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
  -- fpSubFinite unfolds to fpAddFinite which checks if the integer sum is 0
  show ∃ f, fpAddFinite mode a (-b) = Fp.finite f ∧ f.toVal (R := R) = 0
  -- Unfold and use the fact that the sum is 0
  simp only [fpAddFinite, hkey, ↓reduceIte]
  exact ⟨_, rfl, FiniteFp.toVal_isZero rfl⟩

/-! ## Layer 2b: Rounding error representability

The error `(a + b) - s` is exactly representable as a float for round-to-nearest modes. -/

/-- For positive x in normal range, any nearest-mode finite result f satisfies
    `f.toVal ≤ 2x − pred.toVal`, where pred is the floor (roundDown) of x.
    This encodes that nearest rounding never overshoots the "reflected predecessor"
    bound, i.e., the result + pred ≤ 2x. -/
private theorem nearest_round_le_two_x_sub_pred
    (mode : RoundingMode) (x : R) (hxpos : 0 < x) (hx : isNormalRange x)
    (hmode : mode = .NearestTiesToEven ∨ mode = .NearestTiesAwayFromZero)
    (f : FiniteFp) (hf : mode.round x = Fp.finite f) :
    (f.toVal : R) ≤ 2 * x - (findPredecessorPos x hxpos).toVal := by
  have hpred_le := findPredecessorPos_le x hxpos (R := R)
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have h_not_small : ¬(|x| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    intro h_abs; rw [abs_of_pos hxpos] at h_abs
    linarith [FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp (R := R), hx.left]
  cases hmode with
  | inl hTE =>
    subst hTE; simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hf
    unfold roundNearestTiesToEven at hf
    rw [if_neg hxne, if_neg h_not_small] at hf
    by_cases h_overflow : |x| ≥ FloatFormat.overflowThreshold R
    · rw [if_pos h_overflow] at hf; exact absurd hf (by simp)
    · rw [if_neg h_overflow] at hf
      simp only [findPredecessor_pos_eq x hxpos, findSuccessor_pos_eq x hxpos] at hf
      generalize hsucc : findSuccessorPos x hxpos = succ_val at hf
      cases succ_val with
      | finite s =>
        dsimp only at hf
        split_ifs at hf with h1 h2 h3
        all_goals simp only [Fp.finite.injEq] at hf
        · rw [← hf]; linarith  -- x < mid, f = pred
        · rw [← hf]; linarith  -- x > mid, f = succ
        · rw [← hf]; linarith  -- tie, even → pred
        · rw [← hf]; linarith [not_lt.mp h1, not_lt.mp h2]  -- tie, odd → succ
      | infinite b =>
        dsimp only at hf; rw [← Fp.finite.inj hf]; linarith
      | NaN => exfalso; exact findSuccessorPos_ne_nan x hxpos (by simp [hsucc])
  | inr hTA =>
    subst hTA; simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hf
    unfold roundNearestTiesAwayFromZero at hf
    rw [if_neg hxne, if_neg h_not_small] at hf
    by_cases h_overflow : |x| ≥ FloatFormat.overflowThreshold R
    · rw [if_pos h_overflow] at hf; exact absurd hf (by simp)
    · rw [if_neg h_overflow] at hf
      simp only [findPredecessor_pos_eq x hxpos, findSuccessor_pos_eq x hxpos] at hf
      generalize hsucc : findSuccessorPos x hxpos = succ_val at hf
      cases succ_val with
      | finite s =>
        dsimp only at hf
        split_ifs at hf with h1 h2
        all_goals simp only [Fp.finite.injEq] at hf
        · rw [← hf]; linarith  -- x < mid, f = pred
        · rw [← hf]; linarith  -- x > mid, f = succ
        · rw [← hf]; linarith [not_lt.mp h1, not_lt.mp h2]  -- tie → succ
      | infinite b =>
        dsimp only at hf; rw [← Fp.finite.inj hf]; linarith
      | NaN => exfalso; exact findSuccessorPos_ne_nan x hxpos (by simp [hsucc])

/-- The rounding error of a nearest-mode addition of positive floats with `|b| ≤ |a|`
is representable as a float. -/
theorem add_error_representable (mode : RoundingMode) (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hmode : mode = .NearestTiesToEven ∨ mode = .NearestTiesAwayFromZero)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp) (hs : fpAddFinite mode a b = Fp.finite s_fp) :
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
  have hs_correct : mode.round ((a.toVal : R) + b.toVal) = Fp.finite s_fp := by
    rw [← fpAddFinite_correct (R := R) mode a b hsum_ne]; exact hs
  have hs_ge_a := round_sum_ge_left (R := R) mode a b ha hb ha_nz hsum_ne s_fp hs
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
    obtain ⟨g, _, hgv, hround⟩ := subnormal_sum_exact (R := R) mode a b ha hb hb_nz.ne' ha_sub hb_sub hfit
    have : s_fp = g := Fp.finite.inj (by rw [← hs_correct, hround])
    exact absurd (show (a.toVal : R) + b.toVal - s_fp.toVal = 0 by rw [this, hgv]; ring) herr
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
      exact absurd (hs_correct ▸ nearest_round_overflow mode _ hmode h_ot_le) (by simp)
  -- Step D: Error bound |error| ≤ b via helper + roundDown ≥ a
  set pred := findPredecessorPos ((a.toVal : R) + b.toVal) hval_pos with pred_def
  have hhelper := nearest_round_le_two_x_sub_pred mode _ hval_pos hNR hmode s_fp hs_correct
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

/-! ## Layer 3: Main theorem (positive case) -/

/-- **Fast2Sum correctness** for the positive same-sign case.

When `a, b ≥ 0` with `a ≥ b` and both nonzero, the Fast2Sum algorithm produces
exact error recovery for round-to-nearest modes. -/
theorem fast2Sum_pos_exact (mode : RoundingMode) (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hmode : mode = .NearestTiesToEven ∨ mode = .NearestTiesAwayFromZero)
    (s_fp : FiniteFp) (hs : fpAddFinite mode a b = Fp.finite s_fp) :
    ∃ z_fp t_fp : FiniteFp,
      fpSubFinite mode s_fp a = Fp.finite z_fp ∧
        fpSubFinite mode b z_fp = Fp.finite t_fp ∧
          (s_fp.toVal : R) + t_fp.toVal = a.toVal + b.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by linarith
  -- Step 1: z = s - a is exact by Sterbenz
  obtain ⟨z_fp, hz_eq, hz_val⟩ :=
    sterbenz_sub_sa (R := R) mode a b ha hb ha_nz hb_nz hab hsum_ne s_fp hs
  -- Step 2: b - z is exact
  -- b.toVal - z_fp.toVal = b.toVal - (s.toVal - a.toVal) = (a + b) - s
  suffices h_bz : ∃ t_fp : FiniteFp,
      fpSubFinite mode b z_fp = Fp.finite t_fp ∧
        (t_fp.toVal : R) = b.toVal - z_fp.toVal by
    obtain ⟨t_fp, ht_eq, ht_val⟩ := h_bz
    exact ⟨z_fp, t_fp, hz_eq, ht_eq, by rw [ht_val, hz_val]; ring⟩
  by_cases htz : (b.toVal : R) - z_fp.toVal = 0
  · -- Zero error: addition was exact, b = z in value
    have hbeq : (b.toVal : R) = z_fp.toVal := sub_eq_zero.mp htz
    obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) mode b z_fp hbeq
    exact ⟨f, hf_eq, by rw [hf_val, htz]⟩
  · -- Nonzero error: the error is representable
    obtain ⟨err_fp, herr_valid, herr_val⟩ :=
      add_error_representable (R := R) mode a b ha hb ha_nz hb_nz hab hmode hsum_ne s_fp hs
    have hbz_val : (b.toVal : R) - z_fp.toVal = err_fp.toVal := by
      rw [hz_val, herr_val]; ring
    have hsub_eq : fpSubFinite mode b z_fp = Fp.finite err_fp := by
      rw [fpSubFinite_correct (R := R) mode b z_fp htz, hbz_val,
          round_idempotent (R := R) mode err_fp herr_valid]
    exact ⟨err_fp, hsub_eq, hbz_val.symm⟩

end Fast2Sum
