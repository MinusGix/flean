import Flean.Operations.ExpComputableDefs

/-! # Computable exp: bracket correctness (Thread 1)

Soundness proofs for the computable exp kernel. Shows that:
- The exact case (x = 0) produces correct output
- `expBounds` produces valid brackets (`lower < exp(x) ≤ upper`)
- These feed into the generic `stickyTryOne`/`stickyExtractLoop` soundness
-/

section ExpComputable

variable [FloatFormat]

/-! ## Soundness -/

theorem expComputableRun_exact_mag_ne_zero (a : FiniteFp) (o : OpRefOut)
    (hr : expComputableRun a = o) (hExact : o.isExact = true) : o.q ≠ 0 := by
  have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
  rw [expComputableRun_zero a hm] at hr
  subst hr
  norm_num

theorem expComputableRun_exact_value (a : FiniteFp) (o : OpRefOut)
    (hr : expComputableRun a = o) (hExact : o.isExact = true) :
    intSigVal (R := ℝ) false (2 * o.q) o.e_base = Real.exp (a.toVal : ℝ) := by
  have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
  rw [expComputableRun_zero a hm] at hr
  subst hr
  simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
  have hval : (a.toVal : ℝ) = 0 :=
    FiniteFp.toVal_isZero (show a.isZero from hm)
  rw [hval, Real.exp_zero]
  norm_num

/-! ## Bracket correctness -/

omit [FloatFormat] in
/-- The r-interval from `expRIntervalWith` brackets `x - k * log 2`. -/
theorem expRIntervalWith_brackets (x : ℚ) (k : ℤ) (lo2 hi2 : ℚ)
    (hlo2 : (lo2 : ℝ) ≤ Real.log 2) (hhi2 : Real.log 2 ≤ (hi2 : ℝ)) :
    let (r_lo, r_hi) := expRIntervalWith x k lo2 hi2
    (r_lo : ℝ) ≤ (x : ℝ) - ↑k * Real.log 2 ∧
    (x : ℝ) - ↑k * Real.log 2 ≤ (r_hi : ℝ) := by
  simp only [expRIntervalWith]
  split
  · -- k ≥ 0
    case isTrue hk =>
      push_cast
      have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      constructor <;> nlinarith
  · -- k < 0
    case isFalse hk =>
      push_neg at hk
      push_cast
      have : (k : ℝ) < 0 := by exact_mod_cast hk
      constructor <;> nlinarith

omit [FloatFormat] in
/-- `(2:ℝ)^k` is not irrational for any integer k. -/
theorem not_irrational_two_zpow (k : ℤ) : ¬Irrational ((2 : ℝ) ^ k) :=
  fun h => h ⟨(2 : ℚ) ^ k, by push_cast; ring⟩

/-- `lower < exp(x)` for the lower bound from `expBounds`. -/
theorem expBounds_lower_lt_exp (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ((expBounds x k iter).1 : ℝ) < Real.exp (x : ℝ) := by
  simp only [expBounds]
  set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
  set lo2 := ln2SeriesSum N_ln2
  set hi2 := lo2 + 1 / 2 ^ N_ln2
  set rp := expRIntervalWith x k lo2 hi2
  set r_lo := rp.1
  set N := expNumTerms + iter * 10
  have hbracket := expRIntervalWith_brackets x k lo2 hi2
    (ln2SeriesSum_le_log2 N_ln2)
    (by have := log2_le_ln2SeriesSum_add N_ln2
        show Real.log 2 ≤ ((ln2SeriesSum N_ln2 + 1 / 2 ^ N_ln2 : ℚ) : ℝ)
        push_cast; linarith)
  simp only [] at hbracket
  set r := (x : ℝ) - ↑k * Real.log 2
  -- Key facts
  have hr_lo_le : (r_lo : ℝ) ≤ r := hbracket.1
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hr_ne : r ≠ 0 := by
    intro hr_zero
    have hirr := irrational_exp_rat x hx
    rw [show Real.exp (x : ℝ) = (2 : ℝ) ^ k from by
      rw [show (x : ℝ) = ↑k * Real.log 2 from by linarith, exp_int_mul_log2]] at hirr
    exact not_irrational_two_zpow k hirr
  -- exp(x) = 2^k * exp(r), so suffices lower_r < exp(r)
  rw [exp_arg_red (x : ℝ) k]
  -- Factor out 2^k from both sides
  show (↑(expLowerBound r_lo N * (2 : ℚ) ^ k) : ℝ) < (2 : ℝ) ^ k * Real.exp r
  push_cast
  rw [show (expLowerBound r_lo N : ℝ) * (2 : ℝ) ^ (k : ℤ) =
      ((2 : ℝ) ^ k) * (expLowerBound r_lo N : ℝ) from by ring]
  exact mul_lt_mul_of_pos_left (by
    simp only [expLowerBound]; split
    · -- r_lo ≥ 0 → taylorExpQ(r_lo, N) < exp(r)
      case isTrue h =>
        have hr_pos : 0 < r := by
          rcases lt_or_eq_of_le h with h' | h'
          · exact lt_of_lt_of_le (by exact_mod_cast h' : (0:ℝ) < (r_lo : ℝ)) hr_lo_le
          · simp only [← h', Rat.cast_zero] at hr_lo_le
            exact lt_of_le_of_ne hr_lo_le (Ne.symm hr_ne)
        by_cases hr_lo_pos : (0 : ℚ) < r_lo
        · exact lt_of_lt_of_le (by exact_mod_cast taylorExpQ_lt_exp r_lo hr_lo_pos N)
            (Real.exp_le_exp_of_le hr_lo_le)
        · push_neg at hr_lo_pos
          rw [le_antisymm hr_lo_pos h, taylorExpQ_zero, Rat.cast_one]
          have := Real.add_one_le_exp r; linarith
    · -- r_lo < 0 → 1/(ty + rem) < exp(r)
      case isFalse h =>
        push_neg at h
        have habs : (0 : ℚ) < -r_lo := by linarith
        have hN_pos : 0 < N := by show 0 < expNumTerms + iter * 10; unfold expNumTerms; omega
        -- taylorExpQ(-r_lo, N) ≥ exp(-r_lo) ≥ 1 + (-r_lo) > 1
        have hS_ge_exp : (taylorExpQ (-r_lo) N : ℝ) ≤
            Real.exp ((-r_lo : ℚ) : ℝ) := by
          exact_mod_cast taylorExpQ_le_exp (-r_lo) (le_of_lt habs) N
        -- exp(-r_lo) > 1 since -r_lo > 0
        have hexp_gt_one : 1 < Real.exp ((-r_lo : ℚ) : ℝ) := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_strictMono (by exact_mod_cast habs)
        -- taylorRemainder is nonneg
        have hR_nonneg : (0 : ℝ) ≤ (taylorRemainder (-r_lo) (N + 1) : ℝ) := by
          unfold taylorRemainder; simp only [show N + 1 ≠ 0 from by omega, ↓reduceIte]
          exact_mod_cast div_nonneg (mul_nonneg (pow_nonneg (le_of_lt habs) _)
            (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        -- S_N(-r_lo) > 1 since S_N contains terms 1 + y + ... and y > 0
        have hS_gt_one : 1 < (taylorExpQ (-r_lo) N : ℝ) := by
          rw [taylorExpQ_cast_eq_sum]
          have hN_ge2 : 2 ≤ N + 1 := by omega
          have h1 : (1 : ℝ) + ((-r_lo : ℚ) : ℝ) ≤
              ∑ k ∈ Finset.range (N + 1), ((-r_lo : ℚ) : ℝ) ^ k / (k.factorial : ℝ) := by
            calc (1 : ℝ) + ((-r_lo : ℚ) : ℝ)
                = ∑ k ∈ Finset.range 2, ((-r_lo : ℚ) : ℝ) ^ k / (k.factorial : ℝ) := by
                    simp [Finset.sum_range_succ]
              _ ≤ _ := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · exact Finset.range_mono hN_ge2
                  · intro i _ _; positivity
          linarith [show (0:ℝ) < ((-r_lo : ℚ) : ℝ) from by exact_mod_cast habs]
        -- sum > 1
        have hsum_gt_one : 1 < (taylorExpQ (-r_lo) N : ℝ) +
            (taylorRemainder (-r_lo) (N + 1) : ℝ) := by linarith
        push_cast [Rat.cast_div, Rat.cast_one, one_div]
        have hsum_pos : (0 : ℝ) < (taylorExpQ (-r_lo) N : ℝ) +
            (taylorRemainder (-r_lo) (N + 1) : ℝ) := by linarith
        by_cases hr_pos : 0 < r
        · -- r > 0: lower_r < 1 < exp(r)
          calc ((taylorExpQ (-r_lo) N : ℝ) + (taylorRemainder (-r_lo) (N + 1) : ℝ))⁻¹
              < 1 := by rw [inv_lt_one_iff₀]; exact Or.inr hsum_gt_one
            _ < Real.exp r := by
                rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
                exact Real.exp_strictMono hr_pos
        · -- r ≤ 0: bound via exp(-r) ≤ S_N(-r_lo) + R(-r_lo) using Real.exp_bound'
          -- and monotonicity of S_N, R in -r_lo ≥ -r > 0.
          push_neg at hr_pos
          have hr_neg : r < 0 := lt_of_le_of_ne hr_pos hr_ne
          have hnr_pos : (0 : ℝ) < -r := by linarith
          have hnr_lt_one : -r ≤ 1 := by
            have := hk_bound; rw [abs_lt] at this; linarith
          have hN_pos : 0 < N := by show 0 < expNumTerms + iter * 10; unfold expNumTerms; omega
          -- exp(-r) ≤ S_N(-r_lo) + R(-r_lo): use monotonicity of S_N and R
          -- Step 1: exp(-r) ≤ Σ_{range(N+1)} (-r)^k/k! + (-r)^{N+1}*(N+2)/((N+1)!*(N+1))
          have hexp_bound := Real.exp_bound' hnr_pos.le hnr_lt_one (n := N + 1) (by omega)
          -- Step 2: Each term (-r)^k/k! ≤ (-r_lo)^k/k! since -r_lo ≥ -r ≥ 0
          have hnr_le_nrlo : -r ≤ ((-r_lo : ℚ) : ℝ) := by push_cast; linarith
          -- Step 3: S_{N+1}(-r) ≤ taylorExpQ(-r_lo, N) [cast form]
          have hS_mono : ∑ m ∈ Finset.range (N + 1), (-r) ^ m / (m.factorial : ℝ) ≤
              (taylorExpQ (-r_lo) N : ℝ) := by
            rw [taylorExpQ_cast_eq_sum]
            apply Finset.sum_le_sum; intro k _
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact pow_le_pow_left₀ hnr_pos.le hnr_le_nrlo _
          -- Step 4: Remainder (-r)^{N+1}*... ≤ taylorRemainder(-r_lo, N+1)
          have hR_mono : (-r) ^ (N + 1) * ((N + 1 : ℕ) + 1 : ℝ) /
              ((N + 1 : ℕ).factorial * ((N + 1 : ℕ) : ℝ)) ≤
              (taylorRemainder (-r_lo) (N + 1) : ℝ) := by
            rw [taylorRemainder_cast _ N hN_pos]
            apply div_le_div_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right
            · exact pow_le_pow_left₀ hnr_pos.le hnr_le_nrlo _
            · positivity
          -- Combine: exp(-r) ≤ S_N(-r) + R(-r) ≤ S_N(-r_lo) + R(-r_lo) [non-strict]
          have hle : Real.exp (-r) ≤
              (taylorExpQ (-r_lo) N : ℝ) + (taylorRemainder (-r_lo) (N + 1) : ℝ) := by
            linarith [hexp_bound]
          -- Strict: exp(-r) is irrational (= 2^k/exp(x), exp(x) irrational), S+R is rational
          have hirr_neg_r : Irrational (Real.exp (-r)) := by
            rw [Real.exp_neg]; apply irrational_inv_iff.mpr
            -- exp(r) = exp(x) / 2^k, so irrational
            have hirr := irrational_exp_rat x hx
            have harg : Real.exp (x : ℝ) = (2 : ℝ) ^ k * Real.exp r := exp_arg_red _ k
            rw [show Real.exp r = Real.exp (x : ℝ) / (2 : ℝ) ^ k from by
              field_simp [ne_of_gt h2k]; linarith [harg]]
            rw [show Real.exp (x : ℝ) / (2 : ℝ) ^ k =
                Real.exp (x : ℝ) * ((2 : ℝ) ^ k)⁻¹ from div_eq_mul_inv _ _]
            have h2k_ne : ((2:ℚ)^k : ℚ) ≠ 0 := zpow_ne_zero k (by norm_num)
            rw [show ((2 : ℝ) ^ k)⁻¹ = ((((2:ℚ)^k)⁻¹ : ℚ) : ℝ) from by push_cast; rfl]
            exact hirr.mul_ratCast (inv_ne_zero h2k_ne)
          have hne : (taylorExpQ (-r_lo) N : ℝ) + (taylorRemainder (-r_lo) (N + 1) : ℝ) ≠
              Real.exp (-r) := by
            intro heq
            exact hirr_neg_r ⟨taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1),
              by push_cast at heq ⊢; linarith⟩
          calc ((taylorExpQ (-r_lo) N : ℝ) + (taylorRemainder (-r_lo) (N + 1) : ℝ))⁻¹
              < (Real.exp (-r))⁻¹ := by
                rw [inv_lt_inv₀ hsum_pos (Real.exp_pos _)]
                exact lt_of_le_of_ne hle (Ne.symm hne)
            _ = Real.exp r := by rw [Real.exp_neg, inv_inv]
    ) h2k

theorem expBounds_exp_le_upper (x : ℚ) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    Real.exp (x : ℝ) ≤ ((expBounds x k iter).2 : ℝ) := by
  simp only [expBounds]
  set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
  set lo2 := ln2SeriesSum N_ln2
  set hi2 := lo2 + 1 / 2 ^ N_ln2
  set rp := expRIntervalWith x k lo2 hi2
  set r_hi := rp.2
  set N := expNumTerms + iter * 10
  have hbracket := expRIntervalWith_brackets x k lo2 hi2
    (ln2SeriesSum_le_log2 N_ln2)
    (by have := log2_le_ln2SeriesSum_add N_ln2
        show Real.log 2 ≤ ((ln2SeriesSum N_ln2 + 1 / 2 ^ N_ln2 : ℚ) : ℝ)
        push_cast; linarith)
  set r := (x : ℝ) - ↑k * Real.log 2
  have hr_hi_le : r ≤ (r_hi : ℝ) := hbracket.2
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [exp_arg_red (x : ℝ) k]
  show (2 : ℝ) ^ k * Real.exp r ≤ ↑(expUpperBound r_hi N * (2 : ℚ) ^ k)
  push_cast
  rw [show (expUpperBound r_hi N : ℝ) * (2 : ℝ) ^ (k : ℤ) =
      ((2 : ℝ) ^ k) * (expUpperBound r_hi N : ℝ) from by ring]
  exact mul_le_mul_of_nonneg_left (by
    simp only [expUpperBound]; split
    · -- r_hi ≥ 0: exp(r) ≤ S_N(r_hi) + R(r_hi)
      case isTrue h =>
        have hN_pos : 0 < N := by show 0 < expNumTerms + iter * 10; unfold expNumTerms; omega
        have hr_lt_1 : r < 1 := by have := hk_bound; rw [abs_lt] at this; linarith
        by_cases hr_hi_le1 : (r_hi : ℝ) ≤ 1
        · -- r_hi ≤ 1: direct from exp_le_taylor_upper
          calc Real.exp r ≤ Real.exp (r_hi : ℝ) := Real.exp_le_exp_of_le hr_hi_le
            _ ≤ _ := by exact_mod_cast exp_le_taylor_upper r_hi (by exact_mod_cast h) hr_hi_le1 N hN_pos
        · -- r_hi > 1: chain through 1
          push_neg at hr_hi_le1
          have h1_le_rhi : (1 : ℚ) ≤ r_hi := by exact_mod_cast hr_hi_le1.le
          -- S_N(1) + R(1) ≥ exp(1) ≥ exp(r)
          have h1R : (1 : ℝ) ≤ (r_hi : ℝ) := by exact_mod_cast h1_le_rhi
          have hS_mono : (taylorExpQ (1 : ℚ) N : ℝ) ≤ (taylorExpQ r_hi N : ℝ) := by
            rw [taylorExpQ_cast_eq_sum, taylorExpQ_cast_eq_sum]; push_cast
            apply Finset.sum_le_sum; intro m _
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact pow_le_pow_left₀ (by norm_num) h1R _
          have hR_mono : (taylorRemainder (1 : ℚ) (N + 1) : ℝ) ≤
              (taylorRemainder r_hi (N + 1) : ℝ) := by
            rw [taylorRemainder_cast _ N hN_pos, taylorRemainder_cast _ N hN_pos]; push_cast
            apply div_le_div_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact pow_le_pow_left₀ (by norm_num) h1R _
          calc Real.exp r ≤ Real.exp 1 := Real.exp_le_exp_of_le hr_lt_1.le
            _ ≤ (taylorExpQ (1 : ℚ) N : ℝ) + (taylorRemainder (1 : ℚ) (N + 1) : ℝ) := by
                exact_mod_cast exp_le_taylor_upper 1 (by norm_num) (by norm_num) N hN_pos
            _ ≤ (taylorExpQ r_hi N : ℝ) + (taylorRemainder r_hi (N + 1) : ℝ) := by linarith
            _ = ↑(taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)) := by push_cast; ring
    · -- r_hi < 0: exp(r) ≤ exp(r_hi) = 1/exp(-r_hi) ≤ 1/S_N(-r_hi)
      case isFalse h =>
        push_neg at h
        have habs : 0 ≤ -r_hi := by linarith
        push_cast [Rat.cast_div, Rat.cast_one, one_div]
        calc Real.exp r ≤ Real.exp (r_hi : ℝ) := Real.exp_le_exp_of_le hr_hi_le
          _ = (Real.exp ((-r_hi : ℚ) : ℝ))⁻¹ := by
              rw [show ((-r_hi : ℚ) : ℝ) = -((r_hi : ℚ) : ℝ) from by push_cast; ring,
                  Real.exp_neg, inv_inv]
          _ ≤ ((taylorExpQ (-r_hi) N : ℝ))⁻¹ := by
              have htpos : (0 : ℝ) < (taylorExpQ (-r_hi) N : ℝ) := by
                calc (0 : ℝ) < 1 := one_pos
                  _ ≤ (taylorExpQ (-r_hi) N : ℝ) := by
                    rw [taylorExpQ_cast_eq_sum]
                    calc (1:ℝ) = ∑ m ∈ Finset.range 1, ((-r_hi : ℚ) : ℝ) ^ m / (m.factorial : ℝ) := by simp
                      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
                        (Finset.range_mono (by omega)) (fun i _ _ => by positivity)
              exact inv_anti₀ htpos (by exact_mod_cast taylorExpQ_le_exp (-r_hi) habs N)
    ) (le_of_lt h2k)

/-- When `stickyTryOne (expBounds x k)` succeeds, the result brackets `exp(x)`. -/
theorem expBounds_stickyTryOne_sound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
    (r : StickyOut)
    (hr : stickyTryOne (expBounds x k) iter = some r)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    inStickyInterval (R := ℝ) r.q r.e_base (Real.exp (x : ℝ)) :=
  stickyTryOne_sound (expBounds x k) iter r (Real.exp (x : ℝ)) hr
    (expBounds_lower_lt_exp x hx k iter hk_bound)
    (expBounds_exp_le_upper x k iter hk_bound)
    (expBounds_lower_pos x k iter)


end ExpComputable
