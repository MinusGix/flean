import Flean.Operations.ExpComputableSound
import Flean.Operations.ExpTaylor
import Flean.Operations.StickyTermination
import Flean.NumberTheory.PadeExp
import Flean.NumberTheory.ExpEffectiveBound
import Flean.Linearize.Linearize
import Flean.BoundCalc.BoundCalc

/-! # Computable exp: width bounds and termination

Proves that the generic `stickyExtractLoop (expBounds x k)` terminates within
`expFuel x` steps (Thread 2 in the architecture overview).

The proof has three parts:
1. **Width bound** (`expBounds_width_bound`): the bracket `(upper - lower) · 2^s` is bounded
   by `C · (1/N! + 1/2^{N_ln2})`, which decreases super-exponentially in `iter`.
2. **Padé gap** (`pade_delta_log_bound`): using Padé approximants from `PadeExp.lean`,
   `exp(x) · 2^s` stays at least `δ > 0` away from every integer, with `1/δ ≤ 2^L`
   where `L ≤ 114 · ab · log₂(ab)`.
3. **Fuel sufficiency** (`expFuel_sufficient`): at a concrete iteration within `expFuel x`,
   the bracket width drops below `δ`, so `stickyTryOne (expBounds x k)` succeeds.
-/

section ExpComputable

variable [FloatFormat]

/-! ## Bracket width bound

The bracket `[lower, upper]` from `expBounds` shrinks as `iter` increases.
The width has two components:
1. **Taylor remainder**: `~1/N!` where `N = expNumTerms + iter * 10`
2. **ln2 error**: `~|k| / 2^{N_ln2}` where `N_ln2 = log2(k.natAbs) + 52 + iter * 50`

After scaling by `2^{k+s}`, the bracket width for `exp(x) · 2^s` is bounded by
a function that decreases super-exponentially in `iter`. -/

-- `int_log_le_nat_log2_diff` and `stickyShift_le_of_int_log` are in StickyTermination.lean

omit [FloatFormat] in
/-- `exp(2) < 8`, derived from `exp(1) < 2.7182818286`. -/
lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h1 := Real.exp_one_lt_d9
  calc Real.exp 2 = Real.exp (1 + 1) := by norm_num
    _ = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
    _ < 2.7182818286 * 2.7182818286 :=
        mul_lt_mul h1 h1.le (by positivity) (by positivity)
    _ < 8 := by norm_num

omit [FloatFormat] in
/-- The r-interval width from `expRIntervalWith` is `k.natAbs / 2^N_ln2 < 1`
when `N_ln2 ≥ Nat.log2(k.natAbs) + 1`. -/
lemma expRIntervalWith_width_lt_one (x : ℚ) (k : ℤ)
    (lo2 : ℚ) (N_ln2 : ℕ) (hN_ln2 : Nat.log2 k.natAbs + 1 ≤ N_ln2) :
    let hi2 := lo2 + 1 / 2 ^ N_ln2
    let rp := expRIntervalWith x k lo2 hi2
    ((rp.2 : ℚ) - rp.1 : ℚ) < 1 := by
  simp only
  -- k.natAbs < 2^N_ln2
  have hk_lt : (k.natAbs : ℚ) < 2 ^ N_ln2 := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k.natAbs
    rw [← Nat.log2_eq_log_two] at h1
    exact_mod_cast lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hN_ln2)
  simp only [expRIntervalWith]
  have h2N_pos : (0:ℚ) < 2 ^ N_ln2 := by positivity
  have hk_lt_cast : (k.natAbs : ℚ) / 2 ^ N_ln2 < 1 :=
    (div_lt_one h2N_pos).mpr hk_lt
  split
  · case isTrue hk =>
      dsimp only [Prod.snd, Prod.fst]
      have heq : x - ↑k * lo2 - (x - ↑k * (lo2 + 1 / 2 ^ N_ln2)) = ↑k / 2 ^ N_ln2 := by ring
      rw [heq]
      calc (↑k : ℚ) / 2 ^ N_ln2
          ≤ ↑k.natAbs / 2 ^ N_ln2 :=
            div_le_div_of_nonneg_right (Int.cast_le.mpr Int.le_natAbs) (le_of_lt h2N_pos)
        _ < 1 := (div_lt_one h2N_pos).mpr hk_lt
  · case isFalse hk =>
      push_neg at hk
      dsimp only [Prod.snd, Prod.fst]
      have heq : x - ↑k * (lo2 + 1 / 2 ^ N_ln2) - (x - ↑k * lo2) = -↑k / 2 ^ N_ln2 := by ring
      rw [heq]
      calc (-↑k : ℚ) / 2 ^ N_ln2
          ≤ ↑k.natAbs / 2 ^ N_ln2 :=
            div_le_div_of_nonneg_right (Int.cast_le.mpr (show (-k : ℤ) ≤ ↑k.natAbs by omega))
              (le_of_lt h2N_pos)
        _ < 1 := (div_lt_one h2N_pos).mpr hk_lt

/-- The lower bound from `expBounds` satisfies `Int.log 2 lower ≥ k - 5`.
In the `r_lo ≥ 0` case, `taylorExpQ_ge_one` gives `lower_r ≥ 1`, so `lower ≥ 2^k`.
In the `r_lo < 0` case, `lower_r = 1/denom` where
`denom ≤ 3·exp(-r_lo) < 3·exp(2) < 24 ≤ 32 = 2^5`, so `lower ≥ 2^(k-5)`. -/
theorem expBounds_int_log_ge (x : ℚ) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    k - 5 ≤ Int.log 2 ((expBounds x k iter).1 : ℚ) := by
  have hlower_pos := expBounds_lower_pos x k iter
  rw [← Int.zpow_le_iff_le_log (by norm_num : 1 < 2) hlower_pos]
  -- Goal: (2:ℚ)^(k-5) ≤ (expBounds x k iter).1
  simp only [expBounds]
  set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
  set lo2 := ln2SeriesSum N_ln2
  set hi2 := lo2 + 1 / 2 ^ N_ln2 with hhi2_def
  set rp := expRIntervalWith x k lo2 hi2
  set r_lo := rp.1
  set N := expNumTerms + iter * 10
  -- Factor 2^(k-5) = 2^(-5) * 2^k
  -- The goal is: (2:ℚ)^(k-5) ≤ lower_r * (2:ℚ)^k
  -- Suffices: (2:ℚ)^(-5) ≤ lower_r (then multiply both sides by 2^k)
  suffices h_lr : (2:ℚ)^(-5:ℤ) ≤
      if 0 ≤ r_lo then taylorExpQ r_lo N
      else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1)) by
    calc (2:ℚ) ^ (k - 5) = (2:ℚ) ^ (-5 : ℤ) * (2:ℚ) ^ k := by
            rw [show (k : ℤ) - 5 = -5 + k from by ring, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
      _ ≤ _ * (2:ℚ) ^ k := by
            bound_calc
  -- Goal: (2:ℚ)^(-5) ≤ lower_r
  split
  · -- Case r_lo ≥ 0: lower_r = taylorExpQ r_lo N ≥ 1 ≥ 1/32
    case isTrue h =>
      calc (2:ℚ) ^ (-5 : ℤ) ≤ 1 := by norm_num
        _ ≤ taylorExpQ r_lo N := taylorExpQ_ge_one _ h _
  · -- Case r_lo < 0: lower_r = 1/denom, need denom ≤ 32
    case isFalse h =>
      push_neg at h
      have habs : 0 ≤ -r_lo := by linarith
      set denom := taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1) with hdenom_def
      have hrem_nonneg : 0 ≤ taylorRemainder (-r_lo) (N + 1) := by
        unfold taylorRemainder
        simp only [show N + 1 ≠ 0 from by omega, ↓reduceIte]
        exact div_nonneg (mul_nonneg (pow_nonneg habs _) (by positivity)) (by positivity)
      have hty_ge := taylorExpQ_ge_one (-r_lo) habs N
      have hdenom_pos : 0 < denom := by linarith
      -- Suffices: denom ≤ 32
      rw [show (2:ℚ)^(-5:ℤ) = 1/32 from by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) hdenom_pos (show denom ≤ 32 from by
        suffices h_real : (denom : ℝ) < 32 from by exact_mod_cast le_of_lt h_real
        -- Get bracket
        have hlo2_le := ln2SeriesSum_le_log2 N_ln2
        have hhi2_ge : Real.log 2 ≤ ((hi2 : ℚ) : ℝ) := by
          have := log2_le_ln2SeriesSum_add N_ln2
          show Real.log 2 ≤ ((ln2SeriesSum N_ln2 + 1 / 2 ^ N_ln2 : ℚ) : ℝ)
          push_cast; linarith
        have hbracket := expRIntervalWith_brackets x k lo2 hi2 hlo2_le hhi2_ge
        simp only [] at hbracket
        set r := (x : ℝ) - ↑k * Real.log 2
        -- Width bound: rp.2 - rp.1 < 1
        have hwidth : rp.2 - rp.1 < 1 :=
          expRIntervalWith_width_lt_one x k lo2 N_ln2 (by omega)
        -- -r_lo < 2
        have h_neg_rlo : ((-r_lo : ℚ) : ℝ) < 2 := by
          have hr_bound := (abs_lt.mp hk_bound).1  -- -1 < r
          have hw_real : ((rp.2 - rp.1 : ℚ) : ℝ) < 1 := by exact_mod_cast hwidth
          push_cast at hw_real
          push_cast
          linarith [hbracket.1, hbracket.2]
        set y := ((-r_lo : ℚ) : ℝ) with hy_def
        have hy_nonneg : 0 ≤ y := by simp only [hy_def]; exact_mod_cast habs
        -- taylorExpQ ≤ exp
        have h_taylor := taylorExpQ_le_exp (-r_lo) habs N
        -- exp(-r_lo) < exp(2) < 8
        have h_exp : Real.exp y < 8 :=
          lt_trans (Real.exp_strictMono h_neg_rlo) exp_two_lt_eight
        -- y^(N+1)/(N+1)! ≤ exp(y)  (one term of Taylor series)
        have hN_pos : 0 < N := by simp only [N, expNumTerms]; omega
        have h_term : y ^ (N + 1) / ((N + 1).factorial : ℝ) ≤ Real.exp y := by
          have h1 : (taylorExpQ (-r_lo) (N+1) : ℝ) =
              (taylorExpQ (-r_lo) N : ℝ) + y ^ (N+1) / ((N+1).factorial : ℝ) := by
            rw [taylorExpQ_cast_eq_sum, taylorExpQ_cast_eq_sum,
              show N + 1 + 1 = (N + 1) + 1 from by omega, Finset.sum_range_succ]
          have h2 := taylorExpQ_le_exp (-r_lo) habs (N+1)
          have h3 : (0:ℝ) ≤ (taylorExpQ (-r_lo) N : ℝ) := by
            exact_mod_cast le_of_lt (lt_of_lt_of_le zero_lt_one hty_ge)
          linarith
        -- taylorRemainder ≤ 2 * exp(y)
        have h_rem : (taylorRemainder (-r_lo) (N + 1) : ℝ) ≤ 2 * Real.exp y := by
          rw [taylorRemainder_cast _ N hN_pos]
          have h_fac_pos : (0:ℝ) < ((N+1).factorial : ℝ) :=
            Nat.cast_pos.mpr (Nat.factorial_pos _)
          have h_np1_pos : (0:ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
          -- (N+2)/(N+1) ≤ 2
          have h_ratio : (↑(N + 1 : ℕ) : ℝ) + 1 ≤ 2 * (↑(N + 1 : ℕ) : ℝ) := by
            have : (1:ℝ) ≤ ↑(N + 1 : ℕ) := by exact_mod_cast (show 1 ≤ N + 1 by omega)
            linarith
          rw [div_le_iff₀ (mul_pos h_fac_pos h_np1_pos)]
          calc y ^ (N + 1) * ((↑(N + 1 : ℕ) : ℝ) + 1)
              ≤ y ^ (N + 1) * (2 * (↑(N + 1 : ℕ) : ℝ)) :=
                by bound_calc
            _ = (y ^ (N + 1) / ((N + 1).factorial : ℝ)) *
                (2 * ((N + 1).factorial : ℝ) * (↑(N + 1 : ℕ) : ℝ)) := by
                field_simp
            _ ≤ Real.exp y * (2 * ((N + 1).factorial : ℝ) * (↑(N + 1 : ℕ) : ℝ)) :=
                by bound_calc
            _ = 2 * Real.exp y * ((N + 1).factorial * (↑(N + 1 : ℕ) : ℝ)) := by ring
        -- Combine: denom ≤ 3*exp(y) < 24 ≤ 32
        calc (denom : ℝ) = (taylorExpQ (-r_lo) N : ℝ) +
              (taylorRemainder (-r_lo) (N + 1) : ℝ) := by push_cast [hdenom_def]; rfl
          _ ≤ Real.exp y + 2 * Real.exp y := by linarith [h_taylor]
          _ = 3 * Real.exp y := by ring
          _ < 3 * 8 := by linarith [h_exp]
          _ ≤ 32 := by norm_num)

/-- The shift `s = stickyShift(lower)` is uniformly bounded across all iterations.
Uses `expBounds_int_log_ge` to bound `Int.log 2 lower ≥ k - 5`, then
`stickyShift_le_of_int_log` gives `s ≤ prec + 4 - (k - 5) = prec + 9 - k ≤ prec + 9 + |k|`. -/
theorem stickyShift_bound (x : ℚ) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    stickyShift (expBounds x k iter).1 ≤ FloatFormat.prec.toNat + 9 + k.natAbs := by
  have hlower_pos := expBounds_lower_pos x k iter
  have hlog_ge := expBounds_int_log_ge x k iter hk_bound
  have hshift := stickyShift_le_of_int_log _ hlower_pos
  have : (FloatFormat.prec.toNat : ℤ) + 4 - Int.log 2 (expBounds x k iter).1 ≤
         FloatFormat.prec.toNat + 9 + k.natAbs := by
    have : Int.log 2 (expBounds x k iter).1 ≥ k - 5 := hlog_ge
    have : k ≤ k.natAbs := Int.le_natAbs
    omega
  exact le_trans hshift (Int.toNat_le_toNat this)

omit [FloatFormat] in
/-- `|k| ≤ 2·|x.num| + 1` when `|x - k·log 2| < 1`: triangle inequality + `log 2 > 1/2`. -/
theorem expArgRedK_natAbs_bound (x : ℚ) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    k.natAbs ≤ 2 * x.num.natAbs + 1 := by
  by_contra h; push_neg at h
  have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog2_pos : (0 : ℝ) < Real.log 2 := lt_trans (by norm_num) hlog2_gt
  have hx_abs : |(x : ℝ)| ≤ x.num.natAbs := rat_abs_le_natAbs x
  have hk_r : (k.natAbs : ℝ) ≥ 2 * ↑x.num.natAbs + 2 := by exact_mod_cast h
  have : (k.natAbs : ℝ) * Real.log 2 ≥ ↑x.num.natAbs + 1 := by
    calc (k.natAbs : ℝ) * Real.log 2
        ≥ (2 * ↑x.num.natAbs + 2) * Real.log 2 := by nlinarith
      _ ≥ (2 * ↑x.num.natAbs + 2) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hlog2_gt.le (by positivity)
      _ = ↑x.num.natAbs + 1 := by ring
  have : (k.natAbs : ℝ) * Real.log 2 < ↑x.num.natAbs + 1 := by
    have h1 : (k.natAbs : ℝ) * Real.log 2 = |↑k * Real.log 2| := by
      rw [abs_mul, abs_of_pos hlog2_pos, ← Int.cast_abs, Nat.cast_natAbs]
    rw [h1]
    calc |↑k * Real.log 2|
        = |↑x - (↑x - ↑k * Real.log 2)| := by rw [sub_sub_cancel]
      _ ≤ |↑x| + |↑x - ↑k * Real.log 2| := abs_sub _ _
      _ = |↑x - ↑k * Real.log 2| + |↑x| := add_comm _ _
      _ < 1 + ↑x.num.natAbs := add_lt_add_of_lt_of_le hk_bound hx_abs
      _ = ↑x.num.natAbs + 1 := by ring
  linarith

omit [FloatFormat] in
/-- The r-interval width from `expRIntervalWith` is at most `k.natAbs / 2^N_ln2` (in ℝ). -/
lemma expRIntervalWith_width_le (x : ℚ) (k : ℤ) (lo2 : ℚ) (N_ln2 : ℕ) :
    let hi2 := lo2 + 1 / 2 ^ N_ln2
    let rp := expRIntervalWith x k lo2 hi2
    ((rp.2 : ℝ) - (rp.1 : ℝ)) ≤ (k.natAbs : ℝ) / 2 ^ N_ln2 := by
  simp only [expRIntervalWith]
  have h2N_pos : (0:ℝ) < 2 ^ N_ln2 := by positivity
  split
  · case isTrue hk =>
      dsimp only [Prod.snd, Prod.fst]; push_cast
      have : (x : ℝ) - ↑k * (↑lo2 : ℝ) - ((x : ℝ) - ↑k * (↑lo2 + 1 / 2 ^ N_ln2)) =
          (k : ℝ) / 2 ^ N_ln2 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right (Int.cast_le.mpr Int.le_natAbs)
        (le_of_lt h2N_pos)
  · case isFalse hk =>
      push_neg at hk
      dsimp only [Prod.snd, Prod.fst]; push_cast
      have : (x : ℝ) - ↑k * (↑lo2 + 1 / 2 ^ N_ln2) - ((x : ℝ) - ↑k * (↑lo2 : ℝ)) =
          -(k : ℝ) / 2 ^ N_ln2 := by ring
      rw [this]
      have hle : -(k : ℝ) ≤ (k.natAbs : ℝ) := by
        have h : (-k : ℤ) ≤ k.natAbs := by omega
        calc -(k : ℝ) = ((-k : ℤ) : ℝ) := by push_cast; ring
          _ ≤ ((k.natAbs : ℤ) : ℝ) := Int.cast_le.mpr h
          _ = (k.natAbs : ℝ) := Int.cast_natCast k.natAbs
      exact div_le_div_of_nonneg_right hle (le_of_lt h2N_pos)

omit [FloatFormat] in
/-- R-level width bound: for the Taylor bracket around exp,
  `upper_r - lower_r ≤ 2^{N+2}·(N+2)/((N+1)!·(N+1)) + 8·(r_hi - r_lo)`. -/
lemma expBounds_r_width_le (r_lo r_hi : ℚ) (N : ℕ) (hN : 0 < N)
    (hr_lo_lt1 : (r_lo : ℝ) < 1) (hr_hi_gt_m1 : -(1 : ℝ) < (r_hi : ℝ))
    (hr_lo_gt_m2 : -(2 : ℝ) < (r_lo : ℝ)) (hr_hi_lt2 : (r_hi : ℝ) < 2)
    (hr_le : (r_lo : ℝ) ≤ (r_hi : ℝ)) :
    (expUpperBound r_hi N : ℝ) - (expLowerBound r_lo N : ℝ) ≤
    (2 : ℝ) ^ (N + 2) * (↑(N + 2) : ℝ) / (↑(N + 1).factorial * (↑(N + 1) : ℝ)) +
    8 * ((r_hi : ℝ) - (r_lo : ℝ)) := by
  simp only [expUpperBound, expLowerBound]
  -- Key facts
  have hexp_sub := exp_sub_le_mul_exp (r_lo : ℝ) (r_hi : ℝ)
  have hexp_hi_lt8 : Real.exp (r_hi : ℝ) < 8 :=
    lt_trans (Real.exp_strictMono hr_hi_lt2) exp_two_lt_eight
  have hDr_nn : 0 ≤ (r_hi : ℝ) - (r_lo : ℝ) := sub_nonneg.mpr hr_le
  -- B₁ = 2 * R(2)
  have hR2_eq : (taylorRemainder (2 : ℚ) (N + 1) : ℝ) =
      (2 : ℝ) ^ (N + 1) * (↑(N + 2) : ℝ) / (↑(N + 1).factorial * ↑(N + 1)) := by
    rw [taylorRemainder_cast 2 N hN]; push_cast; ring
  have hR2_nn : 0 ≤ (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by rw [hR2_eq]; positivity
  have hB1_eq : (2 : ℝ) ^ (N + 2) * (↑(N + 2) : ℝ) / (↑(N + 1).factorial * ↑(N + 1)) =
      2 * (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by rw [hR2_eq]; ring
  -- MVT bound: exp(r_hi) - exp(r_lo) ≤ 8 * Δr
  have hMVT : Real.exp (r_hi : ℝ) - Real.exp (r_lo : ℝ) ≤
      8 * ((r_hi : ℝ) - (r_lo : ℝ)) := by
    calc Real.exp (r_hi : ℝ) - Real.exp (r_lo : ℝ)
        ≤ Real.exp (r_hi : ℝ) * ((r_hi : ℝ) - (r_lo : ℝ)) := hexp_sub
      _ ≤ 8 * ((r_hi : ℝ) - (r_lo : ℝ)) :=
          by bound_calc
  -- Helper: for y ≥ 0, the reciprocal bound exp(−y) − 1/(S+R(y)) ≤ R(2)
  -- i.e., 1/(S_N(y) + R(y)) ≥ 1/exp(y) − R(2)
  have recip_bound : ∀ (y : ℚ), 0 ≤ y → (y : ℝ) < 2 →
      Real.exp (-(y : ℝ)) - 1 / ((taylorExpQ y N : ℝ) + (taylorRemainder y (N + 1) : ℝ)) ≤
      (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by
    intro y hy hy_lt2
    set D := (taylorExpQ y N : ℝ) + (taylorRemainder y (N + 1) : ℝ)
    have hD_ge1 : 1 ≤ D := by
      calc (1 : ℝ) ≤ (taylorExpQ y N : ℝ) := by exact_mod_cast taylorExpQ_ge_one y hy N
        _ ≤ D := le_add_of_nonneg_right (by
            unfold taylorRemainder; simp only [show N + 1 ≠ 0 from by omega, ↓reduceIte]
            exact_mod_cast div_nonneg (mul_nonneg (pow_nonneg hy _) (by positivity))
              (by positivity))
    have hD_pos : 0 < D := lt_of_lt_of_le one_pos hD_ge1
    have hS_le := taylorExpQ_le_exp y hy N
    have hR_le := taylorRemainder_le_of_le y 2 N hN hy (le_of_lt hy_lt2)
    -- D ≤ exp(y) + R(y) since S_N(y) ≤ exp(y)
    have hD_le : D ≤ Real.exp (y : ℝ) + (taylorRemainder y (N + 1) : ℝ) := by linarith
    -- D - exp(y) ≤ R(y) ≤ R(2)
    have hD_excess : D - Real.exp (y : ℝ) ≤ (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by
      linarith
    have hexp_pos := Real.exp_pos (y : ℝ)
    by_cases hle : D ≤ Real.exp (y : ℝ)
    · -- D ≤ exp(y): 1/D ≥ 1/exp(y) = exp(-y), so gap ≤ 0 ≤ R(2)
      have h1 : (Real.exp (y : ℝ))⁻¹ ≤ D⁻¹ := inv_anti₀ hD_pos hle
      rw [show (1 : ℝ) / D = D⁻¹ from one_div D]
      linarith [show Real.exp (-(y : ℝ)) = (Real.exp (y : ℝ))⁻¹ from Real.exp_neg _]
    · -- D > exp(y): algebraic bound
      push_neg at hle
      rw [show Real.exp (-(y : ℝ)) = (Real.exp (y : ℝ))⁻¹ from Real.exp_neg _,
          show (1 : ℝ) / D = D⁻¹ from one_div D,
          show (Real.exp (y : ℝ))⁻¹ - D⁻¹ =
            (D - Real.exp (y : ℝ)) / (D * Real.exp (y : ℝ)) from by field_simp]
      calc (D - Real.exp (y : ℝ)) / (D * Real.exp (y : ℝ))
          ≤ (taylorRemainder (2 : ℚ) (N + 1) : ℝ) / (D * Real.exp (y : ℝ)) :=
            div_le_div_of_nonneg_right hD_excess (by positivity)
        _ ≤ (taylorRemainder (2 : ℚ) (N + 1) : ℝ) / 1 :=
            div_le_div_of_nonneg_left hR2_nn one_pos
              (le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
                (mul_le_mul hD_ge1 (Real.one_le_exp (by exact_mod_cast hy)) zero_le_one
                  (le_trans zero_le_one hD_ge1)))
        _ = (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := div_one _
  -- Helper: for y ≥ 0 with y < 1, the reciprocal upper bound 1/S_N(y) - exp(-y) ≤ R(2)
  have recip_upper_bound : ∀ (y : ℚ), 0 ≤ y → (y : ℝ) < 1 →
      1 / (taylorExpQ y N : ℝ) - Real.exp (-(y : ℝ)) ≤
      (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by
    intro y hy hy_lt1
    have hS_ge1 := taylorExpQ_ge_one y hy N
    have hS_pos : (0 : ℝ) < (taylorExpQ y N : ℝ) :=
      by exact_mod_cast lt_of_lt_of_le one_pos hS_ge1
    have hS_le := taylorExpQ_le_exp y hy N
    have hexp_upper := exp_le_taylor_upper y hy (le_of_lt hy_lt1) N hN
    have hR := taylorRemainder_le_of_le y 2 N hN hy
      (le_of_lt (by linarith : (y : ℝ) < 2))
    have hexp_pos := Real.exp_pos (y : ℝ)
    have hR_nn : 0 ≤ (taylorRemainder y (N + 1) : ℝ) := by
      unfold taylorRemainder; simp only [show N + 1 ≠ 0 from by omega, ↓reduceIte]
      exact_mod_cast div_nonneg (mul_nonneg (pow_nonneg hy _) (by positivity)) (by positivity)
    rw [show Real.exp (-(y : ℝ)) = (Real.exp (y : ℝ))⁻¹ from Real.exp_neg _,
        one_div,
        show (taylorExpQ y N : ℝ)⁻¹ - (Real.exp (y : ℝ))⁻¹ =
          (Real.exp (y : ℝ) - (taylorExpQ y N : ℝ)) /
          ((taylorExpQ y N : ℝ) * Real.exp (y : ℝ)) from by field_simp]
    calc (Real.exp (y : ℝ) - (taylorExpQ y N : ℝ)) /
            ((taylorExpQ y N : ℝ) * Real.exp (y : ℝ))
        ≤ (taylorRemainder y (N + 1) : ℝ) /
            ((taylorExpQ y N : ℝ) * Real.exp (y : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [hexp_upper]
      _ ≤ (taylorRemainder y (N + 1) : ℝ) / 1 :=
          div_le_div_of_nonneg_left hR_nn one_pos (by
            calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
              _ ≤ (taylorExpQ y N : ℝ) * Real.exp (y : ℝ) :=
                mul_le_mul (by exact_mod_cast hS_ge1)
                  (Real.one_le_exp (by exact_mod_cast hy))
                  zero_le_one (by positivity))
      _ ≤ (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by rw [div_one]; exact hR
  -- Case split on signs using by_cases for predictable hypothesis names
  rw [hB1_eq]
  by_cases h_rhi : (0 : ℚ) ≤ r_hi <;> by_cases h_rlo : (0 : ℚ) ≤ r_lo <;>
    simp only [h_rhi, h_rlo, ↓reduceIte]
  · -- Case 1: 0 ≤ r_hi, 0 ≤ r_lo (both nonneg)
    push_cast
    have hS_hi := taylorExpQ_le_exp r_hi h_rhi N
    have hS_lo_upper := exp_le_taylor_upper r_lo h_rlo (le_of_lt hr_lo_lt1) N hN
    have hR_hi := taylorRemainder_le_of_le r_hi 2 N hN h_rhi (le_of_lt hr_hi_lt2)
    have hR_lo := taylorRemainder_le_of_le r_lo 2 N hN h_rlo
      (le_of_lt (lt_trans hr_lo_lt1 (by norm_num)))
    linarith
  · -- Case 2: 0 ≤ r_hi, r_lo < 0
    push_neg at h_rlo
    push_cast
    have habs : (0 : ℚ) ≤ -r_lo := by linarith
    have habs_lt2 : ((-r_lo : ℚ) : ℝ) < 2 := by push_cast; linarith
    have hS_hi := taylorExpQ_le_exp r_hi h_rhi N
    have hR_hi := taylorRemainder_le_of_le r_hi 2 N hN h_rhi (le_of_lt hr_hi_lt2)
    have h_lo := recip_bound (-r_lo) habs habs_lt2
    simp only [show -((-r_lo : ℚ) : ℝ) = (r_lo : ℝ) from by push_cast; ring] at h_lo
    -- h_lo: exp(r_lo) - 1/(S+R(-r_lo)) ≤ R(2), so -1/(S+R) ≤ R(2) - exp(r_lo)
    linarith
  · -- Vacuous: r_hi < 0 ≤ r_lo contradicts hr_le
    push_neg at h_rhi
    linarith [show (r_hi : ℝ) < 0 from by exact_mod_cast h_rhi,
              show (0 : ℝ) ≤ (r_lo : ℝ) from by exact_mod_cast h_rlo]
  · -- Case 3: r_lo < 0, r_hi < 0
    push_neg at h_rhi h_rlo
    push_cast
    have habs_lo : (0 : ℚ) ≤ -r_lo := by linarith
    have habs_hi : (0 : ℚ) ≤ -r_hi := by linarith
    have habs_lo_lt2 : ((-r_lo : ℚ) : ℝ) < 2 := by push_cast; linarith
    have habs_hi_lt1 : ((-r_hi : ℚ) : ℝ) < 1 := by push_cast; linarith
    -- Upper: 1/S_N(-r_hi) - exp(r_hi) ≤ R(2) via recip_upper_bound
    have h_up : 1 / (taylorExpQ (-r_hi) N : ℝ) - Real.exp (r_hi : ℝ) ≤
        (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by
      have := recip_upper_bound (-r_hi) habs_hi habs_hi_lt1
      simp only [show -((-r_hi : ℚ) : ℝ) = (r_hi : ℝ) from by push_cast; ring] at this
      exact this
    -- Lower bound from recip_bound
    have h_lo := recip_bound (-r_lo) habs_lo habs_lo_lt2
    simp only [show -((-r_lo : ℚ) : ℝ) = (r_lo : ℝ) from by push_cast; ring] at h_lo
    linarith

/-- Upper bound on the bracket width `(upper - lower)` at iteration `iter`.
The Taylor remainder contributes `≤ 2^(N+2)·(N+2)/((N+1)!·(N+1))` (using `|r| < 2`)
and the ln2 error contributes `≤ 8·(|k|+1)/2^{N_ln2}` to the width. -/
theorem expBounds_width_bound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    let (lower, upper) := expBounds x k iter
    let N := expNumTerms + iter * 10
    let N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
    ((upper : ℝ) - (lower : ℝ)) * 2 ^ (stickyShift lower) ≤
      (2 : ℝ) ^ (k.natAbs + stickyShift lower) *
        ((2 : ℝ) ^ (N + 2) * (N + 2 : ℝ) / ((N + 1).factorial * (N + 1)) +
         8 * (k.natAbs + 1 : ℝ) / 2 ^ N_ln2) := by
  -- Step 1: Rewrite the goal using expBounds pair structure
  set lower := (expBounds x k iter).1
  set upper := (expBounds x k iter).2
  -- Reduce the let-match to use .1 and .2
  rw [show expBounds x k iter = (lower, upper) from by ext <;> rfl]
  dsimp only; push_cast
  -- Step 2: Width nonneg from correctness
  have hlower_lt := expBounds_lower_lt_exp x hx k iter hk_bound
  have hupper_ge := expBounds_exp_le_upper x k iter hk_bound
  have hwidth_nn : 0 ≤ (upper : ℝ) - (lower : ℝ) := by
    rw [show (upper : ℝ) = ((expBounds x k iter).2 : ℝ) from rfl,
        show (lower : ℝ) = ((expBounds x k iter).1 : ℝ) from rfl]
    linarith
  -- Step 3: Factor the pair as (lr * 2^k, ur * 2^k) and use r-level bound
  -- The key: expBounds = (lr * 2^k, ur * 2^k) where lr, ur are the r-level bounds
  -- The r-level bound gives: ur - lr ≤ B
  -- Combined with 2^k ≤ 2^|k| and width ≥ 0, we get the result.
  set B := (2 : ℝ) ^ (expNumTerms + iter * 10 + 2) *
    (expNumTerms + iter * 10 + 2 : ℝ) /
    ((expNumTerms + iter * 10 + 1).factorial * (expNumTerms + iter * 10 + 1)) +
    8 * (↑k.natAbs + 1) / 2 ^ (Nat.log2 k.natAbs + 52 + iter * 50)
  have hB_nn : 0 ≤ B := by positivity
  -- The bound follows from:
  -- (upper - lower) ≤ 2^|k| * B  (then multiply both sides by 2^s)
  have h2s_pos : (0 : ℝ) < 2 ^ stickyShift lower := by positivity
  suffices h : (upper : ℝ) - (lower : ℝ) ≤ (2:ℝ) ^ k.natAbs * B by
    have h2s_nn := h2s_pos.le
    calc ((upper : ℝ) - lower) * 2 ^ stickyShift lower
        ≤ (2:ℝ) ^ k.natAbs * B * 2 ^ stickyShift lower :=
          by bound_calc
      _ = 2 ^ (k.natAbs + stickyShift lower) * B := by rw [pow_add]; ring
  -- Set up the r-level variables from expBounds definition
  set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50 with hN_ln2_def
  set lo2 := ln2SeriesSum N_ln2 with hlo2_def
  set hi2 := lo2 + 1 / 2 ^ N_ln2 with hhi2_def
  set rp := expRIntervalWith x k lo2 hi2 with hrp_def
  set r_lo := rp.1 with hr_lo_def
  set r_hi := rp.2 with hr_hi_def
  set N := expNumTerms + iter * 10 with hN_def
  set upper_r := expUpperBound r_hi N with hur_def
  set lower_r := expLowerBound r_lo N with hlr_def
  -- Factor: upper = upper_r * 2^k, lower = lower_r * 2^k
  have h_upper_eq : upper = upper_r * (2:ℚ) ^ k := by
    simp only [upper, upper_r, expBounds, hN_def]; ring
  have h_lower_eq : lower = lower_r * (2:ℚ) ^ k := by
    simp only [lower, lower_r, expBounds, hN_def]; ring
  -- upper - lower = (upper_r - lower_r) * 2^k
  have h_factor : (upper : ℝ) - (lower : ℝ) = ((upper_r : ℝ) - (lower_r : ℝ)) * (2:ℝ) ^ k := by
    rw [h_upper_eq, h_lower_eq]; push_cast; ring
  -- The r-level width bound
  have hN_pos : 0 < N := by simp only [N, expNumTerms]; omega
  -- Get bracket for r_lo, r_hi
  have hlo2_le := ln2SeriesSum_le_log2 N_ln2
  have hhi2_ge : Real.log 2 ≤ ((hi2 : ℚ) : ℝ) := by
    have := log2_le_ln2SeriesSum_add N_ln2
    show Real.log 2 ≤ ((ln2SeriesSum N_ln2 + 1 / 2 ^ N_ln2 : ℚ) : ℝ)
    push_cast; linarith
  have hbracket := expRIntervalWith_brackets x k lo2 hi2 hlo2_le hhi2_ge
  simp only [] at hbracket
  set r := (x : ℝ) - ↑k * Real.log 2
  have hr_bound := hk_bound
  rw [show |(x : ℝ) - ↑k * Real.log 2| = |r| from rfl] at hr_bound
  have hr_lo_le : (r_lo : ℝ) ≤ r := hbracket.1
  have hr_hi_ge : r ≤ (r_hi : ℝ) := hbracket.2
  -- Width bound on r-interval
  have hwidth : ((r_hi : ℝ) - (r_lo : ℝ)) < 1 := by
    have := expRIntervalWith_width_lt_one x k lo2 N_ln2 (by omega : Nat.log2 k.natAbs + 1 ≤ N_ln2)
    simp only [hr_hi_def, hr_lo_def, hrp_def, hhi2_def] at this ⊢; exact_mod_cast this
  have hr_le : (r_lo : ℝ) ≤ (r_hi : ℝ) := le_trans hr_lo_le hr_hi_ge
  -- Bounds on r_lo, r_hi from |r| < 1 and bracket
  have hr_lo_lt1 : (r_lo : ℝ) < 1 := by linarith [(abs_lt.mp hr_bound).2]
  have hr_hi_gt_m1 : -(1 : ℝ) < (r_hi : ℝ) := by linarith [(abs_lt.mp hr_bound).1]
  have hr_lo_gt_m2 : -(2 : ℝ) < (r_lo : ℝ) := by linarith [(abs_lt.mp hr_bound).1]
  have hr_hi_lt2 : (r_hi : ℝ) < 2 := by linarith [(abs_lt.mp hr_bound).2]
  -- Apply r-level width bound
  have hr_width' := expBounds_r_width_le r_lo r_hi N hN_pos
    hr_lo_lt1 hr_hi_gt_m1 hr_lo_gt_m2 hr_hi_lt2 hr_le
  -- Fold the if-then-else back into upper_r/lower_r
  have hr_width : (upper_r : ℝ) - (lower_r : ℝ) ≤
      (2:ℝ) ^ (N + 2) * (↑(N + 2) : ℝ) / (↑(N + 1).factorial * (↑(N + 1) : ℝ)) +
      8 * ((r_hi : ℝ) - (r_lo : ℝ)) := hr_width'
  -- Apply interval width bound: r_hi - r_lo ≤ |k| / 2^N_ln2
  have hinterval_width := expRIntervalWith_width_le x k lo2 N_ln2
  simp only [← hhi2_def, ← hrp_def, ← hr_hi_def, ← hr_lo_def] at hinterval_width
  -- Combine: upper_r - lower_r ≤ B_taylor + 8 * (|k|/2^N_ln2) ≤ B_taylor + 8*(|k|+1)/2^N_ln2
  have hDr_nn : 0 ≤ (r_hi : ℝ) - (r_lo : ℝ) := sub_nonneg.mpr hr_le
  have h2N_pos : (0:ℝ) < 2 ^ N_ln2 := by positivity
  -- 8 * (r_hi - r_lo) ≤ 8 * (|k| + 1) / 2^N_ln2
  have h8_bound : 8 * ((r_hi : ℝ) - (r_lo : ℝ)) ≤
      8 * (↑k.natAbs + 1) / 2 ^ N_ln2 := by
    have h1 : (k.natAbs : ℝ) ≤ ↑k.natAbs + 1 := le_add_of_nonneg_right one_pos.le
    have h2 : ((r_hi : ℝ) - (r_lo : ℝ)) ≤ (↑k.natAbs + 1) / 2 ^ N_ln2 :=
      le_trans hinterval_width (div_le_div_of_nonneg_right h1 h2N_pos.le)
    calc 8 * ((r_hi : ℝ) - (r_lo : ℝ))
        ≤ 8 * ((↑k.natAbs + 1) / 2 ^ N_ln2) := by bound_calc
      _ = 8 * (↑k.natAbs + 1) / 2 ^ N_ln2 := by ring
  -- So upper_r - lower_r ≤ B
  have hur_lr_le_B : (upper_r : ℝ) - (lower_r : ℝ) ≤ B := by
    calc (upper_r : ℝ) - (lower_r : ℝ) ≤
          (2:ℝ) ^ (N + 2) * (↑(N + 2) : ℝ) / (↑(N + 1).factorial * (↑(N + 1) : ℝ)) +
          8 * ((r_hi : ℝ) - (r_lo : ℝ)) := hr_width
      _ ≤ (2:ℝ) ^ (N + 2) * (↑(N + 2) : ℝ) / (↑(N + 1).factorial * (↑(N + 1) : ℝ)) +
          8 * (↑k.natAbs + 1) / 2 ^ N_ln2 := by linarith [h8_bound]
      _ = B := by
          simp only [B, N, N_ln2]; push_cast; ring
  -- Now: (upper - lower) = (ur - lr) * 2^k ≤ B * 2^k ≤ B * 2^|k|
  have h2k_pos : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hur_lr_nn : 0 ≤ (upper_r : ℝ) - (lower_r : ℝ) := by
    have h1 : 0 ≤ ((upper_r : ℝ) - (lower_r : ℝ)) * (2:ℝ) ^ k := by
      have := hwidth_nn; rw [h_factor] at this; exact this
    exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (2:ℝ) ^ k * ((upper_r : ℝ) - lower_r))
      h2k_pos
  rw [h_factor]
  calc ((upper_r : ℝ) - lower_r) * (2:ℝ) ^ k
      ≤ ((upper_r : ℝ) - lower_r) * (2:ℝ) ^ (k.natAbs : ℤ) := by
        bound_calc
    _ ≤ B * (2:ℝ) ^ (k.natAbs : ℤ) :=
        by bound_calc
    _ = (2:ℝ) ^ k.natAbs * B := by
        rw [show (2:ℝ) ^ (k.natAbs : ℤ) = (2:ℝ) ^ k.natAbs from zpow_natCast 2 k.natAbs]; ring

/-- The bracket width scaled by `2^s` eventually drops below any positive bound.
This follows from `expBounds_width_bound` and the fact that `1/(N+1)! → 0`
and `1/2^{N_ln2} → 0` as `iter → ∞`. -/
theorem expBounds_width_tendsto_zero (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) (eps : ℝ) (heps : 0 < eps) :
    ∃ iter₀ : ℕ, ∀ iter, iter₀ ≤ iter →
      let (lower, upper) := expBounds x k iter
      ((upper : ℝ) - (lower : ℝ)) * 2 ^ (stickyShift lower) < eps := by
  -- Step 1: The shift s = stickyShift(lower) is uniformly bounded by prec + 9 + |k|,
  -- because lower = lower_r · 2^k with lower_r ≥ 1/4, so log2(lower) ≥ k - 2.
  set S := FloatFormat.prec.toNat + 9 + k.natAbs
  have hS : ∀ iter, stickyShift (expBounds x k iter).1 ≤ S :=
    fun iter => stickyShift_bound x k iter hk_bound
  -- Step 2: The width bound from expBounds_width_bound gives
  -- width * 2^s ≤ 2^(|k|+s) * (err₁ + err₂)
  -- where err₁ = 2^(N+2)·(N+2)/((N+1)!·(N+1)) and err₂ = 8·(|k|+1)/2^N_ln2.
  -- Since s ≤ S, this is ≤ C * (err₁ + err₂) with C = 2^(|k|+S).
  set C := (2 : ℝ) ^ (k.natAbs + S)
  have hC_pos : 0 < C := by positivity
  -- Step 3: err₁ and err₂ each eventually drop below eps/(2C).
  -- err₁ ≤ 4·2^N/N! → 0 by tendsto_pow_div_factorial_atTop (2:ℝ).
  -- err₂ = const/2^N_ln2 → 0 by exponential growth.
  have h_err_small : ∃ iter₀, ∀ iter, iter₀ ≤ iter →
      let N := expNumTerms + iter * 10
      let N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
      C * ((2 : ℝ) ^ (N + 2) * (N + 2 : ℝ) / ((N + 1).factorial * (N + 1)) +
           8 * (k.natAbs + 1 : ℝ) / 2 ^ N_ln2) < eps := by
    have heps2C : 0 < eps / (2 * C) := div_pos heps (by positivity)
    -- 2^n / n! → 0
    have h_fac := FloorSemiring.tendsto_pow_div_factorial_atTop (2 : ℝ)
    have hA := h_fac.eventually (Iio_mem_nhds (show (0:ℝ) < eps / (8 * C) from
      div_pos heps (by positivity)))
    rw [Filter.eventually_atTop] at hA
    obtain ⟨M₁, hM₁⟩ := hA
    set A := 8 * (↑k.natAbs + 1 : ℝ)
    have hA_pos : 0 < A := by positivity
    have h_geom := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 from by norm_num) (show (1 : ℝ) / 2 < 1 from by norm_num)
    have hB := h_geom.eventually (Iio_mem_nhds (show (0:ℝ) < eps / (2 * C * A) from
      div_pos heps (by positivity)))
    rw [Filter.eventually_atTop] at hB
    obtain ⟨M₂, hM₂⟩ := hB
    refine ⟨M₁ + M₂ + 1, fun iter hiter => ?_⟩
    dsimp only
    have hN : M₁ ≤ expNumTerms + iter * 10 := by omega
    have hN_ln2 : M₂ ≤ Nat.log2 k.natAbs + 52 + iter * 50 := by omega
    set N := expNumTerms + iter * 10
    set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
    have hN_pos : 0 < N := by simp only [N, expNumTerms]; omega
    -- Bound term 1: 2^(N+2)·(N+2)/((N+1)!·(N+1)) ≤ 4·2^N/N! < eps/(2C)
    have h1' : (N + 2 : ℝ) / ((N + 1).factorial * (N + 1)) ≤ 1 / N.factorial := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (N+1).factorial * (N+1))
                           (by positivity : (0:ℝ) < N.factorial)]
      have hfact : (N + 1).factorial = (N + 1) * N.factorial := Nat.factorial_succ N
      push_cast [hfact]
      have hN_ge : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
      have hfact_pos : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
      have hkey : (↑N + 2 : ℝ) ≤ (↑N + 1) * (↑N + 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hkey hfact_pos.le]
    have h1 : (2 : ℝ) ^ (N + 2) * (N + 2 : ℝ) / ((N + 1).factorial * (N + 1)) ≤
        4 * (2 : ℝ) ^ N / N.factorial := by
      rw [show (2:ℝ)^(N+2) = 4 * (2:ℝ)^N from by ring,
          show 4 * (2:ℝ)^N * (↑N+2) / (↑(N+1).factorial * (↑N+1)) =
            4 * (2:ℝ)^N * ((↑N+2) / (↑(N+1).factorial * (↑N+1))) from by ring,
          show 4 * (2:ℝ)^N / ↑N.factorial = 4 * (2:ℝ)^N * (1 / ↑N.factorial) from by ring]
      exact by bound_calc
    have hfac_bound : (2:ℝ) ^ N / ↑N.factorial < eps / (8 * C) := hM₁ N hN
    have hlt1 : (2 : ℝ) ^ (N + 2) * (↑N + 2) / (↑(N + 1).factorial * (↑N + 1)) <
        eps / (2 * C) := by
      calc _ ≤ 4 * (2:ℝ) ^ N / ↑N.factorial := h1
        _ = 4 * ((2:ℝ) ^ N / ↑N.factorial) := by ring
        _ < 4 * (eps / (8 * C)) := by linarith [hfac_bound]
        _ = eps / (2 * C) := by ring
    have hgeom_bound := hM₂ N_ln2 hN_ln2
    -- Bound term 2: A/2^N_ln2 < eps/(2C) via geometric bound
    have h2 : A / 2 ^ N_ln2 < eps / (2 * C) := by
      rw [show A / 2 ^ N_ln2 = A * (1 / 2) ^ N_ln2 from by
        rw [one_div, inv_pow, div_eq_mul_inv]]
      calc A * (1 / 2) ^ N_ln2
          < A * (eps / (2 * C * A)) := by bound_calc
        _ = eps / (2 * C) := by field_simp
    -- Combine: C * (term1 + term2) < eps
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * C)] at hlt1 h2
    have key : 2 * (C * ((2 : ℝ) ^ (N + 2) * (↑N + 2 : ℝ) / (↑(N + 1).factorial * (↑N + 1)) +
        A / 2 ^ N_ln2)) =
      (2 : ℝ) ^ (N + 2) * (↑N + 2 : ℝ) / (↑(N + 1).factorial * (↑N + 1)) * (2 * C) +
      A / 2 ^ N_ln2 * (2 * C) := by ring
    linarith
  obtain ⟨iter₀, hiter₀⟩ := h_err_small
  -- Step 4: Combine
  refine ⟨iter₀, fun iter hiter => ?_⟩
  have hbound := expBounds_width_bound x hx k iter hk_bound
  -- Unfold the match in hbound
  set lower := (expBounds x k iter).1
  set upper := (expBounds x k iter).2
  have hbound' : ((upper : ℝ) - (lower : ℝ)) * 2 ^ stickyShift lower ≤
      (2 : ℝ) ^ (k.natAbs + stickyShift lower) *
        ((2 : ℝ) ^ (expNumTerms + iter * 10 + 2) *
          (expNumTerms + iter * 10 + 2 : ℝ) /
          ((expNumTerms + iter * 10 + 1).factorial * (expNumTerms + iter * 10 + 1)) +
         8 * (k.natAbs + 1 : ℝ) /
          2 ^ (Nat.log2 k.natAbs + 52 + iter * 50)) := by
    have := hbound
    rw [show expBounds x k iter = (lower, upper) from by ext <;> rfl] at this
    dsimp only at this; push_cast at this ⊢
    exact this
  have hS_iter : stickyShift lower ≤ S := hS iter
  have h2s_le : (2 : ℝ) ^ (k.natAbs + stickyShift lower) ≤ C := by linearize
  have herr := hiter₀ iter hiter
  dsimp only at herr; push_cast at herr
  -- width * 2^s ≤ 2^(|k|+s) * err ≤ C * err < eps
  have herr_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (expNumTerms + iter * 10 + 2) *
      (expNumTerms + iter * 10 + 2 : ℝ) /
      ((expNumTerms + iter * 10 + 1).factorial * (expNumTerms + iter * 10 + 1)) +
      8 * (k.natAbs + 1 : ℝ) /
      2 ^ (Nat.log2 k.natAbs + 52 + iter * 50) := by positivity
  calc ((upper : ℝ) - lower) * 2 ^ stickyShift lower
      ≤ (2 : ℝ) ^ (k.natAbs + stickyShift lower) * _ := hbound'
    _ ≤ C * _ := by bound_calc
    _ < eps := herr

/-- **Key lemma**: When the bracket width · 2^s is less than the distance from
`exp(x) · 2^s` to the nearest integer, `stickyTryOne (expBounds x k)` succeeds.
Specializes `stickyTryOne_of_tight_bracket` to `expBounds`. -/
theorem stickyTryOne_expBounds_of_tight_bracket (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1)
    (δ : ℝ)
    (hδ_gap : ∀ m : ℤ, |Real.exp (x : ℝ) * 2 ^ (stickyShift (expBounds x k iter).1) -
      (m : ℝ)| ≥ δ)
    (hwidth : let (lower, upper) := expBounds x k iter
      ((upper : ℝ) - (lower : ℝ)) * 2 ^ (stickyShift lower) < δ) :
    (stickyTryOne (expBounds x k) iter).isSome = true := by
  apply stickyTryOne_of_tight_bracket (expBounds x k) iter (Real.exp (x : ℝ))
    (expBounds_lower_pos x k iter)
    (expBounds_lower_lt_exp x hx k iter hk_bound)
    (expBounds_exp_le_upper x k iter hk_bound)
    δ hδ_gap
  have := hwidth
  rw [show expBounds x k iter = ((expBounds x k iter).1, (expBounds x k iter).2)
    from by ext <;> rfl] at this
  exact this

-- `two_pow_mul_half_pow` and `err1_factorial_bound` are in StickyTermination.lean

omit [FloatFormat] in
/-- **Fuel sufficiency**: within `expFuel x` iterations, `stickyTryOne (expBounds x k)` succeeds.
This is the quantitative core combining all three ingredients:
1. Effective δ from `pade_effective_delta` for the shift `s` at each iteration
2. Bracket width bound from `expBounds_width_bound`
3. Floor agreement from `stickyTryOne_expBounds_of_tight_bracket`

The proof shows the factorial decay of the bracket width dominates the
Padé effective δ bound within the quadratic fuel budget. -/
lemma pade_delta_log_bound (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0) (s : ℕ)
    (ab : ℕ) (hab : a.natAbs ^ 2 / b + a.natAbs + b + 100 ≤ ab) (hs : s ≤ ab) :
    let N₀ := padeConvergenceN₀ a b s
    let D := max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ ((a : ℝ) / b)|)
                 (((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) *
                   |padeP (N₀ + 1) ((a : ℝ) / b)|)
    ∃ L : ℕ, L ≤ 114 * ab * (Nat.log2 ab + 1) ∧ 2 * D ≤ (2 : ℝ) ^ L := by
  simp only
  set N₀ := padeConvergenceN₀ a b s
  set x := (a : ℝ) / (b : ℝ) with hx_def
  -- Basic bounds from hypotheses
  have hab_ge : 100 ≤ ab := by
    have : 0 ≤ a.natAbs ^ 2 / b := Nat.zero_le _; omega
  have ha_le : a.natAbs ≤ ab := by
    have : 0 ≤ a.natAbs ^ 2 / b := Nat.zero_le _; omega
  have hb_le : b ≤ ab := by
    have : 0 ≤ a.natAbs ^ 2 / b := Nat.zero_le _; omega
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb
  -- Step 1: Bound N₀ ≤ 27 * ab
  have hN₀_le : N₀ ≤ 27 * ab :=
    padeConvergenceN₀_le a b hb ha s ab hab hs
  -- Step 2: Bound D using padeP_abs_le
  set N₁ := N₀ + 1
  -- D ≤ max(N₀! * (4b)^N₀ * exp(|x|), N₁! * (4b)^N₁ * exp(|x|))
  --    = N₁! * (4b)^N₁ * exp(|x|)  (N₁ term dominates)
  have hx_le : |x| ≤ a.natAbs := by
    rw [hx_def, abs_div, ← Int.cast_abs, Nat.cast_natAbs, abs_of_pos hb_r]
    exact le_trans (div_le_div_of_nonneg_left (by positivity) one_pos
      (by exact_mod_cast hb)) (by rw [div_one])
  -- Step 2: Bound D ≤ ab^(89*ab) using padeP_abs_le
  -- D ≤ N₁! * (4b)^N₁ * exp(natAbs)          [padeP_abs_le + monotonicity]
  --   ≤ (22ab)^(22ab) * (4ab)^(22ab) * 3^ab   [factorial_le_pow, N₁ ≤ 22ab, b ≤ ab]
  --   ≤ ab^(56ab) * ab^(56ab) * ab^ab           [28ab ≤ ab², 4ab ≤ ab², 3 ≤ ab]
  --   = ab^(113ab)
  have hD_pow : max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)
                     (N₁.factorial * (b : ℝ) ^ N₁ * |padeP N₁ x|) ≤
      (ab : ℝ) ^ (113 * ab) := by
    -- Both terms bounded by N₁! * (4b)^N₁ * exp(|x|) ≤ ab^(113*ab)
    have hx_abs_le : |x| ≤ (a.natAbs : ℝ) := by
      rw [hx_def, abs_div, ← Int.cast_abs, Nat.cast_natAbs, abs_of_pos hb_r]
      exact le_trans (div_le_div_of_nonneg_left (by positivity) one_pos
        (by exact_mod_cast hb)) (by rw [div_one])
    have hterm_le : ∀ N ≤ N₁, (N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x| ≤
        (ab : ℝ) ^ (113 * ab) := by
      intro N hN
      have hN_le : N ≤ 28 * ab := le_trans hN (by omega)
      have hab_r : (0 : ℝ) ≤ (ab : ℝ) := Nat.cast_nonneg _
      -- Handle N = 0 trivially
      rcases Nat.eq_zero_or_pos N with rfl | hN_pos
      · simp [Nat.factorial, padeP, padeCoeff]
        exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ ab by omega))
      -- Step A: N! * b^N * |P_N(x)| ≤ N! * (4b)^N * exp(|x|)
      have h1 : (N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x| ≤
          N.factorial * ((4 : ℝ) * b) ^ N * Real.exp |x| := by
        calc (N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x|
            ≤ N.factorial * (b : ℝ) ^ N * ((4 : ℝ) ^ N * Real.exp |x|) :=
              mul_le_mul_of_nonneg_left (padeP_abs_le N x) (by positivity)
          _ = N.factorial * ((4 : ℝ) * b) ^ N * Real.exp |x| := by
              rw [mul_pow]; ring
      -- Step B: N! ≤ (28*ab)^(28*ab)
      have h_fac : (N.factorial : ℝ) ≤ (ab : ℝ) ^ (56 * ab) := by
        have : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
        have : (N : ℝ) ^ N ≤ (N : ℝ) ^ (28 * ab) := by linearize (base := (N : ℝ))
        have : (N : ℝ) ^ (28 * ab) ≤ ((ab : ℝ) ^ 2) ^ (28 * ab) := by
          apply pow_le_pow_left₀ (Nat.cast_nonneg _)
          have : (N : ℝ) ≤ (28 * ab : ℝ) := by exact_mod_cast hN_le
          have : (28 : ℝ) * ab ≤ (ab : ℝ) ^ 2 := by
            have : (28 : ℝ) ≤ ab := by exact_mod_cast (show 28 ≤ ab by omega)
            nlinarith
          linarith
        calc (N.factorial : ℝ) ≤ (N : ℝ) ^ (28 * ab) := by linarith
          _ ≤ ((ab : ℝ) ^ 2) ^ (28 * ab) := ‹_›
          _ = (ab : ℝ) ^ (56 * ab) := by rw [← pow_mul]; ring_nf
      -- Step C: (4b)^N ≤ ab^(56*ab)
      have h_4b : ((4 : ℝ) * b) ^ N ≤ (ab : ℝ) ^ (56 * ab) := by
        have h4b_le : (4 : ℝ) * b ≤ (ab : ℝ) ^ 2 := by
          have : (4 : ℝ) ≤ ab := by exact_mod_cast (show 4 ≤ ab by omega)
          have : (b : ℝ) ≤ ab := by exact_mod_cast hb_le
          nlinarith
        calc ((4 : ℝ) * b) ^ N ≤ ((4 : ℝ) * b) ^ (28 * ab) := by
              linearize (base := (4 : ℝ) * b)
          _ ≤ ((ab : ℝ) ^ 2) ^ (28 * ab) :=
              pow_le_pow_left₀ (by positivity) h4b_le _
          _ = (ab : ℝ) ^ (56 * ab) := by rw [← pow_mul]; ring_nf
      -- Step D: exp(|x|) ≤ ab^ab
      have h_exp : Real.exp |x| ≤ (ab : ℝ) ^ ab := by
        have hexp1 : Real.exp 1 ≤ 3 :=
          le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
        have : |x| ≤ a.natAbs := hx_abs_le
        have hna_r : (a.natAbs : ℝ) ≤ ab := by exact_mod_cast ha_le
        calc Real.exp |x| ≤ Real.exp (a.natAbs : ℝ) :=
              Real.exp_le_exp_of_le (by linarith)
          _ = Real.exp ((a.natAbs : ℝ) * 1) := by ring_nf
          _ = (Real.exp 1) ^ a.natAbs := by rw [Real.exp_nat_mul]
          _ ≤ (3 : ℝ) ^ a.natAbs :=
              pow_le_pow_left₀ (Real.exp_pos _).le hexp1 _
          _ ≤ (ab : ℝ) ^ a.natAbs :=
              pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (show 3 ≤ ab by omega)) _
          _ ≤ (ab : ℝ) ^ ab := by linearize (base := (ab : ℝ))
      -- Final: ab^(56ab) * ab^(56ab) * ab^ab = ab^(113ab)
      calc (N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x|
          ≤ N.factorial * ((4 : ℝ) * b) ^ N * Real.exp |x| := h1
        _ ≤ (ab : ℝ) ^ (56 * ab) * (ab : ℝ) ^ (56 * ab) * (ab : ℝ) ^ ab := by
            apply mul_le_mul (mul_le_mul h_fac h_4b (by positivity) (by positivity))
              h_exp (by positivity) (by positivity)
        _ = (ab : ℝ) ^ (113 * ab) := by
            rw [← pow_add, ← pow_add]; ring_nf
    exact max_le (hterm_le N₀ (by omega)) (hterm_le N₁ le_rfl)
  -- Step 3: ab^(113*ab) ≤ 2^(113*ab*(log₂(ab)+1)) since ab ≤ 2^(log₂(ab)+1)
  have hpow_bound : (ab : ℝ) ^ (113 * ab) ≤ (2 : ℝ) ^ (113 * ab * (Nat.log2 ab + 1)) := by
    have hab_le_pow : (ab : ℝ) ≤ (2 : ℝ) ^ (Nat.log2 ab + 1) := by
      rw [Nat.log2_eq_log_two]
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ab).le
    calc (ab : ℝ) ^ (113 * ab)
        ≤ ((2 : ℝ) ^ (Nat.log2 ab + 1)) ^ (113 * ab) :=
          pow_le_pow_left₀ (by positivity) hab_le_pow _
      _ = (2 : ℝ) ^ ((Nat.log2 ab + 1) * (113 * ab)) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (113 * ab * (Nat.log2 ab + 1)) := by ring_nf
  -- Combine: 2*D ≤ 2·ab^(113ab) ≤ 2^(1 + 113·ab·log₂ab) ≤ 2^(114·ab·log₂ab)
  refine ⟨114 * ab * (Nat.log2 ab + 1), le_refl _, ?_⟩
  have hab_pos : (0 : ℝ) < ab := by exact_mod_cast (show 0 < ab by omega)
  calc 2 * max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)
               (N₁.factorial * (b : ℝ) ^ N₁ * |padeP N₁ x|)
      ≤ 2 * (ab : ℝ) ^ (113 * ab) := by linarith [hD_pow]
    _ ≤ 2 * (2 : ℝ) ^ (113 * ab * (Nat.log2 ab + 1)) := by linarith [hpow_bound]
    _ ≤ (2 : ℝ) ^ 1 * (2 : ℝ) ^ (113 * ab * (Nat.log2 ab + 1)) := by norm_num
    _ = (2 : ℝ) ^ (1 + 113 * ab * (Nat.log2 ab + 1)) := by rw [← pow_add]
    _ ≤ (2 : ℝ) ^ (114 * ab * (Nat.log2 ab + 1)) := by
        apply pow_le_pow_right₀ (by norm_num)
        -- 1 ≤ ab·(log₂ab+1) since ab ≥ 100, so 1 + 113·X ≤ 114·X
        have : 1 ≤ ab * (Nat.log2 ab + 1) :=
          le_trans (show 1 ≤ 100 * 1 by omega) (Nat.mul_le_mul hab_ge (by omega))
        nlinarith

omit [FloatFormat] in
/-- Pointwise effective irrationality gap for `exp(x) * 2^s`.
Packages `pade_effective_delta` + `pade_delta_log_bound` into a single statement
matching the shape expected by `uniform_gap_from_pointwise`. -/
private theorem exp_effective_gap (x : ℚ) (hx : x ≠ 0) (s : ℕ)
    (ab : ℕ) (hab : x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den + 100 ≤ ab)
    (hs : s ≤ ab) :
    ∃ δ > 0, ∃ L : ℕ, L ≤ 114 * ab * (Nat.log2 ab + 1) ∧
    (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧
    ∀ m : ℤ, |Real.exp (x : ℝ) * 2 ^ s - (m : ℝ)| ≥ δ := by
  have hnum_ne : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden_pos : 0 < x.den := x.den_pos
  have hx_eq : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := by
    push_cast [Rat.cast_def]; ring
  obtain ⟨hD, hgap⟩ := pade_effective_delta x.num x.den hden_pos hnum_ne s
  have ⟨L, hL_le, hLD⟩ := pade_delta_log_bound x.num x.den hden_pos hnum_ne s ab hab hs
  refine ⟨_, div_pos one_pos (mul_pos (by norm_num : (0:ℝ) < 2) hD),
         L, hL_le, ?_, fun m => ?_⟩
  · rw [one_div_one_div]; exact hLD
  · rw [hx_eq]; exact hgap m

/-- **Heart of the termination proof.**

Shows that `stickyTryOne (expBounds x k)` succeeds at some iteration within `expFuel x` steps.
The proof constructs a concrete iteration `iter₀` and shows:
1. The Padé gap `δ` (from `exp_effective_gap`) satisfies `1/δ ≤ 2^L` with `L ≤ 114·ab·log₂(ab)`.
2. At `iter₀ = (L + 3|k| + prec + 20) / 10`, the bracket width `< δ`.
3. `iter₀ < expFuel x` since `expFuel x = 15·ab·(log₂(ab)+1) + 200 > L/10`. -/
theorem expFuel_sufficient (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ∃ iter, iter < expFuel x ∧ (stickyTryOne (expBounds x k) iter).isSome = true := by
  -- Define ab early so the L bound can reference it in the induction.
  set ab := x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den +
    FloatFormat.prec.toNat + 100 with hab_def
  -- Define S (shift bound) concretely and prove it bounds stickyShift.
  have hS_bound : ∀ iter, stickyShift (expBounds x k iter).1 ≤
      FloatFormat.prec.toNat + 9 + k.natAbs := by
    intro iter
    have hlower_pos := expBounds_lower_pos x k iter
    have hlog_ge := expBounds_int_log_ge x k iter hk_bound
    have hshift := stickyShift_le_of_int_log _ hlower_pos
    have : (FloatFormat.prec.toNat : ℤ) + 4 - Int.log 2 (expBounds x k iter).1 ≤
           FloatFormat.prec.toNat + 9 + k.natAbs := by
      have : Int.log 2 (expBounds x k iter).1 ≥ k - 5 := hlog_ge
      have : k ≤ k.natAbs := Int.le_natAbs
      omega
    exact le_trans hshift (Int.toNat_le_toNat this)
  have hk_bound_nat := expArgRedK_natAbs_bound x k hk_bound
  have hSab : FloatFormat.prec.toNat + 9 + k.natAbs ≤ ab := by
    have hsq : 0 ≤ x.num.natAbs ^ 2 / x.den := Nat.zero_le _
    have hden1 : 1 ≤ x.den := x.den_pos
    -- k.natAbs ≤ 2*natAbs + 1 ≤ natAbs + (natAbs + 1) ≤ natAbs + den + natAbs^2/den + 91
    -- (since either natAbs + 1 ≤ den + 91, or natAbs ≥ den so natAbs^2/den ≥ natAbs)
    have : k.natAbs ≤ x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den + 91 := by
      rcases le_or_gt x.num.natAbs x.den with h | h
      · -- natAbs ≤ den, so natAbs + 1 ≤ den + 1 ≤ den + 91
        omega
      · -- natAbs > den, so natAbs^2/den ≥ natAbs
        have : x.num.natAbs ≤ x.num.natAbs ^ 2 / x.den := by
          rw [Nat.le_div_iff_mul_le x.den_pos]
          calc x.num.natAbs * x.den ≤ x.num.natAbs * x.num.natAbs := by bound_calc
            _ = x.num.natAbs ^ 2 := (sq x.num.natAbs).symm
        omega
    simp only [hab_def]; omega
  -- Steps 1+2: Uniform positive gap with bounded 1/δ.
  have ⟨δ, hδ_pos, L, hL_bound, hL_delta, hδ_gap⟩ :
      ∃ δ > 0, ∃ L : ℕ, L ≤ 114 * ab * (Nat.log2 ab + 1) ∧
      (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧
      ∀ iter, ∀ m : ℤ,
      |Real.exp (x : ℝ) * 2 ^ stickyShift (expBounds x k iter).1 - ↑m| ≥ δ := by
    have h := uniform_gap_from_pointwise ab (114 * ab * (Nat.log2 ab + 1))
      (fun s m => |Real.exp (x : ℝ) * 2 ^ s - (m : ℝ)|)
      (fun s hs => exp_effective_gap x hx s ab (by simp only [hab_def]; omega) hs)
    obtain ⟨δ, hδ, L, hL, hLd, hδ_all⟩ := h
    exact ⟨δ, hδ, L, hL, hLd, fun iter m =>
      hδ_all _ (le_trans (hS_bound iter) hSab) m⟩
  -- Step 3: Pick concrete iteration within fuel budget.
  set S := FloatFormat.prec.toNat + 9 + k.natAbs with hS_def
  have hS : ∀ iter, stickyShift (expBounds x k iter).1 ≤ S := hS_bound
  set iter := (L + 3 * k.natAbs + FloatFormat.prec.toNat + 20) / 10 with hiter_def
  have hiter_fuel : iter < expFuel x := by
    -- ab ≥ 100 and contains |k|, prec as summands
    have hab_ge : 100 ≤ ab := by
      have h1 : 0 ≤ x.num.natAbs ^ 2 / x.den := Nat.zero_le _
      have h2 : ab = x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den +
        FloatFormat.prec.toNat + 100 := rfl
      omega
    have hk_le : k.natAbs ≤ ab := by
      have hk_bound_nat := expArgRedK_natAbs_bound x k hk_bound
      -- 2*natAbs + 1 ≤ ab (three-way case split)
      have h_ab : ab = x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den +
        FloatFormat.prec.toNat + 100 := rfl
      rcases le_or_gt x.num.natAbs 100 with hle | hgt
      · -- natAbs ≤ 100: ab ≥ natAbs + den + 100 ≥ natAbs + 101 ≥ 2*natAbs + 1
        have : 0 ≤ x.num.natAbs ^ 2 / x.den := Nat.zero_le _
        omega
      · -- natAbs > 100
        rcases le_or_gt x.den x.num.natAbs with hdn | hdn
        · -- den ≤ natAbs: natAbs^2/den ≥ natAbs, so ab ≥ 2*natAbs + den + 100
          have hsq : x.num.natAbs ≤ x.num.natAbs ^ 2 / x.den := by
            rw [Nat.le_div_iff_mul_le x.den_pos]
            calc x.num.natAbs * x.den
                ≤ x.num.natAbs * x.num.natAbs := by bound_calc
              _ = x.num.natAbs ^ 2 := (sq x.num.natAbs).symm
          omega
        · -- den > natAbs > 100: ab ≥ natAbs + den + 100 > 2*natAbs + 100
          have : 0 ≤ x.num.natAbs ^ 2 / x.den := Nat.zero_le _
          omega
    have hprec_le : FloatFormat.prec.toNat ≤ ab := by
      have h1 : 0 ≤ x.num.natAbs ^ 2 / x.den := Nat.zero_le _
      have h2 : ab = x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den +
        FloatFormat.prec.toNat + 100 := rfl
      omega
    set fuel := expFuel x with hfuel_def
    have hfuel_eq : fuel = 15 * ab * (Nat.log2 ab + 1) + 200 := by
      simp only [hfuel_def, expFuel]; rfl
    -- Numerator ≤ 114·ab·X + 4·ab + 20, iter = numerator/10
    -- Need iter < 15·ab·X + 200
    have hnum : L + 3 * k.natAbs + FloatFormat.prec.toNat + 20 ≤
        114 * ab * (Nat.log2 ab + 1) + 4 * ab + 20 := by omega
    calc iter = (L + 3 * k.natAbs + FloatFormat.prec.toNat + 20) / 10 := rfl
      _ ≤ (114 * ab * (Nat.log2 ab + 1) + 4 * ab + 20) / 10 :=
          Nat.div_le_div_right hnum
      _ < fuel := by
          rw [hfuel_eq]
          -- (114·ab·X + 4·ab + 20)/10 < 15·ab·X + 200
          -- Upper-bound numerator: ≤ 120·ab·X (since 4·ab+20 ≤ 6·ab·X for X≥7,ab≥100)
          -- Then 120·ab·X/10 = 12·ab·X < 15·ab·X + 200.
          set X := Nat.log2 ab + 1
          have hX : 7 ≤ X := by
            have : 6 ≤ Nat.log2 ab :=
              (Nat.le_log2 (by omega : ab ≠ 0)).mpr (by omega : 2 ^ 6 ≤ ab)
            omega
          have habX_ge : 100 * 7 ≤ ab * X := by bound_calc
          have h_num_le : 114 * ab * X + 4 * ab + 20 ≤ 120 * (ab * X) := by
            have h114 : 114 * ab * X = 114 * (ab * X) := by ring
            have : 4 * ab + 20 ≤ 6 * (ab * X) := by
              calc 4 * ab + 20 ≤ 5 * ab := by omega
                _ ≤ 5 * (ab * X) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
                _ ≤ 6 * (ab * X) := by omega
            omega
          calc (114 * ab * X + 4 * ab + 20) / 10
              ≤ 120 * (ab * X) / 10 := Nat.div_le_div_right h_num_le
            _ = 12 * (ab * X) := by omega
            _ < 15 * (ab * X) + 200 := by omega
            _ = 15 * ab * X + 200 := by ring
  -- Step 4: Show width * 2^s < δ at this iteration.
  -- width * 2^s ≤ 2^{|k|+s} * (err₁ + err₂) by expBounds_width_bound
  -- where err₁ ≤ 4 * 2^N / N! and err₂ = 8*(|k|+1)/2^{N_ln2}
  have hwidth : let (lower, upper) := expBounds x k iter
      ((upper : ℝ) - (lower : ℝ)) * 2 ^ (stickyShift lower) < δ := by
    have hbound := expBounds_width_bound x hx k iter hk_bound
    set lower := (expBounds x k iter).1
    set upper := (expBounds x k iter).2
    set N := expNumTerms + iter * 10 with hN_def
    set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50 with hN_ln2_def
    have hbound' : ((upper : ℝ) - (lower : ℝ)) * 2 ^ stickyShift lower ≤
        (2 : ℝ) ^ (k.natAbs + stickyShift lower) *
          ((2 : ℝ) ^ (N + 2) * (N + 2 : ℝ) /
            ((N + 1).factorial * (N + 1 : ℝ)) +
           8 * (k.natAbs + 1 : ℝ) / 2 ^ N_ln2) := by
      have := hbound
      rw [show expBounds x k iter = (lower, upper) from by ext <;> rfl] at this
      dsimp only at this
      exact this
    have hS_iter : stickyShift lower ≤ S := hS iter
    -- 2^{|k|+s} ≤ 2^{|k|+S}
    set C := (2 : ℝ) ^ (k.natAbs + S) with hC_def
    have hC_pos : 0 < C := by positivity
    have h2s_le : (2 : ℝ) ^ (k.natAbs + stickyShift lower) ≤ C := by linearize
    -- Bound err₁: 2^{N+2}*(N+2)/((N+1)!*(N+1)) ≤ 4*2^N/N!
    -- Then 2^N/N! ≤ (2/3)*(1/2)^{N-4} by pow_div_factorial_effective with d=2
    have hN_ge : 4 ≤ N := by simp only [N, expNumTerms]; omega
    have hN_ge_L : N ≥ L + k.natAbs + S + 7 := by
      simp only [N, expNumTerms, iter, S]; omega
    -- Using pow_div_factorial_effective with d = 2
    have h_fac : (2 : ℝ) ^ N / ↑N.factorial ≤
        (2 : ℝ) ^ 4 / ↑(4 : ℕ).factorial * (1 / 2 : ℝ) ^ (N - 4) := by
      have : (2 : ℝ) ^ N / ↑N.factorial ≤
          (2 : ℝ) ^ (2 * 2) / ↑(2 * 2).factorial * (1 / 2 : ℝ) ^ (N - 2 * 2) :=
        pow_div_factorial_geometric_bound 2 (by norm_num) 2 (by norm_num) N (by omega)
      simpa using this
    -- 2^4/4! = 16/24 = 2/3
    have h_init : (2 : ℝ) ^ 4 / ↑(4 : ℕ).factorial = 2 / 3 := by norm_num [Nat.factorial]
    -- C * err₁ ≤ C * 4 * (2/3) * (1/2)^{N-4} < (1/2)^L
    -- because N-4 ≥ L + |k| + S + 3, so (1/2)^{N-4} ≤ (1/2)^{L+|k|+S+3}
    -- and C = 2^{|k|+S}, so C * 4 * (2/3) * (1/2)^{N-4} ≤ (8/3) * (1/2)^{L+3} < (1/2)^L
    -- Bound err₂: 8*(|k|+1)/2^{N_ln2} < (1/2)^L
    -- Need 2^{N_ln2} > 8*(|k|+1)*C*2^L = 8*(|k|+1)*2^{|k|+S+L}
    -- i.e., N_ln2 > L + |k| + S + 3 + log₂(|k|+1) ≤ L + 2|k| + S + 4
    have hN_ln2_ge : N_ln2 ≥ L + 2 * k.natAbs + S + 4 := by
      simp only [N_ln2, iter, S]; omega
    -- Combine: width * 2^s ≤ C * (err₁ + err₂) < δ
    -- We show each of C*err₁ and C*err₂ is small, then combine.
    -- The full proof is broken into separately-stated helper bounds to keep heartbeats low.
    -- Step A: δ ≥ 1/2^L (from hL_delta : 1/δ ≤ 2^L)
    have h2L_pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    have h_delta_lb : (1 : ℝ) / 2 ^ L ≤ δ := by
      have h1 : 1 ≤ δ * (2 : ℝ) ^ L := by
        calc (1 : ℝ) = (1 / δ) * δ := by rw [one_div, inv_mul_cancel₀ hδ_pos.ne']
          _ ≤ (2 : ℝ) ^ L * δ := by nlinarith
          _ = δ * (2 : ℝ) ^ L := mul_comm _ _
      exact (div_le_iff₀ h2L_pos).mpr h1
    -- Step B: C * err₁ ≤ 1/(3*2^L) and C * err₂ ≤ 1/(2*2^L)
    -- These bounds use h_fac, h_init, hN_ge_L, hN_ln2_ge, and hkp1_le.
    -- Proof sketched in comments above; full formal proof deferred.
    have h_total : C * ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)) +
        8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2) < δ := by
      -- Suffices: C*(err₁+err₂) < 1/2^L ≤ δ
      apply lt_of_lt_of_le _ h_delta_lb
      rw [mul_add]
      -- err₁ ≤ (8/3)*(1/2)^(N-4)
      have herr1 := err1_factorial_bound N hN_ge
      -- (1/2)^(N-4) ≤ (1/2)^(L+|k|+S+3)
      have hhalf : (1/2:ℝ)^(N-4) ≤ (1/2:ℝ)^(L+k.natAbs+S+3) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      -- |k|+1 ≤ 2^|k|
      have hkp1 : (↑k.natAbs + 1 : ℝ) ≤ (2:ℝ)^k.natAbs := by exact_mod_cast Nat.lt_two_pow_self
      -- Term 1: C * err₁ ≤ 1/(3*2^L)
      have ht1 : C * ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ))) ≤
          1 / (3 * (2:ℝ)^L) := by
        calc C * ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)))
            ≤ C * ((8/3:ℝ) * (1/2:ℝ)^(N-4)) := by bound_calc
          _ ≤ C * ((8/3:ℝ) * (1/2:ℝ)^(L+k.natAbs+S+3)) := by bound_calc
          _ = (8/3:ℝ) * ((2:ℝ)^(k.natAbs+S) * (1/2:ℝ)^(k.natAbs+S+(L+3))) := by
              rw [show L+k.natAbs+S+3 = k.natAbs+S+(L+3) from by omega]; ring
          _ = (8/3:ℝ) * (1/2:ℝ)^(L+3) := by rw [two_pow_mul_half_pow]
          _ = 1 / (3 * (2:ℝ)^L) := by
              rw [one_div_pow, show L+3 = 3+L from by omega, pow_add]; norm_num; ring
      -- Term 2: C * err₂ ≤ 1/(2*2^L)
      have ht2 : C * (8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2) ≤ 1 / (2 * (2:ℝ)^L) := by
        -- 2^(L+2|k|+S+4) ≤ 2^N_ln2
        have h2Nln2 : (2:ℝ)^(L+2*k.natAbs+S+4) ≤ (2:ℝ)^N_ln2 := by linearize
        calc C * (8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2)
            ≤ C * (8 * (↑k.natAbs + 1) / (2:ℝ)^(L+2*k.natAbs+S+4)) := by
              bound_calc
          _ = 8 * (↑k.natAbs + 1) * ((2:ℝ)^(k.natAbs+S) / (2:ℝ)^(L+2*k.natAbs+S+4)) := by ring
          _ = 8 * (↑k.natAbs + 1) / ((2:ℝ)^(k.natAbs+4) * (2:ℝ)^L) := by
              rw [show L+2*k.natAbs+S+4 = (k.natAbs+S)+(k.natAbs+4+L) from by omega, pow_add,
                  show k.natAbs+4+L = (k.natAbs+4)+L from by omega, pow_add]
              field_simp; ring
          _ = (↑k.natAbs + 1) / (2 * (2:ℝ)^k.natAbs * (2:ℝ)^L) := by
              rw [show k.natAbs+4 = 4+k.natAbs from by omega, pow_add]; norm_num; ring
          _ ≤ (2:ℝ)^k.natAbs / (2 * (2:ℝ)^k.natAbs * (2:ℝ)^L) := by
              apply div_le_div_of_nonneg_right hkp1 (by positivity)
          _ = 1 / (2 * (2:ℝ)^L) := by field_simp
      -- 1/(3*2^L) + 1/(2*2^L) = 5/(6*2^L) < 1/2^L
      calc C * ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ))) +
              C * (8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2)
          ≤ 1 / (3 * (2:ℝ)^L) + 1 / (2 * (2:ℝ)^L) := add_le_add ht1 ht2
        _ < 1 / (2:ℝ)^L := by
            have h6 : (0:ℝ) < 1 / (6 * (2:ℝ)^L) := by positivity
            linarith [show 1/(3*(2:ℝ)^L) + 1/(2*(2:ℝ)^L) + 1/(6*(2:ℝ)^L) = 1/(2:ℝ)^L from by
              field_simp; ring]
    -- Step C: Combine with hbound' and h2s_le
    calc ((upper : ℝ) - (lower : ℝ)) * 2 ^ stickyShift lower
        ≤ (2:ℝ)^(k.natAbs + stickyShift lower) *
          ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)) +
          8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2) := hbound'
      _ ≤ C * ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)) +
          8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2) :=
          by bound_calc
      _ < δ := h_total
  -- Step 5: At iter, the bracket is tight and the gap holds.
  have hsuccess : (stickyTryOne (expBounds x k) iter).isSome = true :=
    stickyTryOne_expBounds_of_tight_bracket x hx k iter hk_bound δ
      (hδ_gap iter) hwidth
  exact ⟨iter, hiter_fuel, hsuccess⟩

/-- **Fuel sufficiency**: the first successful iteration is within `expFuel x`.

The proof combines three ingredients:

1. **Effective irrationality measure** (from Padé, in `PadeExp.lean`):
   For nonzero rational `a/b` and shift `s`, there exists an explicit `δ > 0` such that
   `|exp(a/b) · 2^s - m| ≥ δ` for all integers `m`. The bound is
   `δ = 1/(2 · K)` where `K = N₀! · b^N₀ · P_{N₀}(a/b)` and `N₀` is the Padé convergence
   threshold (see `pade_effective_delta`).

2. **Bracket width bound**: At iteration `iter`, the bracket `[lower, upper]` from `expBounds`
   satisfies `(upper - lower) · 2^s ≤ W(iter)` where `W` decreases super-exponentially
   (dominated by `2^{k+s} / N_taylor!` for the Taylor remainder, plus `2^{k+s} · |k| / 2^{N_ln2}`
   for the ln2 error). See `expBounds_width_bound`.

3. **Floor agreement**: When `W(iter) < δ` and `lower < exp(x) ≤ upper`, the floors
   `⌊lower · 2^s⌋ = ⌊upper · 2^s⌋` agree (from `floor_eq_of_close`).

The Padé parameter `d = 4a²/b` requires `O(a²/b)` terms to converge, hence the quadratic
term in `expFuel`. The factorial growth `1/N!` of the bracket width easily dominates the
effective δ bound within `expFuel x` iterations. -/
theorem stickyTryOne_expBounds_terminates (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ∃ n, 0 ≤ n ∧ n < 0 + expFuel x ∧ (stickyTryOne (expBounds x k) n).isSome = true := by
  obtain ⟨iter, hiter_fuel, hsuccess⟩ := expFuel_sufficient x hx k hk_bound
  exact ⟨iter, by omega, by omega, hsuccess⟩


end ExpComputable
