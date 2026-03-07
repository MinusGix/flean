import Flean.Operations.LogComputableSound
import Flean.Operations.StickyTermination
import Flean.Operations.ExpTermination
import Flean.NumberTheory.PadeExp
import Flean.Linearize.Linearize
import Flean.BoundCalc.BoundCalc

/-! # Computable log: width bounds and termination

Proves that the generic `stickyExtractLoop (logBounds y k)` terminates within
`logFuel y` steps (Thread 2 in the architecture overview).

The proof structure mirrors `ExpTermination.lean`:
1. **Width bound** (`logBounds_width_bound`): the bracket width is bounded by
   `k / 2^{N_ln2} + t^{2N+1}/(2N+1)`, which decreases geometrically in `iter`.
2. **Irrationality gap**: `log(y) · 2^s` stays bounded away from all integers by some
   `δ > 0`, using the Padé effective delta via the exp–log inversion.
3. **Fuel sufficiency** (`logFuel_sufficient`): at some concrete `iter < logFuel y`,
   the width drops below `δ`.

The fuel bound `O(ab² · log ab)` is pessimistic — in practice, `t` is usually bounded
away from 1 and the loop terminates in a few iterations. A tighter fuel could be
achieved by using the atanh series, but the current Taylor-based approach is simpler
and the fuel is only a worst-case termination bound.
-/

section LogComputable

variable [FloatFormat]

/-! ## Helper: lower bound on log(y) for rationals -/

omit [FloatFormat] in
/-- For rational `y > 1`, `log(y) ≥ 1 / y.num.natAbs`.
Proof: `log(y) ≥ 1 - 1/y = (y-1)/y ≥ 1/y.num` since `y.num > y.den`. -/
theorem log_rat_lower_bound (y : ℚ) (hy1 : 1 < y) :
    (1 : ℝ) / y.num.natAbs ≤ Real.log (y : ℝ) := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast lt_trans one_pos hy1
  have hp_int : (0 : ℤ) < y.num := Rat.num_pos.mpr (lt_trans zero_lt_one hy1)
  have hp_nat : 0 < y.num.natAbs := Int.natAbs_pos.mpr (by omega)
  have hp_real : (0 : ℝ) < (y.num.natAbs : ℝ) := by exact_mod_cast hp_nat
  have hnum_cast : (y.num : ℝ) = (y.num.natAbs : ℝ) := by
    rw [show y.num = (y.num.natAbs : ℤ) from (Int.natAbs_of_nonneg (by omega)).symm]
    simp
  -- Step 1: log(y) ≥ 1 - 1/y
  have h_log_lb : 1 - 1 / (y : ℝ) ≤ Real.log (y : ℝ) := by
    have h := Real.add_one_le_exp (-Real.log (y : ℝ))
    rw [Real.exp_neg, Real.exp_log hy_pos, inv_eq_one_div] at h
    linarith
  -- Step 2: 1/p ≤ 1 - 1/y = (y-1)/y ≥ (p-d)/p ≥ 1/p
  have hpd := Rat.den_lt_num_of_one_lt y hy1
  suffices (1 : ℝ) / y.num.natAbs ≤ 1 - 1 / (y : ℝ) by linarith
  have hd_pos : (0 : ℝ) < y.den := by exact_mod_cast y.den_pos
  have hp2 : (y.den : ℝ) + 1 ≤ (y.num.natAbs : ℝ) := by
    have h1 : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg (by omega)
    have h2 : y.den + 1 ≤ y.num.natAbs := by omega
    exact_mod_cast h2
  have hy_eq : (y : ℝ) = (y.num.natAbs : ℝ) / (y.den : ℝ) := by
    rw [Rat.cast_def, hnum_cast]
  rw [hy_eq, one_div_div,
      show (1:ℝ) - (y.den : ℝ) / y.num.natAbs =
        ((y.num.natAbs : ℝ) - y.den) / y.num.natAbs from by field_simp]
  exact div_le_div_of_nonneg_right (by linarith) hp_real.le

/-! ## Shift bound

The shift `s = stickyShift(lower)` depends on `Int.log 2 lower`. For the log bracket,
we need a uniform bound on `s` across all iterations.

The key observation: the lower bracket value is always `> 0` (from `logBounds_lower_pos`)
and converges upward to `log(y)`. We show `lower ≥ 1/(4·y.num.natAbs)`, giving
`Int.log 2 lower ≥ -(2 + log₂(y.num.natAbs))` and thus `s ≤ prec + 6 + log₂(y.num.natAbs)`.
-/

/-- The log lower bracket is at least `1/(4·y.num.natAbs)` for all iterations.
For `k ≥ 1`: `lower ≥ k·ln2_lo ≥ ln2/2 > 1/4 ≥ 1/(4p)`.
For `k = 0`: `lower = logLowerBound (y-1) N ≥ (y-1)/2 ≥ 1/(2·y.den) ≥ 1/(2p)`. -/
private theorem logBounds_lower_ge (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) (iter : ℕ) :
    (1 : ℚ) / (4 * y.num.natAbs) ≤ (logBounds y (logArgRedK y) iter).1 := by
  set k := logArgRedK y with hk_def
  set t := logReducedArg y k with ht_def
  set N := logNumTerms + iter * 10
  set N_ln2 := Nat.log2 k + 52 + iter * 50
  have ht_nonneg : (0 : ℚ) ≤ t := ht_def ▸ logReducedArg_nonneg y hy
  have ht_lt_one : (t : ℝ) < 1 := ht_def ▸ hk_def ▸ logReducedArg_lt_one y hy
  have hp_int : (0 : ℤ) < y.num := Rat.num_pos.mpr (lt_trans zero_lt_one hy1)
  have hp_pos : 0 < y.num.natAbs := Int.natAbs_pos.mpr (by omega)
  simp only [logBounds]
  -- lower = k * ln2_lo + logLowerBound t N
  -- Case split on k
  by_cases hk0 : k = 0
  · -- k = 0: lower = logLowerBound t N ≥ t/2 ≥ 1/(2·y.den) ≥ 1/(4p)
    rw [hk0]; simp only [Nat.cast_zero, zero_mul, zero_add]
    have ht_pos : 0 < t := by
      rw [ht_def, hk_def]; exact logReducedArg_pos_of_k_zero y hy1 (hk_def ▸ hk0)
    -- logLowerBound t N ≥ logLowerBound t 1 ≥ t/2
    have hN_ge : 1 ≤ N := by simp [N, logNumTerms]; omega
    have hLB_mono : (logLowerBound t 1 : ℝ) ≤ (logLowerBound t N : ℝ) :=
      logLowerBound_mono t ht_nonneg ht_lt_one.le 1 N hN_ge
    -- logLowerBound t 1 = taylorLogQ t 2 = t - t²/2
    have hLB1 : (logLowerBound t 1 : ℝ) = (t : ℝ) - (t : ℝ) ^ 2 / 2 := by
      unfold logLowerBound; rw [taylorLogQ_two_terms]; push_cast; ring
    -- t - t²/2 ≥ t/2 (since 0 ≤ t < 1 means t²/2 ≤ t/2)
    have ht_real : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_nonneg
    have hLB1_ge : (t : ℝ) / 2 ≤ (logLowerBound t 1 : ℝ) := by
      rw [hLB1]; nlinarith [sq_nonneg ((t : ℝ) - 1)]
    -- t ≥ 1/y.den (since t = y/2^0 - 1 = y - 1 ≥ 1/d)
    have ht_ge : (1 : ℝ) / y.den ≤ (t : ℝ) := by
      have ht_eq : t = y - 1 := by
        simp only [ht_def, hk0, logReducedArg, pow_zero, div_one]
      rw [ht_eq]; push_cast
      rw [Rat.cast_def, show (y.num : ℝ) / (y.den : ℝ) - 1 = ((y.num : ℝ) - y.den) / y.den from
        by field_simp]
      have hpd := Rat.den_lt_num_of_one_lt y hy1
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ (y.den : ℝ))
      have : (1 : ℤ) ≤ y.num - ↑y.den := by omega
      linarith [show (1 : ℝ) ≤ (y.num : ℝ) - (y.den : ℝ) from by exact_mod_cast this]
    -- y.den ≤ y.num.natAbs (since y > 1 means num > den)
    have hpd := Rat.den_lt_num_of_one_lt y hy1
    have hden_le : (y.den : ℝ) ≤ y.num.natAbs := by
      have h1 : y.den ≤ y.num.natAbs := by
        have := Int.natAbs_of_nonneg (show 0 ≤ y.num by omega)
        omega
      exact_mod_cast h1
    -- Chain: lower ≥ t/2 ≥ 1/(2d) ≥ 1/(2p) ≥ 1/(4p)
    -- Since k = 0, logReducedArg y 0 = t
    have ht_eq0 : logReducedArg y 0 = t := by
      show logReducedArg y 0 = logReducedArg y k
      congr 1; exact hk0.symm
    rw [ht_eq0]
    suffices h : (1 : ℚ) / (4 * ↑y.num.natAbs) ≤ logLowerBound t N by convert h
    have hp_real : (0 : ℝ) < (y.num.natAbs : ℝ) := by exact_mod_cast hp_pos
    have hd_real : (0 : ℝ) < (y.den : ℝ) := by exact_mod_cast y.den_pos
    -- Prove in ℝ then cast back
    have hR : (1 : ℝ) / (4 * y.num.natAbs) ≤ (logLowerBound t N : ℝ) :=
      calc (1 : ℝ) / (4 * y.num.natAbs)
          ≤ 1 / (2 * y.num.natAbs) := by
            apply div_le_div_of_nonneg_left one_pos.le (by positivity) (by linarith)
        _ ≤ 1 / (2 * y.den) := by
            apply div_le_div_of_nonneg_left one_pos.le (by positivity)
            linarith
        _ = (1 : ℝ) / y.den / 2 := by ring
        _ ≤ (t : ℝ) / 2 := div_le_div_of_nonneg_right ht_ge (by norm_num)
        _ ≤ (logLowerBound t 1 : ℝ) := hLB1_ge
        _ ≤ (logLowerBound t N : ℝ) := hLB_mono
    rwa [show (1 : ℝ) / (4 * ↑y.num.natAbs) = ((1 : ℚ) / (4 * ↑y.num.natAbs) : ℚ) from by
      push_cast; ring, Rat.cast_le] at hR
  · -- k ≥ 1: lower ≥ k * ln2_lo + 0 ≥ 1 * (1/2) = 1/2 ≥ 1/(4p)
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have hln2_half : (1 : ℚ) / 2 ≤ ln2SeriesSum N_ln2 :=
      ln2SeriesSum_ge_half N_ln2 (by simp [N_ln2]; omega)
    have hLB_nonneg : (0 : ℚ) ≤ logLowerBound t N :=
      Rat.cast_nonneg.mp (logLowerBound_nonneg t ht_nonneg ht_lt_one N)
    -- lower ≥ k * ln2_lo + logLowerBound ≥ 1 * (1/2) + 0 = 1/2
    have hlower_half : (1 : ℚ) / 2 ≤ ↑k * ln2SeriesSum N_ln2 + logLowerBound t N := by
      calc (1 : ℚ) / 2 ≤ 1 * (1 / 2) := by norm_num
        _ ≤ ↑k * ln2SeriesSum N_ln2 := by
            bound_calc
            exact_mod_cast hk_pos
        _ ≤ ↑k * ln2SeriesSum N_ln2 + logLowerBound t N := le_add_of_nonneg_right hLB_nonneg
    -- 1/(4p) ≤ 1/2 since p ≥ 1
    calc (1 : ℚ) / (4 * ↑y.num.natAbs)
        ≤ 1 / 2 := by
          apply div_le_div_of_nonneg_left one_pos.le (by norm_num) (by
            have : (1 : ℚ) ≤ y.num.natAbs := by exact_mod_cast hp_pos
            linarith)
      _ ≤ ↑k * ln2SeriesSum N_ln2 + logLowerBound t N := hlower_half

/-- The shift `stickyShift(lower)` is uniformly bounded across all iterations. -/
theorem logStickyShift_bound (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) (iter : ℕ) :
    stickyShift (logBounds y (logArgRedK y) iter).1 ≤
      FloatFormat.prec.toNat + 7 + Nat.log2 y.num.natAbs := by
  have hlower_pos : (0 : ℚ) < (logBounds y (logArgRedK y) iter).1 := by
    exact_mod_cast logBounds_lower_pos y hy hy1 iter
  have hlower_ge := logBounds_lower_ge y hy hy1 iter
  -- Int.log 2 lower ≥ -(3 + log2 p)
  -- because 2^{-(3+log2 p)} = 1/(8*2^(log2 p)) ≤ 1/(4p) ≤ lower
  -- (since p < 2^(log2 p + 1) = 2*2^(log2 p), so 4p < 8*2^(log2 p))
  have hlog_ge : -(3 + (Nat.log2 y.num.natAbs : ℤ)) ≤
      Int.log 2 (logBounds y (logArgRedK y) iter).1 := by
    rw [← Int.zpow_le_iff_le_log (by norm_num : 1 < 2) hlower_pos]
    have hp_pos : 0 < y.num.natAbs := Int.natAbs_pos.mpr (by
      have : (0 : ℤ) < y.num := Rat.num_pos.mpr (lt_trans zero_lt_one hy1); omega)
    -- 2^{-(3+log2 p)} ≤ 1/(4p) ≤ lower
    calc (2 : ℚ) ^ (-(3 + (Nat.log2 y.num.natAbs : ℤ))) =
          1 / (8 * (2 : ℚ) ^ Nat.log2 y.num.natAbs) := by
            rw [zpow_neg, show (3 + (Nat.log2 y.num.natAbs : ℤ)) =
              3 + ↑(Nat.log2 y.num.natAbs) from rfl,
              zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]; norm_num
      _ ≤ 1 / (4 * y.num.natAbs) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            -- Need: 4*p ≤ 8*2^(log2 p), i.e., p ≤ 2*2^(log2 p) = 2^(log2 p + 1)
            -- This holds since p < 2^(log2 p + 1) (from Nat.lt_pow_succ_log_self)
            have : y.num.natAbs < 2 ^ (Nat.log2 y.num.natAbs + 1) := by
              rw [Nat.log2_eq_log_two]
              exact Nat.lt_pow_succ_log_self (by norm_num) y.num.natAbs
            have : (y.num.natAbs : ℚ) ≤ 2 * (2 : ℚ) ^ Nat.log2 y.num.natAbs := by
              rw [show 2 * (2 : ℚ) ^ Nat.log2 y.num.natAbs =
                (2 : ℚ) ^ (Nat.log2 y.num.natAbs + 1) from by rw [pow_succ]; ring]
              exact_mod_cast Nat.le_of_lt_succ (by omega)
            linarith
      _ ≤ (logBounds y (logArgRedK y) iter).1 := hlower_ge
  have hshift := stickyShift_le_of_int_log _ hlower_pos
  have : (FloatFormat.prec.toNat : ℤ) + 4 -
      Int.log 2 (logBounds y (logArgRedK y) iter).1 ≤
      FloatFormat.prec.toNat + 7 + Nat.log2 y.num.natAbs := by omega
  exact le_trans hshift (Int.toNat_le_toNat this)

/-! ## Width bound -/

omit [FloatFormat] in
/-- The Taylor bracket width: `logUpperBound t N - logLowerBound t N = t^{2N+1}/(2N+1)`. -/
theorem logTaylor_width (t : ℚ) (N : ℕ) :
    (logUpperBound t N : ℝ) - (logLowerBound t N : ℝ) =
      (t : ℝ) ^ (2 * N + 1) / ((2 * N : ℝ) + 1) := by
  unfold logUpperBound logLowerBound
  rw [taylorLogQ_cast_eq_sum, taylorLogQ_cast_eq_sum,
      Finset.sum_range_succ]
  simp only [mul_div_assoc]
  have : (-1 : ℝ) ^ (2 * N) = 1 := by simp
  rw [this, one_mul]; push_cast; ring

/-- Width bound for logBounds: the bracket width is bounded by
`k / 2^N_ln2 + t^(2N+1) / (2N+1)` where `k = logArgRedK y`, `t = logReducedArg y k`,
`N = logNumTerms + iter * 10`, `N_ln2 = Nat.log2 k + 52 + iter * 50`. -/
theorem logBounds_width_bound (y : ℚ) (iter : ℕ) :
    let k := logArgRedK y
    let t := logReducedArg y k
    let N := logNumTerms + iter * 10
    let N_ln2 := Nat.log2 k + 52 + iter * 50
    ((logBounds y k iter).2 : ℝ) - ((logBounds y k iter).1 : ℝ) ≤
      (k : ℝ) / 2 ^ N_ln2 + (t : ℝ) ^ (2 * N + 1) / ((2 * N : ℝ) + 1) := by
  set k := logArgRedK y with hk_def
  set t := logReducedArg y k with ht_def
  set N := logNumTerms + iter * 10 with hN_def
  set N_ln2 := Nat.log2 k + 52 + iter * 50 with hN_ln2_def
  simp only [logBounds]
  push_cast
  have htaylor_width := logTaylor_width t N
  calc ((k : ℝ) * ((ln2SeriesSum N_ln2 : ℝ) + 1 / 2 ^ N_ln2) + (logUpperBound t N : ℝ)) -
        ((k : ℝ) * (ln2SeriesSum N_ln2 : ℝ) + (logLowerBound t N : ℝ))
      = (k : ℝ) * (1 / 2 ^ N_ln2) +
        ((logUpperBound t N : ℝ) - (logLowerBound t N : ℝ)) := by ring
    _ = (k : ℝ) / 2 ^ N_ln2 + (t : ℝ) ^ (2 * N + 1) / ((2 * N : ℝ) + 1) := by
        rw [htaylor_width]; ring
    _ ≤ _ := le_refl _

/-! ## Tight bracket implies success -/

/-- If the bracket is tighter than the irrationality gap, `stickyTryOne` succeeds. -/
theorem stickyTryOne_logBounds_of_tight_bracket (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y)
    (iter : ℕ) (δ : ℝ)
    (hδ_gap : ∀ m : ℤ, |Real.log (y : ℝ) *
      2 ^ (stickyShift (logBounds y (logArgRedK y) iter).1) - (m : ℝ)| ≥ δ)
    (hwidth : let bounds := logBounds y (logArgRedK y) iter
      ((bounds.2 : ℝ) - (bounds.1 : ℝ)) *
        2 ^ (stickyShift bounds.1) < δ) :
    (stickyTryOne (logBounds y (logArgRedK y)) iter).isSome = true := by
  apply stickyTryOne_of_tight_bracket (logBounds y (logArgRedK y)) iter
    (Real.log (y : ℝ))
    (by exact_mod_cast logBounds_lower_pos y hy hy1 iter)
    (logBounds_lower_lt_log y hy hy1 iter)
    (logBounds_log_le_upper y hy iter)
    δ hδ_gap
  have := hwidth
  rw [show logBounds y (logArgRedK y) iter =
    ((logBounds y (logArgRedK y) iter).1,
     (logBounds y (logArgRedK y) iter).2) from by ext <;> rfl] at this
  exact this

/-! ## Irrationality gap for log

For rational `y > 1` and natural `s`, `|log(y) · 2^s - m| ≥ δ > 0` for all integers `m`.
- m = 0: gap ≥ log(y) · 2^s ≥ 1/p (from `log_rat_lower_bound`)
- m ≠ 0: by MVT, `|log(y) - m/2^s| ≥ |y - exp(m/2^s)| / max(y, exp(m/2^s))`.
  The Padé bound gives `|exp(m/2^s) · y.den - y.num| ≥ 1/(2D)`, hence the gap.
-/

omit [FloatFormat] in
/-- For m = 0, the gap is just `log(y) · 2^s ≥ 1/p`. -/
private theorem log_gap_m_zero (y : ℚ) (hy1 : 1 < y) (s : ℕ) :
    |Real.log (y : ℝ) * 2 ^ s - (0 : ℝ)| ≥ (1 : ℝ) / y.num.natAbs := by
  simp only [sub_zero]
  rw [abs_of_pos (mul_pos (Real.log_pos (by exact_mod_cast hy1)) (by positivity))]
  calc Real.log (y : ℝ) * 2 ^ s ≥ Real.log (y : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
          (Real.log_pos (by exact_mod_cast hy1)).le
    _ = Real.log (y : ℝ) := mul_one _
    _ ≥ 1 / y.num.natAbs := log_rat_lower_bound y hy1

/-! ## Fuel sufficiency -/

omit [FloatFormat] in
/-- For m ≤ 0, the gap `|log(y)·2^s - m| ≥ 1/p` (log is positive). -/
private theorem log_gap_m_nonpos (y : ℚ) (hy1 : 1 < y) (s : ℕ) (m : ℤ) (hm : m ≤ 0) :
    |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| ≥ (1 : ℝ) / y.num.natAbs := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast lt_trans one_pos hy1
  have hlog_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy1)
  have h2s_pos : (0 : ℝ) < 2 ^ s := by positivity
  have hls_pos : 0 < Real.log (y : ℝ) * 2 ^ s := mul_pos hlog_pos h2s_pos
  have hm_nonpos : (m : ℝ) ≤ 0 := by exact_mod_cast hm
  rw [abs_of_pos (by linarith)]
  calc Real.log (y : ℝ) * 2 ^ s - (m : ℝ) ≥ Real.log (y : ℝ) * 2 ^ s := by linarith
    _ ≥ Real.log (y : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hlog_pos.le
    _ = Real.log (y : ℝ) := mul_one _
    _ ≥ 1 / y.num.natAbs := log_rat_lower_bound y hy1

omit [FloatFormat] in
/-- Bound on close m: if |log(y)·2^s - m| < 1, then m ≤ p·2^s + 1. -/
private theorem log_close_m_bound (y : ℚ) (hy1 : 1 < y) (s : ℕ) (m : ℕ)
    (hclose : |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| < 1) :
    m ≤ y.num.natAbs * 2 ^ s + 1 := by
  -- log(y) < y ≤ p, so log(y)·2^s < p·2^s, and m < log(y)·2^s + 1 < p·2^s + 1
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast lt_trans one_pos hy1
  have hp_int : (0 : ℤ) < y.num := Rat.num_pos.mpr (lt_trans zero_lt_one hy1)
  have hnum_eq : y.num = (y.num.natAbs : ℤ) := (Int.natAbs_of_nonneg hp_int.le).symm
  have hy_le_p : (y : ℝ) ≤ (y.num.natAbs : ℝ) := by
    -- y = p/d ≤ p since d ≥ 1
    have hp_real : (y.num : ℝ) = (y.num.natAbs : ℝ) := by
      rw [hnum_eq]; simp
    rw [Rat.cast_def, hp_real]
    exact div_le_of_le_mul₀ (by positivity) (by positivity)
      (by exact_mod_cast Nat.le_mul_of_pos_right _ y.den_pos)
  have hlog_lt_p : Real.log (y : ℝ) < (y.num.natAbs : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hy_pos]
  have := (abs_sub_lt_iff.mp hclose).2
  have : (m : ℝ) < (y.num.natAbs : ℝ) * 2 ^ s + 1 := by
    linarith [mul_lt_mul_of_pos_right hlog_lt_p (show (0:ℝ) < 2 ^ s by positivity)]
  exact_mod_cast this.le

omit [FloatFormat] in
/-- MVT + Padé gap for m ≥ 1 close to log(y)·2^s.

For m ≥ 1 with |log(y)·2^s - m| < 1:
- MVT: |log(y) - m/2^s| ≥ |y - exp(m/2^s)| / max(y, exp(m/2^s))
- exp(m/2^s) < 3y (since m/2^s < log(y) + 1)
- Padé: |exp(m/2^s)·d - p| ≥ 1/(2D)
- Combined: |log(y)·2^s - m| ≥ 2^s / (6D·d·p) -/
private theorem log_gap_m_pos_close (y : ℚ) (hy1 : 1 < y) (s : ℕ) (m : ℤ)
    (hm_pos : 0 < m) (hclose : |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| < 1) :
    let t := Nat.log 2 y.den + 1
    let N₀ := padeConvergenceN₀ m (2 ^ s) t
    let x := (m : ℝ) / (2 : ℝ) ^ s
    let D := max ((N₀.factorial : ℝ) * ((2 : ℝ) ^ s) ^ N₀ * |padeP N₀ x|)
                 (((N₀ + 1).factorial : ℝ) * ((2 : ℝ) ^ s) ^ (N₀ + 1) *
                   |padeP (N₀ + 1) x|)
    |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| ≥
      (2 : ℝ) ^ s / (6 * D * y.den * y.num.natAbs) := by
  simp only
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast lt_trans one_pos hy1
  have hp_int : (0 : ℤ) < y.num := Rat.num_pos.mpr (lt_trans zero_lt_one hy1)
  have hp_pos : 0 < y.num.natAbs := Int.natAbs_pos.mpr (by omega)
  have hd_pos : 0 < y.den := y.den_pos
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hd_real : (0 : ℝ) < (y.den : ℝ) := by exact_mod_cast hd_pos
  have hnum_eq : y.num = (y.num.natAbs : ℤ) := (Int.natAbs_of_nonneg hp_int.le).symm
  set x := (m : ℝ) / (2 : ℝ) ^ s with hx_def
  -- Step 1: Padé bound: |exp(x)·d - n| ≥ 1/(2D) for all n
  have hm_ne : m ≠ 0 := by omega
  have h2s_nat_pos : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
  have ⟨hD_pos, hpade⟩ := pade_effective_delta_nat m (2 ^ s) h2s_nat_pos hm_ne y.den hd_pos
  -- Take n = y.num (cast through natAbs)
  set t := Nat.log 2 y.den + 1
  set N₀ := padeConvergenceN₀ m (2 ^ s) t
  set D := max ((N₀.factorial : ℝ) * ((2 : ℝ) ^ s) ^ N₀ * |padeP N₀ x|)
               (((N₀ + 1).factorial : ℝ) * ((2 : ℝ) ^ s) ^ (N₀ + 1) *
                 |padeP (N₀ + 1) x|)
  -- |exp(x)·d - y.num| ≥ 1/(2D) from Padé
  have h2s_cast : ((2 ^ s : ℕ) : ℝ) = (2 : ℝ) ^ s := by push_cast; ring
  have hpade_p := hpade y.num
  simp only [h2s_cast] at hpade_p
  -- Step 2: |y - exp(x)| ≥ 1/(2Dd)
  have hp_real : (0 : ℝ) < (y.num.natAbs : ℝ) := by exact_mod_cast hp_pos
  have hgap_y : |((y : ℝ)) - Real.exp x| ≥ 1 / (2 * D * y.den) := by
    -- y = y.num/y.den, so |y - exp(x)| = |y.num - exp(x)·d| / d
    rw [Rat.cast_def, ge_iff_le, ← div_div]
    have hsub : (y.num : ℝ) / (y.den : ℝ) - Real.exp x =
      ((y.num : ℝ) - Real.exp x * (y.den : ℝ)) / (y.den : ℝ) := by field_simp
    rw [hsub, abs_div, abs_of_pos hd_real]
    apply div_le_div_of_nonneg_right _ hd_real.le
    rw [abs_sub_comm]
    exact hpade_p
  -- Step 3: x < log(y) + 1 → exp(x) < 3y → max(y, exp(x)) ≤ 3p
  have hx_lt : x < Real.log (y : ℝ) + 1 := by
    rw [hx_def, div_lt_iff₀ h2s_pos]
    have h2s_ge : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith [(abs_sub_lt_iff.mp hclose).2]
  have hexp_lt : Real.exp x < 3 * (y : ℝ) := by
    calc Real.exp x < Real.exp (Real.log ↑↑y + 1) := Real.exp_strictMono hx_lt
      _ = ↑↑y * Real.exp 1 := by rw [Real.exp_add, Real.exp_log hy_pos]
      _ < ↑↑y * 3 := mul_lt_mul_of_pos_left (lt_trans Real.exp_one_lt_d9 (by norm_num)) hy_pos
      _ = 3 * ↑↑y := by ring
  have hnum_real : (y.num : ℝ) = (y.num.natAbs : ℝ) := by rw [hnum_eq]; simp
  have hy_le_p : (y : ℝ) ≤ (y.num.natAbs : ℝ) := by
    rw [Rat.cast_def, hnum_real]
    exact div_le_of_le_mul₀ (by positivity) (by positivity)
      (by exact_mod_cast Nat.le_mul_of_pos_right _ y.den_pos)
  have hmax_le : max ((y : ℝ)) (Real.exp x) ≤ 3 * (y.num.natAbs : ℝ) :=
    max_le (by linarith) (by linarith [hexp_lt])
  -- Step 4: MVT + combine
  have hmvt := Real.log_abs_sub_ge_div_max ((y : ℝ)) (Real.exp x) hy_pos (Real.exp_pos _)
  rw [Real.log_exp] at hmvt
  -- |log(y) - x| ≥ |y - exp(x)| / max(y, exp(x)) ≥ 1/(2Dd) / (3p) = 1/(6Ddp)
  have hlogx : |Real.log (y : ℝ) - x| ≥ 1 / (6 * D * y.den * y.num.natAbs) := by
    calc 1 / (6 * D * ↑y.den * ↑y.num.natAbs) = 1 / (2 * D * ↑y.den) / (3 * ↑y.num.natAbs) := by
          field_simp; ring
      _ ≤ |(y : ℝ) - Real.exp x| / (3 * ↑y.num.natAbs) :=
          div_le_div_of_nonneg_right hgap_y (by positivity)
      _ ≤ |(y : ℝ) - Real.exp x| / max (y : ℝ) (Real.exp x) :=
          div_le_div_of_nonneg_left (by positivity) (lt_max_of_lt_left hy_pos) hmax_le
      _ ≤ |Real.log (y : ℝ) - x| := hmvt
  -- |log(y)·2^s - m| = |log(y) - x| · 2^s ≥ 2^s/(6Ddp)
  rw [ge_iff_le]
  calc (2 : ℝ) ^ s / (6 * D * ↑y.den * ↑y.num.natAbs)
      = 1 / (6 * D * ↑y.den * ↑y.num.natAbs) * 2 ^ s := by ring
    _ ≤ |Real.log (y : ℝ) - x| * 2 ^ s := by bound_calc
    _ = |Real.log (y : ℝ) * 2 ^ s - ↑m| := by
        have heq : Real.log (y : ℝ) * 2 ^ s - ↑m = (Real.log (y : ℝ) - x) * 2 ^ s := by
          rw [hx_def]; field_simp
        rw [heq, abs_mul, abs_of_pos h2s_pos]

omit [FloatFormat] in
/-- ab_pade bound for close m: the Padé `ab` parameter is ≤ 2·ab²·2^ab. -/
private theorem log_ab_pade_bound (y : ℚ) (hy1 : 1 < y) (s : ℕ) (m : ℤ)
    (hm_pos : 0 < m) (hclose : |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| < 1)
    (ab : ℕ) (hab : y.num.natAbs ^ 2 / y.den + y.num.natAbs + y.den + 100 ≤ ab)
    (hs : s ≤ ab) :
    m.natAbs ^ 2 / 2 ^ s + m.natAbs + 2 ^ s + 100 ≤ 2 * ab ^ 2 * 2 ^ ab := by
  have hp_le : y.num.natAbs ≤ ab := by
    have : 0 ≤ y.num.natAbs ^ 2 / y.den := Nat.zero_le _; omega
  have hab_ge : 100 ≤ ab := by
    have : 0 ≤ y.num.natAbs ^ 2 / y.den := Nat.zero_le _; omega
  have h2s : 2 ^ s ≤ 2 ^ ab := Nat.pow_le_pow_right (by omega) hs
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  -- m.natAbs ≤ p·2^s + 1 ≤ (ab+1)·2^ab
  have hm_cast : (m.natAbs : ℝ) = (m : ℝ) := by
    have h : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (by omega)
    have : (m.natAbs : ℝ) = ((m.natAbs : ℤ) : ℝ) := by simp
    rw [this]; exact_mod_cast h
  have hm_nat_bound : m.natAbs ≤ y.num.natAbs * 2 ^ s + 1 :=
    log_close_m_bound y hy1 s m.natAbs (by rwa [hm_cast])
  have hm1 : m.natAbs ≤ (ab + 1) * 2 ^ ab := by
    have h1 : y.num.natAbs * 2 ^ s ≤ ab * 2 ^ ab :=
      le_trans (Nat.mul_le_mul_right _ hp_le) (Nat.mul_le_mul_left _ h2s)
    calc m.natAbs ≤ y.num.natAbs * 2 ^ s + 1 := hm_nat_bound
      _ ≤ ab * 2 ^ ab + 1 * 2 ^ ab := by omega
      _ = (ab + 1) * 2 ^ ab := by ring
  -- m.natAbs^2/2^s ≤ (ab+1)^2·2^s (using tighter bound m ≤ (p+1)·2^s)
  have hm_s : m.natAbs ≤ (ab + 1) * 2 ^ s := by
    calc m.natAbs ≤ y.num.natAbs * 2 ^ s + 1 * 2 ^ s := by linarith [hm_nat_bound, h2s_pos]
      _ ≤ ab * 2 ^ s + 1 * 2 ^ s := by linarith [Nat.mul_le_mul_right (2 ^ s) hp_le]
      _ = (ab + 1) * 2 ^ s := by ring
  have hm2 : m.natAbs ^ 2 / 2 ^ s ≤ (ab + 1) ^ 2 * 2 ^ ab := by
    calc m.natAbs ^ 2 / 2 ^ s
        ≤ ((ab + 1) * 2 ^ s) ^ 2 / 2 ^ s := Nat.div_le_div_right (Nat.pow_le_pow_left hm_s 2)
      _ = (ab + 1) ^ 2 * 2 ^ s := by
          rw [mul_pow, show (ab + 1) ^ 2 * (2 ^ s) ^ 2 =
            ((ab + 1) ^ 2 * 2 ^ s) * 2 ^ s from by ring]
          exact Nat.mul_div_cancel _ h2s_pos
      _ ≤ (ab + 1) ^ 2 * 2 ^ ab := by bound_calc
  -- Total ≤ (ab+1)^2·2^ab + (ab+1)·2^ab + 2^ab + 100
  --       = ((ab+1)^2 + ab + 2)·2^ab + 100
  -- (ab+1)^2 + ab + 2 = ab^2 + 3ab + 3 ≤ 2ab^2 - 1 for ab ≥ 100
  have h100_le : 100 ≤ 2 ^ ab :=
    le_trans (by norm_num : 100 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by omega) (by omega))
  have hcoeff : (ab + 1) ^ 2 + ab + 2 + 1 ≤ 2 * ab ^ 2 := by nlinarith
  -- ((ab+1)^2 + ab + 2)·2^ab + 100 ≤ (2ab^2 - 1)·2^ab + 2^ab = 2ab^2·2^ab
  calc m.natAbs ^ 2 / 2 ^ s + m.natAbs + 2 ^ s + 100
      ≤ (ab + 1) ^ 2 * 2 ^ ab + (ab + 1) * 2 ^ ab + 2 ^ ab + 100 := by
        linarith [hm2, hm1, h2s]
    _ = ((ab + 1) ^ 2 + ab + 2) * 2 ^ ab + 100 := by ring
    _ ≤ (2 * ab ^ 2 - 1) * 2 ^ ab + 2 ^ ab := by
        have h := Nat.mul_le_mul_right (2 ^ ab) (show (ab + 1) ^ 2 + ab + 2 ≤ 2 * ab ^ 2 - 1 from by omega)
        omega
    _ ≤ 2 * ab ^ 2 * 2 ^ ab := by
        -- (A-1)*B + B = A*B when A ≥ 1
        have hab2 : 1 ≤ 2 * ab ^ 2 := by nlinarith
        rw [show (2 * ab ^ 2 - 1) * 2 ^ ab + 2 ^ ab =
          (2 * ab ^ 2 - 1 + 1) * 2 ^ ab from by ring,
          Nat.sub_add_cancel hab2]

omit [FloatFormat] in
/-- For `ab ≥ 100`, `Nat.log2(2 * ab^2 * 2^ab) + 1 ≤ 2 * ab`. -/
private theorem log2_ab_pade_bound (ab : ℕ) (hab : 100 ≤ ab) :
    Nat.log2 (2 * ab ^ 2 * 2 ^ ab) + 1 ≤ 2 * ab := by
  -- 2*ab^2*2^ab < 2^ab * 2^ab = 2^(2*ab)
  -- so log2(...) < 2*ab, i.e., log2(...) + 1 ≤ 2*ab
  rw [Nat.log2_eq_log_two]
  have h_lt : 2 * ab ^ 2 * 2 ^ ab < 2 ^ (2 * ab) := by
    rw [show 2 ^ (2 * ab) = 2 ^ ab * 2 ^ ab from by rw [two_mul]; exact pow_add 2 ab ab]
    exact Nat.mul_lt_mul_of_pos_right (two_mul_sq_lt_two_pow ab hab) (Nat.two_pow_pos ab)
  -- Nat.log 2 x < k when x < 2^k
  have h_log : Nat.log 2 (2 * ab ^ 2 * 2 ^ ab) < 2 * ab :=
    Nat.log_lt_of_lt_pow' (by omega) h_lt
  omega

omit [FloatFormat] in
/-- Effective irrationality gap for `log(y)·2^s` with bounded `1/δ`.

For rational `y > 1`, shift `s ≤ ab`, produces `δ > 0` and `L` with:
- `∀ m, |log(y)·2^s - m| ≥ δ`
- `1/δ ≤ 2^L`
- `L ≤ 500 * ab³ * 2^ab` (crude but sufficient for exponential fuel)

Uses `log_gap_m_nonpos` for `m ≤ 0`, MVT + Padé for close `m ≥ 1`,
and trivial bounds for far `m`. -/
private theorem log_effective_gap (y : ℚ) (hy1 : 1 < y) (s : ℕ)
    (ab : ℕ) (hab : y.num.natAbs ^ 2 / y.den + y.num.natAbs + y.den + 100 ≤ ab)
    (hs : s ≤ ab) :
    ∃ δ > 0, ∃ L : ℕ, L ≤ 500 * ab ^ 3 * 2 ^ ab ∧
    (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧
    ∀ m : ℤ, |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| ≥ δ := by
  -- Setup
  have hp_pos : 0 < y.num.natAbs := Int.natAbs_pos.mpr (by
    have := Rat.num_pos.mpr (lt_trans zero_lt_one hy1); omega)
  have hd_pos : 0 < y.den := y.den_pos
  have hp_le : y.num.natAbs ≤ ab := by
    have : 0 ≤ y.num.natAbs ^ 2 / y.den := Nat.zero_le _; omega
  have hd_le : y.den ≤ ab := by
    have : 0 ≤ y.num.natAbs ^ 2 / y.den := Nat.zero_le _; omega
  have hab_ge : 100 ≤ ab := by
    have : 0 ≤ y.num.natAbs ^ 2 / y.den := Nat.zero_le _; omega
  -- Use δ = 1/2^L with L = 500*ab³*2^ab
  set L := 500 * ab ^ 3 * 2 ^ ab
  refine ⟨1 / (2 : ℝ) ^ L, by positivity, L, le_refl _, ?_, ?_⟩
  · rw [one_div_one_div]
  · -- ∀ m, gap ≥ 1/2^L
    intro m
    rcases le_or_gt m 0 with hm | hm
    · -- m ≤ 0: gap ≥ 1/p ≥ 1/2^ab ≥ 1/2^L
      have hp_le_2ab : (y.num.natAbs : ℝ) ≤ (2 : ℝ) ^ ab := by
        exact_mod_cast le_trans hp_le (Nat.lt_two_pow_self (n := ab)).le
      have h2ab_le_2L : (2 : ℝ) ^ ab ≤ (2 : ℝ) ^ L := by
        apply pow_le_pow_right₀ (by norm_num)
        -- ab ≤ 500*ab³*2^ab = L
        calc ab ≤ ab * 1 := by omega
          _ ≤ ab * (500 * ab ^ 2 * 2 ^ ab) := by
              apply Nat.mul_le_mul_left; nlinarith [Nat.one_le_two_pow (n := ab)]
          _ = 500 * ab ^ 3 * 2 ^ ab := by ring
      calc (1 : ℝ) / (2 : ℝ) ^ L
          ≤ 1 / (y.num.natAbs : ℝ) := by
            apply div_le_div_of_nonneg_left one_pos.le (by positivity) (le_trans hp_le_2ab h2ab_le_2L)
        _ ≤ |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| :=
            log_gap_m_nonpos y hy1 s m hm
    · -- m ≥ 1
      rcases lt_or_ge (|Real.log (y : ℝ) * 2 ^ s - (m : ℝ)|) 1 with hclose | hfar
      · -- close: use MVT + Padé
        have hm_pos : 0 < m := hm
        -- Padé setup: ab_pade = 2*ab²*2^ab
        set ab_pade := 2 * ab ^ 2 * 2 ^ ab
        have hab_pade_ge : 100 ≤ ab_pade := le_trans hab_ge (by
          calc ab ≤ ab * 1 := by omega
            _ ≤ ab * (2 * ab * 2 ^ ab) := by
                apply Nat.mul_le_mul_left; nlinarith [Nat.one_le_two_pow (n := ab)]
            _ = 2 * ab ^ 2 * 2 ^ ab := by ring)
        -- m satisfies Padé preconditions (from log_ab_pade_bound)
        have hab_pade_bound := log_ab_pade_bound y hy1 s m hm_pos hclose ab hab hs
        -- t = Nat.log 2 y.den + 1 ≤ ab_pade
        set t := Nat.log 2 y.den + 1
        have ht_le : t ≤ ab_pade := by
          have h1 : Nat.log 2 y.den < y.den :=
            Nat.log_lt_of_lt_pow' (by omega) Nat.lt_two_pow_self
          have h2 : y.den ≤ ab := hd_le
          have h3 : ab ≤ ab_pade := by
            calc ab ≤ ab * (2 * ab * 2 ^ ab) := by
                  nlinarith [Nat.one_le_two_pow (n := ab)]
              _ = 2 * ab ^ 2 * 2 ^ ab := by ring
          omega
        -- Get gap from log_gap_m_pos_close
        have hgap := log_gap_m_pos_close y hy1 s m hm_pos hclose
        simp only at hgap
        -- Apply pade_delta_log_bound to bound D
        have h2s_nat_pos : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
        have hm_ne : m ≠ 0 := by omega
        have ⟨L_pade, hL_pade_le, h2D_le⟩ :=
          pade_delta_log_bound m (2 ^ s) h2s_nat_pos hm_ne t ab_pade hab_pade_bound ht_le
        -- Bound L_pade ≤ 114 * ab_pade * (log₂(ab_pade) + 1)
        -- ≤ 114 * (2*ab²*2^ab) * (2*ab) = 456 * ab³ * 2^ab
        have hlog2_bound := log2_ab_pade_bound ab hab_ge
        have hL_pade_bound : L_pade ≤ 456 * ab ^ 3 * 2 ^ ab := by
          calc L_pade ≤ 114 * ab_pade * (Nat.log2 ab_pade + 1) := hL_pade_le
            _ ≤ 114 * (2 * ab ^ 2 * 2 ^ ab) * (2 * ab) := by
                apply Nat.mul_le_mul_left
                exact hlog2_bound
            _ = 456 * ab ^ 3 * 2 ^ ab := by ring
        -- D ≤ 2^(L_pade - 1), so 6D ≤ 3*2^L_pade ≤ 3*2^(456*ab³*2^ab)
        -- gap ≥ 2^s / (6*D*d*p)
        -- 1/gap ≤ 6*D*d*p/2^s ≤ 3*d*p*2^L_pade ≤ 3*ab²*2^(456*ab³*2^ab)
        -- Need: 3*ab²*2^(456*ab³*2^ab) ≤ 2^(500*ab³*2^ab) = 2^L
        -- i.e., 3*ab² ≤ 2^(44*ab³*2^ab), which holds for ab ≥ 100
        -- First: gap ≥ 2^s/(6Ddp) and 6D = 3*(2D) ≤ 3*2^L_pade
        set N₀ := padeConvergenceN₀ m (2 ^ s) t
        set x := (m : ℝ) / (2 : ℝ) ^ s
        set D := max ((N₀.factorial : ℝ) * ((2 : ℝ) ^ s) ^ N₀ * |padeP N₀ x|)
                     (((N₀ + 1).factorial : ℝ) * ((2 : ℝ) ^ s) ^ (N₀ + 1) *
                       |padeP (N₀ + 1) x|) with hD_def
        -- Connect pade_delta_log_bound's D with our D
        have h2s_cast : ((2 ^ s : ℕ) : ℝ) = (2 : ℝ) ^ s := by push_cast; ring
        -- pade_delta_log_bound uses (b : ℝ) = ((2^s : ℕ) : ℝ) and (a : ℝ)/b
        -- Our D uses (2 : ℝ)^s directly. They're equal by h2s_cast.
        -- Connect D with the Padé form by rewriting h2D_le
        have h2D_le' : 2 * D ≤ (2 : ℝ) ^ L_pade := by
          simp only [h2s_cast] at h2D_le; exact h2D_le
        have hD_pos : 0 < D := by
          have h := (pade_effective_delta_nat m (2 ^ s) h2s_nat_pos hm_ne y.den hd_pos).1
          simp only [h2s_cast] at h; exact h
        -- gap ≥ 2^s/(6Ddp)
        -- 1/gap ≤ 6Ddp/2^s = 3(2D)dp/2^s ≤ 3*2^L_pade*dp (since 1/2^s ≤ 1, wait: 2^s in numer)
        -- Actually gap = 2^s/(6Ddp), so 1/gap = 6Ddp/2^s.
        -- We need 1/(2^L) ≤ gap, i.e., 6Ddp/2^s ≤ 2^L.
        -- 6D = 3*(2D) ≤ 3*2^L_pade. dp ≤ ab². 1/2^s ≤ 1.
        -- So 6Ddp/2^s ≤ 3*ab²*2^L_pade.
        -- 3*ab² < 2^ab (from two_mul_sq_lt_two_pow + 3 < 2). Actually 3*ab² ≤ 2^ab for ab ≥ 100.
        -- So 3*ab²*2^L_pade ≤ 2^ab * 2^L_pade = 2^(ab + L_pade) ≤ 2^(ab + 456*ab³*2^ab) ≤ 2^(500*ab³*2^ab) = 2^L.
        rw [ge_iff_le] at hgap
        -- Show 1/2^L ≤ 2^s/(6Ddp) via bounding 6Ddp ≤ 2^s * 2^L
        have h6D : 6 * D ≤ 3 * (2 : ℝ) ^ L_pade := by linarith [h2D_le']
        have hdp_le : (y.den : ℝ) * (y.num.natAbs : ℝ) ≤ (ab : ℝ) ^ 2 := by
          have hd : (y.den : ℝ) ≤ (ab : ℝ) := by exact_mod_cast hd_le
          have hp : (y.num.natAbs : ℝ) ≤ (ab : ℝ) := by exact_mod_cast hp_le
          calc (y.den : ℝ) * (y.num.natAbs : ℝ) ≤ (ab : ℝ) * (ab : ℝ) :=
                mul_le_mul hd hp (by positivity) (by positivity)
            _ = (ab : ℝ) ^ 2 := by ring
        have h3ab2 : 3 * (ab : ℝ) ^ 2 ≤ (2 : ℝ) ^ ab := by
          -- 3*ab² ≤ ab³ (since 3 ≤ ab) < 2^ab
          have h1 : 3 * ab ^ 2 ≤ ab ^ 3 := by nlinarith
          have h2 : ab ^ 3 < 2 ^ ab := cube_lt_two_pow ab (by omega)
          exact_mod_cast le_of_lt (lt_of_le_of_lt h1 h2)
        have hL_pade_ab : ab + L_pade ≤ L := by
          have hab2_pos : 0 < ab ^ 2 := by positivity
          have h2ab_pos : 0 < 2 ^ ab := Nat.two_pow_pos ab
          calc ab + L_pade ≤ ab + 456 * ab ^ 3 * 2 ^ ab := by omega
            _ ≤ ab ^ 3 * 2 ^ ab + 456 * ab ^ 3 * 2 ^ ab := by
                apply Nat.add_le_add_right
                calc ab = ab * 1 * 1 := by ring
                  _ ≤ ab * ab ^ 2 * 2 ^ ab :=
                      by bound_calc
                  _ = ab ^ 3 * 2 ^ ab := by ring
            _ = 457 * ab ^ 3 * 2 ^ ab := by ring
            _ ≤ 500 * ab ^ 3 * 2 ^ ab := by
                bound_calc
        have h_inv_le : 6 * D * (y.den : ℝ) * (y.num.natAbs : ℝ) ≤ (2 : ℝ) ^ L := by
          calc 6 * D * (y.den : ℝ) * (y.num.natAbs : ℝ)
              = (6 * D) * ((y.den : ℝ) * (y.num.natAbs : ℝ)) := by ring
            _ ≤ (3 * (2 : ℝ) ^ L_pade) * (ab : ℝ) ^ 2 :=
                mul_le_mul h6D hdp_le (by positivity) (by positivity)
            _ = 3 * (ab : ℝ) ^ 2 * (2 : ℝ) ^ L_pade := by ring
            _ ≤ (2 : ℝ) ^ ab * (2 : ℝ) ^ L_pade := by bound_calc
            _ = (2 : ℝ) ^ (ab + L_pade) := by rw [← pow_add]
            _ ≤ (2 : ℝ) ^ L := by linearize
        -- 1/2^L ≤ 2^s/(6Ddp) ≤ gap
        rw [ge_iff_le]
        calc (1 : ℝ) / (2 : ℝ) ^ L
            ≤ 1 / (6 * D * (y.den : ℝ) * (y.num.natAbs : ℝ)) := by
              apply div_le_div_of_nonneg_left one_pos.le (by positivity) h_inv_le
          _ ≤ (2 : ℝ) ^ s / (6 * D * (y.den : ℝ) * (y.num.natAbs : ℝ)) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
          _ ≤ |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| := hgap
      · -- far: gap ≥ 1 ≥ 1/2^L
        calc (1 : ℝ) / (2 : ℝ) ^ L ≤ 1 := by
              rw [div_le_one (by positivity)]
              exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
          _ ≤ |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)| := hfar

/-! ## Reduced argument gap bound

The reduced argument `t = y/2^k - 1` satisfies `1 - t ≥ 1/p` where `p = y.num.natAbs`,
equivalently `t ≤ 1 - 1/p`. Since `p ≤ ab`, this gives `t ≤ 1 - 1/ab`, which feeds
into `geom_decay_bound` for the geometric convergence of the Taylor series. -/

omit [FloatFormat] in
/-- The reduced argument satisfies `1 - t ≥ 1/p` where `p = y.num.natAbs`. -/
private theorem logReducedArg_one_sub_ge (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) :
    (1 : ℝ) / y.num.natAbs ≤ 1 - (logReducedArg y (logArgRedK y) : ℝ) := by
  set k := logArgRedK y
  set p := y.num.natAbs with hp_def
  set d := y.den with hd_def
  have hp_int : (0 : ℤ) < y.num := Rat.num_pos.mpr (lt_trans zero_lt_one hy1)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast y.den_pos
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  -- Key ℕ bounds (from logArgRedK, via ℚ cross-multiplication)
  have hd_pos_q : (0 : ℚ) < y.den := by exact_mod_cast y.den_pos
  have hd2k_le : d * 2 ^ k ≤ p := by
    have h := logArgRedK_pow_le y hy  -- (2:ℚ)^k ≤ y
    have h₁ : (2 : ℚ) ^ k * y.den ≤ y.num := by
      calc (2 : ℚ) ^ k * y.den ≤ y * y.den := by bound_calc
        _ = y.num := Rat.mul_den_eq_num y
    -- Cast: in ℤ, (d * 2^k) ≤ y.num.natAbs
    have hp_eq : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg (by omega)
    suffices hs : ((d * 2 ^ k : ℕ) : ℚ) ≤ (p : ℚ) by exact_mod_cast hs
    have hp_cast : (y.num : ℚ) = (p : ℚ) := by
      rw [show (p : ℚ) = ((p : ℤ) : ℚ) from by push_cast; rfl, hp_eq.symm]
    calc ((d * 2 ^ k : ℕ) : ℚ) = (d : ℚ) * 2 ^ k := by push_cast; ring
      _ = 2 ^ k * y.den := by ring
      _ ≤ y.num := h₁
      _ = (p : ℚ) := hp_cast
  have hp_lt_nat : p < 2 ^ (k + 1) * d := by
    have h := logArgRedK_lt_pow y hy  -- y < (2:ℚ)^(k+1)
    have h₁ : (y.num : ℚ) < (2 : ℚ) ^ (k + 1) * y.den := by
      calc (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
        _ < (2 : ℚ) ^ (k + 1) * y.den := by bound_calc
    have hp_eq : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg (by omega)
    suffices hs : (p : ℚ) < ((2 ^ (k + 1) * d : ℕ) : ℚ) by exact_mod_cast hs
    have hp_cast : (p : ℚ) = (y.num : ℚ) := by
      rw [show (p : ℚ) = ((p : ℤ) : ℚ) from by push_cast; rfl, hp_eq.symm]
    calc (p : ℚ) = y.num := hp_cast
      _ < 2 ^ (k + 1) * y.den := h₁
      _ = ((2 ^ (k + 1) * d : ℕ) : ℚ) := by push_cast; ring
  -- y = p / d in ℝ
  have hy_eq : (y : ℝ) = (p : ℝ) / d := by
    rw [Rat.cast_def, ← hd_def]
    congr 1
    have : y.num = (p : ℤ) := (Int.natAbs_of_nonneg (by omega : 0 ≤ y.num)).symm
    exact_mod_cast this
  -- Unfold the goal
  simp only [logReducedArg]; push_cast
  rw [show (1 : ℝ) - ((y : ℝ) / (2 : ℝ) ^ k - 1) = 2 - (y : ℝ) / 2 ^ k from by ring]
  -- 2 - y/2^k ≥ 1/(d·2^k) (integer gap)
  have h_gap : (1 : ℝ) / (d * 2 ^ k) ≤ 2 - (y : ℝ) / 2 ^ k := by
    rw [hy_eq, show (p : ℝ) / d / 2 ^ k = p / (d * 2 ^ k) from by rw [div_div]]
    rw [show (2 : ℝ) - (p : ℝ) / ((d : ℝ) * 2 ^ k) =
      (2 * ((d : ℝ) * 2 ^ k) - p) / (d * 2 ^ k) from by field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    -- 2*d*2^k - p ≥ 1 in ℕ (since p < 2^(k+1)*d = 2*d*2^k)
    have h1 : p < 2 * d * 2 ^ k := by
      have : 2 ^ (k + 1) * d = 2 * d * 2 ^ k := by rw [pow_succ]; ring
      omega
    have h2 : 1 ≤ 2 * d * 2 ^ k - p := by omega
    have : (1 : ℝ) ≤ ((2 * d * 2 ^ k - p : ℕ) : ℝ) := by exact_mod_cast h2
    have : ((2 * d * 2 ^ k - p : ℕ) : ℝ) = 2 * ((d : ℝ) * 2 ^ k) - (p : ℝ) := by
      push_cast [show p ≤ 2 * d * 2 ^ k from by omega]; ring
    linarith
  -- 1/p ≤ 1/(d·2^k) (since d·2^k ≤ p)
  calc (1 : ℝ) / p ≤ 1 / (d * 2 ^ k) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast hd2k_le
    _ ≤ 2 - (y : ℝ) / 2 ^ k := h_gap

omit [FloatFormat] in
/-- Helper: fuel bound for the new iteration formula `ab*(L+ab+1) < 600*ab⁴*2^ab + 200`. -/
private theorem logFuel_iter_lt_fuel (ab L : ℕ) (hab_ge : 100 ≤ ab)
    (hL : L ≤ 500 * ab ^ 3 * 2 ^ ab) :
    ab * (L + ab + 1) < 600 * ab ^ 4 * 2 ^ ab + 200 := by
  -- ab*(L+ab+1) ≤ ab*(500*ab³*2^ab + ab + 1)
  -- = 500*ab⁴*2^ab + ab² + ab ≤ 500*ab⁴*2^ab + 2*ab² ≤ 502*ab⁴*2^ab < 600*ab⁴*2^ab + 200
  have hab2 : 1 ≤ 2 ^ ab := Nat.one_le_two_pow
  have h1 : ab * (L + ab + 1) ≤ ab * (500 * ab ^ 3 * 2 ^ ab + ab + 1) := by
    bound_calc
  have h2 : ab * (500 * ab ^ 3 * 2 ^ ab + ab + 1) =
      500 * ab ^ 4 * 2 ^ ab + ab ^ 2 + ab := by ring
  -- ab² + ab ≤ 2*ab⁴*2^ab (since ab² ≤ ab⁴ and ab ≤ ab⁴ for ab ≥ 1, and 2^ab ≥ 1)
  have h3 : ab ^ 2 + ab ≤ 2 * ab ^ 4 * 2 ^ ab := by
    have : ab ^ 2 + ab ≤ 2 * ab ^ 2 := by nlinarith [show 1 ≤ ab from by omega]
    have : 2 * ab ^ 2 ≤ 2 * ab ^ 4 := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have : 2 * ab ^ 4 ≤ 2 * ab ^ 4 * 2 ^ ab :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  calc ab * (L + ab + 1)
      ≤ ab * (500 * ab ^ 3 * 2 ^ ab + ab + 1) := h1
    _ = 500 * ab ^ 4 * 2 ^ ab + ab ^ 2 + ab := h2
    _ = 500 * ab ^ 4 * 2 ^ ab + (ab ^ 2 + ab) := Nat.add_assoc _ _ _
    _ ≤ 500 * ab ^ 4 * 2 ^ ab + 2 * ab ^ 4 * 2 ^ ab :=
        Nat.add_le_add_left h3 _
    _ < 600 * ab ^ 4 * 2 ^ ab + 200 := by
        have : 500 * ab ^ 4 * 2 ^ ab + 2 * ab ^ 4 * 2 ^ ab =
          502 * ab ^ 4 * 2 ^ ab := by ring
        have : 0 < ab ^ 4 * 2 ^ ab := by positivity
        nlinarith

set_option maxHeartbeats 1600000 in
/-- Width bound helper: at iteration `ab*(L+ab+1)`, the bracket is tight enough.
Extracted to keep the proof context small. -/
private theorem logWidth_lt_delta (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y)
    (ab L : ℕ) (hab_ge : 100 ≤ ab) (hp_le : y.num.natAbs ≤ ab)
    (hS_le_ab : ∀ i, stickyShift (logBounds y (logArgRedK y) i).1 ≤ ab)
    (δ : ℝ) (hδ_pos : 0 < δ) (hL_delta : (1 : ℝ) / δ ≤ (2 : ℝ) ^ L) :
    let iter := ab * (L + ab + 1)
    let bounds := logBounds y (logArgRedK y) iter
    ((bounds.2 : ℝ) - (bounds.1 : ℝ)) * 2 ^ (stickyShift bounds.1) < δ := by
  set iter := ab * (L + ab + 1)
  set k := logArgRedK y with hk_def
  set t := logReducedArg y k with ht_def
  set N := logNumTerms + iter * 10 with hN_def
  set N_ln2 := Nat.log2 k + 52 + iter * 50 with hN_ln2_def
  set bounds := logBounds y (logArgRedK y) iter with hbounds_def
  set S := stickyShift bounds.1 with hS_def
  -- S ≤ ab
  have hS_le : S ≤ ab := hS_le_ab iter
  -- δ ≥ 1/2^L
  have h2L_pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have h_delta_lb : (1 : ℝ) / 2 ^ L ≤ δ := by
    have h1 : 1 ≤ δ * (2 : ℝ) ^ L := by
      calc (1 : ℝ) = (1 / δ) * δ := by rw [one_div, inv_mul_cancel₀ hδ_pos.ne']
        _ ≤ (2 : ℝ) ^ L * δ := by nlinarith
        _ = δ * (2 : ℝ) ^ L := mul_comm _ _
    exact (div_le_iff₀ h2L_pos).mpr h1
  -- N_ln2 ≥ L + 2*ab + 2
  have hN_ln2_ge : L + 2 * ab + 2 ≤ N_ln2 := by
    simp only [N_ln2, iter]
    -- Goal: L + 2*ab + 2 ≤ k.log2 + 52 + ab * (L + ab + 1) * 50
    have h50L : L ≤ 50 * ab * L := Nat.le_mul_of_pos_left _ (by omega)
    have h50ab : 2 * ab ≤ 50 * ab * (ab + 1) := by
      calc 2 * ab ≤ 50 * ab := by omega
        _ = 50 * ab * 1 := (Nat.mul_one _).symm
        _ ≤ 50 * ab * (ab + 1) := by bound_calc
    have hkey : L + 2 * ab ≤ ab * (L + ab + 1) * 50 := by
      have : L + 2 * ab ≤ 50 * ab * L + 50 * ab * (ab + 1) := by omega
      have : 50 * ab * L + 50 * ab * (ab + 1) = ab * (L + ab + 1) * 50 := by ring
      omega
    omega
  -- 2*N+1 ≥ ab*(L+S+2)
  have h2N1_ge : ab * (L + S + 2) ≤ 2 * N + 1 := by
    have h1 : ab * (L + S + 2) ≤ ab * (L + ab + 2) := by bound_calc
    have h2 : L + ab + 2 ≤ 20 * (L + ab + 1) := by omega
    have h3 : ab * (L + ab + 2) ≤ ab * (20 * (L + ab + 1)) := by bound_calc
    have h4 : ab * (20 * (L + ab + 1)) = 20 * (ab * (L + ab + 1)) := by ring
    simp only [N, iter, logNumTerms]
    -- Goal: ab * (L + S + 2) ≤ 2 * (pn + 10 + ab * (L + ab + 1) * 10) + 1
    -- We use: ab*(L+S+2) ≤ 20*(ab*(L+ab+1)) ≤ 2*(... + ab*(L+ab+1)*10) + 1
    have h5 : 20 * (ab * (L + ab + 1)) = ab * (L + ab + 1) * 20 := by ring
    omega
  -- === Term 1: k*2^S/2^N_ln2 ≤ 1/(4*2^L) ===
  have hk_le : k ≤ ab := by
    simp only [k, logArgRedK]
    split_ifs with h0
    · exact Nat.zero_le _
    · exact le_trans (Nat.log_le_self 2 _)
        (le_trans (Nat.div_le_self _ _) hp_le)
  have hab_le_2ab : (ab : ℝ) ≤ (2 : ℝ) ^ ab := by exact_mod_cast Nat.lt_two_pow_self.le
  have ht1 : (k : ℝ) * 2 ^ S / 2 ^ N_ln2 ≤ 1 / (4 * (2 : ℝ) ^ L) := by
    have h2Nln2 : (2 : ℝ) ^ (L + 2 * ab + 2) ≤ (2 : ℝ) ^ N_ln2 := by linearize
    have hkS : (k : ℝ) * 2 ^ S ≤ (ab : ℝ) * 2 ^ ab := by bound_calc
    calc (k : ℝ) * 2 ^ S / 2 ^ N_ln2
        ≤ (k : ℝ) * 2 ^ S / 2 ^ (L + 2 * ab + 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2Nln2
      _ ≤ (ab : ℝ) * 2 ^ ab / 2 ^ (L + 2 * ab + 2) :=
          div_le_div_of_nonneg_right hkS (by positivity)
      _ ≤ 1 / (4 * (2 : ℝ) ^ L) := by
          -- ab*2^ab / 2^(L+2*ab+2) ≤ 1/(4*2^L)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          rw [one_mul]
          -- Goal: ab * 2^ab * (4 * 2^L) ≤ 2^(L+2*ab+2)
          calc (ab : ℝ) * 2 ^ ab * (4 * 2 ^ L)
              ≤ 2 ^ ab * 2 ^ ab * (4 * 2 ^ L) := by bound_calc
            _ = (2 : ℝ) ^ (L + 2 * ab + 2) := by
                rw [show L + 2 * ab + 2 = 2 + L + ab + ab from by omega]
                simp only [pow_add]; norm_num; ring
  -- === Term 2: t^(2N+1)*2^S/(2N+1) ≤ 1/(4*2^L) ===
  have ht_nonneg : (0 : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast ht_def ▸ logReducedArg_nonneg y hy
  have ht2 : (t : ℝ) ^ (2 * N + 1) * 2 ^ S / ((2 * N : ℝ) + 1) ≤
      1 / (4 * (2 : ℝ) ^ L) := by
    by_cases ht0 : (t : ℝ) = 0
    · -- t = 0, so 0^(2N+1)*2^S/(2N+1) = 0 ≤ 1/(4*2^L)
      have : (t : ℝ) ^ (2 * N + 1) = 0 := by rw [ht0]; exact zero_pow (by omega)
      rw [this, zero_mul, zero_div]; positivity
    · have h_sub := logReducedArg_one_sub_ge y hy hy1
      simp only [← hk_def, ← ht_def] at h_sub
      have ht_gap : (t : ℝ) ≤ 1 - 1 / (ab : ℝ) := by
        have hp_le_ab : (y.num.natAbs : ℝ) ≤ (ab : ℝ) := by exact_mod_cast hp_le
        have hp_pos : (0 : ℝ) < y.num.natAbs := by
          exact_mod_cast Int.natAbs_pos.mpr (by
            have : (0 : ℤ) < y.num := Rat.num_pos.mpr (lt_trans zero_lt_one hy1); omega)
        linarith [show (1 : ℝ) / ab ≤ 1 / y.num.natAbs from
          div_le_div_of_nonneg_left one_pos.le (by positivity) hp_le_ab]
      have h_decay : (t : ℝ) ^ (2 * N + 1) ≤ (1 / 2 : ℝ) ^ (L + S + 2) :=
        geom_decay_bound (t : ℝ) ab (L + S + 2) (2 * N + 1)
          ht_nonneg (by omega) ht_gap h2N1_ge
      -- t^(2N+1)*2^S/(2N+1) ≤ (1/2)^(L+S+2)*2^S/(2N+1) ≤ (1/2)^(L+2) ≤ 1/(4*2^L)
      have hN_pos : (0 : ℝ) < 2 * ↑N + 1 := by positivity
      calc (t : ℝ) ^ (2 * N + 1) * 2 ^ S / ((2 * N : ℝ) + 1)
          ≤ (1 / 2 : ℝ) ^ (L + S + 2) * 2 ^ S / ((2 * N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_right _ hN_pos.le
            bound_calc
        _ ≤ (1 / 2 : ℝ) ^ (L + S + 2) * 2 ^ S := by
            apply div_le_self (by positivity) (by linarith)
        _ = 1 / (4 * (2 : ℝ) ^ L) := by
            rw [one_div_pow, show L + S + 2 = S + (L + 2) from by omega, pow_add]
            rw [show L + 2 = 2 + L from by omega, pow_add]
            field_simp; ring
  -- === Combine ===
  have hbound := logBounds_width_bound y iter
  have hwidth_bound : ((bounds.2 : ℝ) - (bounds.1 : ℝ)) * 2 ^ S ≤
      (k : ℝ) * 2 ^ S / 2 ^ N_ln2 +
      (t : ℝ) ^ (2 * N + 1) * 2 ^ S / ((2 * N : ℝ) + 1) := by
    calc ((bounds.2 : ℝ) - (bounds.1 : ℝ)) * 2 ^ S
        ≤ ((k : ℝ) / 2 ^ N_ln2 + (t : ℝ) ^ (2 * N + 1) / ((2 * N : ℝ) + 1)) * 2 ^ S := by
          bound_calc
      _ = (k : ℝ) * 2 ^ S / 2 ^ N_ln2 +
          (t : ℝ) ^ (2 * N + 1) * 2 ^ S / ((2 * N : ℝ) + 1) := by ring
  calc ((bounds.2 : ℝ) - (bounds.1 : ℝ)) * 2 ^ S
      ≤ (k : ℝ) * 2 ^ S / 2 ^ N_ln2 +
        (t : ℝ) ^ (2 * N + 1) * 2 ^ S / ((2 * N : ℝ) + 1) := hwidth_bound
    _ ≤ 1 / (4 * (2 : ℝ) ^ L) + 1 / (4 * (2 : ℝ) ^ L) := add_le_add ht1 ht2
    _ = 1 / (2 * (2 : ℝ) ^ L) := by field_simp; ring
    _ < 1 / (2 : ℝ) ^ L := by
        apply div_lt_div_of_pos_left one_pos (by positivity)
        linarith [show (0 : ℝ) < (2 : ℝ) ^ L from by positivity]
    _ ≤ δ := h_delta_lb

set_option maxHeartbeats 1600000 in
/-- **Fuel sufficiency**: within `logFuel y` iterations, `stickyTryOne` succeeds. -/
theorem logFuel_sufficient (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) :
    ∃ iter, iter < logFuel y ∧
      (stickyTryOne (logBounds y (logArgRedK y)) iter).isSome = true := by
  -- ab as in logFuel — hide USize from omega by introducing opaque pn
  obtain ⟨pn, hpn⟩ : ∃ n : ℕ, FloatFormat.prec.toNat = n := ⟨_, rfl⟩
  simp only [logFuel, hpn]
  set ab := y.num.natAbs ^ 2 / y.den + y.num.natAbs + y.den + pn + 100 with hab_def
  have hab_ge : 100 ≤ ab := Nat.le_add_left _ _
  have hp_le : y.num.natAbs ≤ ab :=
    le_trans (Nat.le_add_left _ (y.num.natAbs ^ 2 / y.den))
      (le_trans (Nat.le_add_right _ y.den) (le_trans (Nat.le_add_right _ pn) (Nat.le_add_right _ 100)))
  have hab_eq : y.num.natAbs ^ 2 / y.den + y.num.natAbs + y.den + 100 ≤ ab :=
    Nat.add_le_add_right (Nat.le_add_right _ pn) 100
  -- Shift bound
  have hS_bound : ∀ iter, stickyShift (logBounds y (logArgRedK y) iter).1 ≤
      pn + 7 + Nat.log2 y.num.natAbs := by
    rw [← hpn]; exact logStickyShift_bound y hy hy1
  have hS_le_ab : pn + 7 + Nat.log2 y.num.natAbs ≤ ab := by
    have hlog_le := Nat.log2_le_self y.num.natAbs
    have hpp_le : y.num.natAbs + pn + 100 ≤ ab := by
      have h1 : y.num.natAbs + pn + 100 ≤ y.num.natAbs + y.den + pn + 100 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_right _ _) _) _
      have h2 : y.num.natAbs + y.den + pn + 100 ≤
          y.num.natAbs ^ 2 / y.den + y.num.natAbs + y.den + pn + 100 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.le_add_left _ _) _) _) _
      exact le_trans h1 h2
    suffices h : (pn + 7 + y.num.natAbs : ℤ) ≤ ab from
      le_trans (Nat.add_le_add_left hlog_le _) (by exact_mod_cast h)
    have := show (y.num.natAbs + pn + 100 : ℤ) ≤ ab from by exact_mod_cast hpp_le
    linarith
  have hS_le : ∀ i, stickyShift (logBounds y (logArgRedK y) i).1 ≤ ab :=
    fun i => le_trans (hS_bound i) hS_le_ab
  -- Step 1: Uniform effective irrationality gap
  have ⟨δ, hδ_pos, L, hL_bound, hL_delta, hδ_gap⟩ :
      ∃ δ > 0, ∃ L : ℕ, L ≤ 500 * ab ^ 3 * 2 ^ ab ∧
      (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧
      ∀ iter, ∀ m : ℤ,
      |Real.log (y : ℝ) * 2 ^ (stickyShift (logBounds y (logArgRedK y) iter).1) - (m : ℝ)| ≥ δ := by
    have h := uniform_gap_from_pointwise ab (500 * ab ^ 3 * 2 ^ ab)
      (fun s m => |Real.log (y : ℝ) * 2 ^ s - (m : ℝ)|)
      (fun s hs => log_effective_gap y hy1 s ab hab_eq hs)
    obtain ⟨δ, hδ, L, hL, hLd, hδ_all⟩ := h
    exact ⟨δ, hδ, L, hL, hLd, fun iter m => hδ_all _ (hS_le iter) m⟩
  -- Step 2: Apply logWidth_lt_delta
  set iter := ab * (L + ab + 1)
  have hiter_fuel : iter < 600 * ab ^ 4 * 2 ^ ab + 200 :=
    logFuel_iter_lt_fuel ab L hab_ge hL_bound
  have hwidth := logWidth_lt_delta y hy hy1 ab L hab_ge hp_le hS_le δ hδ_pos hL_delta
  exact ⟨iter, hiter_fuel,
    stickyTryOne_logBounds_of_tight_bracket y hy hy1 iter δ (hδ_gap iter) hwidth⟩

/-- The sticky extraction loop for `logBounds` terminates within `logFuel y` steps.
This is the main termination theorem (Thread 2). -/
theorem stickyTryOne_logBounds_terminates (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) :
    ∃ n, 0 ≤ n ∧ n < 0 + logFuel y ∧
      (stickyTryOne (logBounds y (logArgRedK y)) n).isSome = true := by
  obtain ⟨iter, hiter_fuel, hsuccess⟩ := logFuel_sufficient y hy hy1
  exact ⟨iter, by omega, by omega, hsuccess⟩

end LogComputable
