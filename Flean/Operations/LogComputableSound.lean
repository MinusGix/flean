import Flean.Operations.LogComputableDefs
import Flean.Operations.ExpComputableSound

/-! # Computable log: bracket correctness

Soundness proofs for the computable log kernel. Shows that:
- `logBounds` produces valid brackets (`lower < log(y) ≤ upper`)
- The lower bound is positive (needed for sticky extraction)
- These feed into the generic `stickyTryOne`/`stickyExtractLoop` soundness
-/

/-! ## Irrationality of log -/

/-- `Real.log` of a positive rational ≠ 1 is irrational.
Proof: if `log(r) = q ∈ ℚ`, then `exp(q) = r ∈ ℚ`, contradicting `irrational_exp_rat`. -/
theorem irrational_log_rat (r : ℚ) (hr_pos : (0 : ℝ) < r) (hr_ne_one : (r : ℝ) ≠ 1) :
    Irrational (Real.log (r : ℝ)) := by
  intro ⟨q, hq⟩
  have hq_ne : q ≠ 0 := by
    intro h
    apply hr_ne_one
    have : Real.log (r : ℝ) = 0 := by linarith [hq.symm, show (q : ℝ) = 0 from by rw [h]; simp]
    rw [← Real.exp_log hr_pos, this, Real.exp_zero]
  have hirr := irrational_exp_rat q hq_ne
  rw [hq, Real.exp_log hr_pos] at hirr
  exact hirr ⟨r, rfl⟩

/-! ## Argument reduction correctness -/

/-- `y.num.natAbs / y.den = ⌊y⌋₊` for `y ≥ 0`. -/
private theorem rat_natAbs_div_den_eq_natFloor (y : ℚ) (hy : 0 ≤ y) :
    y.num.natAbs / y.den = ⌊y⌋₊ := by
  have hnum_nonneg : 0 ≤ y.num := Rat.num_nonneg.mpr hy
  -- Suffices to show equality as integers
  have hd_pos : (0 : ℤ) < y.den := by exact_mod_cast y.pos
  apply Int.ofNat_inj.mp
  rw [Int.natCast_ediv]
  rw [Int.natAbs_of_nonneg hnum_nonneg]
  -- LHS: y.num / ↑y.den (Int)
  -- RHS: ↑⌊y⌋₊ = ↑(⌊y⌋.toNat) = max ⌊y⌋ 0 = ⌊y⌋ (since y ≥ 0 → ⌊y⌋ ≥ 0)
  rw [show (⌊y⌋₊ : ℤ) = ⌊y⌋ from Int.toNat_of_nonneg (Int.floor_nonneg.mpr hy)]
  exact (Rat.floor_def' (q := y)).symm

/-- `logArgRedK y` gives `k` such that `2^k ≤ y` when `1 ≤ y`. -/
theorem logArgRedK_pow_le (y : ℚ) (hy : 1 ≤ y) :
    (2 : ℚ) ^ logArgRedK y ≤ y := by
  simp only [logArgRedK]
  have hy0 : (0 : ℚ) ≤ y := by linarith
  rw [rat_natAbs_div_den_eq_natFloor y hy0]
  have hfl_ne : ⌊y⌋₊ ≠ 0 := by
    have : 0 < ⌊y⌋₊ := Nat.floor_pos.mpr hy
    omega
  rw [if_neg hfl_ne]
  calc (2 : ℚ) ^ Nat.log 2 ⌊y⌋₊
      ≤ (⌊y⌋₊ : ℚ) := by exact_mod_cast Nat.pow_log_le_self 2 hfl_ne
    _ ≤ y := Nat.floor_le hy0

/-- `y < 2^(logArgRedK y + 1)` when `1 ≤ y`. -/
theorem logArgRedK_lt_pow (y : ℚ) (hy : 1 ≤ y) :
    y < (2 : ℚ) ^ (logArgRedK y + 1) := by
  simp only [logArgRedK]
  have hy0 : (0 : ℚ) ≤ y := by linarith
  rw [rat_natAbs_div_den_eq_natFloor y hy0]
  have hfl_ne : ⌊y⌋₊ ≠ 0 := by
    have : 0 < ⌊y⌋₊ := Nat.floor_pos.mpr hy
    omega
  rw [if_neg hfl_ne]
  calc y < (⌊y⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one y
    _ ≤ (2 : ℚ) ^ (Nat.log 2 ⌊y⌋₊ + 1) := by
        exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊y⌋₊

/-- The reduced argument `t = y / 2^k - 1 ≥ 0` for `y ≥ 1` and `k = logArgRedK y`. -/
theorem logReducedArg_nonneg (y : ℚ) (hy : 1 ≤ y) :
    0 ≤ logReducedArg y (logArgRedK y) := by
  simp only [logReducedArg]
  have h := logArgRedK_pow_le y hy
  have h2k_pos : (0 : ℚ) < (2 : ℚ) ^ logArgRedK y := by positivity
  rw [sub_nonneg, le_div_iff₀ h2k_pos]
  linarith

/-- The reduced argument `t = y / 2^k - 1 < 1` for `y ≥ 1`. -/
theorem logReducedArg_lt_one (y : ℚ) (hy : 1 ≤ y) :
    (logReducedArg y (logArgRedK y) : ℝ) < 1 := by
  simp only [logReducedArg]; push_cast
  have h := logArgRedK_lt_pow y hy
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ (logArgRedK y) := by positivity
  rw [sub_lt_iff_lt_add, show (1 : ℝ) + 1 = 2 from by ring, div_lt_iff₀ h2k_pos]
  calc (y : ℝ) < (2 : ℝ) ^ (logArgRedK y + 1) := by exact_mod_cast h
    _ = 2 * (2 : ℝ) ^ logArgRedK y := by rw [pow_succ]; ring

/-- The reduced argument `t > 0` when `y > 1` and `k = 0`. -/
theorem logReducedArg_pos_of_k_zero (y : ℚ) (hy1 : 1 < y)
    (hk : logArgRedK y = 0) :
    0 < logReducedArg y (logArgRedK y) := by
  simp only [logReducedArg, hk, pow_zero]
  linarith

/-- Decomposition: `log(y) = k · log(2) + log(1 + t)` where `t = y / 2^k - 1`. -/
theorem log_decompose (y : ℚ) (k : ℕ) (hy : (0 : ℝ) < y) :
    Real.log (y : ℝ) = k * Real.log 2 + Real.log (1 + (logReducedArg y k : ℝ)) := by
  simp only [logReducedArg]; push_cast
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ (k : ℕ) := by positivity
  rw [show 1 + ((y : ℝ) / (2 : ℝ) ^ k - 1) = (y : ℝ) / (2 : ℝ) ^ k from by ring]
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt h2k_pos)]
  rw [Real.log_pow]
  ring

/-! ## Bracket correctness -/

section BracketCorrectness

variable [FloatFormat]

/-- `lower < log(y)` for the lower bound from `logBounds`.
Uses `logArgRedK y` as `k` throughout. -/
theorem logBounds_lower_lt_log (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) (iter : ℕ) :
    ((logBounds y (logArgRedK y) iter).1 : ℝ) < Real.log (y : ℝ) := by
  set k := logArgRedK y with hk_def
  simp only [logBounds]
  set N_ln2 := Nat.log2 k + 52 + iter * 50
  set s_ln2 := ln2SeriesSum N_ln2
  set N := logNumTerms + iter * 10
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast lt_of_lt_of_le one_pos hy
  rw [log_decompose y k hy_pos]
  push_cast
  -- Now set t after push_cast so it captures all occurrences
  set t := logReducedArg y k with ht_def
  have hln2_le : (s_ln2 : ℝ) ≤ Real.log 2 := ln2SeriesSum_le_log2 N_ln2
  have ht_nonneg : (0 : ℚ) ≤ t := ht_def ▸ logReducedArg_nonneg y hy
  have ht_lt_one : (t : ℝ) < 1 := ht_def ▸ hk_def ▸ logReducedArg_lt_one y hy
  have hlog1t_le : (logLowerBound t N : ℝ) ≤ Real.log (1 + (t : ℝ)) :=
    taylorLogQ_even_le_log t ht_nonneg ht_lt_one N
  by_cases hk0 : k = 0
  · -- k = 0: strict from irrationality of log(1+t)
    have ht_pos : (0 : ℚ) < t := by
      rw [ht_def, hk_def]; exact logReducedArg_pos_of_k_zero y hy1 (hk_def ▸ hk0)
    have hirr : Irrational (Real.log (1 + (t : ℝ))) := by
      rw [show 1 + (t : ℝ) = ((1 + t : ℚ) : ℝ) from by push_cast; ring]
      exact irrational_log_rat (1 + t)
        (by exact_mod_cast show (0 : ℚ) < 1 + t from by linarith)
        (by push_cast; linarith [show (0 : ℝ) < (t : ℝ) from by exact_mod_cast ht_pos])
    have hstrict := lt_of_le_of_ne hlog1t_le
      (fun h => hirr ⟨logLowerBound t N, h⟩)
    have hk_zero : (k : ℝ) = 0 := by exact_mod_cast hk0
    simp only [hk_zero, zero_mul] at *
    linarith
  · -- k > 0: strict from irrationality of log(2)
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
    have hirr : Irrational (Real.log 2) := by
      rw [show (2 : ℝ) = ((2 : ℚ) : ℝ) from by push_cast; ring]
      exact irrational_log_rat 2 (by norm_num) (by norm_num)
    have hln2_strict : (s_ln2 : ℝ) < Real.log 2 :=
      lt_of_le_of_ne hln2_le (fun h => hirr ⟨s_ln2, h⟩)
    linarith [mul_lt_mul_of_pos_left hln2_strict hk_pos]

/-- `log(y) ≤ upper` for the upper bound from `logBounds`. -/
theorem logBounds_log_le_upper (y : ℚ) (hy : 1 ≤ y) (iter : ℕ) :
    Real.log (y : ℝ) ≤ ((logBounds y (logArgRedK y) iter).2 : ℝ) := by
  set k := logArgRedK y with hk_def
  simp only [logBounds]
  set t := logReducedArg y k with ht_def
  set N_ln2 := Nat.log2 k + 52 + iter * 50
  set s_ln2 := ln2SeriesSum N_ln2
  set N := logNumTerms + iter * 10
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast lt_of_lt_of_le one_pos hy
  rw [log_decompose y k hy_pos]
  push_cast
  have hln2_upper : Real.log 2 ≤ (s_ln2 : ℝ) + 1 / 2 ^ N_ln2 :=
    log2_le_ln2SeriesSum_add N_ln2
  have ht_nonneg : (0 : ℚ) ≤ t := ht_def ▸ hk_def ▸ logReducedArg_nonneg y hy
  have ht_lt_one : (t : ℝ) < 1 := ht_def ▸ hk_def ▸ logReducedArg_lt_one y hy
  have hlog1t_upper : Real.log (1 + (t : ℝ)) ≤ (logUpperBound t N : ℝ) :=
    log_le_taylorLogQ_odd t ht_nonneg ht_lt_one N
  linarith [mul_le_mul_of_nonneg_left hln2_upper (Nat.cast_nonneg k)]

/-- The lower bound from `logBounds` is positive. -/
theorem logBounds_lower_pos (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) (iter : ℕ) :
    (0 : ℝ) < ((logBounds y (logArgRedK y) iter).1 : ℝ) := by
  set k := logArgRedK y with hk_def
  simp only [logBounds]; push_cast
  -- After simp, goal is about logReducedArg y k directly
  set t := logReducedArg y k with ht_def
  set N_ln2 := Nat.log2 k + 52 + iter * 50
  set N := logNumTerms + iter * 10
  have ht_nonneg : (0 : ℚ) ≤ t := ht_def ▸ logReducedArg_nonneg y hy
  have ht_lt_one : (t : ℝ) < 1 := ht_def ▸ hk_def ▸ logReducedArg_lt_one y hy
  have hln2_nonneg : (0 : ℝ) ≤ (ln2SeriesSum N_ln2 : ℝ) :=
    Rat.cast_nonneg.mpr (ln2SeriesSum_nonneg N_ln2)
  have hlog1t_nonneg : (0 : ℝ) ≤ (logLowerBound t N : ℝ) :=
    logLowerBound_nonneg t ht_nonneg ht_lt_one N
  by_cases hk0 : k = 0
  · -- k = 0: t > 0, so logLowerBound t N > 0
    have ht_pos : (0 : ℚ) < t := by
      rw [ht_def, hk_def]; exact logReducedArg_pos_of_k_zero y hy1 (hk_def ▸ hk0)
    have hN_ge : 1 ≤ N := by
      show 1 ≤ logNumTerms + iter * 10
      simp only [logNumTerms]; omega
    have := logLowerBound_pos t ht_pos ht_lt_one N hN_ge
    simp only [hk0, Nat.cast_zero, zero_mul, zero_add]
    linarith
  · -- k > 0: ln2SeriesSum ≥ 1/2 > 0
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
    have hN_ln2_ge : 1 ≤ N_ln2 := by
      show 1 ≤ Nat.log2 k + 52 + iter * 50; omega
    have hln2_pos : (0 : ℝ) < (ln2SeriesSum N_ln2 : ℝ) := by
      have h := ln2SeriesSum_ge_half N_ln2 hN_ln2_ge
      have : (0 : ℚ) < ln2SeriesSum N_ln2 := by linarith
      exact_mod_cast this
    linarith [mul_pos hk_pos hln2_pos]

end BracketCorrectness
