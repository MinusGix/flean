import Flean.Operations.Exp
import Flean.Operations.ExpTaylor
import Flean.Operations.StickyTermination
import Flean.NumberTheory.ExpEffectiveBound
import Flean.Linearize.Linearize
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Computable exp: definitions and bracket correctness

Core computation definitions for `exp(x)` and proof that each successful
extraction step produces a correct sticky interval.

See `ExpComputable.lean` for the high-level architecture overview. This file contains:
- Constants (ln2 bounds, fuel, Taylor order)
- Computation definitions (argument reduction, Taylor bounds, extraction loop)
- `OpRefExec expTarget` instance (the computable kernel)
- Basic properties (positivity, q bounds, exact-case handling)
- Floor/sticky interval arithmetic
- ln(2) series soundness and argument reduction correctness
- **Bracket correctness** (Thread 1): bracket proofs for `expBounds`
-/

section ExpComputable

variable [FloatFormat]

/-! ## Constants -/

/-- Rational lower bound for `Real.log 2`. From mathlib: `0.6931471803 < Real.log 2`. -/
def ln2_lo : ℚ := 6931471803 / 10000000000

/-- Rational upper bound for `Real.log 2`. From mathlib: `Real.log 2 < 0.6931471808`. -/
def ln2_hi : ℚ := 6931471808 / 10000000000

/-! ## Adaptive ln(2) bounds -/

/-- Partial sum of the series `ln(2) = Σ_{k=1}^∞ 1/(k·2^k)`.
Gives a lower bound: `ln2SeriesSum N ≤ ln(2)`. -/
def ln2SeriesSum (N : ℕ) : ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ
    | 0, _, acc => acc
    | fuel + 1, k, acc => go fuel (k + 1) (acc + 1 / ((k + 1 : ℚ) * 2 ^ (k + 1)))
  go N 0 0

omit [FloatFormat] in
theorem ln2SeriesSum_go_ge_acc : ∀ fuel k (acc : ℚ),
    acc ≤ ln2SeriesSum.go fuel k acc := by
  intro fuel; induction fuel with
  | zero => intro k acc; exact le_refl _
  | succ n ih =>
    intro k acc; simp only [ln2SeriesSum.go]
    linarith [ih (k + 1) (acc + 1 / ((k + 1 : ℚ) * 2 ^ (k + 1))),
      show (0 : ℚ) ≤ 1 / ((↑k + 1) * 2 ^ (k + 1)) from by positivity]

omit [FloatFormat] in
theorem ln2SeriesSum_nonneg (N : ℕ) : (0 : ℚ) ≤ ln2SeriesSum N :=
  ln2SeriesSum_go_ge_acc N 0 0

omit [FloatFormat] in
theorem ln2SeriesSum_ge_half (N : ℕ) (hN : 1 ≤ N) :
    (1 : ℚ) / 2 ≤ ln2SeriesSum N := by
  simp only [ln2SeriesSum]
  match N, hN with
  | n + 1, _ =>
    simp only [ln2SeriesSum.go]
    calc (1 : ℚ) / 2 = 0 + 1 / ((0 + 1 : ℚ) * 2 ^ (0 + 1)) := by norm_num
      _ ≤ ln2SeriesSum.go n (0 + 1) (0 + 1 / ((0 + 1 : ℚ) * 2 ^ (0 + 1))) :=
          ln2SeriesSum_go_ge_acc n _ _

/-- Generous fuel for the iterative extraction loop.
Same formula as `stickyFuel` from `StickyTermination.lean`. -/
def expFuel (x : ℚ) : ℕ :=
  let ab := x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den + FloatFormat.prec.toNat + 100
  15 * ab * (Nat.log2 ab + 1) + 200

theorem expFuel_eq_stickyFuel (x : ℚ) : expFuel x = stickyFuel x := rfl

/-! ## Constants -/

/-- Number of Taylor terms. Same value as `baseTaylorTerms`. -/
def expNumTerms : ℕ := FloatFormat.prec.toNat + 10

theorem expNumTerms_eq : expNumTerms = baseTaylorTerms := rfl

/-! ## Argument reduction mod ln(2) -/

/-- Compute `k = round(x / ln(2))` using adaptive ln2 bounds.
Uses enough ln2 precision that `|x - k·log(2)| < 1`. -/
def expArgRedK (x : ℚ) : ℤ :=
  -- Use enough bits of ln2 so |k|·(error in ln2) < 1/4
  -- |k| ≤ |x/log2| + 1 ≤ 2·|x| + 1, so need N_ln2 bits where
  -- (2·|x|+1) / 2^N_ln2 < 1/4, i.e., 2^N_ln2 > 4·(2·|x|+1)
  let N_ln2 := Nat.log2 (x.num.natAbs + 1) + Nat.log2 (x.den + 1) + 10
  let ln2_mid := ln2SeriesSum N_ln2 + 1 / (2 * 2 ^ N_ln2)
  round (x / ln2_mid)

/-- Compute a rational interval `[r_lo, r_hi]` containing `x - k·ln(2)`.
Since `ln(2)` is irrational, we bracket it using `ln2_lo < ln(2) < ln2_hi`. -/
def expRInterval (x : ℚ) (k : ℤ) : ℚ × ℚ :=
  if 0 ≤ k then
    -- k·ln2_lo ≤ k·ln(2) ≤ k·ln2_hi, so x - k·ln2_hi ≤ r ≤ x - k·ln2_lo
    (x - k * ln2_hi, x - k * ln2_lo)
  else
    -- k < 0: k·ln2_hi ≤ k·ln(2) ≤ k·ln2_lo, so x - k·ln2_lo ≤ r ≤ x - k·ln2_hi
    (x - k * ln2_lo, x - k * ln2_hi)

/-- Compute r interval using adaptive ln2 bounds. -/
def expRIntervalWith (x : ℚ) (k : ℤ) (lo2 hi2 : ℚ) : ℚ × ℚ :=
  if 0 ≤ k then (x - k * hi2, x - k * lo2)
  else (x - k * lo2, x - k * hi2)

/-- Compute the Taylor lower/upper bounds for `exp(x)` at given precision level.
Returns `(lower, upper)` such that `lower ≤ exp(x) ≤ upper`. -/
def expBounds (x : ℚ) (k : ℤ) (iter : ℕ) : ℚ × ℚ :=
  let N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
  let s_ln2 := ln2SeriesSum N_ln2
  let lo2 := s_ln2
  let hi2 := s_ln2 + 1 / 2 ^ N_ln2
  let (r_lo, r_hi) := expRIntervalWith x k lo2 hi2
  let N := expNumTerms + iter * 10
  (expLowerBound r_lo N * (2 : ℚ) ^ k, expUpperBound r_hi N * (2 : ℚ) ^ k)

/-! ## Main kernel -/

/-- Computable exp reference kernel (standard mod-ln(2) method).

For `a.m = 0` (input is ±0): returns exact result for `exp(0) = 1`.
Otherwise: uses `stickyExtractLoop` with `expBounds` to extract the sticky cell.
1. Reduce `x = k·ln(2) + r` with `k = round(x/ln(2))`
2. Iteratively refine ln(2) and Taylor bounds until cell agreement
3. Extract sticky cell when `⌊lower·2^s⌋ = ⌊upper·2^s⌋` -/
def expComputableRun (a : FiniteFp) : OpRefOut :=
  if a.m = 0 then
    -- exp(0) = 1 = 2 · 1 · 2^(-1)
    { q := 1, e_base := -1, isExact := true }
  else
    let x : ℚ := a.toVal
    let k := expArgRedK x
    (stickyExtractLoop (expBounds x k) 0 (expFuel x)).toOpRefOut

instance (priority := 500) : OpRefExec expTarget where
  run := expComputableRun

/-! ## Soundness helpers -/

/-- The lower bound from `expBounds` is always positive. -/
theorem expBounds_lower_pos (x : ℚ) (k : ℤ) (iter : ℕ) :
    0 < (expBounds x k iter).1 := by
  simp only [expBounds]
  exact mul_pos (expLowerBound_pos _ _) (by positivity)

/-- When `isExact = true`, we must be in the zero branch. -/
theorem expComputableRun_exact_is_zero (a : FiniteFp)
    (hExact : (expComputableRun a).isExact = true) : a.m = 0 := by
  by_contra h
  have : (expComputableRun a).isExact = false := by
    simp only [expComputableRun, h, ↓reduceIte, StickyOut.toOpRefOut_isExact]
  rw [this] at hExact; exact absurd hExact (by decide)

/-- In the zero branch, the output is `{q := 1, e_base := -1, isExact := true}`. -/
theorem expComputableRun_zero (a : FiniteFp) (hm : a.m = 0) :
    expComputableRun a = { q := 1, e_base := -1, isExact := true } := by
  simp [expComputableRun, hm]

/-! ## Sticky interval from floor + error bounds -/

/-! ## ln(2) series soundness -/

omit [FloatFormat] in
/-- The `go` accumulator is additive: shifting the accumulator shifts the result. -/
theorem ln2SeriesSum_go_add (fuel k : ℕ) (c acc : ℚ) :
    ln2SeriesSum.go fuel k (c + acc) = c + ln2SeriesSum.go fuel k acc := by
  induction fuel generalizing k acc with
  | zero => simp [ln2SeriesSum.go]
  | succ n ih =>
    simp only [ln2SeriesSum.go]
    rw [show c + acc + 1 / ((↑k + 1) * 2 ^ (k + 1)) =
      c + (acc + 1 / ((↑k + 1) * 2 ^ (k + 1))) from by ring]
    exact ih (k + 1) _

omit [FloatFormat] in
open Finset in
/-- `go N k 0` as a Finset.Ico sum: `Σ_{j ∈ [k+1, k+1+N)} 1/(j * 2^j)`. -/
theorem ln2SeriesSum_go_eq_Ico (N k : ℕ) :
    ln2SeriesSum.go N k 0 =
      ∑ j ∈ Ico (k + 1) (k + 1 + N), (1 : ℚ) / ((j : ℚ) * 2 ^ j) := by
  induction N generalizing k with
  | zero => simp [ln2SeriesSum.go]
  | succ n ih =>
    unfold ln2SeriesSum.go; rw [zero_add]
    rw [show (1 : ℚ) / ((↑k + 1) * 2 ^ (k + 1)) =
      1 / ((↑k + 1) * 2 ^ (k + 1)) + 0 from (add_zero _).symm,
      ln2SeriesSum_go_add, ih (k + 1)]
    rw [show k + 1 + (n + 1) = (k + 2) + n from by omega,
      show k + 1 + 1 + n = (k + 2) + n from by omega]
    rw [show Ico (k + 1) (k + 2 + n) =
      Ico (k + 1) (k + 2) ∪ Ico (k + 2) (k + 2 + n) from
      (Ico_union_Ico_eq_Ico (by omega) (by omega)).symm]
    rw [sum_union (by
      rw [Finset.disjoint_left]; intro x hx hx2
      simp only [mem_Ico] at hx hx2; omega)]
    congr 1
    rw [show Ico (k + 1) (k + 2) = {k + 1} from by
      ext x; simp only [mem_Ico, mem_singleton]; omega]
    simp only [sum_singleton]; push_cast; ring

omit [FloatFormat] in
/-- Cast of `ln2SeriesSum N` to ℝ equals the standard Taylor partial sum for log 2. -/
theorem ln2SeriesSum_cast_eq (N : ℕ) :
    (ln2SeriesSum N : ℝ) =
      ∑ i ∈ Finset.range N, ((1 : ℝ) / 2) ^ (i + 1) / (↑i + 1) := by
  show (ln2SeriesSum.go N 0 0 : ℝ) = _
  rw [ln2SeriesSum_go_eq_Ico, Finset.sum_Ico_eq_sum_range]
  simp only [show 0 + 1 + N - (0 + 1) = N from by omega]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [one_div_pow, show 1 + i = i + 1 from by omega]; field_simp; ring

omit [FloatFormat] in
theorem log2_eq_neg_log_half : Real.log 2 = -Real.log (1 - 1 / 2) := by
  rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ from by ring, Real.log_inv, neg_neg]

omit [FloatFormat] in
/-- `ln2SeriesSum N ≤ log 2`: partial sums of a positive series are below the total. -/
theorem ln2SeriesSum_le_log2 (N : ℕ) :
    (ln2SeriesSum N : ℝ) ≤ Real.log 2 := by
  rw [ln2SeriesSum_cast_eq, log2_eq_neg_log_half]
  have hsum := Real.hasSum_pow_div_log_of_abs_lt_one (by norm_num : |(1 : ℝ) / 2| < 1)
  have hsummable := hsum.summable
  have hle : ∑ i ∈ Finset.range N, ((1 : ℝ) / 2) ^ (i + 1) / (↑i + 1)
      ≤ ∑' (n : ℕ), ((1 : ℝ) / 2) ^ (n + 1) / ((n : ℝ) + 1) :=
    Summable.sum_le_tsum _ (fun i _ => by positivity) hsummable
  linarith [hsum.tsum_eq]

omit [FloatFormat] in
/-- `log 2 ≤ ln2SeriesSum N + 1/2^N`: the tail of the series is bounded by a geometric sum. -/
theorem log2_le_ln2SeriesSum_add (N : ℕ) :
    Real.log 2 ≤ (ln2SeriesSum N : ℝ) + (1 : ℝ) / 2 ^ N := by
  rw [ln2SeriesSum_cast_eq, log2_eq_neg_log_half]
  have h := Real.abs_log_sub_add_sum_range_le (by norm_num : |(1 : ℝ) / 2| < 1) N
  have hbound : |(1 : ℝ) / 2| ^ (N + 1) / (1 - |(1 : ℝ) / 2|) = (1 : ℝ) / 2 ^ N := by
    have : |(1 : ℝ) / 2| = 1 / 2 := abs_of_pos (by norm_num)
    rw [this, show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num, pow_succ,
        mul_div_cancel_of_imp (fun h => absurd h (by norm_num : (1:ℝ)/2 ≠ 0)),
        one_div_pow]
  rw [hbound] at h
  linarith [abs_le.mp h]

omit [FloatFormat] in
/-- The adaptive `expArgRedK` satisfies `|x - k·log(2)| < 1`.
Triangle inequality: `|x - k·log2| ≤ |x - k·mid| + |k·(mid - log2)| ≤ mid/2 + |k|/(2·2^N)`.
Since `mid < 1` and `|k| < 2^N`, the total is `< 1/2 + 1/2 = 1`. -/
theorem expArgRedK_bound (x : ℚ) :
    |(x : ℝ) - ↑(expArgRedK x) * Real.log 2| < 1 := by
  simp only [expArgRedK]
  set N := Nat.log2 (x.num.natAbs + 1) + Nat.log2 (x.den + 1) + 10
  set lo2 := ln2SeriesSum N
  set mid := lo2 + 1 / (2 * 2 ^ N)
  set k := round ((x : ℚ) / mid)
  have hlo2_le : (lo2 : ℝ) ≤ Real.log 2 := ln2SeriesSum_le_log2 N
  have hlog2_le : Real.log 2 ≤ (lo2 : ℝ) + 1 / 2 ^ N := log2_le_ln2SeriesSum_add N
  have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ (N : ℕ) := pow_pos (by norm_num) N
  have hlog2_pos : (0 : ℝ) < Real.log 2 := by linarith [log2_gt_half]
  -- Cast mid to ℝ
  have hmid_cast : (mid : ℝ) = (lo2 : ℝ) + 1 / (2 * (2 : ℝ) ^ N) := by
    show ((lo2 + 1 / (2 * 2 ^ N) : ℚ) : ℝ) = _; push_cast; ring
  have hfrac_pos : (0:ℝ) < 1 / (2 * (2:ℝ) ^ N) := by positivity
  have hlo2_nn : (0 : ℝ) ≤ (lo2 : ℝ) :=
    Rat.cast_nonneg.mpr (ln2SeriesSum_nonneg N)
  have hmid_pos : (0 : ℝ) < (mid : ℝ) := by rw [hmid_cast]; linarith
  -- mid < 1 and mid ≥ 1/2
  have hmid_lt_1 : (mid : ℝ) < 1 := by
    -- lo2 ≤ log2 < 7/8 and N ≥ 10 so 1/(2·2^N) ≤ 1/2048; sum < 1.
    rw [hmid_cast]
    have h2_10_le : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ N := by linearize
    have hfrac_small : 1 / (2 * (2:ℝ) ^ N) ≤ 1 / (2 * (2:ℝ) ^ (10:ℕ)) := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left h2_10_le (by norm_num))
    have : 1 / (2 * (2:ℝ) ^ (10:ℕ)) = 1 / 2048 := by norm_num
    linarith [log2_lt_seven_eighths]
  have hmid_ge_half : (1 : ℝ) / 2 ≤ (mid : ℝ) := by
    rw [hmid_cast]
    have : (1 : ℝ) / 2 ≤ (lo2 : ℝ) := by
      have h := ln2SeriesSum_ge_half N (by omega)
      have : ((1 / 2 : ℚ) : ℝ) ≤ ((lo2 : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at this; linarith
    linarith
  -- |mid - log 2| ≤ 1/(2*2^N)
  have hmid_err : |(mid : ℝ) - Real.log 2| ≤ 1 / (2 * (2:ℝ) ^ N) := by
    rw [abs_le, hmid_cast]; constructor
    · -- Need: -(1/(2*2^N)) ≤ lo2 + 1/(2*2^N) - log2
      -- From hlog2_le: log2 ≤ lo2 + 1/2^N. So lo2 ≥ log2 - 1/2^N.
      -- lo2 + 1/(2*2^N) - log2 ≥ -1/2^N + 1/(2*2^N) = -(2-1)/(2*2^N) = -1/(2*2^N)
      have h12 : (1:ℝ) / 2 ^ N = 2 * (1 / (2 * (2:ℝ) ^ N)) := by field_simp
      linarith
    · linarith
  -- From rounding: |x/mid - k| ≤ 1/2
  have hround_rat := abs_sub_round ((x : ℚ) / mid)
  have hround : |(x : ℝ) / (mid : ℝ) - (k : ℝ)| ≤ 1 / 2 := by
    have hcast : ((((x : ℚ) / mid - ↑(round ((x : ℚ) / mid))) : ℚ) : ℝ) =
        (x : ℝ) / (mid : ℝ) - (k : ℝ) := by push_cast; ring
    calc |(x : ℝ) / (mid : ℝ) - (k : ℝ)|
        = |(((x : ℚ) / mid - ↑(round ((x : ℚ) / mid)) : ℚ) : ℝ)| := by rw [hcast]
      _ = ((|(x : ℚ) / mid - ↑(round ((x : ℚ) / mid))| : ℚ) : ℝ) := (Rat.cast_abs ..).symm
      _ ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hround_rat
      _ = 1 / 2 := by norm_num
  -- |x - k*mid| ≤ mid/2
  have hx_kmid : |(x : ℝ) - (k : ℝ) * (mid : ℝ)| ≤ (mid : ℝ) / 2 := by
    rw [show (x : ℝ) - (k : ℝ) * (mid : ℝ) =
        (mid : ℝ) * ((x : ℝ) / (mid : ℝ) - (k : ℝ)) from by field_simp,
        abs_mul, abs_of_pos hmid_pos]
    calc (mid : ℝ) * |(x : ℝ) / (mid : ℝ) - (k : ℝ)|
        ≤ (mid : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left hround hmid_pos.le
      _ = (mid : ℝ) / 2 := by ring
  -- |k| ≤ |x|/mid + 1/2
  have hk_le : |(k : ℝ)| ≤ |(x : ℝ)| / (mid : ℝ) + 1 / 2 := by
    have h := abs_le.mp hround
    rw [abs_le]; constructor
    · rw [show -(|(x : ℝ)| / (mid : ℝ) + 1 / 2) = -|(x : ℝ)| / (mid : ℝ) - 1 / 2 from by ring]
      linarith [div_le_div_of_nonneg_right (neg_abs_le (x : ℝ)) hmid_pos.le, h.1]
    · linarith [div_le_div_of_nonneg_right (le_abs_self (x : ℝ)) hmid_pos.le, h.2]
  -- |k| < 2^N (key bound)
  have hk_lt_pow : |(k : ℝ)| < (2 : ℝ) ^ N := by
    have hx_le := rat_abs_le_natAbs x
    -- |k| ≤ |x|/mid + 1/2 ≤ a/mid + 1/2 ≤ 2*a + 1/2 (since mid ≥ 1/2)
    have ha_div : |(x : ℝ)| / (mid : ℝ) ≤ 2 * (x.num.natAbs : ℝ) := by
      calc |(x : ℝ)| / (mid : ℝ)
          ≤ (x.num.natAbs : ℝ) / (mid : ℝ) :=
            div_le_div_of_nonneg_right hx_le hmid_pos.le
        _ ≤ (x.num.natAbs : ℝ) / (1 / 2) := by
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) hmid_ge_half
        _ = 2 * (x.num.natAbs : ℝ) := by ring
    -- |k| ≤ 2*a + 1/2 < 2*(a+1)
    have hk_lt : |(k : ℝ)| < 2 * ((x.num.natAbs : ℝ) + 1) := by linarith
    -- 2^N ≥ 2^(log2(a+1)+1) * 2^(log2(b+1)+9) ≥ (a+1) * 2^9 = 512*(a+1)
    -- So 2*(a+1) ≤ 512*(a+1) ≤ 2^N
    -- a+1 ≤ 2^(log2(a+1)+1) ≤ 2^(N-1), so 2*(a+1) ≤ 2^N
    have hN_ge : Nat.log2 (x.num.natAbs + 1) + 1 + 1 ≤ N := by
      show Nat.log2 (x.num.natAbs + 1) + 2 ≤
        Nat.log2 (x.num.natAbs + 1) + Nat.log2 (x.den + 1) + 10
      omega
    have hpow_ge : x.num.natAbs + 1 ≤ 2 ^ (Nat.log2 (x.num.natAbs + 1) + 1) :=
      le_of_lt ((Nat.log2_lt (by omega)).mp (lt_add_one _))
    -- 2*(a+1) ≤ 2^(log2(a+1)+2) ≤ 2^N
    have h2a_le : 2 * (x.num.natAbs + 1) ≤ 2 ^ N := by
      calc 2 * (x.num.natAbs + 1)
          ≤ 2 * 2 ^ (Nat.log2 (x.num.natAbs + 1) + 1) := Nat.mul_le_mul_left 2 hpow_ge
        _ = 2 ^ (Nat.log2 (x.num.natAbs + 1) + 1 + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hN_ge
    calc |(k : ℝ)| < 2 * ((x.num.natAbs : ℝ) + 1) := hk_lt
      _ ≤ (2 : ℝ) ^ N := by exact_mod_cast h2a_le
  -- Combine: mid/2 + |k|/(2*2^N) < 1
  calc |(x : ℝ) - ↑k * Real.log 2|
      = |((x : ℝ) - (k : ℝ) * (mid : ℝ)) + ((k : ℝ) * ((mid : ℝ) - Real.log 2))| := by ring_nf
    _ ≤ |(x : ℝ) - (k : ℝ) * (mid : ℝ)| + |(k : ℝ) * ((mid : ℝ) - Real.log 2)| :=
        abs_add_le _ _
    _ ≤ (mid : ℝ) / 2 + |(k : ℝ)| * (1 / (2 * (2:ℝ) ^ N)) := by
        rw [abs_mul]; exact add_le_add hx_kmid
          (mul_le_mul_of_nonneg_left hmid_err (abs_nonneg _))
    _ < 1 := by
        -- |k| * (1/(2*2^N)) < 2^N * (1/(2*2^N)) = 1/2
        have h1 : |(k : ℝ)| * (1 / (2 * (2:ℝ) ^ N)) < (2:ℝ) ^ N * (1 / (2 * (2:ℝ) ^ N)) :=
          mul_lt_mul_of_pos_right hk_lt_pow (by positivity)
        have h2 : (2:ℝ) ^ N * (1 / (2 * (2:ℝ) ^ N)) = 1 / 2 := by field_simp
        linarith

end ExpComputable
