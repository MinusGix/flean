import Flean.Operations.Exp
import Flean.Operations.ExpTaylor
import Flean.NumberTheory.ExpEffectiveBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Computable exp: definitions and bracket correctness

Core computation definitions for `exp(x)` and proof that each successful
extraction step produces a correct sticky interval.

See `ExpComputable.lean` for the high-level architecture overview. This file contains:
- Constants (ln2 bounds, fuel, Taylor order)
- Computation definitions (argument reduction, Taylor bounds, extraction loop)
- `ExpRefExec` instance (the computable kernel)
- Basic properties (positivity, q bounds, exact-case handling)
- Floor/sticky interval arithmetic
- ln(2) series soundness and argument reduction correctness
- **Bracket correctness** (Thread 1): `expTryOne_sound`, `expExtractLoop_sound`
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
Quadratic in `|x.num|` to accommodate the effective irrationality measure from Padé
approximation (the Padé parameter `d = 4a²/b` requires `O(a²/b)` terms to converge).
Linear terms cover the shift `s`, ln2 precision, and base Taylor order.
The `log₂` factor ensures the fuel grows faster than `N₀ · log(N₀ · b)`,
which is the effective threshold for the factorial decay in the bracket width
to overcome the Padé irrationality denominator `D = N₀! · b^{N₀} · |P_{N₀}|`. -/
def expFuel (x : ℚ) : ℕ :=
  let ab := x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den + FloatFormat.prec.toNat + 100
  15 * ab * (Nat.log2 ab + 1) + 200

/-! ## Constants -/

/-- Number of Taylor terms. With mod-ln(2) reduction, `|r| ≤ ln(2)/2 < 1/2`,
so no input-dependent adjustment is needed. -/
def expNumTerms : ℕ := FloatFormat.prec.toNat + 10

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

/-! ## Sticky cell extraction -/

/-- Compute shift `s` from a positive rational, targeting `prec + 3` bits in `q`. -/
def expShift (r : ℚ) : ℕ :=
  let p := r.num.natAbs
  let d := r.den
  let targetBits := FloatFormat.prec.toNat + 4
  let s_int : ℤ := (targetBits : ℤ) + (Nat.log2 d : ℤ) - (Nat.log2 p : ℤ)
  s_int.toNat

/-- Extract `(q, e_base)` from lower and upper rational bounds for exp.

Given `lower ≤ exp(x) ≤ upper` where both are positive rationals,
finds `q, e_base` such that `exp(x) ∈ (2q·2^e_base, 2(q+1)·2^e_base)`.

Uses ⌊lower·2^s⌋ as `q`. Soundness requires that both `q_lo` and `q_hi`
(floors of lower and upper scaled by 2^s) agree, ensuring exp(x) is in cell q. -/
def expExtract (lower _upper : ℚ) : ExpRefOut :=
  let s := expShift lower
  let p_lo := lower.num.natAbs
  let d_lo := lower.den
  let q := p_lo * 2 ^ s / d_lo
  let e_base : ℤ := -((s : ℤ)) - 1
  { q := q, e_base := e_base, isExact := false }

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

/-- Try one extraction attempt at given precision level.
Returns `some result` if `⌊lower·2^s⌋ = ⌊upper·2^s⌋`, `none` otherwise. -/
def expTryOne (x : ℚ) (k : ℤ) (iter : ℕ) : Option ExpRefOut :=
  let (lower, upper) := expBounds x k iter
  let result := expExtract lower upper
  let s := expShift lower
  let q_hi := upper.num.natAbs * 2 ^ s / upper.den
  if result.q = q_hi then some result
  else none

/-- Iterative sticky cell extraction. Refines precision until cell agreement. -/
def expExtractLoop (x : ℚ) (k : ℤ) (iter : ℕ) : ℕ → ExpRefOut
  | 0 => { q := 0, e_base := 0, isExact := false }
  | fuel + 1 =>
    match expTryOne x k iter with
    | some r => r
    | none => expExtractLoop x k (iter + 1) fuel

/-! ## Main kernel -/

/-- Computable exp reference kernel (standard mod-ln(2) method).

For `a.m = 0` (input is ±0): returns exact result for `exp(0) = 1`.
Otherwise:
1. Reduce `x = k·ln(2) + r` with `k = round(x/ln(2))`
2. Iteratively refine ln(2) and Taylor bounds until cell agreement
3. Use directional Taylor bounds for `exp(r)`:
   - For `y ≥ 0`: lower bound = `T_N(y)`, upper bound = `T_N(y) + R_{N+1}(y)`
   - For `y < 0`: use `exp(y) = 1/exp(-y)` and bound `exp(-y)` instead
4. Extract sticky cell when `⌊lower·2^s⌋ = ⌊upper·2^s⌋` -/
def expComputableRun (a : FiniteFp) : ExpRefOut :=
  if a.m = 0 then
    -- exp(0) = 1 = 2 · 1 · 2^(-1)
    { q := 1, e_base := -1, isExact := true }
  else
    let x : ℚ := a.toVal
    let k := expArgRedK x
    expExtractLoop x k 0 (expFuel x)

instance (priority := 500) : ExpRefExec where
  run := expComputableRun

/-! ## Soundness helpers -/

/-- The lower bound passed to `expExtract` in the non-zero branch is positive. -/
theorem expComputableRun_lower_pos (a : FiniteFp) (_hm : a.m ≠ 0) :
    let x : ℚ := a.toVal
    let k := expArgRedK x
    let (r_lo, _r_hi) := expRInterval x k
    let N := expNumTerms
    let lower := expLowerBound r_lo N * (2 : ℚ) ^ k
    0 < lower := by
  simp only
  exact mul_pos (expLowerBound_pos _ _) (zpow_pos (by norm_num) _)

/-- The lower bound from `expBounds` is always positive. -/
theorem expBounds_lower_pos (x : ℚ) (k : ℤ) (iter : ℕ) :
    0 < (expBounds x k iter).1 := by
  simp only [expBounds]
  exact mul_pos (expLowerBound_pos _ _) (zpow_pos (by norm_num) _)

/-- `expExtract` always returns `isExact = false`. -/
theorem expExtract_isExact_false (lower upper : ℚ) :
    (expExtract lower upper).isExact = false := by
  simp [expExtract]

/-- Core arithmetic: with the log2-based shift, `p * 2^s / d ≥ 2^(prec+3)`. -/
theorem initial_q_ge_minQ (p d : ℕ) (hp : 0 < p) (hd : 0 < d) :
    let s_int : ℤ := ((FloatFormat.prec.toNat + 4 : ℕ) : ℤ) +
      ((Nat.log2 d : ℕ) : ℤ) - ((Nat.log2 p : ℕ) : ℤ)
    2 ^ (FloatFormat.prec.toNat + 3) ≤ p * 2 ^ s_int.toNat / d := by
  simp only
  set prec2 := FloatFormat.prec.toNat + 3
  set lp := Nat.log2 p
  set ld := Nat.log2 d
  set s_int : ℤ := ((prec2 + 1 : ℕ) : ℤ) + (ld : ℤ) - (lp : ℤ)
  set s := s_int.toNat
  have hp_ne : p ≠ 0 := by omega
  have hd_ne : d ≠ 0 := by omega
  have hlp : 2 ^ lp ≤ p := Nat.log2_self_le hp_ne
  have hdlt : d < 2 ^ (ld + 1) := (Nat.log2_lt hd_ne).mp (Nat.lt_succ_of_le (le_refl ld))
  rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
  by_cases hs : (0 : ℤ) ≤ s_int
  · have hlp_le : lp ≤ prec2 + 1 + ld := by omega
    have hs_eq : s = prec2 + 1 + ld - lp := by omega
    have key : 2 ^ (prec2 + 1 + ld) ≤ p * 2 ^ s := by
      calc 2 ^ (prec2 + 1 + ld)
          = 2 ^ (lp + (prec2 + 1 + ld - lp)) := by congr 1; omega
        _ = 2 ^ lp * 2 ^ (prec2 + 1 + ld - lp) := by rw [Nat.pow_add]
        _ ≤ p * 2 ^ s := by rw [hs_eq]; exact Nat.mul_le_mul_right _ hlp
    exact le_of_lt (calc 2 ^ prec2 * d
        < 2 ^ prec2 * 2 ^ (ld + 1) :=
          Nat.mul_lt_mul_of_pos_left hdlt (by positivity)
      _ = 2 ^ (prec2 + 1 + ld) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ p * 2 ^ s := key)
  · push_neg at hs
    have hs_eq : s = 0 := Int.toNat_eq_zero.mpr (le_of_lt hs)
    rw [hs_eq, Nat.pow_zero, Nat.mul_one]
    have step1 : 2 ^ prec2 * d < 2 ^ (prec2 + ld + 1) := by
      calc 2 ^ prec2 * d < 2 ^ prec2 * 2 ^ (ld + 1) :=
            Nat.mul_lt_mul_of_pos_left hdlt (by positivity)
        _ = 2 ^ (prec2 + (ld + 1)) := by rw [← Nat.pow_add]
        _ = 2 ^ (prec2 + ld + 1) := by ring_nf
    have step2 : prec2 + ld + 1 ≤ lp := by omega
    exact le_of_lt (lt_of_lt_of_le step1
      (le_trans (Nat.pow_le_pow_right (by omega) step2) hlp))

/-- `expShift`-based q for a positive rational is ≥ 2^(prec+3). -/
theorem expShift_q_ge (r : ℚ) (hpos : 0 < r) :
    let p := r.num.natAbs
    let d := r.den
    let s := expShift r
    2 ^ (FloatFormat.prec.toNat + 3) ≤ p * 2 ^ s / d := by
  have hp : 0 < r.num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hpos))
  exact initial_q_ge_minQ r.num.natAbs r.den hp r.den_pos

/-- `expExtract` produces `q ≥ 2^(prec+2)` for positive lower bound. -/
theorem expExtract_q_ge (lower upper : ℚ) (hpos : 0 < lower) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ (expExtract lower upper).q := by
  have hraw := expShift_q_ge lower hpos
  simp only at hraw
  simp only [expExtract]
  have : 2 ^ (FloatFormat.prec.toNat + 2) ≤ 2 ^ (FloatFormat.prec.toNat + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- When `expTryOne` succeeds, the result has `isExact = false`. -/
theorem expTryOne_isExact (x : ℚ) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
    (h : expTryOne x k iter = some r) : r.isExact = false := by
  simp only [expTryOne] at h
  split_ifs at h
  all_goals first | contradiction | (simp at h; subst h; rfl)

/-- The extraction loop always returns `isExact = false`. -/
theorem expExtractLoop_isExact_false (x : ℚ) (k : ℤ) (iter fuel : ℕ) :
    (expExtractLoop x k iter fuel).isExact = false := by
  induction fuel generalizing iter with
  | zero => rfl
  | succ n ih =>
    simp only [expExtractLoop]
    match hm : expTryOne x k iter with
    | some r => exact expTryOne_isExact x k iter r hm
    | none => exact ih (iter + 1)

/-- When `isExact = true`, we must be in the zero branch. -/
theorem expComputableRun_exact_is_zero (a : FiniteFp)
    (hExact : (expComputableRun a).isExact = true) : a.m = 0 := by
  by_contra h
  have : (expComputableRun a).isExact = false := by
    simp only [expComputableRun, h, ↓reduceIte]
    exact expExtractLoop_isExact_false _ _ _ _
  rw [this] at hExact; exact absurd hExact (by decide)

/-- In the zero branch, the output is `{q := 1, e_base := -1, isExact := true}`. -/
theorem expComputableRun_zero (a : FiniteFp) (hm : a.m = 0) :
    expComputableRun a = { q := 1, e_base := -1, isExact := true } := by
  simp [expComputableRun, hm]

/-! ## Sticky interval from floor + error bounds -/

omit [FloatFormat] in
/-- If `lower < v ≤ upper` and both `⌊lower·2^s⌋ = ⌊upper·2^s⌋ = q`,
then `v ∈ (q·2^(-s), (q+1)·2^(-s))` i.e. `inStickyInterval q (-(s+1)) v`. -/
theorem inStickyInterval_of_bracket
    (lower upper : ℚ) (hl_pos : 0 < lower) (v : ℝ) (s : ℕ)
    (hv_lower : (lower : ℝ) < v)
    (hv_upper : v ≤ (upper : ℝ))
    (hq_agree : lower.num.natAbs * 2 ^ s / lower.den =
      upper.num.natAbs * 2 ^ s / upper.den) :
    let q := lower.num.natAbs * 2 ^ s / lower.den
    inStickyInterval (R := ℝ) q (-((s : ℤ)) - 1) v := by
  simp only
  set p_lo := lower.num.natAbs
  set d_lo := lower.den
  set p_hi := upper.num.natAbs
  set d_hi := upper.den
  set q := p_lo * 2 ^ s / d_lo
  have hd_lo : 0 < d_lo := lower.den_pos
  have hd_hi : 0 < d_hi := upper.den_pos
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hu_pos : 0 < upper := lt_of_lt_of_le hl_pos (by exact_mod_cast le_of_lt (lt_of_lt_of_le hv_lower hv_upper))
  have hq_le_lower : (q : ℝ) / (2 : ℝ) ^ s ≤ (lower : ℝ) := by
    rw [div_le_iff₀ h2s_pos, Rat.cast_eq_natAbs_div_den lower hl_pos, div_mul_eq_mul_div,
      le_div_iff₀ (Nat.cast_pos.mpr hd_lo)]
    exact_mod_cast nat_floor_div_mul_le p_lo d_lo s
  have hupper_lt : (upper : ℝ) < ((q : ℝ) + 1) / (2 : ℝ) ^ s := by
    rw [lt_div_iff₀ h2s_pos, Rat.cast_eq_natAbs_div_den upper hu_pos, div_mul_eq_mul_div,
      div_lt_iff₀ (Nat.cast_pos.mpr hd_hi)]
    have hq_eq : q = p_hi * 2 ^ s / d_hi := hq_agree
    rw [hq_eq]
    exact_mod_cast real_lt_nat_floor_div_succ_mul p_hi d_hi s hd_hi
  constructor
  · rw [two_mul_zpow_neg_succ, show (q : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) =
      (q : ℝ) / (2 : ℝ) ^ s from by rw [zpow_neg, zpow_natCast]; ring]
    exact lt_of_le_of_lt hq_le_lower hv_lower
  · rw [two_mul_zpow_neg_succ, show ((q : ℝ) + 1) * (2 : ℝ) ^ (-(s : ℤ)) =
      ((q : ℝ) + 1) / (2 : ℝ) ^ s from by rw [zpow_neg, zpow_natCast]; ring]
    exact lt_of_le_of_lt hv_upper hupper_lt

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
    have h2_10_le : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ N :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 10 ≤ N)
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

/-! ## Soundness -/

theorem expComputableRun_exact_mag_ne_zero (a : FiniteFp) (o : ExpRefOut)
    (hr : expComputableRun a = o) (hExact : o.isExact = true) : o.q ≠ 0 := by
  have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
  rw [expComputableRun_zero a hm] at hr
  subst hr
  norm_num

theorem expComputableRun_exact_value (a : FiniteFp) (o : ExpRefOut)
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

/-! ## Loop output properties -/

/-- When `expTryOne` succeeds, the q satisfies q ≥ 2^(prec+2).
This follows from the `expShift` arithmetic: the shift is chosen so that
the scaled value has enough bits. -/
theorem expTryOne_q_ge (x : ℚ) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
    (hr : expTryOne x k iter = some r)
    (hpos : 0 < r.q) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ r.q := by
  simp only [expTryOne] at hr
  split_ifs at hr with heq
  obtain rfl := Option.some.inj hr
  exact expExtract_q_ge _ _ (expBounds_lower_pos x k iter)

/-- For the extraction loop: if q > 0, then q ≥ 2^(prec+2). -/
theorem expExtractLoop_q_ge (x : ℚ) (k : ℤ) (iter fuel : ℕ)
    (hq : 0 < (expExtractLoop x k iter fuel).q) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ (expExtractLoop x k iter fuel).q := by
  induction fuel generalizing iter with
  | zero => simp [expExtractLoop] at hq
  | succ n ih =>
    simp only [expExtractLoop] at hq ⊢
    match hm : expTryOne x k iter with
    | some r =>
      simp [hm] at hq ⊢
      exact expTryOne_q_ge x k iter r hm hq
    | none =>
      simp [hm] at hq ⊢
      exact ih (iter + 1) hq

/-! ## Loop termination and soundness via irrationality -/

/-- When `expTryOne` succeeds, the result has positive `q`.
This follows from `expExtract_q_ge` + `expBounds_lower_pos` without any additional hypothesis. -/
theorem expTryOne_q_pos (x : ℚ) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
    (hr : expTryOne x k iter = some r) :
    0 < r.q := by
  have h1 : 2 ^ (FloatFormat.prec.toNat + 2) ≤ r.q := by
    simp only [expTryOne] at hr
    split_ifs at hr with heq
    obtain rfl := Option.some.inj hr
    exact expExtract_q_ge _ _ (expBounds_lower_pos x k iter)
  have h2 : 0 < 2 ^ (FloatFormat.prec.toNat + 2) := Nat.pos_of_ne_zero (by positivity)
  omega

/-- If some iteration in `[start, start + fuel)` succeeds, the loop returns positive `q`.
Proved by induction on fuel: either the current iteration succeeds (giving `q > 0`),
or we recurse to a later iteration. -/
theorem expExtractLoop_pos_of_success (x : ℚ) (k : ℤ) (start fuel : ℕ)
    (hsuccess : ∃ n, start ≤ n ∧ n < start + fuel ∧
      (expTryOne x k n).isSome = true) :
    0 < (expExtractLoop x k start fuel).q := by
  induction fuel generalizing start with
  | zero => obtain ⟨_, _, hlt, _⟩ := hsuccess; omega
  | succ fuel ih =>
    simp only [expExtractLoop]
    match hm : expTryOne x k start with
    | some r =>
      simp
      exact expTryOne_q_pos x k start r hm
    | none =>
      simp
      apply ih (start + 1)
      obtain ⟨n, hge, hlt, hn⟩ := hsuccess
      refine ⟨n, ?_, by omega, hn⟩
      by_cases h : n = start
      · subst h; simp [hm] at hn
      · omega

/-- If the loop encounters a successful `expTryOne` at any iteration, it returns that result. -/
theorem expExtractLoop_of_isSome (x : ℚ) (k : ℤ) (iter fuel : ℕ)
    (h : (expTryOne x k iter).isSome)
    (hfuel : 0 < fuel) :
    expExtractLoop x k iter fuel = (expTryOne x k iter).get h := by
  match fuel, hfuel with
  | fuel + 1, _ =>
    simp only [expExtractLoop]
    have := Option.isSome_iff_exists.mp h
    obtain ⟨r, hr⟩ := this
    simp [hr]

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
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
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
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
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

/-- When `expTryOne` succeeds, the result is in the correct sticky interval. -/
theorem expTryOne_sound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
    (hr : expTryOne x k iter = some r)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    inStickyInterval (R := ℝ) r.q r.e_base (Real.exp (x : ℝ)) := by
  simp only [expTryOne] at hr
  split_ifs at hr with heq
  obtain rfl := Option.some.inj hr
  -- r = expExtract lower upper with q_lo = q_hi
  set lower := (expBounds x k iter).1
  set upper := (expBounds x k iter).2
  have hl_pos := expBounds_lower_pos x k iter
  have hlower_lt := expBounds_lower_lt_exp x hx k iter hk_bound
  have hupper_le := expBounds_exp_le_upper x k iter hk_bound
  exact inStickyInterval_of_bracket lower upper hl_pos (Real.exp (x : ℝ))
    (expShift lower) hlower_lt hupper_le heq

/-- When the loop finds a result via `expTryOne`, that result satisfies inStickyInterval. -/
theorem expExtractLoop_sound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter fuel : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1)
    (hq : 0 < (expExtractLoop x k iter fuel).q) :
    inStickyInterval (R := ℝ) (expExtractLoop x k iter fuel).q
      (expExtractLoop x k iter fuel).e_base (Real.exp (x : ℝ)) := by
  induction fuel generalizing iter with
  | zero => simp [expExtractLoop] at hq
  | succ n ih =>
    simp only [expExtractLoop] at hq ⊢
    match hm : expTryOne x k iter with
    | some r =>
      simp [hm] at hq ⊢
      exact expTryOne_sound x hx k iter r hm hk_bound
    | none =>
      simp [hm] at hq ⊢
      exact ih (iter + 1) hq


end ExpComputable
