import Flean.Operations.Exp
import Flean.NumberTheory.ExpEffectiveBound
import Flean.NumberTheory.PadeExp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Computable `ExpRefExec` and `ExpRefExecSound` Instances

Evaluates `exp(x)` using rational Taylor series with standard argument reduction:

1. Convert input to `ℚ` via `FiniteFp.toVal`
2. Reduce argument mod ln(2): `exp(x) = 2^k · exp(r)` with `|r| ≤ ln(2)/2`
3. Taylor series for `exp(r)` with `|r| ≤ ln(2)/2 < 1` (fast convergence)
4. Reconstruct via exponent shift (exact — no error amplification)
5. Extract sticky cell `(q, e_base)` via iterative refinement until cell agreement

All four `ExpRefExecSound` obligations are proved modulo the termination claim:
- `expTryOne_terminates`: the successful iteration is within `expFuel x` steps
  (requires an effective irrationality measure — Padé scaffolding in `PadeExp.lean`)
-/

section ExpComputable

variable [FloatFormat]

/-! ## Constants -/

/-- Rational lower bound for `Real.log 2`. From mathlib: `0.6931471803 < Real.log 2`. -/
private def ln2_lo : ℚ := 6931471803 / 10000000000

/-- Rational upper bound for `Real.log 2`. From mathlib: `Real.log 2 < 0.6931471808`. -/
private def ln2_hi : ℚ := 6931471808 / 10000000000

/-! ## Adaptive ln(2) bounds -/

/-- Partial sum of the series `ln(2) = Σ_{k=1}^∞ 1/(k·2^k)`.
Gives a lower bound: `ln2SeriesSum N ≤ ln(2)`. -/
private def ln2SeriesSum (N : ℕ) : ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ
    | 0, _, acc => acc
    | fuel + 1, k, acc => go fuel (k + 1) (acc + 1 / ((k + 1 : ℚ) * 2 ^ (k + 1)))
  go N 0 0

omit [FloatFormat] in
private theorem ln2SeriesSum_go_ge_acc : ∀ fuel k (acc : ℚ),
    acc ≤ ln2SeriesSum.go fuel k acc := by
  intro fuel; induction fuel with
  | zero => intro k acc; exact le_refl _
  | succ n ih =>
    intro k acc; simp only [ln2SeriesSum.go]
    linarith [ih (k + 1) (acc + 1 / ((k + 1 : ℚ) * 2 ^ (k + 1))),
      show (0 : ℚ) ≤ 1 / ((↑k + 1) * 2 ^ (k + 1)) from by positivity]

omit [FloatFormat] in
private theorem ln2SeriesSum_nonneg (N : ℕ) : (0 : ℚ) ≤ ln2SeriesSum N :=
  ln2SeriesSum_go_ge_acc N 0 0

omit [FloatFormat] in
private theorem ln2SeriesSum_ge_half (N : ℕ) (hN : 1 ≤ N) :
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
Linear terms cover the shift `s`, ln2 precision, and base Taylor order. -/
private def expFuel (x : ℚ) : ℕ :=
  x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den + FloatFormat.prec.toNat * 3 + 200

/-! ## Taylor series -/

/-- Number of Taylor terms. With mod-ln(2) reduction, `|r| ≤ ln(2)/2 < 1/2`,
so no input-dependent adjustment is needed. -/
private def expNumTerms : ℕ := FloatFormat.prec.toNat + 10

/-- Evaluate `exp(y) ≈ Σ_{k=0}^{numTerms} y^k/k!` in ℚ.
Uses forward recurrence `term_{k+1} = term_k · y / (k+1)`.
All terms are positive when `y > 0`, guaranteeing a lower bound. -/
private def taylorExpQ (y : ℚ) (numTerms : ℕ) : ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ → ℚ
    | 0, _, acc, _ => acc
    | fuel + 1, k, acc, term =>
        let nextTerm := term * y / (k + 1)
        go fuel (k + 1) (acc + nextTerm) nextTerm
  go numTerms 0 1 1  -- start: k=0, acc=1 (term_0), term=1 (term_0)

/-! ## Taylor remainder -/

/-- Compute the Taylor remainder bound: `y^N * (N+1) / (N! * N)`.
This bounds `|exp(y) - ∑_{k<N} y^k/k!|` for `|y| ≤ 1`.
For our use: exp(y) ≤ taylorExpQ y (N-1) + taylorRemainder y N. -/
private def taylorRemainder (y : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 1  -- degenerate case
  else y ^ n * (n + 1) / (n.factorial * n)

/-! ## Argument reduction mod ln(2) -/

/-- Compute `k = round(x / ln(2))` using adaptive ln2 bounds.
Uses enough ln2 precision that `|x - k·log(2)| < 1`. -/
private def expArgRedK (x : ℚ) : ℤ :=
  -- Use enough bits of ln2 so |k|·(error in ln2) < 1/4
  -- |k| ≤ |x/log2| + 1 ≤ 2·|x| + 1, so need N_ln2 bits where
  -- (2·|x|+1) / 2^N_ln2 < 1/4, i.e., 2^N_ln2 > 4·(2·|x|+1)
  let N_ln2 := Nat.log2 (x.num.natAbs + 1) + Nat.log2 (x.den + 1) + 10
  let ln2_mid := ln2SeriesSum N_ln2 + 1 / (2 * 2 ^ N_ln2)
  round (x / ln2_mid)

/-- Compute a rational interval `[r_lo, r_hi]` containing `x - k·ln(2)`.
Since `ln(2)` is irrational, we bracket it using `ln2_lo < ln(2) < ln2_hi`. -/
private def expRInterval (x : ℚ) (k : ℤ) : ℚ × ℚ :=
  if 0 ≤ k then
    -- k·ln2_lo ≤ k·ln(2) ≤ k·ln2_hi, so x - k·ln2_hi ≤ r ≤ x - k·ln2_lo
    (x - k * ln2_hi, x - k * ln2_lo)
  else
    -- k < 0: k·ln2_hi ≤ k·ln(2) ≤ k·ln2_lo, so x - k·ln2_lo ≤ r ≤ x - k·ln2_hi
    (x - k * ln2_lo, x - k * ln2_hi)

/-! ## Sticky cell extraction -/

/-- Compute shift `s` from a positive rational, targeting `prec + 3` bits in `q`. -/
private def expShift (r : ℚ) : ℕ :=
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
private def expExtract (lower _upper : ℚ) : ExpRefOut :=
  let s := expShift lower
  let p_lo := lower.num.natAbs
  let d_lo := lower.den
  let q := p_lo * 2 ^ s / d_lo
  let e_base : ℤ := -((s : ℤ)) - 1
  { q := q, e_base := e_base, isExact := false }

/-- Compute r interval using adaptive ln2 bounds. -/
private def expRIntervalWith (x : ℚ) (k : ℤ) (lo2 hi2 : ℚ) : ℚ × ℚ :=
  if 0 ≤ k then (x - k * hi2, x - k * lo2)
  else (x - k * lo2, x - k * hi2)

/-- Compute the Taylor lower/upper bounds for `exp(x)` at given precision level.
Returns `(lower, upper)` such that `lower ≤ exp(x) ≤ upper`. -/
private def expBounds (x : ℚ) (k : ℤ) (iter : ℕ) : ℚ × ℚ :=
  let N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
  let s_ln2 := ln2SeriesSum N_ln2
  let lo2 := s_ln2
  let hi2 := s_ln2 + 1 / 2 ^ N_ln2
  let (r_lo, r_hi) := expRIntervalWith x k lo2 hi2
  let N := expNumTerms + iter * 10
  let lower_r :=
    if 0 ≤ r_lo then taylorExpQ r_lo N
    else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))
  let upper_r :=
    if 0 ≤ r_hi then taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)
    else 1 / taylorExpQ (-r_hi) N
  (lower_r * (2 : ℚ) ^ k, upper_r * (2 : ℚ) ^ k)

/-- Try one extraction attempt at given precision level.
Returns `some result` if `⌊lower·2^s⌋ = ⌊upper·2^s⌋`, `none` otherwise. -/
private def expTryOne (x : ℚ) (k : ℤ) (iter : ℕ) : Option ExpRefOut :=
  let (lower, upper) := expBounds x k iter
  let result := expExtract lower upper
  let s := expShift lower
  let q_hi := upper.num.natAbs * 2 ^ s / upper.den
  if result.q = q_hi then some result
  else none

/-- Iterative sticky cell extraction. Refines precision until cell agreement. -/
private def expExtractLoop (x : ℚ) (k : ℤ) (iter : ℕ) : ℕ → ExpRefOut
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

omit [FloatFormat] in
/-- Taylor series with nonneg input gives result ≥ 1 (since first term is 1 and rest are nonneg). -/
private theorem taylorExpQ_ge_one (y : ℚ) (hy : 0 ≤ y) (n : ℕ) :
    1 ≤ taylorExpQ y n := by
  simp only [taylorExpQ]
  -- The recursive function accumulates nonneg terms starting from acc=1
  suffices ∀ fuel k (acc term : ℚ), 1 ≤ acc → 0 ≤ term →
    1 ≤ taylorExpQ.go y fuel k acc term from
    this n 0 1 1 (le_refl _) (by norm_num)
  intro fuel
  induction fuel with
  | zero => simp [taylorExpQ.go]; intros; assumption
  | succ n ih =>
    intro k acc term hacc hterm
    simp only [taylorExpQ.go]
    have hnext : 0 ≤ term * y / (↑k + 1) :=
      div_nonneg (mul_nonneg hterm hy) (by positivity)
    exact ih _ _ _ (by linarith) hnext

/-- The lower bound passed to `expExtract` in the non-zero branch is positive. -/
private theorem expComputableRun_lower_pos (a : FiniteFp) (_hm : a.m ≠ 0) :
    let x : ℚ := a.toVal
    let k := expArgRedK x
    let (r_lo, _r_hi) := expRInterval x k
    let N := expNumTerms
    let lower_r := if 0 ≤ r_lo then taylorExpQ r_lo N
      else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))
    let lower := lower_r * (2 : ℚ) ^ k
    0 < lower := by
  simp only
  apply mul_pos _ (zpow_pos (by norm_num) _)
  set r_lo := (expRInterval (a.toVal (R := ℚ)) (expArgRedK (a.toVal (R := ℚ)))).1
  split
  · -- r_lo ≥ 0: taylorExpQ r_lo N ≥ 1 > 0
    case isTrue h =>
      exact lt_of_lt_of_le (by norm_num) (taylorExpQ_ge_one _ h _)
  · -- r_lo < 0: 1 / (ty + rem) > 0 since ty + rem > 0
    case isFalse h =>
      push_neg at h
      have habs : 0 ≤ -r_lo := by linarith
      have hty_ge := taylorExpQ_ge_one (-r_lo) habs expNumTerms
      have hty_pos : 0 < taylorExpQ (-r_lo) expNumTerms := lt_of_lt_of_le (by norm_num) hty_ge
      have hrem_nonneg : 0 ≤ taylorRemainder (-r_lo) (expNumTerms + 1) := by
        unfold taylorRemainder
        simp only [show expNumTerms + 1 ≠ 0 from by unfold expNumTerms; omega, ↓reduceIte]
        apply div_nonneg
        · exact mul_nonneg (pow_nonneg habs _) (by positivity)
        · positivity
      exact div_pos one_pos (lt_of_lt_of_le hty_pos (le_add_of_nonneg_right hrem_nonneg))

/-- The lower bound from `expBounds` is always positive. -/
private theorem expBounds_lower_pos (x : ℚ) (k : ℤ) (iter : ℕ) :
    0 < (expBounds x k iter).1 := by
  simp only [expBounds]
  apply mul_pos _ (zpow_pos (by norm_num) _)
  set r_lo := (expRIntervalWith x k _ _).1
  split
  · case isTrue h =>
      exact lt_of_lt_of_le (by norm_num) (taylorExpQ_ge_one _ h _)
  · case isFalse h =>
      push_neg at h
      have habs : 0 ≤ -r_lo := by linarith
      set N := expNumTerms + iter * 10
      have hty_ge := taylorExpQ_ge_one (-r_lo) habs N
      have hty_pos : 0 < taylorExpQ (-r_lo) N := lt_of_lt_of_le (by norm_num) hty_ge
      have hrem_nonneg : 0 ≤ taylorRemainder (-r_lo) (N + 1) := by
        unfold taylorRemainder
        simp only [show N + 1 ≠ 0 from by omega, ↓reduceIte]
        exact div_nonneg (mul_nonneg (pow_nonneg habs _) (by positivity)) (by positivity)
      exact div_pos one_pos (lt_of_lt_of_le hty_pos (le_add_of_nonneg_right hrem_nonneg))

/-! ## Taylor series ↔ Finset.sum bridge -/

omit [FloatFormat] in
open Finset in
/-- Loop invariant: when `term = y^k/k!` and `acc = ∑_{i<k+1} y^i/i!`,
the loop computes `∑_{i<k+fuel+1} y^i/i!`. -/
private theorem taylorExpQ_go_eq (y : ℚ) :
    ∀ (fuel k : ℕ) (acc term : ℚ),
    term = y ^ k / (k.factorial : ℚ) →
    acc = ∑ i ∈ range (k + 1), y ^ i / (i.factorial : ℚ) →
    taylorExpQ.go y fuel k acc term =
      ∑ i ∈ range (k + fuel + 1), y ^ i / (i.factorial : ℚ) := by
  intro fuel
  induction fuel with
  | zero => intro k acc term _ hacc; simp [taylorExpQ.go, hacc]
  | succ n ih =>
    intro k acc term hterm hacc
    simp only [taylorExpQ.go]
    -- Next term: term * y / (k+1) = y^(k+1) / (k+1)!
    have hterm_next : term * y / (↑k + 1) = y ^ (k + 1) / ((k + 1).factorial : ℚ) := by
      rw [hterm, pow_succ, Nat.factorial_succ, Nat.cast_mul]
      have : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have : (↑k + 1 : ℚ) ≠ 0 := by positivity
      field_simp; push_cast; ring
    -- Updated acc: acc + nextTerm = ∑_{i<k+2}
    have hacc_next : acc + term * y / (↑k + 1) =
        ∑ i ∈ range (k + 1 + 1), y ^ i / (i.factorial : ℚ) := by
      rw [sum_range_succ, hacc, hterm_next]
    rw [ih (k + 1) _ _ hterm_next hacc_next,
      show k + 1 + n + 1 = k + (n + 1) + 1 from by omega]

omit [FloatFormat] in
open Finset in
/-- `taylorExpQ y n` equals the standard Taylor partial sum `∑_{k<n+1} y^k/k!` in ℚ. -/
private theorem taylorExpQ_eq_sum (y : ℚ) (n : ℕ) :
    taylorExpQ y n = ∑ k ∈ range (n + 1), y ^ k / (k.factorial : ℚ) := by
  simp only [taylorExpQ]
  have hterm : (1 : ℚ) = y ^ 0 / (Nat.factorial 0 : ℚ) := by simp
  have hacc : (1 : ℚ) = ∑ i ∈ range (0 + 1), y ^ i / (i.factorial : ℚ) := by
    rw [sum_range_one]; simp
  rw [taylorExpQ_go_eq y n 0 1 1 hterm hacc, show 0 + n + 1 = n + 1 from by omega]

omit [FloatFormat] in
open Finset in
/-- Cast of `taylorExpQ` to ℝ equals the real Taylor partial sum. -/
private theorem taylorExpQ_cast_eq_sum (y : ℚ) (n : ℕ) :
    (taylorExpQ y n : ℝ) = ∑ k ∈ range (n + 1), (y : ℝ) ^ k / (k.factorial : ℝ) := by
  rw [taylorExpQ_eq_sum]; push_cast; rfl

omit [FloatFormat] in
/-- The real Taylor partial sum lower-bounds `exp` for nonneg arguments. -/
private theorem taylorExpQ_le_exp (y : ℚ) (hy : 0 ≤ y) (n : ℕ) :
    (taylorExpQ y n : ℝ) ≤ Real.exp (y : ℝ) := by
  rw [taylorExpQ_cast_eq_sum]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hy) _

/-- `expExtract` always returns `isExact = false`. -/
private theorem expExtract_isExact_false (lower upper : ℚ) :
    (expExtract lower upper).isExact = false := by
  simp [expExtract]

/-- Core arithmetic: with the log2-based shift, `p * 2^s / d ≥ 2^(prec+3)`. -/
private theorem initial_q_ge_minQ (p d : ℕ) (hp : 0 < p) (hd : 0 < d) :
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
private theorem expShift_q_ge (r : ℚ) (hpos : 0 < r) :
    let p := r.num.natAbs
    let d := r.den
    let s := expShift r
    2 ^ (FloatFormat.prec.toNat + 3) ≤ p * 2 ^ s / d := by
  have hp : 0 < r.num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hpos))
  exact initial_q_ge_minQ r.num.natAbs r.den hp r.den_pos

/-- `expExtract` produces `q ≥ 2^(prec+2)` for positive lower bound. -/
private theorem expExtract_q_ge (lower upper : ℚ) (hpos : 0 < lower) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ (expExtract lower upper).q := by
  have hraw := expShift_q_ge lower hpos
  simp only at hraw
  simp only [expExtract]
  have : 2 ^ (FloatFormat.prec.toNat + 2) ≤ 2 ^ (FloatFormat.prec.toNat + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- When `expTryOne` succeeds, the result has `isExact = false`. -/
private theorem expTryOne_isExact (x : ℚ) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
    (h : expTryOne x k iter = some r) : r.isExact = false := by
  simp only [expTryOne] at h
  split_ifs at h
  all_goals first | contradiction | (simp at h; subst h; rfl)

/-- The extraction loop always returns `isExact = false`. -/
private theorem expExtractLoop_isExact_false (x : ℚ) (k : ℤ) (iter fuel : ℕ) :
    (expExtractLoop x k iter fuel).isExact = false := by
  induction fuel generalizing iter with
  | zero => rfl
  | succ n ih =>
    simp only [expExtractLoop]
    match hm : expTryOne x k iter with
    | some r => exact expTryOne_isExact x k iter r hm
    | none => exact ih (iter + 1)

/-- When `isExact = true`, we must be in the zero branch. -/
private theorem expComputableRun_exact_is_zero (a : FiniteFp)
    (hExact : (expComputableRun a).isExact = true) : a.m = 0 := by
  by_contra h
  have : (expComputableRun a).isExact = false := by
    simp only [expComputableRun, h, ↓reduceIte]
    exact expExtractLoop_isExact_false _ _ _ _
  rw [this] at hExact; exact absurd hExact (by decide)

/-- In the zero branch, the output is `{q := 1, e_base := -1, isExact := true}`. -/
private theorem expComputableRun_zero (a : FiniteFp) (hm : a.m = 0) :
    expComputableRun a = { q := 1, e_base := -1, isExact := true } := by
  simp [expComputableRun, hm]

/-! ## Strict Taylor inequality -/

omit [FloatFormat] in
/-- The Taylor partial sum is STRICTLY less than exp for y > 0.
This follows because all omitted terms y^k/k! for k > N are strictly positive. -/
private theorem taylorExpQ_lt_exp (y : ℚ) (hy : 0 < y) (n : ℕ) :
    (taylorExpQ y n : ℝ) < Real.exp (y : ℝ) := by
  have hy_real : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hterm : (0 : ℝ) < (y : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    div_pos (pow_pos hy_real _) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  have hle2 := Real.sum_le_exp_of_nonneg (le_of_lt hy_real) (n + 2)
  rw [show n + 2 = n + 1 + 1 from by omega, Finset.sum_range_succ] at hle2
  rw [taylorExpQ_cast_eq_sum]
  linarith

/-! ## Floor / cell extraction properties -/

omit [FloatFormat] in
/-- Nat floor division gives a lower bound in ℝ. -/
private theorem nat_floor_div_mul_le (p d s : ℕ) :
    ((p * 2 ^ s / d : ℕ) : ℝ) * (d : ℝ) ≤ (p : ℝ) * 2 ^ s := by
  have := Nat.div_mul_le_self (p * 2 ^ s) d
  exact_mod_cast this

omit [FloatFormat] in
/-- Nat floor division gives a strict upper bound in ℝ. -/
private theorem real_lt_nat_floor_div_succ_mul (p d s : ℕ) (hd : 0 < d) :
    (p : ℝ) * 2 ^ s < ((p * 2 ^ s / d + 1 : ℕ) : ℝ) * (d : ℝ) := by
  set a := p * 2 ^ s
  have h2 : a % d < d := Nat.mod_lt _ hd
  have h3 : d * (a / d) + a % d = a := Nat.div_add_mod a d
  have h4 : a < (a / d + 1) * d := by nlinarith
  exact_mod_cast h4

/-! ## Sticky interval from floor + error bounds -/

omit [FloatFormat] in
/-- `2 * x * 2^(-(s+1)) = x * 2^(-s)` for `s : ℤ`. -/
private theorem two_mul_zpow_neg_succ (x : ℝ) (s : ℤ) :
    2 * x * (2 : ℝ) ^ (-s - 1) = x * (2 : ℝ) ^ (-s) := by
  rw [show -s - 1 = -s + (-1) from by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  ring

omit [FloatFormat] in
/-- If `lower < v ≤ upper` and both `⌊lower·2^s⌋ = ⌊upper·2^s⌋ = q`,
then `v ∈ (q·2^(-s), (q+1)·2^(-s))` i.e. `inStickyInterval q (-(s+1)) v`. -/
private theorem inStickyInterval_of_bracket
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
  have cast_eq (r : ℚ) (hr : 0 < r) :
      (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
    have hnum : r.num = (r.num.natAbs : ℤ) :=
      (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hr))).symm
    have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      push_cast [Rat.cast_def]; ring
    rw [h1, show (r.num : ℝ) = (r.num.natAbs : ℝ) from by rw [hnum]; simp]
  have hu_pos : 0 < upper := lt_of_lt_of_le hl_pos (by exact_mod_cast le_of_lt (lt_of_lt_of_le hv_lower hv_upper))
  have hq_le_lower : (q : ℝ) / (2 : ℝ) ^ s ≤ (lower : ℝ) := by
    rw [div_le_iff₀ h2s_pos, cast_eq lower hl_pos, div_mul_eq_mul_div,
      le_div_iff₀ (Nat.cast_pos.mpr hd_lo)]
    exact_mod_cast nat_floor_div_mul_le p_lo d_lo s
  have hupper_lt : (upper : ℝ) < ((q : ℝ) + 1) / (2 : ℝ) ^ s := by
    rw [lt_div_iff₀ h2s_pos, cast_eq upper hu_pos, div_mul_eq_mul_div,
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

/-! ## Taylor upper bound (remainder covers gap) -/

omit [FloatFormat] in
/-- `taylorRemainder y (N+1)` as a real equals the standard bound form. -/
private theorem taylorRemainder_cast (y : ℚ) (N : ℕ) (hN : 0 < N) :
    (taylorRemainder y (N + 1) : ℝ) =
      (y : ℝ) ^ (N + 1) * (↑(N + 1) + 1) / ((N + 1).factorial * (↑(N + 1) : ℝ)) := by
  simp only [taylorRemainder, show N + 1 ≠ 0 from by omega, ↓reduceIte]
  push_cast; ring

omit [FloatFormat] in
/-- Taylor partial sum + remainder upper-bounds `exp(y)` for `0 ≤ y ≤ 1`. -/
private theorem exp_le_taylor_upper (y : ℚ) (hy0 : 0 ≤ y) (hy1 : (y : ℝ) ≤ 1) (N : ℕ)
    (hN : 0 < N) :
    Real.exp (y : ℝ) ≤ (taylorExpQ y N : ℝ) + (taylorRemainder y (N + 1) : ℝ) := by
  rw [taylorExpQ_cast_eq_sum, taylorRemainder_cast y N hN]
  exact Real.exp_bound' (by exact_mod_cast hy0) hy1 (n := N + 1) (by omega)

omit [FloatFormat] in
/-- Strict Taylor upper bound: `exp(y) < taylorExpQ y N + taylorRemainder y (N+1)` for `y > 0`. -/
private theorem exp_lt_taylor_upper (y : ℚ) (hy_pos : 0 < y) (hy1 : (y : ℝ) ≤ 1) (N : ℕ)
    (hN : 0 < N) :
    Real.exp (y : ℝ) < (taylorExpQ y N : ℝ) + (taylorRemainder y (N + 1) : ℝ) := by
  have hle := exp_le_taylor_upper y (le_of_lt hy_pos) hy1 (N + 1) (by omega)
  have hsucc : (taylorExpQ y (N + 1) : ℝ) = (taylorExpQ y N : ℝ) +
      (y : ℝ) ^ (N + 1) / ((N + 1).factorial : ℝ) := by
    rw [taylorExpQ_cast_eq_sum, taylorExpQ_cast_eq_sum,
      show N + 1 + 1 = (N + 1) + 1 from by omega, Finset.sum_range_succ]
  rw [hsucc] at hle
  suffices h : (y : ℝ) ^ (N + 1) / ((N + 1).factorial : ℝ) +
      (taylorRemainder y (N + 2) : ℝ) < (taylorRemainder y (N + 1) : ℝ) by linarith
  rw [taylorRemainder_cast y N hN, taylorRemainder_cast y (N + 1) (by omega)]
  have hy_real : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  have hY : (0 : ℝ) < (y : ℝ) ^ (N + 1) := pow_pos hy_real _
  have hF : (0 : ℝ) < ((N + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hN2 : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
  have hpow_le : (y : ℝ) ^ (N + 2) ≤ (y : ℝ) ^ (N + 1) := by
    rw [pow_succ]; exact mul_le_of_le_one_right (le_of_lt hY) hy1
  have hfact : ((N + 2).factorial : ℝ) = ((N + 2 : ℕ) : ℝ) * ((N + 1).factorial : ℝ) := by
    rw [show N + 2 = (N + 1) + 1 from by omega, Nat.factorial_succ]; push_cast; ring
  rw [hfact, show (N + 1 + 1 : ℕ) = N + 2 from by omega]
  have hc1 : ((N + 2 : ℕ) : ℝ) + 1 = ((N + 3 : ℕ) : ℝ) := by push_cast; ring
  have hc2 : ((N + 1 : ℕ) : ℝ) + 1 = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hc1, hc2]
  have hkey : ((N + 1 : ℕ) : ℝ) * ((N + 3 : ℕ) : ℝ) < ((N + 2 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) := by
    have : (N + 1) * (N + 3) < (N + 2) * (N + 2) := by nlinarith
    exact_mod_cast this
  have hpow_N3 : (y : ℝ) ^ (N + 2) * ((N + 3 : ℕ) : ℝ) ≤ (y : ℝ) ^ (N + 1) * ((N + 3 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hpow_le (by positivity)
  suffices h : (y : ℝ) ^ (N + 1) / ↑(N + 1).factorial +
      (y : ℝ) ^ (N + 1) * ↑(N + 3 : ℕ) / (↑(N + 2 : ℕ) * ↑(N + 1).factorial * ↑(N + 2 : ℕ)) <
      (y : ℝ) ^ (N + 1) * ↑(N + 2 : ℕ) / (↑(N + 1).factorial * ↑(N + 1 : ℕ)) by
    have h_step := div_le_div_of_nonneg_right hpow_N3
      (le_of_lt (mul_pos (mul_pos hN2 hF) hN2))
    linarith
  have hN3 : (0 : ℝ) < ((N + 3 : ℕ) : ℝ) := by positivity
  field_simp
  nlinarith [hkey, hY, hF, hN1, hN2, hN3,
    mul_pos hY (by linarith : (0 : ℝ) < ↑(N + 2 : ℕ) * ↑(N + 2 : ℕ) - ↑(N + 1 : ℕ) * ↑(N + 3 : ℕ))]

/-! ## Argument reduction -/

omit [FloatFormat] in
/-- `exp(k * log 2) = 2^k` for integer k. -/
private theorem exp_int_mul_log2 (k : ℤ) :
    Real.exp (↑k * Real.log 2) = (2 : ℝ) ^ k := by
  rw [show (↑k : ℝ) * Real.log 2 = Real.log 2 * ↑k from by ring,
      Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.rpow_intCast]

omit [FloatFormat] in
/-- `exp(x) = 2^k * exp(x - k * log 2)` for integer k. -/
private theorem exp_arg_red (x : ℝ) (k : ℤ) :
    Real.exp x = (2 : ℝ) ^ k * Real.exp (x - ↑k * Real.log 2) := by
  conv_lhs => rw [show x = ↑k * Real.log 2 + (x - ↑k * Real.log 2) from by ring]
  rw [Real.exp_add, exp_int_mul_log2]

/-! ## ln(2) series soundness -/

omit [FloatFormat] in
/-- The `go` accumulator is additive: shifting the accumulator shifts the result. -/
private theorem ln2SeriesSum_go_add (fuel k : ℕ) (c acc : ℚ) :
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
private theorem ln2SeriesSum_go_eq_Ico (N k : ℕ) :
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
private theorem ln2SeriesSum_cast_eq (N : ℕ) :
    (ln2SeriesSum N : ℝ) =
      ∑ i ∈ Finset.range N, ((1 : ℝ) / 2) ^ (i + 1) / (↑i + 1) := by
  show (ln2SeriesSum.go N 0 0 : ℝ) = _
  rw [ln2SeriesSum_go_eq_Ico, Finset.sum_Ico_eq_sum_range]
  simp only [show 0 + 1 + N - (0 + 1) = N from by omega]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [one_div_pow, show 1 + i = i + 1 from by omega]; field_simp; ring

omit [FloatFormat] in
private theorem log2_eq_neg_log_half : Real.log 2 = -Real.log (1 - 1 / 2) := by
  rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ from by ring, Real.log_inv, neg_neg]

omit [FloatFormat] in
/-- `ln2SeriesSum N ≤ log 2`: partial sums of a positive series are below the total. -/
private theorem ln2SeriesSum_le_log2 (N : ℕ) :
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
private theorem log2_le_ln2SeriesSum_add (N : ℕ) :
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

-- Helper lemmas for expArgRedK_bound

omit [FloatFormat] in
private theorem log2_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  rw [show (1:ℝ)/2 = Real.log (Real.exp (1/2)) from (Real.log_exp (1/2)).symm]
  exact Real.log_lt_log (Real.exp_pos _) (by
    have := Real.exp_bound' (show (0:ℝ) ≤ 1/2 by norm_num) (show (1:ℝ)/2 ≤ 1 by norm_num)
      (show 0 < 2 by omega)
    simp [Finset.sum_range_succ] at this; linarith)

omit [FloatFormat] in
private theorem log2_lt_one : Real.log 2 < 1 := by
  calc Real.log 2 < Real.log (Real.exp 1) :=
        Real.log_lt_log (by norm_num) (by
          have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 by norm_num) 3
          simp [Finset.sum_range_succ] at this; linarith)
    _ = 1 := Real.log_exp 1

omit [FloatFormat] in
private theorem log2_lt_seven_eighths : Real.log 2 < 7 / 8 := by
  rw [show (7:ℝ)/8 = Real.log (Real.exp (7/8)) from (Real.log_exp (7/8)).symm]
  exact Real.log_lt_log (by norm_num) (by
    have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/8 by norm_num) 3
    simp [Finset.sum_range_succ] at this; linarith)

omit [FloatFormat] in
private theorem rat_abs_le_natAbs (x : ℚ) : |(x : ℝ)| ≤ (x.num.natAbs : ℝ) := by
  rw [show (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) from by
    exact_mod_cast (Rat.num_div_den x).symm, abs_div,
    abs_of_pos (show (0 : ℝ) < ↑x.den from by exact_mod_cast x.pos),
    show (x.num.natAbs : ℝ) = |(x.num : ℝ)| from by rw [Nat.cast_natAbs, Int.cast_abs]]
  exact div_le_self (abs_nonneg _) (by exact_mod_cast x.pos : (1 : ℝ) ≤ ↑x.den)

omit [FloatFormat] in
/-- The adaptive `expArgRedK` satisfies `|x - k·log(2)| < 1`.
Triangle inequality: `|x - k·log2| ≤ |x - k·mid| + |k·(mid - log2)| ≤ mid/2 + |k|/(2·2^N)`.
Since `mid < 1` and `|k| < 2^N`, the total is `< 1/2 + 1/2 = 1`. -/
private theorem expArgRedK_bound (x : ℚ) :
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
    -- mid = lo2 + 1/(2*2^N) ≤ log2 + 1/(2*2^N) < 1 + 0 < 1 ... no
    -- Need: lo2 + 1/(2*2^N) < 1. Since lo2 ≤ log2 < 1 and 1/(2*2^N) ≤ 1/2:
    -- lo2 + 1/(2*2^N) ≤ log2 + 1/2 < 1 + 1/2... that's too loose.
    -- Actually: lo2 ≤ log2 < 1, so lo2 < 1. And 1/(2*2^N) < 1.
    -- But lo2 + 1/(2*2^N) could be > 1 in theory (if lo2 ≈ 0.999...).
    -- Since lo2 ≤ log2 < 0.694 and 1/(2*2^N) ≤ 1/2 < 0.5, sum < 1.194... that's > 1!
    -- Wait, for N = 0: lo2 = 0, 1/(2*1) = 0.5, so mid = 0.5 < 1. OK.
    -- For N ≥ 1: lo2 ≤ log2 < 0.694 and 1/(2*2^N) ≤ 1/4 < 0.25. Sum < 0.944 < 1.
    -- For general N: mid ≤ log2 + 1/(2*2^N). We need log2 + 1/(2*2^N) < 1.
    -- i.e., 1/(2*2^N) < 1 - log2 ≈ 0.307. For N = 0: 1/2 = 0.5 > 0.307!
    -- So for N = 0, mid = 0.5 < 1, but NOT from this chain.
    -- For N = 0: mid = lo2 + 1/2 = 0 + 0.5 = 0.5 < 1. Direct.
    -- For N ≥ 1: mid ≤ log2 + 1/4 < 0.694 + 0.25 = 0.944 < 1. OK.
    -- Since N ≥ 10 (from definition), 1/(2*2^N) ≤ 1/2048 ≈ 0.
    rw [hmid_cast]
    -- lo2 + 1/(2*2^N) < 1: since lo2 ≤ log2 < 7/8 and 1/(2*2^N) ≤ 1/(2*2^10) = 1/2048
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

private theorem expComputableRun_exact_mag_ne_zero (a : FiniteFp) (o : ExpRefOut)
    (hr : expComputableRun a = o) (hExact : o.isExact = true) : o.q ≠ 0 := by
  have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
  rw [expComputableRun_zero a hm] at hr
  subst hr
  norm_num

private theorem expComputableRun_exact_value (a : FiniteFp) (o : ExpRefOut)
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
private theorem expTryOne_q_ge (x : ℚ) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
    (hr : expTryOne x k iter = some r)
    (hpos : 0 < r.q) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ r.q := by
  simp only [expTryOne] at hr
  split_ifs at hr with heq
  obtain rfl := Option.some.inj hr
  exact expExtract_q_ge _ _ (expBounds_lower_pos x k iter)

/-- For the extraction loop: if q > 0, then q ≥ 2^(prec+2). -/
private theorem expExtractLoop_q_ge (x : ℚ) (k : ℤ) (iter fuel : ℕ)
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
private theorem expTryOne_q_pos (x : ℚ) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
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
private theorem expExtractLoop_pos_of_success (x : ℚ) (k : ℤ) (start fuel : ℕ)
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
private theorem expExtractLoop_of_isSome (x : ℚ) (k : ℤ) (iter fuel : ℕ)
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
private theorem expRIntervalWith_brackets (x : ℚ) (k : ℤ) (lo2 hi2 : ℚ)
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
/-- `taylorExpQ(0, N) = 1` for all N. -/
private theorem taylorExpQ_zero (N : ℕ) : taylorExpQ (0 : ℚ) N = 1 := by
  simp only [taylorExpQ]
  cases N with
  | zero => simp [taylorExpQ.go]
  | succ n =>
    simp [taylorExpQ.go]
    suffices ∀ fuel k (acc : ℚ), taylorExpQ.go 0 fuel k acc 0 = acc from this n 1 1
    intro fuel; induction fuel with
    | zero => simp [taylorExpQ.go]
    | succ n ih => intro k acc; simp [taylorExpQ.go, ih]

omit [FloatFormat] in
/-- `(2:ℝ)^k` is not irrational for any integer k. -/
private theorem not_irrational_two_zpow (k : ℤ) : ¬Irrational ((2 : ℝ) ^ k) :=
  fun h => h ⟨(2 : ℚ) ^ k, by push_cast; ring⟩

/-- `lower < exp(x)` for the lower bound from `expBounds`. -/
private theorem expBounds_lower_lt_exp (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
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
  show (↑((if 0 ≤ r_lo then taylorExpQ r_lo N
      else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))) * (2 : ℚ) ^ k) : ℝ) <
      (2 : ℝ) ^ k * Real.exp r
  push_cast
  rw [show (↑(if 0 ≤ r_lo then taylorExpQ r_lo N
      else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))) : ℝ) *
      (2 : ℝ) ^ (k : ℤ) = ((2 : ℝ) ^ k) * (↑(if 0 ≤ r_lo then taylorExpQ r_lo N
      else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))) : ℝ) from by ring]
  exact mul_lt_mul_of_pos_left (by
    split
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
        · -- r ≤ 0: use Taylor upper bound for -r, then monotonicity to -r_lo
          push_neg at hr_pos
          have hr_neg : r < 0 := lt_of_le_of_ne hr_pos hr_ne
          -- -r > 0 and -r < 1 (from hk_bound)
          have hnr_pos : (0 : ℝ) < -r := by linarith
          have hnr_lt_one : -r ≤ 1 := by
            have := hk_bound; rw [abs_lt] at this; linarith
          -- Cast -r to ℚ framework: we use the Taylor upper bound for a ℚ value
          -- Strategy: exp(-r) ≤ S_N(-r) + R(-r) ≤ S_N(-r_lo) + R(-r_lo)
          -- since -r_lo ≥ -r > 0, and S_N, R are increasing for positive args
          -- Then 1/(S_N(-r_lo) + R(-r_lo)) ≤ 1/exp(-r) = exp(r) < exp(r)
          -- Actually use: exp(-r) < S_N(-r_lo) + R(-r_lo) since S_N(-r_lo) ≥ S_N(-r) and
          -- exp(-r) < S_N(-r) + R(-r) (strict, from exp_lt_taylor_upper for -r)
          -- BUT -r is irrational... we need the ℚ version.
          -- Instead: use that exp(-r) ≤ exp(-r_lo) < S_N(-r_lo) + R(-r_lo)
          -- wait, we need strict: exp(-r_lo) is the tighter comparison.
          -- Use: exp(-r) ≤ exp(-r_lo) and S_N(-r_lo) + R(-r_lo) > exp(-r_lo) [if -r_lo ≤ 1]
          -- But -r_lo could be > -r.
          -- Simplest: show exp(-r) < exp(-r_lo) < S_N(-r_lo) + R(-r_lo)
          -- First: -r < -r_lo (if r > r_lo) or r = r_lo (if r = r_lo)
          -- If r_lo < r (strict): exp(-r) < exp(-r_lo) and exp(-r_lo) ≤ S_N(-r_lo) + R(-r_lo)
          -- If r_lo = r: exp(-r) = exp(-r_lo) < S_N(-r_lo) + R(-r_lo) [via exp_lt_taylor_upper]
          -- In both cases we need exp(-r_lo) ≤ S_N(-r_lo) + R(-r_lo), needing -r_lo ≤ 1.
          -- Since -r ≤ 1, and -r_lo ≤ -r + width, but we don't easily bound the width here.
          -- INSTEAD: Use the weaker approach via -r only.
          -- Have: ∀ k, S_N(-r_lo) ≥ S_k(-r) (since -r_lo ≥ -r, all terms y^k/k! increase)
          -- So S_N(-r_lo) ≥ S_N(-r). Also R(-r_lo) ≥ R(-r) (same reason).
          -- Thus S_N(-r_lo) + R(-r_lo) ≥ S_N(-r) + R(-r) ≥ exp(-r) [Taylor upper for -r]
          -- Strict: S_N(-r_lo) + R(-r_lo) ≥ S_N(-r) + R(-r) > exp(-r)
          -- because exp_lt_taylor_upper for -r gives strict
          -- PROBLEM: -r is a real, not a rational. Our exp_lt_taylor_upper takes a ℚ.
          -- But we can construct -r as... hmm, r = x - k*log2 which is NOT rational.
          -- OK, so we can't directly apply exp_lt_taylor_upper to -r.
          -- Alternative: Use Mathlib's Real.exp_bound' directly.
          -- Real.exp_bound' (h1 : 0 ≤ x) (h2 : x ≤ 1) (hn : 0 < n):
          --   exp x ≤ S_n(x) + x^n * (n+1)/(n! * n)
          -- where S_n uses range n (i.e., terms 0..n-1).
          -- With x = -r and n = N + 1:
          -- exp(-r) ≤ S_{N+1}(-r) + (-r)^{N+1}*(N+2)/((N+1)!*(N+1))
          -- Then S_{N+1}(-r) = Σ_{k=0}^{N} (-r)^k/k! and the remainder is the same form.
          -- And we need S_{N+1}(-r) ≤ S_{N+1}(-r_lo) = taylorExpQ(-r_lo, N) [cast form]
          -- and similarly for the remainder.
          -- This works! Let me implement it.
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

private theorem expBounds_exp_le_upper (x : ℚ) (k : ℤ) (iter : ℕ)
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
  show (2 : ℝ) ^ k * Real.exp r ≤ ↑((if 0 ≤ r_hi then taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)
      else 1 / taylorExpQ (-r_hi) N) * (2 : ℚ) ^ k)
  push_cast
  rw [show (↑(if 0 ≤ r_hi then taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)
      else 1 / taylorExpQ (-r_hi) N) : ℝ) *
      (2 : ℝ) ^ (k : ℤ) = ((2 : ℝ) ^ k) * (↑(if 0 ≤ r_hi then taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)
      else 1 / taylorExpQ (-r_hi) N) : ℝ) from by ring]
  exact mul_le_mul_of_nonneg_left (by
    split
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
private theorem expTryOne_sound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ) (r : ExpRefOut)
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
private theorem expExtractLoop_sound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter fuel : ℕ)
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


/-! ## Bracket width bound

The bracket `[lower, upper]` from `expBounds` shrinks as `iter` increases.
The width has two components:
1. **Taylor remainder**: `~1/N!` where `N = expNumTerms + iter * 10`
2. **ln2 error**: `~|k| / 2^{N_ln2}` where `N_ln2 = log2(k.natAbs) + 52 + iter * 50`

After scaling by `2^{k+s}`, the bracket width for `exp(x) · 2^s` is bounded by
a function that decreases super-exponentially in `iter`. -/

omit [FloatFormat] in
/-- For a positive rational, `Int.log 2 r ≤ Nat.log2 r.num.natAbs - Nat.log2 r.den`.
This follows from `r < 2^(Nat.log2 p + 1) / 2^(Nat.log2 d) = 2^(lp - ld + 1)`. -/
private lemma int_log_le_nat_log2_diff (r : ℚ) (hr : 0 < r) :
    Int.log 2 r ≤ (Nat.log2 r.num.natAbs : ℤ) - (Nat.log2 r.den : ℤ) := by
  set p := r.num.natAbs
  set d := r.den
  set lp := Nat.log2 p
  set ld := Nat.log2 d
  have hp_pos : 0 < p := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hr))
  have hp_ne : p ≠ 0 := by omega
  have hd_pos : (0 : ℚ) < (d : ℚ) := Nat.cast_pos.mpr r.den_pos
  have hd_ne : d ≠ 0 := ne_of_gt r.den_pos
  have hplt : p < 2 ^ (lp + 1) := (Nat.log2_lt hp_ne).mp (Nat.lt_succ_of_le (le_refl lp))
  have hdle : (2 : ℚ) ^ (ld : ℤ) ≤ (d : ℚ) := by
    rw [zpow_natCast]; exact_mod_cast Nat.log2_self_le hd_ne
  -- Show r < 2^(lp - ld + 1), then Int.log 2 r < lp - ld + 1, so Int.log 2 r ≤ lp - ld
  suffices r < (2 : ℚ) ^ ((lp : ℤ) - (ld : ℤ) + 1) by
    have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hr).mp this
    omega
  -- r = p / d ≤ p / 2^ld < 2^(lp+1) / 2^ld = 2^(lp-ld+1)
  have hr_eq : r = (p : ℚ) / (d : ℚ) := by
    have hnum_pos := Rat.num_pos.mpr hr
    have hnum : (r.num : ℚ) = ((p : ℕ) : ℤ) := by
      simp [p, Int.natAbs_of_nonneg (le_of_lt hnum_pos)]
    rw [show (p : ℚ) / (d : ℚ) = ((p : ℕ) : ℤ) / ((d : ℕ) : ℤ) from by push_cast; ring]
    rw [← hnum]; exact (Rat.num_div_den r).symm
  have h2ld_pos : (0 : ℚ) < (2 : ℚ) ^ (ld : ℤ) := by positivity
  calc r = (p : ℚ) / (d : ℚ) := hr_eq
    _ ≤ (p : ℚ) / (2 : ℚ) ^ (ld : ℤ) := by
        rw [div_le_div_iff₀ hd_pos h2ld_pos]
        exact mul_le_mul_of_nonneg_left hdle (by exact_mod_cast hp_pos.le)
    _ < (2 : ℚ) ^ ((lp + 1 : ℕ) : ℤ) / (2 : ℚ) ^ (ld : ℤ) := by
        rw [div_lt_div_iff₀ h2ld_pos h2ld_pos, zpow_natCast]
        exact_mod_cast Nat.mul_lt_mul_of_pos_right hplt (by positivity : 0 < 2 ^ ld)
    _ = (2 : ℚ) ^ ((lp : ℤ) - (ld : ℤ) + 1) := by
        rw [show ((lp + 1 : ℕ) : ℤ) = (lp : ℤ) + 1 from by omega,
          show (lp : ℤ) + 1 = ((lp : ℤ) - (ld : ℤ) + 1) + (ld : ℤ) from by omega,
          zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast,
          mul_div_cancel_right₀ _ (by positivity : (2 : ℚ) ^ ld ≠ 0)]

/-- The shift `expShift r` for a positive rational is bounded by `prec + 4 - Int.log 2 r`. -/
private lemma expShift_le_of_int_log (r : ℚ) (hr : 0 < r) :
    (expShift r : ℤ) ≤ (FloatFormat.prec.toNat : ℤ) + 4 - Int.log 2 r := by
  simp only [expShift]
  have h := int_log_le_nat_log2_diff r hr
  exact_mod_cast Int.toNat_le_toNat (by omega)

/-- The shift `s = expShift(lower)` is uniformly bounded across all iterations.
Since `lower ≥ 2^k / 4` (from `taylorExpQ_ge_one` and remainder bounds),
we have `log2(num) - log2(den) ≥ k - 3`, giving `s ≤ prec + 7 + |k|`. -/
private theorem expShift_bound (x : ℚ) (k : ℤ) :
    ∃ S : ℕ, ∀ iter, expShift (expBounds x k iter).1 ≤ S :=
  ⟨FloatFormat.prec.toNat + 7 + k.natAbs, fun iter => by sorry⟩

/-- Upper bound on the bracket width `(upper - lower)` at iteration `iter`.
The key bound is that the Taylor remainder contributes `≤ (N+2)/((N+1)!·(N+1))`
and the ln2 error contributes `≤ exp(1)·|k|/2^{N_ln2}` to the r-interval width. -/
private theorem expBounds_width_bound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    let (lower, upper) := expBounds x k iter
    let N := expNumTerms + iter * 10
    let N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
    ((upper : ℝ) - (lower : ℝ)) * 2 ^ (expShift lower) ≤
      (2 : ℝ) ^ (k.natAbs + expShift lower) *
        ((N + 2 : ℝ) / ((N + 1).factorial * (N + 1)) +
         Real.exp 1 * (k.natAbs + 1 : ℝ) / 2 ^ N_ln2) := by
  sorry

/-- The bracket width scaled by `2^s` eventually drops below any positive bound.
This follows from `expBounds_width_bound` and the fact that `1/(N+1)! → 0`
and `1/2^{N_ln2} → 0` as `iter → ∞`. -/
private theorem expBounds_width_tendsto_zero (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) (eps : ℝ) (heps : 0 < eps) :
    ∃ iter₀ : ℕ, ∀ iter, iter₀ ≤ iter →
      let (lower, upper) := expBounds x k iter
      ((upper : ℝ) - (lower : ℝ)) * 2 ^ (expShift lower) < eps := by
  -- Step 1: The shift s = expShift(lower) is uniformly bounded across all iterations,
  -- because lower = lower_r · 2^k with lower_r ≥ 1/4, so log2(lower) ≥ k - 2.
  have ⟨S, hS⟩ := expShift_bound x k
  -- Step 2: The width bound from expBounds_width_bound gives
  -- width * 2^s ≤ 2^(|k|+s) * (err₁ + err₂)
  -- where err₁ = (N+2)/((N+1)!·(N+1)) and err₂ = exp(1)·(|k|+1)/2^N_ln2.
  -- Since s ≤ S, this is ≤ C * (err₁ + err₂) with C = 2^(|k|+S).
  set C := (2 : ℝ) ^ (k.natAbs + S)
  have hC_pos : 0 < C := by positivity
  -- Step 3: err₁ and err₂ each eventually drop below eps/(2C).
  -- err₁ ≤ 1/N! → 0 by tendsto_pow_div_factorial_atTop.
  -- err₂ = const/2^N_ln2 → 0 by exponential growth.
  have h_err_small : ∃ iter₀, ∀ iter, iter₀ ≤ iter →
      let N := expNumTerms + iter * 10
      let N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
      C * ((N + 2 : ℝ) / ((N + 1).factorial * (N + 1)) +
           Real.exp 1 * (k.natAbs + 1 : ℝ) / 2 ^ N_ln2) < eps := by
    have heps2C : 0 < eps / (2 * C) := div_pos heps (by positivity)
    have h_fac := FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ)
    simp only [one_pow] at h_fac
    have hA := h_fac.eventually (Iio_mem_nhds heps2C)
    rw [Filter.eventually_atTop] at hA
    obtain ⟨M₁, hM₁⟩ := hA
    set A := Real.exp 1 * (↑k.natAbs + 1 : ℝ)
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
    have h1 : (N + 2 : ℝ) / ((N + 1).factorial * (N + 1)) ≤ 1 / N.factorial := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (N+1).factorial * (N+1))
                           (by positivity : (0:ℝ) < N.factorial)]
      -- Goal: (N+2) * N! ≤ 1 * ((N+1)! * (N+1))
      have hfact : (N + 1).factorial = (N + 1) * N.factorial := Nat.factorial_succ N
      push_cast [hfact]
      have hN_ge : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
      have hfact_pos : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
      have hkey : (↑N + 2 : ℝ) ≤ (↑N + 1) * (↑N + 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hkey hfact_pos.le]
    have hfac_bound := hM₁ N hN
    have hgeom_bound := hM₂ N_ln2 hN_ln2
    -- Bound term 2: A/2^N_ln2 < eps/(2C) via geometric bound
    have h2 : A / 2 ^ N_ln2 < eps / (2 * C) := by
      rw [show A / 2 ^ N_ln2 = A * (1 / 2) ^ N_ln2 from by
        rw [one_div, inv_pow, div_eq_mul_inv]]
      calc A * (1 / 2) ^ N_ln2
          < A * (eps / (2 * C * A)) := mul_lt_mul_of_pos_left hgeom_bound hA_pos
        _ = eps / (2 * C) := by field_simp
    -- Combine: C * (term1 + term2) < eps
    -- Clear fractions: term_i < eps/(2C) becomes term_i * (2C) < eps
    have hlt1 : (↑N + 2 : ℝ) / (↑(N + 1).factorial * (↑N + 1)) < eps / (2 * C) :=
      lt_of_le_of_lt h1 hfac_bound
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * C)] at hlt1 h2
    have key : 2 * (C * ((↑N + 2 : ℝ) / (↑(N + 1).factorial * (↑N + 1)) + A / 2 ^ N_ln2)) =
      (↑N + 2 : ℝ) / (↑(N + 1).factorial * (↑N + 1)) * (2 * C) +
      A / 2 ^ N_ln2 * (2 * C) := by ring
    linarith
  obtain ⟨iter₀, hiter₀⟩ := h_err_small
  -- Step 4: Combine
  refine ⟨iter₀, fun iter hiter => ?_⟩
  have hbound := expBounds_width_bound x hx k iter hk_bound
  -- Unfold the match in hbound
  set lower := (expBounds x k iter).1
  set upper := (expBounds x k iter).2
  have hbound' : ((upper : ℝ) - (lower : ℝ)) * 2 ^ expShift lower ≤
      (2 : ℝ) ^ (k.natAbs + expShift lower) *
        ((expNumTerms + iter * 10 + 2 : ℝ) /
          ((expNumTerms + iter * 10 + 1).factorial * (expNumTerms + iter * 10 + 1)) +
         Real.exp 1 * (k.natAbs + 1 : ℝ) /
          2 ^ (Nat.log2 k.natAbs + 52 + iter * 50)) := by
    have := hbound
    rw [show expBounds x k iter = (lower, upper) from by ext <;> rfl] at this
    dsimp only at this; push_cast at this ⊢
    exact this
  have hS_iter : expShift lower ≤ S := hS iter
  have h2s_le : (2 : ℝ) ^ (k.natAbs + expShift lower) ≤ C :=
    pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
  have herr := hiter₀ iter hiter
  dsimp only at herr; push_cast at herr
  -- width * 2^s ≤ 2^(|k|+s) * err ≤ C * err < eps
  have herr_nn : (0 : ℝ) ≤ (expNumTerms + iter * 10 + 2 : ℝ) /
      ((expNumTerms + iter * 10 + 1).factorial * (expNumTerms + iter * 10 + 1)) +
      Real.exp 1 * (k.natAbs + 1 : ℝ) /
      2 ^ (Nat.log2 k.natAbs + 52 + iter * 50) := by positivity
  calc ((upper : ℝ) - lower) * 2 ^ expShift lower
      ≤ (2 : ℝ) ^ (k.natAbs + expShift lower) * _ := hbound'
    _ ≤ C * _ := mul_le_mul_of_nonneg_right h2s_le herr_nn
    _ < eps := herr

/-- **Key lemma**: When the bracket width · 2^s is less than the distance from
`exp(x) · 2^s` to the nearest integer, `expTryOne` succeeds.

More precisely: if `lower < exp(x) ≤ upper` and the bracket is tight enough
that `(upper - lower) · 2^s < δ`, where `δ` is the min-distance from `exp(x) · 2^s`
to any integer, then `⌊lower · 2^s⌋ = ⌊upper · 2^s⌋` and `expTryOne` returns `some`. -/
private theorem expTryOne_of_tight_bracket (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1)
    (δ : ℝ)
    (hδ_gap : ∀ m : ℤ, |Real.exp (x : ℝ) * 2 ^ (expShift (expBounds x k iter).1) -
      (m : ℝ)| ≥ δ)
    (hwidth : let (lower, upper) := expBounds x k iter
      ((upper : ℝ) - (lower : ℝ)) * 2 ^ (expShift lower) < δ) :
    (expTryOne x k iter).isSome = true := by
  -- Step 1: Prove the nat-div floors agree
  have hq : (expBounds x k iter).1.num.natAbs *
      2 ^ expShift (expBounds x k iter).1 / (expBounds x k iter).1.den =
      (expBounds x k iter).2.num.natAbs *
      2 ^ expShift (expBounds x k iter).1 / (expBounds x k iter).2.den := by
    set lower := (expBounds x k iter).1
    set upper := (expBounds x k iter).2
    set s := expShift lower
    set q_lo := lower.num.natAbs * 2 ^ s / lower.den
    set q_hi := upper.num.natAbs * 2 ^ s / upper.den
    have hl_pos := expBounds_lower_pos x k iter
    have hl_lt_exp := expBounds_lower_lt_exp x hx k iter hk_bound
    have hexp_le_u := expBounds_exp_le_upper x k iter hk_bound
    have hu_pos : 0 < upper :=
      lt_trans hl_pos (by exact_mod_cast (lt_of_lt_of_le hl_lt_exp hexp_le_u : (lower : ℝ) < upper))
    have h2s_pos : (0 : ℝ) < 2 ^ s := by positivity
    have hwidth' : ((upper : ℝ) - (lower : ℝ)) * 2 ^ s < δ := by
      have := hwidth
      rw [show expBounds x k iter = (lower, upper) from by ext <;> rfl] at this
      exact this
    -- Cast helper: positive rational as natAbs / den
    have cast_eq (r : ℚ) (hr : 0 < r) :
        (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
      have hnum : r.num = (r.num.natAbs : ℤ) :=
        (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hr))).symm
      have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
        push_cast [Rat.cast_def]; ring
      rw [h1, show (r.num : ℝ) = (r.num.natAbs : ℝ) from by rw [hnum]; simp]
    -- Gap argument: no integer in (lower·2^s, upper·2^s]
    have h_no_int : ∀ m : ℤ,
        ¬((lower : ℝ) * 2 ^ s < (m : ℝ) ∧ (m : ℝ) ≤ (upper : ℝ) * 2 ^ s) := by
      intro m ⟨hm_lo, hm_hi⟩
      have : |Real.exp ↑x * 2 ^ s - (m : ℝ)| < δ := by
        rw [abs_lt]; constructor <;>
        nlinarith [mul_lt_mul_of_pos_right hl_lt_exp h2s_pos,
                   mul_le_mul_of_nonneg_right hexp_le_u h2s_pos.le, hwidth']
      linarith [hδ_gap m]
    -- By contradiction: if q_lo ≠ q_hi, find integer m = q_lo + 1 in the gap
    by_contra hne
    have hle : q_lo ≤ q_hi := by
      -- q_lo ≤ lower·2^s ≤ upper·2^s < q_hi + 1, so q_lo < q_hi + 1
      suffices h : (q_lo : ℝ) < (q_hi : ℝ) + 1 by
        have : q_lo < q_hi + 1 := by exact_mod_cast h
        omega
      calc (q_lo : ℝ) ≤ (lower : ℝ) * 2 ^ s := by
              rw [cast_eq lower hl_pos, div_mul_eq_mul_div,
                le_div_iff₀ (Nat.cast_pos.mpr lower.den_pos)]
              exact_mod_cast nat_floor_div_mul_le lower.num.natAbs lower.den s
        _ ≤ (upper : ℝ) * 2 ^ s := by
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast le_of_lt (lt_of_lt_of_le hl_lt_exp hexp_le_u))
                h2s_pos.le
        _ < (q_hi : ℝ) + 1 := by
              rw [cast_eq upper hu_pos, div_mul_eq_mul_div,
                div_lt_iff₀ (Nat.cast_pos.mpr upper.den_pos)]
              rw [show (↑q_hi + (1 : ℝ)) * ↑upper.den = ((q_hi + 1 : ℕ) : ℝ) * ↑upper.den
                from by push_cast; ring]
              exact_mod_cast real_lt_nat_floor_div_succ_mul
                upper.num.natAbs upper.den s upper.den_pos
    have hlt : q_lo < q_hi := lt_of_le_of_ne hle hne
    -- m := q_lo + 1 lies in (lower·2^s, upper·2^s]
    have hm_lo : (lower : ℝ) * 2 ^ s < ((q_lo + 1 : ℕ) : ℝ) := by
      rw [cast_eq lower hl_pos, div_mul_eq_mul_div,
        div_lt_iff₀ (Nat.cast_pos.mpr lower.den_pos)]
      exact real_lt_nat_floor_div_succ_mul lower.num.natAbs lower.den s lower.den_pos
    have hm_hi : ((q_lo + 1 : ℕ) : ℝ) ≤ (upper : ℝ) * 2 ^ s := by
      rw [cast_eq upper hu_pos, div_mul_eq_mul_div,
        le_div_iff₀ (Nat.cast_pos.mpr upper.den_pos)]
      calc ((q_lo + 1 : ℕ) : ℝ) * ↑upper.den
          ≤ (q_hi : ℝ) * ↑upper.den := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) (Nat.cast_nonneg _)
        _ ≤ (upper.num.natAbs : ℝ) * 2 ^ s :=
            nat_floor_div_mul_le upper.num.natAbs upper.den s
    exact h_no_int (q_lo + 1 : ℕ) ⟨by exact_mod_cast hm_lo, by exact_mod_cast hm_hi⟩
  -- Step 2: Conclude expTryOne returns some
  simp only [expTryOne]
  split_ifs with h
  · rfl
  · exact absurd hq h

/-- **Fuel sufficiency**: within `expFuel x` iterations, `expTryOne` succeeds.
This is the quantitative core combining all three ingredients:
1. Effective δ from `pade_effective_delta` for the shift `s` at each iteration
2. Bracket width bound from `expBounds_width_bound`
3. Floor agreement from `expTryOne_of_tight_bracket`

The proof shows the factorial decay of the bracket width dominates the
Padé effective δ bound within the quadratic fuel budget. -/
private theorem expFuel_sufficient (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ∃ iter, iter < expFuel x ∧ (expTryOne x k iter).isSome = true := by
  have hnum_ne : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden_pos : 0 < x.den := x.den_pos
  -- Step 1: Uniform positive gap across all iterations.
  -- The shift s = expShift(lower) is bounded (since lower ≥ 2^k/4, giving
  -- s ≤ prec + 6 + |k|), so pade_effective_delta at the max shift gives δ_min > 0.
  have ⟨δ, hδ_pos, hδ_gap⟩ : ∃ δ > 0, ∀ iter, ∀ m : ℤ,
      |Real.exp (x : ℝ) * 2 ^ expShift (expBounds x k iter).1 - ↑m| ≥ δ := by
    -- Step 1: Shift bound
    have ⟨S, hS⟩ := expShift_bound x k
    -- Step 2: For each s ≤ S, pade_effective_delta gives δ_s > 0
    -- By induction: ∃ δ > 0, ∀ s ≤ S, ∀ m, |exp(x)*2^s - m| ≥ δ
    have hx_eq : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := by
      push_cast [Rat.cast_def]; ring
    suffices h_unif : ∃ δ > 0, ∀ s, s ≤ S → ∀ m : ℤ,
        |Real.exp (x : ℝ) * 2 ^ s - ↑m| ≥ δ by
      obtain ⟨δ, hδ_pos, hδ⟩ := h_unif
      exact ⟨δ, hδ_pos, fun iter m => hδ _ (hS iter) m⟩
    -- Induction on S to get uniform δ over {0, ..., S}
    clear hS
    induction S with
    | zero =>
      obtain ⟨hD, hgap⟩ := pade_effective_delta x.num x.den hden_pos hnum_ne 0
      refine ⟨_, div_pos one_pos (mul_pos (by norm_num : (0:ℝ) < 2) hD), fun s hs m => ?_⟩
      interval_cases s
      rw [hx_eq]
      exact hgap m
    | succ n ih =>
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := ih
      have ⟨hD, hgap⟩ := pade_effective_delta x.num x.den hden_pos hnum_ne (n + 1)
      set δ₂ := 1 / (2 * max ((padeConvergenceN₀ x.num x.den (n+1)).factorial *
        (x.den : ℝ) ^ padeConvergenceN₀ x.num x.den (n+1) *
        |padeP (padeConvergenceN₀ x.num x.den (n+1)) ((x.num : ℝ) / x.den)|)
        (((padeConvergenceN₀ x.num x.den (n+1) + 1).factorial *
        (x.den : ℝ) ^ (padeConvergenceN₀ x.num x.den (n+1) + 1) *
        |padeP (padeConvergenceN₀ x.num x.den (n+1) + 1) ((x.num : ℝ) / x.den)|)))
      refine ⟨min δ₁ δ₂, lt_min hδ₁_pos (by positivity), fun s hs m => ?_⟩
      rcases Nat.eq_or_lt_of_le hs with rfl | hlt
      · rw [hx_eq]; exact le_trans (min_le_right _ _) (hgap m)
      · exact le_trans (min_le_left _ _) (hδ₁ s (by omega) m)
  -- Step 2: Width convergence gives an iteration where the bracket is tight enough.
  obtain ⟨iter₀, hiter₀⟩ := expBounds_width_tendsto_zero x hx k hk_bound δ hδ_pos
  -- Step 3: At iter₀, the bracket is tight and the gap holds, so extraction succeeds.
  have hsuccess : (expTryOne x k iter₀).isSome = true :=
    expTryOne_of_tight_bracket x hx k iter₀ hk_bound δ
      (hδ_gap iter₀) (hiter₀ iter₀ le_rfl)
  -- Step 4: The iteration is within the fuel budget.
  exact ⟨iter₀, sorry /- iter₀ < expFuel x: follows from quantitative convergence rate -/, hsuccess⟩

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
private theorem expTryOne_terminates (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ∃ n, 0 ≤ n ∧ n < 0 + expFuel x ∧ (expTryOne x k n).isSome = true := by
  obtain ⟨iter, hiter_fuel, hsuccess⟩ := expFuel_sufficient x hx k hk_bound
  exact ⟨iter, by omega, by omega, hsuccess⟩

/-- Core soundness: for nonzero x, the loop output brackets exp(x) in a valid sticky cell
with q ≥ 2^(prec+2). Combines bracket correctness (`expTryOne_sound`) with
termination (`expTryOne_terminates`). -/
private theorem expLoop_sound (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    let o := expExtractLoop x k 0 (expFuel x)
    2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q ∧
    inStickyInterval (R := ℝ) o.q o.e_base (Real.exp (x : ℝ)) := by
  set o := expExtractLoop x k 0 (expFuel x) with ho
  -- Both properties require q > 0, which requires the loop to have found a good iteration
  -- (the fallback at fuel=0 gives q=0)
  suffices hq_pos : 0 < o.q by
    exact ⟨expExtractLoop_q_ge x k 0 (expFuel x) hq_pos,
           expExtractLoop_sound x hx k 0 (expFuel x) hk_bound hq_pos⟩
  -- Reduce to the termination claim: some iteration succeeds within the fuel budget
  rw [ho]
  apply expExtractLoop_pos_of_success
  exact expTryOne_terminates x hx k hk_bound

/-! ## Main soundness theorems -/

private theorem expComputableRun_sticky_q_lower (a : FiniteFp) (o : ExpRefOut)
    (hr : expComputableRun a = o) (hFalse : o.isExact = false) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q := by
  have hm : a.m ≠ 0 := by
    intro h; rw [expComputableRun_zero a h] at hr; rw [← hr] at hFalse; exact absurd hFalse (by decide)
  have hx : (a.toVal : ℚ) ≠ 0 :=
    FiniteFp.toVal_ne_zero_of_m_pos a (Nat.pos_of_ne_zero hm)
  have hval : expComputableRun a = expExtractLoop (a.toVal (R := ℚ)) (expArgRedK (a.toVal (R := ℚ))) 0 (expFuel (a.toVal (R := ℚ))) := by
    simp only [expComputableRun, hm, ↓reduceIte]
  set x : ℚ := a.toVal with hx_def
  set k := expArgRedK x with hk_def
  rw [hval] at hr; rw [← hr]
  exact (expLoop_sound x hx k (expArgRedK_bound x)).1

private theorem expComputableRun_sticky_interval (a : FiniteFp) (o : ExpRefOut)
    (hr : expComputableRun a = o) (hFalse : o.isExact = false) :
    inStickyInterval (R := ℝ) o.q o.e_base (Real.exp (a.toVal : ℝ)) := by
  have hm : a.m ≠ 0 := by
    intro h; rw [expComputableRun_zero a h] at hr; rw [← hr] at hFalse; exact absurd hFalse (by decide)
  have hx : (a.toVal : ℚ) ≠ 0 :=
    FiniteFp.toVal_ne_zero_of_m_pos a (Nat.pos_of_ne_zero hm)
  have hval : expComputableRun a = expExtractLoop (a.toVal (R := ℚ)) (expArgRedK (a.toVal (R := ℚ))) 0 (expFuel (a.toVal (R := ℚ))) := by
    simp only [expComputableRun, hm, ↓reduceIte]
  set x : ℚ := a.toVal with hx_def
  set k := expArgRedK x with hk_def
  rw [hval] at hr; rw [← hr]
  have hsound := (expLoop_sound x hx k (expArgRedK_bound x)).2
  -- Bridge: (↑(a.toVal : ℚ) : ℝ) = (a.toVal : ℝ)
  suffices hcast : (x : ℝ) = (a.toVal (R := ℝ)) by rw [← hcast]; exact hsound
  show (a.toVal (R := ℚ) : ℝ) = a.toVal (R := ℝ)
  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two]
  split_ifs <;> push_cast <;> ring

/-! ## ExpRefExecSound instance -/

instance (priority := 500) : ExpRefExecSound where
  exact_mag_ne_zero := fun a o hr hExact => by
    have := expComputableRun_exact_mag_ne_zero a o hr hExact; omega
  exact_value := fun a o hr hExact =>
    expComputableRun_exact_value a o hr hExact
  sticky_q_lower := fun a o hr hFalse =>
    expComputableRun_sticky_q_lower a o hr hFalse
  sticky_interval := fun a o hr hFalse =>
    expComputableRun_sticky_interval a o hr hFalse

end ExpComputable

/-! ## Smoke tests -/

-- exp(0) = 1: exact case
#eval
  letI : FloatFormat := FloatFormat.Binary16.toFloatFormat
  expComputableRun (0 : FiniteFp)

-- exp(1) for binary16 (s=false, e=0, m=2^10=1024)
#eval
  letI : FloatFormat := FloatFormat.Binary16.toFloatFormat
  expComputableRun ⟨false, 0, 1024, by native_decide⟩

