import Flean.Operations.Exp
import Flean.Operations.ExpTaylor
import Flean.NumberTheory.ExpEffectiveBound
import Flean.NumberTheory.PadeExp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Computable `ExpRefExec` and `ExpRefExecSound` Instances

Provides a fully verified computable `exp` for floating-point arithmetic. The computation
returns either an exact representation or a "sticky cell" bracketing `exp(x)`, and the
proof establishes that the result is always correct. **All proofs are sorry-free.**

## Algorithm

1. **Special case**: `x = ±0` → return exact `exp(0) = 1`.
2. **Argument reduction** (`expArgRedK`): compute `k = round(x / ln 2)` using a rational
   approximation to `ln 2`, giving `exp(x) = 2^k · exp(r)` with `|r| < 1`.
3. **Iterative refinement** (`expExtractLoop`): at increasing precision levels `iter`,
   compute rational brackets `(lower, upper)` around `exp(x)` via Taylor series with
   explicit Lagrange remainder (`expBounds`), then check if `⌊lower · 2^s⌋ = ⌊upper · 2^s⌋`.
   When floors agree, we've identified the sticky cell.
4. **Output**: `{q, e_base, isExact}` where `exp(x) ∈ (2q · 2^e_base, 2(q+1) · 2^e_base)`.

## Proof structure

Two independent threads meet at `expLoop_sound`:

### Thread 1 — Bracket correctness (each step is sound)
```
taylorExpQ_lt_exp, exp_le_taylor_upper    -- Taylor bounds on exp(r)
    → expBounds_lower_lt_exp              -- lower < exp(x)
    → expBounds_exp_le_upper              -- exp(x) ≤ upper
    → inStickyInterval_of_bracket         -- floor agreement → sticky cell
    → expTryOne_sound                     -- if expTryOne succeeds, result is correct
    → expExtractLoop_sound                -- induction on fuel
```

### Thread 2 — Termination (the loop eventually succeeds within `expFuel x` steps)
```
pade_effective_delta (PadeExp.lean)        -- ∃ δ > 0, exp(x)·2^s avoids integers by ≥ δ
    → padeConvergenceN₀_le                -- Padé threshold ≤ 27·ab
    → pade_delta_log_bound                -- 1/δ ≤ 2^(500·ab·log(ab))
    → expBounds_width_bound               -- bracket width ≤ C · (1/N! + 1/2^N_ln2)
    → expFuel_sufficient                  -- ∃ iter < expFuel(x), width < δ
    → expTryOne_terminates
```

### Meeting point: `expLoop_sound`
Combines `expExtractLoop_sound` (correctness) with `expTryOne_terminates` (termination)
to prove the loop output is valid. The four `ExpRefExecSound` obligations then follow directly.
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
Linear terms cover the shift `s`, ln2 precision, and base Taylor order.
The `log₂` factor ensures the fuel grows faster than `N₀ · log(N₀ · b)`,
which is the effective threshold for the factorial decay in the bracket width
to overcome the Padé irrationality denominator `D = N₀! · b^{N₀} · |P_{N₀}|`. -/
private def expFuel (x : ℚ) : ℕ :=
  let ab := x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den + FloatFormat.prec.toNat + 100
  100 * ab * (Nat.log2 ab + 1) + 1000

/-! ## Constants -/

/-- Number of Taylor terms. With mod-ln(2) reduction, `|r| ≤ ln(2)/2 < 1/2`,
so no input-dependent adjustment is needed. -/
private def expNumTerms : ℕ := FloatFormat.prec.toNat + 10

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
    expShift r ≤ ((FloatFormat.prec.toNat : ℤ) + 4 - Int.log 2 r).toNat := by
  simp only [expShift]
  have h := int_log_le_nat_log2_diff r hr
  exact Int.toNat_le_toNat (by omega)

omit [FloatFormat] in
/-- `exp(2) < 8`, derived from `exp(1) < 2.7182818286`. -/
private lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h1 := Real.exp_one_lt_d9
  calc Real.exp 2 = Real.exp (1 + 1) := by norm_num
    _ = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
    _ < 2.7182818286 * 2.7182818286 :=
        mul_lt_mul h1 h1.le (by positivity) (by positivity)
    _ < 8 := by norm_num

omit [FloatFormat] in
/-- The r-interval width from `expRIntervalWith` is `k.natAbs / 2^N_ln2 < 1`
when `N_ln2 ≥ Nat.log2(k.natAbs) + 1`. -/
private lemma expRIntervalWith_width_lt_one (x : ℚ) (k : ℤ)
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
private theorem expBounds_int_log_ge (x : ℚ) (k : ℤ) (iter : ℕ)
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
            exact mul_le_mul_of_nonneg_right h_lr (zpow_nonneg (by norm_num) _)
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
                mul_le_mul_of_nonneg_left h_ratio (pow_nonneg hy_nonneg _)
            _ = (y ^ (N + 1) / ((N + 1).factorial : ℝ)) *
                (2 * ((N + 1).factorial : ℝ) * (↑(N + 1 : ℕ) : ℝ)) := by
                field_simp
            _ ≤ Real.exp y * (2 * ((N + 1).factorial : ℝ) * (↑(N + 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right h_term (by positivity)
            _ = 2 * Real.exp y * ((N + 1).factorial * (↑(N + 1 : ℕ) : ℝ)) := by ring
        -- Combine: denom ≤ 3*exp(y) < 24 ≤ 32
        calc (denom : ℝ) = (taylorExpQ (-r_lo) N : ℝ) +
              (taylorRemainder (-r_lo) (N + 1) : ℝ) := by push_cast [hdenom_def]; rfl
          _ ≤ Real.exp y + 2 * Real.exp y := by linarith [h_taylor]
          _ = 3 * Real.exp y := by ring
          _ < 3 * 8 := by linarith [h_exp]
          _ ≤ 32 := by norm_num)

/-- The shift `s = expShift(lower)` is uniformly bounded across all iterations.
Uses `expBounds_int_log_ge` to bound `Int.log 2 lower ≥ k - 5`, then
`expShift_le_of_int_log` gives `s ≤ prec + 4 - (k - 5) = prec + 9 - k ≤ prec + 9 + |k|`. -/
private theorem expShift_bound (x : ℚ) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ∃ S : ℕ, ∀ iter, expShift (expBounds x k iter).1 ≤ S :=
  ⟨FloatFormat.prec.toNat + 9 + k.natAbs, fun iter => by
    have hlower_pos := expBounds_lower_pos x k iter
    have hlog_ge := expBounds_int_log_ge x k iter hk_bound
    have hshift := expShift_le_of_int_log _ hlower_pos
    have : (FloatFormat.prec.toNat : ℤ) + 4 - Int.log 2 (expBounds x k iter).1 ≤
           FloatFormat.prec.toNat + 9 + k.natAbs := by
      have : Int.log 2 (expBounds x k iter).1 ≥ k - 5 := hlog_ge
      have : k ≤ k.natAbs := Int.le_natAbs
      omega
    exact le_trans hshift (Int.toNat_le_toNat this)⟩

omit [FloatFormat] in
/-- MVT-type bound: `exp(b) - exp(a) ≤ exp(b) * (b - a)` for `a ≤ b`. -/
private theorem exp_sub_le_mul_exp (a b : ℝ) :
    Real.exp b - Real.exp a ≤ Real.exp b * (b - a) := by
  have h1 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
    linarith [Real.add_one_le_exp (-(b - a))]
  have h2 : Real.exp b * (1 - (b - a)) ≤ Real.exp b * Real.exp (-(b - a)) :=
    mul_le_mul_of_nonneg_left h1 (Real.exp_pos b).le
  have h3 : Real.exp b * Real.exp (-(b - a)) = Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  linarith

omit [FloatFormat] in
/-- The r-interval width from `expRIntervalWith` is at most `k.natAbs / 2^N_ln2` (in ℝ). -/
private lemma expRIntervalWith_width_le (x : ℚ) (k : ℤ) (lo2 : ℚ) (N_ln2 : ℕ) :
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
private lemma expBounds_r_width_le (r_lo r_hi : ℚ) (N : ℕ) (hN : 0 < N)
    (hr_lo_lt1 : (r_lo : ℝ) < 1) (hr_hi_gt_m1 : -(1 : ℝ) < (r_hi : ℝ))
    (hr_lo_gt_m2 : -(2 : ℝ) < (r_lo : ℝ)) (hr_hi_lt2 : (r_hi : ℝ) < 2)
    (hr_le : (r_lo : ℝ) ≤ (r_hi : ℝ)) :
    ((if (0 : ℚ) ≤ r_hi then (taylorExpQ r_hi N + taylorRemainder r_hi (N + 1) : ℚ)
      else (1 / taylorExpQ (-r_hi) N : ℚ)) : ℝ) -
    ((if (0 : ℚ) ≤ r_lo then (taylorExpQ r_lo N : ℚ)
      else (1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1)) : ℚ)) : ℝ) ≤
    (2 : ℝ) ^ (N + 2) * (↑(N + 2) : ℝ) / (↑(N + 1).factorial * (↑(N + 1) : ℝ)) +
    8 * ((r_hi : ℝ) - (r_lo : ℝ)) := by
  -- Key facts
  have hexp_sub := exp_sub_le_mul_exp (r_lo : ℝ) (r_hi : ℝ)
  have hexp_hi_lt8 : Real.exp (r_hi : ℝ) < 8 :=
    lt_trans (Real.exp_lt_exp_of_lt hr_hi_lt2) exp_two_lt_eight
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
          mul_le_mul_of_nonneg_right (le_of_lt hexp_hi_lt8) hDr_nn
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
    -- Upper: 1/S_N(-r_hi) - exp(r_hi) ≤ R(2)
    -- (exp(-r_hi) - S_N(-r_hi))/(S_N(-r_hi)*exp(-r_hi)) ≤ R(-r_hi) ≤ R(2)
    have hS_hi_ge1 := taylorExpQ_ge_one (-r_hi) habs_hi N
    have hS_hi_pos : (0 : ℝ) < (taylorExpQ (-r_hi) N : ℝ) :=
      by exact_mod_cast lt_of_lt_of_le one_pos hS_hi_ge1
    have hS_hi_le := taylorExpQ_le_exp (-r_hi) habs_hi N
    have hexp_mhi_upper := exp_le_taylor_upper (-r_hi) habs_hi (le_of_lt habs_hi_lt1) N hN
    have hR_hi := taylorRemainder_le_of_le (-r_hi) 2 N hN habs_hi
      (le_of_lt (by linarith : ((-r_hi : ℚ) : ℝ) < 2))
    have hexp_mhi_pos := Real.exp_pos ((-r_hi : ℚ) : ℝ)
    have hR_mhi_nn : 0 ≤ (taylorRemainder (-r_hi) (N + 1) : ℝ) := by
      unfold taylorRemainder; simp only [show N + 1 ≠ 0 from by omega, ↓reduceIte]
      exact_mod_cast div_nonneg (mul_nonneg (pow_nonneg habs_hi _) (by positivity)) (by positivity)
    have h_up : 1 / (taylorExpQ (-r_hi) N : ℝ) - Real.exp (r_hi : ℝ) ≤
        (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by
      rw [show Real.exp (r_hi : ℝ) = (Real.exp ((-r_hi : ℚ) : ℝ))⁻¹ from by
            rw [show ((-r_hi : ℚ) : ℝ) = -((r_hi : ℚ) : ℝ) from by push_cast; ring,
                Real.exp_neg, inv_inv],
          one_div,
          show (taylorExpQ (-r_hi) N : ℝ)⁻¹ - (Real.exp ((-r_hi : ℚ) : ℝ))⁻¹ =
            (Real.exp ((-r_hi : ℚ) : ℝ) - (taylorExpQ (-r_hi) N : ℝ)) /
            ((taylorExpQ (-r_hi) N : ℝ) * Real.exp ((-r_hi : ℚ) : ℝ)) from by field_simp]
      calc (Real.exp ((-r_hi : ℚ) : ℝ) - (taylorExpQ (-r_hi) N : ℝ)) /
              ((taylorExpQ (-r_hi) N : ℝ) * Real.exp ((-r_hi : ℚ) : ℝ))
          ≤ (taylorRemainder (-r_hi) (N + 1) : ℝ) /
              ((taylorExpQ (-r_hi) N : ℝ) * Real.exp ((-r_hi : ℚ) : ℝ)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            linarith [hexp_mhi_upper]
        _ ≤ (taylorRemainder (-r_hi) (N + 1) : ℝ) / 1 :=
            div_le_div_of_nonneg_left hR_mhi_nn one_pos (by
              calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
                _ ≤ (taylorExpQ (-r_hi) N : ℝ) * Real.exp ((-r_hi : ℚ) : ℝ) :=
                  mul_le_mul (by exact_mod_cast hS_hi_ge1)
                    (Real.one_le_exp (by exact_mod_cast habs_hi))
                    zero_le_one (by positivity))
        _ ≤ (taylorRemainder (2 : ℚ) (N + 1) : ℝ) := by rw [div_one]; exact hR_hi
    -- Lower bound from recip_bound
    have h_lo := recip_bound (-r_lo) habs_lo habs_lo_lt2
    simp only [show -((-r_lo : ℚ) : ℝ) = (r_lo : ℝ) from by push_cast; ring] at h_lo
    linarith

/-- Upper bound on the bracket width `(upper - lower)` at iteration `iter`.
The Taylor remainder contributes `≤ 2^(N+2)·(N+2)/((N+1)!·(N+1))` (using `|r| < 2`)
and the ln2 error contributes `≤ 8·(|k|+1)/2^{N_ln2}` to the width. -/
private theorem expBounds_width_bound (x : ℚ) (hx : x ≠ 0) (k : ℤ) (iter : ℕ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    let (lower, upper) := expBounds x k iter
    let N := expNumTerms + iter * 10
    let N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50
    ((upper : ℝ) - (lower : ℝ)) * 2 ^ (expShift lower) ≤
      (2 : ℝ) ^ (k.natAbs + expShift lower) *
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
  have h2s_pos : (0 : ℝ) < 2 ^ expShift lower := by positivity
  suffices h : (upper : ℝ) - (lower : ℝ) ≤ (2:ℝ) ^ k.natAbs * B by
    have h2s_nn := h2s_pos.le
    calc ((upper : ℝ) - lower) * 2 ^ expShift lower
        ≤ (2:ℝ) ^ k.natAbs * B * 2 ^ expShift lower :=
          mul_le_mul_of_nonneg_right h h2s_nn
      _ = 2 ^ (k.natAbs + expShift lower) * B := by rw [pow_add]; ring
  -- Set up the r-level variables from expBounds definition
  set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50 with hN_ln2_def
  set lo2 := ln2SeriesSum N_ln2 with hlo2_def
  set hi2 := lo2 + 1 / 2 ^ N_ln2 with hhi2_def
  set rp := expRIntervalWith x k lo2 hi2 with hrp_def
  set r_lo := rp.1 with hr_lo_def
  set r_hi := rp.2 with hr_hi_def
  set N := expNumTerms + iter * 10 with hN_def
  set upper_r :=
    (if (0 : ℚ) ≤ r_hi then taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)
     else 1 / taylorExpQ (-r_hi) N) with hur_def
  set lower_r :=
    (if (0 : ℚ) ≤ r_lo then taylorExpQ r_lo N
     else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))) with hlr_def
  -- Factor: upper = upper_r * 2^k, lower = lower_r * 2^k
  have h_upper_eq : upper = upper_r * (2:ℚ) ^ k := by
    simp only [upper, upper_r, expBounds, hrp_def, hN_def, hN_ln2_def, hlo2_def]; ring
  have h_lower_eq : lower = lower_r * (2:ℚ) ^ k := by
    simp only [lower, lower_r, expBounds, hrp_def, hN_def, hN_ln2_def, hlo2_def]; ring
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
      8 * ((r_hi : ℝ) - (r_lo : ℝ)) := by
    simp only [hur_def, hlr_def]
    split_ifs at hr_width' ⊢ <;> push_cast at hr_width' ⊢ <;> linarith [hr_width']
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
        ≤ 8 * ((↑k.natAbs + 1) / 2 ^ N_ln2) := mul_le_mul_of_nonneg_left h2 (by norm_num)
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
  have h2k_pos : (0:ℝ) < (2:ℝ) ^ k := zpow_pos (by norm_num) k
  have hur_lr_nn : 0 ≤ (upper_r : ℝ) - (lower_r : ℝ) := by
    have h1 : 0 ≤ ((upper_r : ℝ) - (lower_r : ℝ)) * (2:ℝ) ^ k := by
      have := hwidth_nn; rw [h_factor] at this; exact this
    exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (2:ℝ) ^ k * ((upper_r : ℝ) - lower_r))
      h2k_pos
  rw [h_factor]
  calc ((upper_r : ℝ) - lower_r) * (2:ℝ) ^ k
      ≤ ((upper_r : ℝ) - lower_r) * (2:ℝ) ^ (k.natAbs : ℤ) := by
        apply mul_le_mul_of_nonneg_left _ hur_lr_nn
        exact zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2:ℝ)) Int.le_natAbs
    _ ≤ B * (2:ℝ) ^ (k.natAbs : ℤ) :=
        mul_le_mul_of_nonneg_right hur_lr_le_B (by positivity)
    _ = (2:ℝ) ^ k.natAbs * B := by
        rw [show (2:ℝ) ^ (k.natAbs : ℤ) = (2:ℝ) ^ k.natAbs from zpow_natCast 2 k.natAbs]; ring

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
  have ⟨S, hS⟩ := expShift_bound x k hk_bound
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
      exact mul_le_mul_of_nonneg_left h1' (by positivity)
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
          < A * (eps / (2 * C * A)) := mul_lt_mul_of_pos_left hgeom_bound hA_pos
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
  have hbound' : ((upper : ℝ) - (lower : ℝ)) * 2 ^ expShift lower ≤
      (2 : ℝ) ^ (k.natAbs + expShift lower) *
        ((2 : ℝ) ^ (expNumTerms + iter * 10 + 2) *
          (expNumTerms + iter * 10 + 2 : ℝ) /
          ((expNumTerms + iter * 10 + 1).factorial * (expNumTerms + iter * 10 + 1)) +
         8 * (k.natAbs + 1 : ℝ) /
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
  have herr_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (expNumTerms + iter * 10 + 2) *
      (expNumTerms + iter * 10 + 2 : ℝ) /
      ((expNumTerms + iter * 10 + 1).factorial * (expNumTerms + iter * 10 + 1)) +
      8 * (k.natAbs + 1 : ℝ) /
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

-- |padeP N x| ≤ 4^N * exp(|x|).
-- Proof: |padeP N x| ≤ Σ C(2N-k,N)/k! * |x|^k ≤ 4^N * Σ |x|^k/k! ≤ 4^N * exp(|x|).
private lemma padeP_abs_le (N : ℕ) (x : ℝ) :
    |padeP N x| ≤ (4 : ℝ) ^ N * Real.exp |x| := by
  simp only [padeP]
  have h4N_pos : (0 : ℝ) ≤ (4 : ℝ) ^ N := pow_nonneg (by norm_num) N
  calc |∑ k ∈ Finset.range (N + 1), padeCoeff N k * (-x) ^ k|
      ≤ ∑ k ∈ Finset.range (N + 1), |padeCoeff N k * (-x) ^ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range (N + 1), padeCoeff N k * |x| ^ k := by
        congr 1; ext k; simp [padeCoeff, abs_mul, abs_div, abs_pow]
    _ ≤ ∑ k ∈ Finset.range (N + 1), (4 : ℝ) ^ N * (|x| ^ k / k.factorial) := by
        apply Finset.sum_le_sum; intro k hk
        have hk_le : k ≤ N := by simp [Finset.mem_range] at hk; omega
        simp only [padeCoeff, div_mul_eq_mul_div]
        have hcoeff : (Nat.choose (2 * N - k) N : ℝ) ≤ (4 : ℝ) ^ N := by
          have h4eq : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * N) := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, ← pow_mul]
          rw [h4eq]
          calc (Nat.choose (2 * N - k) N : ℝ) ≤ (2 : ℝ) ^ (2 * N - k) := by
                exact_mod_cast Nat.choose_le_two_pow (2 * N - k) N
            _ ≤ (2 : ℝ) ^ (2 * N) := pow_le_pow_right₀ (by norm_num) (by omega)
        -- Goal: C(2N-k,N) * |x|^k / k! ≤ 4^N * (|x|^k / k!)
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hcoeff
          (div_nonneg (pow_nonneg (abs_nonneg x) k)
            (Nat.cast_pos.mpr (Nat.factorial_pos k)).le)
    _ = (4 : ℝ) ^ N * ∑ k ∈ Finset.range (N + 1), |x| ^ k / k.factorial := by
        rw [← Finset.mul_sum]
    _ ≤ (4 : ℝ) ^ N * Real.exp |x| := by
        apply mul_le_mul_of_nonneg_left _ h4N_pos
        exact Real.sum_le_exp_of_nonneg (abs_nonneg x) (N + 1)

-- Helper: 2^a * (1/2)^(a+b) = (1/2)^b
private lemma two_pow_mul_half_pow (a b : ℕ) :
    (2:ℝ)^a * (1/2:ℝ)^(a+b) = (1/2:ℝ)^b := by
  rw [one_div_pow, one_div_pow, pow_add]
  field_simp

-- Helper: err₁ bound from factorial geometric decay
private lemma err1_factorial_bound (N : ℕ) (hN : 4 ≤ N) :
    (2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)) ≤ (8/3:ℝ) * (1/2:ℝ)^(N-4) := by
  have hfac_pos : (0:ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h_fac : (2:ℝ)^N / ↑N.factorial ≤
      (2:ℝ)^4 / ↑(4:ℕ).factorial * (1/2:ℝ)^(N-4) := by
    have := pow_div_factorial_geometric_bound 2 (by norm_num) 2 (by norm_num) N (by omega)
    simpa using this
  have h_init : (2:ℝ)^4 / ↑(4:ℕ).factorial = 2/3 := by norm_num [Nat.factorial]
  -- 2^(N+2) = 4 * 2^N
  have h2N2 : (2:ℝ)^(N+2) = 4 * (2:ℝ)^N := by rw [pow_add]; ring
  -- (N+1)! = (N+1) * N!
  have hfac_succ : ((N+1).factorial : ℝ) = (N+1:ℝ) * N.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  -- (N+2) ≤ (N+1)^2
  have hN_r : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hN2_le : (N+2:ℝ) ≤ (N+1:ℝ) * (N+1:ℝ) := by nlinarith
  rw [h2N2, hfac_succ]
  -- 4*2^N*(N+2) / ((N+1)*N!*(N+1)) ≤ 4*2^N/N!
  have h2N_pos : (0:ℝ) < (2:ℝ)^N := by positivity
  have herr1_aux : 4 * (2:ℝ)^N * (N+2:ℝ) / ((N+1:ℝ) * ↑N.factorial * (N+1:ℝ)) ≤
      4 * (2:ℝ)^N / ↑N.factorial := by
    have h_cancel : (0:ℝ) < 4 * (2:ℝ)^N * ↑N.factorial := by positivity
    rw [div_le_div_iff₀ (by positivity) hfac_pos]
    -- Goal: 4*2^N*(N+2)*N! ≤ 4*2^N * ((N+1)*N!*(N+1))
    -- ⟺ (N+2) ≤ (N+1)*(N+1) after cancelling 4*2^N*N!
    have : 4 * (2:ℝ)^N * (N+2:ℝ) * ↑N.factorial =
        4 * (2:ℝ)^N * ↑N.factorial * (N+2:ℝ) := by ring
    have : 4 * (2:ℝ)^N * ((N+1:ℝ) * ↑N.factorial * (N+1:ℝ)) =
        4 * (2:ℝ)^N * ↑N.factorial * ((N+1:ℝ) * (N+1:ℝ)) := by ring
    nlinarith
  -- 4*2^N/N! ≤ (8/3)*(1/2)^(N-4)
  have h4_fac : 4 * (2:ℝ)^N / ↑N.factorial ≤ (8/3:ℝ) * (1/2:ℝ)^(N-4) := by
    have : 4 * ((2:ℝ)^N / ↑N.factorial) ≤ 4 * ((2:ℝ)^4 / ↑(4:ℕ).factorial * (1/2:ℝ)^(N-4)) :=
      mul_le_mul_of_nonneg_left h_fac (by norm_num)
    calc 4 * (2:ℝ)^N / ↑N.factorial
        = 4 * ((2:ℝ)^N / ↑N.factorial) := by ring
      _ ≤ 4 * ((2:ℝ)^4 / ↑(4:ℕ).factorial * (1/2:ℝ)^(N-4)) := this
      _ = (8/3:ℝ) * (1/2:ℝ)^(N-4) := by rw [h_init]; ring
  calc 4 * (2:ℝ)^N * (N+2:ℝ) / ((N+1:ℝ) * ↑N.factorial * (N+1:ℝ))
      ≤ 4 * (2:ℝ)^N / ↑N.factorial := herr1_aux
    _ ≤ (8/3:ℝ) * (1/2:ℝ)^(N-4) := h4_fac

-- Helper: bound padeConvergenceN₀ linearly in ab
private lemma padeConvergenceN₀_le (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0) (s : ℕ)
    (ab : ℕ) (hab : a.natAbs ^ 2 / b + a.natAbs + b + 100 ≤ ab) (hs : s ≤ ab) :
    padeConvergenceN₀ a b s ≤ 27 * ab := by
  simp only [padeConvergenceN₀]
  set x := (a : ℝ) / (b : ℝ) with hx_def
  set d := 4 * (b : ℝ) * x ^ 2 with hd_def
  set m := ⌈d⌉₊ with hm_def
  set K := 2 ^ (s + 1) * Real.exp (2 * |x|) * (2 * |x|) with hK_def
  set C := d ^ (2 * m) / ((2 * m).factorial : ℝ) with hC_def
  set M := Nat.log2 (⌈2 * (K + 1) * (C + 1)⌉₊) + 1 with hM_def
  -- Goal: 2 * m + M ≤ 27 * ab
  have hab_ge : 100 ≤ ab := by have : 0 ≤ a.natAbs ^ 2 / b := Nat.zero_le _; omega
  have ha_le : a.natAbs ≤ ab := by have : 0 ≤ a.natAbs ^ 2 / b := Nat.zero_le _; omega
  have hb_le : b ≤ ab := by have : 0 ≤ a.natAbs ^ 2 / b := Nat.zero_le _; omega
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_r
  have hx_abs : |x| ≤ (a.natAbs : ℝ) := by
    rw [hx_def, abs_div, ← Int.cast_abs, Nat.cast_natAbs, abs_of_pos hb_r]
    exact le_trans (div_le_div_of_nonneg_left (by positivity) one_pos
      (by exact_mod_cast hb)) (by rw [div_one])
  have hx_le_ab : |x| ≤ (ab : ℝ) := le_trans hx_abs (by exact_mod_cast ha_le)
  -- ====== Part 1: m ≤ 5 * ab ======
  -- d = 4*b*(a/b)^2 = 4*a^2/b. Since a^2 < b*(ab+1), d < 4*(ab+1) ≤ 5*ab.
  have ha2b : a.natAbs ^ 2 < b * (ab + 1) := by
    have hq : a.natAbs ^ 2 / b ≤ ab := by
      have := Nat.zero_le (a.natAbs ^ 2 / b); omega
    have hdm := Nat.div_add_mod (a.natAbs ^ 2) b
    have hml := Nat.mod_lt (a.natAbs ^ 2) hb
    have hbq := Nat.mul_le_mul_left b hq
    -- natAbs^2 = b*(natAbs^2/b) + rem, b*(natAbs^2/b) ≤ b*ab, rem < b
    -- so natAbs^2 < b*ab + b = b*(ab+1)
    linarith
  have hd_le : d ≤ 5 * (ab : ℝ) := by
    suffices d ≤ 4 * ((ab : ℝ) + 1) from
      le_trans this (by linarith [show (4 : ℝ) ≤ ab from by exact_mod_cast (show 4 ≤ ab by omega)])
    have hd_eq : d = 4 * (a : ℝ) ^ 2 / (b : ℝ) := by
      rw [hd_def, hx_def]; field_simp
    have h_abs_a : |(a : ℝ)| = (a.natAbs : ℝ) := by
      rw [← Int.cast_abs, Nat.cast_natAbs]
    have ha_sq : (a : ℝ) ^ 2 = (a.natAbs : ℝ) ^ 2 := by rw [← sq_abs, h_abs_a]
    rw [hd_eq, ha_sq, div_le_iff₀ hb_r]
    have : (a.natAbs : ℝ) ^ 2 < (b : ℝ) * ((ab : ℝ) + 1) := by exact_mod_cast ha2b
    nlinarith
  have hd_nonneg : 0 ≤ d := by rw [hd_def]; positivity
  have hm_le : m ≤ 5 * ab := by
    rw [hm_def]
    exact Nat.ceil_le.mpr (by push_cast; linarith)
  -- ====== Part 2: M ≤ 17 * ab ======
  -- Strategy: bound 2*(K+1)*(C+1) ≤ 2^(16*ab+5) < 2^(17*ab)
  -- Sub-step: exp(n*ab) ≤ 3^(n*ab) ≤ 4^(n*ab) = 2^(2*n*ab)
  have hexp1_le3 : Real.exp 1 ≤ 3 :=
    le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hexp_le_pow (n : ℕ) : Real.exp (↑n * (ab : ℝ)) ≤ (2 : ℝ) ^ (2 * n * ab) := by
    calc Real.exp (↑n * (ab : ℝ))
        = Real.exp (↑(n * ab) * 1) := by push_cast; ring_nf
      _ = (Real.exp 1) ^ (n * ab) := Real.exp_nat_mul _ _
      _ ≤ 3 ^ (n * ab) := pow_le_pow_left₀ (Real.exp_pos _).le hexp1_le3 _
      _ ≤ (2 ^ 2) ^ (n * ab) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (2 : ℝ) ^ (2 * n * ab) := by rw [← pow_mul]; ring_nf
  -- C ≤ exp(d) ≤ exp(5*ab) ≤ 2^(10*ab)
  have hC_le : C ≤ (2 : ℝ) ^ (10 * ab) := by
    calc C ≤ Real.exp d := Real.pow_div_factorial_le_exp d hd_nonneg _
      _ ≤ Real.exp (5 * (ab : ℝ)) := Real.exp_le_exp_of_le hd_le
      _ ≤ (2 : ℝ) ^ (2 * 5 * ab) := hexp_le_pow 5
      _ = (2 : ℝ) ^ (10 * ab) := by ring_nf
  -- C + 1 ≤ 2^(10*ab+1)
  have hC1 : C + 1 ≤ (2 : ℝ) ^ (10 * ab + 1) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (10 * ab) := one_le_pow₀ (by norm_num)
    have : C + 1 ≤ (2 : ℝ) ^ (10 * ab) + (2 : ℝ) ^ (10 * ab) := by linarith
    calc C + 1 ≤ (2 : ℝ) ^ (10 * ab) + (2 : ℝ) ^ (10 * ab) := this
      _ = 2 * (2 : ℝ) ^ (10 * ab) := by ring
      _ = (2 : ℝ) ^ (10 * ab + 1) := by
          rw [show 10 * ab + 1 = (10 * ab).succ from rfl, pow_succ]
          ring
  -- K ≤ 2^(ab+1) * exp(2*ab) * 2*ab ≤ 2^(ab+1) * 2^(4*ab) * 2^(ab+1) = 2^(6*ab+2)
  have hK_bound : K ≤ (2 : ℝ) ^ (6 * ab + 2) := by
    have hexp2 : Real.exp (2 * |x|) ≤ (2 : ℝ) ^ (4 * ab) := by
      calc Real.exp (2 * |x|) ≤ Real.exp (2 * (ab : ℝ)) :=
            Real.exp_le_exp_of_le (by nlinarith)
        _ ≤ (2 : ℝ) ^ (2 * 2 * ab) := hexp_le_pow 2
        _ = (2 : ℝ) ^ (4 * ab) := by ring_nf
    have h2x : 2 * |x| ≤ 2 * (2 : ℝ) ^ ab := by
      calc 2 * |x| ≤ 2 * (ab : ℝ) := by linarith
        _ ≤ 2 * (2 : ℝ) ^ ab := by
            linarith [show (ab : ℝ) ≤ 2 ^ ab from by exact_mod_cast Nat.lt_two_pow_self.le]
    calc K = 2 ^ (s + 1) * Real.exp (2 * |x|) * (2 * |x|) := rfl
      _ ≤ (2 : ℝ) ^ (ab + 1) * (2 : ℝ) ^ (4 * ab) * (2 * (2 : ℝ) ^ ab) := by
          apply mul_le_mul
          · apply mul_le_mul
            · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
            · exact hexp2
            · exact (Real.exp_pos _).le
            · exact pow_nonneg (by norm_num) _
          · exact h2x
          · positivity
          · positivity
      _ = (2 : ℝ) ^ (6 * ab + 2) := by
          rw [show (2 : ℝ) * (2 : ℝ) ^ ab = (2 : ℝ) ^ (ab + 1) from by
            rw [show ab + 1 = ab.succ from rfl, pow_succ]; ring]
          rw [← pow_add, ← pow_add]
          congr 1; omega
  -- K + 1 ≤ 2^(6*ab+3)
  have hK1 : K + 1 ≤ (2 : ℝ) ^ (6 * ab + 3) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (6 * ab + 2) := one_le_pow₀ (by norm_num)
    have : K + 1 ≤ 2 * (2 : ℝ) ^ (6 * ab + 2) := by linarith
    rw [show 6 * ab + 3 = (6 * ab + 2) + 1 from by omega, pow_add, pow_one, mul_comm]
    exact this
  -- 2*(K+1)*(C+1) ≤ 2 * 2^(6*ab+3) * 2^(10*ab+1) = 2^(16*ab+5)
  have hprod : 2 * (K + 1) * (C + 1) ≤ (2 : ℝ) ^ (16 * ab + 5) := by
    calc 2 * (K + 1) * (C + 1)
        ≤ 2 * (2 : ℝ) ^ (6 * ab + 3) * (2 : ℝ) ^ (10 * ab + 1) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hK1 (by norm_num))
            hC1 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (16 * ab + 5) := by
          rw [mul_assoc, ← pow_add,
            show 16 * ab + 5 = (6 * ab + 3 + (10 * ab + 1)).succ from by omega, pow_succ]
          ring
  -- ⌈2*(K+1)*(C+1)⌉₊ < 2^(17*ab)
  have hceil : ⌈2 * (K + 1) * (C + 1)⌉₊ < 2 ^ (17 * ab) := by
    have h16_17 : 16 * ab + 5 < 17 * ab := by omega
    have hprod_nat : ⌈2 * (K + 1) * (C + 1)⌉₊ ≤ 2 ^ (16 * ab + 5) := by
      have : (2 : ℝ) ^ (16 * ab + 5) = ((2 ^ (16 * ab + 5) : ℕ) : ℝ) := by push_cast; rfl
      rw [this] at hprod
      exact Nat.ceil_le.mpr (by exact_mod_cast hprod)
    calc ⌈2 * (K + 1) * (C + 1)⌉₊ ≤ 2 ^ (16 * ab + 5) := hprod_nat
      _ < 2 ^ (17 * ab) := Nat.pow_lt_pow_right (by norm_num) h16_17
  have hM_le : M ≤ 17 * ab := by
    rw [hM_def, Nat.log2_eq_log_two]
    have hlog : Nat.log 2 (⌈2 * (K + 1) * (C + 1)⌉₊) < 17 * ab :=
      Nat.log_lt_of_lt_pow' (by omega) hceil
    omega
  -- ====== Combine: N₀ = 2*m + M ≤ 10*ab + 17*ab = 27*ab ======
  calc 2 * m + M ≤ 2 * (5 * ab) + 17 * ab := by omega
    _ = 27 * ab := by ring

/-- **Fuel sufficiency**: within `expFuel x` iterations, `expTryOne` succeeds.
This is the quantitative core combining all three ingredients:
1. Effective δ from `pade_effective_delta` for the shift `s` at each iteration
2. Bracket width bound from `expBounds_width_bound`
3. Floor agreement from `expTryOne_of_tight_bracket`

The proof shows the factorial decay of the bracket width dominates the
Padé effective δ bound within the quadratic fuel budget. -/
private lemma pade_delta_log_bound (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0) (s : ℕ)
    (ab : ℕ) (hab : a.natAbs ^ 2 / b + a.natAbs + b + 100 ≤ ab) (hs : s ≤ ab) :
    let N₀ := padeConvergenceN₀ a b s
    let D := max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ ((a : ℝ) / b)|)
                 (((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) *
                   |padeP (N₀ + 1) ((a : ℝ) / b)|)
    ∃ L : ℕ, L ≤ 500 * ab * (Nat.log2 ab + 1) ∧ 2 * D ≤ (2 : ℝ) ^ L := by
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
      · simp [Nat.factorial, padeP, padeCoeff, Finset.sum_range_one]
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
        have : (N : ℝ) ^ N ≤ (N : ℝ) ^ (28 * ab) :=
          pow_le_pow_right₀ (by exact_mod_cast hN_pos) hN_le
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
        calc ((4 : ℝ) * b) ^ N ≤ ((4 : ℝ) * b) ^ (28 * ab) :=
              pow_le_pow_right₀ (show (1 : ℝ) ≤ 4 * b by
                have : (1 : ℝ) ≤ b := by exact_mod_cast hb
                linarith) hN_le
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
          _ ≤ (ab : ℝ) ^ ab :=
              pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ ab by omega)) ha_le
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
  -- Combine: 2*D ≤ 2 * ab^(113*ab) ≤ 2^(1 + 113*ab*(log₂(ab)+1)) ≤ 2^(500*ab*(log₂(ab)+1))
  refine ⟨500 * ab * (Nat.log2 ab + 1), le_refl _, ?_⟩
  have hab_pos : (0 : ℝ) < ab := by exact_mod_cast (show 0 < ab by omega)
  calc 2 * max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)
               (N₁.factorial * (b : ℝ) ^ N₁ * |padeP N₁ x|)
      ≤ 2 * (ab : ℝ) ^ (113 * ab) := by linarith [hD_pow]
    _ ≤ 2 * (2 : ℝ) ^ (113 * ab * (Nat.log2 ab + 1)) := by linarith [hpow_bound]
    _ ≤ (2 : ℝ) ^ 1 * (2 : ℝ) ^ (113 * ab * (Nat.log2 ab + 1)) := by norm_num
    _ = (2 : ℝ) ^ (1 + 113 * ab * (Nat.log2 ab + 1)) := by rw [← pow_add]
    _ ≤ (2 : ℝ) ^ (500 * ab * (Nat.log2 ab + 1)) := by
        apply pow_le_pow_right₀ (by norm_num)
        have h1 : 1 + 113 * ab * (Nat.log2 ab + 1) ≤ 500 * ab * (Nat.log2 ab + 1) := by
          have hX := Nat.zero_le (ab * (Nat.log2 ab + 1))
          have : 113 * (ab * (Nat.log2 ab + 1)) ≤ 499 * (ab * (Nat.log2 ab + 1)) :=
            Nat.mul_le_mul_right _ (by omega)
          have : 1 ≤ ab * (Nat.log2 ab + 1) :=
            le_trans (show 1 ≤ 100 * 1 by omega)
              (Nat.mul_le_mul hab_ge (by omega))
          linarith [show 113 * ab * (Nat.log2 ab + 1) = 113 * (ab * (Nat.log2 ab + 1)) by ring,
                    show 500 * ab * (Nat.log2 ab + 1) = 500 * (ab * (Nat.log2 ab + 1)) by ring]
        linarith

/-- **Heart of the termination proof.**

Shows that `expTryOne` succeeds at some iteration within `expFuel x` steps.
The proof constructs a concrete iteration `iter₀` and shows:
1. The Padé gap `δ` (from `pade_effective_delta`) satisfies `1/δ ≤ 2^L` with `L ≤ 500·ab·log₂(ab)`.
2. At `iter₀ = (L + 3|k| + prec + 20) / 10`, the bracket width `< δ`.
3. `iter₀ < expFuel x` since `expFuel x = 100·ab·(log₂(ab)+1) + 1000 ≫ L/10`. -/
private theorem expFuel_sufficient (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ∃ iter, iter < expFuel x ∧ (expTryOne x k iter).isSome = true := by
  have hnum_ne : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden_pos : 0 < x.den := x.den_pos
  -- Define ab early so the L bound can reference it in the induction.
  set ab := x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den +
    FloatFormat.prec.toNat + 100 with hab_def
  -- Define S (shift bound) concretely and prove it bounds expShift.
  have hS_bound : ∀ iter, expShift (expBounds x k iter).1 ≤
      FloatFormat.prec.toNat + 9 + k.natAbs := by
    intro iter
    have hlower_pos := expBounds_lower_pos x k iter
    have hlog_ge := expBounds_int_log_ge x k iter hk_bound
    have hshift := expShift_le_of_int_log _ hlower_pos
    have : (FloatFormat.prec.toNat : ℤ) + 4 - Int.log 2 (expBounds x k iter).1 ≤
           FloatFormat.prec.toNat + 9 + k.natAbs := by
      have : Int.log 2 (expBounds x k iter).1 ≥ k - 5 := hlog_ge
      have : k ≤ k.natAbs := Int.le_natAbs
      omega
    exact le_trans hshift (Int.toNat_le_toNat this)
  have hk_bound_nat : k.natAbs ≤ 2 * x.num.natAbs + 1 := by
    by_contra h; push_neg at h
    have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 :=
      lt_trans (by norm_num) Real.log_two_gt_d9
    have hlog2_pos : (0 : ℝ) < Real.log 2 := lt_trans (by norm_num) hlog2_gt
    have hden_r : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
    have hden_ge1 : (1 : ℝ) ≤ x.den := by exact_mod_cast x.den_pos
    have hx_abs : |(x : ℝ)| ≤ x.num.natAbs := by
      have h1 : |(x : ℝ)| = |(x.num : ℝ)| / x.den := by
        push_cast [Rat.cast_def]; rw [abs_div, abs_of_pos hden_r]
      rw [h1, ← Int.cast_abs, Nat.cast_natAbs]
      exact le_trans (div_le_div_of_nonneg_left (by positivity) one_pos hden_ge1) (by rw [div_one])
    have hk_r : (k.natAbs : ℝ) ≥ 2 * ↑x.num.natAbs + 2 := by exact_mod_cast h
    have : (k.natAbs : ℝ) * Real.log 2 ≥ ↑x.num.natAbs + 1 := by
      calc (k.natAbs : ℝ) * Real.log 2
          ≥ (2 * ↑x.num.natAbs + 2) * Real.log 2 := by nlinarith
        _ ≥ (2 * ↑x.num.natAbs + 2) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hlog2_gt.le (by positivity)
        _ = ↑x.num.natAbs + 1 := by ring
    have hk_ln2 : (k.natAbs : ℝ) * Real.log 2 < ↑x.num.natAbs + 1 := by
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
          calc x.num.natAbs * x.den ≤ x.num.natAbs * x.num.natAbs :=
                Nat.mul_le_mul_left _ h.le
            _ = x.num.natAbs ^ 2 := (sq x.num.natAbs).symm
        omega
    simp only [hab_def]; omega
  -- Steps 1+2: Uniform positive gap with bounded 1/δ.
  -- We induct on the shift bound T (with T ≤ ab) to produce δ and L together.
  have hx_eq : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := by
    push_cast [Rat.cast_def]; ring
  have ⟨δ, hδ_pos, L, hL_bound, hL_delta, hδ_gap⟩ :
      ∃ δ > 0, ∃ L : ℕ, L ≤ 500 * ab * (Nat.log2 ab + 1) ∧
      (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧
      ∀ iter, ∀ m : ℤ,
      |Real.exp (x : ℝ) * 2 ^ expShift (expBounds x k iter).1 - ↑m| ≥ δ := by
    -- Suffices to prove for all shifts ≤ T for some T ≥ shift bound
    suffices h_unif : ∀ T, T ≤ ab → ∃ δ > 0, ∃ L : ℕ,
        L ≤ 500 * ab * (Nat.log2 ab + 1) ∧ (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧
        ∀ s, s ≤ T → ∀ m : ℤ,
        |Real.exp (x : ℝ) * 2 ^ s - ↑m| ≥ δ by
      obtain ⟨δ, hδ_pos, L, hL, hLd, hδ⟩ :=
        h_unif (FloatFormat.prec.toNat + 9 + k.natAbs) hSab
      exact ⟨δ, hδ_pos, L, hL, hLd, fun iter m => hδ _ (hS_bound iter) m⟩
    intro T hT
    induction T with
    | zero =>
      obtain ⟨hD, hgap⟩ := pade_effective_delta x.num x.den hden_pos hnum_ne 0
      have ⟨L, hL_le, hLD⟩ := pade_delta_log_bound x.num x.den hden_pos hnum_ne 0 ab
        (by simp only [hab_def]; omega) (by omega)
      refine ⟨_, div_pos one_pos (mul_pos (by norm_num : (0:ℝ) < 2) hD),
             L, hL_le, ?_, fun s hs m => ?_⟩
      · rw [one_div_one_div]; exact hLD
      · interval_cases s; rw [hx_eq]; exact hgap m
    | succ n ih =>
      obtain ⟨δ₁, hδ₁_pos, L₁, hL₁_le, hL₁_d, hδ₁⟩ := ih (by omega)
      have ⟨hD, hgap⟩ := pade_effective_delta x.num x.den hden_pos hnum_ne (n + 1)
      set δ₂ := 1 / (2 * max ((padeConvergenceN₀ x.num x.den (n+1)).factorial *
        (x.den : ℝ) ^ padeConvergenceN₀ x.num x.den (n+1) *
        |padeP (padeConvergenceN₀ x.num x.den (n+1)) ((x.num : ℝ) / x.den)|)
        (((padeConvergenceN₀ x.num x.den (n+1) + 1).factorial *
        (x.den : ℝ) ^ (padeConvergenceN₀ x.num x.den (n+1) + 1) *
        |padeP (padeConvergenceN₀ x.num x.den (n+1) + 1) ((x.num : ℝ) / x.den)|)))
      have ⟨L₂, hL₂_le, hL₂_D⟩ := pade_delta_log_bound x.num x.den hden_pos hnum_ne (n+1) ab
        (by simp only [hab_def]; omega) (by omega)
      refine ⟨min δ₁ δ₂, lt_min hδ₁_pos (by positivity),
             max L₁ L₂, max_le hL₁_le hL₂_le, ?_, fun s hs m => ?_⟩
      · -- 1/min(δ₁,δ₂) ≤ 2^(max L₁ L₂)
        have hδ₂_pos : (0 : ℝ) < δ₂ := by positivity
        rcases le_total δ₁ δ₂ with h | h
        · rw [min_eq_left h]
          calc (1 : ℝ) / δ₁ ≤ (2 : ℝ) ^ L₁ := hL₁_d
            _ ≤ (2 : ℝ) ^ (max L₁ L₂) := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
        · rw [min_eq_right h]
          have h1 : (1 : ℝ) / δ₂ ≤ (2 : ℝ) ^ L₂ := by
            simp only [δ₂]; rw [one_div_one_div]; exact hL₂_D
          calc (1 : ℝ) / δ₂ ≤ (2 : ℝ) ^ L₂ := h1
            _ ≤ (2 : ℝ) ^ (max L₁ L₂) := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
      · rcases Nat.eq_or_lt_of_le hs with rfl | hlt
        · rw [hx_eq]; exact le_trans (min_le_right _ _) (hgap m)
        · exact le_trans (min_le_left _ _) (hδ₁ s (by omega) m)
  -- Step 3: Pick concrete iteration within fuel budget.
  set S := FloatFormat.prec.toNat + 9 + k.natAbs with hS_def
  have hS : ∀ iter, expShift (expBounds x k iter).1 ≤ S := hS_bound
  set iter := (L + 3 * k.natAbs + FloatFormat.prec.toNat + 20) / 10 with hiter_def
  have hiter_fuel : iter < expFuel x := by
    -- ab ≥ 100 and contains |k|, prec as summands
    have hab_ge : 100 ≤ ab := by
      have h1 : 0 ≤ x.num.natAbs ^ 2 / x.den := Nat.zero_le _
      have h2 : ab = x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den +
        FloatFormat.prec.toNat + 100 := rfl
      omega
    have hk_le : k.natAbs ≤ ab := by
      -- Step 1: k.natAbs ≤ 2 * x.num.natAbs + 1
      have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 :=
        lt_trans (by norm_num) Real.log_two_gt_d9
      have hlog2_pos : (0 : ℝ) < Real.log 2 := lt_trans (by norm_num) hlog2_gt
      -- |x| ≤ natAbs since |x| = |num|/den and den ≥ 1
      have hden_r : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
      have hden_ge1 : (1 : ℝ) ≤ x.den := by exact_mod_cast x.den_pos
      have hnum_abs : |(x.num : ℝ)| = (x.num.natAbs : ℝ) := by
        rw [← Int.cast_abs, Nat.cast_natAbs]
      have hx_abs : |(x : ℝ)| ≤ x.num.natAbs := by
        have h1 : |(x : ℝ)| = |(x.num : ℝ)| / x.den := by
          push_cast [Rat.cast_def]; rw [abs_div, abs_of_pos hden_r]
        rw [h1, hnum_abs]
        exact le_trans (div_le_div_of_nonneg_left (by positivity) one_pos hden_ge1)
          (by rw [div_one])
      -- |k|*ln2 ≤ |x - k*ln2| + |x| < 1 + natAbs
      have hk_ln2 : (k.natAbs : ℝ) * Real.log 2 < ↑x.num.natAbs + 1 := by
        have h1 : (k.natAbs : ℝ) * Real.log 2 = |↑k * Real.log 2| := by
          rw [abs_mul, abs_of_pos hlog2_pos, ← Int.cast_abs, Nat.cast_natAbs]
        rw [h1]
        calc |↑k * Real.log 2|
            = |↑x - (↑x - ↑k * Real.log 2)| := by rw [sub_sub_cancel]
          _ ≤ |↑x| + |↑x - ↑k * Real.log 2| := abs_sub _ _
          _ = |↑x - ↑k * Real.log 2| + |↑x| := add_comm _ _
          _ < 1 + ↑x.num.natAbs := add_lt_add_of_lt_of_le hk_bound hx_abs
          _ = ↑x.num.natAbs + 1 := by ring
      -- k.natAbs < 2*(natAbs + 1) since ln2 > 1/2
      have hk_bound_nat : k.natAbs ≤ 2 * x.num.natAbs + 1 := by
        by_contra h; push_neg at h
        have : (k.natAbs : ℝ) ≥ 2 * ↑x.num.natAbs + 2 := by exact_mod_cast h
        have : (k.natAbs : ℝ) * Real.log 2 ≥ (2 * ↑x.num.natAbs + 2) * (1 / 2) := by
          calc (k.natAbs : ℝ) * Real.log 2
              ≥ (2 * ↑x.num.natAbs + 2) * Real.log 2 := by nlinarith
            _ ≥ (2 * ↑x.num.natAbs + 2) * (1 / 2) :=
                mul_le_mul_of_nonneg_left hlog2_gt.le (by positivity)
        have : (k.natAbs : ℝ) * Real.log 2 ≥ ↑x.num.natAbs + 1 := by linarith
        linarith
      -- Step 2: 2*natAbs + 1 ≤ ab (three-way case split)
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
                ≤ x.num.natAbs * x.num.natAbs := Nat.mul_le_mul_left _ hdn
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
    have hfuel_eq : fuel = 100 * ab * (Nat.log2 ab + 1) + 1000 := by
      simp only [hfuel_def, expFuel]; rfl
    -- The numerator: L + 3|k| + prec + 20 ≤ 500*ab*(log₂(ab)+1) + 4*ab + 20
    -- iter = numerator / 10 ≤ 50*ab*(log₂(ab)+1) + (4*ab + 20)/10
    --      < 51*ab*(log₂(ab)+1) + 3 ≤ fuel
    have hnum : L + 3 * k.natAbs + FloatFormat.prec.toNat + 20 ≤
        500 * ab * (Nat.log2 ab + 1) + 4 * ab + 20 := by omega
    calc iter = (L + 3 * k.natAbs + FloatFormat.prec.toNat + 20) / 10 := rfl
      _ ≤ (500 * ab * (Nat.log2 ab + 1) + 4 * ab + 20) / 10 :=
          Nat.div_le_div_right hnum
      _ < fuel := by
          rw [hfuel_eq]
          apply Nat.div_lt_of_lt_mul
          -- 500*ab*X + 4*ab + 20 < 1000*ab*X + 10000
          set X := Nat.log2 ab + 1
          have hX : 1 ≤ X := by omega
          -- Need: 500*ab*X + 4*ab + 20 < 10 * (100*ab*X + 1000)
          -- i.e., 500*ab*X + 4*ab + 20 < 1000*ab*X + 10000
          -- i.e., 4*ab + 20 < 500*ab*X + 10000
          -- Since ab ≥ 0 and X ≥ 1:
          have h500 : 500 * ab * X = 500 * (ab * X) := by ring
          have habX : ab ≤ ab * X := Nat.le_mul_of_pos_right _ (by omega)
          have h1000 : 1000 * ab * X = 1000 * (ab * X) := by ring
          linarith [Nat.zero_le (ab * X)]
  -- Step 4: Show width * 2^s < δ at this iteration.
  -- width * 2^s ≤ 2^{|k|+s} * (err₁ + err₂) by expBounds_width_bound
  -- where err₁ ≤ 4 * 2^N / N! and err₂ = 8*(|k|+1)/2^{N_ln2}
  have hwidth : let (lower, upper) := expBounds x k iter
      ((upper : ℝ) - (lower : ℝ)) * 2 ^ (expShift lower) < δ := by
    have hbound := expBounds_width_bound x hx k iter hk_bound
    set lower := (expBounds x k iter).1
    set upper := (expBounds x k iter).2
    set N := expNumTerms + iter * 10 with hN_def
    set N_ln2 := Nat.log2 k.natAbs + 52 + iter * 50 with hN_ln2_def
    have hbound' : ((upper : ℝ) - (lower : ℝ)) * 2 ^ expShift lower ≤
        (2 : ℝ) ^ (k.natAbs + expShift lower) *
          ((2 : ℝ) ^ (N + 2) * (N + 2 : ℝ) /
            ((N + 1).factorial * (N + 1 : ℝ)) +
           8 * (k.natAbs + 1 : ℝ) / 2 ^ N_ln2) := by
      have := hbound
      rw [show expBounds x k iter = (lower, upper) from by ext <;> rfl] at this
      dsimp only at this; push_cast at this ⊢
      exact this
    have hS_iter : expShift lower ≤ S := hS iter
    -- 2^{|k|+s} ≤ 2^{|k|+S}
    set C := (2 : ℝ) ^ (k.natAbs + S) with hC_def
    have hC_pos : 0 < C := by positivity
    have h2s_le : (2 : ℝ) ^ (k.natAbs + expShift lower) ≤ C :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
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
    -- The full proof is broken into sorry-ed helper bounds to keep heartbeats low.
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
            ≤ C * ((8/3:ℝ) * (1/2:ℝ)^(N-4)) :=
              mul_le_mul_of_nonneg_left herr1 hC_pos.le
          _ ≤ C * ((8/3:ℝ) * (1/2:ℝ)^(L+k.natAbs+S+3)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hhalf (by norm_num)) hC_pos.le
          _ = (8/3:ℝ) * ((2:ℝ)^(k.natAbs+S) * (1/2:ℝ)^(k.natAbs+S+(L+3))) := by
              rw [show L+k.natAbs+S+3 = k.natAbs+S+(L+3) from by omega]; ring
          _ = (8/3:ℝ) * (1/2:ℝ)^(L+3) := by rw [two_pow_mul_half_pow]
          _ = 1 / (3 * (2:ℝ)^L) := by
              rw [one_div_pow, show L+3 = 3+L from by omega, pow_add]; norm_num; ring
      -- Term 2: C * err₂ ≤ 1/(2*2^L)
      have ht2 : C * (8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2) ≤ 1 / (2 * (2:ℝ)^L) := by
        -- 2^(L+2|k|+S+4) ≤ 2^N_ln2
        have h2Nln2 : (2:ℝ)^(L+2*k.natAbs+S+4) ≤ (2:ℝ)^N_ln2 :=
          pow_le_pow_right₀ (by norm_num) hN_ln2_ge
        calc C * (8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2)
            ≤ C * (8 * (↑k.natAbs + 1) / (2:ℝ)^(L+2*k.natAbs+S+4)) := by
              apply mul_le_mul_of_nonneg_left _ hC_pos.le
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2Nln2
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
    calc ((upper : ℝ) - (lower : ℝ)) * 2 ^ expShift lower
        ≤ (2:ℝ)^(k.natAbs + expShift lower) *
          ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)) +
          8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2) := hbound'
      _ ≤ C * ((2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)) +
          8 * (↑k.natAbs + 1) / (2:ℝ)^N_ln2) :=
          mul_le_mul_of_nonneg_right h2s_le (by positivity)
      _ < δ := h_total
  -- Step 5: At iter, the bracket is tight and the gap holds.
  have hsuccess : (expTryOne x k iter).isSome = true :=
    expTryOne_of_tight_bracket x hx k iter hk_bound δ
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
private theorem expTryOne_terminates (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    ∃ n, 0 ≤ n ∧ n < 0 + expFuel x ∧ (expTryOne x k n).isSome = true := by
  obtain ⟨iter, hiter_fuel, hsuccess⟩ := expFuel_sufficient x hx k hk_bound
  exact ⟨iter, by omega, by omega, hsuccess⟩

/-- **Meeting point of correctness and termination.**

For nonzero x, the loop output brackets exp(x) in a valid sticky cell with q ≥ 2^(prec+2).

This is where Thread 1 (bracket correctness) and Thread 2 (termination) meet:
- `expExtractLoop_sound` needs `0 < o.q` to conclude the result is correct.
- `expExtractLoop_pos_of_success` derives `0 < o.q` from `expTryOne_terminates`,
  which guarantees some iteration succeeds within `expFuel x` steps.
- `expExtractLoop_q_ge` then lifts `0 < o.q` to `2^(prec+2) ≤ o.q`. -/
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

/-! ## ExpRefExecSound instance

The final assembly. Each obligation routes through `expLoop_sound`:
- `exact_value`, `exact_mag_ne_zero`: the `x = 0` branch (trivial).
- `sticky_q_lower`, `sticky_interval`: the `x ≠ 0` branch, via `expLoop_sound`. -/

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

