import Flean.Operations.Exp

/-! # Computable `ExpRefExec` Instance

Evaluates `exp(x)` using rational Taylor series with standard argument reduction:

1. Convert input to `ℚ` via `FiniteFp.toVal`
2. Reduce argument mod ln(2): `exp(x) = 2^k · exp(r)` with `|r| ≤ ln(2)/2`
3. Taylor series for `exp(r)` with `|r| ≤ ln(2)/2 < 1` (fast convergence)
4. Reconstruct via exponent shift (exact — no error amplification)
5. Extract sticky cell `(q, e_base)` for `roundIntSigM`

The `ExpRefExec` instance lets `fpExp` be evaluated on concrete inputs.
Three of four `ExpRefExecSound` obligations are proved sorry-free below;
the fourth (`sticky_interval`) requires Hermite-Lindemann — see
`.claude/notes/lindemann-weierstrass-plan.md`.
-/

section ExpComputable

variable [FloatFormat]

/-! ## Constants -/

/-- Rational lower bound for `Real.log 2`. From mathlib: `0.6931471803 < Real.log 2`. -/
private def ln2_lo : ℚ := 6931471803 / 10000000000

/-- Rational upper bound for `Real.log 2`. From mathlib: `Real.log 2 < 0.6931471808`. -/
private def ln2_hi : ℚ := 6931471808 / 10000000000

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

/-- Compute `k = round(x / ln(2))` using a rational approximation.
The result satisfies `|x - k·ln(2)| ≤ ln(2)/2` (approximately). -/
private def expArgRedK (x : ℚ) : ℤ :=
  round (x / ln2_hi)

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

/-! ## Main kernel -/

/-- Computable exp reference kernel (standard mod-ln(2) method).

For `a.m = 0` (input is ±0): returns exact result for `exp(0) = 1`.
Otherwise:
1. Reduce `x = k·ln(2) + r` with `k = round(x/ln(2))`
2. Bracket `r` in `[r_lo, r_hi]` using rational bounds for `ln(2)`
3. Use directional Taylor bounds for `exp(r)`:
   - `exp(r) ≥ exp(r_lo)` and `exp(r) ≤ exp(r_hi)` (monotonicity)
   - For `y ≥ 0`: lower bound = `T_N(y)`, upper bound = `T_N(y) + R_{N+1}(y)`
   - For `y < 0`: use `exp(y) = 1/exp(-y)` and bound `exp(-y)` instead
4. Multiply by `2^k` and extract sticky cell -/
def expComputableRun (a : FiniteFp) : ExpRefOut :=
  if a.m = 0 then
    -- exp(0) = 1 = 2 · 1 · 2^(-1)
    { q := 1, e_base := -1, isExact := true }
  else
    let x : ℚ := a.toVal
    -- Argument reduction: x = k·ln(2) + r
    let k := expArgRedK x
    let (r_lo, r_hi) := expRInterval x k
    let N := expNumTerms
    -- Lower bound: exp(r) ≥ exp(r_lo)
    let lower_r :=
      if 0 ≤ r_lo then
        -- r_lo ≥ 0: Taylor partial sum is a lower bound
        taylorExpQ r_lo N
      else
        -- r_lo < 0: exp(r_lo) = 1/exp(-r_lo) ≥ 1/(T_N(-r_lo) + R_{N+1}(-r_lo))
        1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))
    -- Upper bound: exp(r) ≤ exp(r_hi)
    let upper_r :=
      if 0 ≤ r_hi then
        -- r_hi ≥ 0: Taylor + remainder is an upper bound
        taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)
      else
        -- r_hi < 0: exp(r_hi) = 1/exp(-r_hi) ≤ 1/T_N(-r_hi)
        1 / taylorExpQ (-r_hi) N
    -- Reconstruct: exp(x) = 2^k · exp(r), so bounds for exp(x) are bounds * 2^k
    -- Multiplication by 2^k is exact in ℚ
    let lower := lower_r * (2 : ℚ) ^ k
    let upper := upper_r * (2 : ℚ) ^ k
    -- Extract sticky cell from full exp(x) bounds
    expExtract lower upper

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

/-- When `isExact = true`, we must be in the zero branch. -/
private theorem expComputableRun_exact_is_zero (a : FiniteFp)
    (hExact : (expComputableRun a).isExact = true) : a.m = 0 := by
  by_contra h
  have : (expComputableRun a).isExact = false := by
    simp only [expComputableRun, h, ↓reduceIte, expExtract_isExact_false]
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

/-! ## Soundness -/

-- The full `ExpRefExecSound` instance requires cell agreement
-- (⌊lower·2^s⌋ = ⌊upper·2^s⌋), which depends on Hermite-Lindemann.
-- See `.claude/notes/lindemann-weierstrass-plan.md` for the proof plan.
-- The sorry-free obligations (exact_mag_ne_zero, exact_value, sticky_q_lower)
-- are proved below as standalone theorems; sticky_interval is deferred.

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

private theorem expComputableRun_sticky_q_lower (a : FiniteFp) (o : ExpRefOut)
    (hr : expComputableRun a = o) (hFalse : o.isExact = false) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q := by
  have hm : a.m ≠ 0 := by
    intro h
    rw [expComputableRun_zero a h] at hr
    rw [← hr] at hFalse; exact absurd hFalse (by decide)
  -- The non-zero branch produces expExtract (lower_r * 2^k) (upper_r * 2^k)
  have hval : expComputableRun a =
      let x : ℚ := a.toVal
      let k := expArgRedK x
      let (r_lo, r_hi) := expRInterval x k
      let N := expNumTerms
      let lower_r := if 0 ≤ r_lo then taylorExpQ r_lo N
        else 1 / (taylorExpQ (-r_lo) N + taylorRemainder (-r_lo) (N + 1))
      let upper_r := if 0 ≤ r_hi then taylorExpQ r_hi N + taylorRemainder r_hi (N + 1)
        else 1 / taylorExpQ (-r_hi) N
      expExtract (lower_r * (2 : ℚ) ^ k) (upper_r * (2 : ℚ) ^ k) := by
    simp only [expComputableRun, hm, ↓reduceIte]
  rw [hval] at hr; rw [← hr]
  exact expExtract_q_ge _ _ (expComputableRun_lower_pos a hm)

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

