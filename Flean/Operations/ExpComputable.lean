import Flean.Operations.Exp

/-! # Computable `ExpRefExec` Instance

Evaluates `exp(x)` using rational Taylor series with argument reduction:

1. Convert input to `ℚ` via `FiniteFp.toVal`
2. Reduce argument: `exp(x) = exp(x/2^n)^(2^n)` with `|x/2^n| ≤ 1/2`
3. Taylor series for `exp(y)` with `|y| ≤ 1/2` (fast convergence)
4. Recover via repeated squaring in `ℚ`
5. Extract sticky cell `(q, e_base)` for `roundIntSigM`

Soundness proofs (`ExpRefExecSound`) are deferred — the sorry'd instance lets
`fpExp` be evaluated on concrete inputs right away.
-/

section ExpComputable

variable [FloatFormat]

/-! ## Taylor series -/

/-- Number of Taylor terms. The `n`-dependent term count compensates for
error amplification from `n` repeated squarings: after squaring, relative
error grows by `~2^n`, so we add `n` extra terms. The `prec + 10` base
ensures the truncation error is negligible compared to sticky cell width. -/
private def expNumTerms (n : ℕ) : ℕ := FloatFormat.prec.toNat + 10 + n

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

/-! ## Argument reduction -/

/-- Smallest `n` such that `abs_x / 2^n ≤ 1/2`, i.e., `2 · abs_x ≤ 2^n`.
Returns 0 when `abs_x ≤ 1/2`. -/
private def expArgRedN (abs_x : ℚ) : ℕ :=
  let two_abs_x := 2 * abs_x
  if two_abs_x ≤ 1 then 0
  else
    -- ⌈2·|x|⌉ ≤ 2^n, so n = Nat.log2(⌈2·|x|⌉) + 1 suffices
    -- (Nat.log2 k gives the floor log, so 2^(log2 k + 1) > k)
    let upper := (⌈two_abs_x⌉).toNat  -- ⌈two_abs_x⌉ ≥ 1 here
    Nat.log2 upper + 1

/-! ## Repeated squaring -/

/-- Compute `base^(2^n)` by `n` successive squarings. -/
private def repeatedSquare (base : ℚ) : ℕ → ℚ
  | 0 => base
  | n + 1 => let half := repeatedSquare base n; half * half

/-! ## Taylor remainder -/

/-- Compute the Taylor remainder bound: `y^N * (N+1) / (N! * N)`.
This bounds `|exp(y) - ∑_{k<N} y^k/k!|` for `|y| ≤ 1`.
For our use: exp(y) ≤ taylorExpQ y (N-1) + taylorRemainder y N. -/
private def taylorRemainder (y : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 1  -- degenerate case
  else y ^ n * (n + 1) / (n.factorial * n)

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

/-- Computable exp reference kernel.

For `a.m = 0` (input is ±0): returns exact result for `exp(0) = 1`.
Otherwise: rational Taylor series with argument reduction. -/
def expComputableRun (a : FiniteFp) : ExpRefOut :=
  if a.m = 0 then
    -- exp(0) = 1 = 2 · 1 · 2^(-1)
    { q := 1, e_base := -1, isExact := true }
  else
    let x : ℚ := a.toVal
    let abs_x : ℚ := |x|
    -- Argument reduction: find n such that abs_x / 2^n ≤ 1/2
    let n := expArgRedN abs_x
    let y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
    -- Taylor bounds for exp(y): lower = T_N(y), upper = T_N(y) + R_{N+1}(y)
    let N := expNumTerms n
    let ty_lower := taylorExpQ y N
    let ty_remainder := taylorRemainder y (N + 1)
    let ty_upper := ty_lower + ty_remainder
    -- Repeated squaring: exp(|x|) ∈ [lower^(2^n), upper^(2^n)]
    let pos_lower := repeatedSquare ty_lower n
    let pos_upper := repeatedSquare ty_upper n
    -- Handle sign: exp(-|x|) = 1/exp(|x|)
    -- For x ≥ 0: exp(x) ∈ [pos_lower, pos_upper] (lower is Taylor, upper adds remainder)
    -- For x < 0: exp(x) = 1/exp(|x|) ∈ [1/pos_upper, 1/pos_lower]
    let lower : ℚ := if x < 0 then 1 / pos_upper else pos_lower
    let upper : ℚ := if x < 0 then 1 / pos_lower else pos_upper
    -- Extract sticky cell from bracketing bounds
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

omit [FloatFormat] in
/-- Repeated squaring of a positive value is positive. -/
private theorem repeatedSquare_pos (base : ℚ) (hb : 0 < base) (n : ℕ) :
    0 < repeatedSquare base n := by
  induction n with
  | zero => exact hb
  | succ n ih => exact mul_pos ih ih

/-- The lower bound passed to `expExtract` in the non-zero branch is positive. -/
private theorem expComputableRun_lower_pos (a : FiniteFp) (_hm : a.m ≠ 0) :
    let x : ℚ := a.toVal
    let abs_x : ℚ := |x|
    let n := expArgRedN abs_x
    let y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
    let N := expNumTerms n
    let ty_lower := taylorExpQ y N
    let ty_upper := ty_lower + taylorRemainder y (N + 1)
    let pos_lower := repeatedSquare ty_lower n
    let pos_upper := repeatedSquare ty_upper n
    let lower : ℚ := if x < 0 then 1 / pos_upper else pos_lower
    0 < lower := by
  simp only
  set nn := expArgRedN |a.toVal (R := ℚ)|
  have habs : 0 ≤ |a.toVal (R := ℚ)| := abs_nonneg _
  have hy_nonneg : 0 ≤ |a.toVal (R := ℚ)| / (2 : ℚ) ^ (nn : ℕ) :=
    div_nonneg habs (by positivity)
  set y := |a.toVal (R := ℚ)| / (2 : ℚ) ^ (nn : ℕ)
  have hty_ge : 1 ≤ taylorExpQ y (expNumTerms nn) :=
    taylorExpQ_ge_one _ hy_nonneg _
  have hty_pos : 0 < taylorExpQ y (expNumTerms nn) :=
    lt_of_lt_of_le (by norm_num) hty_ge
  -- Both ty_lower and ty_upper are positive (ty_upper = ty_lower + remainder ≥ ty_lower ≥ 1)
  have hrem_nonneg : 0 ≤ taylorRemainder y (expNumTerms nn + 1) := by
    unfold taylorRemainder
    simp only [show expNumTerms nn + 1 ≠ 0 from by unfold expNumTerms; omega, ↓reduceIte]
    apply div_nonneg
    · exact mul_nonneg (pow_nonneg hy_nonneg _) (by positivity)
    · positivity
  have hty_upper_pos : 0 < taylorExpQ y (expNumTerms nn) +
      taylorRemainder y (expNumTerms nn + 1) :=
    lt_of_lt_of_le hty_pos (le_add_of_nonneg_right hrem_nonneg)
  have hpl := repeatedSquare_pos _ hty_pos nn
  have hpu := repeatedSquare_pos _ hty_upper_pos nn
  split_ifs <;> positivity

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

omit [FloatFormat] in
/-- `repeatedSquare base n` equals `base ^ (2^n)`. -/
private theorem repeatedSquare_eq_pow (base : ℚ) (n : ℕ) :
    repeatedSquare base n = base ^ 2 ^ n := by
  induction n with
  | zero => simp [repeatedSquare]
  | succ n ih =>
    simp only [repeatedSquare, ih]
    rw [← pow_add]; congr 1
    rw [Nat.pow_succ]; omega

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
  -- Need: 2^prec2 * d ≤ p * 2^s
  -- Split on whether s_int ≥ 0
  by_cases hs : (0 : ℤ) ≤ s_int
  · -- s = prec2 + 1 + ld - lp (as ℕ, since s_int ≥ 0 means lp ≤ prec2 + 1 + ld)
    have hlp_le : lp ≤ prec2 + 1 + ld := by omega
    have hs_eq : s = prec2 + 1 + ld - lp := by
      omega
    -- p * 2^s ≥ 2^lp * 2^(prec2+1+ld-lp) = 2^(prec2+1+ld)
    have key : 2 ^ (prec2 + 1 + ld) ≤ p * 2 ^ s := by
      calc 2 ^ (prec2 + 1 + ld)
          = 2 ^ (lp + (prec2 + 1 + ld - lp)) := by congr 1; omega
        _ = 2 ^ lp * 2 ^ (prec2 + 1 + ld - lp) := by rw [Nat.pow_add]
        _ ≤ p * 2 ^ s := by rw [hs_eq]; exact Nat.mul_le_mul_right _ hlp
    -- 2^prec2 * d < 2^(prec2+1+ld) ≤ p * 2^s
    exact le_of_lt (calc 2 ^ prec2 * d
        < 2 ^ prec2 * 2 ^ (ld + 1) :=
          Nat.mul_lt_mul_of_pos_left hdlt (by positivity)
      _ = 2 ^ (prec2 + 1 + ld) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ p * 2 ^ s := key)
  · -- s = 0 (s_int < 0)
    push_neg at hs
    have hs_eq : s = 0 := Int.toNat_eq_zero.mpr (le_of_lt hs)
    -- lp ≥ prec2 + 2 + ld (from s_int < 0)
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
  -- q = p_lo * 2^s / d_lo ≥ 2^(prec+3) ≥ 2^(prec+2)
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
/-- The Taylor partial sum is STRICTLY less than exp for y > 0 and at least 2 terms.
This follows because all omitted terms y^k/k! for k > N are strictly positive. -/
private theorem taylorExpQ_lt_exp (y : ℚ) (hy : 0 < y) (n : ℕ) :
    (taylorExpQ y n : ℝ) < Real.exp (y : ℝ) := by
  have hy_real : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  -- The (n+1)-th term y^(n+1)/(n+1)! is positive
  have hterm : (0 : ℝ) < (y : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    div_pos (pow_pos hy_real _) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  -- Partial sum of (n+2) terms ≤ exp
  have hle2 := Real.sum_le_exp_of_nonneg (le_of_lt hy_real) (n + 2)
  -- sum(n+2 terms) = sum(n+1 terms) + term(n+1)
  rw [show n + 2 = n + 1 + 1 from by omega, Finset.sum_range_succ] at hle2
  -- taylorExpQ y n = partial sum of (n+1) terms
  rw [taylorExpQ_cast_eq_sum]
  linarith

/-! ## Strict monotonicity lemmas for composing bounds -/

omit [FloatFormat] in
/-- `result = taylorExpQ(y, N)^(2^n)` is strictly less than `exp(|x|)` when `|x| > 0`. -/
private theorem pos_result_lt_exp (y : ℚ) (hy_pos : 0 < y) (N n : ℕ) :
    (taylorExpQ y N : ℝ) ^ (2 ^ n) < Real.exp ((y : ℝ) * (2 ^ n : ℕ)) := by
  have hty_pos : (0 : ℝ) < (taylorExpQ y N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (taylorExpQ_ge_one y (le_of_lt hy_pos) N)
  have hty_lt := taylorExpQ_lt_exp y hy_pos N
  rw [show (y : ℝ) * (2 ^ n : ℕ) = (2 ^ n : ℕ) * (y : ℝ) from by ring,
    Real.exp_nat_mul]
  exact pow_lt_pow_left₀ hty_lt (le_of_lt hty_pos) (by positivity)

/-! ## Floor / cell extraction properties -/

/-! ## Floor ↔ real arithmetic bridge -/

omit [FloatFormat] in
/-- Nat floor division gives a lower bound in ℝ:
`(q : ℝ) * d ≤ (p : ℝ) * 2^s` where `q = p * 2^s / d`. -/
private theorem nat_floor_div_mul_le (p d s : ℕ) :
    ((p * 2 ^ s / d : ℕ) : ℝ) * (d : ℝ) ≤ (p : ℝ) * 2 ^ s := by
  have := Nat.div_mul_le_self (p * 2 ^ s) d
  exact_mod_cast this

omit [FloatFormat] in
/-- Nat floor division gives a strict upper bound in ℝ:
`(p : ℝ) * 2^s < ((q + 1) : ℝ) * d` where `q = p * 2^s / d`. -/
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
  -- Helper: r = p/d for positive rationals
  have cast_eq (r : ℚ) (hr : 0 < r) :
      (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
    have hnum : r.num = (r.num.natAbs : ℤ) :=
      (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hr))).symm
    have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      push_cast [Rat.cast_def]; ring
    rw [h1, show (r.num : ℝ) = (r.num.natAbs : ℝ) from by rw [hnum]; simp]
  have hu_pos : 0 < upper := lt_of_lt_of_le hl_pos (by exact_mod_cast le_of_lt (lt_of_lt_of_le hv_lower hv_upper))
  -- q/2^s ≤ lower (from Nat floor of lower)
  have hq_le_lower : (q : ℝ) / (2 : ℝ) ^ s ≤ (lower : ℝ) := by
    rw [div_le_iff₀ h2s_pos, cast_eq lower hl_pos, div_mul_eq_mul_div,
      le_div_iff₀ (Nat.cast_pos.mpr hd_lo)]
    exact_mod_cast nat_floor_div_mul_le p_lo d_lo s
  -- upper < (q+1)/2^s (from Nat floor of upper, using q_agree)
  have hupper_lt : (upper : ℝ) < ((q : ℝ) + 1) / (2 : ℝ) ^ s := by
    rw [lt_div_iff₀ h2s_pos, cast_eq upper hu_pos, div_mul_eq_mul_div,
      div_lt_iff₀ (Nat.cast_pos.mpr hd_hi)]
    -- Need: p_hi * 2^s < (q+1) * d_hi
    -- Since q = p_lo * 2^s / d_lo = p_hi * 2^s / d_hi (by hq_agree),
    -- we have p_hi * 2^s < (p_hi * 2^s / d_hi + 1) * d_hi = (q + 1) * d_hi
    have hq_eq : q = p_hi * 2 ^ s / d_hi := hq_agree
    rw [hq_eq]
    exact_mod_cast real_lt_nat_floor_div_succ_mul p_hi d_hi s hd_hi
  constructor
  · -- Lower: 2q · 2^(-(s+1)) < v
    rw [two_mul_zpow_neg_succ, show (q : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) =
      (q : ℝ) / (2 : ℝ) ^ s from by rw [zpow_neg, zpow_natCast]; ring]
    exact lt_of_le_of_lt hq_le_lower hv_lower
  · -- Upper: v < 2(q+1) · 2^(-(s+1))
    rw [two_mul_zpow_neg_succ, show ((q : ℝ) + 1) * (2 : ℝ) ^ (-(s : ℤ)) =
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
/-- Strict Taylor upper bound: `exp(y) < taylorExpQ y N + taylorRemainder y (N+1)` for `y > 0`.
This follows by applying the non-strict bound at `N+1` and showing the `N+1` bound is
strictly smaller than the `N` bound (because `(N+1)(N+3) < (N+2)²`). -/
private theorem exp_lt_taylor_upper (y : ℚ) (hy_pos : 0 < y) (hy1 : (y : ℝ) ≤ 1) (N : ℕ)
    (hN : 0 < N) :
    Real.exp (y : ℝ) < (taylorExpQ y N : ℝ) + (taylorRemainder y (N + 1) : ℝ) := by
  -- Apply the non-strict bound at N+1
  have hle := exp_le_taylor_upper y (le_of_lt hy_pos) hy1 (N + 1) (by omega)
  -- T_{N+1} = T_N + y^{N+1}/(N+1)!
  have hsucc : (taylorExpQ y (N + 1) : ℝ) = (taylorExpQ y N : ℝ) +
      (y : ℝ) ^ (N + 1) / ((N + 1).factorial : ℝ) := by
    rw [taylorExpQ_cast_eq_sum, taylorExpQ_cast_eq_sum,
      show N + 1 + 1 = (N + 1) + 1 from by omega, Finset.sum_range_succ]
  rw [hsucc] at hle
  -- Suffices: y^{N+1}/(N+1)! + R_{N+2} < R_{N+1}
  suffices h : (y : ℝ) ^ (N + 1) / ((N + 1).factorial : ℝ) +
      (taylorRemainder y (N + 2) : ℝ) < (taylorRemainder y (N + 1) : ℝ) by linarith
  -- Rewrite remainders using taylorRemainder_cast
  rw [taylorRemainder_cast y N hN, taylorRemainder_cast y (N + 1) (by omega)]
  -- Goal: y^(N+1)/(N+1)! + y^(N+2)*(N+3)/((N+2)!*(N+2)) < y^(N+1)*(N+2)/((N+1)!*(N+1))
  have hy_real : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  have hY : (0 : ℝ) < (y : ℝ) ^ (N + 1) := pow_pos hy_real _
  have hF : (0 : ℝ) < ((N + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hN2 : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
  -- y^(N+2) ≤ y^(N+1) since 0 < y ≤ 1
  have hpow_le : (y : ℝ) ^ (N + 2) ≤ (y : ℝ) ^ (N + 1) := by
    rw [pow_succ]; exact mul_le_of_le_one_right (le_of_lt hY) hy1
  -- (N+2)! = (N+2) * (N+1)!
  have hfact : ((N + 2).factorial : ℝ) = ((N + 2 : ℕ) : ℝ) * ((N + 1).factorial : ℝ) := by
    rw [show N + 2 = (N + 1) + 1 from by omega, Nat.factorial_succ]; push_cast; ring
  rw [hfact, show (N + 1 + 1 : ℕ) = N + 2 from by omega]
  -- Normalize ↑(N+k)+1 to ↑(N+k+1)
  have hc1 : ((N + 2 : ℕ) : ℝ) + 1 = ((N + 3 : ℕ) : ℝ) := by push_cast; ring
  have hc2 : ((N + 1 : ℕ) : ℝ) + 1 = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hc1, hc2]
  -- Goal: y^(N+1)/F + y^(N+2)*↑(N+3)/(↑(N+2)*F*↑(N+2)) < y^(N+1)*↑(N+2)/(F*↑(N+1))
  -- Key inequality: (N+1)(N+3) < (N+2)²
  have hkey : ((N + 1 : ℕ) : ℝ) * ((N + 3 : ℕ) : ℝ) < ((N + 2 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) := by
    have : (N + 1) * (N + 3) < (N + 2) * (N + 2) := by nlinarith
    exact_mod_cast this
  -- y^(N+2) ≤ y^(N+1) (since 0 < y ≤ 1), so y^(N+2)*↑(N+3) ≤ y^(N+1)*↑(N+3)
  have hpow_N3 : (y : ℝ) ^ (N + 2) * ((N + 3 : ℕ) : ℝ) ≤ (y : ℝ) ^ (N + 1) * ((N + 3 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hpow_le (by positivity)
  -- Bound y^(N+2) ≤ y^(N+1) and clear denominators
  -- After clearing: (N+1)*(N+3) < (N+2)² is the key arithmetic fact
  suffices h : (y : ℝ) ^ (N + 1) / ↑(N + 1).factorial +
      (y : ℝ) ^ (N + 1) * ↑(N + 3 : ℕ) / (↑(N + 2 : ℕ) * ↑(N + 1).factorial * ↑(N + 2 : ℕ)) <
      (y : ℝ) ^ (N + 1) * ↑(N + 2 : ℕ) / (↑(N + 1).factorial * ↑(N + 1 : ℕ)) by
    have h_step := div_le_div_of_nonneg_right hpow_N3
      (le_of_lt (mul_pos (mul_pos hN2 hF) hN2))
    linarith
  -- Now both sides have Y = y^(N+1) as a common factor. Factor it out.
  -- Divide by Y/F > 0 to get: 1 + ↑(N+3)/(↑(N+2)²) < ↑(N+2)/↑(N+1)
  -- Clear denominators: ↑(N+1)*↑(N+2)² + ↑(N+3)*↑(N+1) < ↑(N+2)³
  -- Simplify: ↑(N+1)*↑(N+3) < ↑(N+2)² (since ↑(N+1)*↑(N+2)² cancels from both sides)
  have hN3 : (0 : ℝ) < ((N + 3 : ℕ) : ℝ) := by positivity
  field_simp
  -- After field_simp: polynomial inequality
  nlinarith [hkey, hY, hF, hN1, hN2, hN3,
    mul_pos hY (by linarith : (0 : ℝ) < ↑(N + 2 : ℕ) * ↑(N + 2 : ℕ) - ↑(N + 1 : ℕ) * ↑(N + 3 : ℕ))]

/-! ## Repeated squaring monotonicity -/

omit [FloatFormat] in
/-- Repeated squaring is monotone for nonneg values. -/
private theorem repeatedSquare_mono {a b : ℚ} (hab : a ≤ b) (ha : 0 ≤ a) (n : ℕ) :
    repeatedSquare a n ≤ repeatedSquare b n := by
  induction n with
  | zero => exact hab
  | succ n ih =>
    simp only [repeatedSquare]
    have ha' : 0 ≤ repeatedSquare a n := le_of_le_of_eq (pow_nonneg ha _)
      (repeatedSquare_eq_pow a n).symm
    exact mul_le_mul ih ih ha' (le_trans ha' ih)

omit [FloatFormat] in
/-- Repeated squaring is strictly monotone for positive values. -/
private theorem repeatedSquare_strict_mono {a b : ℚ} (hab : a < b) (ha : 0 < a) (n : ℕ) :
    repeatedSquare a n < repeatedSquare b n := by
  induction n with
  | zero => exact hab
  | succ n ih =>
    simp only [repeatedSquare]
    have ha' : 0 < repeatedSquare a n := repeatedSquare_pos a ha n
    have hb' : 0 < repeatedSquare b n := repeatedSquare_pos b (lt_trans ha hab) n
    exact mul_lt_mul ih (le_of_lt ih) ha' (le_of_lt hb')

/-! ## Two-sided bracket through squaring -/

-- Note: lower bound `repeatedSquare(taylorExpQ y N, n) < exp(y · 2^n)` for y > 0
-- is already proved as `pos_result_lt_exp`.

omit [FloatFormat] in
/-- Upper bound: `exp(y · 2^n) ≤ repeatedSquare(taylorExpQ y N + taylorRemainder y (N+1), n)`
for `0 ≤ y ≤ 1`. -/
private theorem exp_le_pos_upper (y : ℚ) (hy0 : 0 ≤ y) (hy1 : (y : ℝ) ≤ 1)
    (N n : ℕ) (hN : 0 < N) :
    Real.exp ((y : ℝ) * (2 ^ n : ℕ)) ≤
      (repeatedSquare (taylorExpQ y N + taylorRemainder y (N + 1)) n : ℝ) := by
  rw [show (y : ℝ) * (2 ^ n : ℕ) = (2 ^ n : ℕ) * (y : ℝ) from by ring, Real.exp_nat_mul]
  have hle := exp_le_taylor_upper y hy0 hy1 N hN
  have hty_pos : (0 : ℝ) < (taylorExpQ y N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (taylorExpQ_ge_one y hy0 N)
  have hexp_pos : 0 < Real.exp (y : ℝ) := Real.exp_pos _
  rw [repeatedSquare_eq_pow]; push_cast
  exact pow_le_pow_left₀ (le_of_lt hexp_pos) hle _

omit [FloatFormat] in
/-- Strict upper bound: `exp(y · 2^n) < repeatedSquare(taylorExpQ y N + taylorRemainder y (N+1), n)`
for `0 < y ≤ 1`. -/
private theorem exp_lt_pos_upper (y : ℚ) (hy_pos : 0 < y) (hy1 : (y : ℝ) ≤ 1)
    (N n : ℕ) (hN : 0 < N) :
    Real.exp ((y : ℝ) * (2 ^ n : ℕ)) <
      (repeatedSquare (taylorExpQ y N + taylorRemainder y (N + 1)) n : ℝ) := by
  rw [show (y : ℝ) * (2 ^ n : ℕ) = (2 ^ n : ℕ) * (y : ℝ) from by ring, Real.exp_nat_mul]
  have hlt := exp_lt_taylor_upper y hy_pos hy1 N hN
  have hexp_pos : 0 < Real.exp (y : ℝ) := Real.exp_pos _
  rw [repeatedSquare_eq_pow]; push_cast
  exact pow_lt_pow_left₀ hlt (le_of_lt hexp_pos) (by positivity)

/-! ## Cell agreement -/

-- Cell agreement (⌊lower·2^s⌋ = ⌊upper·2^s⌋) requires that the bracket
-- [lower, upper] doesn't straddle a cell boundary. With n-dependent term count
-- (expNumTerms n = prec + 10 + n), the bracket width is < 1 cell (provable:
-- bracket/cell ≈ 2^(-7) / (prec+11+n)!). However, even a narrow bracket can
-- straddle a boundary if exp(x) is very close to k·2^(-s) for some integer k.
-- Proving this never happens requires Hermite-Lindemann (exp of nonzero rational
-- is irrational), which is not formalized in mathlib.

/-! ## Argument reduction bound -/

omit [FloatFormat] in
/-- After argument reduction, `y = abs_x / 2^n ≤ 1/2`. -/
private theorem expArgRedN_bound (abs_x : ℚ) :
    abs_x / (2 : ℚ) ^ (expArgRedN abs_x : ℕ) ≤ 1 / 2 := by
  -- Equivalent to: 2 * abs_x ≤ 2^n
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (expArgRedN abs_x : ℕ))]
  simp only [expArgRedN]
  split_ifs with h
  · -- 2 * abs_x ≤ 1 = 2^0
    simp [pow_zero]; linarith
  · -- n = Nat.log2(⌈2·abs_x⌉) + 1
    push_neg at h
    set upper := (⌈2 * abs_x⌉).toNat
    set nn := Nat.log2 upper + 1
    have h2ax_pos : 0 < 2 * abs_x := by linarith
    have hceil_pos : 0 < ⌈2 * abs_x⌉ := Int.ceil_pos.mpr h2ax_pos
    have hupper_pos : 0 < upper := by
      simp only [upper]; omega
    -- 2·abs_x ≤ ⌈2·abs_x⌉ = upper (as ℚ)
    have hle_ceil : 2 * abs_x ≤ (upper : ℚ) := by
      have h1 : 2 * abs_x ≤ (⌈2 * abs_x⌉ : ℚ) := by exact_mod_cast Int.le_ceil _
      have h2 : (⌈2 * abs_x⌉ : ℚ) = (upper : ℚ) := by
        simp only [upper]
        exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hceil_pos)).symm
      linarith
    -- upper < 2^nn (from Nat.log2)
    have hpow_gt : upper < 2 ^ nn :=
      (Nat.log2_lt (by omega)).mp (by omega)
    -- 1/2 * 2^nn = 2^nn / 2, and 2*abs_x ≤ upper < 2^nn
    have hpow_gt_q : (upper : ℚ) < (2 ^ nn : ℚ) := by exact_mod_cast hpow_gt
    have : 2 * abs_x < (2 ^ nn : ℚ) := lt_of_le_of_lt hle_ceil hpow_gt_q
    linarith

omit [FloatFormat] in
/-- `y · 2^n = abs_x` after argument reduction. -/
private theorem expArgRedN_recover (abs_x : ℚ) :
    abs_x / (2 : ℚ) ^ (expArgRedN abs_x : ℕ) * (2 : ℚ) ^ (expArgRedN abs_x : ℕ) = abs_x := by
  rw [div_mul_cancel₀]
  exact pow_ne_zero _ (by norm_num)

/-! ## Sticky interval proof -/

private theorem expComputableRun_sticky_interval (a : FiniteFp) (hm : a.m ≠ 0) :
    let o := expComputableRun a
    inStickyInterval (R := ℝ) o.q o.e_base (Real.exp (a.toVal : ℝ)) := by
  -- Align coercion: (a.toVal : ℝ) = ((a.toVal : ℚ) : ℝ)
  have hval_eq : (a.toVal (R := ℝ)) = ((a.toVal (R := ℚ) : ℚ) : ℝ) := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rcases Bool.eq_false_or_eq_true a.s with hs | hs <;> simp [hs, FloatFormat.radix_val_eq_two]
  -- Unfold to get at the components
  simp only [expComputableRun, hm, ↓reduceIte]
  rw [hval_eq]
  set x : ℚ := a.toVal
  set abs_x : ℚ := |x|
  set n := expArgRedN abs_x
  set y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
  set N := expNumTerms n
  set ty_lower := taylorExpQ y N
  set ty_upper := ty_lower + taylorRemainder y (N + 1)
  set pos_lower := repeatedSquare ty_lower n
  set pos_upper := repeatedSquare ty_upper n
  -- Key facts
  have habs_nonneg : 0 ≤ abs_x := abs_nonneg _
  have hy_nonneg : 0 ≤ y := div_nonneg habs_nonneg (by positivity)
  have hy_le_half : y ≤ 1 / 2 := expArgRedN_bound abs_x
  have hy_le_one : (y : ℝ) ≤ 1 := by exact_mod_cast le_trans hy_le_half (by norm_num)
  have hN_pos : 0 < N := by simp only [N, expNumTerms]; omega
  have hx_ne : (x : ℚ) ≠ 0 :=
    FiniteFp.toVal_ne_zero_of_m_pos a (Nat.pos_of_ne_zero hm)
  -- ty_lower ≥ 1 (Taylor of nonneg is ≥ 1)
  have hty_ge : 1 ≤ ty_lower := taylorExpQ_ge_one _ hy_nonneg _
  have hty_pos : 0 < ty_lower := lt_of_lt_of_le (by norm_num) hty_ge
  -- remainder ≥ 0
  have hrem_nonneg : 0 ≤ taylorRemainder y (N + 1) := by
    unfold taylorRemainder
    simp only [show N + 1 ≠ 0 from by omega, ↓reduceIte]
    exact div_nonneg (mul_nonneg (pow_nonneg hy_nonneg _) (by positivity)) (by positivity)
  -- ty_upper ≥ ty_lower
  have hty_upper_ge : ty_lower ≤ ty_upper := le_add_of_nonneg_right hrem_nonneg
  have hty_upper_pos : 0 < ty_upper := lt_of_lt_of_le hty_pos hty_upper_ge
  -- pos bounds are positive
  have hpl_pos : 0 < pos_lower := repeatedSquare_pos _ hty_pos _
  have hpu_pos : 0 < pos_upper := repeatedSquare_pos _ hty_upper_pos _
  -- y · 2^n = abs_x (in ℝ)
  have hy_recover : (y : ℝ) * (2 ^ n : ℕ) = (abs_x : ℝ) := by
    have h : y * (2 : ℚ) ^ (n : ℕ) = abs_x := expArgRedN_recover abs_x
    have : (y : ℝ) * (2 : ℝ) ^ (n : ℕ) = (abs_x : ℝ) := by exact_mod_cast h
    convert this using 1; push_cast; ring
  -- Taylor bracket: ty_lower < exp(y) ≤ ty_upper (for y > 0)
  -- Squaring bracket: pos_lower < exp(abs_x) ≤ pos_upper
  -- exp(y · 2^n) = exp(abs_x)
  by_cases hx : 0 ≤ x
  · -- Positive case: lower = pos_lower, upper = pos_upper
    simp only [show ¬(x < 0) from not_lt.mpr hx, ↓reduceIte]
    -- x > 0 (since x ≥ 0 and x ≠ 0)
    have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx_ne)
    have hy_pos : 0 < y := by
      apply div_pos _ (by positivity)
      rw [show abs_x = x from abs_of_nonneg (le_of_lt hx_pos)]
      exact hx_pos
    -- Cast identity: (repeatedSquare b n : ℝ) = (b : ℝ) ^ 2^n
    have cast_rs (b : ℚ) : (repeatedSquare b n : ℝ) = (b : ℝ) ^ 2 ^ n := by
      rw [repeatedSquare_eq_pow]; push_cast; rfl
    have habs_eq : (abs_x : ℝ) = (x : ℝ) := by
      exact_mod_cast abs_of_nonneg (le_of_lt hx_pos)
    -- pos_lower < exp(x) (strict Taylor underestimate through squaring)
    have hlt : (pos_lower : ℝ) < Real.exp (x : ℝ) := by
      rw [cast_rs]
      have := pos_result_lt_exp y hy_pos N n
      rwa [hy_recover, habs_eq] at this
    -- exp(x) ≤ pos_upper (Taylor + remainder upper bound through squaring)
    have hle : Real.exp (x : ℝ) ≤ (pos_upper : ℝ) := by
      have h := exp_le_pos_upper y hy_nonneg hy_le_one N n hN_pos
      rw [hy_recover, habs_eq] at h
      exact h
    -- Cell agreement
    have hcell : pos_lower.num.natAbs * 2 ^ expShift pos_lower / pos_lower.den =
        pos_upper.num.natAbs * 2 ^ expShift pos_lower / pos_upper.den := by
      sorry -- Cell agreement: bracket < 1 cell (n-dependent terms), but no-straddling
             -- requires Hermite-Lindemann. See "Cell agreement" section comment.
    exact inStickyInterval_of_bracket pos_lower pos_upper hpl_pos _ _ hlt hle hcell
  · -- Negative case: lower = 1/pos_upper, upper = 1/pos_lower
    push_neg at hx
    simp only [show x < 0 from hx, ↓reduceIte]
    -- |x| > 0, y > 0
    have habs_pos : 0 < abs_x := by
      rw [show abs_x = |x| from rfl]; exact abs_pos.mpr hx_ne
    have hy_pos : 0 < y := div_pos habs_pos (by positivity)
    -- Cast identity: (repeatedSquare b n : ℝ) = (b : ℝ) ^ 2^n
    have cast_rs (b : ℚ) : (repeatedSquare b n : ℝ) = (b : ℝ) ^ 2 ^ n := by
      rw [repeatedSquare_eq_pow]; push_cast; rfl
    -- exp(|x|) is bracketed: pos_lower < exp(|x|) ≤ pos_upper
    have hlt_abs : (pos_lower : ℝ) < Real.exp (abs_x : ℝ) := by
      rw [cast_rs]
      have := pos_result_lt_exp y hy_pos N n
      rwa [hy_recover] at this
    have hle_abs : Real.exp (abs_x : ℝ) ≤ (pos_upper : ℝ) := by
      have h := exp_le_pos_upper y hy_nonneg hy_le_one N n hN_pos
      rw [hy_recover] at h
      exact h
    -- exp(x) = 1/exp(|x|) since exp(x) = exp(-|x|) = 1/exp(|x|)
    have hexp_eq : Real.exp (x : ℝ) = 1 / Real.exp (abs_x : ℝ) := by
      rw [show (abs_x : ℝ) = |(x : ℝ)| from by exact_mod_cast rfl,
        abs_of_neg (by exact_mod_cast hx), one_div,
        ← Real.exp_neg, neg_neg]
    -- Reciprocal bounds: pos_lower < exp(|x|) ≤ pos_upper gives
    -- 1/pos_upper ≤ exp(x) = 1/exp(|x|) < 1/pos_lower
    -- For inStickyInterval_of_bracket we need lower < v ≤ upper.
    -- Here: lower = 1/pos_upper, upper = 1/pos_lower.
    -- We have exp(x) < 1/pos_lower (strict, from pos_lower < exp(|x|)).
    -- We need 1/pos_upper < exp(x), but we only have ≤.
    -- The strict version requires exp(|x|) < pos_upper (strict Taylor upper bound).
    -- For now, sorry the strict lower bound.
    -- Strict upper: exp(|x|) < pos_upper (using strict Taylor bound)
    have hlt_abs_strict : Real.exp (abs_x : ℝ) < (pos_upper : ℝ) := by
      have h := exp_lt_pos_upper y hy_pos hy_le_one N n hN_pos
      rw [hy_recover] at h
      exact h
    have hlt : ((1 : ℚ) / pos_upper : ℝ) < Real.exp (x : ℝ) := by
      rw [hexp_eq]; push_cast
      have hexp_abs_pos := Real.exp_pos (abs_x : ℝ)
      have hpu_pos_r : (0 : ℝ) < (pos_upper : ℝ) := by exact_mod_cast hpu_pos
      rw [div_lt_div_iff₀ hpu_pos_r hexp_abs_pos]
      linarith [hlt_abs_strict]
    have hle : Real.exp (x : ℝ) ≤ ((1 : ℚ) / pos_lower : ℝ) := by
      rw [hexp_eq]; push_cast
      have hexp_abs_pos := Real.exp_pos (abs_x : ℝ)
      have hpl_pos_r : (0 : ℝ) < (pos_lower : ℝ) := by exact_mod_cast hpl_pos
      rw [div_le_div_iff₀ hexp_abs_pos hpl_pos_r]
      linarith [hlt_abs]
    -- Cell agreement
    have hcell : (1 / pos_upper).num.natAbs * 2 ^ expShift (1 / pos_upper) /
        (1 / pos_upper).den =
        (1 / pos_lower).num.natAbs * 2 ^ expShift (1 / pos_upper) /
        (1 / pos_lower).den := by
      sorry -- Cell agreement: bracket < 1 cell (n-dependent terms), but no-straddling
             -- requires Hermite-Lindemann. See "Cell agreement" section comment.
    have h1pu_pos : 0 < (1 : ℚ) / pos_upper := div_pos one_pos hpu_pos
    -- Normalize casts: (↑(1/q) : ℝ) vs (↑1/↑q : ℝ)
    have hlt' : ((1 / pos_upper : ℚ) : ℝ) < Real.exp (x : ℝ) := by push_cast at hlt ⊢; exact hlt
    have hle' : Real.exp (x : ℝ) ≤ ((1 / pos_lower : ℚ) : ℝ) := by push_cast at hle ⊢; exact hle
    exact inStickyInterval_of_bracket (1 / pos_upper) (1 / pos_lower) h1pu_pos _ _ hlt' hle' hcell

/-! ## Soundness -/

instance (priority := 500) : ExpRefExecSound where
  exact_mag_ne_zero := by
    intro a o hr hExact
    have hrun : ExpRefExec.run a = expComputableRun a := rfl
    rw [hrun] at hr
    have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
    rw [expComputableRun_zero a hm] at hr
    subst hr
    norm_num
  exact_value := by
    intro a o hr hExact
    have hrun : ExpRefExec.run a = expComputableRun a := rfl
    rw [hrun] at hr
    have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
    rw [expComputableRun_zero a hm] at hr
    subst hr
    simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
    have hval : (a.toVal : ℝ) = 0 :=
      FiniteFp.toVal_isZero (show a.isZero from hm)
    rw [hval, Real.exp_zero]
    norm_num
  sticky_q_lower := by
    intro a o hr hFalse
    have hrun : ExpRefExec.run a = expComputableRun a := rfl
    rw [hrun] at hr
    -- isExact = false means we're in the non-zero branch
    have hm : a.m ≠ 0 := by
      intro h
      rw [expComputableRun_zero a h] at hr
      rw [← hr] at hFalse; exact absurd hFalse (by decide)
    -- The output comes from expExtract (lower, upper)
    -- expExtract_q_ge gives q ≥ 2^(prec+2) from lower > 0
    have hnonzero : expComputableRun a = expExtract
        (if a.toVal (R := ℚ) < 0
         then 1 / repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ))
           (expNumTerms (expArgRedN |a.toVal (R := ℚ)|)) +
           taylorRemainder (|a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ))
           (expNumTerms (expArgRedN |a.toVal (R := ℚ)|) + 1)) (expArgRedN |a.toVal (R := ℚ)|)
         else repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ))
           (expNumTerms (expArgRedN |a.toVal (R := ℚ)|)))
           (expArgRedN |a.toVal (R := ℚ)|))
        (if a.toVal (R := ℚ) < 0
         then 1 / repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ))
           (expNumTerms (expArgRedN |a.toVal (R := ℚ)|)))
           (expArgRedN |a.toVal (R := ℚ)|)
         else repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ))
           (expNumTerms (expArgRedN |a.toVal (R := ℚ)|)) +
           taylorRemainder (|a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ))
           (expNumTerms (expArgRedN |a.toVal (R := ℚ)|) + 1)) (expArgRedN |a.toVal (R := ℚ)|)) := by
      simp only [expComputableRun, hm, ↓reduceIte]
    rw [hnonzero] at hr; rw [← hr]
    exact expExtract_q_ge _ _ (expComputableRun_lower_pos a hm)
  sticky_interval := by
    intro a o hr hFalse
    have hrun : ExpRefExec.run a = expComputableRun a := rfl
    rw [hrun] at hr
    have hm : a.m ≠ 0 := by
      intro h; rw [expComputableRun_zero a h] at hr
      rw [← hr] at hFalse; exact absurd hFalse (by decide)
    rw [← hr]
    exact expComputableRun_sticky_interval a hm

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
