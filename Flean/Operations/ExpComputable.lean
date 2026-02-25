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

/-- Number of Taylor terms. `prec + 10` guard terms ensures the truncation
error is negligible compared to sticky cell width for `|y| ≤ 1/2`. -/
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

/-! ## Sticky cell extraction -/

/-- Extract `(q, e_base)` from a positive rational `result`.

Finds shift `s` such that `q := ⌊result · 2^s⌋` has at least `prec + 2` bits
(guaranteed by `initial_q_ge_minQ`),
then sets `e_base := -(s + 1)` so that `result ≈ 2q · 2^e_base`.

When `isUpper = true` (negative input: result > exp(x)), and `result · 2^s` is
an exact integer, we subtract 1 from `q` so that `exp(x)` falls strictly inside
the interval `(q/2^s, (q+1)/2^s)` rather than at the upper boundary.
The extra `targetBits` margin ensures `q - 1 ≥ 2^(prec+2)`. -/
private def expExtract (result : ℚ) (isUpper : Bool) : ExpRefOut :=
  let p := result.num.natAbs
  let d := result.den
  let targetBits := FloatFormat.prec.toNat + 4  -- extra bit for negative adjustment
  -- Approximate shift: s ≈ targetBits + log2(d) - log2(p)
  -- Use Int to avoid Nat subtraction underflow
  let s_int : ℤ := (targetBits : ℤ) + (Nat.log2 d : ℤ) - (Nat.log2 p : ℤ)
  let s := s_int.toNat  -- clamp negative to 0
  -- Compute q = ⌊p · 2^s / d⌋ (≥ 2^(prec+3) by initial_q_ge_minQ)
  let q := p * 2 ^ s / d
  -- For upper bounds (negative case), if ⌊result·2^s⌋ = result·2^s exactly,
  -- shift q down by 1 to keep exp(x) strictly inside the cell.
  let q := if isUpper && (p * 2 ^ s % d == 0) then q - 1 else q
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
    -- Taylor approximation of exp(y) for y ∈ (0, 1/2]
    let ty := taylorExpQ y expNumTerms
    -- Repeated squaring: exp(|x|) ≈ ty^(2^n)
    let pos_result := repeatedSquare ty n
    -- Handle sign: exp(-|x|) = 1/exp(|x|)
    let result : ℚ := if x < 0 then 1 / pos_result else pos_result
    -- Extract sticky cell
    expExtract result (x < 0)

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

/-- The result passed to `expExtract` in the non-zero branch is positive. -/
private theorem expComputableRun_result_pos (a : FiniteFp) (_hm : a.m ≠ 0) :
    let x : ℚ := a.toVal
    let abs_x : ℚ := |x|
    let n := expArgRedN abs_x
    let y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
    let ty := taylorExpQ y expNumTerms
    let pos_result := repeatedSquare ty n
    let result : ℚ := if x < 0 then 1 / pos_result else pos_result
    0 < result := by
  simp only
  have habs : 0 ≤ |a.toVal (R := ℚ)| := abs_nonneg _
  have hy_nonneg : 0 ≤ |a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ) :=
    div_nonneg habs (by positivity)
  have hty_ge : 1 ≤ taylorExpQ (|a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms :=
    taylorExpQ_ge_one _ hy_nonneg _
  have hty_pos : 0 < taylorExpQ (|a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms :=
    lt_of_lt_of_le (by norm_num) hty_ge
  have hpos := repeatedSquare_pos _ hty_pos (expArgRedN |a.toVal (R := ℚ)|)
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
private theorem expExtract_isExact_false (result : ℚ) (isUpper : Bool) :
    (expExtract result isUpper).isExact = false := by
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

/-- The raw q (before isUpper adjustment) in expExtract. -/
private theorem expExtract_raw_q_ge (result : ℚ) (hpos : 0 < result) :
    let p := result.num.natAbs
    let d := result.den
    let s_int : ℤ := ((FloatFormat.prec.toNat + 4 : ℕ) : ℤ) +
      ((Nat.log2 d : ℕ) : ℤ) - ((Nat.log2 p : ℕ) : ℤ)
    2 ^ (FloatFormat.prec.toNat + 3) ≤ p * 2 ^ s_int.toNat / d := by
  have hp : 0 < result.num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hpos))
  exact initial_q_ge_minQ result.num.natAbs result.den hp result.den_pos

omit [FloatFormat] in
/-- Helper: if `q ≥ 2^(n+1)` then `q - 1 ≥ 2^n` and `q ≥ 2^n`. -/
private theorem q_adjust_ge (q n : ℕ) (hq : 2 ^ (n + 1) ≤ q) (b : Bool) :
    2 ^ n ≤ (if b then q - 1 else q) := by
  have h1 : 2 ^ n + 1 ≤ 2 ^ (n + 1) := by
    have := Nat.one_le_pow n 2 (by omega)
    rw [pow_succ]; omega
  split_ifs <;> omega

/-- `expExtract` produces `q ≥ 2^(prec+2)` for positive rational input. -/
private theorem expExtract_q_ge (result : ℚ) (hpos : 0 < result) (isUpper : Bool) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ (expExtract result isUpper).q := by
  have hraw := expExtract_raw_q_ge result hpos
  simp only at hraw  -- beta-reduce let bindings
  -- expExtract.q is: if isUpper && exact then raw_q - 1 else raw_q
  -- where raw_q = p * 2^s / d ≥ 2^(prec+3)
  show 2 ^ (FloatFormat.prec.toNat + 2) ≤ (expExtract result isUpper).q
  simp only [expExtract]
  exact q_adjust_ge _ _ hraw _

/-- When `isExact = true`, we must be in the zero branch. -/
private theorem expComputableRun_exact_is_zero (a : FiniteFp)
    (hExact : (expComputableRun a).isExact = true) : a.m = 0 := by
  by_contra h
  have : (expComputableRun a).isExact = false := by
    simp only [expComputableRun, h, ↓reduceIte, expExtract_isExact_false _ _]
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

/-! ## Sticky interval proof -/

/-- The Taylor error after repeated squaring is less than one cell width.
This is the core analytical bound: for our Taylor approximation `result` of `exp(x)`,
`|exp(x) - (result : ℝ)| < (result : ℝ) / 2^(prec+3)`.

The proof uses:
- `Real.exp_bound'`: Taylor error for `0 ≤ y ≤ 1` is at most `y^N·(N+1)/(N!·N)`
- With `y ≤ 1/2` and `N = prec+11`, this is `≤ (1/2)^(prec+11)·(prec+12)/((prec+11)!·(prec+11))`
- After `2^n` squarings, error amplification is bounded by `2^n·exp(|x|)^(2^n-1)·ε`
- The `prec+10` guard terms ensure this stays below `1/2^(prec+3)` relative error -/
private theorem taylor_approx_error (a : FiniteFp) (hm : a.m ≠ 0)
    (hx_nonneg : 0 ≤ a.toVal (R := ℚ)) :
    let x : ℚ := a.toVal
    let abs_x : ℚ := |x|
    let n := expArgRedN abs_x
    let y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
    let ty := taylorExpQ y expNumTerms
    let pos_result := repeatedSquare ty n
    let result : ℚ := pos_result
    let p := result.num.natAbs
    let d := result.den
    let s_int : ℤ := ((FloatFormat.prec.toNat + 4 : ℕ) : ℤ) +
      ((Nat.log2 d : ℕ) : ℤ) - ((Nat.log2 p : ℕ) : ℤ)
    let s := s_int.toNat
    Real.exp (a.toVal : ℝ) - (result : ℝ) < 1 / (2 : ℝ) ^ s := by
  sorry

/-- Analogous error bound for the negative case. -/
private theorem taylor_approx_error_neg (a : FiniteFp) (hm : a.m ≠ 0)
    (hx_neg : a.toVal (R := ℚ) < 0) :
    let x : ℚ := a.toVal
    let abs_x : ℚ := |x|
    let n := expArgRedN abs_x
    let y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
    let ty := taylorExpQ y expNumTerms
    let pos_result := repeatedSquare ty n
    let result : ℚ := 1 / pos_result
    let p := result.num.natAbs
    let d := result.den
    let s_int : ℤ := ((FloatFormat.prec.toNat + 4 : ℕ) : ℤ) +
      ((Nat.log2 d : ℕ) : ℤ) - ((Nat.log2 p : ℕ) : ℤ)
    let s := s_int.toNat
    (result : ℝ) - Real.exp (a.toVal : ℝ) < 1 / (2 : ℝ) ^ s := by
  sorry

private theorem expComputableRun_sticky_interval (a : FiniteFp) (hm : a.m ≠ 0) :
    let o := expComputableRun a
    inStickyInterval (R := ℝ) o.q o.e_base (Real.exp (a.toVal : ℝ)) := by
  -- Unfold to get at the components
  simp only [expComputableRun, hm, ↓reduceIte]
  set x : ℚ := a.toVal
  set abs_x : ℚ := |x|
  set n := expArgRedN abs_x
  set y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
  set ty := taylorExpQ y expNumTerms
  set pos_result := repeatedSquare ty n
  -- The goal is inStickyInterval q e_base (exp(a.toVal)) after unfolding expExtract.
  -- This means: 2q · 2^e_base < exp(x) ∧ exp(x) < 2(q+1) · 2^e_base
  -- Split on sign
  by_cases hx : 0 ≤ x
  · -- Positive case: result = pos_result, isUpper = false (no q-adjustment)
    have hx_not_neg : ¬(x < 0) := not_lt.mpr hx
    simp only [hx_not_neg, ↓reduceIte]
    -- Now goal involves expExtract pos_result false
    -- Use the error bound and floor properties
    sorry
  · -- Negative case: result = 1/pos_result, isUpper = true
    push_neg at hx
    simp only [hx, ↓reduceIte]
    sorry

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
    -- In the non-zero branch, output comes from expExtract
    have hnonzero : expComputableRun a = expExtract
        (if a.toVal (R := ℚ) < 0
         then 1 / repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms)
           (expArgRedN |a.toVal (R := ℚ)|)
         else repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms)
           (expArgRedN |a.toVal (R := ℚ)|))
        (decide (a.toVal (R := ℚ) < 0)) := by
      simp only [expComputableRun, hm, ↓reduceIte]
    rw [hnonzero] at hr; rw [← hr]
    exact expExtract_q_ge _ (expComputableRun_result_pos a hm) _
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
