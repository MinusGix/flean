import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Taylor series for `exp` in ℚ

Rational Taylor partial sums and remainder bounds for `exp(y)`.
Used by `ExpComputable.lean` to compute rigorous brackets around `exp(x)`.

## Main definitions

- `taylorExpQ y n`: evaluates `Σ_{k=0}^{n} y^k/k!` in ℚ via forward recurrence
- `taylorRemainder y n`: computes a rational upper bound on `|exp(y) - taylorExpQ y (n-1)|`

## Main results

- `taylorExpQ_le_exp`: `taylorExpQ y n ≤ exp(y)` for `y ≥ 0` (all terms positive)
- `taylorExpQ_lt_exp`: strict version for `y > 0`
- `exp_le_taylor_upper`: `exp(y) ≤ taylorExpQ y N + taylorRemainder y (N+1)` for `0 ≤ y ≤ 1`
- `taylorExpQ_ge_one`: `taylorExpQ y n ≥ 1` for `y ≥ 0`
- `taylorExpQ_zero`: `taylorExpQ 0 n = 1`
-/

/-- Evaluate `exp(y) ≈ Σ_{k=0}^{numTerms} y^k/k!` in ℚ.
Uses forward recurrence `term_{k+1} = term_k · y / (k+1)`.
All terms are positive when `y > 0`, guaranteeing a lower bound. -/
def taylorExpQ (y : ℚ) (numTerms : ℕ) : ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ → ℚ
    | 0, _, acc, _ => acc
    | fuel + 1, k, acc, term =>
        let nextTerm := term * y / (k + 1)
        go fuel (k + 1) (acc + nextTerm) nextTerm
  go numTerms 0 1 1  -- start: k=0, acc=1 (term_0), term=1 (term_0)

/-- Compute the Taylor remainder bound: `y^N * (N+1) / (N! * N)`.
This bounds `|exp(y) - ∑_{k<N} y^k/k!|` for `|y| ≤ 1`.
For our use: exp(y) ≤ taylorExpQ y (N-1) + taylorRemainder y N. -/
def taylorRemainder (y : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 1  -- degenerate case
  else y ^ n * (n + 1) / (n.factorial * n)

/-! ## taylorExpQ ≥ 1 -/

/-- Taylor series with nonneg input gives result ≥ 1 (since first term is 1 and rest are nonneg). -/
theorem taylorExpQ_ge_one (y : ℚ) (hy : 0 ≤ y) (n : ℕ) :
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

/-! ## taylorExpQ ↔ Finset.sum bridge -/

open Finset in
/-- Loop invariant: when `term = y^k/k!` and `acc = ∑_{i<k+1} y^i/i!`,
the loop computes `∑_{i<k+fuel+1} y^i/i!`. -/
theorem taylorExpQ_go_eq (y : ℚ) :
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

open Finset in
/-- `taylorExpQ y n` equals the standard Taylor partial sum `∑_{k<n+1} y^k/k!` in ℚ. -/
theorem taylorExpQ_eq_sum (y : ℚ) (n : ℕ) :
    taylorExpQ y n = ∑ k ∈ range (n + 1), y ^ k / (k.factorial : ℚ) := by
  simp only [taylorExpQ]
  have hterm : (1 : ℚ) = y ^ 0 / (Nat.factorial 0 : ℚ) := by simp
  have hacc : (1 : ℚ) = ∑ i ∈ range (0 + 1), y ^ i / (i.factorial : ℚ) := by
    rw [sum_range_one]; simp
  rw [taylorExpQ_go_eq y n 0 1 1 hterm hacc, show 0 + n + 1 = n + 1 from by omega]

open Finset in
/-- Cast of `taylorExpQ` to ℝ equals the real Taylor partial sum. -/
theorem taylorExpQ_cast_eq_sum (y : ℚ) (n : ℕ) :
    (taylorExpQ y n : ℝ) = ∑ k ∈ range (n + 1), (y : ℝ) ^ k / (k.factorial : ℝ) := by
  rw [taylorExpQ_eq_sum]; push_cast; rfl

/-- The real Taylor partial sum lower-bounds `exp` for nonneg arguments. -/
theorem taylorExpQ_le_exp (y : ℚ) (hy : 0 ≤ y) (n : ℕ) :
    (taylorExpQ y n : ℝ) ≤ Real.exp (y : ℝ) := by
  rw [taylorExpQ_cast_eq_sum]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hy) _

/-! ## Strict Taylor inequality -/

/-- The Taylor partial sum is STRICTLY less than exp for y > 0.
This follows because all omitted terms y^k/k! for k > N are strictly positive. -/
theorem taylorExpQ_lt_exp (y : ℚ) (hy : 0 < y) (n : ℕ) :
    (taylorExpQ y n : ℝ) < Real.exp (y : ℝ) := by
  have hy_real : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hterm : (0 : ℝ) < (y : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    div_pos (pow_pos hy_real _) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  have hle2 := Real.sum_le_exp_of_nonneg (le_of_lt hy_real) (n + 2)
  rw [show n + 2 = n + 1 + 1 from by omega, Finset.sum_range_succ] at hle2
  rw [taylorExpQ_cast_eq_sum]
  linarith

/-- `taylorExpQ(0, N) = 1` for all N. -/
theorem taylorExpQ_zero (N : ℕ) : taylorExpQ (0 : ℚ) N = 1 := by
  simp only [taylorExpQ]
  cases N with
  | zero => simp [taylorExpQ.go]
  | succ n =>
    simp [taylorExpQ.go]
    suffices ∀ fuel k (acc : ℚ), taylorExpQ.go 0 fuel k acc 0 = acc from this n 1 1
    intro fuel; induction fuel with
    | zero => simp [taylorExpQ.go]
    | succ n ih => intro k acc; simp [taylorExpQ.go, ih]

/-! ## Taylor remainder -/

/-- `taylorRemainder y (N+1)` as a real equals the standard bound form. -/
theorem taylorRemainder_cast (y : ℚ) (N : ℕ) (hN : 0 < N) :
    (taylorRemainder y (N + 1) : ℝ) =
      (y : ℝ) ^ (N + 1) * (↑(N + 1) + 1) / ((N + 1).factorial * (↑(N + 1) : ℝ)) := by
  simp only [taylorRemainder, show N + 1 ≠ 0 from by omega, ↓reduceIte]
  push_cast; ring

/-- Taylor partial sum + remainder upper-bounds `exp(y)` for `0 ≤ y ≤ 1`. -/
theorem exp_le_taylor_upper (y : ℚ) (hy0 : 0 ≤ y) (hy1 : (y : ℝ) ≤ 1) (N : ℕ)
    (hN : 0 < N) :
    Real.exp (y : ℝ) ≤ (taylorExpQ y N : ℝ) + (taylorRemainder y (N + 1) : ℝ) := by
  rw [taylorExpQ_cast_eq_sum, taylorRemainder_cast y N hN]
  exact Real.exp_bound' (by exact_mod_cast hy0) hy1 (n := N + 1) (by omega)

/-- Strict Taylor upper bound: `exp(y) < taylorExpQ y N + taylorRemainder y (N+1)` for `y > 0`. -/
theorem exp_lt_taylor_upper (y : ℚ) (hy_pos : 0 < y) (hy1 : (y : ℝ) ≤ 1) (N : ℕ)
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

/-- Taylor remainder `R(a, N+1) ≤ R(b, N+1)` for `0 ≤ a ≤ b`. -/
lemma taylorRemainder_le_of_le (a b : ℚ) (N : ℕ) (hN : 0 < N)
    (ha : 0 ≤ a) (hab : (a : ℝ) ≤ (b : ℝ)) :
    (taylorRemainder a (N + 1) : ℝ) ≤ (taylorRemainder b (N + 1) : ℝ) := by
  rw [taylorRemainder_cast a N hN, taylorRemainder_cast b N hN]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by exact_mod_cast ha) hab _
