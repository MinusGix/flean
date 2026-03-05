import Flean.Util
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Taylor series for `log(1+t)` in ℚ

Rational Taylor partial sums for `log(1+t) = t - t²/2 + t³/3 - t⁴/4 + ...`
Used by the log reference kernel to compute rigorous brackets around `log(x)`.

## Key property: alternating series bounds

For `0 ≤ t ≤ 1`, the series is alternating with decreasing terms, so:
- **Even** partial sums are **lower bounds**: `taylorLogQ t (2N) ≤ log(1+t)`
- **Odd** partial sums are **upper bounds**: `log(1+t) ≤ taylorLogQ t (2N+1)`

This gives clean brackets without a separate remainder estimate.

## Main definitions

- `taylorLogQ t n`: evaluates `∑_{k=1}^{n} (-1)^{k+1} t^k/k` in ℚ via forward recurrence
- `logLowerBound t N`: even partial sum `taylorLogQ t (2N)` (lower bound)
- `logUpperBound t N`: odd partial sum `taylorLogQ t (2N+1)` (upper bound)
-/

/-- Evaluate `log(1+t) ≈ ∑_{k=1}^{numTerms} (-1)^{k+1} t^k/k` in ℚ.
Uses forward recurrence: `term_{k+1} = term_k · (-t) · k/(k+1)`.
The alternating sign is absorbed into the term. -/
def taylorLogQ (t : ℚ) (numTerms : ℕ) : ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ → ℚ
    | 0, _, _, acc => acc
    | fuel + 1, k, term, acc =>
        -- term = (-1)^{k} · t^{k+1} / (k+1) at entry (0-indexed: k=0 gives +t/1)
        let nextTerm := term * (-t) * ((k + 1 : ℚ) / (k + 2 : ℚ))
        go fuel (k + 1) nextTerm (acc + nextTerm)
  if numTerms = 0 then 0
  else go (numTerms - 1) 0 t t
  -- Start: k=0, term = t (the first term +t/1), acc = t

/-- Lower bound on `log(1+t)` using an even number of Taylor terms. -/
def logLowerBound (t : ℚ) (N : ℕ) : ℚ := taylorLogQ t (2 * N)

/-- Upper bound on `log(1+t)` using an odd number of Taylor terms. -/
def logUpperBound (t : ℚ) (N : ℕ) : ℚ := taylorLogQ t (2 * N + 1)

/-! ## Basic computational properties -/

theorem taylorLogQ_zero_terms (t : ℚ) : taylorLogQ t 0 = 0 := by
  simp [taylorLogQ]

theorem taylorLogQ_one_term (t : ℚ) : taylorLogQ t 1 = t := by
  simp [taylorLogQ, taylorLogQ.go]

theorem taylorLogQ_two_terms (t : ℚ) : taylorLogQ t 2 = t - t ^ 2 / 2 := by
  simp [taylorLogQ, taylorLogQ.go]; ring

theorem taylorLogQ_at_zero (n : ℕ) : taylorLogQ 0 n = 0 := by
  simp only [taylorLogQ]
  split
  · rfl
  · -- All terms are 0 since t = 0
    suffices ∀ fuel k (term acc : ℚ), term = 0 → acc = 0 →
        taylorLogQ.go 0 fuel k term acc = 0 from
      this _ 0 0 0 (by ring) rfl
    intro fuel; induction fuel with
    | zero => intro _ _ _ _ hacc; simp [taylorLogQ.go, hacc]
    | succ n ih =>
      intro k term acc hterm hacc
      simp only [taylorLogQ.go]
      apply ih
      · rw [hterm]; ring
      · rw [hacc, hterm]; ring

/-! ## Cast to ℝ as Finset sum -/

/-- The `go` function with acc=0 is additive in acc. -/
theorem taylorLogQ_go_add (t : ℚ) (fuel k : ℕ) (term c acc : ℚ) :
    taylorLogQ.go t fuel k term (c + acc) = c + taylorLogQ.go t fuel k term acc := by
  induction fuel generalizing k term acc with
  | zero => simp [taylorLogQ.go]
  | succ n ih =>
    simp only [taylorLogQ.go]
    rw [show c + acc + term * (-t) * ((↑k + 1) / (↑k + 2)) =
        c + (acc + term * (-t) * ((↑k + 1) / (↑k + 2))) from by ring]
    exact ih _ _ _

/-- The k-th term (1-indexed) of the log series: `(-1)^{k+1} · t^k / k`. -/
noncomputable def logSeriesTerm (t : ℝ) (k : ℕ) : ℝ :=
  (-1) ^ (k + 1) * t ^ k / k

/-- `taylorLogQ t n` cast to ℝ equals `∑_{k=1}^{n} (-t)^{k-1} · t / k · (-1)^...`,
i.e., the standard log(1+t) partial sum. -/
theorem taylorLogQ_cast_eq_sum (t : ℚ) (n : ℕ) :
    (taylorLogQ t n : ℝ) =
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (t : ℝ) ^ (k + 1) / (↑k + 1) := by
  simp only [taylorLogQ]
  split
  · case isTrue h => subst h; simp
  · case isFalse h =>
    push_neg at h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    -- Prove by induction on fuel that go computes the partial sum
    sorry

/-! ## Alternating series bounds -/

/-- For `0 ≤ t ≤ 1` and even `N`, `taylorLogQ t N ≤ log(1+t)` (lower bound). -/
theorem taylorLogQ_even_le_log (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) ≤ 1) (N : ℕ) :
    (taylorLogQ t (2 * N) : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  sorry

/-- For `0 ≤ t ≤ 1` and odd `N ≥ 1`, `log(1+t) ≤ taylorLogQ t (2N+1)` (upper bound). -/
theorem log_le_taylorLogQ_odd (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) ≤ 1) (N : ℕ) :
    Real.log (1 + (t : ℝ)) ≤ (taylorLogQ t (2 * N + 1) : ℝ) := by
  sorry

/-- For `0 < t ≤ 1`, the even partial sum is *strictly* less than `log(1+t)`. -/
theorem taylorLogQ_even_lt_log (t : ℚ) (ht : 0 < t) (ht1 : (t : ℝ) ≤ 1) (N : ℕ) :
    (taylorLogQ t (2 * N) : ℝ) < Real.log (1 + (t : ℝ)) := by
  sorry

/-! ## Positivity -/

/-- `logUpperBound t N > 0` for `0 < t ≤ 1`. -/
theorem logUpperBound_pos (t : ℚ) (ht : 0 < t) (ht1 : (t : ℝ) ≤ 1) (N : ℕ) :
    (0 : ℝ) < (logUpperBound t N : ℝ) := by
  sorry

/-- `logLowerBound t N ≥ 0` for `0 ≤ t ≤ 1`. -/
theorem logLowerBound_nonneg (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) ≤ 1) (N : ℕ) :
    (0 : ℝ) ≤ (logLowerBound t N : ℝ) := by
  sorry
