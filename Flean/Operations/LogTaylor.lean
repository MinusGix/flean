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

/-- The `go` function with `term = (-t)^k · t / (k+1)` and `acc = 0` produces
the partial sum from index k to k+fuel. Cast version to ℝ. -/
theorem taylorLogQ_go_cast_eq (t : ℚ) (fuel k : ℕ) (term acc : ℚ)
    (hterm : (term : ℝ) = (-(t : ℝ)) ^ k * (t : ℝ) / ((k : ℝ) + 1)) :
    (taylorLogQ.go t fuel k term acc : ℝ) = (acc : ℝ) +
      ∑ j ∈ Finset.Ico (k + 1) (k + 1 + fuel),
        (-1 : ℝ) ^ j * (↑t : ℝ) ^ (j + 1) / ((j : ℝ) + 1) := by
  induction fuel generalizing k term acc with
  | zero =>
    simp [taylorLogQ.go, Finset.Ico_self]
  | succ n ih =>
    simp only [taylorLogQ.go]
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    have hk2q : (k : ℚ) + 2 ≠ 0 := by positivity
    set nextTerm := term * (-t) * ((↑k + 1) / (↑k + 2)) with hnext_def
    have hnext_cast : (nextTerm : ℝ) = (-(t : ℝ)) ^ (k + 1) * (t : ℝ) / ((↑(k + 1) : ℝ) + 1) := by
      simp only [hnext_def]; push_cast; rw [hterm]
      field_simp; ring
    rw [ih (k + 1) nextTerm (acc + nextTerm) hnext_cast]
    push_cast
    rw [show k + 1 + 1 + n = k + 1 + (n + 1) from by omega]
    rw [show Finset.Ico (k + 1 + 1) (k + 1 + (n + 1)) =
        Finset.Ico (k + 2) (k + 2 + n) from by congr 1 <;> omega]
    have hIco : Finset.Ico (k + 1) (k + 1 + (n + 1)) =
        {k + 1} ∪ Finset.Ico (k + 2) (k + 2 + n) := by
      ext x; simp [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
    rw [hIco]
    have hdisj : Disjoint ({k + 1} : Finset ℕ) (Finset.Ico (k + 2) (k + 2 + n)) := by
      rw [Finset.disjoint_left]; intro x hx hx2
      simp [Finset.mem_singleton] at hx; simp [Finset.mem_Ico] at hx2; omega
    rw [Finset.sum_union hdisj, Finset.sum_singleton, hnext_cast]
    rw [show (-(t : ℝ)) ^ (k + 1) * (↑t : ℝ) / (↑(k + 1) + 1) =
        (-1 : ℝ) ^ (k + 1) * (↑t : ℝ) ^ (k + 1 + 1) / (↑(k + 1) + 1) from by
      rw [neg_pow]; ring]
    push_cast; ring

/-- `taylorLogQ t n` cast to ℝ equals `∑_{i=0}^{n-1} (-1)^i · t^(i+1) / (i+1)`. -/
theorem taylorLogQ_cast_eq_sum (t : ℚ) (n : ℕ) :
    (taylorLogQ t n : ℝ) =
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (t : ℝ) ^ (k + 1) / (↑k + 1) := by
  simp only [taylorLogQ]
  split
  · case isTrue h => subst h; simp
  · case isFalse h =>
    push_neg at h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    show (taylorLogQ.go t (n - 1) 0 t t : ℝ) = _
    have hterm : (t : ℝ) = (-(t : ℝ)) ^ 0 * (↑t : ℝ) / ((↑(0 : ℕ) : ℝ) + 1) := by simp
    rw [taylorLogQ_go_cast_eq t (n - 1) 0 t t hterm]
    push_cast
    rw [show 0 + 1 + (n - 1) = n from by omega]
    -- acc = t = the k=0 term, plus sum from k=1 to n-1
    rw [show Finset.range n = {0} ∪ Finset.Ico 1 n from by
      ext x; simp [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      omega]
    rw [Finset.sum_union (by
      rw [Finset.disjoint_left]; intro x hx hx2
      simp [Finset.mem_singleton, Finset.mem_Ico] at hx hx2; omega)]
    simp only [Finset.sum_singleton, pow_zero, one_mul, Nat.cast_zero, zero_add]
    ring

/-! ## Alternating series bounds -/

/-- The log Taylor terms `t^(k+1)/(k+1)` are antitone for `0 ≤ t ≤ 1`. -/
private theorem logTerms_antitone (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) ≤ 1) :
    Antitone (fun k : ℕ => (t : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) := by
  have ht' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  intro a b hab
  -- t^(b+1)/(b+1) ≤ t^(a+1)/(a+1) because t^(b+1) ≤ t^(a+1) and 1/(b+1) ≤ 1/(a+1)
  apply mul_le_mul
  · exact pow_le_pow_of_le_one ht' ht1 (by omega)
  · exact inv_anti₀ (by positivity) (by linarith [show (a : ℝ) ≤ b from Nat.cast_le.mpr hab])
  · positivity
  · exact pow_nonneg ht' _

/-- The log Taylor series `∑ (-1)^k t^(k+1)/(k+1)` converges to `log(1+t)` for `0 ≤ t < 1`. -/
theorem hasSum_log_taylor (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) < 1) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (t : ℝ) ^ (k + 1) / ((k : ℝ) + 1))
      (Real.log (1 + (t : ℝ))) := by
  have htabs : |(-↑t : ℝ)| < 1 := by rwa [abs_neg, abs_of_nonneg (by exact_mod_cast ht)]
  have h := Real.hasSum_pow_div_log_of_abs_lt_one htabs
  -- h : HasSum (fun n => (-t)^(n+1) / (n+1)) (-log(1-(-t))) = (-log(1+t))
  -- We want: HasSum (fun n => (-1)^n * t^(n+1) / (n+1)) (log(1+t))
  simp only [neg_neg, ← neg_pow] at h
  convert h.neg using 1
  · ext k; ring
  · simp

/-- Tendsto version of `hasSum_log_taylor` in the `(-1)^i * f i` form. -/
theorem tendsto_log_taylor (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) < 1) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * ((t : ℝ) ^ (i + 1) / ((i : ℝ) + 1)))
      Filter.atTop (nhds (Real.log (1 + (t : ℝ)))) := by
  have h := (hasSum_log_taylor t ht ht1).tendsto_sum_nat
  simp only [mul_div_assoc] at h
  exact h

/-- For `0 ≤ t < 1` and even `N`, `taylorLogQ t (2N) ≤ log(1+t)` (lower bound). -/
theorem taylorLogQ_even_le_log (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) < 1) (N : ℕ) :
    (taylorLogQ t (2 * N) : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  rw [taylorLogQ_cast_eq_sum]
  simp only [mul_div_assoc]
  exact Antitone.alternating_series_le_tendsto
    (tendsto_log_taylor t ht ht1) (logTerms_antitone t ht ht1.le) N

/-- For `0 ≤ t < 1`, `log(1+t) ≤ taylorLogQ t (2N+1)` (upper bound). -/
theorem log_le_taylorLogQ_odd (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) < 1) (N : ℕ) :
    Real.log (1 + (t : ℝ)) ≤ (taylorLogQ t (2 * N + 1) : ℝ) := by
  rw [taylorLogQ_cast_eq_sum]
  simp only [mul_div_assoc]
  exact Antitone.tendsto_le_alternating_series
    (tendsto_log_taylor t ht ht1) (logTerms_antitone t ht ht1.le) N

/-! ## Positivity -/

/-- `logUpperBound t N > 0` for `0 < t < 1`. -/
theorem logUpperBound_pos (t : ℚ) (ht : 0 < t) (ht1 : (t : ℝ) < 1) (N : ℕ) :
    (0 : ℝ) < (logUpperBound t N : ℝ) := by
  calc (0 : ℝ) < Real.log (1 + (t : ℝ)) := by
        apply Real.log_pos; linarith [show (0 : ℝ) < (t : ℝ) from by exact_mod_cast ht]
    _ ≤ (logUpperBound t N : ℝ) := by
        exact log_le_taylorLogQ_odd t ht.le ht1 N

/-- Even partial sums are monotonically increasing: `S_{2M} ≤ S_{2N}` for `M ≤ N`. -/
theorem logLowerBound_mono (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) ≤ 1) (M N : ℕ) (hMN : M ≤ N) :
    (logLowerBound t M : ℝ) ≤ (logLowerBound t N : ℝ) := by
  suffices h : ∀ k : ℕ, (logLowerBound t M : ℝ) ≤ (logLowerBound t (M + k) : ℝ) by
    have := h (N - M)
    rwa [show M + (N - M) = N from by omega] at this
  intro k; induction k with
  | zero => simp
  | succ k ih =>
    calc (logLowerBound t M : ℝ) ≤ (logLowerBound t (M + k) : ℝ) := ih
      _ ≤ (logLowerBound t (M + k + 1) : ℝ) := by
          unfold logLowerBound
          rw [taylorLogQ_cast_eq_sum, taylorLogQ_cast_eq_sum]
          rw [show 2 * (M + k + 1) = 2 * (M + k) + 1 + 1 from by omega]
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          simp only [mul_div_assoc]
          set S := ∑ i ∈ Finset.range (2 * (M + k)),
            (-1 : ℝ) ^ i * ((t : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
          -- Adding pair: (-1)^{2(M+k)} * a + (-1)^{2(M+k)+1} * a' = a - a' ≥ 0
          have h_even : (-1 : ℝ) ^ (2 * (M + k)) = 1 := by simp
          have h_odd : (-1 : ℝ) ^ (2 * (M + k) + 1) = -1 := by simp [pow_succ]
          simp only [h_even, h_odd, one_mul, neg_one_mul, neg_div]
          have hanti := logTerms_antitone t ht ht1
            (show 2 * (M + k) ≤ 2 * (M + k) + 1 by omega)
          simp only [show (2 * (M + k) + 1 : ℕ) + 1 = 2 * (M + k) + 1 + 1 from by omega,
                     show ((2 * (M + k) + 1 : ℕ) : ℝ) + 1 = ↑(2 * (M + k) + 1) + 1 from by push_cast; ring,
                     show ((2 * (M + k) : ℕ) : ℝ) + 1 = ↑(2 * (M + k)) + 1 from by push_cast; ring] at hanti
          linarith

/-- `logLowerBound t N > 0` for `0 < t < 1` and `N ≥ 1`.
`S_2 = t - t²/2 > 0`, and even partial sums are increasing. -/
theorem logLowerBound_pos (t : ℚ) (ht : 0 < t) (ht1 : (t : ℝ) < 1) (N : ℕ) (hN : 1 ≤ N) :
    (0 : ℝ) < (logLowerBound t N : ℝ) := by
  calc (0 : ℝ) < (logLowerBound t 1 : ℝ) := by
        unfold logLowerBound; rw [taylorLogQ_two_terms]; push_cast
        have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
        nlinarith [sq_nonneg ((t : ℝ) - 1)]
    _ ≤ (logLowerBound t N : ℝ) :=
        logLowerBound_mono t ht.le ht1.le 1 N hN

/-- `logLowerBound t N ≥ 0` for `0 ≤ t < 1`. -/
theorem logLowerBound_nonneg (t : ℚ) (ht : 0 ≤ t) (ht1 : (t : ℝ) < 1) (N : ℕ) :
    (0 : ℝ) ≤ (logLowerBound t N : ℝ) := by
  -- S_0 = 0 ≤ S_2 ≤ ... ≤ S_{2N} (even partial sums are monotonically increasing
  -- for antitone alternating series), so 0 = S_0 ≤ S_{2N}.
  unfold logLowerBound
  rw [taylorLogQ_cast_eq_sum]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 from by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have ht' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    -- Adding two consecutive terms: (-1)^{2N} * a_{2N} + (-1)^{2N+1} * a_{2N+1}
    -- = a_{2N} - a_{2N+1} ≥ 0 since a is antitone
    have h2N_even : (-1 : ℝ) ^ (2 * N) = 1 := by simp
    have h2N1_odd : (-1 : ℝ) ^ (2 * N + 1) = -1 := by simp [pow_succ]
    simp only [mul_div_assoc, h2N_even, h2N1_odd, one_mul, neg_one_mul, neg_div] at ih ⊢
    have hanti := logTerms_antitone t ht ht1.le (show 2 * N ≤ 2 * N + 1 by omega)
    -- hanti : t^(2N+2)/(2N+2) ≤ t^(2N+1)/(2N+1)
    simp only [show (2 * N + 1 : ℕ) + 1 = 2 * N + 1 + 1 from by omega,
               show ((2 * N + 1 : ℕ) : ℝ) + 1 = ↑(2 * N + 1) + 1 from by push_cast; ring,
               show ((2 * N : ℕ) : ℝ) + 1 = ↑(2 * N) + 1 from by push_cast; ring] at hanti
    linarith
