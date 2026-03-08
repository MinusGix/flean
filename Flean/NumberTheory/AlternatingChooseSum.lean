import Mathlib.Data.Nat.Choose.Vandermonde

/-! # Alternating binomial identity via polynomial method

We prove `Σ_{k=0}^j (-1)^k C(j,k) C(M-k,n) = C(M-j, n-j)` for `j ≤ n ≤ M`
using the binomial theorem in `Polynomial ℤ`.

Key application: establishing the Padé condition for the diagonal Padé
approximant to `exp(x)`, showing the first `2N+1` Taylor coefficients of
`P_N(x)·exp(x) - Q_N(x)` vanish.
-/

open Nat Finset BigOperators Polynomial

/-- The binomial theorem for `(-1) + (X+1) = X` in `Polynomial ℤ`:
`Σ_{k=0}^j (-1)^k · (X+1)^{j-k} · C(j,k) = X^j`. -/
lemma binom_neg_one_X_add_one (j : ℕ) :
    ∑ k ∈ range (j + 1), (-1 : Polynomial ℤ) ^ k * (X + 1) ^ (j - k) *
      Polynomial.C (j.choose k : ℤ) = (X : Polynomial ℤ) ^ j := by
  have h := (Commute.all (-1 : Polynomial ℤ) (X + 1)).add_pow j
  simp only [show (-1 : Polynomial ℤ) + (X + 1) = X from by ring] at h
  rw [h]; exact Finset.sum_congr rfl fun k _ => by norm_cast

private lemma neg_one_poly_pow (k : ℕ) :
    (-1 : Polynomial ℤ) ^ k = Polynomial.C ((-1 : ℤ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_1]

/-- Main combinatorial identity:
`Σ_{k=0}^j (-1)^k C(j,k) C(M-k, n) = C(M-j, n-j)` for `j ≤ n ≤ M`.

Proof: multiply `binom_neg_one_X_add_one` by `(X+1)^{M-j}` and extract
the coefficient of `X^n`. -/
theorem alternating_choose_sum (M n j : ℕ) (hjn : j ≤ n) (hnM : n ≤ M) :
    ∑ k ∈ range (j + 1), (-1 : ℤ) ^ k * (j.choose k : ℤ) * ((M - k).choose n : ℤ) =
      ((M - j).choose (n - j) : ℤ) := by
  have hpoly := binom_neg_one_X_add_one j
  have hmul : (∑ k ∈ range (j + 1), (-1 : Polynomial ℤ) ^ k * (X + 1) ^ (j - k) *
      Polynomial.C (↑(j.choose k) : ℤ)) * (X + 1) ^ (M - j) =
      (X : Polynomial ℤ) ^ j * (X + 1) ^ (M - j) := by rw [hpoly]
  rw [Finset.sum_mul] at hmul
  have hcoeff := congr_arg (Polynomial.coeff · n) hmul
  simp only [Polynomial.finset_sum_coeff] at hcoeff
  -- RHS: [X^n](X^j · (X+1)^{M-j}) = C(M-j, n-j)
  conv_rhs at hcoeff =>
    rw [show n = (n - j) + j from by omega, Polynomial.coeff_X_pow_mul,
        Polynomial.coeff_X_add_one_pow]
  rw [← hcoeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ j := by simp [Finset.mem_range] at hk; omega
  symm
  rw [neg_one_poly_pow]
  have hpow : (X + 1 : Polynomial ℤ) ^ (j - k) * (X + 1) ^ (M - j) = (X + 1) ^ (M - k) := by
    rw [← pow_add]; congr 1; omega
  rw [show Polynomial.C ((-1 : ℤ) ^ k) * (X + 1) ^ (j - k) *
      Polynomial.C (↑(j.choose k) : ℤ) * (X + 1) ^ (M - j) =
      Polynomial.C ((-1 : ℤ) ^ k * ↑(j.choose k)) * ((X + 1) ^ (j - k) * (X + 1) ^ (M - j))
      from by rw [Polynomial.C_mul]; ring]
  rw [hpow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]

/-- Coefficient of `X^j * p` below degree `j` is 0. -/
private lemma coeff_X_pow_mul_of_lt {R : Type*} [CommSemiring R] (j : ℕ) (p : Polynomial R)
    (n : ℕ) (hn : n < j) : Polynomial.coeff (X ^ j * p) n = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_antidiagonal] at hab
  -- a + b = n, and coeff (X^j) a = 0 since a ≤ n < j
  have : a ≠ j := by omega
  simp [Polynomial.coeff_X_pow, this]

/-- For `j > n`, the alternating sum vanishes because `X^j · (X+1)^{M-j}` has
minimum degree `j > n`, so its `n`-th coefficient is 0.
This handles the Padé condition for indices `N < j ≤ 2N`. -/
theorem alternating_choose_sum_zero (M n j : ℕ) (hjn : n < j) (hjM : j ≤ M) :
    ∑ k ∈ range (j + 1), (-1 : ℤ) ^ k * (j.choose k : ℤ) * ((M - k).choose n : ℤ) = 0 := by
  have hpoly := binom_neg_one_X_add_one j
  have hmul : (∑ k ∈ range (j + 1), (-1 : Polynomial ℤ) ^ k * (X + 1) ^ (j - k) *
      Polynomial.C (↑(j.choose k) : ℤ)) * (X + 1) ^ (M - j) =
      (X : Polynomial ℤ) ^ j * (X + 1) ^ (M - j) := by rw [hpoly]
  rw [Finset.sum_mul] at hmul
  have hcoeff := congr_arg (Polynomial.coeff · n) hmul
  simp only [Polynomial.finset_sum_coeff] at hcoeff
  -- RHS: [X^n](X^j · (X+1)^{M-j}) = 0 because min degree = j > n
  rw [coeff_X_pow_mul_of_lt j _ n hjn] at hcoeff
  -- Now hcoeff : Σ ... = 0. Rewrite LHS to match goal.
  rw [← hcoeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ j := by simp [Finset.mem_range] at hk; omega
  symm
  rw [neg_one_poly_pow]
  have hpow : (X + 1 : Polynomial ℤ) ^ (j - k) * (X + 1) ^ (M - j) = (X + 1) ^ (M - k) := by
    rw [← pow_add]; congr 1; omega
  rw [show Polynomial.C ((-1 : ℤ) ^ k) * (X + 1) ^ (j - k) *
      Polynomial.C (↑(j.choose k) : ℤ) * (X + 1) ^ (M - j) =
      Polynomial.C ((-1 : ℤ) ^ k * ↑(j.choose k)) * ((X + 1) ^ (j - k) * (X + 1) ^ (M - j))
      from by rw [Polynomial.C_mul]; ring]
  rw [hpow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]
