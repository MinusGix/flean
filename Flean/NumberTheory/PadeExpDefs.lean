import Flean.NumberTheory.ExpEffectiveBound
import Flean.NumberTheory.AlternatingChooseSum
import Flean.Linearize.Linearize
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Padé approximation to `exp(x)` — definitions and basic properties

Definitions of `padeCoeff`, `padeP`, `padeQ`, `padeR`, clearing denominators,
the Padé condition (coefficient vanishing), the remainder bound (`padeR_bound`),
positivity, `padeP_abs_le`, and non-vanishing (`padeR_ne_zero`).

The effective irrationality measure built on these is in `PadeExp.lean`.
-/

open Real Finset BigOperators

/-! ## Padé polynomials -/

/-- Coefficient of the Padé polynomial: `C(2N-k, N) / k!` -/
noncomputable def padeCoeff (N k : ℕ) : ℝ :=
  (Nat.choose (2 * N - k) N : ℝ) / (k.factorial : ℝ)

/-- The P polynomial: `P_N(x) = Σ_{k=0}^N C(2N-k,N) · (-x)^k / k!` -/
noncomputable def padeP (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), padeCoeff N k * (-x) ^ k

/-- The Q polynomial: `Q_N(x) = Σ_{k=0}^N C(2N-k,N) · x^k / k!` -/
noncomputable def padeQ (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), padeCoeff N k * x ^ k

/-- The Padé remainder: `R_N(x) = P_N(x) · exp(x) - Q_N(x)`. -/
noncomputable def padeR (N : ℕ) (x : ℝ) : ℝ :=
  padeP N x * exp x - padeQ N x

/-! ## Basic properties -/

theorem padeCoeff_pos (N k : ℕ) (hk : k ≤ N) : 0 < padeCoeff N k := by
  simp only [padeCoeff]
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega)
  · exact_mod_cast Nat.factorial_pos k

theorem padeP_zero (N : ℕ) : padeP N 0 = (Nat.choose (2 * N) N : ℝ) := by
  simp only [padeP, padeCoeff, neg_zero]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · simp
  · intro k _ hk; simp [zero_pow (by omega : k ≠ 0)]

theorem padeQ_zero (N : ℕ) : padeQ N 0 = (Nat.choose (2 * N) N : ℝ) := by
  simp only [padeQ, padeCoeff]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · simp
  · intro k _ hk; simp [zero_pow (by omega : k ≠ 0)]

theorem padeR_zero (N : ℕ) : padeR N 0 = 0 := by
  simp [padeR, padeP_zero, padeQ_zero]

/-! ## Clearing denominators

For `x = a/b`, `N! · b^N · padeCoeff N k · x^k` is an integer for `k ≤ N`:
`N! · b^N · C(2N-k,N) · (a/b)^k / k! = (N!/k!) · C(2N-k,N) · a^k · b^{N-k}`
and `N!/k!` is an integer since `k ≤ N`. -/

/-- `k! ∣ N!` as naturals for `k ≤ N`. -/
private theorem factorial_dvd_factorial (k N : ℕ) (hk : k ≤ N) :
    k.factorial ∣ N.factorial :=
  Nat.factorial_dvd_factorial hk

/-- Each term of `N! · b^N · P_N(a/b)` is an integer.
`N! · b^N · C(2N-k,N)/k! · (-a/b)^k = (N!/k!) · C(2N-k,N) · (-a)^k · b^{N-k}` -/
private theorem padeP_term_clears (a : ℤ) (b : ℕ) (hb : 0 < b) (N k : ℕ) (hk : k ≤ N) :
    ∃ A : ℤ, (N.factorial : ℝ) * (b : ℝ) ^ N *
      (padeCoeff N k * (-(a : ℝ) / (b : ℝ)) ^ k) = (A : ℝ) := by
  unfold padeCoeff
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hk
  refine ⟨(c : ℤ) * ↑(Nat.choose (2 * N - k) N) * (-1) ^ k * a ^ k * ↑b ^ (N - k), ?_⟩
  have hb_ne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Reduce to: N! * b^N * (C/k! * (-a/b)^k) = c * C * (-1)^k * a^k * b^(N-k)
  -- Equivalently: N! * C * (-a)^k * b^N = c * C * (-a)^k * b^(N-k) * k! * b^k
  -- which follows from N! = k! * c and b^N = b^(N-k) * b^k
  -- After unfold, goal is:
  -- N! * b^N * (C(2N-k,N) / k! * (-a/b)^k) = ↑(c * C * (-1)^k * a^k * b^(N-k))
  -- We prove this by showing LHS = c * C * (-1)^k * a^k * b^(N-k) using:
  -- N! = k! * c and b^N = b^k * b^(N-k)
  have hfac_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hbk_ne : (b : ℝ) ^ k ≠ 0 := pow_ne_zero _ hb_ne
  -- Rewrite (-a/b)^k
  rw [show (-(↑a : ℝ) / ↑b) ^ k = (-1) ^ k * (↑a : ℝ) ^ k / (↑b : ℝ) ^ k from by
    rw [show -(↑a : ℝ) / ↑b = (-1) * (↑a / ↑b) from by ring, mul_pow, div_pow, mul_div_assoc]]
  -- Goal: N! * b^N * (C * ((-1)^k * a^k / b^k) / k!) = ...
  -- Rewrite N! using hc
  rw [show (↑N.factorial : ℝ) = (↑k.factorial : ℝ) * (↑c : ℝ) from by exact_mod_cast hc]
  -- Rewrite b^N
  rw [show (↑b : ℝ) ^ N = (↑b : ℝ) ^ k * (↑b : ℝ) ^ (N - k) from by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hk]]
  -- Now: (k!*c) * (b^k * b^(N-k)) * (C * ((-1)^k * a^k / b^k) / k!) = ...
  -- Cancel k! and b^k
  push_cast
  field_simp

/-- A sum of reals that are all integers is an integer. -/
private theorem sum_int_of_terms_int {s : Finset ℕ} {f : ℕ → ℝ}
    (h : ∀ k ∈ s, ∃ A : ℤ, f k = (A : ℝ)) :
    ∃ A : ℤ, ∑ k ∈ s, f k = (A : ℝ) := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a s hna ih =>
    rw [Finset.sum_insert hna]
    obtain ⟨A₁, hA₁⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    obtain ⟨A₂, hA₂⟩ := h _ (Finset.mem_insert_self _ _)
    exact ⟨A₂ + A₁, by push_cast; linarith⟩

/-- `N! · b^N · P_N(a/b)` is an integer. -/
theorem padeP_clears (a : ℤ) (b : ℕ) (hb : 0 < b) (N : ℕ) :
    ∃ A : ℤ, (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N ((a : ℝ) / (b : ℝ)) = (A : ℝ) := by
  simp only [padeP, mul_sum]
  apply sum_int_of_terms_int
  intro k hk
  have hk_le : k ≤ N := by simp [Finset.mem_range] at hk; omega
  convert padeP_term_clears a b hb N k hk_le using 2
  ring_nf

/-- Each term of `N! · b^N · Q_N(a/b)` is an integer.
Same argument as `padeP_term_clears` but with `x^k` instead of `(-x)^k`. -/
private theorem padeQ_term_clears (a : ℤ) (b : ℕ) (hb : 0 < b) (N k : ℕ) (hk : k ≤ N) :
    ∃ A : ℤ, (N.factorial : ℝ) * (b : ℝ) ^ N *
      (padeCoeff N k * ((a : ℝ) / (b : ℝ)) ^ k) = (A : ℝ) := by
  -- Same as padeP_term_clears but with a instead of -a
  have h := padeP_term_clears (-a) b hb N k hk
  simp only [Int.cast_neg, neg_neg] at h
  exact h

/-- `N! · b^N · Q_N(a/b)` is an integer. -/
theorem padeQ_clears (a : ℤ) (b : ℕ) (hb : 0 < b) (N : ℕ) :
    ∃ A : ℤ, (N.factorial : ℝ) * (b : ℝ) ^ N * padeQ N ((a : ℝ) / (b : ℝ)) = (A : ℝ) := by
  simp only [padeQ, mul_sum]
  apply sum_int_of_terms_int
  intro k hk
  have hk_le : k ≤ N := by simp [Finset.mem_range] at hk; omega
  exact padeQ_term_clears a b hb N k hk_le

/-! ## Padé condition: coefficient vanishing

The key identity: the "formal product" `P_N(x)·exp(x) - Q_N(x)` has its first
`2N+1` Taylor coefficients vanish. More precisely, if we expand
`P_N(x)·exp(x) = Σ_j (Σ_{k=0}^{min(j,N)} c(N,k)·(-1)^k/(j-k)!) · x^j`
then the coefficient of `x^j` matches that of `Q_N(x)` for `j ≤ 2N`.

This follows from `alternating_choose_sum` (for `j ≤ N`) and
`alternating_choose_sum_zero` (for `N < j ≤ 2N`).

### Helper: pade_coeff_product
For `j ≤ 2N`, the coefficient of `x^j` in `P_N(x)·exp(x)` is
`(1/j!) · Σ_{k=0}^{min(j,N)} (-1)^k · C(j,k) · C(2N-k, N)`.
This uses `1/(k!·(j-k)!) = C(j,k)/j!`.

### Helper: pade_condition_le (j ≤ N)
By `alternating_choose_sum` with `M = 2N, n = N`:
`Σ_{k=0}^j (-1)^k C(j,k) C(2N-k,N) = C(2N-j, N-j) = C(2N-j, N)`.
So the coefficient is `C(2N-j,N)/j!`, which matches `Q_N`'s coefficient. ✓

### Helper: pade_condition_gt (N < j ≤ 2N)
Extend the sum to `k=0..j` (extra terms have `C(2N-k,N) = 0` since `2N-k < N`).
By `alternating_choose_sum_zero` with `M = 2N, n = N, j > N`:
the sum is 0. And `Q_N` has no `x^j` term for `j > N`. ✓

### Helper: padeR_as_tail_sum
Since the first 2N+1 coefficients vanish:
`R_N(x) = Σ_{j≥2N+1} c_j · x^j` where `c_j = (1/j!) · Σ_{k=0}^N (-1)^k C(j,k) C(2N-k,N)`.

### Helper: padeR_coeff_bound
`|c_j| ≤ C(2N,N) · 2^j / j!` (since `C(2N-k,N) ≤ C(2N,N)` and `Σ_{k=0}^N C(j,k) ≤ 2^j`).
Combined with `C(2N,N) ≤ 4^N`:
`|c_j| ≤ 4^N · 2^j / j!`.
-/

/-! ## Remainder bound

Strategy: use the integral representation of the Padé remainder.

`R_N(x) = (-1)^N · x^{2N+1} / (N!)² · ∫₀¹ t^N·(1-t)^N · exp(t·x) dt`

Then `|R_N(x)| ≤ |x|^{2N+1} / (N!)² · ∫₀¹ t^N·(1-t)^N · exp(|x|) dt`
               `= |x|^{2N+1} · exp(|x|) / (N!)² · B(N+1, N+1)`
               `= |x|^{2N+1} · exp(|x|) / (N!)² · N!² / (2N+1)!`
               `= |x|^{2N+1} · exp(|x|) / (2N+1)!`

where `B(N+1,N+1) = N!²/(2N+1)!` is the Beta integral.

However, proving the integral representation requires substantial setup.
A simpler approach: use the tail-sum bound from the Padé condition.

From `padeR_as_tail_sum`:
`|R_N(x)| ≤ Σ_{j≥2N+1} |c_j| · |x|^j ≤ Σ_{j≥2N+1} C(2N,N) · (2|x|)^j / j!`
         `≤ C(2N,N) · (2|x|)^{2N+1} / (2N+1)! · Σ_{i≥0} (2|x|)^i / ((2N+2)·...·(2N+1+i))`
         `≤ C(2N,N) · (2|x|)^{2N+1} / (2N+1)! · exp(2|x|)`

And `C(2N,N) ≤ 4^N ≤ 4^N`. So: `|R_N(x)| ≤ 4^N · (2|x|)^{2N+1} · exp(2|x|) / (2N+1)!`.

Since `(2N+1)! = (2N+1) · (2N)! ≥ (2N+1) · (N!)²` (by `C(2N,N) = (2N)!/(N!)² ≥ 1`),
we get `|R_N(x)| ≤ 4^N · (2|x|)^{2N+1} · exp(2|x|) / ((2N+1) · (N!)²)`.

And `4^N · (2|x|)^{2N+1} = (2|x|)^{2N+1} · 4^N ≤ (2|x|)^{2N+1} · 2 · 4^N`... hmm.

Actually let's use the cleaner bound directly:

**Approach**: Prove `|R_N(x)| ≤ |x|^{2N+1} · exp(|x|) / ((2N+1) · (N!)²)`

via the Padé condition. Needs:

**HELPER THEOREM `pade_taylor_coeff_vanish`** (separate lemma, ~50 lines):
  For `j ≤ 2N`, the formal Taylor coefficient of `P_N·exp - Q_N` at order `j` is 0.
  Uses `alternating_choose_sum` and `alternating_choose_sum_zero`.

**HELPER THEOREM `pade_tail_coeff_bound`** (separate lemma, ~20 lines):
  For `j ≥ 2N+1`, `|c_j| ≤ C(2N,N)/j!`.
  Uses `|Σ_{k=0}^N (-1)^k C(j,k) C(2N-k,N)| ≤ Σ C(j,k) C(2N,N) = C(2N,N) · Σ C(j,k)`
  and `Σ_{k=0}^N C(j,k) ≤ 2^j ≤ ...`. Actually simpler:
  `|Σ (...)| ≤ Σ C(j,k) · C(2N-k,N) ≤ Σ C(j,k) · C(2N,N) = C(2N,N) · 2^j`... no.
  Better: `|c_j| ≤ (1/j!) · Σ_{k=0}^N C(j,k) · C(2N-k,N) ≤ C(2N,N)·(N+1)/j!`
  since `Σ_{k=0}^N C(j,k) ≤ Σ_{k=0}^j C(j,k) = 2^j` but that's too loose.
  Actually for the tail: `Σ_{k=0}^N 1 = N+1` and `C(j,k) ≤ j^N/N!` ... also messy.
  Simplest: `C(2N-k,N) ≤ C(2N,N)` and each term is `≤ C(j,k)·C(2N,N)`.
  Then `Σ_{k=0}^N C(j,k) ≤ 2^j`. So `|c_j| ≤ C(2N,N)·2^j/j!`.

**HELPER THEOREM `exp_tail_sum_bound`** (separate lemma, ~30 lines):
  `Σ_{j≥M} a^j/j! ≤ a^M/M! · exp(a)` for `a ≥ 0`.
  Proof: `Σ_{j≥M} a^j/j! = a^M/M! · Σ_{i≥0} a^i·M!/(M+i)! ≤ a^M/M! · Σ a^i/i! = a^M/M!·exp(a)`.
  The inequality `M!/(M+i)! ≤ 1/i!` holds since `(M+1)···(M+i) ≥ 1·2···i = i!`.
  Needs HasSum for exp. Mathlib has `Real.hasSum_exp`.

**HELPER THEOREM `central_binom_le_four_pow`** (~5 lines):
  `C(2N,N) ≤ 4^N`. Standard, might be in Mathlib.

**HELPER THEOREM `two_N_factorial_ge`** (~10 lines):
  `(2N+1)! ≥ (2N+1) · (N!)²`. From `C(2N,N) ≥ 1`, i.e., `(2N)! ≥ (N!)²`.

Then assembling: `|R_N(x)| ≤ C(2N,N) · Σ_{j≥2N+1} (2|x|)^j/j!`
  `≤ C(2N,N) · (2|x|)^{2N+1}/(2N+1)! · exp(2|x|)`
  `≤ 4^N · (2|x|)^{2N+1} · exp(2|x|) / (2N+1)!`
  `≤ 4^N · (2|x|)^{2N+1} · exp(2|x|) / ((2N+1) · (N!)²)`

And then `4^N · (2|x|)^{2N+1} = 2^{2N} · 2^{2N+1} · |x|^{2N+1} = 2^{4N+1} · |x|^{2N+1}`
while the stated bound has `(2|x|)^{2N+1} · 2 / (N!)²`.
`(2|x|)^{2N+1} · 2 = 2^{2N+2} · |x|^{2N+1}`.

Hmm these don't match. Let me re-derive.

**CLEAN STATEMENT**: Use `|R_N(x)| ≤ |x|^{2N+1} · exp(|x|) / ((2N+1) · (N!)²)`.

This is the TIGHT bound from the integral representation. Much cleaner.
Provable from tail sum approach if we're careful:
- Tail sum: Σ_{j≥2N+1} |c_j|·|x|^j
- Better coeff bound: from the integral representation, `|c_j| ≤ 1/(j! · (N!)²) · (N!)²·j!/((2N+1)!·(j-2N-1)!)` ... this is getting circular.

Let me just use the simpler (looser) bound and adjust the statement.
-/

/-! ### Padé condition: Taylor coefficient vanishing

We show the j-th coefficient of the Cauchy product `P_N · exp` equals `padeCoeff N j`
for `j ≤ N`, and vanishes for `N < j ≤ 2N`. -/

/-- The j-th Cauchy product coefficient of `P_N · exp`:
`(1/j!) · Σ_{k=0}^{min(j,N)} (-1)^k C(j,k) C(2N-k,N)`. -/
private noncomputable def padeProdCoeff (N j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (min j N + 1),
    padeCoeff N k * (-1 : ℝ) ^ k / ((j - k).factorial : ℝ)

/-- For j ≤ N, the Cauchy product coefficient equals the Q_N coefficient (Padé condition). -/
private theorem padeProdCoeff_eq_low (N j : ℕ) (hN : 0 < N) (hj : j ≤ N) :
    padeProdCoeff N j = padeCoeff N j := by
  simp only [padeProdCoeff, show min j N = j from by omega]
  have hj_fac_ne : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos j).ne'
  -- Suffices: both sides * j! are equal
  rw [show padeCoeff N j = ((2 * N - j).choose N : ℝ) / j.factorial from rfl]
  rw [eq_div_iff hj_fac_ne, Finset.sum_mul]
  -- Use alternating_choose_sum: Σ (-1)^k C(j,k) C(2N-k,N) = C(2N-j, N-j)
  have key := alternating_choose_sum (2 * N) N j hj (by omega)
  -- Convert the ℤ sum to ℝ
  suffices hgoal : ∑ k ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ k * (j.choose k : ℝ) * ((2 * N - k).choose N : ℝ) =
      ((2 * N - j).choose N : ℝ) by
    -- Show our sum (with padeCoeff) equals this sum
    have hsame : ∀ k ∈ Finset.range (j + 1),
        padeCoeff N k * (-1 : ℝ) ^ k / ((j - k).factorial : ℝ) * j.factorial =
        (-1 : ℝ) ^ k * (j.choose k : ℝ) * ((2 * N - k).choose N : ℝ) := by
      intro k hk; simp only [Finset.mem_range] at hk; simp only [padeCoeff]
      have hfac_nat := Nat.choose_mul_factorial_mul_factorial (show k ≤ j by omega)
      have : (j.factorial : ℝ) = (j.choose k : ℝ) * k.factorial * (j - k).factorial := by
        exact_mod_cast hfac_nat.symm
      field_simp; rw [this]; ring
    rw [Finset.sum_congr rfl hsame]; exact hgoal
  -- Cast from ℤ and use Nat.choose_symm
  have hchoose : (2 * N - j).choose (N - j) = (2 * N - j).choose N := by
    have h1 : N ≤ 2 * N - j := by omega
    have h2 : (2 * N - j) - N = N - j := by omega
    rw [← h2]; exact Nat.choose_symm h1
  rw [← hchoose]
  exact_mod_cast key

/-- For `N < j ≤ 2N`, the Cauchy product coefficient vanishes (Padé condition). -/
private theorem padeProdCoeff_eq_zero (N j : ℕ) (hjN : N < j) (hj2N : j ≤ 2 * N) :
    padeProdCoeff N j = 0 := by
  simp only [padeProdCoeff, show min j N = N from by omega]
  -- The sum is Σ_{k=0}^N C(2N-k,N)/(k!) · (-1)^k / (j-k)!
  -- = (1/j!) · Σ_{k=0}^N (-1)^k C(j,k) C(2N-k,N)
  -- Extend to Σ_{k=0}^j: for k > N, C(2N-k,N) = 0 (since 2N-k < N).
  -- By alternating_choose_sum_zero (M=2N, n=N, j > N): sum = 0.
  have hj_fac_ne : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos j).ne'
  -- Suffices: sum * j! = 0 (then divide by j!)
  suffices h : (∑ k ∈ Finset.range (N + 1),
      padeCoeff N k * (-1 : ℝ) ^ k / ((j - k).factorial : ℝ)) * j.factorial = 0 by
    have := mul_eq_zero.mp h; exact this.elim id (fun h => absurd h hj_fac_ne)
  -- Factor each summand * j! = (-1)^k * C(j,k) * C(2N-k,N)
  rw [Finset.sum_mul]
  have hfactor : ∀ k ∈ Finset.range (N + 1),
      padeCoeff N k * (-1 : ℝ) ^ k / ((j - k).factorial : ℝ) * j.factorial =
      (-1 : ℝ) ^ k * (j.choose k : ℝ) * ((2 * N - k).choose N : ℝ) := by
    intro k hk; simp only [Finset.mem_range] at hk; simp only [padeCoeff]
    have hfac_nat := Nat.choose_mul_factorial_mul_factorial (show k ≤ j by omega)
    have : (j.factorial : ℝ) = (j.choose k : ℝ) * k.factorial * (j - k).factorial := by
      exact_mod_cast hfac_nat.symm
    field_simp; rw [this]; ring
  rw [Finset.sum_congr rfl hfactor]
  -- Extend Σ_{k=0}^N to Σ_{k=0}^j: for k > N, C(2N-k,N) = 0
  have hext : ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * (j.choose k : ℝ) *
      ((2 * N - k).choose N : ℝ) =
      ∑ k ∈ Finset.range (j + 1), (-1 : ℝ) ^ k * (j.choose k : ℝ) *
      ((2 * N - k).choose N : ℝ) := by
    exact Finset.sum_subset (Finset.range_mono (show N + 1 ≤ j + 1 by omega)) (by
      intro k hk1 hk2
      simp only [Finset.mem_range, not_lt] at hk2
      rw [show (2 * N - k).choose N = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      simp)
  rw [hext]
  -- Use alternating_choose_sum_zero
  have key := alternating_choose_sum_zero (2 * N) N j hjN (by omega)
  have : ∑ k ∈ Finset.range (j + 1), (-1 : ℝ) ^ k * (j.choose k : ℝ) *
      ((2 * N - k).choose N : ℝ) = (0 : ℝ) := by exact_mod_cast key
  rw [this]

/-! ### Helper lemmas for `padeR_bound` -/

/-- Coefficient bound: `|padeProdCoeff N j| ≤ C(2N,N) · 2^j / j!`.
Each term in the sum has `|(-1)^k C(j,k) C(2N-k,N)| ≤ C(j,k)·C(2N,N)`,
and `Σ_{k=0}^N C(j,k) ≤ 2^j`. -/
private theorem padeProdCoeff_abs_le (N j : ℕ) :
    |padeProdCoeff N j| ≤ (Nat.centralBinom N : ℝ) * 2 ^ j / j.factorial := by
  unfold padeProdCoeff
  -- Step 1: Triangle inequality, simplify |(-1)^k| = 1
  have habs : ∀ k ∈ Finset.range (min j N + 1),
      |padeCoeff N k * (-1 : ℝ) ^ k / ((j - k).factorial : ℝ)| =
      padeCoeff N k / ((j - k).factorial : ℝ) := by
    intro k hk; simp only [Finset.mem_range] at hk
    have hkN : k ≤ N := by omega
    rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt (padeCoeff_pos N k hkN)),
        abs_pow, abs_neg, abs_one, one_pow, mul_one,
        abs_of_nonneg (Nat.cast_nonneg' _)]
  -- Step 2: |sum| ≤ Σ |term| = Σ C(2N-k,N)/(k! · (j-k)!)
  have h1 : |∑ k ∈ Finset.range (min j N + 1),
      padeCoeff N k * (-1 : ℝ) ^ k / ((j - k).factorial : ℝ)| ≤
      ∑ k ∈ Finset.range (min j N + 1), padeCoeff N k / ((j - k).factorial : ℝ) := by
    calc _ ≤ ∑ k ∈ Finset.range (min j N + 1),
          |padeCoeff N k * (-1 : ℝ) ^ k / ((j - k).factorial : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_congr rfl habs
  -- Step 3: Bound C(2N-k,N) ≤ C(2N,N) and rewrite using C(j,k) = j!/(k!·(j-k)!)
  have h2 : ∑ k ∈ Finset.range (min j N + 1), padeCoeff N k / ((j - k).factorial : ℝ) ≤
      (Nat.centralBinom N : ℝ) / (j.factorial : ℝ) *
      ∑ k ∈ Finset.range (min j N + 1), (j.choose k : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k hk; simp only [Finset.mem_range] at hk
    have hkN : k ≤ N := by omega
    have hkj : k ≤ j := by omega
    -- LHS = C(2N-k,N) / (k! · (j-k)!)
    -- RHS = C(2N,N) / j! · C(j,k) = C(2N,N) · C(j,k) / j!
    --     = C(2N,N) / (k! · (j-k)!)  (since C(j,k) · (j-k)! · k! = j!)
    simp only [padeCoeff, Nat.centralBinom_eq_two_mul_choose, div_div]
    -- Goal: C(2N-k,N) / (k! * (j-k)!) ≤ C(2N,N) / j! * C(j,k)
    -- Rewrite RHS: C(2N,N) * C(j,k) / j! = C(2N,N) / (k! * (j-k)!)
    have hchoose_fac := Nat.choose_mul_factorial_mul_factorial hkj
    -- hchoose_fac : C(j,k) * k! * (j-k)! = j!
    have hRHS : (↑((2 * N).choose N) : ℝ) / ↑j.factorial * ↑(j.choose k) =
        (↑((2 * N).choose N) : ℝ) / (↑k.factorial * ↑(j - k).factorial) := by
      have : (j.factorial : ℝ) = (j.choose k : ℝ) * k.factorial * (j - k).factorial := by
        exact_mod_cast hchoose_fac.symm
      rw [this]
      have : (j.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hkj).ne'
      field_simp
    rw [hRHS]
    apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _))
    exact_mod_cast Nat.choose_le_choose N (by omega : 2 * N - k ≤ 2 * N)
  -- Step 4: Extend sum from range(min j N + 1) to range(j + 1) and use Σ C(j,k) = 2^j
  have h3 : (Nat.centralBinom N : ℝ) / (j.factorial : ℝ) *
      ∑ k ∈ Finset.range (min j N + 1), (j.choose k : ℝ) ≤
      (Nat.centralBinom N : ℝ) * 2 ^ j / (j.factorial : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg' j.factorial)
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ Nat.centralBinom N)
    have hsub : Finset.range (min j N + 1) ⊆ Finset.range (j + 1) :=
      Finset.range_mono (by omega)
    calc (∑ k ∈ Finset.range (min j N + 1), (j.choose k : ℝ))
        ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg' _)
      _ = 2 ^ j := by
          have := Nat.sum_range_choose j
          exact_mod_cast this
  linarith [h1, h2, h3]

/-- The Cauchy product `P_N(x) · exp(x)` equals `∑ padeProdCoeff(N,n) · x^n`. -/
private theorem padeP_mul_exp_hasSum (N : ℕ) (x : ℝ) :
    HasSum (fun n => padeProdCoeff N n * x ^ n) (padeP N x * exp x) := by
  -- Extended P coefficients: padeCoeff N k * (-1)^k * x^k for k ≤ N, else 0
  set fP : ℕ → ℝ := fun k => if k ≤ N then padeCoeff N k * (-1) ^ k * x ^ k else 0
  -- Exp series coefficients
  set fE : ℕ → ℝ := fun j => x ^ j / ↑j.factorial
  -- fP is norm-summable (finitely supported)
  have hfP_ns : Summable (fun k => ‖fP k‖) := by
    apply summable_of_ne_finset_zero (s := range (N + 1))
    intro b hb; simp only [Finset.mem_range, not_lt] at hb
    simp only [fP, show ¬(b ≤ N) from by omega, ite_false, norm_zero]
  -- fE is norm-summable (absolute convergence of exp)
  have hfE_ns : Summable (fun j => ‖fE j‖) :=
    NormedSpace.norm_expSeries_div_summable (𝕂 := ℝ) x
  -- Cauchy product HasSum
  have hCP := hasSum_sum_range_mul_of_summable_norm hfP_ns hfE_ns
  -- Compute tsum of fP = padeP N x
  have hfP_tsum : ∑' k, fP k = padeP N x := by
    rw [tsum_eq_sum (s := range (N + 1)) (hf := fun b hb => by
      simp only [fP, Finset.mem_range, not_lt] at hb ⊢
      simp [show ¬(b ≤ N) from by omega])]
    simp only [padeP]
    apply Finset.sum_congr rfl; intro k hk
    simp only [Finset.mem_range] at hk
    simp only [fP, show k ≤ N from by omega, ite_true]
    rw [show (-x) ^ k = (-1 : ℝ) ^ k * x ^ k from by
      rw [show (-x : ℝ) = (-1) * x from by ring, mul_pow]]
    ring
  -- Compute tsum of fE = exp x
  have hfE_tsum : ∑' j, fE j = exp x := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (𝕂 := ℝ) x).tsum_eq
  rw [hfP_tsum, hfE_tsum] at hCP
  -- Show each Cauchy coefficient = padeProdCoeff N n * x^n
  have hcoeff : ∀ n : ℕ, padeProdCoeff N n * x ^ n =
      ∑ k ∈ range (n + 1), fP k * fE (n - k) := by
    intro n
    -- Reduce sum: for k > min n N, fP k = 0 (since k > N or vacuously k > n)
    rw [(Finset.sum_subset (Finset.range_mono (show min n N + 1 ≤ n + 1 by omega))
      (fun k hk1 hk2 => by
        simp only [Finset.mem_range, not_lt] at hk1 hk2
        have hkN : ¬(k ≤ N) := by
          intro h; exact absurd (show k < min n N + 1 from by omega) (not_lt.mpr hk2)
        simp only [fP, hkN, ite_false, zero_mul])).symm]
    -- Match with padeProdCoeff definition
    simp only [padeProdCoeff, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k hk
    simp only [Finset.mem_range] at hk
    have hkN : k ≤ N := by omega
    have hkn : k ≤ n := by omega
    simp only [fP, hkN, ite_true, fE, padeCoeff]
    have hpow : x ^ k * x ^ (n - k) = x ^ n := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    have hkf_ne : (↑k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hnkf_ne : (↑(n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    rw [mul_assoc, hpow]
  rw [show (fun n => ∑ k ∈ range (n + 1), fP k * fE (n - k)) =
      fun n => padeProdCoeff N n * x ^ n from funext (fun n => (hcoeff n).symm)] at hCP
  exact hCP

/-- `Q_N(x)` equals the first `2N+1` terms of the Cauchy product series. -/
private theorem padeQ_eq_sum_padeProdCoeff (N : ℕ) (hN : 0 < N) (x : ℝ) :
    ∑ n ∈ range (2 * N + 1), padeProdCoeff N n * x ^ n = padeQ N x := by
  -- Split range(2N+1) into range(N+1) ∪ {N+1,...,2N}
  rw [show 2 * N + 1 = (N + 1) + N from by omega, Finset.sum_range_add]
  -- Second sum vanishes (padeProdCoeff = 0 for N < j ≤ 2N)
  have h2 : ∑ i ∈ range N, padeProdCoeff N (N + 1 + i) * x ^ (N + 1 + i) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_range] at hi
    rw [padeProdCoeff_eq_zero N (N + 1 + i) (by omega) (by omega), zero_mul]
  rw [h2, add_zero]
  -- First sum: padeProdCoeff = padeCoeff for j ≤ N
  simp only [padeQ]
  apply Finset.sum_congr rfl; intro n hn
  simp only [Finset.mem_range] at hn
  rw [padeProdCoeff_eq_low N n hN (by omega)]

/-- `R_N(x) = Σ_{j≥2N+1} padeProdCoeff(N, j) · x^j` as a convergent series.
The first 2N+1 terms of the Cauchy product `P_N·exp` cancel with `Q_N`. -/
private theorem padeR_hasSum (N : ℕ) (hN : 0 < N) (x : ℝ) :
    HasSum (fun j => padeProdCoeff N (j + (2 * N + 1)) * x ^ (j + (2 * N + 1)))
      (padeR N x) := by
  have h1 : HasSum (fun n => padeProdCoeff N n * x ^ n) (padeP N x * exp x) :=
    padeP_mul_exp_hasSum N x
  have h2 : ∑ n ∈ range (2 * N + 1), padeProdCoeff N n * x ^ n = padeQ N x :=
    padeQ_eq_sum_padeProdCoeff N hN x
  -- padeR = padeP * exp x - padeQ = (total series value) - (first 2N+1 terms)
  rw [show padeR N x = padeP N x * exp x -
      ∑ n ∈ range (2 * N + 1), padeProdCoeff N n * x ^ n from by
    unfold padeR; linarith [h2]]
  exact (hasSum_nat_add_iff' (2 * N + 1)).mpr h1

/-- Exp tail bound: `Σ_{j≥M} a^j/j! ≤ a^M/M! · exp(a)` for `a ≥ 0`. -/
private theorem exp_tail_le (a : ℝ) (ha : 0 ≤ a) (M : ℕ) :
    ∑' j, a ^ (j + M) / (j + M).factorial ≤ a ^ M / M.factorial * exp a := by
  -- Each term: a^(j+M)/(j+M)! ≤ a^M/M! · a^j/j!  (since M!·j! ≤ (j+M)!)
  -- Sum RHS: a^M/M! · Σ a^j/j! = a^M/M! · exp(a)
  have hexp := NormedSpace.expSeries_div_hasSum_exp (𝕂 := ℝ) a
  rw [Real.exp_eq_exp_ℝ, hexp.tsum_eq.symm, ← tsum_mul_left]
  -- Summability of LHS: it's bounded termwise by a summable series
  have hsumR : Summable (fun j => a ^ M / M.factorial * (a ^ j / j.factorial)) :=
    hexp.summable.mul_left _
  have hle : ∀ j, a ^ (j + M) / (j + M).factorial ≤
      a ^ M / M.factorial * (a ^ j / j.factorial) := fun j => by
    rw [div_mul_div_comm, pow_add, mul_comm (a ^ j) (a ^ M)]
    apply div_le_div_of_nonneg_left (by positivity : 0 ≤ a ^ M * a ^ j)
      (by positivity : (0 : ℝ) < (M.factorial : ℝ) * (j.factorial : ℝ))
    rw [← Nat.cast_mul]
    exact (Nat.cast_le (α := ℝ)).mpr (Nat.le_of_dvd (Nat.factorial_pos _)
      (add_comm j M ▸ Nat.factorial_mul_factorial_dvd_factorial_add M j))
  have hsumL : Summable (fun j => a ^ (j + M) / (j + M).factorial) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle hsumR
  exact hsumL.tsum_le_tsum hle hsumR

/-- `C(2N,N) / (2N+1)! = 1 / ((2N+1) · (N!)²)` -/
private theorem centralBinom_div_factorial (N : ℕ) (hN : 0 < N) :
    (Nat.centralBinom N : ℝ) / ((2 * N + 1).factorial : ℝ) =
    1 / ((2 * N + 1 : ℕ) * ((N.factorial : ℝ) ^ 2)) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have key := Nat.choose_mul_factorial_mul_factorial (show N ≤ 2 * N by omega)
  rw [show 2 * N - N = N from by omega] at key
  -- key : C(2N,N) * N! * N! = (2N)!
  -- Cross-multiply: C(2N,N) * ((2N+1) * (N!)²) = 1 * (2N+1)!
  rw [div_eq_div_iff
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (by apply mul_ne_zero
        · exact Nat.cast_ne_zero.mpr (by omega)
        · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))]
  -- Goal: C(2N,N) * ((2N+1) * (N!)²) = 1 * (2N+1)!
  have h2N1fac : (2 * N + 1).factorial = (2 * N + 1) * (2 * N).factorial :=
    Nat.mul_factorial_pred (by omega)
  have keyR : ((2 * N).choose N : ℝ) * (N.factorial : ℝ) * (N.factorial : ℝ) =
      ((2 * N).factorial : ℝ) := by exact_mod_cast key
  push_cast [h2N1fac, sq]
  nlinarith [keyR]

/-- The Padé remainder is bounded:
`|R_N(x)| ≤ (2|x|)^{2N+1} · 2·exp(2|x|) / ((2N+1) · (N!)²)` -/
theorem padeR_bound (N : ℕ) (hN : 0 < N) (x : ℝ) :
    |padeR N x| ≤ (2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|)) /
      ((2 * N + 1 : ℕ) * ((N.factorial : ℝ) ^ 2)) := by
  set M := 2 * N + 1
  set a := 2 * |x| with ha_def
  have ha : 0 ≤ a := by positivity
  have hhs := padeR_hasSum N hN x
  -- Exp tail summability
  have htail_sum : Summable (fun j => a ^ (j + M) / ↑(j + M).factorial) :=
    (NormedSpace.expSeries_div_summable (𝕂 := ℝ) a).comp_injective
      (add_left_injective M)
  -- Pointwise bound: |padeProdCoeff(j+M) · x^(j+M)| ≤ C(2N,N) · a^(j+M)/(j+M)!
  have hpw : ∀ j, |padeProdCoeff N (j + M) * x ^ (j + M)| ≤
      (Nat.centralBinom N : ℝ) * (a ^ (j + M) / ↑(j + M).factorial) := by
    intro j; rw [abs_mul, abs_pow]
    calc |padeProdCoeff N (j + M)| * |x| ^ (j + M)
        ≤ (↑(Nat.centralBinom N) * 2 ^ (j + M) / ↑(j + M).factorial) *
          |x| ^ (j + M) :=
          mul_le_mul_of_nonneg_right (padeProdCoeff_abs_le N _) (pow_nonneg (abs_nonneg _) _)
      _ = ↑(Nat.centralBinom N) * (a ^ (j + M) / ↑(j + M).factorial) := by
          simp only [ha_def, mul_pow]; ring
  -- Summability of |f|
  have hf_ns : Summable (fun j => ‖padeProdCoeff N (j + M) * x ^ (j + M)‖) := by
    rw [show (fun j => ‖padeProdCoeff N (j + M) * x ^ (j + M)‖) =
        (fun j => |padeProdCoeff N (j + M) * x ^ (j + M)|) from by ext; exact Real.norm_eq_abs _]
    exact Summable.of_nonneg_of_le (fun j => abs_nonneg _) hpw (htail_sum.mul_left _)
  -- Denominator is positive
  have hD : (0 : ℝ) < ↑(M : ℕ) * ((N.factorial : ℝ) ^ 2) := by positivity
  -- Chain of inequalities
  calc |padeR N x|
      = ‖padeR N x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖padeProdCoeff N (j + M) * x ^ (j + M)‖ := by
        rw [← hhs.tsum_eq]; exact norm_tsum_le_tsum_norm hf_ns
    _ ≤ ∑' j, ↑(Nat.centralBinom N) * (a ^ (j + M) / ↑(j + M).factorial) :=
        hf_ns.tsum_le_tsum (fun j => by rw [Real.norm_eq_abs]; exact hpw j)
          (htail_sum.mul_left _)
    _ = ↑(Nat.centralBinom N) * ∑' j, a ^ (j + M) / ↑(j + M).factorial := tsum_mul_left ..
    _ ≤ ↑(Nat.centralBinom N) * (a ^ M / ↑M.factorial * exp a) :=
        mul_le_mul_of_nonneg_left (exp_tail_le a ha M) (Nat.cast_nonneg' _)
    _ = a ^ M * exp a / (↑(M : ℕ) * ((N.factorial : ℝ) ^ 2)) := by
        have hcbf := centralBinom_div_factorial N hN
        have hF : (↑M.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        calc ↑(Nat.centralBinom N) * (a ^ M / ↑M.factorial * exp a)
            = (↑(Nat.centralBinom N) / ↑M.factorial) * a ^ M * exp a := by
                field_simp [hF]
          _ = (1 / (↑(M : ℕ) * (N.factorial : ℝ) ^ 2)) * a ^ M * exp a := by rw [hcbf]
          _ = a ^ M * exp a / (↑(M : ℕ) * ((N.factorial : ℝ) ^ 2)) := by
                field_simp [ne_of_gt hD]
    _ ≤ a ^ M * (2 * exp a) / (↑(M : ℕ) * ((N.factorial : ℝ) ^ 2)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith [exp_pos a]) (pow_nonneg ha _)) hD.le

/-! ## Positivity of Padé polynomials at rational points

Key facts for the irrationality argument:
- `Q_N(x) > 0` for `x > 0` (all terms positive)
- `P_N(x) > 0` for `x < 0` (all terms `C·|x|^k/k! > 0`)

These ensure the integer `K_N = N!·b^N·P_N(a/b)` or `J_N = N!·b^N·Q_N(a/b)`
is nonzero, which is needed for the irrationality contradiction. -/

/-- `Q_N(x) > 0` for `x > 0` and `N ≥ 1`. -/
theorem padeQ_pos (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : 0 < x) :
    0 < padeQ N x := by
  apply Finset.sum_pos
  · intro k hk
    have hk_le : k ≤ N := by simp [Finset.mem_range] at hk; omega
    exact mul_pos (padeCoeff_pos N k hk_le) (pow_pos hx k)
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

/-- `P_N(x) > 0` for `x < 0` and `N ≥ 1`. -/
theorem padeP_pos_of_neg (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : x < 0) :
    0 < padeP N x := by
  apply Finset.sum_pos
  · intro k hk
    have hk_le : k ≤ N := by simp [Finset.mem_range] at hk; omega
    exact mul_pos (padeCoeff_pos N k hk_le) (pow_pos (by linarith) k)
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

/-- `|P_N(x)| ≤ 4^N · exp(|x|)`.
Proof: |P_N(x)| ≤ Σ C(2N-k,N)/k! · |x|^k ≤ 4^N · Σ |x|^k/k! ≤ 4^N · exp(|x|). -/
theorem padeP_abs_le (N : ℕ) (x : ℝ) :
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
            _ ≤ (2 : ℝ) ^ (2 * N) := by linearize
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

/-! ## Non-vanishing of the Padé remainder

`R_N(q) ≠ 0` for nonzero rational `q` and `N ≥ 1`, by the irrationality of `exp(q)`.
If `R_N(q) = 0` then `exp(q) = Q_N(q)/P_N(q) ∈ ℚ`, contradiction. -/

/-- The Padé remainder `R_N(q) = P_N(q)·exp(q) - Q_N(q)` is nonzero for `q ∈ ℚ \ {0}`. -/
theorem padeR_ne_zero (N : ℕ) (hN : 0 < N) (q : ℚ) (hq : q ≠ 0) :
    padeR N (q : ℝ) ≠ 0 := by
  intro hR
  simp only [padeR] at hR
  have hPexp : padeP N (q : ℝ) * exp (q : ℝ) = padeQ N (q : ℝ) := by linarith
  by_cases hP : padeP N (q : ℝ) = 0
  · -- P_N(q) = 0 → Q_N(q) = 0, contradicts positivity
    rw [hP, zero_mul] at hPexp
    have hQ : padeQ N (q : ℝ) = 0 := hPexp.symm
    rcases (ne_iff_lt_or_gt.mp (show (q : ℝ) ≠ 0 from by exact_mod_cast hq)) with hlt | hgt
    · exact absurd hP (ne_of_gt (padeP_pos_of_neg N hN (q : ℝ) hlt))
    · exact absurd hQ (ne_of_gt (padeQ_pos N hN (q : ℝ) hgt))
  · -- P_N(q) ≠ 0 → exp(q) = Q_N(q)/P_N(q) ∈ ℚ, contradicts irrationality
    set a := q.num
    set b := q.den
    have hb : 0 < b := q.pos
    have hq_eq : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
      exact_mod_cast q.num_div_den.symm
    obtain ⟨K, hK⟩ := padeP_clears a b (by omega) N
    obtain ⟨J, hJ⟩ := padeQ_clears a b (by omega) N
    have hD_ne : (N.factorial : ℝ) * (b : ℝ) ^ N ≠ 0 := by positivity
    have hP' : padeP N ((a : ℝ) / (b : ℝ)) ≠ 0 := by rwa [hq_eq] at hP
    have hK_ne : (K : ℝ) ≠ 0 := by
      intro hK0
      have : (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N ((a : ℝ) / (b : ℝ)) = 0 := by
        rw [hK]; simp [hK0]
      exact mul_ne_zero hD_ne hP' this
    have hexp_rat : exp (q : ℝ) = (J : ℝ) / (K : ℝ) := by
      have hexp_qp : exp ((a : ℝ) / (b : ℝ)) =
          padeQ N ((a : ℝ) / (b : ℝ)) / padeP N ((a : ℝ) / (b : ℝ)) := by
        rw [← hq_eq]; field_simp; linarith
      rw [hq_eq, hexp_qp]
      have hQ_eq : padeQ N ((a : ℝ) / (b : ℝ)) =
          (J : ℝ) / ((N.factorial : ℝ) * (b : ℝ) ^ N) := by
        field_simp; linarith [hJ]
      have hP_eq : padeP N ((a : ℝ) / (b : ℝ)) =
          (K : ℝ) / ((N.factorial : ℝ) * (b : ℝ) ^ N) := by
        field_simp; linarith [hK]
      rw [hQ_eq, hP_eq]; field_simp
    have hirr := irrational_exp_rat q hq
    exact hirr.ne_rat (↑J / ↑K) (by push_cast; exact hexp_rat)

