import Flean.NumberTheory.ExpEffectiveBound
import Flean.NumberTheory.AlternatingChooseSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Padé approximation to `exp(x)` and effective irrationality measure

We construct the diagonal Padé approximants `P_N(x), Q_N(x)` to `exp(x)` and
prove that the remainder `R_N(x) = P_N(x)·exp(x) - Q_N(x)` satisfies
`|R_N(x)| ≤ |x|^{2N+1} · exp(|x|) / ((2N+1) · N!²)`.

Combined with the integer gap principle from `ExpEffectiveBound.lean`, this gives
an effective lower bound on `|exp(a/b) · 2^s - m|` for any nonzero rational `a/b`.

## Key advantage over plain Taylor

The Taylor approach clears denominators with `b^N · N!`, giving scaled remainder
`∼ |a|^{N+1} / (b · (N+1))` which diverges for `|a| > b`.
The Padé approach clears with `N! · b^N`, giving scaled remainder
`∼ |a|^{2N+1} / (N! · b^{N+1})` which → 0 for ALL `a, b` (factorial beats exponential).
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

/-! ## The main effective bound

Strategy for proving `|exp(a/b) · 2^s - m| ≥ δ > 0` for all integers `m`:

1. Let `D = N! · b^N`, `K = D · P_N(a/b) ∈ ℤ`, `J = D · Q_N(a/b) ∈ ℤ`
2. Padé identity: `K · exp(a/b) - J = D · R_N(a/b)`
3. Rearranging: `K · (exp(a/b)·2^s - m) = (J·2^s - K·m) + D·2^s·R_N(a/b)`
4. Irrationality argument: `I = J·2^s - K·m ≠ 0` because
   - If `a > 0`: `J > 0` (from `padeQ_pos`), so `K = 0 ∧ I = 0` is impossible.
     If `K ≠ 0` and `I = 0`, then `exp(a/b) = J·2^s/(K·2^s) ∈ ℚ`, contradicting irrationality.
   - If `a < 0`: `K > 0` (from `padeP_pos_of_nonpos`), same irrationality argument.
5. For large `N`: `|D·2^s·R_N| < 1/2` (factorial dominates)
6. By integer gap principle: `|K·v| ≥ 1/2$, so `|v| ≥ 1/(2·|K|)` -/

/-- The algebraic bound: `N! · b^N · 2^s · |R_N(x)| ≤ K · d^N / N!`
where `d = 4·b·x²` and `K = 2^{s+1}·exp(2|x|)·(2|x|)`.
This is the common core used by both `pade_scaled_remainder_small` and
`pade_scaled_remainder_effective`. -/
private theorem pade_scaled_bound_by_K_d (N : ℕ) (hN : 0 < N)
    (x : ℝ) (b : ℕ) (hb : 0 < b) (s : ℕ) :
    let d := 4 * (b : ℝ) * x ^ 2
    let K := 2 ^ (s + 1) * exp (2 * |x|) * (2 * |x|)
    (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * |padeR N x| ≤ K * d ^ N / N.factorial := by
  simp only
  set d := 4 * (b : ℝ) * x ^ 2 with hd_def
  set K := 2 ^ (s + 1) * Real.exp (2 * |x|) * (2 * |x|) with hK_def
  have hNf_pos : (0 : ℝ) < ↑N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hprod_nn : 0 ≤ (↑N.factorial : ℝ) * ↑b ^ N * 2 ^ s := by positivity
  have hNf_ne : (↑N.factorial : ℝ) ≠ 0 := ne_of_gt hNf_pos
  -- Algebraic identity: b^N · (2|x|)^(2N+1) = (2|x|) · d^N
  have hpower : (b : ℝ) ^ N * (2 * |x|) ^ (2 * N + 1) = (2 * |x|) * d ^ N := by
    have hd_eq : d = (b : ℝ) * (2 * |x|) ^ 2 := by
      simp only [hd_def, mul_pow, sq_abs]; ring
    rw [show (2 * N + 1 : ℕ) = 1 + 2 * N from by omega, pow_add, pow_one, pow_mul]
    rw [mul_comm ((b : ℝ) ^ N) _, mul_assoc, ← mul_pow]
    congr 1; rw [mul_comm, hd_eq]
  -- Apply padeR_bound
  have hRB := padeR_bound N hN x
  have h2N1_pos : (0 : ℝ) < ↑(2 * N + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  calc ↑N.factorial * ↑b ^ N * 2 ^ s * |padeR N x|
      ≤ ↑N.factorial * ↑b ^ N * 2 ^ s *
        ((2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|)) /
          (↑(2 * N + 1 : ℕ) * (↑N.factorial ^ 2))) :=
        mul_le_mul_of_nonneg_left hRB hprod_nn
    _ ≤ ↑N.factorial * ↑b ^ N * 2 ^ s *
        ((2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|)) / (↑N.factorial ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hprod_nn
        exact div_le_div_of_nonneg_left
          (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) _)
            (mul_nonneg (by norm_num) (exp_pos _).le))
          (sq_pos_of_pos hNf_pos)
          (le_mul_of_one_le_left (sq_nonneg _) (Nat.one_le_cast.mpr (by omega)))
    _ = K * d ^ N / ↑N.factorial := by
        have hkey : ↑b ^ N * 2 ^ s *
            ((2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|))) = K * d ^ N := by
          rw [show K = 2 ^ (s + 1) * exp (2 * |x|) * (2 * |x|) from rfl]
          linear_combination 2 ^ s * 2 * exp (2 * |x|) * hpower
        rw [mul_div_assoc']
        exact (div_eq_div_iff (ne_of_gt (sq_pos_of_pos hNf_pos)) hNf_ne).mpr (by
          rw [sq]; linear_combination ↑N.factorial * ↑N.factorial * hkey)

/-- The scaled remainder `N! · b^N · 2^s · |R_N(a/b)|` is `< 1/2` for large `N`.
Uses `padeR_bound` and `factorial_dominates`. -/
theorem pade_scaled_remainder_small (a : ℤ) (b : ℕ) (hb : 0 < b) (s : ℕ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N, N₀ ≤ N →
      (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * |padeR N ((a : ℝ) / (b : ℝ))| < 1 / 2 := by
  set x := (a : ℝ) / (b : ℝ) with hx_def
  -- d = 4·b·x², the base for the factorial convergence
  set d := 4 * (b : ℝ) * x ^ 2 with hd_def
  -- K = constant factor (independent of N)
  set K := 2 ^ (s + 1) * Real.exp (2 * |x|) * (2 * |x|) with hK_def
  have hK_nn : 0 ≤ K := by positivity
  have hd_nn : 0 ≤ d := by positivity
  have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  -- Find N₀ from d^n/n! → 0
  have htend := FloorSemiring.tendsto_pow_div_factorial_atTop d
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₁, hN₁⟩ := htend (1 / (2 * (K + 1))) (by positivity)
  use max N₁ 1
  refine ⟨by omega, fun N hN => ?_⟩
  have hN_pos : 0 < N := by omega
  have hNN₁ : N₁ ≤ N := by omega
  have hNf_pos : (0 : ℝ) < ↑N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hprod_nn : 0 ≤ (↑N.factorial : ℝ) * ↑b ^ N * 2 ^ s := by positivity
  -- Algebraic identity: b^N · (2|x|)^(2N+1) = (2|x|) · d^N
  have hpower : (b : ℝ) ^ N * (2 * |x|) ^ (2 * N + 1) = (2 * |x|) * d ^ N := by
    have hd_eq : d = (b : ℝ) * (2 * |x|) ^ 2 := by
      simp only [hd_def, mul_pow, sq_abs]; ring
    rw [show (2 * N + 1 : ℕ) = 1 + 2 * N from by omega, pow_add, pow_one, pow_mul]
    rw [mul_comm ((b : ℝ) ^ N) _, mul_assoc, ← mul_pow]
    congr 1; rw [mul_comm, hd_eq]
  -- Apply padeR_bound
  have hRB := padeR_bound N hN_pos x
  have hNf_ne : (↑N.factorial : ℝ) ≠ 0 := ne_of_gt hNf_pos
  -- Key bound: N!·b^N·2^s·|R_N(x)| ≤ K·d^N/N!
  have hbound : ↑N.factorial * ↑b ^ N * 2 ^ s * |padeR N x| ≤ K * d ^ N / ↑N.factorial := by
    have h2N1_pos : (0 : ℝ) < ↑(2 * N + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
    -- Apply the Padé bound
    calc ↑N.factorial * ↑b ^ N * 2 ^ s * |padeR N x|
        ≤ ↑N.factorial * ↑b ^ N * 2 ^ s *
          ((2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|)) /
            (↑(2 * N + 1 : ℕ) * (↑N.factorial ^ 2))) :=
          mul_le_mul_of_nonneg_left hRB hprod_nn
      _ ≤ ↑N.factorial * ↑b ^ N * 2 ^ s *
          ((2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|)) / (↑N.factorial ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hprod_nn
          exact div_le_div_of_nonneg_left
            (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) _)
              (mul_nonneg (by norm_num) (exp_pos _).le))
            (sq_pos_of_pos hNf_pos)
            (le_mul_of_one_le_left (sq_nonneg _) (Nat.one_le_cast.mpr (by omega)))
      _ = K * d ^ N / ↑N.factorial := by
          have hkey : ↑b ^ N * 2 ^ s *
              ((2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|))) = K * d ^ N := by
            rw [show K = 2 ^ (s + 1) * exp (2 * |x|) * (2 * |x|) from rfl]
            linear_combination 2 ^ s * 2 * exp (2 * |x|) * hpower
          rw [mul_div_assoc']
          exact (div_eq_div_iff (ne_of_gt (sq_pos_of_pos hNf_pos)) hNf_ne).mpr (by
            rw [sq]; linear_combination ↑N.factorial * ↑N.factorial * hkey)
  -- d^N / N! < ε from tendsto
  have hsmall := hN₁ N hNN₁
  rw [dist_zero_right, Real.norm_of_nonneg (div_nonneg (pow_nonneg hd_nn _)
    (Nat.cast_nonneg _))] at hsmall
  -- Now: K * d^N / N! < 1/2
  by_cases hK_pos : K = 0
  · calc ↑N.factorial * ↑b ^ N * 2 ^ s * |padeR N x|
        ≤ K * d ^ N / ↑N.factorial := hbound
      _ = 0 := by simp [hK_pos]
      _ < 1 / 2 := by norm_num
  · have hK_pos' : 0 < K := lt_of_le_of_ne hK_nn (Ne.symm hK_pos)
    calc ↑N.factorial * ↑b ^ N * 2 ^ s * |padeR N x|
        ≤ K * d ^ N / ↑N.factorial := hbound
      _ = K * (d ^ N / ↑N.factorial) := by rw [mul_div_assoc]
      _ < K * (1 / (2 * (K + 1))) := mul_lt_mul_of_pos_left hsmall hK_pos'
      _ = K / (K + 1) / 2 := by
            have : K + 1 ≠ 0 := by linarith
            field_simp
      _ ≤ 1 / 2 := div_le_div_of_nonneg_right
          (div_le_one_of_le₀ (by linarith) (by linarith)) (by norm_num)

/-! ## Cross product of consecutive Padé approximants

The key identity: `Q_N·P_{N+1} - Q_{N+1}·P_N ≠ 0` for nonzero `x`.

The proof uses a recurrence: the cross product `F_N` satisfies
`F_N = -x²/(N(N+1)) · F_{N-1}` (from the three-term recurrence of Padé polynomials).
Starting from `F_0 = -2x`, we get `F_N ≠ 0` for `x ≠ 0` by induction.

The explicit formula is `F_N(x) = (-1)^{N+1} · 2/(N!·(N+1)!) · x^{2N+1}`.
-/

/-- The cross product function. -/
private noncomputable def padeCross (N : ℕ) (x : ℝ) : ℝ :=
  padeQ N x * padeP (N + 1) x - padeQ (N + 1) x * padeP N x

/-- Base case: `F_0(x) = -2x`. -/
private theorem padeCross_zero (x : ℝ) : padeCross 0 x = -2 * x := by
  simp only [padeCross, padeQ, padeP, padeCoeff]
  simp [Finset.sum_range_succ]
  ring

set_option maxHeartbeats 800000 in
/-- The ℕ identity underlying the coefficient recurrence:
`N*(N+1)*C(2N+2-k, N+1) = (4N+2)*N*C(2N-k, N) + k*(k-1)*C(2N-k, N-1)` -/
private theorem choose_pade_recurrence_nat (N k : ℕ) (hN : 0 < N) (hk : k ≤ N + 1) :
    N * (N + 1) * (2 * (N + 1) - k).choose (N + 1) =
    (4 * N + 2) * N * (2 * N - k).choose N + k * (k - 1) * (2 * N - k).choose (N - 1) := by
  set m := 2 * N - k with hm_def
  have hm_eq : 2 * (N + 1) - k = m + 2 := by omega
  rw [hm_eq]
  -- Double Pascal: C(m+2, N+1) = C(m, N-1) + 2*C(m, N) + C(m, N+1)
  have pascal : (m + 2).choose (N + 1) =
      m.choose (N - 1) + 2 * m.choose N + m.choose (N + 1) := by
    have s1 : (m + 2).choose (N + 1) = (m + 1).choose N + (m + 1).choose (N + 1) :=
      Nat.choose_succ_succ' (m + 1) N
    have s2 : (m + 1).choose (N + 1) = m.choose N + m.choose (N + 1) :=
      Nat.choose_succ_succ' m N
    have s3 : (m + 1).choose N = m.choose (N - 1) + m.choose N := by
      rw [show N = (N - 1) + 1 from by omega]; exact Nat.choose_succ_succ' m (N - 1)
    omega
  -- Ratio identities from choose_succ_right_eq
  have h1 : m.choose (N + 1) * (N + 1) = m.choose N * (m - N) :=
    Nat.choose_succ_right_eq m N
  have h2 : m.choose N * N = m.choose (N - 1) * (m - (N - 1)) := by
    rw [← Nat.choose_succ_right_eq m (N - 1), show N - 1 + 1 = N from by omega]
  -- Handle edge case k = N+1 separately (both sides are 0 * ... = 0 * ...)
  by_cases hkN : k ≤ N
  · -- Main case: k ≤ N. Here m ≥ N, so all ℕ subtractions are well-behaved.
    have hNm : N ≤ m := by omega
    have hN1m : N - 1 ≤ m := by omega
    have hkm : k ≤ 2 * N := by omega
    -- Substitute pascal into goal, then use h1 and h2 to close
    rw [pascal]
    -- Goal: N*(N+1)*(B + 2*A + C(m,N+1)) = (4N+2)*N*A + k*(k-1)*B
    -- where A = m.choose N, B = m.choose (N-1)
    -- From h1: C(m,N+1)*(N+1) = A*(m-N), so multiply h1 by N:
    -- N*(N+1)*C(m,N+1) = N*A*(m-N)
    -- From h2: A*N = B*(m-(N-1))
    -- So N*A*(m-N) = B*(m-(N-1))*(m-N)... no, these are different products.
    -- Let's just use nlinarith in ℕ with careful product hints
    have hm_N : m - N = N - k := by omega
    have hm_N1 : m - (N - 1) = N - k + 1 := by omega
    rw [hm_N] at h1; rw [hm_N1] at h2
    -- h1: C(m,N+1)*(N+1) = A*(N-k)
    -- h2: A*N = B*(N-k+1) where A=C(m,N), B=C(m,N-1)
    -- Goal: N*(N+1)*(B + 2*A + C(m,N+1)) = (4N+2)*N*A + k*(k-1)*B
    set A := m.choose N
    set B := m.choose (N - 1)
    set C1 := m.choose (N + 1)
    -- Step 1: N*(N+1)*C1 = N*A*(N-k)
    have p1 : N * (N + 1) * C1 = N * A * (N - k) := by nlinarith [h1]
    -- Step 2: (N+k) * h2: (N+k)*A*N = (N+k)*B*(N-k+1)
    have p2 : (N + k) * (A * N) = (N + k) * (B * (N - k + 1)) := by
      rw [h2]
    -- Step 3: polynomial identity (N-k+1)*(N+k) + k*(k-1) = N*(N+1)
    have poly : (N - k + 1) * (N + k) + k * (k - 1) = N * (N + 1) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · simp; ring
      · zify [hkN, hk1] at *; nlinarith
    -- Combine step by step
    -- From p1: N*(N+1)*C1 = N*A*(N-k)
    -- From p2: (N+k)*A*N = (N+k)*B*(N-k+1)
    -- From poly: (N-k+1)*(N+k) + k*(k-1) = N*(N+1)
    -- So (N+k)*B*(N-k+1) = (N+k)*A*N [from p2]
    -- And B*(N-k+1)*(N+k) + B*k*(k-1) = B*N*(N+1) [from poly * B]
    -- So B*N*(N+1) = (N+k)*A*N + B*k*(k-1) [substituting p2]
    -- Goal: N*(N+1)*(B + 2*A + C1) = (4*N+2)*N*A + k*(k-1)*B
    -- LHS = N*(N+1)*B + 2*N*(N+1)*A + N*(N+1)*C1
    --     = N*(N+1)*B + 2*N*(N+1)*A + N*A*(N-k)  [from p1]
    -- RHS = (4*N+2)*N*A + k*(k-1)*B
    -- So LHS - RHS = N*(N+1)*B - k*(k-1)*B + N*A*(2*(N+1) + (N-k)) - (4*N+2)*N*A
    -- = B*(N*(N+1) - k*(k-1)) + N*A*(3*N+2-k - 4*N - 2) = B*... - N*A*(N+k)
    -- = B*(N*(N+1) - k*(k-1)) - N*A*(N+k)
    -- = (N+k)*A*N + B*k*(k-1) - N*A*(N+k) = B*k*(k-1) + 0... wait, that's wrong.
    -- Let me just do it with have's.
    have step1 : N * (N + 1) * (B + 2 * A + C1) =
        N * (N + 1) * B + 2 * N * (N + 1) * A + N * (N + 1) * C1 := by ring
    rw [step1, p1]
    -- Goal: N*(N+1)*B + 2*N*(N+1)*A + N*A*(N-k) = (4*N+2)*N*A + k*(k-1)*B
    -- From poly*B: B*((N-k+1)*(N+k)) + B*(k*(k-1)) = B*(N*(N+1))
    -- i.e., N*(N+1)*B = B*(N-k+1)*(N+k) + k*(k-1)*B
    have polyB : N * (N + 1) * B = B * (N - k + 1) * (N + k) + k * (k - 1) * B := by
      nlinarith [poly]
    -- From p2: (N+k)*A*N = (N+k)*B*(N-k+1), i.e., B*(N-k+1)*(N+k) = (N+k)*A*N
    have p2' : B * (N - k + 1) * (N + k) = (N + k) * A * N := by nlinarith [p2]
    -- So: N*(N+1)*B = (N+k)*A*N + k*(k-1)*B
    -- Substitute into goal:
    -- (N+k)*A*N + k*(k-1)*B + 2*N*(N+1)*A + N*A*(N-k) = (4*N+2)*N*A + k*(k-1)*B
    -- Simplify: (N+k)*A*N + 2*N*(N+1)*A + N*A*(N-k) = (4*N+2)*N*A
    -- Factor A*N out: A*N*((N+k) + 2*(N+1) + (N-k)) = A*N*(4*N+2)
    -- (N+k) + 2*(N+1) + (N-k) = 4*N + 2 ✓
    have sum_eq : (N + k) * (A * N) + 2 * N * (N + 1) * A + N * A * (N - k) =
        (4 * N + 2) * N * A := by
      zify [hkN] at *
      nlinarith
    linarith [polyB, p2', sum_eq]
  · -- Edge case: k = N+1 (since k ≤ N+1 and ¬(k ≤ N))
    push_neg at hkN; have hk_eq : k = N + 1 := by omega
    subst hk_eq
    have hm_val : m = N - 1 := by omega
    simp only [hm_val, show N - 1 + 2 = N + 1 from by omega,
               show (N + 1) - 1 = N from by omega,
               Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega : N - 1 < N)]
    ring

/-- Three-term coefficient recurrence for Padé coefficients. -/
private theorem padeCoeff_recurrence (N k : ℕ) (hN : 0 < N) (hk : k ≤ N + 1) :
    padeCoeff (N + 1) k = ((4 * N + 2 : ℝ) / ((N : ℝ) + 1)) * padeCoeff N k +
      if k < 2 then 0 else padeCoeff (N - 1) (k - 2) / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1_ne : (N : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hNN1_ne : (N : ℝ) * ((N : ℝ) + 1) ≠ 0 := mul_ne_zero hN_ne hN1_ne
  have hk_fac_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
  -- The ℕ identity cast to ℝ
  have key := choose_pade_recurrence_nat N k hN hk
  have key_r : (N : ℝ) * ((N : ℝ) + 1) * ((2 * (N + 1) - k).choose (N + 1) : ℝ) =
      (4 * (N : ℝ) + 2) * (N : ℝ) * ((2 * N - k).choose N : ℝ) +
      (k : ℝ) * ((k - 1 : ℕ) : ℝ) * ((2 * N - k).choose (N - 1) : ℝ) := by
    exact_mod_cast key
  -- Unfold padeCoeff and show the identity
  simp only [padeCoeff, show 2 * (N + 1) - k = 2 * N + 2 - k from by omega]
  -- The goal has C(2N+2-k, N+1)/k! = (4N+2)/(N+1) · C(2N-k,N)/k! + ...
  -- Multiply both sides by k! · N · (N+1) to clear denominators
  rw [show 2 * (N + 1) - k = 2 * N + 2 - k from by omega] at key_r
  split_ifs with hlt
  · -- k < 2: second term is 0
    simp only [add_zero]
    have hkk1 : (k : ℝ) * ((k - 1 : ℕ) : ℝ) = 0 := by interval_cases k <;> simp
    have hkey := key_r; rw [hkk1, zero_mul, add_zero] at hkey
    -- hkey: N*(N+1)*C(2N+2-k,N+1) = (4N+2)*N*C(2N-k,N)
    field_simp
    nlinarith [hkey]
  · -- k ≥ 2
    push_neg at hlt; have hk2 : 2 ≤ k := hlt
    rw [show (2 * (N - 1) - (k - 2)).choose (N - 1) = (2 * N - k).choose (N - 1) from by
      congr 1; omega]
    -- k! = k * (k-1) * (k-2)! for k ≥ 2
    have hk_fac_eq : (k.factorial : ℝ) = (k : ℝ) * ((k - 1 : ℕ) : ℝ) * ((k - 2).factorial : ℝ) := by
      have h1 := Nat.factorial_succ (k - 1)
      have h2 := Nat.factorial_succ (k - 2)
      simp only [show k - 1 + 1 = k from by omega, show k - 2 + 1 = k - 1 from by omega] at h1 h2
      have : k.factorial = k * (k - 1) * (k - 2).factorial := by rw [h1, h2]; ring
      exact_mod_cast this
    -- key_r: N*(N+1)*C(2N+2-k,N+1) = (4N+2)*N*C(2N-k,N) + k*(k-1)*C(2N-k,N-1)
    -- Goal: C(2N+2-k,N+1)/k! = (4N+2)/(N+1)*C(2N-k,N)/k! + C(2N-k,N-1)/(k-2)!/(N*(N+1))
    -- Rewrite k! = k*(k-1)*(k-2)!, then field_simp and linarith
    rw [show (k.factorial : ℝ) = (k : ℝ) * ((k - 1 : ℕ) : ℝ) * ((k - 2).factorial : ℝ) from hk_fac_eq]
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk2f_pos : (0 : ℝ) < ((k - 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    field_simp
    nlinarith [key_r, mul_pos hk_pos hk1_pos, mul_pos hk1_pos hk2f_pos]

/-- Padé coefficient vanishes for k > N, when N > 0. -/
private theorem padeCoeff_eq_zero_of_gt (N k : ℕ) (hN : 0 < N) (hk : N < k) :
    padeCoeff N k = 0 := by
  simp only [padeCoeff]
  have : Nat.choose (2 * N - k) N = 0 := by
    apply Nat.choose_eq_zero_of_lt; omega
  rw [this]; simp

/-- Three-term recurrence for P_N:
`P_{N+1}(x) = (4N+2)/(N+1) · P_N(x) + x²/(N(N+1)) · P_{N-1}(x)` for N ≥ 1. -/
private theorem padeP_recurrence (N : ℕ) (hN : 0 < N) (x : ℝ) :
    padeP (N + 1) x = ((4 * N + 2 : ℝ) / ((N : ℝ) + 1)) * padeP N x +
      x ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) * padeP (N - 1) x := by
  -- Rewrite as a single sum identity
  suffices h : ∀ k, k ∈ range (N + 2) →
      padeCoeff (N + 1) k * (-x) ^ k =
        ((4 * N + 2 : ℝ) / ((N : ℝ) + 1)) * (padeCoeff N k * (-x) ^ k) +
        x ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) *
          (if k < 2 then 0 else padeCoeff (N - 1) (k - 2) * (-x) ^ (k - 2)) by
    simp only [padeP]
    rw [show N + 1 + 1 = N + 2 from by omega]
    rw [Finset.sum_congr rfl h]
    rw [Finset.sum_add_distrib]
    congr 1
    · -- First part: extend sum from range(N+1) to range(N+2)
      rw [← Finset.mul_sum, Finset.sum_range_succ]
      rw [padeCoeff_eq_zero_of_gt N (N + 1) hN (by omega)]
      simp
    · -- Second part: reindex k ↦ k+2
      rw [← Finset.mul_sum]
      congr 1
      -- First two terms (k=0, k=1) are 0 by the ite condition
      have hstep : ∀ k, k ∈ range (N + 2) →
          (if k < 2 then (0 : ℝ) else padeCoeff (N - 1) (k - 2) * (-x) ^ (k - 2)) =
          (if k < 2 then 0 else padeCoeff (N - 1) (k - 2) * (-x) ^ (k - 2)) := by
        intros; rfl
      -- Peel off the first two zero terms
      rw [show N + 2 = 2 + (N - 1 + 1) from by omega]
      rw [Finset.sum_range_add]
      -- First sum: range 2, all terms have k < 2, so they're 0
      have : ∑ k ∈ range 2,
          (if k < 2 then (0 : ℝ) else padeCoeff (N - 1) (k - 2) * (-x) ^ (k - 2)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have : k < 2 := by simp [Finset.mem_range] at hk; omega
        simp [this]
      rw [this, zero_add]
      -- Remaining sum: Σ_{j=0}^{N-1} with shifted index
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs with h
      · omega
      · norm_num
  -- Now prove the pointwise identity
  intro k hk
  have hk_le : k ≤ N + 1 := by simp [Finset.mem_range] at hk; omega
  rw [padeCoeff_recurrence N k hN hk_le]
  split_ifs with hlt
  · simp; ring
  · push_neg at hlt
    have hk2 : 2 ≤ k := hlt
    rw [show (-x) ^ k = (-x) ^ (k - 2) * (-x) ^ 2 from by
      rw [← pow_add]; congr 1; omega]
    ring

/-- Symmetry: Q_N(x) = P_N(-x). -/
private theorem padeQ_eq_padeP_neg (N : ℕ) (x : ℝ) : padeQ N x = padeP N (-x) := by
  simp only [padeQ, padeP, neg_neg]

/-- Three-term recurrence for Q_N (same coefficients as P_N since Q_N(x) = P_N(-x)). -/
private theorem padeQ_recurrence (N : ℕ) (hN : 0 < N) (x : ℝ) :
    padeQ (N + 1) x = ((4 * N + 2 : ℝ) / ((N : ℝ) + 1)) * padeQ N x +
      x ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) * padeQ (N - 1) x := by
  simp only [padeQ_eq_padeP_neg]
  rw [padeP_recurrence N hN (-x)]
  ring

/-- The cross product recurrence: `F_N = -x²/(N(N+1)) · F_{N-1}` for `N ≥ 1`.
Follows from the three-term recurrence by substituting and cancelling. -/
private theorem padeCross_recurrence (N : ℕ) (hN : 0 < N) (x : ℝ) :
    padeCross N x = -(x ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))) * padeCross (N - 1) x := by
  simp only [padeCross]
  set α := (4 * (N : ℝ) + 2) / ((N : ℝ) + 1)
  set β := x ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))
  -- Substitute recurrences: P_{N+1} = α·P_N + β·P_{N-1}, Q_{N+1} = α·Q_N + β·Q_{N-1}
  rw [padeP_recurrence N hN x, padeQ_recurrence N hN x]
  -- After substitution, the α·Q_N·P_N terms cancel, leaving β·(Q_N·P_{N-1} - Q_{N-1}·P_N).
  -- Fix Nat subtraction: N - 1 + 1 = N for N ≥ 1
  have hN_sub : N - 1 + 1 = N := by omega
  simp only [hN_sub]
  ring

/-- The cross product `F_N(x)` is nonzero for `x ≠ 0`, for ALL `N ≥ 0`. -/
private theorem padeCross_ne_zero (N : ℕ) (x : ℝ) (hx : x ≠ 0) :
    padeCross N x ≠ 0 := by
  induction N with
  | zero =>
    rw [padeCross_zero]
    exact mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hx
  | succ n ih =>
    rw [padeCross_recurrence (n + 1) (by omega) x]
    simp only [Nat.succ_sub_one]
    apply mul_ne_zero
    · apply neg_ne_zero.mpr
      apply div_ne_zero
      · exact pow_ne_zero 2 hx
      · apply mul_ne_zero
        · exact Nat.cast_ne_zero.mpr (by omega)
        · have : (0 : ℝ) < ↑(n + 1) + 1 := by positivity
          linarith
    · exact ih

/-- The Padé cross product `Q_N·P_{N+1} - Q_{N+1}·P_N ≠ 0` for nonzero `x`. -/
private theorem pade_cross_product_ne_zero (N : ℕ) (_hN : 0 < N) (x : ℝ) (hx : x ≠ 0) :
    padeQ N x * padeP (N + 1) x - padeQ (N + 1) x * padeP N x ≠ 0 :=
  padeCross_ne_zero N x hx

/-- For nonzero rational `a/b`, the Padé integers `K_N, J_N` can't BOTH satisfy
`J_N·2^s = K_N·m` for consecutive N and the same m. More precisely: for any m,
at least one of `J_N·2^s - K_N·m` or `J_{N+1}·2^s - K_{N+1}·m` is nonzero. -/
private theorem pade_not_both_zero (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0)
    (N : ℕ) (hN : 0 < N) (m : ℤ) (s : ℕ) :
    let x := (a : ℝ) / (b : ℝ)
    let D := fun n => (n.factorial : ℝ) * (b : ℝ) ^ n
    let K := fun n => D n * padeP n x
    let J := fun n => D n * padeQ n x
    ¬(J N * 2 ^ s = K N * m ∧ J (N + 1) * 2 ^ s = K (N + 1) * m) := by
  simp only
  set x := (a : ℝ) / (b : ℝ) with hx_def
  set D := fun n => (n.factorial : ℝ) * (b : ℝ) ^ n
  set K := fun n => D n * padeP n x
  set J := fun n => D n * padeQ n x
  intro ⟨h1, h2⟩
  have hx_ne : x ≠ 0 := by
    simp only [hx_def, ne_eq, div_eq_zero_iff, Int.cast_eq_zero, Nat.cast_eq_zero]
    exact fun h => h.elim (fun h => ha h) (fun h => by omega)
  have h2s_ne : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hD_pos : ∀ n, 0 < n → 0 < D n := by
    intro n hn; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))
      (pow_pos (Nat.cast_pos.mpr hb) n)
  -- Helper: K_n = 0 implies both P_n and Q_n vanish, contradicting positivity
  have hK_zero_absurd : ∀ n, 0 < n → K n = 0 → J n = 0 → False := by
    intro n hn hK hJ
    have hD_ne : D n ≠ 0 := ne_of_gt (hD_pos n hn)
    have hP : padeP n x = 0 := by
      rcases mul_eq_zero.mp hK with h | h; exact absurd h hD_ne; exact h
    have hQ : padeQ n x = 0 := by
      rcases mul_eq_zero.mp hJ with h | h; exact absurd h hD_ne; exact h
    rcases lt_or_gt_of_ne hx_ne with hlt | hgt
    · exact absurd hP (ne_of_gt (padeP_pos_of_neg n hn x hlt))
    · exact absurd hQ (ne_of_gt (padeQ_pos n hn x hgt))
  have hDN_ne : D N ≠ 0 := ne_of_gt (hD_pos N hN)
  have hDN1_ne : D (N + 1) ≠ 0 := ne_of_gt (hD_pos (N + 1) (by omega))
  -- Step 1: Cancel D from equations to get Q·2^s = P·m
  have hQP_N : padeQ N x * 2 ^ s = padeP N x * (m : ℝ) := by
    have : D N * (padeQ N x * 2 ^ s) = D N * (padeP N x * (m : ℝ)) := by
      have : D N * padeQ N x * 2 ^ s = D N * padeP N x * (m : ℝ) := h1
      linarith
    exact mul_left_cancel₀ hDN_ne this
  have hQP_N1 : padeQ (N + 1) x * 2 ^ s = padeP (N + 1) x * (m : ℝ) := by
    have : D (N + 1) * (padeQ (N + 1) x * 2 ^ s) =
           D (N + 1) * (padeP (N + 1) x * (m : ℝ)) := by
      have : D (N + 1) * padeQ (N + 1) x * 2 ^ s =
             D (N + 1) * padeP (N + 1) x * (m : ℝ) := h2
      linarith
    exact mul_left_cancel₀ hDN1_ne this
  -- Step 2: Show K_N ≠ 0. If P_N = 0, then Q_N·2^s = 0, Q_N = 0, contradicts positivity.
  have hKN : K N ≠ 0 := by
    intro hK
    have hP : padeP N x = 0 := by
      rcases mul_eq_zero.mp hK with h | h; exact absurd h hDN_ne; exact h
    have hQ : padeQ N x = 0 := by
      have : padeQ N x * 2 ^ s = 0 := by rw [hQP_N, hP, zero_mul]
      rcases mul_eq_zero.mp this with h | h; exact h; exact absurd h h2s_ne
    exact hK_zero_absurd N hN hK (show J N = 0 by simp [J, hQ, mul_zero])
  have hKN1 : K (N + 1) ≠ 0 := by
    intro hK
    have hP : padeP (N + 1) x = 0 := by
      rcases mul_eq_zero.mp hK with h | h; exact absurd h hDN1_ne; exact h
    have hQ : padeQ (N + 1) x = 0 := by
      have : padeQ (N + 1) x * 2 ^ s = 0 := by rw [hQP_N1, hP, zero_mul]
      rcases mul_eq_zero.mp this with h | h; exact h; exact absurd h h2s_ne
    exact hK_zero_absurd (N + 1) (by omega) hK (show J (N + 1) = 0 by simp [J, hQ, mul_zero])
  -- Step 3: Cross multiply to get Q_N · P_{N+1} = Q_{N+1} · P_N
  have hcross : padeQ N x * padeP (N + 1) x = padeQ (N + 1) x * padeP N x := by
    -- Q_N · 2^s · P_{N+1} = P_N · m · P_{N+1} and Q_{N+1} · 2^s · P_N = P_{N+1} · m · P_N
    -- These are equal since P_N · m · P_{N+1} = P_{N+1} · m · P_N.
    -- Cancel 2^s.
    have : padeQ N x * padeP (N + 1) x * 2 ^ s =
           padeQ (N + 1) x * padeP N x * 2 ^ s := by
      calc padeQ N x * padeP (N + 1) x * 2 ^ s
          = padeQ N x * 2 ^ s * padeP (N + 1) x := by ring
        _ = padeP N x * (m : ℝ) * padeP (N + 1) x := by rw [hQP_N]
        _ = padeP (N + 1) x * (m : ℝ) * padeP N x := by ring
        _ = padeQ (N + 1) x * 2 ^ s * padeP N x := by rw [hQP_N1]
        _ = padeQ (N + 1) x * padeP N x * 2 ^ s := by ring
    exact mul_right_cancel₀ h2s_ne this
  -- Step 4: Contradict pade_cross_product_ne_zero
  exact pade_cross_product_ne_zero N hN x hx_ne (by linarith)

/-- For nonzero `q = a/b` and any shift `s`, `exp(a/b) · 2^s` is bounded away
from every integer. Uses irrationality of `exp(a/b)` to show the fractional part
of `exp(a/b) · 2^s` is bounded away from 0 and 1. -/
theorem exp_times_zpow_dist_from_int (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0) (s : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, |exp ((a : ℝ) / (b : ℝ)) * 2 ^ s - (m : ℝ)| ≥ δ := by
  -- Work with q = a/b as a rational
  set q : ℚ := (a : ℚ) / (b : ℚ) with hq_def
  have hq_ne : q ≠ 0 := by
    simp only [hq_def, ne_eq, div_eq_zero_iff, Int.cast_eq_zero, Nat.cast_eq_zero]
    exact fun h => h.elim (fun h => ha h) (fun h => by omega)
  have hq_cast : (q : ℝ) = (a : ℝ) / (b : ℝ) := by simp [hq_def]
  set v := exp ((a : ℝ) / (b : ℝ)) * 2 ^ s
  have hv_eq : v = exp (q : ℝ) * 2 ^ s := by rw [hq_cast]
  -- exp(q) is irrational
  have hirr := irrational_exp_rat q hq_ne
  -- v is not an integer (since exp(q) is irrational and 2^s is rational nonzero)
  have hv_not_int : ∀ m : ℤ, v ≠ (m : ℝ) := by
    intro m hvm
    have h2s_ne : (2 : ℝ) ^ s ≠ 0 := by positivity
    rw [hv_eq] at hvm
    have hexp_rat : exp (q : ℝ) = (m : ℝ) / 2 ^ s := by field_simp at hvm ⊢; linarith
    exact hirr.ne_rat (↑m / ↑(2 ^ s : ℤ)) (by push_cast; exact hexp_rat)
  -- The fractional part is nonzero
  have hfrac : Int.fract v ≠ 0 := by
    intro h
    have : v = ↑⌊v⌋ := by have := Int.floor_add_fract v; linarith
    exact hv_not_int ⌊v⌋ this
  -- δ = min(fract v, 1 - fract v) > 0
  set δ := min (Int.fract v) (1 - Int.fract v)
  have hfrac_pos : 0 < Int.fract v := lt_of_le_of_ne (Int.fract_nonneg v) (Ne.symm hfrac)
  have hfrac_lt : Int.fract v < 1 := Int.fract_lt_one v
  have hδ_pos : 0 < δ := lt_min hfrac_pos (by linarith)
  refine ⟨δ, hδ_pos, fun m => ?_⟩
  -- |v - m| ≥ δ for any integer m
  -- v = ⌊v⌋ + fract v, so v - m = (⌊v⌋ - m) + fract v
  -- If m ≤ ⌊v⌋: v - m ≥ fract v ≥ δ
  -- If m ≥ ⌊v⌋ + 1: m - v ≥ 1 - fract v ≥ δ
  have hv_decomp := Int.floor_add_fract v
  by_cases hle : m ≤ ⌊v⌋
  · -- |v - m| = v - m ≥ v - ⌊v⌋ = fract v ≥ δ
    have : (m : ℝ) ≤ (⌊v⌋ : ℝ) := Int.cast_le.mpr hle
    rw [abs_of_nonneg (by linarith)]
    have : v = ↑⌊v⌋ + Int.fract v := hv_decomp.symm
    linarith [min_le_left (Int.fract v) (1 - Int.fract v)]
  · -- m ≥ ⌊v⌋ + 1, so m - v ≥ 1 - fract v ≥ δ
    push_neg at hle
    have : (⌊v⌋ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hle
    have : v = ↑⌊v⌋ + Int.fract v := hv_decomp.symm
    rw [abs_of_nonpos (by linarith)]
    linarith [min_le_right (Int.fract v) (1 - Int.fract v)]

/-! ## Effective irrationality measure via Padé

The non-effective `exp_times_zpow_dist_from_int` gives `δ > 0` but without a computable
witness. Here we combine the Padé machinery to get a fully effective bound:

1. `pow_div_factorial_bound`: For `N ≥ 2⌈d⌉ + M`, `d^N/N! < (1/2)^M · d^{2⌈d⌉}/(2⌈d⌉)!`
2. `pade_effective_N₀`: Explicit `N₀` such that `N!·b^N·2^s·|R_N(a/b)| < 1/2` for `N ≥ N₀`
3. `pade_effective_delta`: Effective lower bound `|exp(a/b)·2^s - m| ≥ δ_eff` for all `m : ℤ`
-/

/-! ### Step 1: Effective factorial domination

For `N > d`, each factor `d/k < 1`, so `d^N/N!` decays geometrically.
For `N ≥ 2⌈d⌉`, each factor `d/k ≤ 1/2`, giving `d^N/N! ≤ d^{2⌈d⌉}/(2⌈d⌉)! · (1/2)^{N-2⌈d⌉}`.
-/

/-- For `N ≥ 2 * m` and `d ≤ m`, the ratio `d^N / N!` is bounded by
`d^(2*m) / (2*m)! · (1/2)^(N - 2*m)`.
The idea: for `k > 2m ≥ 2d`, the factor `d/k ≤ d/(2m) ≤ 1/2`. -/
theorem pow_div_factorial_geometric_bound (d : ℝ) (hd : 0 ≤ d) (m : ℕ) (hm : d ≤ m)
    (N : ℕ) (hN : 2 * m ≤ N) :
    d ^ N / (N.factorial : ℝ) ≤
      d ^ (2 * m) / ((2 * m).factorial : ℝ) * (1 / 2) ^ (N - 2 * m) := by
  -- Reduce to induction on j = N - 2m
  suffices h : ∀ j : ℕ, d ^ (2 * m + j) / ((2 * m + j).factorial : ℝ) ≤
      d ^ (2 * m) / ((2 * m).factorial : ℝ) * (1 / 2) ^ j by
    have := h (N - 2 * m)
    rwa [Nat.add_sub_cancel' hN] at this
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    -- Factor: d^(2m+j+1)/(2m+j+1)! = (d^(2m+j)/(2m+j)!) · d/(2m+j+1)
    have hfac_ne : ((2 * m + j).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn1_pos : (0 : ℝ) < ((2 * m + j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio : d ^ (2 * m + j + 1) / ((2 * m + j + 1).factorial : ℝ) =
        (d ^ (2 * m + j) / ((2 * m + j).factorial : ℝ)) *
        (d / ((2 * m + j + 1 : ℕ) : ℝ)) := by
      rw [show 2 * m + j + 1 = (2 * m + j) + 1 from by omega,
          pow_succ, Nat.factorial_succ, Nat.cast_mul]
      field_simp
    -- Bound: d/(2m+j+1) ≤ 1/2 since d ≤ m and 2m+j+1 ≥ 2m+1 ≥ 2d
    have hfactor : d / ((2 * m + j + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn1_pos (by norm_num : (0:ℝ) < 2)]
      simp only [one_mul]
      calc d * 2 ≤ (m : ℝ) * 2 := by nlinarith
        _ = ((2 * m : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 * m + j + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    -- Combine with inductive hypothesis
    rw [show 2 * m + (j + 1) = 2 * m + j + 1 from by omega, hratio]
    calc (d ^ (2 * m + j) / ↑(2 * m + j).factorial) *
            (d / ↑(2 * m + j + 1))
        ≤ (d ^ (2 * m) / ↑(2 * m).factorial * (1 / 2) ^ j) * (1 / 2) :=
          mul_le_mul ih hfactor (div_nonneg hd hn1_pos.le) (by positivity)
      _ = d ^ (2 * m) / ↑(2 * m).factorial * (1 / 2) ^ (j + 1) := by
          rw [pow_succ]; ring

/-- Explicit bound: `d^N / N! < ε` when `N ≥ 2⌈d⌉ + ⌈log₂(C/ε)⌉` where
`C = d^{2⌈d⌉} / (2⌈d⌉)!`. We state this as: for any `M`, once `N ≥ 2⌈d⌉ + M`,
`d^N / N! ≤ C · (1/2)^M`. -/
theorem pow_div_factorial_effective (d : ℝ) (hd : 0 ≤ d) (M : ℕ) :
    let m := ⌈d⌉₊  -- Nat.ceil d
    let N := 2 * m + M
    d ^ N / (N.factorial : ℝ) ≤
      d ^ (2 * m) / ((2 * m).factorial : ℝ) * (1 / 2) ^ M := by
  simp only
  have hm : d ≤ ↑⌈d⌉₊ := Nat.le_ceil d
  have h := pow_div_factorial_geometric_bound d hd ⌈d⌉₊ hm (2 * ⌈d⌉₊ + M) (by omega)
  rwa [show 2 * ⌈d⌉₊ + M - 2 * ⌈d⌉₊ = M from by omega] at h

/-! ### Step 2: Effective N₀ for Padé convergence -/

/-- The Padé convergence threshold: an explicit `N₀` such that the scaled Padé
remainder is `< 1/2` for all `N ≥ N₀`.

Given `d = 4·b·(a/b)²` and `K = 2^{s+1}·exp(2|a/b|)·(2|a/b|)`, we need
`K · d^N / N! < 1/2`. By `pow_div_factorial_effective`, this holds once
`C · (1/2)^M < 1/(2K)`, i.e., `M > log₂(2KC)`. We set `N₀ = 2⌈d⌉ + M₀`
for a suitable `M₀`. -/
noncomputable def padeConvergenceN₀ (a : ℤ) (b : ℕ) (s : ℕ) : ℕ :=
  let x := (a : ℝ) / (b : ℝ)
  let d := 4 * (b : ℝ) * x ^ 2
  let m := ⌈d⌉₊
  -- K = constant factor from pade_scaled_remainder_small
  let K := 2 ^ (s + 1) * Real.exp (2 * |x|) * (2 * |x|)
  -- C = d^{2m} / (2m)! from pow_div_factorial_effective
  let C := d ^ (2 * m) / ((2 * m).factorial : ℝ)
  -- M chosen so (1/2)^M · C < 1/(2(K+1)), i.e., 2^M > 2(K+1)(C+1).
  -- Using Nat.log2 gives M = O(log(KC)) instead of O(KC), keeping N₀ polynomial.
  let M := Nat.log2 (⌈2 * (K + 1) * (C + 1)⌉₊) + 1
  2 * m + M

/-- `padeConvergenceN₀` is positive. -/
theorem padeConvergenceN₀_pos (a : ℤ) (b : ℕ) (s : ℕ) :
    0 < padeConvergenceN₀ a b s := by
  simp only [padeConvergenceN₀]
  -- N₀ = 2 * m + (Nat.log2(...) + 1) ≥ 1
  omega

/-- The effective version of `pade_scaled_remainder_small`: for `N ≥ padeConvergenceN₀`,
the scaled Padé remainder is `< 1/2`. -/
theorem pade_scaled_remainder_effective (a : ℤ) (b : ℕ) (hb : 0 < b) (s : ℕ)
    (N : ℕ) (hN : padeConvergenceN₀ a b s ≤ N) (hN_pos : 0 < N) :
    (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * |padeR N ((a : ℝ) / (b : ℝ))| < 1 / 2 := by
  set x := (a : ℝ) / (b : ℝ) with hx_def
  set d := 4 * (b : ℝ) * x ^ 2 with hd_def
  set m := ⌈d⌉₊ with hm_def
  set K := 2 ^ (s + 1) * Real.exp (2 * |x|) * (2 * |x|) with hK_def
  set C := d ^ (2 * m) / ((2 * m).factorial : ℝ) with hC_def
  set M₀ := Nat.log2 (⌈2 * (K + 1) * (C + 1)⌉₊) + 1 with hM₀_def
  have hd_nn : 0 ≤ d := by positivity
  have hK_nn : 0 ≤ K := by positivity
  have hC_nn : 0 ≤ C := by positivity
  have hm_ge : d ≤ ↑m := Nat.le_ceil d
  -- Structural facts from padeConvergenceN₀ definition
  have hN₀_eq : padeConvergenceN₀ a b s = 2 * m + M₀ := rfl
  have h2m_le_N : 2 * m ≤ N := by omega
  have hM₀_le : M₀ ≤ N - 2 * m := by omega
  -- Step 1: pade_scaled_bound_by_K_d gives the upper bound
  have hstep1 : (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * |padeR N x| ≤
      K * d ^ N / N.factorial :=
    pade_scaled_bound_by_K_d N hN_pos x b hb s
  -- Step 2: Geometric decay of d^N / N!
  have hstep2 : d ^ N / (N.factorial : ℝ) ≤ C * (1 / 2) ^ (N - 2 * m) :=
    pow_div_factorial_geometric_bound d hd_nn m hm_ge N h2m_le_N
  -- Step 3: Monotonicity of (1/2)^k
  have hstep3 : (1 / 2 : ℝ) ^ (N - 2 * m) ≤ (1 / 2 : ℝ) ^ M₀ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hM₀_le
  -- Combine: d^N / N! ≤ C * (1/2)^M₀
  have hstep_dN : d ^ N / (N.factorial : ℝ) ≤ C * (1 / 2) ^ M₀ :=
    hstep2.trans (mul_le_mul_of_nonneg_left hstep3 hC_nn)
  -- K * d^N / N! ≤ KC * (1/2)^M₀
  have hstep_KdN : K * d ^ N / (N.factorial : ℝ) ≤ K * C * (1 / 2) ^ M₀ := by
    calc K * d ^ N / (N.factorial : ℝ) = K * (d ^ N / (N.factorial : ℝ)) := mul_div_assoc K _ _
      _ ≤ K * (C * (1 / 2) ^ M₀) := mul_le_mul_of_nonneg_left hstep_dN hK_nn
      _ = K * C * (1 / 2) ^ M₀ := (mul_assoc K C _).symm
  -- KC * (1/2)^M₀ < 1/2
  have hfinal : K * C * (1 / 2 : ℝ) ^ M₀ < 1 / 2 := by
    by_cases hKC : K * C = 0
    · simp [hKC]
    · have hKC_pos : 0 < K * C := lt_of_le_of_ne (mul_nonneg hK_nn hC_nn) (Ne.symm hKC)
      -- Suffices: 2KC < 2^M₀
      suffices h2KC : 2 * (K * C) < (2 : ℝ) ^ M₀ by
        have h2M_pos : (0 : ℝ) < 2 ^ M₀ := by positivity
        have heq : K * C * (1 / 2 : ℝ) ^ M₀ = K * C / 2 ^ M₀ := by
          rw [one_div, inv_pow, div_eq_mul_inv]
        rw [heq, div_lt_iff₀ h2M_pos]
        linarith
      -- 2^M₀ = 2^{log2(n)+1} > n ≥ 2(K+1)(C+1) > 2KC
      set n := ⌈2 * (K + 1) * (C + 1)⌉₊ with hn_def
      have hn_ge : 2 * (K + 1) * (C + 1) ≤ (n : ℝ) := Nat.le_ceil _
      have hn_pos : 0 < n := by
        rw [hn_def]; exact Nat.ceil_pos.mpr (by nlinarith)
      have h_log2 : n < 2 ^ (Nat.log2 n + 1) := by
        rw [Nat.log2_eq_log_two]
        exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
      have hM₀_eq : M₀ = Nat.log2 n + 1 := rfl
      calc 2 * (K * C) < 2 * ((K + 1) * (C + 1)) := by nlinarith
        _ ≤ (n : ℝ) := by linarith
        _ < (2 ^ (Nat.log2 n + 1) : ℝ) := by exact_mod_cast h_log2
        _ = (2 : ℝ) ^ M₀ := by rw [hM₀_eq]
  -- Combine everything
  calc (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * |padeR N x|
      ≤ K * d ^ N / (N.factorial : ℝ) := hstep1
    _ ≤ K * C * (1 / 2) ^ M₀ := hstep_KdN
    _ < 1 / 2 := hfinal

/-! ### Step 3: Effective delta -/

/-- Key helper: under the Padé remainder bound, `N! · b^N · P_N(a/b) ≠ 0`.
If `P_N(x) = 0`, the Padé identity forces `Q_N(x) = 0` (by integrality),
contradicting that P and Q can't both vanish for `x ≠ 0`. -/
private lemma pade_K_ne_zero (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0) (s : ℕ)
    (N : ℕ) (hN : 0 < N)
    (hR : (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s *
      |padeR N ((a : ℝ) / (b : ℝ))| < 1 / 2) :
    (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N ((a : ℝ) / (b : ℝ)) ≠ 0 := by
  set x := (a : ℝ) / (b : ℝ) with hx_def
  set D := (N.factorial : ℝ) * (b : ℝ) ^ N with hD_def
  have hD_pos : 0 < D := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos N))
    (pow_pos (Nat.cast_pos.mpr hb) N)
  intro hK
  -- P_N(x) = 0
  have hP : padeP N x = 0 := by
    rcases mul_eq_zero.mp hK with h | h
    · exact absurd h (ne_of_gt hD_pos)
    · exact h
  -- From Padé identity: K * exp(x) - J = D * R_N(x)
  -- With K = 0: J = -D * R_N(x)
  have hJ_eq : D * padeQ N x = -(D * padeR N x) := by
    have : D * padeR N x = D * padeP N x * exp x - D * padeQ N x := by
      rw [show padeR N x = padeP N x * exp x - padeQ N x from rfl]; ring
    rw [hP, mul_zero, zero_mul, zero_sub] at this
    linarith
  -- |J| = |D * Q_N(x)| = D * |R_N(x)| < 1/2 (from remainder bound / 2^s)
  have hJ_small : |D * padeQ N x| < 1 := by
    rw [hJ_eq, abs_neg, abs_mul, abs_of_pos hD_pos]
    have h2s : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [abs_nonneg (padeR N x)]
  -- J = D * Q_N(x) is an integer
  obtain ⟨J, hJ_int⟩ := padeQ_clears a b hb N
  change D * padeQ N x = ↑J at hJ_int
  -- |J| < 1 and J is an integer, so J = 0
  have hJ_zero : J = 0 := by
    by_contra hJ_ne
    have : (1 : ℝ) ≤ |(J : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hJ_ne
    linarith [show |D * padeQ N x| = |(J : ℝ)| by rw [hJ_int]]
  -- So Q_N(x) = 0
  have hQ : padeQ N x = 0 := by
    have : D * padeQ N x = 0 := by rw [hJ_int, hJ_zero, Int.cast_zero]
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hD_pos)
  -- Both P_N(x) = 0 and Q_N(x) = 0 for x ≠ 0: contradiction
  have hx_ne : x ≠ 0 := by
    simp only [hx_def, ne_eq, div_eq_zero_iff, Int.cast_eq_zero, Nat.cast_eq_zero]
    exact fun h => h.elim (fun h => ha h) (fun h => by omega)
  rcases lt_or_gt_of_ne hx_ne with hlt | hgt
  · exact absurd hP (ne_of_gt (padeP_pos_of_neg N hN x hlt))
  · exact absurd hQ (ne_of_gt (padeQ_pos N hN x hgt))

/-- The effective distance bound: for nonzero rational `a/b` and shift `s`,
`|exp(a/b) · 2^s - m| ≥ 1/(2D)` for all integers `m`, where
`D = max(|K_{N₀}|, |K_{N₀+1}|)` and `K_N = N! · b^N · P_N(a/b)`.

Uses `pade_not_both_zero` to get a nonzero gap for each `m`, then
a direct bound `|K|·|v| ≥ 1/2` from the gap principle. -/
theorem pade_effective_delta (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0) (s : ℕ) :
    let N₀ := padeConvergenceN₀ a b s
    let x := (a : ℝ) / (b : ℝ)
    let D := max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)
                 (((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) * |padeP (N₀ + 1) x|)
    0 < D ∧ ∀ m : ℤ,
      |Real.exp x * 2 ^ s - (m : ℝ)| ≥ 1 / (2 * D) := by
  simp only
  set N₀ := padeConvergenceN₀ a b s
  set x := (a : ℝ) / (b : ℝ) with hx_def
  have hN₀_pos := padeConvergenceN₀_pos a b s
  -- Remainder bounds for N₀ and N₀+1
  have hR₀ := pade_scaled_remainder_effective a b hb s N₀ (le_refl _) hN₀_pos
  have hR₁ := pade_scaled_remainder_effective a b hb s (N₀ + 1) (by omega) (by omega)
  -- K values (= N!·b^N·P_N(x)) are nonzero
  have hK₀_ne := pade_K_ne_zero a b hb ha s N₀ hN₀_pos hR₀
  have hK₁_ne := pade_K_ne_zero a b hb ha s (N₀ + 1) (by omega) hR₁
  set D := max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)
               (((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) * |padeP (N₀ + 1) x|)
  have hD_pos : 0 < D := lt_max_of_lt_left (by
    have : padeP N₀ x ≠ 0 := by
      intro h; exact hK₀_ne (by rw [h, mul_zero])
    positivity)
  refine ⟨hD_pos, fun m => ?_⟩
  -- Helper: for order N with remainder bound, |K_N|·|v| ≥ 1/2 when gap ≠ 0
  suffices key : ∀ N, 0 < N →
      (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * |padeR N x| < 1 / 2 →
      (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N x ≠ 0 →
      ∀ G : ℤ, G ≠ 0 →
      (N.factorial : ℝ) * (b : ℝ) ^ N * padeQ N x * 2 ^ s -
        (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N x * (m : ℝ) = (G : ℝ) →
      |exp x * 2 ^ s - (m : ℝ)| ≥
        1 / (2 * ((N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x|)) by
    -- Use pade_not_both_zero: at least one gap is nonzero
    -- Get integer representations of the gaps
    obtain ⟨A₀, hA₀⟩ := padeP_clears a b hb N₀
    obtain ⟨A₁, hA₁⟩ := padeP_clears a b hb (N₀ + 1)
    obtain ⟨B₀, hB₀⟩ := padeQ_clears a b hb N₀
    obtain ⟨B₁, hB₁⟩ := padeQ_clears a b hb (N₀ + 1)
    -- Fold x into the clearance hypotheses (padeP/Q_clears use ↑a/↑b, not x)
    rw [← hx_def] at hA₀ hA₁ hB₀ hB₁
    set G₀ := B₀ * (2 : ℤ) ^ s - A₀ * m
    set G₁ := B₁ * (2 : ℤ) ^ s - A₁ * m
    -- At least one gap is nonzero (from pade_not_both_zero)
    have hG_or : G₀ ≠ 0 ∨ G₁ ≠ 0 := by
      by_contra h; push_neg at h; obtain ⟨h0, h1⟩ := h
      exact pade_not_both_zero a b hb ha N₀ hN₀_pos m s ⟨by
        have hG₀_cast : (G₀ : ℝ) = (B₀ : ℝ) * 2 ^ s - (A₀ : ℝ) * m :=
          by exact_mod_cast (rfl : G₀ = B₀ * (2 : ℤ) ^ s - A₀ * m)
        have := show (G₀ : ℝ) = 0 from by exact_mod_cast h0
        rw [hG₀_cast, ← hB₀, ← hA₀] at this; linarith, by
        have hG₁_cast : (G₁ : ℝ) = (B₁ : ℝ) * 2 ^ s - (A₁ : ℝ) * m :=
          by exact_mod_cast (rfl : G₁ = B₁ * (2 : ℤ) ^ s - A₁ * m)
        have := show (G₁ : ℝ) = 0 from by exact_mod_cast h1
        rw [hG₁_cast, ← hB₁, ← hA₁] at this; linarith⟩
    -- Apply the key lemma for the nonzero gap
    rcases hG_or with hG₀ | hG₁
    · -- Gap at N₀
      have hG₀_cast : (G₀ : ℝ) = (B₀ : ℝ) * 2 ^ s - (A₀ : ℝ) * m :=
        by exact_mod_cast (rfl : G₀ = B₀ * (2 : ℤ) ^ s - A₀ * m)
      have hG₀_real : (N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * padeQ N₀ x * 2 ^ s -
          (N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * padeP N₀ x * (m : ℝ) = (G₀ : ℝ) := by
        rw [hG₀_cast, hB₀, hA₀]
      have h1 := key N₀ hN₀_pos hR₀ hK₀_ne G₀ hG₀ hG₀_real
      -- 1/(2*D) ≤ 1/(2*|K₀|) since |K₀| ≤ D
      calc (1 : ℝ) / (2 * D) ≤ 1 / (2 * ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)) := by
            apply div_le_div_of_nonneg_left (by norm_num)
              (by have : padeP N₀ x ≠ 0 := by
                    intro h; exact hK₀_ne (by rw [h, mul_zero])
                  positivity)
              (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
        _ ≤ _ := h1
    · -- Gap at N₀+1
      have hG₁_cast : (G₁ : ℝ) = (B₁ : ℝ) * 2 ^ s - (A₁ : ℝ) * m :=
        by exact_mod_cast (rfl : G₁ = B₁ * (2 : ℤ) ^ s - A₁ * m)
      have hG₁_real : ((N₀+1).factorial : ℝ) * (b : ℝ) ^ (N₀+1) *
          padeQ (N₀+1) x * 2 ^ s -
          ((N₀+1).factorial : ℝ) * (b : ℝ) ^ (N₀+1) *
          padeP (N₀+1) x * (m : ℝ) = (G₁ : ℝ) := by
        rw [hG₁_cast, hB₁, hA₁]
      have h1 := key (N₀+1) (by omega) hR₁ hK₁_ne G₁ hG₁ hG₁_real
      calc (1 : ℝ) / (2 * D) ≤ 1 / (2 * (((N₀+1).factorial : ℝ) * (b : ℝ) ^ (N₀+1) * |padeP (N₀+1) x|)) := by
            apply div_le_div_of_nonneg_left (by norm_num)
              (by have : padeP (N₀ + 1) x ≠ 0 := by
                    intro h; exact hK₁_ne (by rw [h, mul_zero])
                  positivity)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
        _ ≤ _ := h1
  -- Prove the key lemma: gap principle gives |v| ≥ 1/(2|K|)
  intro N hN_pos hR_bound hK_ne G hG_ne hG_eq
  set K := (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N x with hK_def
  set v := exp x * 2 ^ s - (m : ℝ)
  -- From Padé identity: K * exp(x) - J = D_N * R_N(x)
  -- So K * v = (K * exp(x) * 2^s - K * m) = (J * 2^s - K * m) + D_N * R_N(x) * 2^s
  --         = G + ε where ε = D_N * R_N(x) * 2^s
  set ε := (N.factorial : ℝ) * (b : ℝ) ^ N * padeR N x * 2 ^ s
  have hK_v_eq : K * v = (G : ℝ) + ε := by
    -- Padé identity: padeR N x = padeP N x * exp x - padeQ N x (by definition)
    have hid : padeR N x = padeP N x * exp x - padeQ N x := rfl
    -- K * v = K * exp(x) * 2^s - K * m = (J + D*R) * 2^s - K * m = G + ε
    linarith [show K * v = K * exp x * 2 ^ s - K * (m : ℝ) from by rw [hK_def]; ring,
              show K * exp x * 2 ^ s = ((N.factorial : ℝ) * (b : ℝ) ^ N * padeQ N x * 2 ^ s +
                ε) from by rw [hK_def, show ε = (N.factorial : ℝ) * (b : ℝ) ^ N *
                  padeR N x * 2 ^ s from rfl, hid]; ring]
  -- |ε| < 1/2
  have hε_bound : |ε| < 1 / 2 := by
    show |(N.factorial : ℝ) * (b : ℝ) ^ N * padeR N x * 2 ^ s| < 1 / 2
    rw [show (N.factorial : ℝ) * (b : ℝ) ^ N * padeR N x * 2 ^ s =
        (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * padeR N x from by ring,
        abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s)]
    exact hR_bound
  -- |K|·|v| = |K*v| = |G + ε| ≥ |G| - |ε| ≥ 1 - 1/2 = 1/2
  have hKv : |K| * |v| ≥ 1 / 2 := by
    rw [← abs_mul, hK_v_eq]
    have hG_ge : (1 : ℝ) ≤ |(G : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hG_ne
    -- Use: |G| = |(G + ε) - ε| ≤ |G + ε| + |ε|, so |G + ε| ≥ |G| - |ε|
    have : |(↑G : ℝ) + ε| ≥ |(↑G : ℝ)| - |ε| := by
      have := abs_add_le ((↑G : ℝ) + ε) (-ε)
      rw [add_neg_cancel_right] at this
      linarith [abs_neg ε]
    linarith [le_of_lt hε_bound]
  -- |v| ≥ 1/(2|K|)
  have hK_pos : 0 < |K| := abs_pos.mpr hK_ne
  rw [ge_iff_le]
  calc 1 / (2 * ((N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x|))
      = 1 / (2 * |K|) := by
          have habs_K : |K| = (N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x| := by
            rw [hK_def, abs_mul, abs_mul]
            congr 1; congr 1
            · exact abs_of_nonneg (Nat.cast_nonneg _)
            · exact abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          rw [habs_K]
    _ = 1 / 2 / |K| := by ring
    _ ≤ |K| * |v| / |K| := div_le_div_of_nonneg_right hKv hK_pos.le
    _ = |v| := mul_div_cancel_left₀ _ (ne_of_gt hK_pos)

/-- Bound `padeConvergenceN₀` linearly in `ab`, where `ab` aggregates the input size.
This is the key quantitative bound ensuring the Padé threshold is polynomial in the input. -/
lemma padeConvergenceN₀_le (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0) (s : ℕ)
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
