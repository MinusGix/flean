import Flean.NumberTheory.ExpEffectiveBound
import Flean.NumberTheory.AlternatingChooseSum
import Mathlib.Analysis.SpecialFunctions.Exponential

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
  ring

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
  have hchoose : (2 * N - j).choose (N - j) = (2 * N - j).choose N :=
    (Nat.choose_symm (show N ≤ 2 * N - j by omega)).symm
  rw [← hchoose]
  exact_mod_cast key

/-- For `N < j ≤ 2N`, the Cauchy product coefficient vanishes (Padé condition). -/
private theorem padeProdCoeff_eq_zero (N j : ℕ) (hN : 0 < N) (hjN : N < j) (hj2N : j ≤ 2 * N) :
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

/-- The Padé remainder is bounded:

`|R_N(x)| ≤ (2|x|)^{2N+1} · 2·exp(2|x|) / ((2N+1) · (N!)²)` -/
theorem padeR_bound (N : ℕ) (hN : 0 < N) (x : ℝ) :
    |padeR N x| ≤ (2 * |x|) ^ (2 * N + 1) * (2 * exp (2 * |x|)) /
      ((2 * N + 1 : ℕ) * ((N.factorial : ℝ) ^ 2)) := by
  -- INFORMAL PROOF SKETCH:
  --
  -- Step 1 (Padé condition): The first 2N+1 Taylor coefficients of R_N vanish.
  --   For j ≤ N: use `alternating_choose_sum` to show coeff = C(2N-j,N)/j! - C(2N-j,N)/j! = 0.
  --   For N < j ≤ 2N: use `alternating_choose_sum_zero` to show coeff = 0.
  --   [Needs HELPER: `pade_taylor_coeff_vanish`]
  --
  -- Step 2 (Tail bound): R_N(x) = Σ_{j≥2N+1} c_j · x^j where each |c_j| ≤ C(2N,N) · 2^j / j!
  --   But wait — the tail series is NOT just |x|^j but involves the REAL exp function.
  --   We need the HasSum form: R_N = P_N·exp - Q_N, and exp is given by its Taylor series.
  --   [Needs HELPER: `padeR_hasSum` — express R_N as a convergent tail sum]
  --
  -- Step 3 (Geometric tail): Σ_{j≥M} a^j/j! ≤ a^M/M! · exp(a) for a ≥ 0.
  --   [Needs HELPER: `exp_tail_sum_bound`]
  --
  -- Step 4 (Central binomial): C(2N,N) ≤ 4^N.
  --   [Needs HELPER: `central_binom_le_four_pow` — might be in Mathlib]
  --
  -- Step 5 (Factorial relation): (2N+1)! ≥ (2N+1)·(N!)²
  --   From C(2N,N) = (2N)!/(N!)² ≥ 1, so (2N)! ≥ (N!)².
  --   [Needs HELPER: `two_N_plus_one_factorial_ge`]
  --
  -- Assembly:
  --   |R_N(x)| ≤ C(2N,N) · (2|x|)^{2N+1}/(2N+1)! · exp(2|x|)   [Steps 1-3]
  --            ≤ 4^N · (2|x|)^{2N+1} · exp(2|x|) / (2N+1)!       [Step 4]
  --            ≤ 4^N · (2|x|)^{2N+1} · exp(2|x|) / ((2N+1)·(N!)²) [Step 5]
  --
  -- The stated bound has an extra factor of 2·exp(2|x|) which is ≥ 4^N·exp(2|x|)/(N!)²... hmm
  -- Actually `4^N/(N!)²` is NOT bounded by 2. This bound form is wrong.
  --
  -- Let me re-check: the RHS is (2|x|)^{2N+1} · 2 · exp(2|x|) / ((2N+1)·(N!)²).
  -- My derivation gives 4^N · (2|x|)^{2N+1} · exp(2|x|) / ((2N+1)·(N!)²).
  -- The stated bound is WEAKER by a factor of 2/4^N, which is NOT weaker for N ≥ 1!
  -- 4^N > 2 for N ≥ 1. So the stated bound is TIGHTER than what I can prove.
  --
  -- FIX: Change the statement to include the 4^N factor, or use the tight integral bound.
  -- The tight bound is |R_N(x)| ≤ |x|^{2N+1} · exp(|x|) / ((2N+1)·(N!)²).
  -- That IS what we'd get from the integral representation directly.
  --
  -- For the tail-sum approach, the tightest we can get without the integral is:
  -- |R_N(x)| ≤ C(2N,N) · Σ_{j≥2N+1} |x|^j / j!  (using each c_j ≤ C(2N,N)/j!)
  --          ≤ C(2N,N) · |x|^{2N+1}/(2N+1)! · exp(|x|)
  --          ≤ |x|^{2N+1} · exp(|x|) · C(2N,N) / (2N+1)!
  --          = |x|^{2N+1} · exp(|x|) / ((2N+1) · (N!)²)
  --
  -- That last step uses C(2N,N)/(2N)! = 1/(N!)², i.e. C(2N,N)/(2N+1)! = 1/((2N+1)·(N!)²).
  -- Wait: C(2N,N) = (2N)!/(N!)², so C(2N,N)/(2N+1)! = (2N)!/((N!)²·(2N+1)!) = 1/((2N+1)·(N!)²).
  -- YES! So the tight bound IS provable from the tail-sum approach!
  --
  -- KEY: the coefficient bound is |c_j| ≤ C(2N,N)/j!, NOT C(2N,N)·2^j/j!.
  -- This is because:
  --   c_j = (1/j!) · Σ_{k=0}^N (-1)^k C(j,k) C(2N-k,N)
  -- and |c_j| ≤ (1/j!) · Σ_{k=0}^N C(j,k) C(2N-k,N)
  --          ≤ (1/j!) · C(2N,N) · Σ_{k=0}^N C(j,k)
  --          ≤ (1/j!) · C(2N,N) · 2^j   ... NO this gives 2^j, not 1.
  --
  -- Hmm. With the alternating signs, we get CANCELLATION, which is why the bound is tighter.
  -- Without exploiting cancellation, we only get the C(2N,N)·2^j/j! bound.
  -- So the tail sum gives: Σ_{j≥2N+1} C(2N,N)·(2|x|)^j/j! = C(2N,N) · tail of exp(2|x|)
  --                       ≤ C(2N,N) · (2|x|)^{2N+1}/(2N+1)! · exp(2|x|)
  --                       = (2|x|)^{2N+1} · exp(2|x|) / ((2N+1)·(N!)²)
  --
  -- And that IS the stated bound (with factor 2·exp(2|x|) being ≥ exp(2|x|)).
  -- The stated bound has the "2 · exp(2|x|)" factor. My derivation gives "exp(2|x|)".
  -- So the stated bound IS provable! (It's weaker by a factor of 2, which is fine.)
  --
  -- REVISED ASSEMBLY:
  --   |R_N(x)| ≤ C(2N,N) · (2|x|)^{2N+1}/(2N+1)! · exp(2|x|)
  --            = (2|x|)^{2N+1} · exp(2|x|) / ((2N+1)·(N!)²)
  --            ≤ (2|x|)^{2N+1} · (2·exp(2|x|)) / ((2N+1)·(N!)²)   [since 1 ≤ 2]
  --            = RHS. ✓
  --
  -- HELPERS NEEDED (in order of dependency):
  -- 1. `pade_product_coeff`: coefficient of x^j in P_N·exp is (1/j!)·Σ_{k} (-1)^k C(j,k) C(2N-k,N)
  -- 2. `pade_coeff_abs_le`: |coeff of x^j in R_N| ≤ C(2N,N)/j! for j ≥ 2N+1
  --    (NOT the tight bound, but the one using |(-1)^k C(j,k) C(2N-k,N)| ≤ C(j,k)·C(2N,N))
  --    Wait, the sum goes to N, and Σ_{k=0}^N C(j,k) ≤ 2^j.
  --    So |coeff| ≤ C(2N,N)·2^j/j!. OK so the bound involves 2^j.
  --    Then Σ_{j≥2N+1} C(2N,N)·2^j·|x|^j/j! = C(2N,N)·Σ (2|x|)^j/j!.
  -- 3. `exp_tail_sum_le`: Σ_{j≥M} a^j/j! ≤ a^M/M! · exp(a) for a ≥ 0
  -- 4. `central_binom_div_factorial`: C(2N,N)/(2N+1)! = 1/((2N+1)·(N!)²)
  --
  -- The approach works. The key difficulty is expressing R_N as a formal power series
  -- and showing it converges (HasSum). This requires connecting padeP, padeQ, exp
  -- via their power series representations.
  --
  -- ALTERNATIVE (SIMPLER): Instead of the HasSum approach, use a DIRECT bound:
  -- |P_N(x)·exp(x) - Q_N(x)| = |Σ_k c_k ((-x)^k·exp(x) - x^k)|
  -- This doesn't simplify.
  --
  -- SIMPLEST PATH: Prove the integral representation and bound the integral.
  -- R_N(x) = x^{2N+1}/(N!)² · ∫₀¹ t^N·(1-t)^N·exp(t·x) dt  (up to sign)
  -- Then |R_N(x)| ≤ |x|^{2N+1}/(N!)² · ∫₀¹ t^N·(1-t)^N·exp(|x|) dt
  --              = |x|^{2N+1}·exp(|x|)/(N!)² · B(N+1,N+1)
  --              = |x|^{2N+1}·exp(|x|)/(N!)² · N!²/(2N+1)!
  --              = |x|^{2N+1}·exp(|x|)/(2N+1)!
  -- This is TIGHT and CLEAN. Easier to prove than the tail-sum approach
  -- if we can establish the integral representation.
  --
  -- INTEGRAL REPRESENTATION PROOF (separate theorem `padeR_integral`):
  -- Define I_N(x) = ∫₀¹ t^N·(1-t)^N·exp(t·x) dt.
  -- By integration by parts twice:
  --   I_N'(x) = ∫₀¹ t^{N+1}·(1-t)^N·exp(tx) dt
  -- More precisely, define f(x) = x^{2N+1}·I_N(x).
  -- Show f satisfies the same ODE as R_N: f' - f = something.
  -- Actually the standard proof is via REPEATED integration by parts:
  --   ∫₀¹ t^N(1-t)^N·exp(tx) dt, integrate by parts N times on t^N factor,
  --   then N times on (1-t)^N factor, to get a polynomial in exp(x).
  -- This gives: (N!)²·I_N(x) = Σ ... = P_N(-x)·exp(x) - P_N(x)... hmm.
  --
  -- Actually the standard identity is:
  --   R_N(x) = (-x)^{2N+1}/(N!)² · ∫₀¹ t^N(1-t)^N exp(tx) dt
  -- Proof by induction on N, integrating by parts.
  --
  -- This is perhaps 50-80 lines of Lean. Let me plan it.
  --
  -- DECISION: Prove via the tail-sum approach (more elementary, avoids integrals).
  -- The integral approach needs Mathlib's MeasureTheory and intervalIntegral.
  -- The tail-sum approach needs HasSum for exp (available: Real.hasSum_exp or similar).
  sorry

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
      push_cast; exact_mod_cast q.num_div_den.symm
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

/-- The scaled remainder `N! · b^N · 2^s · |R_N(a/b)|` is `< 1/2` for large `N`.
Uses `padeR_bound` and `factorial_dominates`. -/
theorem pade_scaled_remainder_small (a : ℤ) (b : ℕ) (hb : 0 < b) (s : ℕ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N, N₀ ≤ N →
      (N.factorial : ℝ) * (b : ℝ) ^ N * 2 ^ s * |padeR N ((a : ℝ) / (b : ℝ))| < 1 / 2 := by
  -- INFORMAL PROOF SKETCH:
  --
  -- From `padeR_bound` (using the (2|x|)^{2N+1}·2·exp(2|x|)/((2N+1)·(N!)²) form):
  --
  --   N!·b^N·2^s·|R_N(a/b)|
  --     ≤ N!·b^N·2^s · (2|a/b|)^{2N+1} · 2·exp(2|a/b|) / ((2N+1)·(N!)²)
  --     = b^N · 2^s · 2·exp(2|a/b|) · (2|a/b|)^{2N+1} / ((2N+1)·N!)
  --     = b^N · 2^s · 2·exp(2|a/b|) · 2^{2N+1}·|a|^{2N+1} / (b^{2N+1}·(2N+1)·N!)
  --     = 2^{s+1} · exp(2|a/b|) · 2^{2N+1} · |a|^{2N+1} / (b^{N+1}·(2N+1)·N!)
  --
  -- Let C = 2^{s+1} · exp(2|a/b|) / b^{N+1}  (constant w.r.t. N... no, depends on N through b^{N+1})
  --
  -- Better: group as
  --   ≤ [2^{s+1} · exp(2|a/b|)] · [4|a|²/b]^N · 2|a|/b / ((2N+1)·N!)
  --   since 2^{2N+1}·|a|^{2N+1}/b^{N+1} = 2·(4|a|²/b)^N · |a|/b^{???}
  --   Hmm, let me just factor differently.
  --
  -- Set c = 4·|a|²·b (or similar). Then:
  --   (2|a/b|)^{2N+1} · b^N = 2^{2N+1}·|a|^{2N+1}·b^N / b^{2N+1}
  --                          = 2^{2N+1}·|a|^{2N+1} / b^{N+1}
  --
  -- The whole expression is:
  --   ≤ 2^{s+2} · exp(2|a/b|) · (2|a|)^{2N+1} / (b^{N+1} · (2N+1) · N!)
  --
  -- For this to go to 0 as N→∞: we need N! to dominate (2|a|)^{2N+1}/b^{N+1}.
  -- Write (2|a|)^{2N+1}/b^{N+1} = (2|a|)·((2|a|)²/b)^N = (2|a|)·(4|a|²/b)^N.
  -- So the expression is ≤ C · (4|a|²/b)^N / N! where C = 2^{s+2}·exp(2|a/b|)·2|a|/(2N+1).
  --
  -- Since N! grows faster than any c^N (factorial_dominates), this → 0.
  --
  -- Concretely: use `factorial_dominates` from ExpEffectiveBound.lean:
  --   `∃ N₀, ∀ p ≥ N₀, |c|^p / (p-1)! < 1`
  -- with c = 4·|a|²/b + 1 (or similar constant).
  --
  -- Then for N ≥ N₀: the expression is < 1/2 (by choosing N₀ large enough to absorb
  -- the constant factors 2^{s+2}·exp(2|a/b|)·2|a| as well).
  --
  -- HELPERS NEEDED:
  -- - `padeR_bound` (the theorem above)
  -- - `factorial_dominates` (already proved in ExpEffectiveBound.lean)
  -- - Basic algebra to bound the product
  --
  -- This is straightforward (~30-40 lines) once padeR_bound is proved.
  sorry

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
  simp [Finset.sum_range_succ, Finset.sum_range_zero]
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
      congr 1 <;> omega]
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
