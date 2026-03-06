import Flean.NumberTheory.PadeExpDefs
import Flean.Util

/-! # Padé approximation to `exp(x)` — effective irrationality measure

Building on the Padé definitions and remainder bound from `PadeExpDefs.lean`,
this file proves an effective lower bound on `|exp(a/b) · 2^s - m|` for all
integers `m` and nonzero rationals `a/b`.

## Key results

- `pade_scaled_bound_by_K_d`: algebraic bound on scaled remainder
- `pade_scaled_remainder_small`: convergence of scaled remainder to 0
- Cross product recurrence: `padeCross_ne_zero`
- `pade_not_both_zero`: consecutive Padé integers can't both match same m
- `padeConvergenceN₀_le`: effective threshold ≤ 27·ab
- `pade_effective_delta`: effective delta with gap principle
-/

open Real Finset BigOperators

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
    have hm_N : m - N = N - k := by omega
    have hm_N1 : m - (N - 1) = N - k + 1 := by omega
    rw [hm_N] at h1; rw [hm_N1] at h2
    rw [pascal]
    set A := m.choose N
    set B := m.choose (N - 1)
    set C1 := m.choose (N + 1)
    -- Work in ℤ to avoid ℕ subtraction pain
    -- Need k*(k-1) in the goal; handle k=0 separately since zify needs 1 ≤ k
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp at h1 h2 ⊢; nlinarith [h1, h2]
    · zify [hkN, hk1] at h1 h2 ⊢
      nlinarith [h1, h2]
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
        = Real.exp (↑(n * ab) * 1) := by push_cast [Int.cast_natCast]; ring_nf
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

/-! ## Generalized effective delta for arbitrary positive integer multipliers

The standard `pade_effective_delta` bounds `|exp(a/b) · 2^s - m|` from below.
For the log termination proof, we need `|exp(a/b) · c - m|` for arbitrary
positive integer `c` (specifically `c = y.den` for the rational `y` whose log
we compute). The proof is identical — the `2^s` in the Padé gap argument is
only used as a nonzero integer multiplier.
-/

/-- Generalization of `pade_not_both_zero`: consecutive Padé integers can't both
satisfy `J_N · c = K_N · d` for any nonzero integer `c`. -/
private theorem pade_not_both_zero_nat (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0)
    (N : ℕ) (hN : 0 < N) (c : ℕ) (hc : 0 < c) (d : ℤ) :
    let x := (a : ℝ) / (b : ℝ)
    let D := fun n => (n.factorial : ℝ) * (b : ℝ) ^ n
    let K := fun n => D n * padeP n x
    let J := fun n => D n * padeQ n x
    ¬(J N * c = K N * d ∧ J (N + 1) * c = K (N + 1) * d) := by
  simp only
  set x := (a : ℝ) / (b : ℝ) with hx_def
  set D := fun n => (n.factorial : ℝ) * (b : ℝ) ^ n
  set K := fun n => D n * padeP n x
  set J := fun n => D n * padeQ n x
  intro ⟨h1, h2⟩
  have hx_ne : x ≠ 0 := by
    simp only [hx_def, ne_eq, div_eq_zero_iff, Int.cast_eq_zero, Nat.cast_eq_zero]
    exact fun h => h.elim (fun h => ha h) (fun h => by omega)
  have hc_ne : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hDN_ne : D N ≠ 0 := ne_of_gt (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos N))
    (pow_pos (Nat.cast_pos.mpr hb) N))
  have hDN1_ne : D (N + 1) ≠ 0 := ne_of_gt (mul_pos
    (Nat.cast_pos.mpr (Nat.factorial_pos (N + 1)))
    (pow_pos (Nat.cast_pos.mpr hb) (N + 1)))
  -- Cancel D to get Q·c = P·d
  have hQP_N : padeQ N x * (c : ℝ) = padeP N x * (d : ℝ) :=
    mul_left_cancel₀ hDN_ne (by linarith [h1])
  have hQP_N1 : padeQ (N + 1) x * (c : ℝ) = padeP (N + 1) x * (d : ℝ) :=
    mul_left_cancel₀ hDN1_ne (by linarith [h2])
  -- Cross multiply and cancel c: Q_N·P_{N+1} = Q_{N+1}·P_N
  have hcross : padeQ N x * padeP (N + 1) x = padeQ (N + 1) x * padeP N x :=
    mul_right_cancel₀ hc_ne (by
      calc padeQ N x * padeP (N + 1) x * (c : ℝ)
          = padeQ N x * (c : ℝ) * padeP (N + 1) x := by ring
        _ = padeP N x * (d : ℝ) * padeP (N + 1) x := by rw [hQP_N]
        _ = padeP (N + 1) x * (d : ℝ) * padeP N x := by ring
        _ = padeQ (N + 1) x * (c : ℝ) * padeP N x := by rw [hQP_N1]
        _ = padeQ (N + 1) x * padeP N x * (c : ℝ) := by ring)
  exact pade_cross_product_ne_zero N hN x hx_ne (by linarith)

/-- Generalization of `pade_K_ne_zero`: if the scaled remainder times `c` is `< 1/2`,
then `K_N = N!·b^N·P_N(a/b) ≠ 0`. -/
private lemma pade_K_ne_zero_nat (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0)
    (c : ℕ) (hc : 0 < c)
    (N : ℕ) (hN : 0 < N)
    (hR : (N.factorial : ℝ) * (b : ℝ) ^ N * (c : ℝ) *
      |padeR N ((a : ℝ) / (b : ℝ))| < 1 / 2) :
    (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N ((a : ℝ) / (b : ℝ)) ≠ 0 := by
  set x := (a : ℝ) / (b : ℝ) with hx_def
  set F := (N.factorial : ℝ) * (b : ℝ) ^ N with hF_def
  have hF_pos : 0 < F := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos N))
    (pow_pos (Nat.cast_pos.mpr hb) N)
  intro hK
  have hP : padeP N x = 0 := by
    rcases mul_eq_zero.mp hK with h | h
    · exact absurd h (ne_of_gt hF_pos)
    · exact h
  have hJ_eq : F * padeQ N x = -(F * padeR N x) := by
    have : F * padeR N x = F * padeP N x * exp x - F * padeQ N x := by
      rw [show padeR N x = padeP N x * exp x - padeQ N x from rfl]; ring
    rw [hP, mul_zero, zero_mul, zero_sub] at this; linarith
  have hJ_small : |F * padeQ N x| < 1 := by
    rw [hJ_eq, abs_neg, abs_mul, abs_of_pos hF_pos]
    have hc_ge : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    nlinarith [abs_nonneg (padeR N x)]
  obtain ⟨J, hJ_int⟩ := padeQ_clears a b hb N
  change F * padeQ N x = ↑J at hJ_int
  have hJ_zero : J = 0 := by
    by_contra hJ_ne
    have : (1 : ℝ) ≤ |(J : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hJ_ne
    linarith [show |F * padeQ N x| = |(J : ℝ)| by rw [hJ_int]]
  have hQ : padeQ N x = 0 := by
    have : F * padeQ N x = 0 := by rw [hJ_int, hJ_zero, Int.cast_zero]
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hF_pos)
  have hx_ne : x ≠ 0 := by
    simp only [hx_def, ne_eq, div_eq_zero_iff, Int.cast_eq_zero, Nat.cast_eq_zero]
    exact fun h => h.elim (fun h => ha h) (fun h => by omega)
  rcases lt_or_gt_of_ne hx_ne with hlt | hgt
  · exact absurd hP (ne_of_gt (padeP_pos_of_neg N hN x hlt))
  · exact absurd hQ (ne_of_gt (padeQ_pos N hN x hgt))

/-- Effective distance bound for `exp(a/b) · c` from integers, where `c` is any
positive integer (not just a power of 2).

Uses `padeConvergenceN₀(a, b, t)` with `t = ⌈log₂ c⌉` to ensure the Padé
remainder scaled by `c` is `< 1/2`, then applies the standard gap principle. -/
theorem pade_effective_delta_nat (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0)
    (c : ℕ) (hc : 0 < c) :
    let t := Nat.log 2 c + 1
    let N₀ := padeConvergenceN₀ a b t
    let x := (a : ℝ) / (b : ℝ)
    let D := max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)
                 (((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) * |padeP (N₀ + 1) x|)
    0 < D ∧ ∀ m : ℤ,
      |Real.exp x * (c : ℝ) - (m : ℝ)| ≥ 1 / (2 * D) := by
  simp only
  set t := Nat.log 2 c + 1
  set N₀ := padeConvergenceN₀ a b t
  set x := (a : ℝ) / (b : ℝ) with hx_def
  have hN₀_pos := padeConvergenceN₀_pos a b t
  -- c < 2^t, so remainder scaled by c < remainder scaled by 2^t < 1/2
  have hc_lt_2t : c < 2 ^ t := Nat.lt_pow_succ_log_self (by norm_num) c
  have hc_le_2t : (c : ℝ) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast le_of_lt hc_lt_2t
  have hR₀_2t := pade_scaled_remainder_effective a b hb t N₀ (le_refl _) hN₀_pos
  have hR₁_2t := pade_scaled_remainder_effective a b hb t (N₀ + 1) (by omega) (by omega)
  rw [← hx_def] at hR₀_2t hR₁_2t
  -- Convert 2^t remainder bounds to c remainder bounds
  have hR₀ : (N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * (c : ℝ) *
      |padeR N₀ x| < 1 / 2 := by
    calc (N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * (c : ℝ) * |padeR N₀ x|
        ≤ (N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * (2 : ℝ) ^ t * |padeR N₀ x| := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hc_le_2t (by positivity)
          · exact abs_nonneg _
      _ < 1 / 2 := hR₀_2t
  have hR₁ : ((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) * (c : ℝ) *
      |padeR (N₀ + 1) x| < 1 / 2 := by
    calc ((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) * (c : ℝ) * |padeR (N₀ + 1) x|
        ≤ ((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) * (2 : ℝ) ^ t *
          |padeR (N₀ + 1) x| := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hc_le_2t (by positivity)
          · exact abs_nonneg _
      _ < 1 / 2 := hR₁_2t
  have hK₀_ne := pade_K_ne_zero_nat a b hb ha c hc N₀ hN₀_pos hR₀
  have hK₁_ne := pade_K_ne_zero_nat a b hb ha c hc (N₀ + 1) (by omega) hR₁
  set D := max ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)
               (((N₀ + 1).factorial : ℝ) * (b : ℝ) ^ (N₀ + 1) * |padeP (N₀ + 1) x|)
  have hD_pos : 0 < D := lt_max_of_lt_left (by
    have : padeP N₀ x ≠ 0 := by
      intro h; exact hK₀_ne (by rw [h, mul_zero])
    positivity)
  refine ⟨hD_pos, fun m => ?_⟩
  -- Use pade_not_both_zero_nat: at least one gap is nonzero
  obtain ⟨A₀, hA₀⟩ := padeP_clears a b hb N₀
  obtain ⟨A₁, hA₁⟩ := padeP_clears a b hb (N₀ + 1)
  obtain ⟨B₀, hB₀⟩ := padeQ_clears a b hb N₀
  obtain ⟨B₁, hB₁⟩ := padeQ_clears a b hb (N₀ + 1)
  rw [← hx_def] at hA₀ hA₁ hB₀ hB₁
  set G₀ := B₀ * (c : ℤ) - A₀ * m
  set G₁ := B₁ * (c : ℤ) - A₁ * m
  have hG_or : G₀ ≠ 0 ∨ G₁ ≠ 0 := by
    by_contra h; push_neg at h; obtain ⟨h0, h1⟩ := h
    exact pade_not_both_zero_nat a b hb ha N₀ hN₀_pos c hc m ⟨by
      have hG₀_cast : (G₀ : ℝ) = (B₀ : ℝ) * (c : ℝ) - (A₀ : ℝ) * m := by
        simp only [G₀]; push_cast [Int.cast_natCast]; ring
      have := show (G₀ : ℝ) = 0 from by exact_mod_cast h0
      rw [hG₀_cast, ← hB₀, ← hA₀] at this; linarith, by
      have hG₁_cast : (G₁ : ℝ) = (B₁ : ℝ) * (c : ℝ) - (A₁ : ℝ) * m := by
        simp only [G₁]; push_cast [Int.cast_natCast]; ring
      have := show (G₁ : ℝ) = 0 from by exact_mod_cast h1
      rw [hG₁_cast, ← hB₁, ← hA₁] at this; linarith⟩
  -- Apply gap principle for the nonzero gap
  suffices key : ∀ N, 0 < N →
      (N.factorial : ℝ) * (b : ℝ) ^ N * (c : ℝ) * |padeR N x| < 1 / 2 →
      (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N x ≠ 0 →
      ∀ G : ℤ, G ≠ 0 →
      (N.factorial : ℝ) * (b : ℝ) ^ N * padeQ N x * (c : ℝ) -
        (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N x * (m : ℝ) = (G : ℝ) →
      |exp x * (c : ℝ) - (m : ℝ)| ≥
        1 / (2 * ((N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x|)) by
    rcases hG_or with hG₀ | hG₁
    · have hG₀_real : (N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * padeQ N₀ x * (c : ℝ) -
          (N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * padeP N₀ x * (m : ℝ) = (G₀ : ℝ) := by
        have : (G₀ : ℝ) = (B₀ : ℝ) * (c : ℝ) - (A₀ : ℝ) * m := by
          simp only [G₀]; push_cast [Int.cast_natCast]; ring
        rw [this, hB₀, hA₀]
      calc (1 : ℝ) / (2 * D)
          ≤ 1 / (2 * ((N₀.factorial : ℝ) * (b : ℝ) ^ N₀ * |padeP N₀ x|)) := by
            apply div_le_div_of_nonneg_left (by norm_num)
              (by have : padeP N₀ x ≠ 0 := by intro h; exact hK₀_ne (by rw [h, mul_zero])
                  positivity)
              (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
        _ ≤ _ := key N₀ hN₀_pos hR₀ hK₀_ne G₀ hG₀ hG₀_real
    · have hG₁_real : ((N₀+1).factorial : ℝ) * (b : ℝ) ^ (N₀+1) *
          padeQ (N₀+1) x * (c : ℝ) -
          ((N₀+1).factorial : ℝ) * (b : ℝ) ^ (N₀+1) *
          padeP (N₀+1) x * (m : ℝ) = (G₁ : ℝ) := by
        have : (G₁ : ℝ) = (B₁ : ℝ) * (c : ℝ) - (A₁ : ℝ) * m := by
          simp only [G₁]; push_cast [Int.cast_natCast]; ring
        rw [this, hB₁, hA₁]
      calc (1 : ℝ) / (2 * D)
          ≤ 1 / (2 * (((N₀+1).factorial : ℝ) * (b : ℝ) ^ (N₀+1) * |padeP (N₀+1) x|)) := by
            apply div_le_div_of_nonneg_left (by norm_num)
              (by have : padeP (N₀+1) x ≠ 0 := by intro h; exact hK₁_ne (by rw [h, mul_zero])
                  positivity)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
        _ ≤ _ := key (N₀+1) (by omega) hR₁ hK₁_ne G₁ hG₁ hG₁_real
  -- Prove the key gap principle
  intro N hN_pos hR_bound hK_ne G hG_ne hG_eq
  set K := (N.factorial : ℝ) * (b : ℝ) ^ N * padeP N x with hK_def
  set v := exp x * (c : ℝ) - (m : ℝ)
  set ε := (N.factorial : ℝ) * (b : ℝ) ^ N * padeR N x * (c : ℝ)
  have hK_v_eq : K * v = (G : ℝ) + ε := by
    have hid : padeR N x = padeP N x * exp x - padeQ N x := rfl
    linarith [show K * v = K * exp x * (c : ℝ) - K * (m : ℝ) from by rw [hK_def]; ring,
              show K * exp x * (c : ℝ) = ((N.factorial : ℝ) * (b : ℝ) ^ N *
                padeQ N x * (c : ℝ) + ε) from by
                rw [hK_def, show ε = (N.factorial : ℝ) * (b : ℝ) ^ N *
                  padeR N x * (c : ℝ) from rfl, hid]; ring]
  have hε_bound : |ε| < 1 / 2 := by
    show |(N.factorial : ℝ) * (b : ℝ) ^ N * padeR N x * (c : ℝ)| < 1 / 2
    rw [show (N.factorial : ℝ) * (b : ℝ) ^ N * padeR N x * (c : ℝ) =
        (N.factorial : ℝ) * (b : ℝ) ^ N * (c : ℝ) * padeR N x from by ring,
        abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (N.factorial : ℝ) * (b : ℝ) ^ N * (c : ℝ))]
    exact hR_bound
  have hKv : |K| * |v| ≥ 1 / 2 := by
    rw [← abs_mul, hK_v_eq]
    have hG_ge : (1 : ℝ) ≤ |(G : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hG_ne
    have : |(↑G : ℝ) + ε| ≥ |(↑G : ℝ)| - |ε| := by
      have := abs_add_le ((↑G : ℝ) + ε) (-ε)
      rw [add_neg_cancel_right] at this
      linarith [abs_neg ε]
    linarith [le_of_lt hε_bound]
  have hK_pos : 0 < |K| := abs_pos.mpr hK_ne
  rw [ge_iff_le]
  calc 1 / (2 * ((N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x|))
      = 1 / (2 * |K|) := by
          have : |K| = (N.factorial : ℝ) * (b : ℝ) ^ N * |padeP N x| := by
            rw [hK_def, abs_mul, abs_mul]
            congr 1; congr 1
            · exact abs_of_nonneg (Nat.cast_nonneg _)
            · exact abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          rw [this]
    _ = 1 / 2 / |K| := by ring
    _ ≤ |K| * |v| / |K| := div_le_div_of_nonneg_right hKv hK_pos.le
    _ = |v| := mul_div_cancel_left₀ _ (ne_of_gt hK_pos)
