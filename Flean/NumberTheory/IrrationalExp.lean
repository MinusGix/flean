import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Order.Floor

/-! # Irrationality of `exp` at nonzero rationals

We prove `irrational_exp_rat`: for nonzero `q : ℚ`, `Real.exp (q : ℝ)` is irrational.

This is the **algebraic part** of the Hermite-Lindemann theorem. The analytical part
(`exp_polynomial_approx`) is already in mathlib. We supply the algebraic scaffolding:
construct the linear polynomial `f = b·X - a` for `q = a/b`, show `q` is a root,
clear denominators, and derive a contradiction from prime divisibility.
-/

open Polynomial Complex Real

/-! ## Step 1: Polynomial setup -/

/-- The linear polynomial `f = (q.den : ℤ) · X - q.num` for a rational `q`.
This has `q` as a root and `f(0) = -q.num ≠ 0` when `q ≠ 0`. -/
noncomputable def expPoly (q : ℚ) : ℤ[X] :=
  C (q.den : ℤ) * X - C q.num

theorem expPoly_eval_zero (q : ℚ) : (expPoly q).eval 0 = -q.num := by
  simp [expPoly]

theorem expPoly_eval_zero_ne (q : ℚ) (hq : q ≠ 0) : (expPoly q).eval 0 ≠ 0 := by
  rw [expPoly_eval_zero]
  simp only [neg_ne_zero]
  exact Rat.num_ne_zero.mpr hq

theorem expPoly_ne_zero (q : ℚ) (hq : q ≠ 0) : expPoly q ≠ 0 := by
  intro h
  have := congr_arg (fun p => p.eval 0) h
  simp at this
  exact expPoly_eval_zero_ne q hq (by simpa [expPoly] using this)

theorem expPoly_natDegree (q : ℚ) (_hq : q ≠ 0) : (expPoly q).natDegree = 1 := by
  unfold expPoly
  have hden : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Rat.den_ne_zero q)
  rw [sub_eq_add_neg, ← map_neg C q.num]
  rw [natDegree_add_C, natDegree_C_mul_X _ hden]

/-! ## Step 2: `q` is a root of `expPoly q` -/

theorem expPoly_aeval_eq_zero (q : ℚ) :
    Polynomial.aeval (q : ℂ) (expPoly q) = 0 := by
  have hden : (q.den : ℂ) ≠ 0 := by exact_mod_cast Rat.den_ne_zero q
  have hq_cast : (q : ℂ) = (q.num : ℂ) / (q.den : ℂ) := by
    rw [Rat.cast_def]
  simp only [expPoly, map_sub, map_mul, aeval_C, aeval_X, hq_cast,
    algebraMap_int_eq, Int.coe_castRingHom]
  field_simp; push_cast; ring

theorem expPoly_mem_aroots (q : ℚ) (hq : q ≠ 0) :
    (q : ℂ) ∈ (expPoly q).aroots ℂ := by
  rw [Polynomial.mem_aroots]
  refine ⟨expPoly_ne_zero q hq, ?_⟩
  have h := expPoly_aeval_eq_zero q
  rwa [Polynomial.aeval_def] at h

/-! ## Step 3: Clearing denominators -/

-- For `g : ℤ[X]` with `natDegree ≤ d` and `q = a/b`:
-- `b^d * g(a/b)` is an integer (in any ℤ-algebra).
-- We prove this over ℂ.

/-- Monomial case: `b^d * (c * (a/b)^n) = c * a^n * b^(d-n)` as integers. -/
private theorem monomial_clear_denom (c : ℤ) (n : ℕ) (a : ℤ) (b : ℕ) (hb : (b : ℂ) ≠ 0)
    (d : ℕ) (hnd : n ≤ d) :
    (b : ℂ) ^ d * ((c : ℂ) * ((a : ℂ) / (b : ℂ)) ^ n) =
      ↑(c * a ^ n * (b : ℤ) ^ (d - n)) := by
  have hbz : (b : ℂ) ^ n ≠ 0 := pow_ne_zero _ hb
  rw [div_pow]
  field_simp
  rw [show (b : ℂ) ^ d = (b : ℂ) ^ n * (b : ℂ) ^ (d - n) from by
      rw [← pow_add]; congr 1; omega]
  push_cast; ring

theorem int_poly_clear_denom (g : ℤ[X]) (a : ℤ) (b : ℕ) (hb : b ≠ 0) (d : ℕ)
    (hdeg : g.natDegree ≤ d) :
    ∃ M : ℤ, (b : ℂ) ^ d * Polynomial.aeval ((a : ℂ) / (b : ℂ)) g = (M : ℂ) := by
  have hbc : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  refine ⟨∑ i ∈ Finset.range (d + 1), g.coeff i * a ^ i * (b : ℤ) ^ (d - i), ?_⟩
  -- Write g as a sum of monomials
  have hg := g.as_sum_range' (d + 1) (by omega)
  conv_lhs => rw [hg]
  rw [map_sum, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hid : i ≤ d := by simp [Finset.mem_range] at hi; omega
  simp only [Polynomial.aeval_monomial, algebraMap_int_eq, Int.coe_castRingHom]
  rw [monomial_clear_denom (g.coeff i) i a b hbc d hid]
  push_cast; ring

/-! ## Step 4: Factorial dominates exponential -/

theorem factorial_dominates (c : ℝ) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p → |c| ^ p / (p - 1).factorial < 1 := by
  by_cases hc : c = 0
  · -- c = 0: |0|^p = 0 for p ≥ 1
    use 1; intro p hp
    have : 0 < p := by omega
    simp [hc, zero_pow (by omega : p ≠ 0)]
  · -- c ≠ 0: |c| > 0. Use |c|^n/n! → 0 with ε = 1/(|c|+1)
    have hc_pos : 0 < |c| := abs_pos.mpr hc
    have htend := FloorSemiring.tendsto_pow_div_factorial_atTop (|c|)
    have heps : (0 : ℝ) < 1 / (|c| + 1) := div_pos one_pos (by linarith)
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend (1 / (|c| + 1)) heps
    use N + 1
    intro p hp
    have hpN : N ≤ p - 1 := Nat.le_sub_one_of_lt (by omega)
    have hsmall := hN (p - 1) hpN
    rw [dist_zero_right, Real.norm_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg _) _)
      (Nat.cast_nonneg _))] at hsmall
    have hpeq : |c| ^ p = |c| ^ (p - 1) * |c| := by
      rw [← pow_succ]; congr 1; omega
    calc |c| ^ p / ↑(p - 1).factorial
        = |c| ^ (p - 1) * |c| / ↑(p - 1).factorial := by rw [hpeq]
      _ = |c| ^ (p - 1) / ↑(p - 1).factorial * |c| := by ring
      _ < 1 / (|c| + 1) * |c| := by
          exact mul_lt_mul_of_pos_right hsmall hc_pos
      _ ≤ 1 := by
          have h1 : 0 < |c| + 1 := by linarith
          rw [div_mul_eq_mul_div, one_mul]
          exact le_of_lt (div_lt_one h1 |>.mpr (lt_add_one _))

/-! ## Step 5: Main theorem -/

theorem irrational_exp_rat (q : ℚ) (hq : q ≠ 0) : Irrational (Real.exp (q : ℝ)) := by
  -- Apply exp_polynomial_approx to the linear polynomial f = b·X - a
  set f := expPoly q
  have hf0 := expPoly_eval_zero_ne q hq
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  -- Assume for contradiction: exp(q) is rational, say P/Q
  rw [irrational_iff_ne_rational]
  intro P Q hQ hexp
  -- Set up key constants
  set a := q.num
  set b := q.den
  have hb_pos : 0 < b := q.den_pos
  have hb_ne : b ≠ 0 := by omega
  -- exp(q : ℂ) = P/Q
  have hexp_complex : Complex.exp (q : ℂ) = (P : ℂ) / (Q : ℂ) := by
    have := Complex.ofReal_exp (q : ℝ)
    rw [hexp] at this
    push_cast at this ⊢
    exact this.symm
  -- q is a root of f in ℂ
  have hroot := expPoly_mem_aroots q hq
  -- D = max of all relevant constants; factorial_dominates for D^2
  set D := max (max |(Q : ℝ)| (b : ℝ)) (max |c| 1) with hD_def
  obtain ⟨N_fac, hN_fac⟩ := factorial_dominates (D ^ 2)
  -- Choose large enough prime p
  set bound := max (max (f.eval 0).natAbs (Int.natAbs P)) (max b N_fac) + 1
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes bound
  have hp_f0 : (f.eval 0).natAbs < p := by omega
  have hp_P : (Int.natAbs P) < p := by omega
  have hp_b : b < p := by omega
  have hp_Nfac : N_fac ≤ p := by omega
  -- Get the approximation for this prime
  obtain ⟨n, hn_ndvd, gp, hgp_deg, hgp_bound⟩ := hc p (by omega) hp_prime
  -- The bound at root q
  have hbound := hgp_bound hroot
  -- gp has degree ≤ p - 1 (since f has degree 1)
  have hgp_deg' : gp.natDegree ≤ p - 1 := by
    rw [expPoly_natDegree q hq] at hgp_deg; omega
  -- Clear denominators: b^(p-1) * aeval(q : ℂ) gp is an integer
  obtain ⟨M, hM⟩ := int_poly_clear_denom gp a b hb_ne (p - 1) hgp_deg'
  -- The key integer
  set I := n * P * (b : ℤ) ^ (p - 1) - (p : ℤ) * Q * M
  -- Step A: I = Q * b^(p-1) * (n * exp(q) - p * gp(q)) in ℂ
  have hq_complex : (q : ℂ) = (a : ℂ) / (b : ℂ) := by
    rw [Rat.cast_def]
  -- Steps A-C: ‖I‖ < 1 (exp approximation bound * clearing denominators)
  have hI_lt_one : ‖(I : ℂ)‖ < 1 := by
    -- A: Show (I : ℂ) = Q * b^(p-1) * (n * exp(q) - p * gp(q))
    have hQne : (Q : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    have hbne : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb_ne
    have hval : (b : ℂ) ^ (p - 1) * Polynomial.aeval (↑↑q : ℂ) gp = (M : ℂ) := by
      rw [hq_complex]; exact hM
    have hI_eq : (I : ℂ) = (Q : ℂ) * (b : ℂ) ^ (p - 1) *
        (↑n * Complex.exp (q : ℂ) - ↑(p : ℤ) * Polynomial.aeval (q : ℂ) gp) := by
      push_cast [I]
      rw [hexp_complex, ← hval]
      field_simp
    -- B: Bound ‖...‖ using hbound
    have hsmul_eq : n • Complex.exp (↑↑q : ℂ) - (p : ℕ) • Polynomial.aeval (↑↑q : ℂ) gp =
        ↑n * Complex.exp (↑↑q : ℂ) - ↑(p : ℤ) * Polynomial.aeval (↑↑q : ℂ) gp := by
      simp only [zsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
    rw [hI_eq, norm_mul, norm_mul]
    -- ‖Q‖ * ‖b^(p-1)‖ * ‖...‖ ≤ |Q| * b^(p-1) * c^p/(p-1)! < 1
    have h_norm_bound : ‖↑n * Complex.exp (↑↑q : ℂ) - ↑(p : ℤ) * Polynomial.aeval (↑↑q : ℂ) gp‖ ≤
        c ^ p / ↑(p - 1).factorial := by
      rw [← hsmul_eq]; exact hbound
    have hQ_norm : ‖(Q : ℂ)‖ = |(Q : ℝ)| := by
      rw [Complex.norm_intCast]
    have hb_norm : ‖(b : ℂ) ^ (p - 1)‖ = (b : ℝ) ^ (p - 1) := by
      rw [norm_pow, Complex.norm_natCast]
    rw [hQ_norm, hb_norm]
    -- Goal: |Q:ℝ| * b^(p-1) * ‖exp approx‖ < 1
    -- Bound ‖exp approx‖ ≤ c^p / (p-1)! and then show |Q| * b^(p-1) * c^p / (p-1)! < 1
    calc |(Q : ℝ)| * (b : ℝ) ^ (p - 1) *
          ‖↑n * Complex.exp ↑↑q - ↑(p : ℤ) * Polynomial.aeval (↑↑q) gp‖
        ≤ |(Q : ℝ)| * (b : ℝ) ^ (p - 1) * (c ^ p / ↑(p - 1).factorial) :=
          mul_le_mul_of_nonneg_left h_norm_bound (mul_nonneg (abs_nonneg _)
            (pow_nonneg (Nat.cast_nonneg _) _))
      _ < 1 := by
          -- Use D = max(|Q| * |c|, b * |c|, 1), then bound by |D|^p / (p-1)! < 1
          -- Simplify: |Q| * b^(p-1) * c^p / (p-1)!
          --   = |Q| * c * (b * c)^(p-1) / (p-1)!  ... but c could be ≤ 0
          -- Just use: everything ≤ D^(2p) / (p-1)! with D large enough
          have hD_ge_Q : |(Q : ℝ)| ≤ D := le_max_of_le_left (le_max_left _ _)
          have hD_ge_b : (b : ℝ) ≤ D := le_max_of_le_left (le_max_right _ _)
          have hD_ge_c : |c| ≤ D := le_max_of_le_right (le_max_left _ _)
          have hD_ge_one : 1 ≤ D := le_max_of_le_right (le_max_right _ _)
          have hD_pos : 0 < D := lt_of_lt_of_le one_pos hD_ge_one
          have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
          -- |Q| * b^(p-1) ≤ D * D^(p-1) = D^p
          have h1 : |(Q : ℝ)| * (b : ℝ) ^ (p - 1) ≤ D ^ p := by
            calc |(Q : ℝ)| * (b : ℝ) ^ (p - 1)
                ≤ D * D ^ (p - 1) := by
                  apply mul_le_mul hD_ge_Q _ (pow_nonneg (Nat.cast_nonneg _) _) hD_nonneg
                  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hD_ge_b _
              _ = D ^ (p - 1 + 1) := by rw [pow_succ]; ring
              _ = D ^ p := by congr 1; omega
          -- c^p ≤ |c|^p ≤ D^p
          have h2 : c ^ p / ↑(p - 1).factorial ≤ D ^ p / ↑(p - 1).factorial := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            calc c ^ p ≤ |c| ^ p := abs_pow c p ▸ le_abs_self (c ^ p)
              _ ≤ D ^ p := pow_le_pow_left₀ (abs_nonneg _) hD_ge_c _
          -- D^p * (D^p / (p-1)!) = (D^2)^p / (p-1)! < 1
          calc |(Q : ℝ)| * (b : ℝ) ^ (p - 1) * (c ^ p / ↑(p - 1).factorial)
              ≤ D ^ p * (D ^ p / ↑(p - 1).factorial) := by
                apply mul_le_mul h1 h2
                  (le_trans (norm_nonneg _) h_norm_bound)
                  (pow_nonneg hD_nonneg _)
            _ = (D ^ 2) ^ p / ↑(p - 1).factorial := by
                rw [mul_div_assoc', ← pow_mul]; ring_nf
            _ ≤ |D ^ 2| ^ p / ↑(p - 1).factorial := by
                apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
                exact pow_le_pow_left₀ (pow_nonneg hD_nonneg _) (le_abs_self _) _
            _ < 1 := hN_fac p hp_Nfac
  -- Step D: Integer with |·| < 1 is 0
  have hI_zero : I = 0 := by
    by_contra hI_ne
    have : 1 ≤ ‖(I : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hI_ne
    linarith
  -- Step E: I = 0 means p | n * P * b^(p-1)
  have hdvd : (p : ℤ) ∣ n * P * (b : ℤ) ^ (p - 1) := by
    simp only [I] at hI_zero
    exact ⟨Q * M, by linarith⟩
  -- Step F: p doesn't divide n (given), P, or b^(p-1)
  have hP_ne : P ≠ 0 := by
    intro hP0; rw [hP0, Int.cast_zero, zero_div] at hexp
    exact absurd hexp (by positivity)
  have hp_ndvd_P : ¬(p : ℤ) ∣ P := by
    intro h
    have hP_pos : 0 < P.natAbs := Int.natAbs_pos.mpr hP_ne
    have := Int.natAbs_dvd_natAbs.mpr h
    rw [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd hP_pos this) (by omega)
  have hp_ndvd_bpow : ¬(p : ℤ) ∣ (b : ℤ) ^ (p - 1) := by
    intro h
    have := Int.Prime.dvd_pow' hp_prime h
    have hb_pos : (0 : ℤ) < b := by exact_mod_cast hb_pos
    have := Int.natAbs_dvd_natAbs.mpr this
    rw [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  -- Combine: p | n * (P * b^(p-1))
  have hdvd' : (p : ℤ) ∣ n * (P * (b : ℤ) ^ (p - 1)) := by
    rwa [mul_assoc] at hdvd
  rcases Int.Prime.dvd_mul' hp_prime hdvd' with h | h
  · exact hn_ndvd h
  · rcases Int.Prime.dvd_mul' hp_prime h with h | h
    · exact hp_ndvd_P h
    · exact hp_ndvd_bpow h
