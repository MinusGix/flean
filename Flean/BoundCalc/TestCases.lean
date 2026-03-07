/-
BoundCalc tactic — test cases from real codebase patterns.

Each section corresponds to a phase from Design.md.

Status key:
  PASS    = bound_calc closes it
  FAIL    = bound_calc can't close it yet (sorry'd, future phase)
  GCONGR  = gcongr alone closes it (bound_calc subsumes)
-/
import Flean.BoundCalc.BoundCalc

/-! ## Phase 1: gcongr + rich subgoal dispatch

These are the "easy wins" — goals where both sides are known and the
needed bounds are already hypotheses or closable by standard tactics. -/

section Phase1

-- P1.1: Basic two-factor product bound (LogTermination:623 pattern)
-- MANUAL: `mul_le_mul hd hp (by positivity) (by positivity)`
example (den num ab : ℝ) (hd : den ≤ ab) (hp : num ≤ ab)
    (hd_nn : 0 ≤ num) (hab_nn : 0 ≤ ab) :
    den * num ≤ ab * ab := by
  bound_calc

-- P1.2: Nested three-factor product bound (ExpTermination:816 pattern)
-- MANUAL: `mul_le_mul (mul_le_mul h_fac h_4b ...) h_exp ...` (6 args!)
example (a b c A B C : ℝ) (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hc : 0 ≤ c) (hA : 0 ≤ A) (hAB : 0 ≤ A * B) :
    a * b * c ≤ A * B * C := by
  bound_calc

-- P1.3: One-sided scaling (CommonConstants:221 pattern)
-- MANUAL: `mul_le_mul_of_nonneg_right h_m_le (by positivity)`
example (m bound step : ℝ) (hm : m ≤ bound) (hstep : 0 ≤ step) :
    m * step ≤ bound * step := by
  bound_calc

-- P1.4: Strict inequality version
-- MANUAL: `mul_lt_mul_of_pos_right h_cast_bound (by positivity)`
example (a b bound : ℝ) (ha : a < bound) (hb : 0 < b) :
    a * b < bound * b := by
  bound_calc

-- P1.5: Left-side scaling
-- MANUAL: `mul_le_mul_of_nonneg_left h_pow_le (by positivity)`
example (coeff pow1 pow2 : ℝ) (hpow : pow1 ≤ pow2) (hcoeff : 0 ≤ coeff) :
    coeff * pow1 ≤ coeff * pow2 := by
  bound_calc

-- P1.6: Natural number product bound (LogTermination:638 pattern)
-- MANUAL: `Nat.mul_le_mul (Nat.mul_le_mul_left _ hab2_pos) Nat.one_le_two_pow`
-- FAIL: subgoal `1 ≤ 2^ab` needs Nat.one_le_two_pow (not in dispatch chain)
example (ab : ℕ) (hab : 1 ≤ ab ^ 2) :
    ab * 1 * 1 ≤ ab * ab ^ 2 * 2 ^ ab := by
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hab) Nat.one_le_two_pow

-- P1.7: Mixed strict/nonstrict in product
-- MANUAL: `mul_lt_mul h_strict h_le h_pos h_nn`
-- FAIL: gcongr decomposes to `0 ≤ a` (not given) and `b < B` (have b ≤ B)
-- gcongr uses a different factoring than mul_lt_mul
example (a b A B : ℝ) (h1 : a < A) (h2 : b ≤ B) (hb : 0 < b) (hA : 0 ≤ A) :
    a * b < A * B := by
  exact mul_lt_mul h1 h2 hb hA

-- P1.8: Power monotonicity subgoal (needs linearize in dispatch)
-- MANUAL: `mul_le_mul_of_nonneg_right h (by linearize)`
example (m : ℝ) (e1 e2 : ℤ) (hm : m ≤ 100) (he : e1 ≤ e2) (hm_nn : 0 ≤ m) :
    m * (2:ℝ)^e1 ≤ 100 * (2:ℝ)^e2 := by
  bound_calc

-- P1.9: Nat with omega subgoals
example (a b : ℕ) (ha : a ≤ 10) (hb : b ≤ 20) :
    a * b ≤ 10 * 20 := by
  bound_calc

-- P1.10: Rational domain
example (a b : ℚ) (ha : a ≤ 1/2) (hb : b ≤ 1/3)
    (ha_nn : 0 ≤ b) (hq : 0 ≤ (1:ℚ)/2) :
    a * b ≤ 1/2 * (1/3) := by
  bound_calc

end Phase1

/-! ## Phase 2: Factor matching / hypothesis search

Goals where the tactic must figure out which hypothesis bounds which factor,
or where the RHS isn't fully determined. -/

section Phase2

-- P2.1: Synthesize RHS from context (bound_calc would need to infer 10 * 20 = 200)
example (x y : ℝ) (hx : x ≤ 10) (hy : y ≤ 20) (hx_nn : 0 ≤ y) (h10 : 0 ≤ (10:ℝ)) :
    x * y ≤ 200 := by
  sorry
  -- TARGET: by bound_calc (finds hx, hy, computes 10 * 20 = 200)

-- P2.2: Factor matching with reordering
example (a b c : ℝ) (hb : b ≤ 5) (ha : a ≤ 3) (hc : c ≤ 7)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) :
    a * b * c ≤ 3 * 5 * 7 := by
  sorry
  -- TARGET: by bound_calc (matches a→3, b→5, c→7 despite hypothesis order)

-- P2.3: Power factor within product (interaction with linearize)
example (m : ℝ) (e1 e2 : ℤ) (hm : m ≤ 100) (he : e1 ≤ e2)
    (hm_nn : 0 ≤ m) (hpow_nn : 0 ≤ (2:ℝ)^e1) :
    m * (2:ℝ)^e1 ≤ 100 * (2:ℝ)^e2 := by
  bound_calc
  -- NOTE: This might already work if gcongr decomposes and linearize handles 2^e1 ≤ 2^e2

end Phase2

/-! ## Phase 3: Ring normalization + factor group matching

Goals where LHS and RHS have different syntactic groupings. -/

section Phase3

-- P3.1: Regrouping factors (LogTermination:644-647 pattern)
example (D den num ab : ℝ) (L : ℕ)
    (h6D : 6 * D ≤ 3 * (2:ℝ)^L) (hdp : den * num ≤ ab^2)
    (hdp_nn : 0 ≤ den * num) (h6D_nn : 0 ≤ 3 * (2:ℝ)^L) :
    6 * D * den * num ≤ 3 * ab^2 * (2:ℝ)^L := by
  sorry
  -- TARGET: by bound_calc [h6D, hdp]

-- P3.2: Constant factor absorption
example (x : ℕ) : 457 * x ≤ 500 * x := by
  sorry
  -- TARGET: by bound_calc (or omega)

-- P3.3: Division anti-monotonicity
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    1 / y ≤ 1 / x := by
  sorry
  -- TARGET: by bound_calc

end Phase3

/-! ## Phase 4: Multi-step chain composition (aspirational) -/

section Phase4

-- P4.1: Full chain from LogTermination:643-652
example (D den num ab : ℝ) (L_pade L : ℕ)
    (h6D : 6 * D ≤ 3 * (2:ℝ)^L_pade)
    (hdp : den * num ≤ ab^2)
    (h3ab2 : 3 * ab^2 ≤ (2:ℝ)^ab)
    (hL : ab + L_pade ≤ L) :
    6 * D * den * num ≤ (2:ℝ)^L := by
  sorry
  -- STRETCH: by bound_calc [h6D, hdp, h3ab2, hL]

-- P4.2: Three-factor with exponent collapse (ExpTermination:813-819)
example (f g h A B C : ℝ) (ab : ℕ)
    (hf : f ≤ A) (hg : g ≤ B) (hh : h ≤ C)
    (hA : A = (ab:ℝ)^(56*ab)) (hB : B = (ab:ℝ)^(56*ab)) (hC : C = (ab:ℝ)^ab)
    (hg_nn : 0 ≤ g) (hB_nn : 0 ≤ B) (hh_nn : 0 ≤ h) (hAB_nn : 0 ≤ A * B) :
    f * g * h ≤ (ab:ℝ)^(113*ab) := by
  sorry
  -- STRETCH: by bound_calc [hf, hg, hh] (needs ring on exponents: 56+56+1 = 113)

end Phase4

/-! ## Edge cases -/

section EdgeCases

-- E1: Zero factors
example (a : ℝ) (ha : a ≤ 5) : a * 0 ≤ 5 * 0 := by
  simp

-- E2: Negative left factor, positive right factor
example (a b : ℝ) (ha : a ≤ -1) (hb : 3 ≤ b) :
    a * b ≤ -1 * b := by
  bound_calc

-- E3: Natural number basic
example (a b : ℕ) (ha : a ≤ 10) (hb : b ≤ 20) :
    a * b ≤ 10 * 20 := by
  bound_calc

-- E4: Reflexive (same on both sides)
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a * b := by
  bound_calc

end EdgeCases
