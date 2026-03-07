/-
BoundCalc tactic — test cases from real codebase patterns.

Status key:
  PASS    = bound_calc closes it
  FAIL    = bound_calc can't close it yet (sorry'd, tagged with roadmap item)
  MANUAL  = requires manual proof (out of scope or aspirational)
-/
import Flean.BoundCalc.BoundCalc

/-! ## Phase 1: gcongr + rich subgoal dispatch

Goals where both sides have the same syntactic factor structure and
needed bounds are already hypotheses or closable by standard tactics. -/

section Phase1

-- P1.1: Basic two-factor product bound (LogTermination:623 pattern)
-- PASS
example (den num ab : ℝ) (hd : den ≤ ab) (hp : num ≤ ab)
    (hd_nn : 0 ≤ num) (hab_nn : 0 ≤ ab) :
    den * num ≤ ab * ab := by
  bound_calc

-- P1.2: Nested three-factor product bound (ExpTermination:816 pattern)
-- PASS
example (a b c A B C : ℝ) (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hc : 0 ≤ c) (hA : 0 ≤ A) (hAB : 0 ≤ A * B) :
    a * b * c ≤ A * B * C := by
  bound_calc

-- P1.3: One-sided scaling (CommonConstants:221 pattern)
-- PASS
example (m bound step : ℝ) (hm : m ≤ bound) (hstep : 0 ≤ step) :
    m * step ≤ bound * step := by
  bound_calc

-- P1.4: Strict inequality (CommonConstants:139 pattern)
-- PASS
example (a b bound : ℝ) (ha : a < bound) (hb : 0 < b) :
    a * b < bound * b := by
  bound_calc

-- P1.5: Left-side scaling
-- PASS
example (coeff pow1 pow2 : ℝ) (hpow : pow1 ≤ pow2) (hcoeff : 0 ≤ coeff) :
    coeff * pow1 ≤ coeff * pow2 := by
  bound_calc

-- P1.6: Natural number with Nat.one_le_two_pow subgoal
-- PASS [R2]: dispatch chain proves `1 ≤ 2^ab` via Nat.one_le_two_pow
example (ab : ℕ) (hab : 1 ≤ ab ^ 2) :
    ab * 1 * 1 ≤ ab * ab ^ 2 * 2 ^ ab := by
  bound_calc

-- P1.7: Mixed strict/nonstrict product
-- PASS [R3]: factor matching uses mul_lt_mul
example (a b A B : ℝ) (h1 : a < A) (h2 : b ≤ B) (hb : 0 < b) (hA : 0 ≤ A) :
    a * b < A * B := by
  bound_calc

-- P1.8: Power monotonicity subgoal (linearize in dispatch)
-- PASS
example (m : ℝ) (e1 e2 : ℤ) (hm : m ≤ 100) (he : e1 ≤ e2) (hm_nn : 0 ≤ m) :
    m * (2:ℝ)^e1 ≤ 100 * (2:ℝ)^e2 := by
  bound_calc

-- P1.9: Nat with omega subgoals
-- PASS
example (a b : ℕ) (ha : a ≤ 10) (hb : b ≤ 20) :
    a * b ≤ 10 * 20 := by
  bound_calc

-- P1.10: Rational domain
-- PASS
example (a b : ℚ) (ha : a ≤ 1/2) (hb : b ≤ 1/3)
    (ha_nn : 0 ≤ b) (hq : 0 ≤ (1:ℚ)/2) :
    a * b ≤ 1/2 * (1/3) := by
  bound_calc

-- P1.11: RoundNormal:44 pattern — one-sided with div
-- PASS
example (x y : ℝ) (e : ℤ) (h : x ≤ y) (hprec : 0 ≤ (2:ℝ)^e) :
    x * (2:ℝ)^e ≤ y * (2:ℝ)^e := by
  bound_calc

-- P1.12: Negative left factor (edge case)
-- PASS
example (a b : ℝ) (ha : a ≤ -1) (hb : 3 ≤ b) :
    a * b ≤ -1 * b := by
  bound_calc

-- P1.13: Reflexive (same on both sides)
-- PASS
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a * b := by
  bound_calc

end Phase1

/-! ## Factor matching: hypothesis search + reordering

Goals where the tactic must figure out which hypothesis bounds which factor,
or where factors are in a different order than the hypotheses. -/

section FactorMatching

-- FM.1: Three individual factor bounds, any order
-- PASS: factor matching finds ha, hb, hc as individual factor bounds
example (a b c : ℝ) (hb : b ≤ 5) (ha : a ≤ 3) (hc : c ≤ 7)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) :
    a * b * c ≤ 3 * 5 * 7 := by
  bound_calc

-- FM.2: Two-factor regrouping (LogTermination:644-647 pattern)
-- PASS: factor matching finds h6D covers [6,D]→[3,2^L] and hdp covers [den,num]→[ab^2]
example (D den num ab : ℝ) (L : ℕ)
    (h6D : 6 * D ≤ 3 * (2:ℝ)^L) (hdp : den * num ≤ ab^2)
    (hdp_nn : 0 ≤ den * num) (h6D_nn : 0 ≤ 3 * (2:ℝ)^L) :
    6 * D * den * num ≤ 3 * ab^2 * (2:ℝ)^L := by
  bound_calc

-- FM.3: Power factor within product (linearize integration)
-- PASS
example (m : ℝ) (e1 e2 : ℤ) (hm : m ≤ 100) (he : e1 ≤ e2)
    (hm_nn : 0 ≤ m) (hpow_nn : 0 ≤ (2:ℝ)^e1) :
    m * (2:ℝ)^e1 ≤ 100 * (2:ℝ)^e2 := by
  bound_calc

-- FM.4: Two multi-factor hypotheses, 3 factors each side
-- PASS
example (a b c d e f : ℝ) (h1 : a * b ≤ d * e) (h2 : c ≤ f)
    (hc_nn : 0 ≤ c) (hde_nn : 0 ≤ d * e) :
    a * b * c ≤ d * e * f := by
  bound_calc

end FactorMatching

/-! ## Synthesized bounds (R1)

Goals where factors are identical on both sides (reflexive), differ only
by numeric constants, or differ by power exponents. -/

section SynthesizedBounds

-- SB.1: One-sided with identical factor (OddInterval:80 pattern)
-- PASS [R1]: reflexive synthesis for fm, hypothesis for 2^d
example (fm : ℕ) (d : ℕ) (hd : 2^d ≤ 2^3) :
    fm * 2^d ≤ fm * 2^3 := by
  bound_calc

-- SB.2: Constant factor absorption (LogTermination:641 pattern)
-- PASS: nlinarith handles this
example (x : ℕ) : 457 * x ≤ 500 * x := by
  bound_calc

-- SB.3: Two hypotheses matching factors (OddInterval:80-81 combined)
-- PASS: hypothesis hfm + hypothesis hd
example (fm d p : ℕ) (hd : 2^d ≤ 2^3) (hfm : fm ≤ 2^p - 1) :
    fm * 2^d ≤ (2^p - 1) * 2^3 := by
  bound_calc

-- SB.4: Power factor with linearize synthesis (2^e₁ ≤ 2^e₂)
-- TARGET: bound_calc (match a→10 via ha, 2^e1→2^e2 via linearize synthesis)
example (a : ℝ) (e1 e2 : ℤ) (ha : a ≤ 10) (he : e1 ≤ e2)
    (ha_nn : 0 ≤ a) :
    a * (2:ℝ)^e1 ≤ 10 * (2:ℝ)^e2 := by
  bound_calc

-- SB.5: One hypothesis + one reflexive factor
-- PASS [R1]
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ 10) :
    a * b ≤ 10 * b := by
  bound_calc

-- SB.6: Nat constant comparison within product
-- PASS [R1]: match x→3 via hx, y→y reflexive
example (x y : ℕ) (hx : x ≤ 3) :
    x * y ≤ 3 * y := by
  bound_calc

end SynthesizedBounds

/-! ## Strict inequalities (R3)

Goals with `<` instead of `≤`. -/

section StrictInequalities

-- SI.1: Strict one-sided (mul_lt_mul_of_pos_right pattern)
-- PASS: gcongr handles this
example (a bound : ℝ) (b : ℝ) (ha : a < bound) (hb : 0 < b) :
    a * b < bound * b := by
  bound_calc

-- SI.2: Strict left-side (mul_lt_mul_of_pos_left pattern, CommonConstants:139)
-- PASS: gcongr handles this
example (a b : ℝ) (ha : 0 < a) (hb : b < 10) :
    a * b < a * 10 := by
  bound_calc

-- SI.3: Strict with regrouping
-- PASS [R3]: factor matching weakens h1 with le_of_lt, then mul_le_mul
example (a b c : ℝ) (h1 : a * b < 10) (h2 : c ≤ 5)
    (h1_nn : 0 ≤ a * b) (hc_nn : 0 ≤ c) :
    a * b * c ≤ 10 * 5 := by
  bound_calc

-- SI.4: Mixed strict/nonstrict, 4-arg mul_lt_mul
-- PASS [R3]: factor matching uses mul_lt_mul for strict goal
example (a b A B : ℝ) (h1 : a < A) (h2 : b ≤ B) (hb : 0 < b) (hA : 0 ≤ A) :
    a * b < A * B := by
  bound_calc

-- SI.5: Strict in calc context (RoundNormal:110 pattern)
-- PASS: gcongr handles this
example (x : ℝ) (e : ℤ) (hx : x < 2) (he : 0 < (2:ℝ)^e) :
    x * (2:ℝ)^e < 2 * (2:ℝ)^e := by
  bound_calc

-- SI.6: Strict with right-side strict (mul_lt_mul' pattern)
-- PASS [R3]: factor matching uses mul_lt_mul'
example (a b A B : ℝ) (h1 : a ≤ A) (h2 : b < B) (hb : 0 ≤ b) (hA : 0 < A) :
    a * b < A * B := by
  bound_calc

-- SI.7: Both strict
-- PASS [R3]
example (a b A B : ℝ) (h1 : a < A) (h2 : b < B) (hb : 0 < b) (hA : 0 ≤ A) :
    a * b < A * B := by
  bound_calc

-- SI.8: Strict regrouping with < goal
-- PASS [R3]: factor matching finds strict bound, uses mul_lt_mul
example (a b c : ℝ) (h1 : a * b < 10) (h2 : c ≤ 5)
    (h1_pos : 0 < a * b) (hc_pos : 0 < c) :
    a * b * c < 10 * 5 := by
  bound_calc

end StrictInequalities

/-! ## Nat domain patterns (R2 / dispatch)

Natural number multiplication with omega/norm_num side goals. -/

section NatPatterns

-- NP.1: Basic Nat product
-- PASS
example (a b : ℕ) (ha : a ≤ 10) (hb : b ≤ 20) :
    a * b ≤ 10 * 20 := by
  bound_calc

-- NP.2: Nat.mul_le_mul_left pattern (OddInterval)
-- PASS [R1]: reflexive fm + hypothesis h
example (fm : ℕ) (a b : ℕ) (h : a ≤ b) :
    fm * a ≤ fm * b := by
  bound_calc

-- NP.3: Nat.mul_le_mul_right pattern (OddInterval)
-- PASS [R1]: hypothesis h + reflexive d
example (a b d : ℕ) (h : a ≤ b) :
    a * d ≤ b * d := by
  bound_calc

-- NP.4: Nat calc chain step (LogTermination:445 pattern)
-- PASS [R1]: hypothesis hp + hypothesis hs
example (p s ab : ℕ) (hp : p ≤ ab) (hs : 2^s ≤ 2^ab) :
    p * 2^s ≤ ab * 2^ab := by
  bound_calc

-- NP.5: Two-factor with omega side goal
-- PASS: nlinarith handles
example (x : ℕ) : 457 * x ≤ 500 * x := by
  bound_calc

-- NP.6: Product with 1 ≤ 2^n subgoal
-- PASS [R2]: dispatch chain proves `1 ≤ 2^a` via Nat.one_le_two_pow
example (a : ℕ) : a * 1 ≤ a * 2^a := by
  bound_calc

-- NP.7: 1 ≤ 3^n via Nat.one_le_pow
-- PASS [R2]: dispatch chain proves via Nat.one_le_pow
example (n : ℕ) : n * 1 ≤ n * 3^n := by
  bound_calc

-- NP.8: 1 ≤ 5^n via Nat.one_le_pow
-- PASS [R2]
example (a b : ℕ) (hab : a ≤ b) : a * 1 ≤ b * 5^b := by
  bound_calc

end NatPatterns

/-! ## PadeExp patterns: nested multi-factor products

Complex 3-factor products from PadeExp.lean convergence bounds. -/

section PadeExpPatterns

-- PE.1: Three-factor nested mul_le_mul (PadeExp:925-933)
-- PASS: gcongr handles aligned structure
example (a b c A B C : ℝ) (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C)
    (hb_nn : 0 ≤ b) (hB_nn : 0 ≤ B) (hc_nn : 0 ≤ c) (hA_nn : 0 ≤ A)
    (hAB_nn : 0 ≤ A * B) :
    a * b * c ≤ A * B * C := by
  bound_calc

-- PE.2: Mixed scaling with nonneg_left (PadeExp:949 pattern)
-- PASS: gcongr handles this
example (K1 C x : ℝ) (hK1 : K1 ≤ 100) (hC : C ≤ x)
    (hK1_nn : 0 ≤ K1) (hC_nn : 0 ≤ C) (h2 : 0 ≤ (2:ℝ)) :
    2 * K1 * C ≤ 2 * 100 * x := by
  bound_calc

-- PE.3: Factor with mul_le_mul_of_nonneg_left (PadeExp:602 pattern)
-- PASS
example (K step bound : ℝ) (hK_nn : 0 ≤ K) (h : step ≤ bound) :
    K * step ≤ K * bound := by
  bound_calc

end PadeExpPatterns

/-! ## Division patterns (R4) -/

section DivisionPatterns

-- D.1: Division anti-monotonicity
-- FAIL [R4]
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    1 / y ≤ 1 / x := by
  sorry -- TARGET: bound_calc

-- D.2: RoundNormal:44 — mul after div
-- FAIL [R4]: has div inside product
-- Actually this is: (x / 2^e) * 2^prec ≤ (y / 2^e) * 2^prec
-- which is just scaling, gcongr should handle if it can see through div
example (x y : ℝ) (e : ℤ) (h : x ≤ y) (he : 0 < (2:ℝ)^e) (hp : 0 ≤ (2:ℝ)^(5:ℤ)) :
    x / (2:ℝ)^e * (2:ℝ)^(5:ℤ) ≤ y / (2:ℝ)^e * (2:ℝ)^(5:ℤ) := by
  sorry -- TARGET: bound_calc

end DivisionPatterns

/-! ## Multi-step chain composition (aspirational) -/

section ChainComposition

-- CC.1: Full LogTermination:643-652 chain
-- MANUAL: user writes calc, bound_calc closes each step
example (D den num ab : ℝ) (L_pade L : ℕ)
    (h6D : 6 * D ≤ 3 * (2:ℝ)^L_pade)
    (hdp : den * num ≤ ab^2)
    (h3ab2 : 3 * ab^2 ≤ (2:ℝ)^ab)
    (hL : ab + L_pade ≤ L) :
    6 * D * den * num ≤ (2:ℝ)^L := by
  sorry

-- CC.2: ExpTermination:813-819 three-factor collapse
-- MANUAL
example (f g h A B C : ℝ) (ab : ℕ)
    (hf : f ≤ A) (hg : g ≤ B) (hh : h ≤ C)
    (hA : A = (ab:ℝ)^(56*ab)) (hB : B = (ab:ℝ)^(56*ab)) (hC : C = (ab:ℝ)^ab)
    (hg_nn : 0 ≤ g) (hB_nn : 0 ≤ B) (hh_nn : 0 ≤ h) (hAB_nn : 0 ≤ A * B) :
    f * g * h ≤ (ab:ℝ)^(113*ab) := by
  sorry

end ChainComposition

/-! ## nlinarith fallback patterns

Goals where factor matching doesn't apply but nlinarith handles
the 2-factor nonlinear arithmetic. -/

section NlinarithFallback

-- NL.1: Product ≤ constant (2-factor, nlinarith degree-2)
-- PASS
example (x y : ℝ) (hx : x ≤ 10) (hy : y ≤ 20) (hx_nn : 0 ≤ y) (h10 : 0 ≤ (10:ℝ)) :
    x * y ≤ 200 := by
  bound_calc

-- NL.2: Constant factor (Nat)
-- PASS
example (x : ℕ) : 457 * x ≤ 500 * x := by
  bound_calc

-- NL.3: Square bound
-- PASS
example (x : ℝ) (hx : x ≤ 5) (hx_nn : 0 ≤ x) :
    x * x ≤ 25 := by
  bound_calc

end NlinarithFallback

/-! ## Edge cases -/

section EdgeCases

-- EC.1: Zero factors
example (a : ℝ) (ha : a ≤ 5) : a * 0 ≤ 5 * 0 := by
  simp

-- EC.2: Single factor (not a product)
-- PASS: gcongr works even on non-products
example (a : ℝ) (ha : a ≤ 5) : a ≤ 5 := by
  bound_calc

-- EC.3: Four factors each side
-- PASS
example (a b c d A B C D : ℝ)
    (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) (h4 : d ≤ D)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hd : 0 ≤ d) (hA : 0 ≤ A) (hAB : 0 ≤ A * B) (hABC : 0 ≤ A * B * C) :
    a * b * c * d ≤ A * B * C * D := by
  bound_calc

end EdgeCases
