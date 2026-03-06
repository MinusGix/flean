import Flean.Linearize.Linearize
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Mathlib.Tactic.Linearize

section BasicTests

-- -- set_option trace.linearize true
-- set_option diagnostics true

-- Test 1: Basic < transformation (lhs < base^exp)
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^100) : Int.log 2 a < 100 := by
  linearize at h
  trivial

-- Test 2: Basic ≤ transformation (lhs ≤ base^exp)
example (a : ℝ) (ha : 0 < a) (h : a ≤ (2 : ℝ)^100) : Int.log 2 a ≤ 100 := by
  linearize at h
  trivial

-- Test 3: Reverse < transformation (base^exp < rhs)
example (a : ℝ) (ha : 0 < a) (h : (2 : ℝ)^100 < a) : 100 < Int.log 2 a + 1 := by
  linearize at h
  trivial

-- Test 4: Reverse ≤ transformation (base^exp ≤ rhs)
example (a : ℝ) (ha : 0 < a) (h : (2 : ℝ)^100 ≤ a) : 100 ≤ Int.log 2 a := by
  linearize at h
  trivial

end BasicTests

section IntegerExponentTests

-- Test 5: Integer exponent
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^(100 : ℤ)) : Int.log 2 a < 100 := by
  linearize at h
  trivial

end IntegerExponentTests

section MultipleBaseTests

-- Test 6: Different bases
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^50) (h2 : b ≤ (3 : ℝ)^30) :
        Int.log 2 a < 50 ∧ Int.log 3 b ≤ 30 := by
  linearize at h1
  linearize at h2
  trivial

end MultipleBaseTests

section AllHypothesesTest

-- Test 7: Linearize all hypotheses at once
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
        (h1 : a < (2 : ℝ)^100) (h2 : b ≤ (2 : ℝ)^200) :
        Int.log 2 a < 100 ∧ Int.log 2 b ≤ 200 := by
  linearize at h1 h2
  trivial

end AllHypothesesTest

section RealWorldExample

-- Test 8: More realistic example using linearize with linarith
example (x y : ℝ) (hx : 1 < x) (hy : 1 < y)
        (h1 : x < (2 : ℝ)^10) (h2 : y < (2 : ℝ)^20) :
        x * y < (2 : ℝ)^31 := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith

  -- Transform to logarithmic form
  linearize at h1
  linearize at h2
  sorry

end RealWorldExample

section ZpowGoalTests

-- -- set_option trace.linearize true
-- set_option diagnostics true
-- Test 9: Goal linearization - 2^m < 2^n reduces to m < n
example (m n : ℤ) (h : m < n) : (2 : ℝ)^m < (2 : ℝ)^n := by
  linearize

-- Test 10: Goal linearization - 2^m ≤ 2^n reduces to m ≤ n
example (m n : ℤ) (h : m ≤ n) : (2 : ℝ)^m ≤ (2 : ℝ)^n := by
  linearize

-- Test 11: Goal linearization with different base
example (m n : ℤ) (h : m < n) : (3 : ℝ)^m < (3 : ℝ)^n := by
  linearize

-- Test 12: Goal linearization with more complex expressions
example (m n k : ℤ) (h : m + k < n + k) : (2 : ℝ)^(m + k) < (2 : ℝ)^(n + k) := by
  linearize

end ZpowGoalTests

section LinearizeBangTests

-- Test 13: linearize! with simple hypothesis transformation
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^5) : Int.log 2 a ≤ 4 := by
  linearize! at h

-- Test 14: linearize! with goal transformation
example (m : ℤ) (h : m ≤ 5) : (2 : ℝ)^m ≤ (2 : ℝ)^5 := by
  linearize!

-- Test 15: linearize! with wildcard (all hypotheses and goal)
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^3) : (2 : ℝ)^1 < (2 : ℝ)^3 := by
  linearize!

-- Test 16: linearize! with additional lemmas
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^5) (extra : Int.log 2 a ≥ 2) : Int.log 2 a = 4 ∨ Int.log 2 a = 3 ∨ Int.log 2 a = 2 := by
  linearize! [extra] at h

-- Test 17: linearize! with only modifier and lemmas
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ)^5) (extra : Int.log 2 a ≥ 2) : Int.log 2 a ≤ 4 := by
  linearize! only [h, extra] at h

end LinearizeBangTests

section ZpowTests

-- set_option trace.linearize true

-- Test 18: Goal linearization using zpow_pos for 0 < a^n pattern
example : (0 : ℝ) < (2 : ℝ)^5 := by
  linearize

-- Test 19: Goal linearization using zpow_pos with integer exponent
example : (0 : ℝ) < (2 : ℝ)^(-3 : ℤ) := by
  linearize

-- Test 20: Goal linearization using zpow_pos with variable exponent
example (n : ℤ) : (0 : ℝ) < (3 : ℝ)^n := by
  linearize

-- Test 21: Goal linearization using zpow_nonneg for 0 ≤ a^n pattern
example : (0 : ℝ) ≤ (2 : ℝ)^5 := by
  linearize

-- Test 22: Goal linearization using zpow_nonneg with integer exponent
example : (0 : ℝ) ≤ (2 : ℝ)^(-3 : ℤ) := by
  linearize

-- Test 23: Goal linearization using zpow_nonneg with variable exponent
example (n : ℤ) : (0 : ℝ) ≤ (3 : ℝ)^n := by
  linearize

-- Test 24: Goal linearization using one_lt_zpow₀ for 1 < a^n pattern
example : (1 : ℝ) < (2 : ℝ)^(5 : ℤ) := by
  linearize

-- Test 25: Goal linearization using one_lt_zpow₀ with variable exponent
example (n : ℤ) (hn : 0 < n) : (1 : ℝ) < (3 : ℝ)^n := by
  linearize

-- Test 26: Goal linearization using one_lt_pow for 1 < a^n pattern with natural exponent
example : (1 : ℝ) < (2 : ℝ)^5 := by
  linearize

-- Test 27: Goal linearization using one_lt_pow with variable natural exponent
example (n : ℕ) (hn : n ≠ 0) : (1 : ℝ) < (3 : ℝ)^n := by
  linearize

-- Test 28: Goal linearization using one_le_zpow₀ for 1 ≤ a^n pattern with integer exponent
example : (1 : ℝ) ≤ (2 : ℝ)^(5 : ℤ) := by
  linearize

-- Test 29: Goal linearization using one_le_zpow₀ with variable exponent
example (n : ℤ) (hn : 0 ≤ n) : (1 : ℝ) ≤ (3 : ℝ)^n := by
  linearize

-- Test 30: Goal linearization using one_le_pow₀ for 1 ≤ a^n pattern with natural exponent
example : (1 : ℝ) ≤ (2 : ℝ)^5 := by
  linearize

-- Test 31: Goal linearization using one_le_pow₀ with variable natural exponent
example (n : ℕ) : (1 : ℝ) ≤ (3 : ℝ)^n := by
  linearize

end ZpowTests

section NeZpowTests

-- Test 32: Goal linearization for 2^e ≠ 0
example (e : ℤ) : (2 : ℝ)^e ≠ 0 := by
  linearize

end NeZpowTests

/-! ## Tests inspired by exp/log termination proof patterns

These test cases mirror repetitive patterns found in ExpTermination.lean and
LogTermination.lean. The goal is to see which patterns `linearize` already handles
and which it should be extended to support. -/

section ExpLogPatterns

/-! ### Pattern E: Same-base power monotonicity with ℕ exponents over ℝ

In exp/log proofs, this appears as:
  `pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (some_omega_bound)`
Can linearize handle `(2:ℝ)^a ≤ (2:ℝ)^b` when `a b : ℕ`? -/

-- E1: ℕ exponents, ≤ — PASS (fixed: use pow_le_pow_right₀ for ℕ exponents)
example (a b : ℕ) (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
  linearize!

-- E2: ℕ exponents, < — PASS (fixed: use pow_lt_pow_right₀ for ℕ exponents)
example (a b : ℕ) (h : a < b) : (2 : ℝ) ^ a < (2 : ℝ) ^ b := by
  linearize!

-- E3: ℕ exponents with concrete bound — PASS
example (ab : ℕ) (h : 6 ≤ ab) : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ ab := by
  linearize!

-- E4: max pattern — PASS with linearize! (replaces `pow_le_pow_right₀ (by norm_num) (le_max_left L₁ L₂)`)
example (L₁ L₂ : ℕ) : (2 : ℝ) ^ L₁ ≤ (2 : ℝ) ^ (max L₁ L₂) := by
  linearize!

/-! ### Pattern F: Division bounds involving powers

`k * 2^S / 2^N ≤ 1/(4 * 2^L)` reduces to exponent arithmetic.
Can linearize help simplify these? -/

-- F1: `1 / 2^a ≤ 1 / 2^b` from `b ≤ a` — PASS (reciprocal recognition)
example (a b : ℕ) (h : b ≤ a) : (1 : ℝ) / 2 ^ a ≤ 1 / 2 ^ b := by
  linearize

-- F2: `2^a / 2^b = 2^(a-b)` — FAIL (equality, not comparison)
-- Out of scope for linearize (this is field_simp + zpow_sub territory)
example (a b : ℤ) (h : b ≤ a) : (2 : ℝ) ^ a / (2 : ℝ) ^ b = (2 : ℝ) ^ (a - b) := by
  -- linearize  -- fails: not a comparison
  rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]

-- F3: Bound with mixed expression — FAIL (not pure power comparison)
example (a : ℝ) (ha : 0 < a) (s n : ℕ) (h : n ≤ s) :
    a / (2 : ℝ) ^ n ≤ a / (2 : ℝ) ^ 0 := by
  -- linearize  -- fails: not same-base zpow comparison
  simp only [pow_zero, div_one]
  exact div_le_self ha.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

/-! ### Pattern involving positivity of powers

These come up as preconditions. linearize already handles some of these
(Tests 18-23), but let's test the ℕ-exponent versions. -/

-- P1: 0 < 2^n for ℕ exponent — PASS
example (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n := by
  linearize!

-- P2: (1:ℝ) ≤ 2 (the `by norm_num` that feeds pow_le_pow_right₀)
-- Not a linearize target, just checking
example : (1 : ℝ) ≤ 2 := by norm_num

/-! ### Pattern: Hypothesis linearization with ℕ powers

In exp/log, hypotheses like `a < 2^N` need to become `Int.log 2 a < N`
for linarith to work. -/

-- H1: Hypothesis with ℕ exponent — PASS (linearize transforms, trivial closes)
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ) ^ (100 : ℕ)) :
    Int.log 2 a < 100 := by
  linearize at h
  trivial

-- H2: Two hypotheses bounding a value (the "sandwich" pattern) — PASS
example (a : ℝ) (ha : 0 < a)
    (h1 : (2 : ℝ) ^ (10 : ℕ) ≤ a) (h2 : a < (2 : ℝ) ^ (20 : ℕ)) :
    10 ≤ Int.log 2 a ∧ Int.log 2 a < 20 := by
  linearize at h1 h2
  exact ⟨h1, h2⟩

/-! ### Pattern: Combining linearize with linarith for exp/log style goals

These are the actual proof patterns we want to simplify. -/

-- C1: Transitive power bound — linearize! transforms h but goal changes shape.
-- The goal becomes `a < (2:ℝ)^20` which isn't pure zpow comparison.
-- linearize! can't auto-solve because it only calls linarith on the transformed hyps.
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ) ^ 10) : a < (2 : ℝ) ^ 20 := by
  calc a < (2 : ℝ) ^ 10 := h
    _ ≤ (2 : ℝ) ^ 20 := by linearize

-- C2: Same-base power comparison with arithmetic on exponents — PASS
example (n : ℤ) (h : n ≤ 100) : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 100 := by
  linearize!

-- C3: Product bound — FAIL (out of scope, mixed expression)
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha2 : a ≤ 10) (hb2 : b ≤ (2 : ℝ) ^ 5) :
    a * b ≤ 10 * (2 : ℝ) ^ 5 := by
  -- linearize  -- fails: not same-base zpow comparison
  exact mul_le_mul ha2 hb2 hb (by norm_num)

end ExpLogPatterns

section OmegaSideGoalTests

-- Test: exponent side goal needs omega (10 ≤ N pattern from ExpComputableDefs)
example (N : ℕ) (hN : 10 ≤ N) : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ N := by
  linearize!

-- Test: exponent side goal needs omega (k.natAbs + s ≤ k.natAbs + S)
example (k : ℤ) (s S : ℕ) (hS : s ≤ S) :
    (2 : ℝ) ^ (k.natAbs + s) ≤ (2 : ℝ) ^ (k.natAbs + S) := by
  linearize!

-- Test: have pattern (as used in exp/log code) — now works with linearize!
example (N : ℕ) (hN : 10 ≤ N) : True := by
  have _h2_10_le : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ N := by linearize!
  trivial

-- Test: exponent side goal with linarith-solvable bound
example (ab L_pade L : ℕ) (h : ab + L_pade ≤ L) :
    (2 : ℝ) ^ (ab + L_pade) ≤ (2 : ℝ) ^ L := by
  linearize!

-- Test: omega on ℤ side goal (zpow path)
example (N : ℤ) (hN : 10 ≤ N) : (2 : ℝ) ^ (10 : ℤ) ≤ (2 : ℝ) ^ N := by
  linearize!

-- Test: omega on ℤ side goal (explicit zpow)
example (N : ℤ) (hN : 10 ≤ N) : (2 : ℝ) ^ (10 : ℤ) ≤ (2 : ℝ) ^ N := by
  linearize!

end OmegaSideGoalTests

section BaseExprTests

/-! ### Pattern: `linearize (base := expr)` for non-literal bases

These test cases mirror patterns from ExpTermination.lean where the base
is a variable or expression, not a literal like 2. -/

-- B1: Variable base, ℕ exponents, ≤
example (N ab : ℕ) (hN_pos : 1 ≤ N) (hN_le : N ≤ 28 * ab) :
    (N : ℝ) ^ N ≤ (N : ℝ) ^ (28 * ab) := by
  linearize (base := (N : ℝ))

-- B2: Expression base (4 * b), ℕ exponents
example (N ab : ℕ) (b : ℕ) (hb : 1 ≤ b) (hN_le : N ≤ 28 * ab) :
    ((4 : ℝ) * b) ^ N ≤ ((4 : ℝ) * b) ^ (28 * ab) := by
  linearize (base := (4 : ℝ) * b)

-- B3: Variable base (ab), ℕ exponents
example (ab : ℕ) (a_natAbs : ℕ) (hab : 1 ≤ ab) (ha_le : a_natAbs ≤ ab) :
    (ab : ℝ) ^ a_natAbs ≤ (ab : ℝ) ^ ab := by
  linearize (base := (ab : ℝ))

-- B4: linearize! auto-solves when side goals are tractable
example (ab : ℕ) (a_natAbs : ℕ) (hab : 1 ≤ ab) (ha_le : a_natAbs ≤ ab) :
    (ab : ℝ) ^ a_natAbs ≤ (ab : ℝ) ^ ab := by
  linearize! (base := (ab : ℝ))

-- B5: Literal base still works with (base := ...) syntax
example (a b : ℕ) (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
  linearize! (base := (2 : ℝ))

-- B6: Strict inequality with variable base
example (N ab : ℕ) (hN_pos : 1 < N) (hN_lt : N < 28 * ab) :
    (N : ℝ) ^ N < (N : ℝ) ^ (28 * ab) := by
  linearize (base := (N : ℝ))

end BaseExprTests

section ReciprocalTests

/-! ### Pattern: Reciprocal monotonicity `c / base^m ≤ c / base^n`

These test cases mirror `div_le_div_of_nonneg_left` patterns from
ExpTermination.lean and LogTermination.lean. -/

-- R1: Basic reciprocal with literal base
example (a b : ℕ) (h : b ≤ a) : (1 : ℝ) / 2 ^ a ≤ 1 / 2 ^ b := by
  linearize

-- R2: Reciprocal with general numerator
example (c : ℝ) (hc : 0 ≤ c) (a b : ℕ) (h : b ≤ a) :
    c / 2 ^ a ≤ c / 2 ^ b := by
  linearize

-- R3: Strict reciprocal
example (a b : ℕ) (h : b < a) : (1 : ℝ) / 2 ^ a < 1 / 2 ^ b := by
  linearize

-- R4: linearize! auto-solves
example (a b : ℕ) (h : b ≤ a) : (1 : ℝ) / 2 ^ a ≤ 1 / 2 ^ b := by
  linearize!

end ReciprocalTests

section UnfoldLetTests

/-! ### Pattern: `set` alias transparency

After `set C := (2:ℝ)^k`, linearize should see through C to the underlying power. -/

-- U1: set alias for power expression in goal
example (m n : ℤ) (h : m ≤ n) : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := by
  set C := (2 : ℝ) ^ m
  linearize

-- U2: set alias used on both sides
example (k : ℤ) (m n : ℤ) (h : m ≤ n) : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := by
  set a := (2 : ℝ) ^ m
  set b := (2 : ℝ) ^ n
  linearize

-- U3: set alias in hypothesis
example (a : ℝ) (ha : 0 < a) (h : a < (2 : ℝ) ^ 100) : Int.log 2 a < 100 := by
  set bound := (2 : ℝ) ^ (100 : ℤ)
  linearize at h
  trivial

-- U4: set alias in reciprocal pattern
example (a b : ℕ) (h : b ≤ a) : (1 : ℝ) / 2 ^ a ≤ 1 / 2 ^ b := by
  set da := (2 : ℝ) ^ a
  set db := (2 : ℝ) ^ b
  linearize

end UnfoldLetTests

section NormCastTests

/-! ### Pattern: `have` block zpow elaboration

Inside `have` blocks, Lean may choose zpow (ℤ exponents) instead of pow (ℕ)
for expressions like `(2:ℝ)^10`. The side goal then has `Int.ofNat` vs
`@OfNat.ofNat ℤ` mismatch that omega can't handle. -/

-- N1: linearize! inside have — previously failed due to Int.ofNat mismatch
example (N : ℕ) (hN : 10 ≤ N) : True := by
  have _h : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ N := by linearize!
  trivial

-- N2: have with variable-only exponents
example (N M : ℕ) (hN : N ≤ M) : True := by
  have _h : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ M := by linearize!
  trivial

-- N3: have inside a proof term (the original failing pattern)
example (N : ℕ) (hN : 10 ≤ N) : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ N := by
  linearize!

-- N4: nested have
example (N : ℕ) (hN : 10 ≤ N) : True := by
  have : True := by
    have _h : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ N := by linearize!
    trivial
  trivial

-- N5: zpow path inside have (Lean may choose ℤ exponents)
example (N : ℤ) (hN : 10 ≤ N) : True := by
  have _h : (2 : ℝ) ^ (10 : ℤ) ≤ (2 : ℝ) ^ N := by linearize!
  trivial

-- N6: complex expression inside have
example (k : ℤ) (s S : ℕ) (hS : s ≤ S) : True := by
  have _h : (2 : ℝ) ^ (k.natAbs + s) ≤ (2 : ℝ) ^ (k.natAbs + S) := by linearize!
  trivial

end NormCastTests
