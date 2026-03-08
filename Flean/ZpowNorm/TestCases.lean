/-
Copyright (c) 2026. All rights reserved.
-/
import Flean.ZpowNorm.ZpowNorm

/-!
# ZpowNorm Test Cases

Test cases derived from real codebase patterns. Each test is tagged with its
pattern category and a representative source location.

## Pattern categories
- **A**: zpow product collapse/split (`two_zpow_mul` + `congr 1; ring`)
- **B**: npow ↔ zpow cast bridge (`zpow_natCast` + prec lemmas)
- **C**: Combined A + B chains
- **D**: zpow arithmetic (`zpow_sub₀`, `zpow_add₀`, `zpow_add_one₀`)
- **E**: Exponent equality after normalization
-/

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [FloatFormat]
local notation "prec" => FloatFormat.prec

/-! ## Pattern A: zpow product collapse -/

-- A.1: Basic collapse (RoundDown:145, RoundUp:177, ToVal:406)
-- Before: `rw [two_zpow_mul]; congr 1; ring`
example (a b : ℤ) :
    (2 : R) ^ a * (2 : R) ^ b = (2 : R) ^ (a + b) := by
  zpow_norm

-- A.2: Reverse (split) direction (Ulp:210)
-- Before: `rw [← two_zpow_mul, mul_comm]`
example (a b : ℤ) :
    (2 : R) ^ (a + b) = (2 : R) ^ a * (2 : R) ^ b := by
  zpow_norm

-- A.3: With scalar factor (ToVal:396, general pattern)
-- Before: `rw [← zpow_natCast ..., two_zpow_mul]; congr 1; ...; ring`
example (x : R) (a b : ℤ) :
    x * (2 : R) ^ a * (2 : R) ^ b = x * (2 : R) ^ (a + b) := by
  zpow_norm

-- A.4: Concrete exponent arithmetic (RoundDown:145)
-- Goal: 2^prec * 2^(max_exp - prec + 1) = 2^(max_exp + 1)
example (e : ℤ) :
    (2 : R) ^ prec * (2 : R) ^ (e - prec + 1) = (2 : R) ^ (e + 1) := by
  zpow_norm

-- A.5: One factor with 1 * cleanup (RoundDown:148)
-- Before: `rw [one_mul, two_zpow_mul]; congr 1; ring`
example (a b : ℤ) :
    1 * (2 : R) ^ (a + b) = (2 : R) ^ a * (2 : R) ^ b := by
  zpow_norm

-- A.6: Nested product, three zpow factors
example (a b c : ℤ) :
    (2 : R) ^ a * (2 : R) ^ b * (2 : R) ^ c = (2 : R) ^ (a + b + c) := by
  zpow_norm

/-! ## Pattern B: ℕ↔ℤ exponent cast bridge -/

-- B.1: prec_toNat_eq bridge (RoundDown:162, CommonConstants:90)
-- Before: `rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]`
example :
    (2 : R) ^ FloatFormat.prec.toNat = (2 : R) ^ prec := by
  zpow_norm

-- B.2: prec_sub_one bridge (RoundSubnormal:362)
-- Before: `rw [← zpow_natCast (2 : R), FloatFormat.prec_sub_one_toNat_eq]`
example :
    (2 : R) ^ (prec - 1).toNat = (2 : R) ^ (prec - 1) := by
  zpow_norm

-- B.3: Generic ℕ→ℤ cast (no FloatFormat-specific lemma)
example (n : ℕ) :
    (2 : R) ^ n = (2 : R) ^ (n : ℤ) := by
  zpow_norm

/-! ## Pattern C: Combined cast + collapse -/

-- C.1: Full chain (RoundNormal:538, RoundNormal:608, Neighbor/Basic:287)
-- Before: `rw [← zpow_natCast (2 : R), FloatFormat.prec_sub_one_toNat_eq, two_zpow_mul]; congr 1; ring`
example (e : ℤ) :
    (2 : R) ^ (prec - 1).toNat * (2 : R) ^ (e - prec + 1) = (2 : R) ^ e := by
  zpow_norm

-- C.2: With prec (not prec-1) (Neighbor/Basic:332, MulErrorRepresentable:313)
-- Before: `rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq, two_zpow_mul]; congr 1; ring`
example (e : ℤ) :
    (2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ (e - prec + 1) = (2 : R) ^ (e + 1) := by
  zpow_norm

-- C.3: Scalar × natpow × zpow (GridInstance:188-189)
-- Before: `push_cast; rw [← zpow_natCast ..., two_zpow_mul]; congr 1; rw [...]; ring`
example (x : R) (e : ℤ) :
    x * (2 : R) ^ (prec - 1).toNat * (2 : R) ^ (e - prec + 1) = x * (2 : R) ^ e := by
  zpow_norm

-- C.4: 2 * FloatFormat.prec.toNat version (MulErrorRepresentable:313)
-- Before: `rw [← zpow_natCast (2 : R) (2 * FloatFormat.prec.toNat), two_zpow_mul (R := R)]; congr 1; ...`
-- Note: omega needed for exponent equality involving prec as ℤ
example (e : ℤ) :
    (2 : R) ^ (2 * FloatFormat.prec.toNat) * (2 : R) ^ (e + 1) = (2 : R) ^ (2 * prec + e + 1) := by
  zpow_norm

/-! ## Pattern D: zpow arithmetic (sub, add, add_one) -/

-- D.1: Division / subtraction (Ulp:278, CommonConstants:91)
-- Before: `rw [sub_add, zpow_sub₀ (by norm_num : (2 : R) ≠ 0)]`
example (a b : ℤ) :
    (2 : R) ^ a / (2 : R) ^ b = (2 : R) ^ (a - b) := by
  zpow_norm

-- D.2: zpow_add_one₀ pattern (SplitPositive:174)
-- Before: `rw [zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]; ring`
-- The bare 2 is 2^1
example (n : ℤ) :
    (2 : R) ^ (n + 1) = (2 : R) ^ n * 2 := by
  zpow_norm

-- D.3: Bare 2 recognized as 2^1 (RoundDown:143-144)
-- Before: `rw [mul_comm, show (2:R) * (2:R)^e = (2:R)^(e+1) from ...]`
example (e : ℤ) :
    (2 : R) * (2 : R) ^ e = (2 : R) ^ (e + 1) := by
  zpow_norm

-- D.4: Reverse: split off one factor
example (e : ℤ) :
    (2 : R) ^ (e + 1) = 2 * (2 : R) ^ e := by
  zpow_norm

-- D.5: Mixed division and multiplication (Util.lean pattern)
-- Before: `rw [div_mul_eq_mul_div, ← two_zpow_div, mul_div_assoc]`
example (x : R) (a b : ℤ) :
    x / (2 : R) ^ a * (2 : R) ^ b = x * (2 : R) ^ (b - a) := by
  zpow_norm

-- D.6: x * 2^a / 2^b normalization
example (x : R) (a b : ℤ) :
    x * (2 : R) ^ a / (2 : R) ^ b = x * (2 : R) ^ (a - b) := by
  zpow_norm

/-! ## Pattern E: Exponent equality (after congr 1) -/

-- These test the exponent solver directly. zpow_norm should handle these
-- as part of its final step, but they're also useful standalone tests.

-- E.1: ring-solvable (most common)
example (e : ℤ) : prec + (e - prec + 1) = e + 1 := by
  ring

-- E.2: omega-needed (with ℕ→ℤ casts, MulErrorRepresentable:314)
example : (2 * FloatFormat.prec.toNat : ℤ) = 2 * prec := by
  have := FloatFormat.prec_pos; omega

-- E.3: prec_toNat_eq + ring
example (e : ℤ) : (FloatFormat.prec.toNat : ℤ) + (e - prec + 1) = e + 1 := by
  rw [FloatFormat.prec_toNat_eq]; ring

/-! ## Edge cases -/

-- EC.1: Trivial identity
example (a : ℤ) : (2 : R) ^ a = (2 : R) ^ a := by
  zpow_norm -- should be rfl

-- EC.2: zpow_zero
example : (2 : R) ^ (0 : ℤ) = 1 := by
  zpow_norm

-- EC.3: zpow_one
example : (2 : R) ^ (1 : ℤ) = (2 : R) := by
  zpow_norm

-- EC.4: Both sides have scalar
example (x : R) (a b : ℤ) :
    x * (2 : R) ^ a * (2 : R) ^ b = x * (2 : R) ^ b * (2 : R) ^ a := by
  zpow_norm -- commutativity of exponent addition

-- EC.5: No zpow at all — should fail gracefully
-- example (x y : R) : x + y = y + x := by zpow_norm  -- expected: error

/-! ## Aspirational (may not be in v1) -/

-- ASP.1: Through let bindings
-- example (e : ℤ) : let step := (2 : R) ^ (e - prec + 1);
--     (2 : R) ^ (prec - 1) * step = (2 : R) ^ e := by
--   zpow_norm

-- ASP.2: In hypothesis position
-- example (e : ℤ) (h : (2 : R) ^ (prec - 1) * (2 : R) ^ (e - prec + 1) = (2 : R) ^ e) :
--     True := by
--   zpow_norm at h  -- should close or simplify h
--   trivial
