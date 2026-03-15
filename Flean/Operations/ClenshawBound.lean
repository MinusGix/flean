import Flean.Operations.Clenshaw

/-!
# Clenshaw Error Bounds via Quadratic Invariant

The Clenshaw linear map `L(a,b) = (w·a - b, a)` preserves the quadratic form
`Q(a,b) = a² - w·a·b + b²`. This is the key to tight error bounds:

- For `|w| < 2` (i.e., `|x| < 1` with `w = 2x`): Q is positive definite,
  and Q-preservation gives bounded (non-exponential) error growth.
- The spectral radius of L is 1 for `|w| ≤ 2`, matching the Q-invariance.

## Approach

Instead of fitting into the `Gauge` framework (which would need √Q),
we prove the Q-invariant directly and derive squared component bounds:
- `Q(a,b) ≥ (1 - |w|/2)(a² + b²)` when `|w| < 2`
- So `a² ≤ Q(a,b) / (1 - |w|/2)`

This avoids square roots while giving the tight bound.
-/

namespace ClenshawBound

open Clenshaw

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Quadratic Invariant -/

/-- The quadratic form preserved by Clenshaw's linear map. -/
def Q (w a b : R) : R := a ^ 2 - w * a * b + b ^ 2

/-- **Q-invariance**: the Clenshaw step preserves Q exactly.

    `Q(w·a - b, a) = Q(a, b)`

    This is the fundamental reason Clenshaw is stable for `|w| ≤ 2`. -/
theorem Q_step_invariant (w a b : R) :
    Q w (w * a - b) a = Q w a b := by
  unfold Q; ring

/-- **Q-invariance for propagation**: after n steps, Q is preserved.

    `Q(clenshawProp n ea eb w) = Q(ea, eb)` -/
theorem Q_prop_invariant (n : ℕ) (ea eb w : R) :
    Q w (clenshawProp n ea eb w).1 (clenshawProp n ea eb w).2 = Q w ea eb := by
  induction n generalizing ea eb with
  | zero => simp [clenshawProp]
  | succ n ih =>
    simp only [clenshawProp]
    rw [ih]
    exact Q_step_invariant w ea eb

/-! ## Positive Definiteness -/

/-- When `|w| < 2`, Q is bounded below by `(1 - |w|/2)(a² + b²)`.

    This means Q is positive definite, and Q-preservation implies
    bounded component growth. -/
theorem Q_lower_bound (w a b : R) (hw : |w| < 2) :
    (1 - |w| / 2) * (a ^ 2 + b ^ 2) ≤ Q w a b := by
  unfold Q
  -- Key: Q - (1-|w|/2)(a²+b²) = |w|/2 · (a² - 2|a||b| + b²) + (|w|·|a|·|b| - w·a·b)
  --     = |w|/2 · (|a|-|b|)² + (|w|·|a|·|b| - w·a·b) ≥ 0
  -- since |w·a·b| ≤ |w|·|a|·|b|, i.e., w·a·b ≤ |w|·|a|·|b|
  have h_sq_a : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have h_sq_b : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  have h_diff_sq : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg _
  have h_w_nn : 0 ≤ |w| := abs_nonneg w
  have h_a_nn : 0 ≤ |a| := abs_nonneg a
  have h_b_nn : 0 ≤ |b| := abs_nonneg b
  have h_wab : w * a * b ≤ |w| * |a| * |b| := by
    have h := le_abs_self (w * a * b)
    rwa [abs_mul, abs_mul] at h
  -- The identity: Q - (1-|w|/2)(a²+b²) = |w|/2·(|a|-|b|)² + (|w|·|a|·|b| - w·a·b)
  -- Both terms ≥ 0. After substituting a²=|a|², b²=|b|², this follows from nlinarith.
  nlinarith [sq_nonneg (|a| - |b|), mul_nonneg h_w_nn h_diff_sq,
             mul_nonneg (mul_nonneg h_w_nn h_a_nn) h_b_nn]

/-- Coefficient `1 - |w|/2` is positive when `|w| < 2`. -/
theorem one_sub_half_w_pos (w : R) (hw : |w| < 2) : 0 < 1 - |w| / 2 := by
  linarith

/-! ## Component Bounds from Q-Invariance -/

/-- **Squared component bound**: after n propagation steps,
    `(prop.1)² + (prop.2)² ≤ Q(ea, eb) / (1 - |w|/2)`.

    This bounds both components simultaneously without square roots. -/
theorem prop_sq_bound (n : ℕ) (ea eb w : R) (hw : |w| < 2) :
    (clenshawProp n ea eb w).1 ^ 2 + (clenshawProp n ea eb w).2 ^ 2 ≤
      Q w ea eb / (1 - |w| / 2) := by
  have hpos := one_sub_half_w_pos w hw
  rw [le_div_iff₀ hpos]
  have hinv := Q_prop_invariant n ea eb w
  have hlower := Q_lower_bound w (clenshawProp n ea eb w).1 (clenshawProp n ea eb w).2 hw
  linarith

/-- **First component squared bound**: `(prop.1)² ≤ Q(ea, eb) / (1 - |w|/2)`. -/
theorem prop_fst_sq_bound (n : ℕ) (ea eb w : R) (hw : |w| < 2) :
    (clenshawProp n ea eb w).1 ^ 2 ≤ Q w ea eb / (1 - |w| / 2) := by
  have h := prop_sq_bound n ea eb w hw
  linarith [sq_nonneg (clenshawProp n ea eb w).2]

/-- **Q value for zero-perturbation in second component**: `Q(ea, 0) = ea²`. -/
theorem Q_zero_snd (w ea : R) : Q w ea 0 = ea ^ 2 := by
  unfold Q; ring

/-- **Propagation from (ea, 0)**: components satisfy `fst² + snd² ≤ ea² / (1 - |w|/2)`.

    This is the typical case for error propagation (perturbation only in first component). -/
theorem prop_from_zero_sq_bound (n : ℕ) (ea w : R) (hw : |w| < 2) :
    (clenshawProp n ea 0 w).1 ^ 2 + (clenshawProp n ea 0 w).2 ^ 2 ≤
      ea ^ 2 / (1 - |w| / 2) := by
  rw [← Q_zero_snd w ea]
  exact prop_sq_bound n ea 0 w hw

end ClenshawBound
