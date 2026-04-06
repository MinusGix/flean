import Flean.Operations.Horner
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Connection to Mathlib Polynomials

Bridges between `hornerPoly` (our recursive Horner evaluation) and
Mathlib's `Polynomial.eval`, enabling access to Mathlib's polynomial algebra
(degree, roots, derivative via `Polynomial.derivative`, etc.).

## Main Results

- `hornerListPoly`: convert a coefficient list to a Mathlib `Polynomial`
- `hornerPoly_eq_eval`: `hornerPoly cs 0 x = (hornerListPoly cs).eval x`
- `hornerListPoly_derivative_eval`: derivative evaluation as a sum

## Coefficient Convention

Our `hornerPoly [c₀, c₁, ..., cₙ₋₁] 0 x` evaluates
`c₀·x^{n-1} + c₁·x^{n-2} + ... + cₙ₋₁`, where `cs[i]` is the
coefficient of `x^{n-1-i}`. In Mathlib's convention, `Polynomial.coeff p k`
gives the coefficient of `x^k`, so the coefficient of `x^k` in
`hornerListPoly cs` is `cs[n-1-k]` (reversed indexing).
-/

open Polynomial

variable {R : Type*} [CommRing R]

namespace Horner

/-! ## hornerPoly as a Finset sum -/

/-- `hornerPoly cs acc x = acc * x^n + hornerPoly cs 0 x`. -/
private theorem hornerPoly_acc_eq' (cs : List R) (acc x : R) :
    hornerPoly cs acc x = acc * x ^ cs.length + hornerPoly cs 0 x := by
  induction cs generalizing acc with
  | nil => simp [hornerPoly]
  | cons c cs ih =>
    simp only [hornerPoly, zero_mul, zero_add, List.length_cons]
    rw [ih (acc * x + c), ih c]
    ring

/-- `hornerPoly cs 0 x` as a Finset sum: `Σ cs[i] · x^{n-1-i}`.
    Standalone version with minimal typeclasses (`CommRing R`). -/
theorem hornerPoly_eq_fin_sum' (cs : List R) (x : R) :
    hornerPoly cs 0 x =
      ∑ i : Fin cs.length, cs.get i * x ^ (cs.length - 1 - i.val) := by
  induction cs with
  | nil => simp [hornerPoly]
  | cons c cs ih =>
    simp only [hornerPoly, zero_mul, zero_add, List.length_cons]
    rw [hornerPoly_acc_eq' cs c x, ih, add_comm, Fin.sum_univ_succ]
    simp only [List.get_cons_zero, Fin.val_zero, Nat.sub_zero]
    rw [show c * x ^ cs.length = c * x ^ (cs.length + 1 - 1) by simp]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hexp : cs.length - 1 - i.val = cs.length + 1 - 1 - i.succ.val := by
      simp [Fin.val_succ]; omega
    rw [hexp]; simp

/-! ## Mathlib Polynomial Connection -/

/-- Convert a coefficient list (Horner ordering) to a Mathlib `Polynomial`.

    `hornerListPoly [c₀, c₁, ..., cₙ₋₁]` represents the polynomial
    `c₀·X^{n-1} + c₁·X^{n-2} + ... + cₙ₋₁`, matching `hornerPoly cs 0 x`. -/
noncomputable def hornerListPoly (cs : List R) : R[X] :=
  ∑ i : Fin cs.length, C (cs.get i) * X ^ (cs.length - 1 - i.val)

/-- Evaluating `hornerListPoly` distributes into a sum of `cᵢ · x^{n-1-i}`. -/
theorem hornerListPoly_eval (cs : List R) (x : R) :
    (hornerListPoly cs).eval x =
      ∑ i : Fin cs.length, cs.get i * x ^ (cs.length - 1 - i.val) := by
  simp [hornerListPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

/-- **Main theorem**: `hornerPoly cs 0 x = (hornerListPoly cs).eval x`.

    This connects our recursive Horner evaluation to Mathlib's polynomial
    evaluation, giving access to Mathlib's polynomial algebra. -/
theorem hornerPoly_eq_eval (cs : List R) (x : R) :
    hornerPoly cs 0 x = (hornerListPoly cs).eval x := by
  rw [hornerListPoly_eval, hornerPoly_eq_fin_sum']

/-- `hornerListPoly` of the empty list is zero. -/
@[simp]
theorem hornerListPoly_nil : hornerListPoly ([] : List R) = 0 := by
  simp [hornerListPoly]

/-- The derivative of `hornerListPoly` evaluated at `x`. -/
theorem hornerListPoly_derivative_eval (cs : List R) (x : R) :
    (hornerListPoly cs).derivative.eval x =
      ∑ i : Fin cs.length, cs.get i *
        ((cs.length - 1 - i.val : ℕ) : R) * x ^ (cs.length - 1 - i.val - 1) := by
  simp only [hornerListPoly, map_sum, derivative_C_mul_X_pow]
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

end Horner
