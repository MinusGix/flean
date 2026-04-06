import Flean.Operations.Horner
import Flean.Operations.JetHorner
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

/-! ## JetHorner / polyDeriv Connection -/

namespace JetHorner

open Horner

variable {R : Type*} [Field R]

/-- The value component of `jetHornerExact` equals `hornerPoly`.
    The derivative input `d` is irrelevant for the value. -/
theorem jetHornerExact_fst_eq_hornerPoly (cs : List R) (init d x : R) :
    (jetHornerExact cs init d x).1 = hornerPoly cs init x := by
  induction cs generalizing init d with
  | nil => simp [jetHornerExact, hornerPoly]
  | cons c cs ih =>
    simp only [jetHornerExact, hornerPoly]
    rw [ih, mul_comm x init]

/-- `hornerListPoly` cons recurrence: prepending a coefficient `c` adds `C c * X^n`. -/
theorem hornerListPoly_cons (c : R) (cs : List R) :
    hornerListPoly (c :: cs) =
      C c * X ^ cs.length + hornerListPoly cs := by
  simp only [hornerListPoly, List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [List.get_cons_zero, Fin.val_zero, Nat.sub_zero, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [List.get_cons_succ, Fin.val_succ]
  congr 2
  omega

/-- **polyDeriv connection**: `polyDeriv cs 0 x = (hornerListPoly cs).derivative.eval x`.

    This validates our JetHorner derivative computation against Mathlib's
    formal polynomial derivative: the jet Horner recurrence computes the same
    derivative as Mathlib's formal `Polynomial.derivative`.

    Proof: by induction on `cs`, using `hornerListPoly_cons` to decompose the
    polynomial and `polyDeriv_affine` to handle the accumulator shift. -/
theorem polyDeriv_eq_derivative_eval
    (cs : List R) (x : R) :
    polyDeriv cs 0 x = (Horner.hornerListPoly cs).derivative.eval x := by
  induction cs with
  | nil => simp [polyDeriv_nil, Horner.hornerListPoly_nil]
  | cons c cs ih =>
    -- LHS: polyDeriv (c::cs) 0 x = polyDeriv cs c x (by polyDeriv_cons with init=0)
    --     = polyDeriv cs 0 x + cs.length * x^{cs.length-1} * c (by polyDeriv_affine)
    rw [polyDeriv_cons, show x * 0 + c = 0 + c from by ring, polyDeriv_affine]
    -- RHS: derivative(C c * X^n + hornerListPoly cs).eval x
    --     = (C (c * n) * X^{n-1}).eval x + (hornerListPoly cs).derivative.eval x
    --     = c * n * x^{n-1} + (hornerListPoly cs).derivative.eval x
    rw [hornerListPoly_cons, map_add, derivative_C_mul_X_pow, Polynomial.eval_add,
      eval_mul, eval_C, eval_pow, eval_X]
    -- Now both sides have (hornerListPoly cs).derivative.eval x; use IH
    rw [← ih]
    ring

end JetHorner
