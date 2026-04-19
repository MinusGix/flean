import Flean.Operations.FpDotProduct

/-!
# Generic Floating-Point Matrix-Vector Product with Error Bound

Parallel to `Flean/Operations/FpDotProduct.lean`, one level up: bundles a
computed matrix-vector product `A·x` with a *uniform* relative error bound
holding row-wise. Built row-by-row on top of `FpDotProductBound`.

## Main definitions

* `FpMatVecBound A x R` — bundles `result : Fin m → FiniteFp` with a uniform
  `relErr` bounding `|result i - Σⱼ A_{ij}·xⱼ| ≤ relErr · Σⱼ |A_{ij}·xⱼ|` for
  every row `i`.
* `FpMatVecBound.ofRows` — assemble from per-row `FpDotProductBound` given a
  uniform upper bound on the row relErrs.

Users pick their row algorithm (naive, FMA, compensated-then-collapse, etc.)
to build the row-wise `FpDotProductBound`, and this file stitches the rows
together under a single coarse error coefficient.
-/

set_option autoImplicit false

namespace FpMatVec

open Finset BigOperators FpDotProduct

variable [FloatFormat]

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The `FpMatVecBound` structure -/

/-- Bundles a computed FP matrix-vector product `A·x` with a uniform
row-wise relative error bound. -/
structure FpMatVecBound {m n : ℕ}
    (A : Fin m → Fin n → FiniteFp) (x : Fin n → FiniteFp) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] where
  /-- The FP vector result. -/
  result : Fin m → FiniteFp
  /-- Uniform relative error coefficient across rows. -/
  relErr : R
  /-- Nonnegativity of `relErr`. -/
  h_relErr_nn : (0 : R) ≤ relErr
  /-- Row-wise bound: each row's FP value is within `relErr` of the true inner product. -/
  h_bound : ∀ i, |((result i).toVal : R) -
                   ∑ j, ((A i j).toVal : R) * ((x j).toVal : R)| ≤
                 relErr *
                 ∑ j, |((A i j).toVal : R) * ((x j).toVal : R)|

/-! ## Adapter: per-row `FpDotProductBound` → `FpMatVecBound` -/

section OfRows

/-- **Constructor**: assemble per-row dot-product bounds under a uniform
upper bound on their `relErr`s. -/
def FpMatVecBound.ofRows {m n : ℕ}
    {A : Fin m → Fin n → FiniteFp} {x : Fin n → FiniteFp}
    (rows : ∀ i, FpDotProductBound (A i) x R)
    (ub : R) (hub_nn : (0 : R) ≤ ub)
    (h_ub : ∀ i, (rows i).relErr ≤ ub) :
    FpMatVecBound A x R :=
  { result := fun i => (rows i).result
    relErr := ub
    h_relErr_nn := hub_nn
    h_bound := by
      intro i
      have habs_nn : (0 : R) ≤
          ∑ j, |((A i j).toVal : R) * ((x j).toVal : R)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      calc |(((rows i).result.toVal) : R) -
              ∑ j, ((A i j).toVal : R) * ((x j).toVal : R)|
          ≤ (rows i).relErr *
              ∑ j, |((A i j).toVal : R) * ((x j).toVal : R)| :=
            (rows i).h_bound
        _ ≤ ub * ∑ j, |((A i j).toVal : R) * ((x j).toVal : R)| :=
            mul_le_mul_of_nonneg_right (h_ub i) habs_nn }

/-- **Convenience constructor**: take the uniform coefficient to be the
`sup` of the per-row `relErr`s. Only defined for `m > 0`. -/
def FpMatVecBound.ofRowsMax {m n : ℕ}
    {A : Fin m → Fin n → FiniteFp} {x : Fin n → FiniteFp}
    (rows : ∀ i, FpDotProductBound (A i) x R)
    (hm : 0 < m) :
    FpMatVecBound A x R :=
  let ub := Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
            (fun i => (rows i).relErr)
  have hub_nn : (0 : R) ≤ ub := by
    have h0 := (rows ⟨0, hm⟩).h_relErr_nn
    exact le_trans h0 (Finset.le_sup' (f := fun i => (rows i).relErr)
      (Finset.mem_univ ⟨0, hm⟩))
  have h_ub : ∀ i, (rows i).relErr ≤ ub := fun i =>
    Finset.le_sup' (f := fun i => (rows i).relErr) (Finset.mem_univ i)
  FpMatVecBound.ofRows rows ub hub_nn h_ub

end OfRows

/-! ## Structural adapters -/

section Adapters

/-- Relax the relative-error coefficient. -/
def FpMatVecBound.weaken {m n : ℕ}
    {A : Fin m → Fin n → FiniteFp} {x : Fin n → FiniteFp}
    (b : FpMatVecBound A x R) (newRelErr : R)
    (h_ge : b.relErr ≤ newRelErr) :
    FpMatVecBound A x R :=
  { result := b.result
    relErr := newRelErr
    h_relErr_nn := le_trans b.h_relErr_nn h_ge
    h_bound := by
      intro i
      have habs_nn : (0 : R) ≤
          ∑ j, |((A i j).toVal : R) * ((x j).toVal : R)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      calc |((b.result i).toVal : R) -
              ∑ j, ((A i j).toVal : R) * ((x j).toVal : R)|
          ≤ b.relErr * ∑ j, |((A i j).toVal : R) * ((x j).toVal : R)| := b.h_bound i
        _ ≤ newRelErr * ∑ j, |((A i j).toVal : R) * ((x j).toVal : R)| :=
            mul_le_mul_of_nonneg_right h_ge habs_nn }

/-- Rewrite the inputs along pointwise equalities. -/
def FpMatVecBound.congr {m n : ℕ}
    {A A' : Fin m → Fin n → FiniteFp} {x x' : Fin n → FiniteFp}
    (b : FpMatVecBound A x R) (hA : A = A') (hx : x = x') :
    FpMatVecBound A' x' R :=
  hx ▸ hA ▸ b

end Adapters

end FpMatVec
