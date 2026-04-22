import Flean.Tags.AbsBoundPropagate
import Flean.Operations.FpSum
import Flean.Operations.FpDotProduct

/-!
# Tag propagation through `FpSumBound` / `FpDotProductBound`

Bridges the tag layer to the algorithm-bundle layer: given per-index
magnitude bounds on the inputs to a summation or dot product, derive
a magnitude bound on the bundle's `.result`.

## Why this is useful

`FpSumBound` and `FpDotProductBound` wrap a concrete FP summation /
dot-product algorithm with its relative-error bound, opaque to any
input-side magnitude information.  Downstream tagged bounds that want
`HasAbsBound` on the output either have to re-derive it from scratch
(duplicating the triangle inequality + `relErr` slack) or unbundle
the adapter (losing the algorithm abstraction).

This file supplies the per-bundle bridges, so downstream code can
compose tags across the algorithm boundary.

## API shape

For each bundle type (`FpSumBound`, `FpDotProductBound`), three
variants:

1. **Per-index**: per-index `HasAbsBound (c i) (xs i)` hypotheses
   give output bound `(1 + relErr) · Σ c i`.
2. **Uniform**: single `HasAbsBound c` for every input gives output
   bound `(1 + relErr) · n · c`.
3. **From `IsBoundedRange`**: an `IsBoundedRange I xs` tag gives
   output bound `(1 + relErr) · n · I.maxMag`.

The per-index version is primary; the other two are corollaries.

## Design note: option 1 (extrinsic), not option 2 (intrinsic)

Per the backlog (T-M4), we start with extrinsic theorems rather than
adding tag fields to the bundle structs.  If users hit composition
friction that extrinsic theorems can't smoothen out, revisit option 2.
-/

set_option autoImplicit false

namespace FpSum

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## `FpSumBound` → `HasAbsBound` -/

/-- Core bridge: per-index `HasAbsBound (c i) (xs i)` witnesses give a
magnitude bound on the FP sum result.  Combines the bundle's relative
error bound with the triangle inequality on the per-index magnitudes. -/
theorem FpSumBound.hasAbsBound_of_per_index {n : ℕ} {xs : Fin n → FiniteFp}
    (b : FpSumBound xs R) (c : Fin n → R)
    (h_bounds : ∀ i, HasAbsBound (R := R) (c i) (xs i)) :
    HasAbsBound (R := R) ((1 + b.relErr) * ∑ i, c i) b.result := by
  refine ⟨?_⟩
  -- |result| ≤ |result - Σ xs_i.toVal| + |Σ xs_i.toVal|
  have h_tri : |(b.result.toVal : R)| ≤
      |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| +
        |∑ i, ((xs i).toVal : R)| := by
    have : |((b.result.toVal : R) - ∑ i, ((xs i).toVal : R)) +
             ∑ i, ((xs i).toVal : R)| ≤
           |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| +
             |∑ i, ((xs i).toVal : R)| :=
      abs_add_le _ _
    simpa using this
  -- |Σ xs_i.toVal| ≤ Σ |xs_i.toVal| ≤ Σ c i.
  have h_sum_abs : |∑ i, ((xs i).toVal : R)| ≤ ∑ i, |((xs i).toVal : R)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_bound : ∑ i, |((xs i).toVal : R)| ≤ ∑ i, c i :=
    Finset.sum_le_sum (fun i _ => (h_bounds i).toVal_abs_le)
  have h_sum_abs_le : |∑ i, ((xs i).toVal : R)| ≤ ∑ i, c i :=
    le_trans h_sum_abs h_sum_bound
  -- |result - Σ| ≤ relErr · Σ|xs| ≤ relErr · Σ c i.
  have h_err := b.h_bound
  have h_relErr_nn := b.h_relErr_nn
  have h_err_bound : |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| ≤
      b.relErr * ∑ i, c i := by
    have := mul_le_mul_of_nonneg_left h_sum_bound h_relErr_nn
    linarith
  -- Combine.
  calc |(b.result.toVal : R)|
      ≤ |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| +
          |∑ i, ((xs i).toVal : R)| := h_tri
    _ ≤ b.relErr * ∑ i, c i + ∑ i, c i := by linarith
    _ = (1 + b.relErr) * ∑ i, c i := by ring

/-- Uniform variant: a single per-index bound `c` yields
`(1 + relErr) · n · c` on the result. -/
theorem FpSumBound.hasAbsBound_of_uniform {n : ℕ} {xs : Fin n → FiniteFp}
    (b : FpSumBound xs R) (c : R)
    (h_bounds : ∀ i, HasAbsBound (R := R) c (xs i)) :
    HasAbsBound (R := R) ((1 + b.relErr) * (n : R) * c) b.result := by
  have h := b.hasAbsBound_of_per_index (fun _ => c) h_bounds
  have h_sum : (∑ _i : Fin n, c) = (n : R) * c := by
    rw [Finset.sum_const]; simp [mul_comm]
  rw [h_sum] at h
  refine h.weaken ?_
  rw [mul_assoc]

/-- `IsBoundedRange I xs` gives `(1 + relErr) · n · I.maxMag` on the result. -/
theorem FpSumBound.hasAbsBound_of_isBoundedRange {n : ℕ} {xs : Fin n → FiniteFp}
    (b : FpSumBound xs R)
    {I : FpInterval R} (h : IsBoundedRange (R := R) I xs) :
    HasAbsBound (R := R) ((1 + b.relErr) * (n : R) * I.maxMag) b.result :=
  b.hasAbsBound_of_uniform I.maxMag (fun i => ⟨h.toVal_abs_le i⟩)

/-! ## `FpSumBoundCompensated` → `HasAbsBound` on `sigma`

Mirror of the `FpSumBound` suite.  Bound applies to the **compensated
value** `sigma := sum.toVal + comp.toVal`, not to `sum.toVal` alone;
`sigma` is the quantity that matches the true `Σ xs` closely.  For a
magnitude bound on `sum.toVal` (instead of `sigma`), combine with
`compErr` via the triangle inequality. -/

/-- Core bridge for compensated sums: per-index magnitude bounds give a
bound on `sigma = sum + comp`. -/
theorem FpSumBoundCompensated.hasAbsBound_sigma_of_per_index {n : ℕ}
    {xs : Fin n → FiniteFp} (cb : FpSumBoundCompensated xs R)
    (c : Fin n → R) (h_bounds : ∀ i, HasAbsBound (R := R) (c i) (xs i)) :
    |((cb.sum.toVal : R) + cb.comp.toVal)| ≤ (1 + cb.relErr) * ∑ i, c i := by
  have h_tri : |((cb.sum.toVal : R) + cb.comp.toVal)| ≤
      |((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R)| +
        |∑ i, ((xs i).toVal : R)| := by
    have : |(((cb.sum.toVal : R) + cb.comp.toVal) -
              ∑ i, ((xs i).toVal : R)) +
             ∑ i, ((xs i).toVal : R)| ≤
           |((cb.sum.toVal : R) + cb.comp.toVal) -
              ∑ i, ((xs i).toVal : R)| +
             |∑ i, ((xs i).toVal : R)| :=
      abs_add_le _ _
    simpa using this
  have h_sum_abs : |∑ i, ((xs i).toVal : R)| ≤ ∑ i, |((xs i).toVal : R)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_bound : ∑ i, |((xs i).toVal : R)| ≤ ∑ i, c i :=
    Finset.sum_le_sum (fun i _ => (h_bounds i).toVal_abs_le)
  have h_sum_abs_le : |∑ i, ((xs i).toVal : R)| ≤ ∑ i, c i :=
    le_trans h_sum_abs h_sum_bound
  have h_err := cb.h_bound
  have h_relErr_nn := cb.h_relErr_nn
  have h_err_bound :
      |((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R)| ≤
        cb.relErr * ∑ i, c i := by
    have := mul_le_mul_of_nonneg_left h_sum_bound h_relErr_nn
    linarith
  calc |((cb.sum.toVal : R) + cb.comp.toVal)|
      ≤ |((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R)| +
          |∑ i, ((xs i).toVal : R)| := h_tri
    _ ≤ cb.relErr * ∑ i, c i + ∑ i, c i := by linarith
    _ = (1 + cb.relErr) * ∑ i, c i := by ring

/-- Uniform variant. -/
theorem FpSumBoundCompensated.hasAbsBound_sigma_of_uniform {n : ℕ}
    {xs : Fin n → FiniteFp} (cb : FpSumBoundCompensated xs R)
    (c : R) (h_bounds : ∀ i, HasAbsBound (R := R) c (xs i)) :
    |((cb.sum.toVal : R) + cb.comp.toVal)| ≤ (1 + cb.relErr) * (n : R) * c := by
  have h := cb.hasAbsBound_sigma_of_per_index (fun _ => c) h_bounds
  have h_sum : (∑ _i : Fin n, c) = (n : R) * c := by
    rw [Finset.sum_const]; simp [mul_comm]
  rw [h_sum] at h
  have : (1 + cb.relErr) * ((n : R) * c) = (1 + cb.relErr) * (n : R) * c := by
    rw [mul_assoc]
  linarith

/-- `IsBoundedRange`-driven variant. -/
theorem FpSumBoundCompensated.hasAbsBound_sigma_of_isBoundedRange {n : ℕ}
    {xs : Fin n → FiniteFp} (cb : FpSumBoundCompensated xs R)
    {I : FpInterval R} (h : IsBoundedRange (R := R) I xs) :
    |((cb.sum.toVal : R) + cb.comp.toVal)| ≤
      (1 + cb.relErr) * (n : R) * I.maxMag :=
  cb.hasAbsBound_sigma_of_uniform I.maxMag (fun i => ⟨h.toVal_abs_le i⟩)

end FpSum

namespace FpDotProduct

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## `FpDotProductBound` → `HasAbsBound` -/

/-- Core bridge for dot products: per-index magnitude bounds on both
vectors give a magnitude bound on the FP dot-product result.

`0 ≤ c_x i` is derived automatically from the tag hypotheses via
`HasAbsBound.c_nonneg`, so the caller doesn't need to supply it. -/
theorem FpDotProductBound.hasAbsBound_of_per_index
    {n : ℕ} {xs ys : Fin n → FiniteFp} (b : FpDotProductBound xs ys R)
    (c_x c_y : Fin n → R)
    (h_x : ∀ i, HasAbsBound (R := R) (c_x i) (xs i))
    (h_y : ∀ i, HasAbsBound (R := R) (c_y i) (ys i)) :
    HasAbsBound (R := R) ((1 + b.relErr) * ∑ i, c_x i * c_y i) b.result := by
  have hc_x_nn : ∀ i, 0 ≤ c_x i := fun i => (h_x i).c_nonneg
  refine ⟨?_⟩
  have h_tri : |(b.result.toVal : R)| ≤
      |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| +
        |∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| := by
    have : |((b.result.toVal : R) - ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)) +
             ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
           |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| +
             |∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| :=
      abs_add_le _ _
    simpa using this
  -- Per-index product bound.
  have h_prod_bound : ∀ i, |((xs i).toVal : R) * ((ys i).toVal : R)| ≤ c_x i * c_y i := by
    intro i
    rw [abs_mul]
    exact mul_le_mul (h_x i).toVal_abs_le (h_y i).toVal_abs_le
      (abs_nonneg _) (hc_x_nn i)
  have h_sum_abs : |∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
      ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_bound :
      ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| ≤ ∑ i, c_x i * c_y i :=
    Finset.sum_le_sum (fun i _ => h_prod_bound i)
  have h_sum_abs_le :
      |∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤ ∑ i, c_x i * c_y i :=
    le_trans h_sum_abs h_sum_bound
  -- relErr side.
  have h_err := b.h_bound
  have h_relErr_nn := b.h_relErr_nn
  have h_err_bound :
      |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
        b.relErr * ∑ i, c_x i * c_y i := by
    have := mul_le_mul_of_nonneg_left h_sum_bound h_relErr_nn
    linarith
  calc |(b.result.toVal : R)|
      ≤ |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| +
          |∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| := h_tri
    _ ≤ b.relErr * ∑ i, c_x i * c_y i + ∑ i, c_x i * c_y i := by linarith
    _ = (1 + b.relErr) * ∑ i, c_x i * c_y i := by ring

/-- Uniform variant: single per-index bounds `c_x, c_y` for both vectors.

The nonempty hypothesis on `n` is needed only to derive
`0 ≤ c_x` from the tag (via `c_nonneg`).  If `n = 0` the claim is
vacuous (the sum is empty and the result is undefined — in practice
the bundle wouldn't exist for `n = 0` either). -/
theorem FpDotProductBound.hasAbsBound_of_uniform
    {n : ℕ} {xs ys : Fin n → FiniteFp} (b : FpDotProductBound xs ys R)
    (c_x c_y : R)
    (h_x : ∀ i, HasAbsBound (R := R) c_x (xs i))
    (h_y : ∀ i, HasAbsBound (R := R) c_y (ys i)) :
    HasAbsBound (R := R) ((1 + b.relErr) * (n : R) * (c_x * c_y)) b.result := by
  have h := b.hasAbsBound_of_per_index (fun _ => c_x) (fun _ => c_y) h_x h_y
  have h_sum : (∑ _i : Fin n, c_x * c_y) = (n : R) * (c_x * c_y) := by
    rw [Finset.sum_const]; simp [mul_comm]
  rw [h_sum] at h
  refine h.weaken ?_
  rw [mul_assoc]

/-- From `IsBoundedRange` on both vectors, an `HasAbsBound` on the result. -/
theorem FpDotProductBound.hasAbsBound_of_isBoundedRange
    {n : ℕ} {xs ys : Fin n → FiniteFp} (b : FpDotProductBound xs ys R)
    {Ix Iy : FpInterval R}
    (hx : IsBoundedRange (R := R) Ix xs) (hy : IsBoundedRange (R := R) Iy ys) :
    HasAbsBound (R := R)
      ((1 + b.relErr) * (n : R) * (Ix.maxMag * Iy.maxMag)) b.result :=
  b.hasAbsBound_of_uniform Ix.maxMag Iy.maxMag
    (fun i => ⟨hx.toVal_abs_le i⟩) (fun i => ⟨hy.toVal_abs_le i⟩)

end FpDotProduct
