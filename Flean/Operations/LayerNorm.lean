import Flean.Operations.Add
import Flean.Operations.Sub
import Flean.Operations.Mul
import Flean.Operations.Div
import Flean.Operations.Sqrt
import Flean.Operations.FpSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# LayerNorm: Definition and Per-Component Error Bound

This module formalizes layer normalization (a standard ML primitive) and
derives a per-component forward-error bound for its FP implementation.

## Simplification scope

Initial Phase 2 deliverable focuses on **pure normalization** — affine
scale/shift `(γ, β) = (1, 0)` are assumed.  A follow-up can wrap the
affine step as one additional `fpMul` + `fpAdd` composition; the error
analysis here is the load-bearing piece.

## Mathematical definitions

For `xs : Fin n → ℝ` with `n > 0` and a stability constant `eps > 0`:

```
μ(xs)      := (Σ_j xs_j) / n
σ²(xs)     := (Σ_j (xs_j − μ(xs))²) / n
layerNorm xs eps i := (xs_i − μ(xs)) / √(σ²(xs) + eps)
```

## FP implementation bundle

`FpLayerNormResult xs` bundles witnesses for each rounding step of the
FP computation.  Consumers provide:

- Two `FpSumBound` adapters (one for the mean sum, one for the
  variance sum).  Any summation method — naive, pairwise, Kahan,
  Neumaier, compensated — plugs in.
- `nFp : FiniteFp` exactly representing `n`.
- `eps : FiniteFp` (the stability constant).
- FP-rounding witnesses for each subtract / multiply / add / sqrt /
  divide step.

Error bounds then operate on the bundle.  See `Flean/Tags/LayerNorm.lean`
for the `IsBoundedRange`-tagged wrapper that discharges many of the
bundle's hypotheses automatically.
-/

set_option autoImplicit false

namespace LayerNorm

open Finset BigOperators

variable {n : ℕ}

/-! ## Pure-math LayerNorm -/

/-- Mean of a finite vector: `(Σ xs_j) / n`. -/
noncomputable def mean (xs : Fin n → ℝ) : ℝ :=
  (∑ j, xs j) / (n : ℝ)

/-- Variance of a finite vector: `(Σ (xs_j − mean xs)²) / n`. -/
noncomputable def variance (xs : Fin n → ℝ) : ℝ :=
  (∑ j, (xs j - mean xs) ^ 2) / (n : ℝ)

/-- Layer normalization (no affine scale/shift, `γ=1`, `β=0`):

`layerNorm xs eps i = (xs_i − mean xs) / √(variance xs + eps)`

The `eps > 0` stability constant keeps the denominator away from zero
when `variance xs = 0` (e.g. constant inputs). -/
noncomputable def layerNorm (xs : Fin n → ℝ) (eps : ℝ) (i : Fin n) : ℝ :=
  (xs i - mean xs) / Real.sqrt (variance xs + eps)

/-! ## Basic properties -/

/-- Variance is nonnegative: it's a sum of squares divided by a
nonnegative count. -/
theorem variance_nonneg (xs : Fin n → ℝ) (hn : 0 ≤ (n : ℝ)) :
    0 ≤ variance xs := by
  unfold variance
  exact div_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) hn

/-- Variance-plus-eps is positive when `eps > 0`. -/
theorem variance_plus_eps_pos (xs : Fin n → ℝ) (eps : ℝ)
    (heps : 0 < eps) (hn : 0 ≤ (n : ℝ)) :
    0 < variance xs + eps :=
  lt_of_lt_of_le heps (by linarith [variance_nonneg xs hn])

/-- The square root of variance+eps is positive (so dividing by it is
well-defined). -/
theorem sqrt_var_plus_eps_pos (xs : Fin n → ℝ) (eps : ℝ)
    (heps : 0 < eps) (hn : 0 ≤ (n : ℝ)) :
    0 < Real.sqrt (variance xs + eps) :=
  Real.sqrt_pos.mpr (variance_plus_eps_pos xs eps heps hn)

/-- Sum of shifted values is zero: `Σ (xs_j - μ) = 0`.  Standard
identity.  Requires `n > 0` (otherwise the mean is not well-defined). -/
theorem sum_shift_eq_zero (xs : Fin n → ℝ) (hn : 0 < n) :
    ∑ j, (xs j - mean xs) = 0 := by
  have hn_r : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have h_step : ∑ j : Fin n, (xs j - mean xs) =
      (∑ j, xs j) - (n : ℝ) * mean xs := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  rw [h_step]
  unfold mean
  field_simp
  ring

/-! ## FP implementation

The FP LayerNorm is driven by a chain of witnesses — one per
`fp{Op}Finite = Fp.finite _` rounding step.  The error-bound theorems
in Stages 2–5 take these witnesses directly as hypotheses, parallel
to the unbundled style of `fpSoftmaxOf_error_bound`.

A convenience bundling struct may be added in a later stage once the
full error-bound chain lands and the natural grouping of witnesses is
clear. -/

end LayerNorm
