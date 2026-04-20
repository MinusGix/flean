import Flean.Operations.Add
import Flean.Operations.Sub
import Flean.Operations.Mul
import Flean.Operations.Div
import Flean.Operations.Sqrt
import Flean.Operations.FpSum
import Flean.Operations.FpFiniteRound
import Flean.Rounding.RoundPreserves
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
take these witnesses directly as hypotheses, parallel to the unbundled
style of `fpSoftmaxOf_error_bound`.  A convenience bundling struct may
be added in a later stage once the full error-bound chain lands. -/

section FP

variable [FloatFormat]

/-! ### Stage 2: mean + shift error bound -/

/-- **Mean error bound**.  Given a summation witness `sumBound`
producing `sumBound.result` + an exact-integer FP representation `nFp`
of `n` + an `fpDivFinite` witness giving `mean` + normal-range
hypotheses on the quotient, the FP mean differs from the exact mean
`μ = (Σ xs) / n` by at most one division rounding step plus the
propagated summation error.

```
|mean.toVal − μ| ≤ η · |Ŝ/n̂| + relErr · (Σ|xs|) / n
```

where `Ŝ = sumBound.result.toVal` and `n̂ = nFp.toVal = n`.  The first
term is the division's rounding slack; the second is the summation
error propagated through the divide. -/
theorem fpMean_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ]
    {xs : Fin n → FiniteFp}
    (hn_pos : 0 < n)
    (sumBound : FpSum.FpSumBound xs ℝ)
    {nFp mean : FiniteFp}
    (hNFp_toVal : (nFp.toVal : ℝ) = (n : ℝ))
    (hNFp_m_ne : nFp.m ≠ 0)
    (h_mean : fpDivFinite sumBound.result nFp = Fp.finite mean)
    (h_quot_ne : (sumBound.result.toVal : ℝ) / nFp.toVal ≠ 0)
    (h_quot_normal :
      (2 : ℝ) ^ FloatFormat.min_exp ≤
        |(sumBound.result.toVal : ℝ) / nFp.toVal|) :
    |(mean.toVal : ℝ) - (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ)| ≤
      (η : ℝ) * |(sumBound.result.toVal : ℝ) / nFp.toVal| +
      sumBound.relErr * (∑ j, |((xs j).toVal : ℝ)|) / (n : ℝ) := by
  -- Abbreviations (kept as explicit `have`s so `rw` on `hNFp_toVal`
  -- can still reach the raw expressions when needed).
  have hn_r_pos : (0 : ℝ) < (nFp.toVal : ℝ) := by
    rw [hNFp_toVal]; exact_mod_cast hn_pos
  have hn_r_ne : (nFp.toVal : ℝ) ≠ 0 := ne_of_gt hn_r_pos
  -- Division via fpDivFinite_correct + round preservation.
  have h_div_round :
      (RMode.round ((sumBound.result.toVal : ℝ) / nFp.toVal) : Fp) =
        Fp.finite mean := by
    have heq :=
      fpDivFinite_correct (R := ℝ) sumBound.result nFp hNFp_m_ne h_quot_ne
    simp only [div_eq_fpDiv, fpDiv, hNFp_m_ne, ↓reduceIte,
               div_finite_eq_fpDivFinite] at heq
    rw [h_mean] at heq
    exact heq.symm
  have h_div_err :
      |(mean.toVal : ℝ) - (sumBound.result.toVal : ℝ) / nFp.toVal| ≤
        (η : ℝ) * |(sumBound.result.toVal : ℝ) / nFp.toVal| :=
    round_preserves_abs_error_normal h_quot_normal h_div_round
  -- Sum error via sumBound.
  have h_sum_err :
      |(sumBound.result.toVal : ℝ) - ∑ j, ((xs j).toVal : ℝ)| ≤
        sumBound.relErr * ∑ j, |((xs j).toVal : ℝ)| :=
    sumBound.h_bound
  -- The middle error: (Shat − S) / N has magnitude ≤ relErr · (Σ|xs|) / n.
  have h_mid_err :
      |(sumBound.result.toVal : ℝ) / nFp.toVal -
         (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ)| ≤
        sumBound.relErr * (∑ j, |((xs j).toVal : ℝ)|) / (n : ℝ) := by
    have hdiff :
        (sumBound.result.toVal : ℝ) / nFp.toVal -
            (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ) =
        ((sumBound.result.toVal : ℝ) - ∑ j, ((xs j).toVal : ℝ)) /
            (n : ℝ) := by
      rw [hNFp_toVal]; ring
    rw [hdiff, abs_div]
    have habs_n : |((n : ℝ))| = (n : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
      exact abs_of_nonneg this
    rw [habs_n]
    have hn_r_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have hn_r_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    exact div_le_div_of_nonneg_right h_sum_err hn_r_nn
  -- Triangle inequality.
  have htri :
      |(mean.toVal : ℝ) - (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ)| ≤
        |(mean.toVal : ℝ) - (sumBound.result.toVal : ℝ) / nFp.toVal| +
        |(sumBound.result.toVal : ℝ) / nFp.toVal -
          (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ)| :=
    abs_sub_le _ _ _
  linarith

/-- **Shift error bound**.  Given an `fpSubFinite` witness for one
entry, the shifted FP value differs from the exact shift `x_i − μ`
by one subtraction rounding step plus the mean's error:

```
|shifted_i − (x_i − μ)| ≤ η · |x_i − μ̂| + |μ̂ − μ|
```

where `μ̂ = mean.toVal` is the FP mean.  The first term is the
subtraction's rounding slack (normal-range regime); the second is the
propagated mean error (`δ_mean` in downstream analyses). -/
theorem fpShift_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
    [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]
    {xs : Fin n → FiniteFp} {mean : FiniteFp}
    (shifted : Fin n → FiniteFp)
    (h_shifted : ∀ i, fpSubFinite (xs i) mean = Fp.finite (shifted i))
    (i : Fin n)
    (h_shift_normal :
      (2 : ℝ) ^ FloatFormat.min_exp ≤ |((xs i).toVal : ℝ) - mean.toVal|) :
    |((shifted i).toVal : ℝ) -
        (((xs i).toVal : ℝ) -
          (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ))| ≤
      (η : ℝ) * |((xs i).toVal : ℝ) - mean.toVal| +
      |(mean.toVal : ℝ) - (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ)| := by
  -- fpSubFinite (xs i) mean = fpAddFinite (xs i) (-mean) by definition.
  have h_add : fpAddFinite (xs i) (-mean) = Fp.finite (shifted i) :=
    h_shifted i
  obtain ⟨g, hg_round, hg_eq⟩ :=
    fpAddFinite_round_witness (R := ℝ) (xs i) (-mean) h_add
  -- (xs i).toVal + (-mean).toVal = (xs i).toVal - mean.toVal.
  have h_diff_eq :
      ((xs i).toVal : ℝ) + ((-mean).toVal : ℝ) =
        ((xs i).toVal : ℝ) - mean.toVal := by
    rw [FiniteFp.toVal_neg_eq_neg (R := ℝ) mean]; ring
  rw [h_diff_eq] at hg_round
  -- Subtraction rounding error.
  have h_sub_err :
      |(g.toVal : ℝ) - (((xs i).toVal : ℝ) - mean.toVal)| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - mean.toVal| :=
    round_preserves_abs_error_normal h_shift_normal hg_round
  -- Transport through g.toVal = (shifted i).toVal.
  have h_sub_err' :
      |((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - mean.toVal)| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - mean.toVal| := by
    rw [← hg_eq]; exact h_sub_err
  -- Triangle inequality: split the exact shift via the FP mean.
  set μ : ℝ := (∑ j, ((xs j).toVal : ℝ)) / (n : ℝ) with hμ_def
  have htri :
      |((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - μ)| ≤
        |((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - mean.toVal)| +
        |(mean.toVal : ℝ) - μ| := by
    have hdiff :
        ((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - μ) =
          (((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - mean.toVal)) +
          (μ - (mean.toVal : ℝ)) := by ring
    have habs_neg :
        |μ - (mean.toVal : ℝ)| = |(mean.toVal : ℝ) - μ| := abs_sub_comm _ _
    calc |((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - μ)|
        = |(((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - mean.toVal)) +
            (μ - (mean.toVal : ℝ))| := by rw [hdiff]
      _ ≤ |((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - mean.toVal)| +
          |μ - (mean.toVal : ℝ)| := abs_add_le _ _
      _ = |((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - mean.toVal)| +
          |(mean.toVal : ℝ) - μ| := by rw [habs_neg]
  linarith

end FP

end LayerNorm
