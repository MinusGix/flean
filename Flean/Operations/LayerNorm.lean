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

/-! ### Stage 3: square + variance error bounds -/

/-- **Per-component square rounding error**.  Given an `fpMulFinite`
witness `sqDiffs i = fpMulFinite (shifted i) (shifted i)` + normal-range
on the exact square, the FP square differs from the real square by at
most one multiplication rounding step:

```
|sqDiffs_i − (shifted_i)²| ≤ η · (shifted_i)²
```
-/
theorem fpSqDiff_step_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
    [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]
    {shifted sqDiffs : Fin n → FiniteFp}
    (h_sqDiffs : ∀ i,
      fpMulFinite (shifted i) (shifted i) = Fp.finite (sqDiffs i))
    (i : Fin n)
    (h_sq_normal : (2 : ℝ) ^ FloatFormat.min_exp ≤
      |((shifted i).toVal : ℝ) * (shifted i).toVal|) :
    |((sqDiffs i).toVal : ℝ) - ((shifted i).toVal : ℝ) ^ 2| ≤
      (η : ℝ) * ((shifted i).toVal : ℝ) ^ 2 := by
  obtain ⟨g, hg_round, hg_eq⟩ :=
    fpMulFinite_round_witness (R := ℝ) (shifted i) (shifted i) (h_sqDiffs i)
  have h_err :
      |(g.toVal : ℝ) - (shifted i).toVal * (shifted i).toVal| ≤
        (η : ℝ) * |((shifted i).toVal : ℝ) * (shifted i).toVal| :=
    round_preserves_abs_error_normal h_sq_normal hg_round
  have hsq_nn : (0 : ℝ) ≤ (shifted i).toVal * (shifted i).toVal :=
    mul_self_nonneg _
  rw [abs_of_nonneg hsq_nn] at h_err
  have h_sq_eq :
      ((shifted i).toVal : ℝ) ^ 2 = (shifted i).toVal * (shifted i).toVal := by
    ring
  rw [h_sq_eq, ← hg_eq]
  exact h_err

/-- **Variance rounding error**.  Analogous to `fpMean_error_bound`
but for the variance: given a variance-sum witness + `fpDivFinite`
witness producing `var`, bounds `|var.toVal − Σ sqDiffs / n|`. -/
theorem fpVar_step_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ]
    {sqDiffs : Fin n → FiniteFp}
    (hn_pos : 0 < n)
    (varSumBound : FpSum.FpSumBound sqDiffs ℝ)
    {nFp var : FiniteFp}
    (hNFp_toVal : (nFp.toVal : ℝ) = (n : ℝ))
    (hNFp_m_ne : nFp.m ≠ 0)
    (h_var : fpDivFinite varSumBound.result nFp = Fp.finite var)
    (h_quot_ne : (varSumBound.result.toVal : ℝ) / nFp.toVal ≠ 0)
    (h_quot_normal :
      (2 : ℝ) ^ FloatFormat.min_exp ≤
        |(varSumBound.result.toVal : ℝ) / nFp.toVal|) :
    |(var.toVal : ℝ) - (∑ j, ((sqDiffs j).toVal : ℝ)) / (n : ℝ)| ≤
      (η : ℝ) * |(varSumBound.result.toVal : ℝ) / nFp.toVal| +
      varSumBound.relErr * (∑ j, |((sqDiffs j).toVal : ℝ)|) / (n : ℝ) :=
  fpMean_error_bound hn_pos varSumBound hNFp_toVal hNFp_m_ne h_var
    h_quot_ne h_quot_normal

/-! ### Stage 4: eps-add + sqrt error bounds -/

/-- **Eps-add rounding error**.  Given an `fpAddFinite` witness for
`var + eps` + normal-range, bounds `|varPlusEps − (var + eps)|` by one
addition rounding step. -/
theorem fpVarPlusEps_step_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ]
    [RModeNearest ℝ] [RModeConj ℝ] [RModeZero ℝ]
    {var eps varPlusEps : FiniteFp}
    (h_varPlusEps : fpAddFinite var eps = Fp.finite varPlusEps)
    (h_sum_normal :
      (2 : ℝ) ^ FloatFormat.min_exp ≤ |((var.toVal : ℝ)) + eps.toVal|) :
    |((varPlusEps.toVal : ℝ)) - (var.toVal + eps.toVal)| ≤
      (η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| := by
  obtain ⟨g, hg_round, hg_eq⟩ :=
    fpAddFinite_round_witness (R := ℝ) var eps h_varPlusEps
  have h_err :
      |(g.toVal : ℝ) - ((var.toVal : ℝ) + eps.toVal)| ≤
        (η : ℝ) * |((var.toVal : ℝ)) + eps.toVal| :=
    round_preserves_abs_error_normal h_sum_normal hg_round
  rw [← hg_eq]; exact h_err

/-- **Sqrt rounding error**.  Given an `fpSqrtFinite` witness + normal
range on `√(varPlusEps)`, bounds `|stddev − √varPlusEps|` by one sqrt
rounding step.

Derived via `fpSqrtFinite_correct` + `round_preserves_abs_error_normal`. -/
theorem fpStddev_step_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ]
    {varPlusEps stddev : FiniteFp}
    (h_ve_pos : varPlusEps.s = false)
    (h_ve_m_ne : varPlusEps.m ≠ 0)
    (h_stddev : fpSqrtFinite varPlusEps = Fp.finite stddev)
    (h_sqrt_normal :
      (2 : ℝ) ^ FloatFormat.min_exp ≤ |Real.sqrt ((varPlusEps.toVal : ℝ))|) :
    |((stddev.toVal : ℝ)) - Real.sqrt ((varPlusEps.toVal : ℝ))| ≤
      (η : ℝ) * |Real.sqrt ((varPlusEps.toVal : ℝ))| := by
  have h_sqrt_round :
      (RMode.round (R := ℝ) (Real.sqrt ((varPlusEps.toVal : ℝ))) : Fp) =
        Fp.finite stddev := by
    have hcorr := fpSqrtFinite_correct varPlusEps h_ve_pos h_ve_m_ne
    rw [hcorr] at h_stddev
    exact h_stddev
  exact round_preserves_abs_error_normal h_sqrt_normal h_sqrt_round

/-! ### Stage 5: per-component normalize + composition -/

/-- **Per-component normalize rounding error**.  Given an
`fpDivFinite` witness for `shifted_i / stddev`, bounds
`|result_i − shifted_i / stddev|` by one division rounding step. -/
theorem fpNormalize_step_error_bound
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [RModeConj ℝ]
    {shifted : Fin n → FiniteFp} {stddev : FiniteFp}
    {result : Fin n → FiniteFp}
    (h_stddev_m_ne : stddev.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (shifted i) stddev = Fp.finite (result i))
    (i : Fin n)
    (h_quot_ne : ((shifted i).toVal : ℝ) / stddev.toVal ≠ 0)
    (h_quot_normal :
      (2 : ℝ) ^ FloatFormat.min_exp ≤
        |((shifted i).toVal : ℝ) / stddev.toVal|) :
    |((result i).toVal : ℝ) - (shifted i).toVal / stddev.toVal| ≤
      (η : ℝ) * |((shifted i).toVal : ℝ) / stddev.toVal| := by
  have h_div_round :
      (RMode.round (R := ℝ) ((shifted i).toVal / stddev.toVal) : Fp) =
        Fp.finite (result i) := by
    have heq :=
      fpDivFinite_correct (R := ℝ) (shifted i) stddev h_stddev_m_ne h_quot_ne
    simp only [div_eq_fpDiv, fpDiv, h_stddev_m_ne, ↓reduceIte,
               div_finite_eq_fpDivFinite] at heq
    rw [h_result i] at heq
    exact heq.symm
  exact round_preserves_abs_error_normal h_quot_normal h_div_round

/-! ### Stage 5b: end-to-end composition

The per-step bounds above are "local" — each compares an FP value to
its immediate exact input.  The end-to-end theorem composes these
into a forward-error bound comparing the FP output to the exact
`layerNorm xs eps i`.

Three exact-side quantities thread through:
- `μ := (Σ xs)/n`
- `σ² := Σ(x_j − μ)²/n`
- `σ := √(σ² + eps)` (exact stddev)

and the bound takes the form

```
|result_i − (x_i − μ)/σ| ≤
    δ_final + δ_shift/|stddev| + |x_i − μ| · δ_stddev / (|stddev|·|σ|)
```

where `δ_{final, shift, stddev}` are the accumulated per-step errors.
-/

/-- **End-to-end forward error composition**.  Given:

- `μ_exact` — the exact mean,
- `σ_exact > 0` — the exact stddev `√(variance + eps)`,
- per-step error bounds (`δ_shift`, `δ_stddev`, `δ_final`)

produces a per-component bound

```
|result_i − (xs_i − μ_exact)/σ_exact| ≤
    δ_final + δ_shift/stddev + |xs_i − μ_exact| · δ_stddev / (stddev · σ_exact)
```

The RHS's `stddev.toVal` in the denominator is the *FP* stddev (it
must be positive; the `h_stddev_pos` hypothesis captures this).  The
LHS's `σ_exact` is the real-valued exact stddev. -/
theorem fpLayerNorm_composition_bound
    {xs : Fin n → FiniteFp}
    {shifted : Fin n → FiniteFp} {stddev : FiniteFp}
    {result : Fin n → FiniteFp}
    (i : Fin n) {μ_exact σ_exact : ℝ}
    (hσ_exact_pos : 0 < σ_exact)
    (h_stddev_pos : 0 < (stddev.toVal : ℝ))
    {δ_shift δ_stddev δ_final : ℝ}
    (h_shift :
      |((shifted i).toVal : ℝ) - (((xs i).toVal : ℝ) - μ_exact)| ≤ δ_shift)
    (h_stddev : |((stddev.toVal : ℝ)) - σ_exact| ≤ δ_stddev)
    (h_final :
      |((result i).toVal : ℝ) - (shifted i).toVal / stddev.toVal| ≤ δ_final) :
    |((result i).toVal : ℝ) -
        (((xs i).toVal : ℝ) - μ_exact) / σ_exact| ≤
      δ_final + δ_shift / stddev.toVal +
        |((xs i).toVal : ℝ) - μ_exact| * δ_stddev /
          ((stddev.toVal : ℝ) * σ_exact) := by
  set Sh : ℝ := (stddev.toVal : ℝ) with hSh_def
  set σ : ℝ := σ_exact with hσ_def
  set x : ℝ := ((xs i).toVal : ℝ) with hx_def
  set xμ : ℝ := x - μ_exact with hxμ_def
  set s : ℝ := ((shifted i).toVal : ℝ) with hs_def
  set r : ℝ := ((result i).toVal : ℝ) with hr_def
  -- Decompose: r - xμ/σ = (r - s/Sh) + (s/Sh - xμ/Sh) + (xμ/Sh - xμ/σ).
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ_exact_pos
  have hSh_ne : Sh ≠ 0 := ne_of_gt h_stddev_pos
  -- Step 1: |r - s/Sh| ≤ δ_final.  (h_final.)
  -- Step 2: |s/Sh - xμ/Sh| = |s - xμ|/|Sh| ≤ δ_shift / Sh.
  have h2 : |s / Sh - xμ / Sh| ≤ δ_shift / Sh := by
    have : s / Sh - xμ / Sh = (s - xμ) / Sh := by ring
    rw [this, abs_div, abs_of_pos h_stddev_pos]
    exact div_le_div_of_nonneg_right h_shift (le_of_lt h_stddev_pos)
  -- Step 3: |xμ/Sh - xμ/σ| = |xμ| · |σ - Sh| / (Sh·σ) = |xμ| · δ_stddev / (Sh·σ).
  have h3 : |xμ / Sh - xμ / σ| ≤ |xμ| * δ_stddev / (Sh * σ) := by
    have h_ident : xμ / Sh - xμ / σ = xμ * (σ - Sh) / (Sh * σ) := by
      field_simp
    rw [h_ident, abs_div, abs_mul]
    have hpos : 0 < Sh * σ := mul_pos h_stddev_pos hσ_exact_pos
    rw [abs_of_pos hpos]
    have h_abs_stddev_err : |σ - Sh| ≤ δ_stddev := by
      rw [abs_sub_comm]; exact h_stddev
    have habs_xμ_nn : 0 ≤ |xμ| := abs_nonneg _
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_abs_stddev_err habs_xμ_nn)
      (le_of_lt hpos)
  -- Triangle inequality.
  have htri :
      |r - xμ / σ| ≤
        |r - s / Sh| + |s / Sh - xμ / Sh| + |xμ / Sh - xμ / σ| := by
    have hdecomp : r - xμ / σ =
        (r - s / Sh) + (s / Sh - xμ / Sh) + (xμ / Sh - xμ / σ) := by ring
    calc |r - xμ / σ|
        = |(r - s / Sh) + (s / Sh - xμ / Sh) + (xμ / Sh - xμ / σ)| := by
          rw [hdecomp]
      _ ≤ |(r - s / Sh) + (s / Sh - xμ / Sh)| + |xμ / Sh - xμ / σ| :=
          abs_add_le _ _
      _ ≤ |r - s / Sh| + |s / Sh - xμ / Sh| + |xμ / Sh - xμ / σ| := by
          have := abs_add_le (r - s / Sh) (s / Sh - xμ / Sh)
          linarith
  linarith

/-- **End-to-end forward error bound** (relative to `layerNorm`).

`fpLayerNorm_composition_bound` expressed with the RHS tied to the
real-valued `layerNorm xs eps i`.  The exact mean and exact stddev
are unpacked from the `layerNorm` definition:

```
layerNorm xs eps i = (xs_i − mean xs) / √(variance xs + eps)
```

so `μ_exact := mean (toVal ∘ xs)` and
`σ_exact := √(variance (toVal ∘ xs) + eps)`. -/
theorem fpLayerNorm_end_to_end_error_bound
    {xs : Fin n → FiniteFp}
    {shifted : Fin n → FiniteFp} {stddev : FiniteFp}
    {result : Fin n → FiniteFp}
    (i : Fin n) {eps : ℝ} (heps_pos : 0 < eps)
    (hn_pos_r : 0 < (n : ℝ))
    (h_stddev_pos : 0 < (stddev.toVal : ℝ))
    {δ_shift δ_stddev δ_final : ℝ}
    (h_shift :
      |((shifted i).toVal : ℝ) -
          (((xs i).toVal : ℝ) - mean (fun j => ((xs j).toVal : ℝ)))| ≤ δ_shift)
    (h_stddev :
      |((stddev.toVal : ℝ)) -
          Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) + eps)| ≤ δ_stddev)
    (h_final :
      |((result i).toVal : ℝ) - (shifted i).toVal / stddev.toVal| ≤ δ_final) :
    |((result i).toVal : ℝ) -
        layerNorm (fun j => ((xs j).toVal : ℝ)) eps i| ≤
      δ_final + δ_shift / stddev.toVal +
        |((xs i).toVal : ℝ) -
            mean (fun j => ((xs j).toVal : ℝ))| * δ_stddev /
          ((stddev.toVal : ℝ) *
            Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) + eps)) := by
  have hn_pos_r_nn : 0 ≤ (n : ℝ) := le_of_lt hn_pos_r
  have hσ_pos :
      0 < Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) + eps) :=
    sqrt_var_plus_eps_pos _ eps heps_pos hn_pos_r_nn
  unfold layerNorm
  exact fpLayerNorm_composition_bound i hσ_pos h_stddev_pos
    h_shift h_stddev h_final

end FP

end LayerNorm
