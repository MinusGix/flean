import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian

/-! # The statistical mechanics of rounding — probabilistic error, the √n law

Every error bound in this library so far is **worst-case**: `|fp.toVal − ideal| ≤ err`, with `err`
accumulating *linearly* (`n · η · scale` for an `n`-term sum). That is the right bound but the wrong
*typical* behaviour. Under the **probabilistic rounding model** (Higham–Mary; exact for stochastic
rounding, a good model for round-to-nearest), each elementary rounding error is a **mean-zero random
variable** bounded by `η · scale`. Independent mean-zero errors do not add in absolute value — their
**variances add** — so the typical total error grows like **`√n · η · scale`, not `n · η · scale`**.
That `√n`-vs-`n` gap is the statistical-mechanics version of error accumulation: rounding is noise,
and noise cancels.

This file is the first brick of that program — the **quadrature law** and its concentration
corollary, built on Mathlib's `variance` / independence / Chebyshev:

* `variance_sum_le` — independent per-step errors' variances add: `Var[∑ eᵢ] ≤ ∑ vᵢ`.
* `concentration` — Chebyshev turns the variance into a high-probability bound: the total error
  exceeds `k · √n · σ` with probability at most `1/k²`. The `√n` is explicit.
* `variance_le_sq_of_abs_le` — the **σ↔η bridge**: a mean-zero error bounded by `η · scale` has
  variance `≤ (η · scale)²`, so the abstract `σ` *is* the FP rounding unit.
* `concentration_fp` / `concentration_fp_vec` — the √n law spelled out for floating point: typical
  error `≤ k · η · √n · scale` (uniform) or `≤ k · η · √(∑ scaleᵢ²)` (per-term), versus the
  deterministic worst case `η · n · scale` / `η · ∑ scaleᵢ`. The aggregate that matters is the **ℓ²
  norm** of the scales, not their ℓ¹ sum.

In the renormalization picture this is where `err` stops being a hard cutoff and becomes a
*fluctuation scale* (a temperature/variance): the macroscopic shadow is the mean, the rounding is
the microscopic noise around it, and concentration is the law of large numbers for the reduction.
The σ↔η bridge is the statistical counterpart of `ScaledInt.err` / `AffineForm.err`: those track the
worst-case `err`, this tracks its variance.
-/

namespace Flean.ProbError

open ProbabilityTheory MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The σ↔η bridge.** A rounding error that is bounded in magnitude by `b` (almost everywhere)
has variance at most `b²`. This is the statistical counterpart of the deterministic per-op bound
`|eᵢ| ≤ η · scaleᵢ` proved everywhere in the library: it turns that hard cutoff into a *fluctuation
scale* `σ = η · scaleᵢ` feeding the √n law below. (No mean-zero hypothesis is needed for the variance
bound itself — this is Popoviciu's inequality with `a = -b`, `b = b`; mean-zero is what later centres
the concentration statement on the ideal value.) -/
theorem variance_le_sq_of_abs_le [IsProbabilityMeasure μ] {b : ℝ} {X : Ω → ℝ}
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) (hX : AEMeasurable X μ) :
    variance X μ ≤ b ^ 2 := by
  have h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-b) b := by
    filter_upwards [hb] with ω hω using abs_le.mp hω
  refine (variance_le_sq_of_bounded h hX).trans_eq ?_
  ring

/-- **The quadrature law.** For pairwise-independent (square-integrable) rounding errors, the
variance of the accumulated error is the *sum* of the per-step variances — they add in quadrature,
not in absolute value. With each `Var[eᵢ] ≤ σ²` this gives `Var[∑ eᵢ] ≤ n · σ²`, hence a typical
error `~ √n · σ` rather than the worst-case `~ n · (bound)`. -/
theorem variance_sum_le {n : ℕ} (e : Fin n → Ω → ℝ) (v : Fin n → ℝ)
    (hmem : ∀ i, MemLp (e i) 2 μ)
    (hindep : Set.Pairwise Set.univ fun i j => IndepFun (e i) (e j) μ)
    (hvar : ∀ i, variance (e i) μ ≤ v i) :
    variance (∑ i, e i) μ ≤ ∑ i, v i := by
  rw [IndepFun.variance_sum (s := Finset.univ) (fun i _ => hmem i)
    (by rwa [Finset.coe_univ])]
  exact Finset.sum_le_sum (fun i _ => hvar i)

/-- **Concentration engine.** Given *any* variance bound `Var[∑ eᵢ] ≤ V` for a mean-zero total
error, Chebyshev caps the probability that the accumulated error exceeds `k · √V`: it is at most
`1/k²`. Everything below is this lemma with a particular `V` substituted (`V = n σ²` for the √n law,
`V = η² ∑ scaleᵢ²` for the floating-point versions). -/
theorem concentration_of_variance_le [IsProbabilityMeasure μ] {n : ℕ}
    (e : Fin n → Ω → ℝ) (V : ℝ) (hV : 0 < V)
    (hmem : ∀ i, MemLp (e i) 2 μ)
    (hmean : ∀ i, μ[e i] = 0)
    (hsum : variance (∑ i, e i) μ ≤ V)
    {k : ℝ} (hk : 0 < k) :
    μ {ω | k * Real.sqrt V ≤ |(∑ i, e i) ω|} ≤ ENNReal.ofReal (1 / k ^ 2) := by
  have hSmem : MemLp (∑ i, e i) 2 μ := memLp_finset_sum' _ (fun i _ => hmem i)
  have hSmean : μ[∑ i, e i] = 0 := by
    rw [show (∑ i, e i) = (fun x => ∑ i, e i x) from funext fun x => Finset.sum_apply x _ e,
      integral_finset_sum _ (fun i _ => (hmem i).integrable one_le_two)]
    simp [hmean]
  have hsqrtV : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hc : 0 < k * Real.sqrt V := mul_pos hk hsqrtV
  have hsub : {ω | k * Real.sqrt V ≤ |(∑ i, e i) ω|}
      ⊆ {ω | k * Real.sqrt V ≤ |(∑ i, e i) ω - μ[∑ i, e i]|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rwa [hSmean, sub_zero]
  refine (measure_mono hsub).trans
    ((meas_ge_le_variance_div_sq hSmem hc).trans (ENNReal.ofReal_le_ofReal ?_))
  have hc2 : (k * Real.sqrt V) ^ 2 = k ^ 2 * V := by
    rw [mul_pow, Real.sq_sqrt hV.le]
  have hkV : (0 : ℝ) < k ^ 2 * V := mul_pos (pow_pos hk 2) hV
  rw [hc2, div_le_div_iff₀ hkV (pow_pos hk 2)]
  nlinarith [hsum, sq_nonneg k]

/-- **Concentration — the `√n` law.** Under the probabilistic rounding model (independent,
square-integrable, **mean-zero** per-step errors, each `Var[eᵢ] ≤ σ²`), the total error exceeds
`k · √n · σ` with probability at most `1/k²`. So the typical error is `Θ(√n · σ)`, a `√n` factor
*smaller* than the deterministic worst case `Θ(n · σ)` — rounding noise cancels. Proof: the
quadrature law caps `Var[∑ eᵢ] ≤ n σ²`, and the concentration engine does the rest. -/
theorem concentration [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (e : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hmem : ∀ i, MemLp (e i) 2 μ)
    (hindep : Set.Pairwise Set.univ fun i j => IndepFun (e i) (e j) μ)
    (hmean : ∀ i, μ[e i] = 0)
    (hvar : ∀ i, variance (e i) μ ≤ σ ^ 2)
    {k : ℝ} (hk : 0 < k) :
    μ {ω | k * Real.sqrt n * σ ≤ |(∑ i, e i) ω|} ≤ ENNReal.ofReal (1 / k ^ 2) := by
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hSvar : variance (∑ i, e i) μ ≤ (n : ℝ) * σ ^ 2 := by
    refine (variance_sum_le e (fun _ => σ ^ 2) hmem hindep hvar).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hV : (0 : ℝ) < (n : ℝ) * σ ^ 2 := mul_pos hnr (pow_pos hσ 2)
  have key := concentration_of_variance_le e _ hV hmem hmean hSvar hk
  rwa [show Real.sqrt ((n : ℝ) * σ ^ 2) = Real.sqrt n * σ by
    rw [Real.sqrt_mul hnr.le, Real.sqrt_sq hσ.le], ← mul_assoc] at key

/-- **The `√n` law for floating point (uniform scale).** The honest FP statement: if each elementary
rounding error is mean-zero and bounded by the deterministic per-op bound `|eᵢ| ≤ η · scale` (the
quantity proved everywhere in this library), then the accumulated error exceeds `k · η · √n · scale`
with probability at most `1/k²`. Compare the deterministic worst case `η · n · scale`: the
probabilistic typical error is a factor `√n` smaller. This is `concentration` with the σ↔η bridge
supplying `σ = η · scale`. -/
theorem concentration_fp [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (e : Fin n → Ω → ℝ) (η scale : ℝ) (hη : 0 < η) (hscale : 0 < scale)
    (hmem : ∀ i, MemLp (e i) 2 μ)
    (hindep : Set.Pairwise Set.univ fun i j => IndepFun (e i) (e j) μ)
    (hmean : ∀ i, μ[e i] = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |e i ω| ≤ η * scale)
    {k : ℝ} (hk : 0 < k) :
    μ {ω | k * Real.sqrt n * (η * scale) ≤ |(∑ i, e i) ω|} ≤ ENNReal.ofReal (1 / k ^ 2) :=
  concentration hn e (η * scale) (mul_pos hη hscale) hmem hindep hmean
    (fun i => variance_le_sq_of_abs_le (hbound i) (hmem i).aemeasurable) hk

/-- **The `√n` law for floating point (per-term scale).** The non-uniform version: each error is
mean-zero with its own deterministic bound `|eᵢ| ≤ η · scaleᵢ`. The accumulated error exceeds
`k · η · √(∑ scaleᵢ²)` with probability at most `1/k²` — the variances add in quadrature, so the
relevant aggregate is the **ℓ² norm** of the scales, not their ℓ¹ sum `∑ scaleᵢ` (the worst-case
bound). For uniform `scaleᵢ = scale` this recovers `√(n) · scale` of `concentration_fp`. -/
theorem concentration_fp_vec [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (e : Fin n → Ω → ℝ) (η : ℝ) (scale : Fin n → ℝ)
    (hη : 0 < η) (hscale : ∀ i, 0 < scale i)
    (hmem : ∀ i, MemLp (e i) 2 μ)
    (hindep : Set.Pairwise Set.univ fun i j => IndepFun (e i) (e j) μ)
    (hmean : ∀ i, μ[e i] = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |e i ω| ≤ η * scale i)
    {k : ℝ} (hk : 0 < k) :
    μ {ω | k * (η * Real.sqrt (∑ i, scale i ^ 2)) ≤ |(∑ i, e i) ω|}
      ≤ ENNReal.ofReal (1 / k ^ 2) := by
  have hSvar : variance (∑ i, e i) μ ≤ η ^ 2 * ∑ i, scale i ^ 2 := by
    refine (variance_sum_le e (fun i => (η * scale i) ^ 2) hmem hindep
      (fun i => variance_le_sq_of_abs_le (hbound i) (hmem i).aemeasurable)).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => le_of_eq (mul_pow η (scale i) 2))
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    Finset.univ_nonempty
  have hSpos : (0 : ℝ) < ∑ i, scale i ^ 2 :=
    Finset.sum_pos (fun i _ => pow_pos (hscale i) 2) hne
  have hV : (0 : ℝ) < η ^ 2 * ∑ i, scale i ^ 2 := mul_pos (pow_pos hη 2) hSpos
  have key := concentration_of_variance_le e _ hV hmem hmean hSvar hk
  rwa [show Real.sqrt (η ^ 2 * ∑ i, scale i ^ 2) = η * Real.sqrt (∑ i, scale i ^ 2) by
    rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le]] at key

/-- **The exponential √n law (sub-Gaussian sharpening).** Chebyshev (`concentration_fp`) gives only a
*polynomial* tail `1/k²`. But a bounded mean-zero error is not merely square-integrable — by
Hoeffding's lemma it is **sub-Gaussian**, and independent sub-Gaussians sum to a sub-Gaussian. So the
accumulated FP rounding error has a *Gaussian* tail: it exceeds `k · η · √n · scale` with probability
at most `exp(-k²/2)`. This is the rigorous form of "rounding error is approximately Gaussian noise" —
the same `√n` aggregation as before, but now with exponential concentration. (One-sided; the
two-sided `|·|` bound is `concentration_fp_subgaussian_abs`, at most `2·exp(-k²/2)`.) -/
theorem concentration_fp_subgaussian [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (e : Fin n → Ω → ℝ) (η scale : ℝ) (hη : 0 < η) (hscale : 0 < scale)
    (hmeas : ∀ i, AEMeasurable (e i) μ)
    (hindep : iIndepFun e μ)
    (hmean : ∀ i, μ[e i] = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |e i ω| ≤ η * scale)
    {k : ℝ} (hk : 0 ≤ k) :
    μ.real {ω | k * Real.sqrt n * (η * scale) ≤ ∑ i, e i ω} ≤ Real.exp (-k ^ 2 / 2) := by
  set b : ℝ := η * scale with hb_def
  have hbpos : 0 < b := mul_pos hη hscale
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hIcc : ∀ i, ∀ᵐ ω ∂μ, e i ω ∈ Set.Icc (-b) b := fun i => by
    filter_upwards [hbound i] with ω hω using abs_le.mp hω
  have hsubG : ∀ i, HasSubgaussianMGF (e i) ((‖b - -b‖₊ / 2) ^ 2) μ := fun i =>
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i) (hIcc i) (hmean i)
  have hc0 : (((‖b - -b‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = b ^ 2 := by
    push_cast [Real.norm_eq_abs]
    rw [show b - -b = 2 * b by ring, abs_of_pos (by positivity : (0 : ℝ) < 2 * b)]
    ring
  have hε : (0 : ℝ) ≤ k * Real.sqrt n * b :=
    mul_nonneg (mul_nonneg hk (Real.sqrt_nonneg _)) hbpos.le
  have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ)
    hindep (fun i _ => hsubG i) hε
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [NNReal.coe_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc0,
    mul_pow, mul_pow, Real.sq_sqrt hnr.le]
  have hden : (0 : ℝ) < n * b ^ 2 := mul_pos hnr (pow_pos hbpos 2)
  field_simp

/-- **Two-sided exponential √n law.** The `|·|` form of `concentration_fp_subgaussian`: by a union
bound over the two tails, the *magnitude* of the accumulated FP rounding error exceeds
`k · η · √n · scale` with probability at most `2·exp(-k²/2)` — a genuine Gaussian two-sided tail.
This is the sharp probabilistic counterpart of the worst-case `|fp.toVal − ideal| ≤ η · n · scale`. -/
theorem concentration_fp_subgaussian_abs [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (e : Fin n → Ω → ℝ) (η scale : ℝ) (hη : 0 < η) (hscale : 0 < scale)
    (hmeas : ∀ i, AEMeasurable (e i) μ)
    (hindep : iIndepFun e μ)
    (hmean : ∀ i, μ[e i] = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |e i ω| ≤ η * scale)
    {k : ℝ} (hk : 0 ≤ k) :
    μ.real {ω | k * Real.sqrt n * (η * scale) ≤ |∑ i, e i ω|} ≤ 2 * Real.exp (-k ^ 2 / 2) := by
  have hpos := concentration_fp_subgaussian hn e η scale hη hscale hmeas hindep hmean hbound hk
  have hindep' : iIndepFun (fun i => -(e i)) μ :=
    hindep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hneg := concentration_fp_subgaussian hn (fun i => -(e i)) η scale hη hscale
    (fun i => (hmeas i).neg) hindep'
    (fun i => by simp only [Pi.neg_apply, integral_neg, hmean i, neg_zero])
    (fun i => by filter_upwards [hbound i] with ω hω; simpa using hω) hk
  have hsub : {ω | k * Real.sqrt n * (η * scale) ≤ |∑ i, e i ω|} ⊆
      {ω | k * Real.sqrt n * (η * scale) ≤ ∑ i, e i ω} ∪
        {ω | k * Real.sqrt n * (η * scale) ≤ ∑ i, (-(e i)) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [Pi.neg_apply, Finset.sum_neg_distrib]
      exact h
  calc μ.real {ω | k * Real.sqrt n * (η * scale) ≤ |∑ i, e i ω|}
      ≤ μ.real ({ω | k * Real.sqrt n * (η * scale) ≤ ∑ i, e i ω} ∪
          {ω | k * Real.sqrt n * (η * scale) ≤ ∑ i, (-(e i)) ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | k * Real.sqrt n * (η * scale) ≤ ∑ i, e i ω} +
          μ.real {ω | k * Real.sqrt n * (η * scale) ≤ ∑ i, (-(e i)) ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-k ^ 2 / 2) + Real.exp (-k ^ 2 / 2) := add_le_add hpos hneg
    _ = 2 * Real.exp (-k ^ 2 / 2) := by ring

end Flean.ProbError
