# Session Prompt — Probabilistic / RG Physics of FP Rounding

**Goal:** continue the *probabilistic / renormalization-group* thread of the Flean reduction stack —
turn worst-case error analysis into the **statistical mechanics of rounding** (rounding as noise),
where `err` is a *fluctuation scale* (variance/temperature), not a hard cutoff. First brick is
shipped; this session pushes the next ones.

## Read first (in order)

1. `.claude/notes/exact-int-design.md` — the "Strategic read" + "Regime map" sections, esp. the
   **renormalization-group dictionary**: MvForm = UV-complete theory, fixed-degree forms = effective
   theories, `truncate` = integrating out modes, the leak = irrelevant operators (suppressed by
   `X^k`), `IsImage` residues = conserved charges, `err`/`η` = cutoff, snapping = gap. This is the
   *why*: the whole stack is **certified abstract interpretation of FP**, and it has RG structure.
2. `.claude/notes/exact-int-reduction.md` — the last few UPDATE entries (continuous tower → MvForm →
   loop-closed → probabilistic brick). The full tactical log.
3. `Flean/Operations/ProbError.lean` — the first probabilistic brick (read it; it's short).

## What's shipped (the √n law)

`Flean/Operations/ProbError.lean` (`namespace Flean.ProbError`, built on
`Mathlib.Probability.Moments.Variance`). The core phenomenon: worst-case rounding error accumulates
**linearly** (`n·η·scale`), but under the probabilistic rounding model (independent **mean-zero**
per-step errors — Higham–Mary; exact for stochastic rounding) the **variances add**, so typical
error grows like **`√n·η·scale`**. Noise cancels.

- `variance_sum_le` — quadrature law: `Var[∑ eᵢ] ≤ ∑ vᵢ` (via `IndepFun.variance_sum`).
- `concentration` — Chebyshev: `μ{ω | k·√n·σ ≤ |∑ eᵢ ω|} ≤ 1/k²`. The `√n` is explicit.

These take the per-step variance bounds / independence / mean-zero as the model's hypotheses (which
is exactly how the literature states it). The errors `eᵢ` are abstract random variables `Ω → ℝ`.

## DONE in session 2 (2026-06-15)

- **Brick #1 (σ↔η bridge) — COMPLETE.** `variance_le_sq_of_abs_le` (bounded mean-zero ⇒ `Var ≤ b²`,
  via Mathlib Popoviciu `variance_le_sq_of_bounded` — cleaner than the `E[X²]` route, and the variance
  bound doesn't even need mean-zero). Refactored `concentration` through a general engine
  `concentration_of_variance_le`. FP statements: `concentration_fp` (uniform scale) + `concentration_fp_vec`
  (per-term, aggregate is the **ℓ² norm** `√(∑scaleᵢ²)`).
- **Brick #3 (Gaussian shadows) — mostly done.** `concentration_fp_subgaussian` (one-sided) +
  `concentration_fp_subgaussian_abs` (two-sided): bounded mean-zero rounding errors are **sub-Gaussian**
  (Hoeffding lemma `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` + Hoeffding sum inequality
  `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`), giving an **exponential** tail `exp(-k²/2)` —
  strictly sharper than Chebyshev's `1/k²`. This is the rigorous "rounding ≈ Gaussian noise". Requires
  independence (`iIndepFun`).
- **Verdict recorded** in `exact-int-design.md` (UPDATE session 2): statistical-mechanics core *proved*
  (fluctuation scale, cancellation, Gaussianity); RG-*flow* half still program.

Remaining: **Brick #2 (Azuma/martingale)** for round-to-nearest's dependence — Mathlib has
`measure_sum_ge_le_of_HasCondSubgaussianMGF` (line ~930 of `SubGaussian.lean`) + the conditional
sub-Gaussian MGF machinery (`HasCondSubgaussianMGF`, needs a filtration). This is the realistic model
(round-to-nearest errors are mean-zero *given the past*, not independent). Bigger lift. Then **Brick #4**
(formalize RG flow). A true CLT-convergence (not just sub-Gaussian upper bound) would complete #3.

## Original next bricks (priority order) — #1 and most of #3 now done above

### 1. The σ↔η bridge (DO THIS FIRST — it makes the √n law about *floating point*)

Right now `σ` is abstract. Tie it to the FP rounding unit: a **bounded mean-zero** error has variance
`≤ bound²`. So if `|eᵢ| ≤ η·scaleᵢ` (the deterministic per-op bound we already prove everywhere) and
`E[eᵢ] = 0` (the model), then `Var[eᵢ] ≤ (η·scaleᵢ)²`. Feed that into `concentration` and you get the
honest FP statement: *typical error `≤ k·η·√(∑ scaleᵢ²)`* vs worst-case `η·∑|scaleᵢ|` — i.e. `√n·η`
vs `n·η` for uniform scale.

- Key lemma to prove: for `X : Ω → ℝ` with `μ[X] = 0` and `|X ω| ≤ b` (a.e.), `variance X μ ≤ b²`.
  Route: `variance X μ = μ[X²] − μ[X]² = μ[X²]` (mean-zero); then `μ[X²] ≤ b²` because `X² ≤ b²`
  pointwise and `μ` is a probability measure (`∫ const = const`). Look for `variance_eq` /
  `ProbabilityTheory.variance_def'` (`Var = E[X²] − E[X]²`), `integral_mono`, `integral_const`.
- Then a corollary of `concentration` with `σ := η·scale` (uniform) or a vector of `scaleᵢ`.
- Connect conceptually (docstring) to the existing forms: this is the *probabilistic* `err`, the
  statistical counterpart of `ScaledInt.err` / `AffineForm.err`.

### 2. Martingale / Azuma for round-to-nearest

Round-to-nearest errors are NOT independent, but they ARE mean-zero **given the past** (martingale
differences) and bounded. Mathlib has Azuma (`MeasureTheory.azuma` / in `Probability`). This gives
the same `√n` with deterministic-looking high-probability bounds *without* the independence
assumption — the more realistic model. Bigger lift (needs a filtration), but the honest version.

### 3. Output-distribution shadows (≈ Gaussian)

A probabilistic analogue of the `*Form` structures: a float tracked against an *ideal* plus a
*distributional* error (mean 0, variance v, maybe sub-Gaussian). The CLT-flavoured statement: a sum
of many small independent rounding errors is approximately Gaussian. Mathlib has Gaussians and CLT
machinery. This is the full "rounding as noise → output is a distribution" capability.

### 4. Formalize the RG flow (the theory spine)

Make the `(α, γ)` Galois connection explicit (α = best abstraction), and the tower-as-RG-flow:
running couplings (truncated-model coefficients flowing with the input scale `X`), and the
universality statement (many microscopic FP computations → same effective shadow = ML's "different
nets, same function"). More foundational than capability-adding; do after 1–3 give it teeth.

## Gotchas (measure-theory API, learned the hard way in `ProbError.lean`)

- `μ[∑ i, e i]` (expectation of a function-sum) does NOT match `integral_finset_sum`'s `∫ ∑ i, e i a`
  form. First `rw [show (∑ i, e i) = fun x => ∑ i, e i x from funext fun x => Finset.sum_apply x _ e]`.
- `rw` under a set-builder binder `{ω | … μ[X] …}` fails ("pattern not found"). Use `measure_mono`
  with a pointwise subset proof instead (intro ω, `simp only [Set.mem_setOf_eq]`, then `rw`).
- `div_le_div_iff` is renamed → **`div_le_div_iff₀`** `(hb : 0<b) (hd : 0<d) : a/b ≤ c/d ↔ a*d ≤ c*b`.
- `positivity` will NOT strict-ify a `Nat` cast: for `0 < (n:ℝ)` provide `have hnr : (0:ℝ) < n := by
  exact_mod_cast hn` and build products with `mul_pos` explicitly. Same for `0 < √n` (`Real.sqrt_pos`).
- `MemLp` of a finite sum: `memLp_finset_sum'`. `MemLp.integrable one_le_two` for integrability.
- Chebyshev: `ProbabilityTheory.meas_ge_le_variance_div_sq (hX : MemLp X 2 μ) (hc : 0<c) :
  μ {ω | c ≤ |X ω − μ[X]|} ≤ ENNReal.ofReal (variance X μ / c^2)` (needs `[IsFiniteMeasure μ]`;
  `IsProbabilityMeasure` gives it).
- `IndepFun.variance_sum (s) (hs : ∀ i∈s, MemLp (X i) 2 μ) (h : Set.Pairwise ↑s …) : variance (∑) =
  ∑ variance`. For `s = univ`, convert independence with `Finset.coe_univ`.

## The meta-question to carry

The deep claim is that **the FP reduction stack literally has RG structure** and the probabilistic
layer is its statistical mechanics. Each brick should either (a) make a real FP error statement
sharper (the `√n` win is the template), or (b) make an RG-dictionary entry into a theorem. By the end
of the thread: is "rounding error analysis = statistical mechanics / RG of FP" a *proved* organizing
principle, or a productive analogy? Record the verdict in `exact-int-design.md` — exactly as the
`AbstractFp` framework question was settled by building `IsImage`.

## Build discipline

`lake build` often. Everything sorry-free, warning-clean. Measure-theory proofs need iteration —
expect to fix lemma names against the installed Mathlib (grep `.lake/packages/mathlib`). The whole
library is at 2962 build jobs, all green.
