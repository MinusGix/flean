import Flean.Operations.Softmax
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-Sum-Exp: Verified End-to-End Error Bound

`logsumexp(xs) = log(Σ exp(xs_i))`, computed numerically via the subtract-max
identity `logsumexp(xs) = max(xs) + log(Σ exp(xs_i - max(xs)))`. The shift-by-max
trick bounds each shifted input in `(-∞, 0]`, so every `exp` is in `(0, 1]` (no
overflow). The post-shift sum `S' ≥ 1` (the `max` term contributes `exp(0) = 1`),
so `log(S')` is well-defined and non-negative.

## Main results

* `logsumexp`, `logsumexp_shift_eq`, `logsumexp_ge` — real-valued setup
* `log_rel_error_bound` — `|log y - log x| ≤ ε/(1-ε)` when `|y-x| ≤ ε·x`
* `fpLogSumExp_end_to_end_error_bound` — the main theorem, with an abstract log
  witness (since no `fpLogFinite` / `LogApprox` typeclass exists yet)
* `fpLogSumExp_naiveSum_error_bound` — NaiveSum demo

## Abstract log witness

No `fpLogFinite` / `LogApprox` typeclass is available. The log step enters as a
hypothesis `h_log_close : |logResult.toVal - log(sum.result.toVal)| ≤
η_log · |log(sum.result.toVal)|`, mirroring how `fpSoftmax` takes `h_exp` for
the exp step. When a concrete `fpLogFinite` lands, a thin wrapper should
produce the required witness.
-/

set_option autoImplicit false

namespace LogSumExp

open Finset BigOperators Softmax

variable {n : ℕ}

/-! ## Real-Valued Setup -/

/-- The log-sum-exp function: `log(Σ_j exp(xs j))`. -/
noncomputable def logsumexp (xs : Fin n → ℝ) : ℝ :=
  Real.log (∑ j : Fin n, Real.exp (xs j))

@[simp] theorem logsumexp_eq_log_softmaxDenom (xs : Fin n → ℝ) :
    logsumexp xs = Real.log (softmaxDenom xs) := rfl

/-- `logsumexp` is translation-equivariant: shifting inputs by `c` subtracts `c`
from the output. -/
theorem logsumexp_shift_eq (xs : Fin n → ℝ) (c : ℝ) (hn : 0 < n) :
    logsumexp (shift xs c) = logsumexp xs - c := by
  show Real.log (softmaxDenom (shift xs c)) = Real.log (softmaxDenom xs) - c
  rw [softmaxDenom_shift,
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (softmaxDenom_pos xs hn)),
      Real.log_exp]
  ring

/-- `logsumexp(xs) ≥ xs i` for every `i`. (Equivalently: `logsumexp ≥ max xs`
when the max is attained at some index.) -/
theorem logsumexp_ge (xs : Fin n → ℝ) (i : Fin n) : xs i ≤ logsumexp xs := by
  unfold logsumexp
  have h1 : Real.exp (xs i) ≤ ∑ j, Real.exp (xs j) :=
    Finset.single_le_sum (f := fun j => Real.exp (xs j))
      (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i)
  have h2 : Real.log (Real.exp (xs i)) ≤ Real.log (∑ j, Real.exp (xs j)) :=
    Real.log_le_log (Real.exp_pos _) h1
  rwa [Real.log_exp] at h2

/-! ## Lipschitz / Monotonicity of `logsumexp`

Standard facts used by the MLP-on-CE composition.  `logsumexp` is
monotone in each input coordinate and 1-Lipschitz in the L∞ norm:
perturbing every input by at most `δ` perturbs `logsumexp` by at most
`δ`.  Proof: monotonicity + translation-equivariance (`logsumexp_shift_eq`). -/

/-- `logsumexp` is monotone: if every `xs i ≤ ys i`, then
`logsumexp xs ≤ logsumexp ys`. -/
theorem logsumexp_monotone (hn : 0 < n) {xs ys : Fin n → ℝ}
    (h : ∀ i, xs i ≤ ys i) :
    logsumexp xs ≤ logsumexp ys := by
  unfold logsumexp
  apply Real.log_le_log (softmaxDenom_pos xs hn)
  apply Finset.sum_le_sum
  intro i _
  exact Real.exp_le_exp.mpr (h i)

/-- `logsumexp` is 1-Lipschitz in the L∞ norm: if every input
differs by at most `δ`, the outputs differ by at most `δ`. -/
theorem logsumexp_lipschitz (hn : 0 < n) (xs ys : Fin n → ℝ) {δ : ℝ}
    (h_dx : ∀ j, |xs j - ys j| ≤ δ) :
    |logsumexp xs - logsumexp ys| ≤ δ := by
  have hδ_nn : 0 ≤ δ := le_trans (abs_nonneg _) (h_dx ⟨0, hn⟩)
  -- Pointwise two-sided bounds: xs i ≤ ys i + δ and ys i ≤ xs i + δ.
  have h_upper : ∀ i, xs i ≤ ys i + δ := fun i => by
    have h := (abs_le.mp (h_dx i)).2
    linarith
  have h_lower : ∀ i, ys i ≤ xs i + δ := fun i => by
    have h := (abs_le.mp (h_dx i)).1
    linarith
  -- Rewrite `fun i => ys i + δ` as `shift ys (-δ)` and use translation.
  have h_plus_eq : (fun i => ys i + δ) = shift ys (-δ) := by
    funext i; simp [shift]
  have h_plus_eq' : (fun i => xs i + δ) = shift xs (-δ) := by
    funext i; simp [shift]
  have h_LSE_up : logsumexp xs ≤ logsumexp ys + δ := by
    have h := logsumexp_monotone (ys := fun i => ys i + δ) hn h_upper
    rw [h_plus_eq] at h
    rw [logsumexp_shift_eq ys (-δ) hn] at h
    linarith
  have h_LSE_lo : logsumexp ys ≤ logsumexp xs + δ := by
    have h := logsumexp_monotone (ys := fun i => xs i + δ) hn h_lower
    rw [h_plus_eq'] at h
    rw [logsumexp_shift_eq xs (-δ) hn] at h
    linarith
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-! ## Log Relative-Error Bound

Standalone helper used in the main error analysis: a relative perturbation of
the argument to `log` gives a multiplicative `ε/(1-ε)` absolute change in the
output. -/

/-- If `|y - x| ≤ ε·x` with `x > 0` and `0 ≤ ε < 1`, then `|log y - log x| ≤ ε/(1-ε)`.

This is the standard "log is Lipschitz-ish" bound used whenever a multiplicative
error propagates through `log`. The bound `ε/(1-ε)` is tight when `y = (1-ε)x`
(giving `-log(1-ε)`). -/
theorem log_rel_error_bound (x y eps : ℝ) (hx : 0 < x) (hε_nn : 0 ≤ eps)
    (hε_lt : eps < 1) (h : |y - x| ≤ eps * x) :
    |Real.log y - Real.log x| ≤ eps / (1 - eps) := by
  have h1ε : 0 < 1 - eps := by linarith
  have h_abs := abs_le.mp h
  have hy_ge : (1 - eps) * x ≤ y := by nlinarith [h_abs.1]
  have hy_le : y ≤ (1 + eps) * x := by nlinarith [h_abs.2]
  have hy_pos : 0 < y := lt_of_lt_of_le (mul_pos h1ε hx) hy_ge
  -- Upper bound: log y ≤ log((1+eps)x), so log y - log x ≤ log(1+eps) ≤ eps ≤ eps/(1-eps).
  have hup : Real.log y - Real.log x ≤ eps / (1 - eps) := by
    have h1 : Real.log y ≤ Real.log ((1 + eps) * x) := Real.log_le_log hy_pos hy_le
    rw [Real.log_mul (by linarith : (1 + eps : ℝ) ≠ 0) (ne_of_gt hx)] at h1
    have h2 : Real.log (1 + eps) ≤ eps := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + eps); linarith
    have hε_self : eps ≤ eps / (1 - eps) := by
      rw [le_div_iff₀ h1ε]; nlinarith
    linarith
  -- Lower bound: log(x/y) ≤ x/y - 1 ≤ 1/(1-eps) - 1 = eps/(1-eps).
  have hdn : Real.log x - Real.log y ≤ eps / (1 - eps) := by
    have hxy_pos : 0 < x / y := div_pos hx hy_pos
    have h1 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos hxy_pos
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy_pos)] at h1
    have h3 : x / y ≤ 1 / (1 - eps) := by
      rw [div_le_div_iff₀ hy_pos h1ε]
      have : x * (1 - eps) ≤ y := le_trans (by linarith : x * (1 - eps) ≤ (1 - eps) * x) hy_ge
      linarith
    have h4 : (1 : ℝ) / (1 - eps) - 1 = eps / (1 - eps) := by
      field_simp; ring
    linarith
  rw [abs_le]
  exact ⟨by linarith, hup⟩

/-! ## End-to-End FP Log-Sum-Exp Error Bound

The full pipeline `xs → xs' (= xs - c) → exps → sum → logResult → result` is:

1. `c := fpMax xs hn`                         (existing, uses FP order)
2. `xs' i := fpSubFinite (xs i) c`            (abstracted via `h_shift_exact`)
3. `exps i := fpExpFinite (xs' i)`            (abstracted via `h_exp`)
4. `sum.result := Σ_FP exps`                  (any `FpSumBound` witness)
5. `logResult := fpLog sum.result`            (abstracted via `h_log_close`)
6. `result := fpAdd c logResult`              (uses `fpAddFinite`)

Steps 2 and 5 are currently abstracted away — step 2 because tracking the
subtract rounding through `log` makes the bound much messier (users in the
Sterbenz regime get exactness for free), and step 5 because no `LogApprox`
typeclass exists yet. -/

section EndToEnd

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

/-- **End-to-end log-sum-exp error bound**.

Given raw inputs `xs`, an exact-shift witness `xs'`, FP exp/sum results, an
abstract log-rounding witness `(logResult, η_log, logSubConst, h_log_close)`,
and a final `fpAdd` witness with a nonzero side condition (handling both
signs via `RModeConj`), this produces a bound on
`|result.toVal - logsumexp((xs _).toVal)|`.

Let
  `ε_sum := (η + sum.relErr·(1+η)) + (1 + sum.relErr)·n·subnormalConst`

(the effective rel-error on the FP sum vs `S' = Σ exp((xs' _).toVal)` after
folding the subnormal tail in — valid because `S' ≥ 1` from the shifted argmax
term contributing `exp(0) = 1`). Let

  `D_log := ε_sum / (1 - ε_sum)`

(induced `log` error via `log_rel_error_bound`). Then

  `|result.toVal - logsumexp(xs.toVal)|
      ≤ η · |logsumexp(xs.toVal)|
        + (1+η) · (η_log · (logsumexp(xs.toVal) - (fpMax xs hn).toVal)
                   + (1 + η_log) · D_log + logSubConst)
        + Softmax.subnormalConst`

The `η_log · (LSE - c)` term is multiplicative log-rounding; `(1+η_log) · D_log`
is sum error through `log`; `logSubConst` is the log's own additive (subnormal)
tail; `subnormalConst` is the final `fpAdd` tail. Passing `logSubConst = 0`
recovers the purely-multiplicative log regime. -/
theorem fpLogSumExp_end_to_end_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp) (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (h_margin :
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (_h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst)
    (result : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0) :
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    |((result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) - ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst := by
  -- Setup abbreviations. `ε_sum` and `D_log` exactly match the statement's letI shape.
  set c : ℝ := ((fpMax xs hn).toVal : ℝ) with hc_def
  set L : ℝ := (logResult.toVal : ℝ) with hL_def
  set D : ℝ := ((sum.result.toVal : ℝ)) with hD_def
  set S : ℝ := ∑ j, Real.exp ((xs j).toVal : ℝ) with hS_def
  set S' : ℝ := ∑ j, Real.exp ((xs' j).toVal : ℝ) with hS'_def
  set LSE : ℝ := logsumexp (fun j => ((xs j).toVal : ℝ)) with hLSE_def
  set ε_sum : ℝ :=
    ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
      (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst with hε_def
  set D_log : ℝ := ε_sum / (1 - ε_sum) with hDlog_def
  -- Basic sign/pos facts.
  have hη_nn : (0 : ℝ) ≤ (η : ℝ) := by positivity
  have hrel_nn : (0 : ℝ) ≤ sum.relErr := sum.h_relErr_nn
  have hsc_nn : 0 ≤ Softmax.subnormalConst := Softmax.subnormalConst_nn
  have hε_nn : 0 ≤ ε_sum := by
    simp only [hε_def]
    have h1 : 0 ≤ (η : ℝ) + sum.relErr * (1 + (η : ℝ)) := by positivity
    have h2 : 0 ≤ (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst :=
      mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hsc_nn
    linarith
  have hε_lt : ε_sum < 1 := by simp only [hε_def]; exact h_margin
  have h1ε_pos : 0 < 1 - ε_sum := by linarith
  have hDlog_nn : 0 ≤ D_log := div_nonneg hε_nn (le_of_lt h1ε_pos)
  have hη_log_one_nn : 0 ≤ 1 + η_log := by linarith
  have hη_one_nn : 0 ≤ 1 + (η : ℝ) := by linarith
  -- S' ≥ 1: argmax term contributes exp(0) = 1.
  have h_S'_ge_one : (1 : ℝ) ≤ S' := by
    obtain ⟨i₀, hi₀⟩ :
        ∃ i₀ : Fin n, fpMax xs hn = xs i₀ := by
      have h_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
        Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
      obtain ⟨i₀, _, h_max⟩ := Finset.exists_max_image Finset.univ xs h_ne
      refine ⟨i₀, le_antisymm ?_ ?_⟩
      · exact Finset.sup'_le h_ne xs (fun j _ => h_max j (Finset.mem_univ j))
      · exact Finset.le_sup' xs (Finset.mem_univ i₀)
    have h_zero : ((xs' i₀).toVal : ℝ) = 0 := by
      have hc_eq : c = ((xs i₀).toVal : ℝ) := by simp only [hc_def, hi₀]
      linarith [h_shift_exact i₀, hc_eq]
    have h_exp_zero : Real.exp ((xs' i₀).toVal : ℝ) = 1 := by
      rw [h_zero]; exact Real.exp_zero
    simp only [hS'_def]
    calc (1 : ℝ) = Real.exp ((xs' i₀).toVal : ℝ) := h_exp_zero.symm
      _ ≤ ∑ j, Real.exp ((xs' j).toVal : ℝ) :=
        Finset.single_le_sum
          (f := fun j => Real.exp ((xs' j).toVal : ℝ))
          (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i₀)
  have h_S'_pos : 0 < S' := lt_of_lt_of_le zero_lt_one h_S'_ge_one
  -- S' = exp(-c) · S, so log S' = log S - c, i.e., LSE = c + log S'.
  have h_S'_shift : S' = Real.exp (-c) * S := by
    have h_fun : (fun j => (xs' j).toVal) = shift (fun j => ((xs j).toVal : ℝ)) c := by
      funext j; exact h_shift_exact j
    simp only [hS'_def, hS_def, hc_def]
    change ∑ j, Real.exp ((fun j => ((xs' j).toVal : ℝ)) j) = _
    rw [h_fun]
    change softmaxDenom (shift (fun j => ((xs j).toVal : ℝ)) c) = _
    rw [softmaxDenom_shift]
    rfl
  have hS_pos : 0 < S := by
    simp only [hS_def]
    exact Finset.sum_pos (fun j _ => Real.exp_pos _)
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
  have h_log_S' : Real.log S' = LSE - c := by
    rw [h_S'_shift, Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hS_pos), Real.log_exp]
    simp only [hLSE_def, logsumexp_eq_log_softmaxDenom, softmaxDenom, hS_def]
    ring
  have h_log_S'_nn : 0 ≤ Real.log S' := Real.log_nonneg h_S'_ge_one
  -- Sum-vs-S' error: folding subnormal tail via S' ≥ 1 gives `|D - S'| ≤ ε_sum · S'`.
  have h_denom_close_bound :
      |(sum.result.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
        sum.relErr * ∑ j, |((exps j).toVal : ℝ)| := sum.h_bound
  have h_D_close : |D - S'| ≤ ε_sum * S' := by
    have h_denom_unified :
        |D - S'| ≤ ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) * S' +
            (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst := by
      simp only [hD_def, hS'_def]
      exact Softmax.denom_unified_error xs' exps sum.result sum.relErr h_exp
        h_denom_close_bound hrel_nn
    have hB_nn : 0 ≤ (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst :=
      mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hsc_nn
    calc |D - S'|
        ≤ ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) * S' +
            (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst := h_denom_unified
      _ ≤ ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) * S' +
            (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst * S' := by
          have := mul_le_mul_of_nonneg_left h_S'_ge_one hB_nn
          linarith
      _ = ε_sum * S' := by simp only [hε_def]; ring
  -- D > 0 via S' - ε·S' bound.
  have h_D_pos : 0 < D := by
    have := abs_le.mp h_D_close
    have h1 : (1 - ε_sum) * S' ≤ D := by linarith [this.1]
    exact lt_of_lt_of_le (mul_pos h1ε_pos h_S'_pos) h1
  -- |log D - log S'| ≤ D_log.
  have h_log_close_D :
      |Real.log D - Real.log S'| ≤ D_log := by
    simp only [hDlog_def]
    exact log_rel_error_bound S' D ε_sum h_S'_pos hε_nn hε_lt h_D_close
  -- |log D| ≤ log S' + D_log (since log S' ≥ 0).
  have h_abs_logD_le : |Real.log D| ≤ Real.log S' + D_log := by
    have h1 : Real.log D ≤ Real.log S' + D_log := by
      have := abs_le.mp h_log_close_D
      linarith [this.2]
    have h2 : -(Real.log S' + D_log) ≤ Real.log D := by
      have := abs_le.mp h_log_close_D
      linarith [this.1]
    exact abs_le.mpr ⟨h2, h1⟩
  -- |L - log S'| ≤ η_log · log S' + (1 + η_log) · D_log + logSubConst.
  have h_L_close :
      |L - Real.log S'| ≤
        η_log * Real.log S' + (1 + η_log) * D_log + logSubConst := by
    have h_tri : |L - Real.log S'| ≤
        |L - Real.log D| + |Real.log D - Real.log S'| := by
      have : L - Real.log S' = (L - Real.log D) + (Real.log D - Real.log S') := by ring
      rw [this]; exact abs_add_le _ _
    have h_log_abs : |Real.log D| = |Real.log ((sum.result.toVal : ℝ))| := by
      simp only [hD_def]
    have h_log_close' :
        |L - Real.log D| ≤ η_log * |Real.log D| + logSubConst := by
      rw [h_log_abs]
      simpa [hL_def, hD_def] using h_log_close
    calc |L - Real.log S'|
        ≤ |L - Real.log D| + |Real.log D - Real.log S'| := h_tri
      _ ≤ (η_log * |Real.log D| + logSubConst) + D_log := by
          linarith [h_log_close_D]
      _ ≤ (η_log * (Real.log S' + D_log) + logSubConst) + D_log := by
          have := mul_le_mul_of_nonneg_left h_abs_logD_le h_η_log_nn
          linarith
      _ = η_log * Real.log S' + (1 + η_log) * D_log + logSubConst := by ring
  -- Let v := c + L. Final add: |result - v| ≤ η·|v| + subnormalConst, both signs.
  set v : ℝ := c + L with hv_def
  have h_v_ne : v ≠ 0 := by simpa [hv_def, hc_def, hL_def] using h_final_ne
  have h_fpadd_correct : fpAddFinite (fpMax xs hn) logResult = ○v := by
    have := fpAddFinite_correct (fpMax xs hn) logResult h_final_ne
    simpa [hv_def, hc_def, hL_def] using this
  have h_round_eq : ○v = Fp.finite result := by rw [← h_fpadd_correct]; exact h_final_add
  -- Key bound: |result - v| ≤ η·|v| + subnormalConst (sign-symmetric).
  have h_round_unified :
      |(result.toVal : ℝ) - v| ≤ (η : ℝ) * |v| + Softmax.subnormalConst := by
    rcases lt_or_gt_of_ne h_v_ne with hv_neg | hv_pos
    · -- v < 0 case: conjugate to positive.
      have hneg_pos : 0 < -v := by linarith
      have h_round_neg : ○(-v) = Fp.finite (-result) := by
        rw [RModeConj.round_neg v h_v_ne, h_round_eq, Fp.neg_finite]
      have h_round_err_neg : |(-v) - ((-result).toVal : ℝ)| ≤ Fp.ulp (-v) / 2 :=
        RModeNearest_abs_error_le_ulp_half_pos (-v) hneg_pos (-result) h_round_neg
      have hulp_neg := Softmax.ulp_half_le_unified (-v) hneg_pos
      have habs_v : |v| = -v := abs_of_neg hv_neg
      rw [FiniteFp.toVal_neg_eq_neg] at h_round_err_neg
      have h_eq_abs :
          |(-v) - (-(result.toVal : ℝ))| = |(result.toVal : ℝ) - v| := by
        rw [show (-v) - (-(result.toVal : ℝ)) = (result.toVal : ℝ) - v from by ring]
      rw [h_eq_abs] at h_round_err_neg
      rw [habs_v]; linarith
    · -- v > 0 case: direct.
      have h_round_err : |v - (result.toVal : ℝ)| ≤ Fp.ulp v / 2 :=
        RModeNearest_abs_error_le_ulp_half_pos v hv_pos result h_round_eq
      have hulp := Softmax.ulp_half_le_unified v hv_pos
      have habs_v : |v| = v := abs_of_pos hv_pos
      have h_sym : |v - (result.toVal : ℝ)| = |(result.toVal : ℝ) - v| := abs_sub_comm _ _
      rw [h_sym] at h_round_err
      rw [habs_v]; linarith
  -- v = LSE + (L - log S'), so |v| ≤ |LSE| + |L - log S'|.
  have hv_eq : v = LSE + (L - Real.log S') := by
    simp only [hv_def, hc_def, hL_def]
    have : Real.log S' = LSE - c := h_log_S'
    linarith
  have h_abs_v_le : |v| ≤ |LSE| + |L - Real.log S'| := by
    rw [hv_eq]
    exact abs_add_le LSE (L - Real.log S')
  -- Combine everything (sign-agnostic now via |v|).
  have h_v_LSE : |v - LSE| = |L - Real.log S'| := by
    have : v - LSE = L - Real.log S' := by rw [hv_eq]; ring
    rw [this]
  have h_step1 : |(result.toVal : ℝ) - LSE| ≤
      |(result.toVal : ℝ) - v| + |v - LSE| := by
    have : (result.toVal : ℝ) - LSE = ((result.toVal : ℝ) - v) + (v - LSE) := by ring
    rw [this]; exact abs_add_le _ _
  have h_step4 : |(result.toVal : ℝ) - LSE| ≤
      (η : ℝ) * |LSE| +
      (1 + (η : ℝ)) * |L - Real.log S'| + Softmax.subnormalConst := by
    have h_step3 : (η : ℝ) * |v| ≤ (η : ℝ) * (|LSE| + |L - Real.log S'|) :=
      mul_le_mul_of_nonneg_left h_abs_v_le hη_nn
    calc |(result.toVal : ℝ) - LSE|
        ≤ |(result.toVal : ℝ) - v| + |v - LSE| := h_step1
      _ ≤ ((η : ℝ) * |v| + Softmax.subnormalConst) + |L - Real.log S'| := by
          rw [h_v_LSE] at *; linarith
      _ ≤ ((η : ℝ) * (|LSE| + |L - Real.log S'|) + Softmax.subnormalConst) +
            |L - Real.log S'| := by linarith
      _ = (η : ℝ) * |LSE| +
          (1 + (η : ℝ)) * |L - Real.log S'| + Softmax.subnormalConst := by ring
  -- Expand |L - log S'| into its bound.
  have h_logS_eq_diff : Real.log S' = LSE - c := h_log_S'
  have h_L_expand :
      (1 + (η : ℝ)) * |L - Real.log S'| ≤
        (1 + (η : ℝ)) *
          (η_log * (LSE - c) + (1 + η_log) * D_log + logSubConst) := by
    have h : |L - Real.log S'| ≤
        η_log * (LSE - c) + (1 + η_log) * D_log + logSubConst := by
      rw [← h_logS_eq_diff]; exact h_L_close
    exact mul_le_mul_of_nonneg_left h hη_one_nn
  -- Final: assemble into target shape.
  calc |(result.toVal : ℝ) - LSE|
      ≤ (η : ℝ) * |LSE| +
        (1 + (η : ℝ)) * |L - Real.log S'| + Softmax.subnormalConst := h_step4
    _ ≤ (η : ℝ) * |LSE| +
        (1 + (η : ℝ)) *
          (η_log * (LSE - c) + (1 + η_log) * D_log + logSubConst) +
        Softmax.subnormalConst := by linarith

end EndToEnd

/-! ## Bundle

`FpLogSumExpResult` bundles all pipeline hypotheses into a single structure
and exposes `.error_bound`. Parallels `FpSoftmaxResultSubnormalTight`. -/

section Bundle

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

/-- Complete LSE pipeline witness, ready to produce an error bound. -/
structure FpLogSumExpResult (xs : Fin n → FiniteFp) (hn : 0 < n) where
  /-- Shifted inputs `xs' i = xs i - fpMax xs hn`. -/
  xs' : Fin n → FiniteFp
  /-- The shift is exact (holds e.g. under Sterbenz). -/
  h_shift_exact : ∀ j,
    ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ)
  /-- FP exp results on shifted inputs. -/
  exps : Fin n → FiniteFp
  /-- Correctness of the FP exp step. -/
  h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i)
  /-- FP summation witness (any algorithm). -/
  sum : FpSum.FpSumBound exps ℝ
  /-- Combined sum-error margin; ensures log is well-defined. -/
  h_margin :
    ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
      (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1
  /-- Abstract FP log result (a concrete `fpLogFinite` would provide this). -/
  logResult : FiniteFp
  /-- Multiplicative log-rounding coefficient. -/
  η_log : ℝ
  /-- Nonnegativity of `η_log`. -/
  η_log_nn : 0 ≤ η_log
  /-- Additive (subnormal) tail of the log step. -/
  logSubConst : ℝ
  /-- Nonnegativity of `logSubConst`. -/
  logSubConst_nn : 0 ≤ logSubConst
  /-- Log-rounding proximity bound. -/
  h_log_close :
    |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
      η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst
  /-- Final FP result. -/
  result : FiniteFp
  /-- Final `fpAdd(max, logResult) = result` witness. -/
  h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result
  /-- Final-add nonzero side condition (handled sign-symmetrically). -/
  h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0

/-- The main error bound, stated as a bundle method. -/
theorem FpLogSumExpResult.error_bound
    {xs : Fin n → FiniteFp} {hn : 0 < n} (r : FpLogSumExpResult xs hn) :
    letI ε_sum : ℝ :=
      ((η : ℝ) + r.sum.relErr * (1 + (η : ℝ))) +
        (1 + r.sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    |((r.result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (r.η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) - ((fpMax xs hn).toVal : ℝ)) +
          (1 + r.η_log) * D_log + r.logSubConst) +
      Softmax.subnormalConst :=
  fpLogSumExp_end_to_end_error_bound hn xs r.xs' r.h_shift_exact
    r.exps r.h_exp r.sum r.h_margin r.logResult r.η_log r.η_log_nn
    r.logSubConst r.logSubConst_nn r.h_log_close r.result
    r.h_final_add r.h_final_ne

end Bundle

/-! ## Concrete Adapters

Demonstrates plugging `FpSumBound.ofNaive` into the LSE error framework.
Given a `NaiveSum` witness on the `exps` plus the abstract log+add witnesses,
you get an LSE error bound directly. -/

section Demo

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

/-- **NaiveSum demo**: wire `FpSumBound.ofNaive` through
`fpLogSumExp_end_to_end_error_bound`. The resulting
`sum.relErr = (1+η)^(trace.toPairwise.depth) - 1`, with `depth + 1 = n`. -/
theorem fpLogSumExp_naiveSum_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp) (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    {sumResult : FiniteFp}
    (trace : FpSum.NaiveSum (List.ofFn exps) sumResult)
    (hnr : trace.AllNormalRange (R := ℝ))
    (h_margin :
      letI sum := FpSum.FpSumBound.ofNaive exps trace hnr
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sumResult.toVal : ℝ))| ≤
        η_log * |Real.log ((sumResult.toVal : ℝ))| + logSubConst)
    (result : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0) :
    letI sum := FpSum.FpSumBound.ofNaive exps trace hnr
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    |((result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) - ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst := by
  set sum := FpSum.FpSumBound.ofNaive exps trace hnr with hsum_def
  have h_log_close' :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst := by
    simpa [hsum_def, FpSum.FpSumBound.ofNaive, FpSum.FpSumBound.ofPairwise]
      using h_log_close
  exact fpLogSumExp_end_to_end_error_bound hn xs xs' h_shift_exact exps h_exp sum
    h_margin logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close'
    result h_final_add h_final_ne

/-- **Kahan demo**: wire `FpSumBound.ofKahanTrace` through
`fpLogSumExp_end_to_end_error_bound`. The resulting
`sum.relErr = 2η + n·η²` (via `kahan_higham_bound`). -/
theorem fpLogSumExp_kahanSum_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp) (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    {init final : KahanSum.State}
    (trace : KahanSum.Trace (List.ofFn exps) init final)
    (hinit_sum : init.sum.toVal (R := ℝ) = 0)
    (hinit_comp : init.comp.toVal (R := ℝ) = 0)
    (hexact : ∀ (st : KahanSum.State) (x : FiniteFp)
                (step : KahanSum.StepWitness st x),
      KahanSum.StepTwoSumExact (R := ℝ) st x step)
    (hnr : ∀ (st : KahanSum.State) (x : FiniteFp)
             (step : KahanSum.StepWitness st x),
      KahanSum.StepNormalRange (R := ℝ) st x step)
    (hM : ∀ (st : KahanSum.State) (x : FiniteFp)
            (step : KahanSum.StepWitness st x),
      |(st.sum.toVal : ℝ) + step.y.toVal| ≤
        ((List.ofFn exps).map (fun x => |x.toVal (R := ℝ)|)).sum)
    (h_margin :
      letI sum := FpSum.FpSumBound.ofKahanTrace exps trace
        hinit_sum hinit_comp hexact hnr hM
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((final.sum.toVal : ℝ))| ≤
        η_log * |Real.log ((final.sum.toVal : ℝ))| + logSubConst)
    (result : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0) :
    letI sum := FpSum.FpSumBound.ofKahanTrace exps trace
      hinit_sum hinit_comp hexact hnr hM
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    |((result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) - ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst := by
  set sum := FpSum.FpSumBound.ofKahanTrace exps trace
    hinit_sum hinit_comp hexact hnr hM with hsum_def
  have h_log_close' :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst := by
    simpa [hsum_def, FpSum.FpSumBound.ofKahanTrace] using h_log_close
  exact fpLogSumExp_end_to_end_error_bound hn xs xs' h_shift_exact exps h_exp sum
    h_margin logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close'
    result h_final_add h_final_ne

/-- **Neumaier demo** (loose): wire `FpSumBound.ofNeumaierTrace` through
`fpLogSumExp_end_to_end_error_bound`. See the `NeumaierAdapter` docstring in
`FpSum.lean`: the bound is loose because `FpSumBound` cannot expose the
compensator. For tight bounds prefer `fpLogSumExp_kahanSum_error_bound` or
`fpLogSumExp_neumaierCompensated_error_bound`. -/
theorem fpLogSumExp_neumaierSum_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp) (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    {init final : NeumaierSum.NState}
    (trace : NeumaierSum.NTrace (R := ℝ) (List.ofFn exps) init final)
    (hinit_sum : init.sum.toVal (R := ℝ) = 0)
    (hinit_comp : init.comp.toVal (R := ℝ) = 0)
    (hnr : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
             (step : NeumaierSum.NStepWitness (R := ℝ) st x),
      NeumaierSum.NStepNormalRange (R := ℝ) st x step)
    (hM : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
            (_step : NeumaierSum.NStepWitness (R := ℝ) st x),
      |(st.sum.toVal : ℝ) + x.toVal| ≤
        ((List.ofFn exps).map (fun x => |x.toVal (R := ℝ)|)).sum)
    (h_margin :
      letI sum := FpSum.FpSumBound.ofNeumaierTrace exps trace
        hinit_sum hinit_comp hnr hM
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((final.sum.toVal : ℝ))| ≤
        η_log * |Real.log ((final.sum.toVal : ℝ))| + logSubConst)
    (result : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0) :
    letI sum := FpSum.FpSumBound.ofNeumaierTrace exps trace
      hinit_sum hinit_comp hnr hM
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    |((result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) - ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst := by
  set sum := FpSum.FpSumBound.ofNeumaierTrace exps trace
    hinit_sum hinit_comp hnr hM with hsum_def
  have h_log_close' :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst := by
    simpa [hsum_def, FpSum.FpSumBound.ofNeumaierTrace] using h_log_close
  exact fpLogSumExp_end_to_end_error_bound hn xs xs' h_shift_exact exps h_exp sum
    h_margin logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close'
    result h_final_add h_final_ne

/-- **Compensated-Neumaier demo** (tight): Neumaier via
`FpSumBoundCompensated.ofNeumaierTrace` + `compensateAndRound`. Preserves
Neumaier's `O(n²η²)` accuracy at the cost of one extra `fpAdd(sum, comp)`
step. Final `relErr = η + O(n²η²)`. -/
theorem fpLogSumExp_neumaierCompensated_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp) (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    {init final : NeumaierSum.NState}
    (trace : NeumaierSum.NTrace (R := ℝ) (List.ofFn exps) init final)
    (hinit_sum : init.sum.toVal (R := ℝ) = 0)
    (hinit_comp : init.comp.toVal (R := ℝ) = 0)
    (hnr : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
             (step : NeumaierSum.NStepWitness (R := ℝ) st x),
      NeumaierSum.NStepNormalRange (R := ℝ) st x step)
    (hM : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
            (_step : NeumaierSum.NStepWitness (R := ℝ) st x),
      |(st.sum.toVal : ℝ) + x.toVal| ≤
        ((List.ofFn exps).map (fun x => |x.toVal (R := ℝ)|)).sum)
    {combinedResult : FiniteFp}
    (hadd : final.sum + final.comp = Fp.finite combinedResult)
    (hnr_add : isNormalRange ((final.sum.toVal : ℝ) + final.comp.toVal) ∨
               (final.sum.toVal : ℝ) + final.comp.toVal = 0)
    (h_margin :
      letI sum := (FpSum.FpSumBoundCompensated.ofNeumaierTrace exps trace
        hinit_sum hinit_comp hnr hM).compensateAndRound hadd hnr_add
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((combinedResult.toVal : ℝ))| ≤
        η_log * |Real.log ((combinedResult.toVal : ℝ))| + logSubConst)
    (result : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite result)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0) :
    letI sum := (FpSum.FpSumBoundCompensated.ofNeumaierTrace exps trace
      hinit_sum hinit_comp hnr hM).compensateAndRound hadd hnr_add
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    |((result.toVal : ℝ)) - logsumexp (fun j => ((xs j).toVal : ℝ))| ≤
      (η : ℝ) * |logsumexp (fun j => ((xs j).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun j => ((xs j).toVal : ℝ)) - ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst := by
  set sum := (FpSum.FpSumBoundCompensated.ofNeumaierTrace exps trace
    hinit_sum hinit_comp hnr hM).compensateAndRound hadd hnr_add with hsum_def
  have h_log_close' :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst := by
    simpa [hsum_def, FpSum.FpSumBoundCompensated.compensateAndRound]
      using h_log_close
  exact fpLogSumExp_end_to_end_error_bound hn xs xs' h_shift_exact exps h_exp sum
    h_margin logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close'
    result h_final_add h_final_ne

end Demo

end LogSumExp
