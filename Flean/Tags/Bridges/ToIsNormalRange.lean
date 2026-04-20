import Flean.Tags.BoundedRange
import Flean.Util
import Flean.Rounding.Rounding
import Flean.Operations.Softmax

/-!
# Bridges to `isNormalRange`

Theorems that discharge an `isNormalRange (...)` hypothesis given a
tag on some input value. Organized by **target hypothesis** per
design doc §1.3:

> A user hitting `h_exp_nr : isNormalRange (...)` on a call site wants
> to ask "which tags can give me this?" Indexing by target makes that
> question answerable via file navigation. Indexing by source forces
> the user to pre-guess the answer.

## Current contents

- `IsBoundedRange.exp_isNormalRange` — if `xs` is in `I : FpInterval ℝ`
  with `I.lo ≥ min_exp · log 2` and `I.hi < (max_exp + 1) · log 2`, then
  `isNormalRange (Real.exp ((xs i).toVal : ℝ))` for all `i`.
- `IsBoundedRange.quot_isNormalRange` — bounded `xs` + softmax-denom
  hypotheses + separation condition → `isNormalRange (exps_i / denom)`.
  Discharges the `h_quot_nr` precondition of `fpSoftmaxOf_error_bound`.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]

/-- **Bridge theorem**: if `xs` lies in `I : FpInterval ℝ` with
`I.lo ≥ min_exp · log 2` and `I.hi < (max_exp+1) · log 2`, then
`Real.exp ((xs i).toVal)` is in the normal range for all `i`.

Discharges the `h_exp_nr` precondition of `fpSoftmaxOf_error_bound`
from an input `IsBoundedRange` tag automatically. -/
theorem IsBoundedRange.exp_isNormalRange
    {n : ℕ} {I : FpInterval ℝ} {xs : Fin n → FiniteFp}
    (h : IsBoundedRange (R := ℝ) I xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ I.lo)
    (hhi : I.hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (i : Fin n) : isNormalRange (Real.exp ((xs i).toVal : ℝ)) := by
  refine ⟨?_, ?_⟩
  · have hy_ge : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ ((xs i).toVal : ℝ) :=
      le_trans hlo (h.lower i)
    have hexp_step : Real.exp ((FloatFormat.min_exp : ℝ) * Real.log 2) ≤
                     Real.exp ((xs i).toVal : ℝ) :=
      Real.exp_le_exp_of_le hy_ge
    rwa [exp_int_mul_log2] at hexp_step
  · have hy_lt : ((xs i).toVal : ℝ) <
                 ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2 :=
      lt_of_le_of_lt (h.upper i) hhi
    have hexp_step : Real.exp ((xs i).toVal : ℝ) <
                     Real.exp (((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2) :=
      Real.exp_strictMono hy_lt
    rwa [exp_int_mul_log2] at hexp_step

/-! ## `quot_isNormalRange` — softmax quotient bridge

The heavy bridge.  Given a bounded-range tag on softmax inputs `xs`,
log-bound conditions on `I.lo` / `I.hi`, pointwise exp correctness,
denominator closeness to the exact sum, and a "separation" condition
`4·n·2^min_exp ≤ exp(I.lo − I.hi)` (smallest softmax entry doesn't
underflow), produce `isNormalRange ((exps i).toVal / denom.toVal)`
for each `i`.

### Why the separation constant is 4

The proof needs `4(1−t) ≥ (1+u)(1+t)` (for the `2^min_exp` lower
bound, with `t := η`, `u := εsum`) and `(1+t) ≤ 3(1−u)(1−t)` (for
the `< 2^(max_exp+1)` upper bound, giving quotient
`≤ 3 < 4 ≤ 2^(max_exp+1)`).  Both hold for `0 ≤ t, u ≤ 1/4`.
`η ≤ 1/4` is universal via `FloatFormat.valid_prec` (`prec ≥ 2`);
`εsum ≤ 1/4` is a user hypothesis (satisfied by any practical
summation with `n·η ≤ 1/4`, e.g. Kahan's `2η + nη²`).  The separation
constant 4 is the smallest clean integer that makes the `2^min_exp`
lower bound work at `t = u = 1/4`; tighter formats or tighter `εsum`
permit smaller constants but 4 suffices universally.
-/

omit [FloatFormat] in
/-- Scalar lemma: `4(1−t) ≥ (1+u)(1+t)` for `0 ≤ t, u ≤ 1/4`.  Used
with `t := η[ℝ]`, `u := εsum` in the quotient lower-bound chain. -/
private theorem four_one_sub_ge_one_add_mul_one_add
    {t u : ℝ} (ht_nn : 0 ≤ t) (ht_le : t ≤ 1/4)
    (_hu_nn : 0 ≤ u) (hu_le : u ≤ 1/4) :
    (1 + u) * (1 + t) ≤ 4 * (1 - t) := by
  nlinarith [mul_nonneg ht_nn ht_nn]

omit [FloatFormat] in
/-- Scalar lemma: `(1+t) ≤ 3(1−u)(1−t)` for `0 ≤ t, u ≤ 1/4`.  Used
with `t := η[ℝ]`, `u := εsum` in the quotient upper-bound chain. -/
private theorem one_add_le_three_one_sub_mul_one_sub
    {t u : ℝ} (ht_nn : 0 ≤ t) (ht_le : t ≤ 1/4)
    (hu_nn : 0 ≤ u) (hu_le : u ≤ 1/4) :
    1 + t ≤ 3 * ((1 - u) * (1 - t)) := by
  nlinarith [mul_nonneg hu_nn ht_nn]

/-- `η = 2^(−prec) ≤ 1/4` for any format (since `prec ≥ 2`). -/
private theorem eta_le_quarter : η[ℝ] ≤ 1/4 := by
  simp only [FloatFormat.hEps_def]
  have h_prec : 2 ≤ FloatFormat.prec := FloatFormat.valid_prec
  have : (2 : ℝ) ^ (-(FloatFormat.prec : ℤ)) ≤ (2 : ℝ) ^ (-2 : ℤ) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  calc (2 : ℝ) ^ (-(FloatFormat.prec : ℤ))
      ≤ (2 : ℝ) ^ (-2 : ℤ) := this
    _ = 1/4 := by norm_num

/-- **Softmax-quotient bridge**: bounded-range tag + separation + denom
correctness + exp correctness → each rounded softmax quotient is in
the normal range.

The `εsum ≤ 1/4` hypothesis captures any practical summation-based
denom error bound (single fp-add gives `εsum = η`; Kahan gives
`εsum = 2η + nη²`; as long as this stays `≤ 1/4`).  Separation constant
`4·n·2^min_exp ≤ exp(I.lo − I.hi)` is sufficient for `prec ≥ 2`
(universal); tighter formats or tighter `εsum` admit smaller constants
(see module doc).  Discharges the `h_quot_nr` precondition of
`fpSoftmaxOf_error_bound` from inputs that already carry an
`IsBoundedRange` tag, a separation witness, and the usual
denominator-closeness hypothesis. -/
theorem IsBoundedRange.quot_isNormalRange
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]
    {n : ℕ} (hn : 0 < n) {I : FpInterval ℝ} {εsum : ℝ}
    {xs : Fin n → FiniteFp} {exps : Fin n → FiniteFp} {denom : FiniteFp}
    (hxs : IsBoundedRange (R := ℝ) I xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ I.lo)
    (hhi : I.hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_εsum_nn : 0 ≤ εsum) (h_εsum_le : εsum ≤ 1/4)
    (hd_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (hd_pos : 0 < (denom.toVal : ℝ))
    (h_separation : 4 * (n : ℝ) * (2 : ℝ) ^ (FloatFormat.min_exp : ℤ) ≤
                    Real.exp (I.lo - I.hi))
    (i : Fin n) :
    isNormalRange (((exps i).toVal : ℝ) / denom.toVal) := by
  -- Abbreviations.
  set d : ℝ := (denom.toVal : ℝ) with hd_def
  set S : ℝ := ∑ j, ((exps j).toVal : ℝ) with hS_def
  set E : ℝ := ∑ j, Real.exp ((xs j).toVal : ℝ) with hE_def
  -- Bridge: h_exp_nr from IsBoundedRange.
  have h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)) :=
    hxs.exp_isNormalRange hlo hhi
  -- η / εsum bookkeeping.
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hη_le_q : η[ℝ] ≤ 1/4 := eta_le_quarter
  have hη_lt_one : η[ℝ] < 1 := by linarith
  have h1mη_pos : (0 : ℝ) < 1 - η[ℝ] := by linarith
  have h1pη_pos : (0 : ℝ) < 1 + η[ℝ] := by linarith
  have h_εsum_lt_one : εsum < 1 := by linarith
  have h1m_εsum_pos : (0 : ℝ) < 1 - εsum := by linarith
  have h1p_εsum_pos : (0 : ℝ) < 1 + εsum := by linarith
  -- Per-exp multiplicative error.
  have h_ei_ge : ∀ j, (1 - η[ℝ]) * Real.exp ((xs j).toVal : ℝ) ≤
                      ((exps j).toVal : ℝ) :=
    fun j => Softmax.exps_ge_of_correct xs exps h_exp h_exp_nr j
  have h_ei_le : ∀ j, ((exps j).toVal : ℝ) ≤
                      (1 + η[ℝ]) * Real.exp ((xs j).toVal : ℝ) :=
    fun j => Softmax.exps_le_of_correct xs exps h_exp h_exp_nr j
  -- Each (exps j).toVal > 0 via the (1−η) · exp(xs_j) lower bound.
  have h_ej_pos : ∀ j, 0 < ((exps j).toVal : ℝ) := by
    intro j
    have := h_ei_ge j
    have hexp_pos : 0 < Real.exp ((xs j).toVal : ℝ) := Real.exp_pos _
    exact lt_of_lt_of_le (mul_pos h1mη_pos hexp_pos) this
  -- |êⱼ| = êⱼ.  Rewrite hd_close.
  have h_sum_abs_eq : ∑ j, |((exps j).toVal : ℝ)| = S := by
    apply Finset.sum_congr rfl
    intro j _; exact abs_of_pos (h_ej_pos j)
  rw [h_sum_abs_eq] at hd_close
  -- Σ, E positivity.
  have hS_pos : 0 < S := by
    apply Finset.sum_pos (fun j _ => h_ej_pos j)
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hE_pos : 0 < E := by
    apply Finset.sum_pos (fun j _ => Real.exp_pos _)
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  -- Closeness-derived bounds on d.
  have hd_bounds := abs_le.mp hd_close
  have hd_ge : (1 - εsum) * S ≤ d := by nlinarith [hd_bounds.1]
  have hd_le : d ≤ (1 + εsum) * S := by nlinarith [hd_bounds.2]
  -- Rounded sum / exact sum bounds via per-exp bounds.
  have hS_le_E : S ≤ (1 + η[ℝ]) * E := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => h_ei_le j)
  have hS_ge_E : (1 - η[ℝ]) * E ≤ S := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => h_ei_ge j)
  -- eᵢ bounds via I.lo / I.hi.
  have h_ei_ge_lo : Real.exp I.lo ≤ Real.exp ((xs i).toVal : ℝ) :=
    Real.exp_le_exp_of_le (hxs.lower i)
  have h_ei_le_hi : Real.exp ((xs i).toVal : ℝ) ≤ Real.exp I.hi :=
    Real.exp_le_exp_of_le (hxs.upper i)
  -- Σⱼeⱼ ≤ n · exp(I.hi).
  have hE_le_n_hi : E ≤ (n : ℝ) * Real.exp I.hi := by
    calc E = ∑ j, Real.exp ((xs j).toVal : ℝ) := rfl
      _ ≤ ∑ _j : Fin n, Real.exp I.hi :=
          Finset.sum_le_sum (fun j _ => Real.exp_le_exp_of_le (hxs.upper j))
      _ = (n : ℝ) * Real.exp I.hi := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  -- eᵢ ≤ Σⱼeⱼ (single entry ≤ nonneg sum).
  have h_ei_le_E : Real.exp ((xs i).toVal : ℝ) ≤ E := by
    apply Finset.single_le_sum
      (f := fun j => Real.exp ((xs j).toVal : ℝ))
      (fun j _ => le_of_lt (Real.exp_pos _))
    exact Finset.mem_univ _
  -- Auxiliary positives.
  have hei_pos : 0 < Real.exp ((xs i).toVal : ℝ) := Real.exp_pos _
  have hexp_hi_pos : 0 < Real.exp I.hi := Real.exp_pos _
  have hexp_diff_pos : 0 < Real.exp (I.lo - I.hi) := Real.exp_pos _
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have h_two_min_exp_pos : 0 < (2 : ℝ) ^ (FloatFormat.min_exp : ℤ) := by positivity
  refine ⟨?_, ?_⟩
  · -- LOWER BOUND: 2^min_exp ≤ d̂_i / denom.
    rw [le_div_iff₀ hd_pos]
    -- Goal: 2^min_exp * d ≤ (exps i).toVal.
    -- Strategy: show (exps i).toVal ≥ (1−η)·exp(xs_i), and
    -- d ≤ (1+εsum)(1+η)·n·exp(I.hi).
    have hd_le_n_hi :
        d ≤ (1 + εsum) * (1 + η[ℝ]) * ((n : ℝ) * Real.exp I.hi) := by
      calc d ≤ (1 + εsum) * S := hd_le
        _ ≤ (1 + εsum) * ((1 + η[ℝ]) * E) :=
            mul_le_mul_of_nonneg_left hS_le_E (le_of_lt h1p_εsum_pos)
        _ = (1 + εsum) * (1 + η[ℝ]) * E := by ring
        _ ≤ (1 + εsum) * (1 + η[ℝ]) * ((n : ℝ) * Real.exp I.hi) := by
            have h_nn : (0 : ℝ) ≤ (1 + εsum) * (1 + η[ℝ]) :=
              mul_nonneg (le_of_lt h1p_εsum_pos) (le_of_lt h1pη_pos)
            exact mul_le_mul_of_nonneg_left hE_le_n_hi h_nn
    -- Target chain:
    -- 2^min_exp · d ≤ 2^min_exp · (1+εsum)(1+η) · n · exp(I.hi)
    --              ≤ (1+εsum)(1+η)/4 · exp(I.lo)    [from h_separation]
    --              ≤ (1−η) · exp(I.lo)              [from scalar helper]
    --              ≤ (exps i).toVal                [from h_ei_ge]
    have h_sep_mul : 4 * (n : ℝ) * (2 : ℝ)^(FloatFormat.min_exp : ℤ) *
                      Real.exp I.hi ≤ Real.exp I.lo := by
      have h_diff : Real.exp (I.lo - I.hi) * Real.exp I.hi = Real.exp I.lo := by
        rw [← Real.exp_add]; ring_nf
      calc 4 * (n : ℝ) * (2 : ℝ)^(FloatFormat.min_exp : ℤ) * Real.exp I.hi
          ≤ Real.exp (I.lo - I.hi) * Real.exp I.hi :=
            mul_le_mul_of_nonneg_right h_separation (le_of_lt hexp_hi_pos)
        _ = Real.exp I.lo := h_diff
    have step1 : (2 : ℝ)^(FloatFormat.min_exp : ℤ) * d ≤
                  (2 : ℝ)^(FloatFormat.min_exp : ℤ) *
                    ((1 + εsum) * (1 + η[ℝ]) * ((n : ℝ) * Real.exp I.hi)) :=
      mul_le_mul_of_nonneg_left hd_le_n_hi (le_of_lt h_two_min_exp_pos)
    have hkey : (1 + εsum) * (1 + η[ℝ]) ≤ 4 * (1 - η[ℝ]) :=
      four_one_sub_ge_one_add_mul_one_add hη_nn hη_le_q h_εsum_nn h_εsum_le
    have step2 :
        (2 : ℝ)^(FloatFormat.min_exp : ℤ) *
          ((1 + εsum) * (1 + η[ℝ]) * ((n : ℝ) * Real.exp I.hi)) ≤
        (1 - η[ℝ]) * Real.exp I.lo := by
      have h_sep_rearrange :
          (2 : ℝ)^(FloatFormat.min_exp : ℤ) * ((n : ℝ) * Real.exp I.hi) ≤
            Real.exp I.lo / 4 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
        linarith [h_sep_mul]
      have h_coef_nn : (0 : ℝ) ≤ (1 + εsum) * (1 + η[ℝ]) :=
        mul_nonneg (le_of_lt h1p_εsum_pos) (le_of_lt h1pη_pos)
      calc (2 : ℝ)^(FloatFormat.min_exp : ℤ) *
            ((1 + εsum) * (1 + η[ℝ]) * ((n : ℝ) * Real.exp I.hi))
          = (1 + εsum) * (1 + η[ℝ]) *
              ((2 : ℝ)^(FloatFormat.min_exp : ℤ) *
                ((n : ℝ) * Real.exp I.hi)) := by ring
        _ ≤ (1 + εsum) * (1 + η[ℝ]) * (Real.exp I.lo / 4) :=
            mul_le_mul_of_nonneg_left h_sep_rearrange h_coef_nn
        _ = (1 + εsum) * (1 + η[ℝ]) / 4 * Real.exp I.lo := by ring
        _ ≤ (1 - η[ℝ]) * Real.exp I.lo := by
            have hlo_pos : (0 : ℝ) < Real.exp I.lo := Real.exp_pos _
            have h_div_le : (1 + εsum) * (1 + η[ℝ]) / 4 ≤ 1 - η[ℝ] := by
              linarith
            exact mul_le_mul_of_nonneg_right h_div_le (le_of_lt hlo_pos)
    have step3 : (1 - η[ℝ]) * Real.exp I.lo ≤ ((exps i).toVal : ℝ) := by
      calc (1 - η[ℝ]) * Real.exp I.lo
          ≤ (1 - η[ℝ]) * Real.exp ((xs i).toVal : ℝ) :=
            mul_le_mul_of_nonneg_left h_ei_ge_lo (le_of_lt h1mη_pos)
        _ ≤ ((exps i).toVal : ℝ) := h_ei_ge i
    linarith
  · -- UPPER BOUND: d̂_i / denom < 2^(max_exp+1).
    rw [div_lt_iff₀ hd_pos]
    -- Strategy: show (exps i).toVal ≤ (1+η)·eᵢ ≤ (1+η)·E
    -- and (1−εsum)(1−η)·E ≤ d, so (exps i).toVal / d
    --     ≤ (1+η)/((1−εsum)(1−η)) ≤ 3 < 4 ≤ 2^(max_exp+1).
    have hd_ge_E : (1 - εsum) * (1 - η[ℝ]) * E ≤ d := by
      calc (1 - εsum) * (1 - η[ℝ]) * E
          = (1 - εsum) * ((1 - η[ℝ]) * E) := by ring
        _ ≤ (1 - εsum) * S :=
            mul_le_mul_of_nonneg_left hS_ge_E (le_of_lt h1m_εsum_pos)
        _ ≤ d := hd_ge
    have hei_le_3 :
        ((exps i).toVal : ℝ) ≤ (3 : ℝ) * ((1 - εsum) * (1 - η[ℝ]) * E) := by
      calc ((exps i).toVal : ℝ)
          ≤ (1 + η[ℝ]) * Real.exp ((xs i).toVal : ℝ) := h_ei_le i
        _ ≤ (1 + η[ℝ]) * E :=
            mul_le_mul_of_nonneg_left h_ei_le_E (le_of_lt h1pη_pos)
        _ ≤ (3 : ℝ) * ((1 - εsum) * (1 - η[ℝ])) * E := by
            have h_coef : 1 + η[ℝ] ≤ (3 : ℝ) * ((1 - εsum) * (1 - η[ℝ])) :=
              one_add_le_three_one_sub_mul_one_sub
                hη_nn hη_le_q h_εsum_nn h_εsum_le
            exact mul_le_mul_of_nonneg_right h_coef (le_of_lt hE_pos)
        _ = (3 : ℝ) * ((1 - εsum) * (1 - η[ℝ]) * E) := by ring
    have hei_le_3d : ((exps i).toVal : ℝ) ≤ (3 : ℝ) * d :=
      le_trans hei_le_3
        (mul_le_mul_of_nonneg_left hd_ge_E (by norm_num : (0 : ℝ) ≤ (3 : ℝ)))
    have h3d_lt_4d : (3 : ℝ) * d < (4 : ℝ) * d := by linarith
    have h4_le_two_me : (4 : ℝ) ≤ (2 : ℝ)^(FloatFormat.max_exp + 1 : ℤ) := by
      have h_me_ge : (2 : ℤ) ≤ FloatFormat.max_exp + 1 := by
        have := FloatFormat.max_exp_pos; omega
      calc (4 : ℝ) = (2 : ℝ)^(2 : ℤ) := by norm_num
        _ ≤ (2 : ℝ)^(FloatFormat.max_exp + 1 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_me_ge
    have h4d_le_twod : (4 : ℝ) * d ≤ (2 : ℝ)^(FloatFormat.max_exp + 1 : ℤ) * d :=
      mul_le_mul_of_nonneg_right h4_le_two_me (le_of_lt hd_pos)
    linarith

end Flean.Tags
