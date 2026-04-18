import Flean.Operations.Exp
import Flean.Operations.Div
import Flean.Operations.FpSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Softmax: Definition and Numerical Stability

This module formalizes the softmax function and proves that the subtract-max trick
prevents overflow in floating-point exponential computations.

## Main definitions

* `Softmax.softmax` — the real-valued softmax function on `Fin n → ℝ`
* `Softmax.shift` — vector shifting by a constant

## Main results

* `Softmax.softmax_shift_eq` — softmax is invariant under uniform translation
* `Softmax.exp_lt_overflowThreshold_of_nonpos` — `exp(x) < overflowThreshold` when `x ≤ 0`
* `Softmax.shifted_exp_no_overflow` — shifted exponentials do not overflow
* `Softmax.softmax_nonneg` — softmax outputs are nonneg
* `Softmax.softmax_le_one` — softmax outputs are in [0, 1]
* `Softmax.softmax_sum_eq_one` — softmax outputs sum to 1
-/

set_option autoImplicit false

namespace Softmax

open Finset BigOperators

/-! ## Mathematical Softmax -/

variable {n : ℕ}

/-- Softmax denominator: `Σ_j exp(xs j)`. -/
noncomputable def softmaxDenom (xs : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, Real.exp (xs j)

/-- Mathematical softmax: `exp(xs i) / Σ_j exp(xs j)`. -/
noncomputable def softmax (xs : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (xs i) / softmaxDenom xs

/-- Shift a vector by subtracting a constant from each component. -/
def shift (xs : Fin n → ℝ) (c : ℝ) : Fin n → ℝ :=
  fun i => xs i - c

/-! ### Basic properties -/

theorem softmaxDenom_pos (xs : Fin n → ℝ) (hn : 0 < n) :
    0 < softmaxDenom xs := by
  apply Finset.sum_pos
  · intro j _
    exact Real.exp_pos (xs j)
  · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)

theorem softmax_nonneg (xs : Fin n → ℝ) (hn : 0 < n) (i : Fin n) :
    0 ≤ softmax xs i :=
  div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (softmaxDenom_pos xs hn))

theorem softmax_le_one (xs : Fin n → ℝ) (i : Fin n) :
    softmax xs i ≤ 1 := by
  unfold softmax softmaxDenom
  apply div_le_one_of_le₀
  · exact Finset.single_le_sum (fun j _ => le_of_lt (Real.exp_pos (xs j)))
      (Finset.mem_univ i)
  · exact le_of_lt (Finset.sum_pos (fun j _ => Real.exp_pos (xs j))
      ⟨i, Finset.mem_univ i⟩)

theorem softmax_sum_eq_one (xs : Fin n → ℝ) (hn : 0 < n) :
    ∑ i : Fin n, softmax xs i = 1 := by
  unfold softmax
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (softmaxDenom_pos xs hn))

/-! ## Shift Invariance -/

theorem softmaxDenom_shift (xs : Fin n → ℝ) (c : ℝ) :
    softmaxDenom (shift xs c) = Real.exp (-c) * softmaxDenom xs := by
  unfold softmaxDenom shift
  rw [Finset.mul_sum]
  congr 1
  ext j
  rw [sub_eq_add_neg, Real.exp_add]
  ring

/-- Softmax is invariant under uniform translation of the input vector. -/
theorem softmax_shift_eq (xs : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    softmax (shift xs c) i = softmax xs i := by
  unfold softmax
  rw [softmaxDenom_shift]
  show Real.exp (xs i - c) / (Real.exp (-c) * softmaxDenom xs) = _
  rw [sub_eq_add_neg, Real.exp_add]
  rw [mul_comm (Real.exp (-c)) (softmaxDenom xs)]
  rw [mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos _))]

/-! ## Overflow Analysis -/

section Overflow

variable [FloatFormat]

omit [FloatFormat] in
/-- `exp(x) ≤ 1` when `x ≤ 0`. -/
theorem exp_le_one_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    Real.exp x ≤ 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp_of_le hx

/-- `1 < overflowThreshold` for any float format. -/
theorem one_lt_overflowThreshold :
    1 < FloatFormat.overflowThreshold ℝ := by
  have h1 : (1 : ℝ) < (2 : ℝ) ^ FloatFormat.max_exp := by
    have : (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by simp
    rw [this]
    apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
    exact FloatFormat.max_exp_pos
  linarith [FloatFormat.zpow_max_exp_le_overflow_threshold (R := ℝ)]

/-- When `x ≤ 0`, `exp(x) < overflowThreshold`. This is the key fact that makes
the subtract-max trick work: shifted exponentials cannot overflow. -/
theorem exp_lt_overflowThreshold_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    Real.exp x < FloatFormat.overflowThreshold ℝ :=
  lt_of_le_of_lt (exp_le_one_of_nonpos x hx) one_lt_overflowThreshold

/-- When `x > ln(overflowThreshold)`, `exp(x)` overflows. This shows why naive
softmax fails for large inputs. -/
theorem exp_ge_overflowThreshold_of_large (x : ℝ)
    (hx : Real.log (FloatFormat.overflowThreshold ℝ) ≤ x) :
    FloatFormat.overflowThreshold ℝ ≤ Real.exp x := by
  rw [← Real.exp_log (FloatFormat.overflow_threshold_pos (R := ℝ))]
  exact Real.exp_le_exp_of_le hx

/-! ### Shifted inputs are safe -/

omit [FloatFormat] in
/-- After shifting by c, any input with `xs i ≤ c` has `xs i - c ≤ 0`. -/
theorem shift_nonpos_of_le (xs : Fin n → ℝ) (c : ℝ) (i : Fin n)
    (hle : xs i ≤ c) : shift xs c i ≤ 0 := by
  unfold shift; linarith

omit [FloatFormat] in
/-- After shifting by the maximum, all shifted values are `≤ 0`. -/
theorem shift_by_max_nonpos (xs : Fin n → ℝ)
    (i₀ : Fin n) (hi₀ : ∀ j, xs j ≤ xs i₀) (j : Fin n) :
    shift xs (xs i₀) j ≤ 0 :=
  shift_nonpos_of_le xs (xs i₀) j (hi₀ j)

/-- Each `exp(xs j - max(xs))` is below `overflowThreshold`. -/
theorem shifted_exp_no_overflow (xs : Fin n → ℝ)
    (c : ℝ) (hc : ∀ i, xs i ≤ c) (j : Fin n) :
    Real.exp (shift xs c j) < FloatFormat.overflowThreshold ℝ :=
  exp_lt_overflowThreshold_of_nonpos _ (shift_nonpos_of_le xs c j (hc j))

omit [FloatFormat] in
/-- The denominator sum of shifted exponentials is bounded by `n`. -/
theorem shifted_softmaxDenom_le (xs : Fin n → ℝ)
    (c : ℝ) (hc : ∀ i, xs i ≤ c) :
    softmaxDenom (shift xs c) ≤ n := by
  unfold softmaxDenom
  calc ∑ j : Fin n, Real.exp (shift xs c j)
      ≤ ∑ _ : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact exp_le_one_of_nonpos _ (shift_nonpos_of_le xs c j (hc j))
    _ = n := by simp

omit [FloatFormat] in
/-- The denominator has at least one term equal to 1 (from the max element). -/
theorem shifted_softmaxDenom_ge_one (xs : Fin n → ℝ)
    (i₀ : Fin n) (_hi₀ : ∀ j, xs j ≤ xs i₀) :
    1 ≤ softmaxDenom (shift xs (xs i₀)) := by
  unfold softmaxDenom
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ = Real.exp (shift xs (xs i₀) i₀) := by unfold shift; ring_nf
    _ ≤ ∑ j : Fin n, Real.exp (shift xs (xs i₀) j) :=
        Finset.single_le_sum (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i₀)

end Overflow

/-! ## FP-Level Results -/

section FPLevel

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

omit [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [ExpApprox] [ExpApproxSound] in
/-- For nearest rounding, `○x ≤ Fp.finite largestFiniteFloat` when `x ≤ largestFiniteFloat.toVal`.
Proof: by monotonicity + idempotence. -/
theorem round_le_largestFiniteFloat (x : ℝ)
    (hle : x ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    RMode.round (R := ℝ) x ≤ Fp.finite FiniteFp.largestFiniteFloat := by
  calc RMode.round (R := ℝ) x
      ≤ RMode.round (R := ℝ) (FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :=
        RModeMono.round_mono hle
    _ = Fp.finite FiniteFp.largestFiniteFloat :=
        RModeIdem.round_idempotent _ (Or.inl rfl)

omit [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [ExpApprox] [ExpApproxSound] in
/-- For nearest rounding, if `x ≤ largestFiniteFloat.toVal` then `○x ≠ +∞`. -/
theorem round_ne_pos_inf_of_le_largest (x : ℝ)
    (hle : x ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    RMode.round (R := ℝ) x ≠ Fp.infinite false := by
  intro h
  have hle' := round_le_largestFiniteFloat x hle
  rw [h] at hle'
  simp at hle'

omit [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [ExpApprox] [ExpApproxSound] in
/-- For nearest rounding, if `0 ≤ x ≤ largestFiniteFloat.toVal`, then `○x` is finite. -/
theorem round_exists_finite_of_nonneg_bounded (x : ℝ)
    (hx_nn : 0 ≤ x)
    (hx_le : x ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    ∃ f : FiniteFp, RMode.round (R := ℝ) x = Fp.finite f := by
  have hlo : Fp.finite 0 ≤ RMode.round (R := ℝ) x := by
    rw [show (Fp.finite 0 : Fp) = RMode.round (R := ℝ) (0 : ℝ) from
      (RModeZero.round_zero (R := ℝ)).symm]
    exact RModeMono.round_mono hx_nn
  have hhi : RMode.round (R := ℝ) x ≤ Fp.finite FiniteFp.largestFiniteFloat :=
    round_le_largestFiniteFloat x hx_le
  cases hr : RMode.round (R := ℝ) x with
  | finite f => exact ⟨f, rfl⟩
  | infinite b =>
    cases b with
    | true =>
      rw [hr] at hlo
      simp at hlo
    | false =>
      rw [hr] at hhi
      simp at hhi
  | NaN =>
    rw [hr] at hlo
    simp at hlo

/-- For nonpos inputs, `fpExpFinite a` evaluates to some `Fp.finite f`. -/
theorem fpExpFinite_exists_finite (a : FiniteFp)
    (ha : (a.toVal : ℝ) ≤ 0) :
    ∃ f : FiniteFp, fpExpFinite a = Fp.finite f := by
  rw [fpExpFinite_correct]
  apply round_exists_finite_of_nonneg_bounded
  · exact le_of_lt (Real.exp_pos _)
  · calc Real.exp (a.toVal : ℝ) ≤ 1 := exp_le_one_of_nonpos _ ha
      _ ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ) := by
          have h1 := FiniteFp.zpow_max_exp_le_largestFiniteFloat_toVal (R := ℝ)
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ FloatFormat.max_exp := by
            have : (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by simp
            rw [this]
            apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            linarith [FloatFormat.max_exp_pos]
          linarith

theorem fpExpFinite_no_overflow (a : FiniteFp)
    (ha : (a.toVal : ℝ) ≤ 0) :
    fpExpFinite a ≠ Fp.infinite false := by
  rw [fpExpFinite_correct]
  apply round_ne_pos_inf_of_le_largest
  calc Real.exp (a.toVal : ℝ) ≤ 1 := exp_le_one_of_nonpos _ ha
    _ ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ) := by
        have h1 := FiniteFp.zpow_max_exp_le_largestFiniteFloat_toVal (R := ℝ)
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ FloatFormat.max_exp := by
          have : (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by simp
          rw [this]
          apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          linarith [FloatFormat.max_exp_pos]
        linarith

end FPLevel

/-! ## FP Softmax Computation

The definition and properties of the FP softmax algorithm are parameterized by:
1. A family of FP exponentials `exps : Fin n → FiniteFp` (externally computed, typically
   via `fpExpFinite`),
2. A denominator `denom : FiniteFp` (externally summed, typically via an `FpSumBound`).

This separation lets the same algorithm be used with any summation method
(naive, pairwise, Kahan, etc.) and any exp approximation, with error analysis
composing via per-component hypotheses. -/

section FpSoftmax

variable [FloatFormat] [RModeExec]

/-- FP softmax: `fpSoftmaxOf exps denom i = fpDivFinite (exps i) denom`.
Each component is the FP quotient of the `i`-th exp value and the denominator. -/
def fpSoftmaxOf {n : ℕ} (exps : Fin n → FiniteFp) (denom : FiniteFp) : Fin n → Fp :=
  fun i => fpDivFinite (exps i) denom

@[simp] theorem fpSoftmaxOf_apply {n : ℕ} (exps : Fin n → FiniteFp) (denom : FiniteFp) (i : Fin n) :
    fpSoftmaxOf exps denom i = fpDivFinite (exps i) denom := rfl

/-- Plug-in wrapper taking an `FpSumBound` to provide the denominator. -/
def fpSoftmaxFromSum {n : ℕ} (exps : Fin n → FiniteFp)
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (sum : FpSum.FpSumBound exps R) : Fin n → Fp :=
  fpSoftmaxOf exps sum.result

end FpSoftmax

/-! ## No-Overflow Theorems for the FP Softmax Pipeline -/

section NoOverflow

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

omit [ExpApprox] [ExpApproxSound] in
/-- For `denom.m ≠ 0` and the quotient in `[0, largestFiniteFloat.toVal]`,
`fpDivFinite` produces a finite result. -/
theorem fpDivFinite_exists_finite_of_bounded (a b : FiniteFp)
    (hb : b.m ≠ 0)
    (h_nn : 0 ≤ ((a.toVal : ℝ) / b.toVal))
    (h_le : ((a.toVal : ℝ) / b.toVal) ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    ∃ f, fpDivFinite a b = Fp.finite f := by
  by_cases hq : ((a.toVal : ℝ) / b.toVal) = 0
  · -- quot = 0: a.toVal = 0 forces a.m = 0, and fpDivFinite returns signed zero
    have hb_ne : (b.toVal : ℝ) ≠ 0 := FiniteFp.toVal_ne_zero_of_m_pos b (Nat.pos_of_ne_zero hb)
    have ha_zero : (a.toVal : ℝ) = 0 := by
      rcases div_eq_zero_iff.mp hq with h' | h'
      · exact h'
      · exact absurd h' hb_ne
    have ham : a.m = 0 := (FiniteFp.toVal_significand_zero_iff (R := ℝ)).mpr ha_zero
    have hscaled : a.m * 2 ^ divShift = 0 := by simp [ham]
    refine ⟨if a.s ^^ b.s then -0 else 0, ?_⟩
    have hmag : 2 * (a.m * 2 ^ divShift / b.m) + (if a.m * 2 ^ divShift % b.m = 0 then 0 else 1) = 0 := by
      simp [hscaled]
    simp only [fpDivFinite, roundIntSigM, hmag, ↓reduceDIte]
  · -- quot ≠ 0: apply fpDivFinite_correct
    have hcorr : fpDivFinite a b = ○((a.toVal : ℝ) / b.toVal) := by
      have h := fpDivFinite_correct (R := ℝ) a b hb hq
      simp only [div_eq_fpDiv, fpDiv, hb, ↓reduceIte, div_finite_eq_fpDivFinite] at h
      exact h
    rw [hcorr]
    exact round_exists_finite_of_nonneg_bounded _ h_nn h_le

omit [ExpApprox] [ExpApproxSound] in
/-- `fpSoftmaxOf exps denom i` is a finite FP value when the quotient is bounded. -/
theorem fpSoftmaxOf_exists_finite {n : ℕ} (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (hd : denom.m ≠ 0)
    (i : Fin n)
    (h_nn : 0 ≤ (((exps i).toVal : ℝ) / denom.toVal))
    (h_le : (((exps i).toVal : ℝ) / denom.toVal) ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    ∃ f, fpSoftmaxOf exps denom i = Fp.finite f := by
  simp only [fpSoftmaxOf_apply]
  exact fpDivFinite_exists_finite_of_bounded (exps i) denom hd h_nn h_le

end NoOverflow

end Softmax
