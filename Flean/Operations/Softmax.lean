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
/-- **Safe fpAddFinite**: returns `Fp.finite` under nonneg bounded operands. -/
theorem fpAddFinite_exists_finite_of_nonneg_bounded (a b : FiniteFp)
    (h_nn_a : 0 ≤ (a.toVal : ℝ)) (h_nn_b : 0 ≤ (b.toVal : ℝ))
    (h_le : (a.toVal : ℝ) + b.toVal ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    ∃ f, fpAddFinite a b = Fp.finite f := by
  by_cases hzero : ((a.toVal : ℝ) + b.toVal) = 0
  · -- Real sum is 0; both operands have toVal = 0 (they're both nonneg)
    have hav_z : (a.toVal : ℝ) = 0 := le_antisymm (by linarith) h_nn_a
    have hbv_z : (b.toVal : ℝ) = 0 := le_antisymm (by linarith) h_nn_b
    have ham : a.m = 0 := (FiniteFp.toVal_significand_zero_iff (R := ℝ)).mpr hav_z
    have hbm : b.m = 0 := (FiniteFp.toVal_significand_zero_iff (R := ℝ)).mpr hbv_z
    -- With a.m = 0 and b.m = 0, the aligned integer sums are both 0
    refine ⟨⟨exactCancelSign a.s b.s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩, ?_⟩
    simp only [fpAddFinite, ham, hbm, Nat.cast_zero, condNeg]
    -- condNeg s 0 = 0 regardless of s
    have h_condZero : ∀ s : Bool, (if s then -0 else 0 : ℤ) = 0 := by
      intro s; cases s <;> simp
    simp only [h_condZero, zero_mul, add_zero, ↓reduceIte]
  · have hcorr : fpAddFinite a b = ○((a.toVal : ℝ) + b.toVal) := by
      have h := fpAddFinite_correct (R := ℝ) a b hzero
      simp only [add_finite_eq_fpAddFinite] at h
      exact h
    rw [hcorr]
    have hsum_nn : 0 ≤ ((a.toVal : ℝ) + b.toVal) := add_nonneg h_nn_a h_nn_b
    exact round_exists_finite_of_nonneg_bounded _ hsum_nn h_le

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

omit [ExpApprox] [ExpApproxSound] in
/-- **NaiveSum step extension** for bounded nonneg operands.

Given any prior `NaiveSum` trace and a new nonneg element with partial sum bounded
by `largestFiniteFloat`, produces the fpAdd result as a `Fp.finite` — the witness
needed to invoke `NaiveSum.step`. This automates the per-step finiteness proof
when all inputs are nonneg and the partial-sum bound holds. -/
theorem naiveSum_step_finite_of_nonneg_bounded (acc : FiniteFp) (x : FiniteFp)
    (h_nn_acc : 0 ≤ (acc.toVal : ℝ))
    (h_nn_x : 0 ≤ (x.toVal : ℝ))
    (h_le : (acc.toVal : ℝ) + x.toVal ≤ FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    ∃ next : FiniteFp, acc + x = Fp.finite next := by
  obtain ⟨f, hf⟩ := fpAddFinite_exists_finite_of_nonneg_bounded acc x h_nn_acc h_nn_x h_le
  exact ⟨f, hf⟩

/-- Extract FiniteFp exp values automatically from nonpos-shifted FP inputs.

Uses classical choice via `fpExpFinite_exists_finite`. The extracted values satisfy
`fpExpFinite (xs i) = Fp.finite (fpExpsFromXs xs h_nonpos i)` (see `fpExpsFromXs_correct`). -/
noncomputable def fpExpsFromXs {n : ℕ} (xs : Fin n → FiniteFp)
    (h_nonpos : ∀ i, ((xs i).toVal : ℝ) ≤ 0) :
    Fin n → FiniteFp :=
  fun i => Classical.choose (fpExpFinite_exists_finite (xs i) (h_nonpos i))

theorem fpExpsFromXs_correct {n : ℕ} (xs : Fin n → FiniteFp)
    (h_nonpos : ∀ i, ((xs i).toVal : ℝ) ≤ 0) (i : Fin n) :
    fpExpFinite (xs i) = Fp.finite (fpExpsFromXs xs h_nonpos i) :=
  Classical.choose_spec (fpExpFinite_exists_finite (xs i) (h_nonpos i))

/-- Extract FiniteFp result values automatically when softmax outputs are bounded. -/
noncomputable def fpSoftmaxResults {n : ℕ} (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (hd_m : denom.m ≠ 0)
    (h_bounded : ∀ i, 0 ≤ (((exps i).toVal : ℝ) / denom.toVal) ∧
                      (((exps i).toVal : ℝ) / denom.toVal) ≤
                        FiniteFp.largestFiniteFloat.toVal (R := ℝ)) :
    Fin n → FiniteFp :=
  fun i => Classical.choose (fpDivFinite_exists_finite_of_bounded (exps i) denom hd_m
    (h_bounded i).1 (h_bounded i).2)

omit [ExpApprox] [ExpApproxSound] in
theorem fpSoftmaxResults_correct {n : ℕ} (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (hd_m : denom.m ≠ 0)
    (h_bounded : ∀ i, 0 ≤ (((exps i).toVal : ℝ) / denom.toVal) ∧
                      (((exps i).toVal : ℝ) / denom.toVal) ≤
                        FiniteFp.largestFiniteFloat.toVal (R := ℝ)) (i : Fin n) :
    fpDivFinite (exps i) denom = Fp.finite (fpSoftmaxResults exps denom hd_m h_bounded i) :=
  Classical.choose_spec (fpDivFinite_exists_finite_of_bounded (exps i) denom hd_m
    (h_bounded i).1 (h_bounded i).2)

end NoOverflow

/-! ## Componentwise Error Bound

The main error theorem for `fpSoftmaxOf`. Given:
- Correct FP exp values `exps` for normal-range exp inputs,
- A sum bound `εsum` on `|denom.toVal - Σ eb_j| ≤ εsum · Σ|eb_j|`,
- Normal-range quotients,

we bound `|(result i).toVal - softmax xs̄ i| ≤ softmaxErrorCoeff εsum · softmax xs̄ i`,
where `xs̄ j = (xs j).toVal`.

The coefficient is `(η² + 2η + δ) / (1 - δ)` with `δ = η + εsum·(1+η)`, valid when `δ < 1`.
For small `η, εsum` this is approximately `3η + εsum`. -/

section ErrorBound

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

open Finset BigOperators

omit [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [RModeNearest ℝ]
  [ExpApprox] [ExpApproxSound] in
/-- `η < 1` follows from `prec > 0`. -/
theorem hEps_lt_one : (η : ℝ) < 1 := by
  simp only [FloatFormat.hEps_def]
  have hp := FloatFormat.prec_pos
  have hneg : -(FloatFormat.prec : ℤ) < 0 := by omega
  have h1 : (1 : ℝ) < 2 := by norm_num
  -- 2^(negative) < 2^0 = 1
  calc (2 : ℝ) ^ (-(FloatFormat.prec : ℤ))
      < (2 : ℝ) ^ (0 : ℤ) := zpow_lt_zpow_right₀ h1 hneg
    _ = 1 := zpow_zero _

/-- Relative error coefficient for the FP softmax computation.

`softmaxErrorCoeff εsum = (η² + 2η + δ) / (1 - δ)` where `δ = η + εsum · (1+η)`. -/
noncomputable def softmaxErrorCoeff (εsum : ℝ) : ℝ :=
  ((η : ℝ)^2 + 2*(η : ℝ) + ((η : ℝ) + εsum*(1+(η : ℝ)))) /
    (1 - ((η : ℝ) + εsum*(1+(η : ℝ))))

omit [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [RModeNearest ℝ]
  [ExpApprox] [ExpApproxSound] in
/-- Simpler upper bound: `softmaxErrorCoeff εsum ≤ 7η + 3εsum` under `η + 2εsum ≤ 1/2`.

This is looser than the exact `softmaxErrorCoeff` but easier to reason about.
For typical FP (e.g., `η ≈ 10⁻⁷` for binary32) and small-`n` naive sums
(`εsum ≈ nη`), the condition is trivially satisfied and the bound is within
a small constant factor of the tight one. -/
theorem softmaxErrorCoeff_le_linear (εsum : ℝ)
    (h_εsum_nn : 0 ≤ εsum)
    (h_small : (η : ℝ) + 2 * εsum ≤ 1/2) :
    softmaxErrorCoeff εsum ≤ 7 * (η : ℝ) + 3 * εsum := by
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hη_le : (η : ℝ) ≤ 1/2 := by linarith
  set δ : ℝ := (η : ℝ) + εsum * (1 + (η : ℝ)) with hδ_def
  have hδ_nn : 0 ≤ δ := by positivity
  -- δ = η + εsum(1+η) ≤ η + (3/2)εsum ≤ 1/2
  have hδ_le_half : δ ≤ 1/2 := by
    have h1 : εsum * (1 + (η : ℝ)) ≤ εsum * (3/2) :=
      mul_le_mul_of_nonneg_left (by linarith) h_εsum_nn
    have h2 : (η : ℝ) + εsum * (3/2) ≤ 1/2 := by linarith
    linarith
  have h_denom_ge : (1/2 : ℝ) ≤ 1 - δ := by linarith
  have h_denom_pos : 0 < 1 - δ := by linarith
  -- Numerator: η² + 2η + δ
  -- ≤ η·(1/2) + 2η + η + (3/2)εsum = (7/2)η + (3/2)εsum
  have h_num_le : (η : ℝ)^2 + 2*(η : ℝ) + δ ≤ (7/2) * (η : ℝ) + (3/2) * εsum := by
    have hη_sq : (η : ℝ)^2 ≤ (η : ℝ) * (1/2) := by
      have : (η : ℝ)^2 = (η : ℝ) * (η : ℝ) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hη_le hη_nn
    have hεtrunc : εsum * (1 + (η : ℝ)) ≤ (3/2) * εsum := by
      have h1 : εsum * (1 + (η : ℝ)) ≤ εsum * (3/2) :=
        mul_le_mul_of_nonneg_left (by linarith) h_εsum_nn
      linarith
    have : δ ≤ (η : ℝ) + (3/2) * εsum := by linarith
    nlinarith [hη_sq, this]
  have h_num_nn : 0 ≤ (η : ℝ)^2 + 2*(η : ℝ) + δ := by positivity
  -- Divide by (1-δ) ≥ 1/2, so ≤ 2·num ≤ 2·((7/2)η + (3/2)εsum) = 7η + 3εsum
  calc softmaxErrorCoeff εsum
      = ((η : ℝ)^2 + 2*(η : ℝ) + δ) / (1 - δ) := by simp [softmaxErrorCoeff, hδ_def]
    _ ≤ ((η : ℝ)^2 + 2*(η : ℝ) + δ) / (1/2) := by
        apply div_le_div_of_nonneg_left h_num_nn (by norm_num) h_denom_ge
    _ = 2 * ((η : ℝ)^2 + 2*(η : ℝ) + δ) := by ring
    _ ≤ 2 * ((7/2) * (η : ℝ) + (3/2) * εsum) :=
        mul_le_mul_of_nonneg_left h_num_le (by norm_num)
    _ = 7 * (η : ℝ) + 3 * εsum := by ring

/-- Per-component exp error: `|(exps i).toVal - exp(xs_i)| ≤ η · exp(xs_i)`. -/
theorem exps_error_of_correct {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (i : Fin n) :
    |((exps i).toVal : ℝ) - Real.exp ((xs i).toVal : ℝ)| ≤
      (η : ℝ) * Real.exp ((xs i).toVal : ℝ) := by
  have hcorr : fpExpFinite (xs i) = ○(Real.exp ((xs i).toVal : ℝ)) :=
    fpExpFinite_correct (xs i)
  have hfe : ○(Real.exp ((xs i).toVal : ℝ)) = Fp.finite (exps i) := by
    rw [← hcorr]; exact h_exp i
  have h := KahanSum.standard_error_additive (R := ℝ) _ (h_exp_nr i) (exps i) hfe
  have hexp_pos : (0 : ℝ) ≤ Real.exp ((xs i).toVal : ℝ) := le_of_lt (Real.exp_pos _)
  rwa [abs_of_nonneg hexp_pos] at h

/-- Bound on each FP exp value: `(exps i).toVal ≤ (1+η) · exp(xs_i)`. -/
theorem exps_le_of_correct {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (i : Fin n) :
    ((exps i).toVal : ℝ) ≤ (1 + (η : ℝ)) * Real.exp ((xs i).toVal : ℝ) := by
  have h := exps_error_of_correct xs exps h_exp h_exp_nr i
  have := abs_le.mp h
  linarith [this.2]

/-- Lower bound on each FP exp value: `(1-η) · exp(xs_i) ≤ (exps i).toVal`. -/
theorem exps_ge_of_correct {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (i : Fin n) :
    (1 - (η : ℝ)) * Real.exp ((xs i).toVal : ℝ) ≤ ((exps i).toVal : ℝ) := by
  have h := exps_error_of_correct xs exps h_exp h_exp_nr i
  have := abs_le.mp h
  linarith [this.1]

/-- Subnormal unit: `2^(min_exp - prec)` — the absolute rounding error in subnormal range. -/
noncomputable def subnormalConst : ℝ :=
  (2 : ℝ) ^ (FloatFormat.min_exp - FloatFormat.prec)

omit [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [RModeNearest ℝ]
  [ExpApprox] [ExpApproxSound] in
theorem subnormalConst_pos : (0 : ℝ) < subnormalConst := by
  unfold subnormalConst; positivity

omit [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [RModeNearest ℝ]
  [ExpApprox] [ExpApproxSound] in
theorem subnormalConst_nn : (0 : ℝ) ≤ subnormalConst :=
  le_of_lt subnormalConst_pos

omit [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [RModeNearest ℝ]
  [ExpApprox] [ExpApproxSound] in
/-- **Unified ulp bound**: `Fp.ulp v / 2 ≤ η · v + subnormalConst` for positive `v`.

This lets us unify the normal-range (relative error ≤ η·v) and subnormal-range
(absolute error ≤ subnormalConst) bounds into a single expression that always holds. -/
theorem ulp_half_le_unified (v : ℝ) (hv_pos : 0 < v) :
    Fp.ulp v / 2 ≤ (η : ℝ) * v + subnormalConst := by
  unfold Fp.ulp subnormalConst
  simp only [FloatFormat.hEps_def]
  set e : ℤ := max (Int.log 2 |v|) FloatFormat.min_exp with he_def
  -- e ≥ min_exp, so 2^(e - prec) ≥ 2^(min_exp - prec)
  have hv_abs : |v| = v := abs_of_pos hv_pos
  have hη_pos : (0 : ℝ) < (2 : ℝ)^(-(FloatFormat.prec : ℤ)) := by positivity
  have hsub_pos : (0 : ℝ) < (2 : ℝ)^(FloatFormat.min_exp - FloatFormat.prec) := by positivity
  -- (2^(e - prec + 1)) / 2 = 2^(e - prec)
  have halgebra : (2 : ℝ) ^ (e - FloatFormat.prec + 1) / 2 = (2 : ℝ) ^ (e - FloatFormat.prec) := by
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [halgebra]
  -- Case split: subnormal (v < 2^min_exp) or normal (v ≥ 2^min_exp)
  by_cases hnormal : (2 : ℝ) ^ FloatFormat.min_exp ≤ v
  · -- Normal case: e = Int.log 2 v, and 2^e ≤ v, so 2^(e - prec) ≤ v · 2^(-prec)
    have hlog_ge : FloatFormat.min_exp ≤ Int.log 2 |v| := by
      rw [hv_abs]
      exact (Int.zpow_le_iff_le_log (b := 2) (R := ℝ) (by norm_num : (1 : ℕ) < 2) hv_pos).mp
        hnormal
    have he_eq : e = Int.log 2 |v| := by
      rw [he_def]; exact max_eq_left hlog_ge
    rw [he_eq]
    -- 2^(Int.log 2 |v|) ≤ |v| = v
    have hlog_le_v : (2 : ℝ) ^ (Int.log 2 |v|) ≤ v := by
      have h := Int.zpow_log_le_self (R := ℝ) (b := 2) (by norm_num : (1 : ℕ) < 2) hv_pos
      calc (2 : ℝ) ^ (Int.log 2 |v|) = (2 : ℝ) ^ (Int.log 2 v) := by rw [hv_abs]
        _ ≤ v := by exact_mod_cast h
    -- 2^(Int.log 2 |v| - prec) = 2^(Int.log 2 |v|) * 2^(-prec) ≤ v * 2^(-prec)
    have h1 : (2 : ℝ) ^ (Int.log 2 |v| - FloatFormat.prec) =
              (2 : ℝ) ^ (Int.log 2 |v|) * (2 : ℝ) ^ (-(FloatFormat.prec : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring_nf
    rw [h1]
    calc (2 : ℝ) ^ (Int.log 2 |v|) * (2 : ℝ) ^ (-(FloatFormat.prec : ℤ))
        ≤ v * (2 : ℝ) ^ (-(FloatFormat.prec : ℤ)) :=
          mul_le_mul_of_nonneg_right hlog_le_v (le_of_lt hη_pos)
      _ = (2 : ℝ) ^ (-(FloatFormat.prec : ℤ)) * v := by ring
      _ ≤ (2 : ℝ) ^ (-(FloatFormat.prec : ℤ)) * v +
          (2 : ℝ) ^ (FloatFormat.min_exp - FloatFormat.prec) := by linarith
  · -- Subnormal case: v < 2^min_exp
    push_neg at hnormal
    have hlog_lt : Int.log 2 |v| < FloatFormat.min_exp := by
      rw [hv_abs]
      -- Int.log 2 v < min_exp iff v < 2^min_exp (when v ≥ 1)
      -- Hmm, Int.log is tricky for v < 1. Let me use a different argument.
      by_contra h_ge
      push_neg at h_ge
      -- h_ge : min_exp ≤ Int.log 2 v
      have : (2 : ℝ) ^ FloatFormat.min_exp ≤ v := by
        have h1 : (2 : ℝ) ^ (FloatFormat.min_exp : ℤ) ≤ (2 : ℝ) ^ Int.log 2 v :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_ge
        have h2 : (2 : ℝ) ^ Int.log 2 v ≤ v :=
          Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) hv_pos
        linarith
      linarith
    have he_eq : e = FloatFormat.min_exp := by
      rw [he_def]; exact max_eq_right (le_of_lt hlog_lt)
    rw [he_eq]
    -- 2^(min_exp - prec) ≤ 2^(-prec) * v + 2^(min_exp - prec)
    linarith [mul_nonneg (le_of_lt hη_pos) (le_of_lt hv_pos)]

/-- Per-component exp error (subnormal-tolerant form): absolute error ≤ `ulp/2`.

Uses `RModeNearest_abs_error_le_ulp_half_pos`, which holds for any positive exp
output regardless of whether it's in normal or subnormal range. For a full
subnormal-tolerant softmax theorem, this would replace `exps_error_of_correct`
in the main proof, with the sum-error track similarly generalized.

**Quantification**: for typical binary64 (`min_exp = -1022`, `prec = 53`),
the subnormal ulp is `2^(-1074)`, so subnormal exp errors contribute at most
`~10^(-324)` per term — negligible unless `n > 10^308` terms underflow. -/
theorem exps_ulp_error_of_correct {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (i : Fin n) :
    |((exps i).toVal : ℝ) - Real.exp ((xs i).toVal : ℝ)| ≤
      Fp.ulp (Real.exp ((xs i).toVal : ℝ)) / 2 := by
  have hcorr : fpExpFinite (xs i) = ○(Real.exp ((xs i).toVal : ℝ)) :=
    fpExpFinite_correct (xs i)
  have hfe : ○(Real.exp ((xs i).toVal : ℝ)) = Fp.finite (exps i) := by
    rw [← hcorr]; exact h_exp i
  have h := RModeNearest_abs_error_le_ulp_half_pos (R := ℝ) _ (Real.exp_pos _) (exps i) hfe
  rwa [abs_sub_comm]

/-- Per-component unified exp error: `|ē_i - e_i| ≤ η · e_i + subnormalConst`.

Subnormal-tolerant: this always holds whether `e_i` is in normal range (where
`η · e_i` is tight) or subnormal (where `subnormalConst` dominates). -/
theorem exps_unified_error_of_correct {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i)) (i : Fin n) :
    |((exps i).toVal : ℝ) - Real.exp ((xs i).toVal : ℝ)| ≤
      (η : ℝ) * Real.exp ((xs i).toVal : ℝ) + subnormalConst := by
  have h := exps_ulp_error_of_correct xs exps h_exp i
  have hbd := ulp_half_le_unified _ (Real.exp_pos ((xs i).toVal : ℝ))
  linarith

/-- FP exp values are nonneg (subnormal-tolerant: drops the normal-range hypothesis).

Follows from `RModeZero.round_zero + RModeMono.round_mono`: rounding the nonneg
real `exp(x_i)` to nearest gives a nonneg FP. -/
theorem exps_nonneg_unified {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (i : Fin n) :
    0 ≤ ((exps i).toVal : ℝ) := by
  have hcorr : fpExpFinite (xs i) = ○(Real.exp ((xs i).toVal : ℝ)) :=
    fpExpFinite_correct (xs i)
  have hfe : ○(Real.exp ((xs i).toVal : ℝ)) = Fp.finite (exps i) := by
    rw [← hcorr]; exact h_exp i
  have hexp_nn : (0 : ℝ) ≤ Real.exp ((xs i).toVal : ℝ) := le_of_lt (Real.exp_pos _)
  have hzero : RMode.round (R := ℝ) (0 : ℝ) = Fp.finite 0 := RModeZero.round_zero
  have hmono : RMode.round (R := ℝ) (0 : ℝ) ≤
               RMode.round (R := ℝ) (Real.exp ((xs i).toVal : ℝ)) :=
    RModeMono.round_mono hexp_nn
  rw [hzero, hfe] at hmono
  have h_fin_le : (0 : FiniteFp) ≤ exps i := (Fp.finite_le_finite_iff _ _).mp hmono
  have htoVal_le := FiniteFp.le_toVal_le ℝ h_fin_le
  have h_zero_toVal : ((0 : FiniteFp).toVal : ℝ) = 0 := FiniteFp.toVal_isZero rfl
  linarith

/-- Positivity from `m ≠ 0`, subnormal-tolerant form: combines `exps_nonneg_unified`
with the `m = 0 ↔ toVal = 0` equivalence. -/
theorem exps_pos_of_m_ne_zero {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (i : Fin n) (hm : (exps i).m ≠ 0) :
    0 < ((exps i).toVal : ℝ) := by
  have hnn := exps_nonneg_unified xs exps h_exp i
  have hne : ((exps i).toVal : ℝ) ≠ 0 := by
    intro heq
    exact hm ((FiniteFp.toVal_significand_zero_iff (R := ℝ)).mpr heq)
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- FP exp values are nonneg when inputs give normal-range exp outputs. -/
theorem exps_nonneg_of_correct {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (hη : (η : ℝ) < 1)
    (i : Fin n) :
    0 ≤ ((exps i).toVal : ℝ) := by
  have h := exps_ge_of_correct xs exps h_exp h_exp_nr i
  have hexp : 0 < Real.exp ((xs i).toVal : ℝ) := Real.exp_pos _
  have h1 : (0 : ℝ) < 1 - (η : ℝ) := by linarith
  have : (0 : ℝ) ≤ (1 - (η : ℝ)) * Real.exp ((xs i).toVal : ℝ) :=
    mul_nonneg (le_of_lt h1) (le_of_lt hexp)
  linarith

/-- Summed bound: `|Σ (exps j).toVal - Σ exp((xs j).toVal)| ≤ η · Σ exp((xs j).toVal)`. -/
theorem sum_exps_error {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ))) :
    |∑ j, ((exps j).toVal : ℝ) - ∑ j, Real.exp ((xs j).toVal : ℝ)| ≤
      (η : ℝ) * ∑ j, Real.exp ((xs j).toVal : ℝ) := by
  have hperj : ∀ j, |((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ)| ≤
      (η : ℝ) * Real.exp ((xs j).toVal : ℝ) :=
    fun j => exps_error_of_correct xs exps h_exp h_exp_nr j
  have hsum_eq : ∑ j, ((exps j).toVal : ℝ) - ∑ j, Real.exp ((xs j).toVal : ℝ) =
      ∑ j, (((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ)) := by
    rw [Finset.sum_sub_distrib]
  rw [hsum_eq]
  calc |∑ j, (((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ))|
      ≤ ∑ j, |((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (η : ℝ) * Real.exp ((xs j).toVal : ℝ) :=
        Finset.sum_le_sum (fun j _ => hperj j)
    _ = (η : ℝ) * ∑ j, Real.exp ((xs j).toVal : ℝ) :=
        by rw [← Finset.mul_sum]

/-- Sum of FP exp values is positive when inputs yield normal-range exp outputs. -/
theorem sum_exps_pos {n : ℕ} (hn : 0 < n) (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (hη : (η : ℝ) < 1) :
    0 < ∑ j, ((exps j).toVal : ℝ) := by
  -- Use (1-η) Σ exp ≤ Σ exps and (1-η) Σ exp > 0
  have hsum_exp_pos : 0 < ∑ j, Real.exp ((xs j).toVal : ℝ) := by
    apply Finset.sum_pos
    · intros; exact Real.exp_pos _
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hbd := sum_exps_error xs exps h_exp h_exp_nr
  have := abs_le.mp hbd
  have h1 : 0 < 1 - (η : ℝ) := by linarith
  nlinarith [this.1, mul_pos h1 hsum_exp_pos]

/-- Sum of |(exps j).toVal| = Σ (exps j).toVal since they're nonneg. -/
theorem sum_abs_exps_eq_sum {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (hη : (η : ℝ) < 1) :
    ∑ j, |((exps j).toVal : ℝ)| = ∑ j, ((exps j).toVal : ℝ) := by
  apply Finset.sum_congr rfl
  intro j _
  exact abs_of_nonneg (exps_nonneg_of_correct xs exps h_exp h_exp_nr hη j)

/-- **Summed unified exp error** (subnormal-tolerant). -/
theorem sum_exps_unified_error {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i)) :
    |∑ j, ((exps j).toVal : ℝ) - ∑ j, Real.exp ((xs j).toVal : ℝ)| ≤
      (η : ℝ) * ∑ j, Real.exp ((xs j).toVal : ℝ) + (n : ℝ) * subnormalConst := by
  have hperj : ∀ j, |((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ)| ≤
      (η : ℝ) * Real.exp ((xs j).toVal : ℝ) + subnormalConst :=
    fun j => exps_unified_error_of_correct xs exps h_exp j
  have hsum_eq : ∑ j, ((exps j).toVal : ℝ) - ∑ j, Real.exp ((xs j).toVal : ℝ) =
      ∑ j, (((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ)) := by
    rw [Finset.sum_sub_distrib]
  rw [hsum_eq]
  calc |∑ j, (((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ))|
      ≤ ∑ j, |((exps j).toVal : ℝ) - Real.exp ((xs j).toVal : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, ((η : ℝ) * Real.exp ((xs j).toVal : ℝ) + subnormalConst) :=
        Finset.sum_le_sum (fun j _ => hperj j)
    _ = (η : ℝ) * ∑ j, Real.exp ((xs j).toVal : ℝ) + (n : ℝ) * subnormalConst := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Unified denom error** (subnormal-tolerant): combines `εsum · Σ|ē_j|`
(sum FP error) with `η·S + n·subnormalConst` (sum-of-exps error, unified). -/
theorem denom_unified_error {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (denom : FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum) :
    |(denom.toVal : ℝ) - ∑ j, Real.exp ((xs j).toVal : ℝ)| ≤
      ((η : ℝ) + εsum * (1 + (η : ℝ))) * ∑ j, Real.exp ((xs j).toVal : ℝ) +
        (1 + εsum) * (n : ℝ) * subnormalConst := by
  set S : ℝ := ∑ j, Real.exp ((xs j).toVal : ℝ) with hS_def
  set Se : ℝ := ∑ j, ((exps j).toVal : ℝ) with hSe_def
  -- |Σē - S| ≤ η·S + n·subnormalConst
  have hsum_err := sum_exps_unified_error xs exps h_exp
  -- |ē_j| ≤ |e_j| + η·e_j + subnormalConst = (1+η)·e_j + subnormalConst (e_j ≥ 0)
  have habs_bd : ∀ j, |((exps j).toVal : ℝ)| ≤
                      (1 + (η : ℝ)) * Real.exp ((xs j).toVal : ℝ) + subnormalConst := by
    intro j
    have hper := exps_unified_error_of_correct xs exps h_exp j
    have hexp_nn : (0 : ℝ) ≤ Real.exp ((xs j).toVal : ℝ) := le_of_lt (Real.exp_pos _)
    have := abs_sub_abs_le_abs_sub ((exps j).toVal : ℝ) (Real.exp ((xs j).toVal : ℝ))
    have : |((exps j).toVal : ℝ)| ≤ |Real.exp ((xs j).toVal : ℝ)| +
           ((η : ℝ) * Real.exp ((xs j).toVal : ℝ) + subnormalConst) := by
      have h := abs_sub_abs_le_abs_sub ((exps j).toVal : ℝ) (Real.exp ((xs j).toVal : ℝ))
      linarith
    rw [abs_of_nonneg hexp_nn] at this
    linarith
  -- Sum of absolute values ≤ (1+η)·S + n·subnormalConst
  have habs_sum_bd : ∑ j, |((exps j).toVal : ℝ)| ≤
                     (1 + (η : ℝ)) * S + (n : ℝ) * subnormalConst := by
    calc ∑ j, |((exps j).toVal : ℝ)|
        ≤ ∑ j : Fin n, ((1 + (η : ℝ)) * Real.exp ((xs j).toVal : ℝ) + subnormalConst) :=
          Finset.sum_le_sum (fun j _ => habs_bd j)
      _ = (1 + (η : ℝ)) * S + (n : ℝ) * subnormalConst := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS_def]
  have hSe_to_S : |Se - S| ≤ (η : ℝ) * S + (n : ℝ) * subnormalConst := by
    simp only [hSe_def, hS_def]
    exact hsum_err
  -- Triangle: |denom - S| ≤ |denom - Σē| + |Σē - S|
  --         ≤ εsum · (Σ|ē|) + η·S + n·subnormalConst
  --         ≤ εsum · ((1+η)S + n·sc) + η·S + n·sc
  --         = (η + εsum(1+η)) · S + (1+εsum) · n · sc
  have hn_sc_nn : 0 ≤ (n : ℝ) * subnormalConst :=
    mul_nonneg (Nat.cast_nonneg _) subnormalConst_nn
  calc |(denom.toVal : ℝ) - S|
      = |((denom.toVal : ℝ) - Se) + (Se - S)| := by ring_nf
    _ ≤ |(denom.toVal : ℝ) - Se| + |Se - S| := abs_add_le _ _
    _ ≤ εsum * ∑ j, |((exps j).toVal : ℝ)| + ((η : ℝ) * S + (n : ℝ) * subnormalConst) := by
        linarith [h_denom_close, hSe_to_S]
    _ ≤ εsum * ((1 + (η : ℝ)) * S + (n : ℝ) * subnormalConst) +
          ((η : ℝ) * S + (n : ℝ) * subnormalConst) := by
        have : εsum * ∑ j, |((exps j).toVal : ℝ)| ≤
               εsum * ((1 + (η : ℝ)) * S + (n : ℝ) * subnormalConst) := by
          apply mul_le_mul_of_nonneg_left habs_sum_bd h_εsum_nn
        linarith
    _ = ((η : ℝ) + εsum * (1 + (η : ℝ))) * S + (1 + εsum) * (n : ℝ) * subnormalConst := by ring

/-- Denominator total error: `|denom.toVal - Σ exp((xs j).toVal)| ≤ (η + εsum(1+η)) · Σ exp(...)`. -/
theorem denom_error_of_correct {n : ℕ} (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (denom : FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (hη : (η : ℝ) < 1) :
    |(denom.toVal : ℝ) - ∑ j, Real.exp ((xs j).toVal : ℝ)| ≤
      ((η : ℝ) + εsum * (1 + (η : ℝ))) * ∑ j, Real.exp ((xs j).toVal : ℝ) := by
  set S : ℝ := ∑ j, Real.exp ((xs j).toVal : ℝ) with hS_def
  set Seb : ℝ := ∑ j, ((exps j).toVal : ℝ) with hSeb_def
  -- Σ|eb_j| = Σ eb_j since nonneg
  have habs_eq : ∑ j, |((exps j).toVal : ℝ)| = Seb :=
    sum_abs_exps_eq_sum xs exps h_exp h_exp_nr hη
  rw [habs_eq] at h_denom_close
  -- |Seb - S| ≤ η·S
  have hsum_err := sum_exps_error xs exps h_exp h_exp_nr
  -- Seb ≤ (1+η)·S
  have hsum_le : Seb ≤ (1 + (η : ℝ)) * S := by
    have hbd := abs_le.mp hsum_err
    linarith [hbd.2]
  -- Triangle: |denom - S| ≤ |denom - Seb| + |Seb - S| ≤ εsum·Seb + η·S
  --                      ≤ εsum·(1+η)S + η·S = (η + εsum(1+η))·S
  calc |(denom.toVal : ℝ) - S|
      = |((denom.toVal : ℝ) - Seb) + (Seb - S)| := by ring_nf
    _ ≤ |(denom.toVal : ℝ) - Seb| + |Seb - S| := abs_add_le _ _
    _ ≤ εsum * Seb + (η : ℝ) * S := by
        have : |Seb - S| = |∑ j, ((exps j).toVal : ℝ) - ∑ j, Real.exp ((xs j).toVal : ℝ)| := by
          simp [hSeb_def, hS_def]
        rw [this]
        linarith [h_denom_close, hsum_err]
    _ ≤ εsum * ((1 + (η : ℝ)) * S) + (η : ℝ) * S := by
        have : εsum * Seb ≤ εsum * ((1 + (η : ℝ)) * S) := by
          apply mul_le_mul_of_nonneg_left hsum_le h_εsum_nn
        linarith
    _ = ((η : ℝ) + εsum * (1 + (η : ℝ))) * S := by ring

/-- Denom is positive when the combined error `δ = η + εsum(1+η) < 1` and n ≥ 1. -/
theorem denom_pos_of_correct {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_δ_lt : (η : ℝ) + εsum * (1 + (η : ℝ)) < 1) :
    0 < (denom.toVal : ℝ) := by
  have hη_lt : (η : ℝ) < 1 := hEps_lt_one
  have hS_pos : 0 < ∑ j, Real.exp ((xs j).toVal : ℝ) := by
    apply Finset.sum_pos
    · intros; exact Real.exp_pos _
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hbd := denom_error_of_correct xs exps denom εsum h_exp h_exp_nr h_denom_close h_εsum_nn hη_lt
  have := abs_le.mp hbd
  set δ : ℝ := (η : ℝ) + εsum * (1 + (η : ℝ)) with hδ_def
  have h1mδ : 0 < 1 - δ := by linarith
  -- denom.toVal ≥ (1 - δ) · S > 0
  have : (1 - δ) * ∑ j, Real.exp ((xs j).toVal : ℝ) ≤ (denom.toVal : ℝ) := by
    have hlo := this.1
    linarith
  have : 0 < (1 - δ) * ∑ j, Real.exp ((xs j).toVal : ℝ) := mul_pos h1mδ hS_pos
  linarith

/-- **Main theorem: FP softmax componentwise error bound.**

Given:
- `xs`, `exps`, `denom`, `result` satisfy the FP pipeline equations
  (`h_exp` and `h_result`),
- each exp output is in normal range (`h_exp_nr`),
- denom approximates `Σ exps` with relative error `εsum`,
- each quotient `(exps i).toVal / denom.toVal` is in normal range,
- combined error `δ = η + εsum(1+η) < 1`,
- at least one input (`hn : 0 < n`),

then:
`|(result i).toVal - softmax i| ≤ softmaxErrorCoeff εsum · softmax i`

where `softmaxErrorCoeff εsum = (η² + 2η + δ) / (1 - δ)`. -/
theorem fpSoftmaxOf_error_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_δ_lt : (η : ℝ) + εsum * (1 + (η : ℝ)) < 1)
    (hd_m : denom.m ≠ 0)
    (h_quot_nr : ∀ i, isNormalRange (((exps i).toVal : ℝ) / denom.toVal))
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i := by
  -- Shorthand
  set e : Fin n → ℝ := fun j => Real.exp ((xs j).toVal : ℝ) with he_def
  set eb : Fin n → ℝ := fun j => ((exps j).toVal : ℝ) with heb_def
  set S : ℝ := ∑ j, e j with hS_def
  set Sb : ℝ := (denom.toVal : ℝ) with hSb_def
  set sig : Fin n → ℝ := fun j => e j / S with hsig_def
  set q : ℝ := ((result i).toVal : ℝ) with hq_def
  set δ : ℝ := (η : ℝ) + εsum * (1 + (η : ℝ)) with hδ_def
  -- Basic facts
  have hη_lt : (η : ℝ) < 1 := hEps_lt_one
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have h1mδ : 0 < 1 - δ := by linarith
  have h1mη : 0 < 1 - (η : ℝ) := by linarith
  have he_pos : ∀ j, 0 < e j := fun j => Real.exp_pos _
  have he_nn : ∀ j, 0 ≤ e j := fun j => le_of_lt (he_pos j)
  have hS_pos : 0 < S := by
    apply Finset.sum_pos
    · intros; exact he_pos _
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hSb_pos : 0 < Sb := denom_pos_of_correct hn xs exps denom εsum h_exp h_exp_nr
    h_denom_close h_εsum_nn h_δ_lt
  -- Bounds on eb_j and Σeb_j
  have heb_bd : ∀ j, |eb j - e j| ≤ (η : ℝ) * e j := by
    intro j; exact exps_error_of_correct xs exps h_exp h_exp_nr j
  have heb_le : ∀ j, eb j ≤ (1 + (η : ℝ)) * e j := by
    intro j; exact exps_le_of_correct xs exps h_exp h_exp_nr j
  have heb_nn : ∀ j, 0 ≤ eb j := by
    intro j; exact exps_nonneg_of_correct xs exps h_exp h_exp_nr hη_lt j
  -- Denom error
  have hdenom_err : |Sb - S| ≤ δ * S :=
    denom_error_of_correct xs exps denom εsum h_exp h_exp_nr h_denom_close h_εsum_nn hη_lt
  -- Sb bounds
  have hSb_ge : (1 - δ) * S ≤ Sb := by
    have := abs_le.mp hdenom_err
    linarith
  -- Softmax of i
  have hsigi_eq : softmax (fun j => ((xs j).toVal : ℝ)) i = sig i := by
    simp [softmax, softmaxDenom, hsig_def, he_def, hS_def]
  have hsigi_pos : 0 < sig i := div_pos (he_pos i) hS_pos
  have hsigi_nn : 0 ≤ sig i := le_of_lt hsigi_pos
  -- result i = ○(eb i / Sb)
  have hei_nn : 0 ≤ eb i / Sb := div_nonneg (heb_nn i) (le_of_lt hSb_pos)
  have h_fpDiv : fpDivFinite (exps i) denom = Fp.finite (result i) := h_result i
  have h_fpDiv_eq : fpDivFinite (exps i) denom = ○(eb i / Sb) := by
    have hq_ne : (eb i / Sb : ℝ) ≠ 0 := ne_of_gt (isNormalRange_pos _ (h_quot_nr i))
    have h := fpDivFinite_correct (R := ℝ) (exps i) denom hd_m hq_ne
    simp only [div_eq_fpDiv, fpDiv, hd_m, ↓reduceIte, div_finite_eq_fpDivFinite] at h
    exact h
  have h_round_eq : ○(eb i / Sb) = Fp.finite (result i) := h_fpDiv_eq ▸ h_fpDiv
  -- Division error bound
  have hq_err : |q - eb i / Sb| ≤ (η : ℝ) * (eb i / Sb) := by
    have h := KahanSum.standard_error_additive (R := ℝ) _ (h_quot_nr i) (result i) h_round_eq
    have habs : |eb i / Sb| = eb i / Sb := abs_of_nonneg hei_nn
    rwa [habs] at h
  -- Numerator/denom bounds
  have h1η_nn : (0 : ℝ) ≤ 1 + (η : ℝ) := by linarith
  have h1δS_pos : 0 < (1 - δ) * S := mul_pos h1mδ hS_pos
  -- Facts about sig
  have hsig_i : sig i = e i / S := by simp [hsig_def]
  have hSsig : S * sig i = e i := by
    rw [hsig_i]; field_simp
  -- First: eb i / Sb ≤ (1+η)·e i / ((1-δ)·S) = (1+η)/(1-δ) · sig i
  have hei_le : eb i / Sb ≤ (1 + (η : ℝ)) / (1 - δ) * sig i := by
    have h1 : eb i / Sb ≤ (1 + (η : ℝ)) * e i / ((1 - δ) * S) := by
      rw [div_le_div_iff₀ hSb_pos h1δS_pos]
      nlinarith [heb_le i, hSb_ge, heb_nn i, he_nn i, mul_nonneg h1η_nn (he_nn i)]
    have h2 : (1 + (η : ℝ)) * e i / ((1 - δ) * S) = (1 + (η : ℝ)) / (1 - δ) * sig i := by
      rw [hsig_i]
      field_simp
    linarith
  -- Division error: |q - eb i/Sb| ≤ η · (eb i/Sb) ≤ η · ((1+η)/(1-δ) · sig i)
  have hq_div_err : |q - eb i / Sb| ≤ (η : ℝ) * ((1 + (η : ℝ)) / (1 - δ) * sig i) := by
    calc |q - eb i / Sb| ≤ (η : ℝ) * (eb i / Sb) := hq_err
      _ ≤ (η : ℝ) * ((1 + (η : ℝ)) / (1 - δ) * sig i) :=
          mul_le_mul_of_nonneg_left hei_le hη_nn
  -- Second: |eb i/Sb - sig i| ≤ (η+δ)/(1-δ) · sig i
  -- eb i·S - e i·Sb decomposed
  have h_num_decomp : eb i * S - e i * Sb = (eb i - e i) * S - e i * (Sb - S) := by ring
  have h_num_bd : |eb i * S - e i * Sb| ≤ ((η : ℝ) + δ) * (e i * S) := by
    have h1 : |eb i - e i| ≤ (η : ℝ) * e i := heb_bd i
    have h2 : |Sb - S| ≤ δ * S := hdenom_err
    have heS_nn : 0 ≤ e i * S := mul_nonneg (he_nn i) (le_of_lt hS_pos)
    have : |(eb i - e i) * S - e i * (Sb - S)| ≤ |(eb i - e i) * S| + |e i * (Sb - S)| := by
      have := abs_sub (((eb i - e i)) * S) (e i * (Sb - S))
      linarith [abs_sub ((eb i - e i) * S) (e i * (Sb - S)),
                abs_add_le ((eb i - e i) * S) (-(e i * (Sb - S)))]
    calc |eb i * S - e i * Sb|
        = |(eb i - e i) * S - e i * (Sb - S)| := by rw [h_num_decomp]
      _ ≤ |(eb i - e i) * S| + |e i * (Sb - S)| := this
      _ = |eb i - e i| * S + e i * |Sb - S| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hS_pos), abs_of_nonneg (he_nn i)]
      _ ≤ (η : ℝ) * e i * S + e i * (δ * S) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right h1 (le_of_lt hS_pos)
          · exact mul_le_mul_of_nonneg_left h2 (he_nn i)
      _ = ((η : ℝ) + δ) * (e i * S) := by ring
  -- |eb i / Sb - sig i| = |eb i · S - e i · Sb| / (Sb · S)
  have h_diff_eq : eb i / Sb - sig i = (eb i * S - e i * Sb) / (Sb * S) := by
    simp [hsig_def]
    field_simp [ne_of_gt hS_pos, ne_of_gt hSb_pos]
  have h_ratio_bd : |eb i / Sb - sig i| ≤ ((η : ℝ) + δ) / (1 - δ) * sig i := by
    rw [h_diff_eq, abs_div, abs_of_pos (mul_pos hSb_pos hS_pos)]
    rw [show (Sb * S : ℝ) = Sb * S from rfl]
    -- |num| ≤ (η+δ)(e i S), denom = Sb S ≥ (1-δ) S · S > 0
    have hbd := h_num_bd
    have hden_ge : (1 - δ) * S * S ≤ Sb * S :=
      mul_le_mul_of_nonneg_right hSb_ge (le_of_lt hS_pos)
    have h1δSS_pos : 0 < (1 - δ) * S * S := by positivity
    calc |eb i * S - e i * Sb| / (Sb * S)
        ≤ ((η : ℝ) + δ) * (e i * S) / (Sb * S) := by
          apply div_le_div_of_nonneg_right hbd
          positivity
      _ ≤ ((η : ℝ) + δ) * (e i * S) / ((1 - δ) * S * S) := by
          apply div_le_div_of_nonneg_left _ h1δSS_pos hden_ge
          positivity
      _ = ((η : ℝ) + δ) / (1 - δ) * sig i := by
          rw [hsig_i]
          field_simp
  -- Combine
  have h_total : |q - sig i| ≤
      (η : ℝ) * ((1 + (η : ℝ)) / (1 - δ) * sig i) + ((η : ℝ) + δ) / (1 - δ) * sig i := by
    calc |q - sig i| = |(q - eb i / Sb) + (eb i / Sb - sig i)| := by ring_nf
      _ ≤ |q - eb i / Sb| + |eb i / Sb - sig i| := abs_add_le _ _
      _ ≤ (η : ℝ) * ((1 + (η : ℝ)) / (1 - δ) * sig i) + ((η : ℝ) + δ) / (1 - δ) * sig i :=
          add_le_add hq_div_err h_ratio_bd
  -- Simplify the RHS
  rw [hsigi_eq]
  show |q - sig i| ≤ softmaxErrorCoeff εsum * sig i
  have h_simplify :
      (η : ℝ) * ((1 + (η : ℝ)) / (1 - δ) * sig i) + ((η : ℝ) + δ) / (1 - δ) * sig i =
      softmaxErrorCoeff εsum * sig i := by
    simp only [softmaxErrorCoeff, hδ_def]
    field_simp
    ring
  linarith

/-- **FpSumBound-taking wrapper**: the main error bound phrased in terms of a
packed `FpSumBound` for the denominator computation. This is the user-facing
form — pass any FP summation adapter producing a `FpSumBound` and get the
full softmax error. -/
theorem fpSoftmaxOf_error_bound_of_sumBound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (sum : FpSum.FpSumBound exps ℝ)
    (result : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (h_δ_lt : (η : ℝ) + sum.relErr * (1 + (η : ℝ)) < 1)
    (hd_m : sum.result.m ≠ 0)
    (h_quot_nr : ∀ i, isNormalRange (((exps i).toVal : ℝ) / sum.result.toVal))
    (h_result : ∀ i, fpDivFinite (exps i) sum.result = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff sum.relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i :=
  fpSoftmaxOf_error_bound hn xs exps sum.result result sum.relErr
    h_exp h_exp_nr sum.h_bound sum.h_relErr_nn h_δ_lt hd_m h_quot_nr h_result i

/-- If `fpDivFinite a b = Fp.finite f` and `a.m = 0`, then `f.toVal = 0`.

When the numerator has significand zero, `fpDivFinite` short-circuits to a
signed zero float (via `roundIntSigM` with `mag = 0`). Both signed zeros have
`.m = 0`, so `f.toVal = 0`. -/
private lemma fpDivFinite_toVal_zero_of_num_m_zero
    (a b : FiniteFp) (ha : a.m = 0) (f : FiniteFp)
    (hf : fpDivFinite a b = Fp.finite f) : (f.toVal : ℝ) = 0 := by
  have hscaled : a.m * 2 ^ divShift = 0 := by simp [ha]
  simp only [fpDivFinite, hscaled, Nat.zero_div, Nat.zero_mod,
             roundIntSigM] at hf
  have hfm : f.m = 0 := by
    rcases Bool.eq_false_or_eq_true (a.s ^^ b.s) with hs | hs <;>
      simp only [hs, ↓reduceIte] at hf <;>
      cases (Fp.finite.inj hf) <;> rfl
  exact FiniteFp.toVal_significand_zero_iff.mp hfm

/-- Additive coefficient for the (factor-of-2) subnormal-tolerant softmax error bound.

Multiplied by `subnormalConst`, this captures the additive terms that do not
scale with `σ_i`. For typical binary64 (`subnormalConst ≈ 2^(-1075) ≈ 10^(-324)`),
the resulting additive error is astronomically negligible in practice even with
large `n`. -/
noncomputable def subnormalSoftmaxAbs {n : ℕ} (xs : Fin n → FiniteFp) (εsum : ℝ) : ℝ :=
  1 + 2 * (1 + (η : ℝ) + (1 + εsum) * (n : ℝ)) /
    ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
     ∑ j, Real.exp ((xs j).toVal : ℝ))

/-- Effective denominator margin `m := (1-δ)·S - N·sc` used in the tight bound.

Positivity of this quantity (`h_S_margin_tight`) is the minimal hypothesis
needed to ensure the FP denominator is strictly positive. -/
noncomputable def subnormalSoftmaxDenomMargin {n : ℕ} (xs : Fin n → FiniteFp)
    (εsum : ℝ) : ℝ :=
  (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
    (∑ j, Real.exp ((xs j).toVal : ℝ)) -
  (1 + εsum) * (n : ℝ) * subnormalConst

/-- Tight multiplicative coefficient: `((η² + 2η + δ)·S + N·sc) / m`.

When subnormal contributions vanish (`N·sc → 0`), this reduces to
`softmaxErrorCoeff εsum` — no factor-of-2 looseness. -/
noncomputable def softmaxErrorCoeff_tight {n : ℕ} (xs : Fin n → FiniteFp) (εsum : ℝ) : ℝ :=
  (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
     (∑ j, Real.exp ((xs j).toVal : ℝ)) +
   (1 + εsum) * (n : ℝ) * subnormalConst) /
  subnormalSoftmaxDenomMargin xs εsum

/-- Tight additive coefficient: `1 + (1+η)/m`. -/
noncomputable def subnormalSoftmaxAbs_tight {n : ℕ} (xs : Fin n → FiniteFp) (εsum : ℝ) : ℝ :=
  1 + (1 + (η : ℝ)) / subnormalSoftmaxDenomMargin xs εsum

set_option maxHeartbeats 800000 in
/-- **Core per-component subnormal-tolerant softmax bound**, parametrized over an
abstract lower bound `m` on the FP denominator.

Specializations with different `m` yield the tight (`m := (1-δ)·S - N·sc`) and
factor-of-2 (`m := (1-δ)·S/2`) variants as thin corollaries. The conclusion is
always in the tight form; callers can further relax it via `σ_i ≤ 1` if desired. -/
private theorem fpSoftmax_apply_core_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (m : ℝ) (h_m_pos : 0 < m)
    (h_m_le_margin : m ≤ (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
                         (∑ j, Real.exp ((xs j).toVal : ℝ)) -
                         (1 + εsum) * (n : ℝ) * subnormalConst)
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
         (∑ j, Real.exp ((xs j).toVal : ℝ)) +
       (1 + εsum) * (n : ℝ) * subnormalConst) / m *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      ((1 + (η : ℝ)) / m + 1) * subnormalConst := by
  -- Shorthand
  set S : ℝ := ∑ j, Real.exp ((xs j).toVal : ℝ) with hS_def
  set Sb : ℝ := (denom.toVal : ℝ) with hSb_def
  set q : ℝ := ((result i).toVal : ℝ) with hq_def
  set δ : ℝ := (η : ℝ) + εsum * (1 + (η : ℝ)) with hδ_def
  set ei : ℝ := Real.exp ((xs i).toVal : ℝ) with hei_def
  set ebi : ℝ := ((exps i).toVal : ℝ) with hebi_def
  set Nsc : ℝ := (1 + εsum) * (n : ℝ) * subnormalConst with hNsc_def
  set σi : ℝ := ei / S with hσi_def
  -- Basic facts
  have hη_lt : (η : ℝ) < 1 := hEps_lt_one
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hsc_nn : 0 ≤ subnormalConst := subnormalConst_nn
  have hsc_pos : 0 < subnormalConst := subnormalConst_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have h1ε_pos : (0 : ℝ) < 1 + εsum := by linarith
  have hNsc_nn : 0 ≤ Nsc := by show 0 ≤ (1 + εsum) * (n : ℝ) * subnormalConst; positivity
  have he_pos : ∀ j, 0 < Real.exp ((xs j).toVal : ℝ) := fun j => Real.exp_pos _
  have he_nn : ∀ j, 0 ≤ Real.exp ((xs j).toVal : ℝ) := fun j => le_of_lt (Real.exp_pos _)
  have hei_pos : 0 < ei := he_pos i
  have hei_nn : 0 ≤ ei := he_nn i
  have hS_pos : 0 < S := by
    show 0 < ∑ j, Real.exp ((xs j).toVal : ℝ)
    exact Finset.sum_pos (fun j _ => he_pos j)
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
  have hS_nn : 0 ≤ S := le_of_lt hS_pos
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt h_m_pos
  -- Fold h_m_le_margin in terms of δ, Nsc
  have hm_le_margin : m ≤ (1 - δ) * S - Nsc := h_m_le_margin
  -- Derive 1 - δ > 0 from m > 0 and the margin hypothesis
  have h1mδ_pos : 0 < 1 - δ := by
    by_contra h
    push_neg at h
    have hle : (1 - δ) * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hS_nn
    linarith [hm_le_margin, h_m_pos, hNsc_nn]
  have hδ_nn : 0 ≤ δ := by
    show (0 : ℝ) ≤ (η : ℝ) + εsum * (1 + (η : ℝ)); positivity
  have hδ_ge_η : (η : ℝ) ≤ δ := by
    show (η : ℝ) ≤ (η : ℝ) + εsum * (1 + (η : ℝ))
    have : 0 ≤ εsum * (1 + (η : ℝ)) := mul_nonneg h_εsum_nn (by linarith)
    linarith
  have hm_le_1δS : m ≤ (1 - δ) * S := by linarith
  -- Exp error (unified)
  have heb_err_i : |ebi - ei| ≤ (η : ℝ) * ei + subnormalConst :=
    exps_unified_error_of_correct xs exps h_exp i
  have hebi_nn : 0 ≤ ebi := exps_nonneg_unified xs exps h_exp i
  have hdenom_err : |Sb - S| ≤ δ * S + Nsc :=
    denom_unified_error xs exps denom εsum h_exp h_denom_close h_εsum_nn
  have hSb_lo : (1 - δ) * S - Nsc ≤ Sb := by
    have := (abs_le.mp hdenom_err).1; linarith
  have hSb_ge_m : m ≤ Sb := le_trans hm_le_margin hSb_lo
  have hSb_pos : 0 < Sb := lt_of_lt_of_le h_m_pos hSb_ge_m
  have hSb_ne : (Sb : ℝ) ≠ 0 := ne_of_gt hSb_pos
  have hebi_le : ebi ≤ (1 + (η : ℝ)) * ei + subnormalConst := by
    have := (abs_le.mp heb_err_i).2; linarith
  -- Softmax of i
  have hsigi_eq : softmax (fun j => ((xs j).toVal : ℝ)) i = σi := by
    show Real.exp ((xs i).toVal : ℝ) / softmaxDenom _ = ei / S
    simp [softmaxDenom, hS_def, hei_def]
  have hσi_pos : 0 < σi := div_pos hei_pos hS_pos
  have hσi_nn : 0 ≤ σi := le_of_lt hσi_pos
  rw [hsigi_eq]
  -- Case split on (exps i).m = 0
  by_cases h_mi : (exps i).m = 0
  · -- Underflow case: ebi = 0, q = 0
    have h_ebi_zero : ebi = 0 := by
      show ((exps i).toVal : ℝ) = 0
      exact (FiniteFp.toVal_significand_zero_iff (R := ℝ)).mp h_mi
    have h_q_zero : q = 0 := by
      show ((result i).toVal : ℝ) = 0
      exact fpDivFinite_toVal_zero_of_num_m_zero (exps i) denom h_mi (result i) (h_result i)
    have h1mη_pos : 0 < 1 - (η : ℝ) := by linarith
    have hei_bd : ei ≤ subnormalConst / (1 - (η : ℝ)) := by
      have hr : |ebi - ei| ≤ (η : ℝ) * ei + subnormalConst := heb_err_i
      rw [h_ebi_zero, zero_sub, abs_neg] at hr
      rw [abs_of_pos hei_pos] at hr
      rw [le_div_iff₀ h1mη_pos]; linarith
    have hei_bd' : ei * (1 - (η : ℝ)) ≤ subnormalConst :=
      (le_div_iff₀ h1mη_pos).mp hei_bd
    have hσi_bd : σi ≤ subnormalConst / ((1 - (η : ℝ)) * S) := by
      show ei / S ≤ subnormalConst / ((1 - (η : ℝ)) * S)
      rw [div_le_div_iff₀ hS_pos (mul_pos h1mη_pos hS_pos)]
      nlinarith [hei_bd', hS_nn, h1mη_pos, hei_nn]
    -- Bound: 1/((1-η)·S) ≤ (1+η)/m via m ≤ (1-η²)·S
    have h1mδ_le_1mη : (1 - δ) ≤ (1 - (η : ℝ)) := by linarith
    have h_m_le_1ηS : m ≤ (1 - (η : ℝ)) * S := by
      have : (1 - δ) * S ≤ (1 - (η : ℝ)) * S :=
        mul_le_mul_of_nonneg_right h1mδ_le_1mη hS_nn
      linarith
    have h_ratio_bd : (1 : ℝ) / ((1 - (η : ℝ)) * S) ≤ (1 + (η : ℝ)) / m := by
      rw [div_le_div_iff₀ (mul_pos h1mη_pos hS_pos) h_m_pos]
      nlinarith [h_m_le_1ηS, hη_nn, hS_nn]
    have h_SSAt_bd : subnormalConst / ((1 - (η : ℝ)) * S) ≤
                     ((1 + (η : ℝ)) / m + 1) * subnormalConst := by
      have h1 : subnormalConst / ((1 - (η : ℝ)) * S) =
                1 / ((1 - (η : ℝ)) * S) * subnormalConst := by ring
      have h2 : 1 / ((1 - (η : ℝ)) * S) * subnormalConst ≤
                (1 + (η : ℝ)) / m * subnormalConst :=
        mul_le_mul_of_nonneg_right h_ratio_bd hsc_nn
      have h3 : (1 + (η : ℝ)) / m * subnormalConst ≤
                ((1 + (η : ℝ)) / m + 1) * subnormalConst := by
        have : (1 + (η : ℝ)) / m ≤ (1 + (η : ℝ)) / m + 1 := by linarith
        exact mul_le_mul_of_nonneg_right this hsc_nn
      linarith
    have h_mult_nn :
        0 ≤ (((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S + Nsc) / m * σi := by
      apply mul_nonneg _ hσi_nn
      apply div_nonneg _ (le_of_lt h_m_pos)
      have : 0 ≤ (η : ℝ)^2 + 2 * (η : ℝ) + δ := by positivity
      have : 0 ≤ ((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S := mul_nonneg this hS_nn
      linarith
    calc |q - σi|
        = |(-σi : ℝ)| := by rw [h_q_zero, zero_sub]
      _ = σi := by rw [abs_neg]; exact abs_of_nonneg hσi_nn
      _ ≤ subnormalConst / ((1 - (η : ℝ)) * S) := hσi_bd
      _ ≤ ((1 + (η : ℝ)) / m + 1) * subnormalConst := h_SSAt_bd
      _ ≤ (((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S + Nsc) / m * σi +
          ((1 + (η : ℝ)) / m + 1) * subnormalConst := by linarith
  · -- Non-underflow case: 0 < ebi
    have hebi_pos : 0 < ebi := exps_pos_of_m_ne_zero xs exps h_exp i h_mi
    have hei_Sb_pos : 0 < ebi / Sb := div_pos hebi_pos hSb_pos
    have hei_Sb_ne : ebi / Sb ≠ 0 := ne_of_gt hei_Sb_pos
    have h_fpDiv_eq : fpDivFinite (exps i) denom = ○(ebi / Sb) := by
      have h := fpDivFinite_correct (R := ℝ) (exps i) denom hd_m hei_Sb_ne
      simp only [div_eq_fpDiv, fpDiv, hd_m, ↓reduceIte, div_finite_eq_fpDivFinite] at h
      exact h
    have h_round_eq : ○(ebi / Sb) = Fp.finite (result i) := by
      rw [← h_fpDiv_eq]; exact h_result i
    have hq_err : |q - ebi / Sb| ≤ (η : ℝ) * (ebi / Sb) + subnormalConst := by
      have h := RModeNearest_abs_error_le_ulp_half_pos (R := ℝ) _ hei_Sb_pos (result i) h_round_eq
      rw [abs_sub_comm] at h
      have hbd := ulp_half_le_unified (ebi / Sb) hei_Sb_pos
      linarith
    have hebi_Sb_bd : ebi / Sb ≤ ((1 + (η : ℝ)) * ei + subnormalConst) / m := by
      have h1 : ebi ≤ (1 + (η : ℝ)) * ei + subnormalConst := hebi_le
      have hnum_nn : (0 : ℝ) ≤ (1 + (η : ℝ)) * ei + subnormalConst := by positivity
      calc ebi / Sb
          ≤ ((1 + (η : ℝ)) * ei + subnormalConst) / Sb :=
            div_le_div_of_nonneg_right h1 (le_of_lt hSb_pos)
        _ ≤ ((1 + (η : ℝ)) * ei + subnormalConst) / m :=
            div_le_div_of_nonneg_left hnum_nn h_m_pos hSb_ge_m
    have h_div_err_bd : |q - ebi / Sb| ≤
        (η : ℝ) * (1 + (η : ℝ)) * ei / m + (η : ℝ) * subnormalConst / m + subnormalConst := by
      have step1 : (η : ℝ) * (ebi / Sb) ≤
          (η : ℝ) * (((1 + (η : ℝ)) * ei + subnormalConst) / m) :=
        mul_le_mul_of_nonneg_left hebi_Sb_bd hη_nn
      have step2 : (η : ℝ) * (((1 + (η : ℝ)) * ei + subnormalConst) / m) =
                   (η : ℝ) * (1 + (η : ℝ)) * ei / m + (η : ℝ) * subnormalConst / m := by
        field_simp
      linarith [hq_err]
    have h_num_decomp : ebi * S - ei * Sb = (ebi - ei) * S - ei * (Sb - S) := by ring
    have h_num_bd : |ebi * S - ei * Sb| ≤
        ((η : ℝ) + δ) * (ei * S) + subnormalConst * S + ei * Nsc := by
      have h1 := heb_err_i
      have h2 := hdenom_err
      have hS_abs : |S| = S := abs_of_pos hS_pos
      have he_abs : |ei| = ei := abs_of_pos hei_pos
      calc |ebi * S - ei * Sb|
          = |(ebi - ei) * S - ei * (Sb - S)| := by rw [h_num_decomp]
        _ = |(ebi - ei) * S + (-(ei * (Sb - S)))| := by ring_nf
        _ ≤ |(ebi - ei) * S| + |(-(ei * (Sb - S)))| := abs_add_le _ _
        _ = |ebi - ei| * S + ei * |Sb - S| := by
            rw [abs_mul, abs_neg, abs_mul, hS_abs, he_abs]
        _ ≤ ((η : ℝ) * ei + subnormalConst) * S + ei * (δ * S + Nsc) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right h1 hS_nn
            · exact mul_le_mul_of_nonneg_left h2 hei_nn
        _ = ((η : ℝ) + δ) * (ei * S) + subnormalConst * S + ei * Nsc := by ring
    have h_diff_eq : ebi / Sb - σi = (ebi * S - ei * Sb) / (Sb * S) := by
      rw [hσi_def]; field_simp
    have hSbS_pos : 0 < Sb * S := mul_pos hSb_pos hS_pos
    have hmS_pos : 0 < m * S := mul_pos h_m_pos hS_pos
    have hmS_le : m * S ≤ Sb * S :=
      mul_le_mul_of_nonneg_right hSb_ge_m hS_nn
    have h_num_bd_nn : 0 ≤
        ((η : ℝ) + δ) * (ei * S) + subnormalConst * S + ei * Nsc := by
      have hηδ_nn : 0 ≤ (η : ℝ) + δ := by linarith
      have ha : 0 ≤ ((η : ℝ) + δ) * (ei * S) :=
        mul_nonneg hηδ_nn (mul_nonneg hei_nn hS_nn)
      have hb : 0 ≤ subnormalConst * S := mul_nonneg hsc_nn hS_nn
      have hc : 0 ≤ ei * Nsc := mul_nonneg hei_nn hNsc_nn
      linarith
    have h_ratio_bd : |ebi / Sb - σi| ≤
        ((η : ℝ) + δ) * ei / m + subnormalConst / m + ei * Nsc / (m * S) := by
      rw [h_diff_eq, abs_div, abs_of_pos hSbS_pos]
      calc |ebi * S - ei * Sb| / (Sb * S)
          ≤ (((η : ℝ) + δ) * (ei * S) + subnormalConst * S + ei * Nsc) / (Sb * S) :=
            div_le_div_of_nonneg_right h_num_bd (le_of_lt hSbS_pos)
        _ ≤ (((η : ℝ) + δ) * (ei * S) + subnormalConst * S + ei * Nsc) / (m * S) :=
            div_le_div_of_nonneg_left h_num_bd_nn hmS_pos hmS_le
        _ = ((η : ℝ) + δ) * ei / m + subnormalConst / m + ei * Nsc / (m * S) := by
            field_simp
    have h_total : |q - σi| ≤
        ((η : ℝ) * (1 + (η : ℝ)) * ei / m + (η : ℝ) * subnormalConst / m + subnormalConst) +
        (((η : ℝ) + δ) * ei / m + subnormalConst / m + ei * Nsc / (m * S)) := by
      calc |q - σi|
          = |(q - ebi / Sb) + (ebi / Sb - σi)| := by ring_nf
        _ ≤ |q - ebi / Sb| + |ebi / Sb - σi| := abs_add_le _ _
        _ ≤ _ := by linarith [h_div_err_bd, h_ratio_bd]
    calc |q - σi|
        ≤ ((η : ℝ) * (1 + (η : ℝ)) * ei / m + (η : ℝ) * subnormalConst / m + subnormalConst) +
          (((η : ℝ) + δ) * ei / m + subnormalConst / m + ei * Nsc / (m * S)) := h_total
      _ = (((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S + Nsc) / m * σi +
          ((1 + (η : ℝ)) / m + 1) * subnormalConst := by
          rw [hσi_def]
          field_simp
          ring

set_option maxHeartbeats 800000 in
/-- **Subnormal-tolerant FP softmax componentwise error bound.**

Drop-in replacement for `fpSoftmaxOf_error_bound` that does *not* assume the
exp outputs or the quotients are in normal range, *and* tolerates exp outputs
that underflow fully to zero.

- `h_S_margin` replaces `h_δ_lt`: it ensures that even after absorbing the
  additive `(1+εsum)·n·subnormalConst` term from the denominator error, the
  FP denominator stays strictly positive (in fact `≥ (1-δ)·S/2`).

The bound picks up an additive `subnormalSoftmaxAbs xs εsum · subnormalConst`
term alongside a factor-of-2 loosening of the multiplicative coefficient.

**Quantification.** For binary64 with `n ≤ 10^308` terms, the additive term is
dwarfed by roundoff even at `η ≈ 10^(-16)`: `subnormalSoftmaxAbs · subnormalConst`
is typically `≲ 10^(-300)`. The bound is conservative but correct. -/
theorem fpSoftmaxOf_error_bound_subnormal
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_S_margin : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
                  (∑ j, Real.exp ((xs j).toVal : ℝ)) >
                  2 * (1 + εsum) * (n : ℝ) * subnormalConst)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      2 * softmaxErrorCoeff εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs xs εsum * subnormalConst := by
  -- Abbreviations
  set S : ℝ := ∑ j, Real.exp ((xs j).toVal : ℝ) with hS_def
  set δ : ℝ := (η : ℝ) + εsum * (1 + (η : ℝ)) with hδ_def
  set Nsc : ℝ := (1 + εsum) * (n : ℝ) * subnormalConst with hNsc_def
  set σi : ℝ := softmax (fun j => ((xs j).toVal : ℝ)) i with hσi_def
  -- Basic positivity facts
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have h1ε_nn : (0 : ℝ) ≤ 1 + εsum := by linarith
  have hsc_nn : 0 ≤ subnormalConst := subnormalConst_nn
  have hNsc_nn : 0 ≤ Nsc := by show 0 ≤ (1 + εsum) * (n : ℝ) * subnormalConst; positivity
  have h_S_margin_Nsc : (1 - δ) * S > 2 * Nsc := by
    show (1 - δ) * S > 2 * ((1 + εsum) * (n : ℝ) * subnormalConst)
    have := h_S_margin; linarith
  have he_pos : ∀ j, 0 < Real.exp ((xs j).toVal : ℝ) := fun j => Real.exp_pos _
  have hS_pos : 0 < S := by
    show 0 < ∑ j, Real.exp ((xs j).toVal : ℝ)
    exact Finset.sum_pos (fun j _ => he_pos j)
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
  have hS_nn : 0 ≤ S := le_of_lt hS_pos
  have hS_ne : (S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have h1mδ_pos : 0 < 1 - δ := by
    by_contra h
    push_neg at h
    have hle : (1 - δ) * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hS_nn
    have hge : (0 : ℝ) ≤ 2 * Nsc := by positivity
    linarith [h_S_margin_Nsc]
  have h1δS_pos : 0 < (1 - δ) * S := mul_pos h1mδ_pos hS_pos
  -- m := (1-δ)·S/2; derive positivity and margin inequality
  have h_m_pos : 0 < (1 - δ) * S / 2 := by linarith
  have h_m_le_margin : (1 - δ) * S / 2 ≤
      (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
        (∑ j, Real.exp ((xs j).toVal : ℝ)) -
      (1 + εsum) * (n : ℝ) * subnormalConst := by
    show (1 - δ) * S / 2 ≤ (1 - δ) * S - Nsc
    linarith [h_S_margin_Nsc]
  -- Invoke the core tight bound with m = (1-δ)·S/2
  have h_core := fpSoftmax_apply_core_bound hn xs exps denom result εsum
    h_exp h_denom_close h_εsum_nn hd_m h_result
    ((1 - δ) * S / 2) h_m_pos h_m_le_margin i
  -- σ_i nonneg and ≤ 1
  have hσi_nn : 0 ≤ σi := softmax_nonneg _ hn i
  have hσi_le_one : σi ≤ 1 := softmax_le_one _ i
  -- Core RHS ≤ target RHS via algebra + σ_i ≤ 1
  -- target - core = 2·Nsc·(1 - σ_i)/((1-δ)·S) ≥ 0
  have h_bound_diff :
      (((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S + Nsc) / ((1 - δ) * S / 2) * σi +
      ((1 + (η : ℝ)) / ((1 - δ) * S / 2) + 1) * subnormalConst ≤
      2 * softmaxErrorCoeff εsum * σi + subnormalSoftmaxAbs xs εsum * subnormalConst := by
    have h_target_minus_core :
        2 * softmaxErrorCoeff εsum * σi +
        subnormalSoftmaxAbs xs εsum * subnormalConst -
        ((((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S + Nsc) / ((1 - δ) * S / 2) * σi +
         ((1 + (η : ℝ)) / ((1 - δ) * S / 2) + 1) * subnormalConst) =
        2 * Nsc * (1 - σi) / ((1 - δ) * S) := by
      simp only [softmaxErrorCoeff, subnormalSoftmaxAbs, ← hδ_def, ← hS_def]
      field_simp
      ring
    have hdiff_nn : 0 ≤ 2 * Nsc * (1 - σi) / ((1 - δ) * S) := by
      have h1sigma : 0 ≤ 1 - σi := by linarith
      have h2Nsc : 0 ≤ 2 * Nsc := by linarith
      have hnum : 0 ≤ 2 * Nsc * (1 - σi) := mul_nonneg h2Nsc h1sigma
      exact div_nonneg hnum (le_of_lt h1δS_pos)
    linarith
  -- Combine: |q - σ_i| ≤ core RHS ≤ target RHS
  have h_core' :
      |((result i).toVal : ℝ) - σi| ≤
      (((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S + Nsc) / ((1 - δ) * S / 2) * σi +
      ((1 + (η : ℝ)) / ((1 - δ) * S / 2) + 1) * subnormalConst := by
    have : (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
             (∑ j, Real.exp ((xs j).toVal : ℝ)) +
           (1 + εsum) * (n : ℝ) * subnormalConst) / ((1 - δ) * S / 2) =
           (((η : ℝ)^2 + 2 * (η : ℝ) + δ) * S + Nsc) / ((1 - δ) * S / 2) := by
      simp only [← hδ_def, ← hS_def, ← hNsc_def]
    exact this ▸ h_core
  linarith [h_core', h_bound_diff]

set_option maxHeartbeats 800000 in
/-- **Tight subnormal-tolerant FP softmax componentwise error bound.**

Uses `Sb ≥ (1-δ)·S - N·subnormalConst` directly (no factor-of-2 looseness).
Requires only the minimal `h_S_margin_tight : 0 < subnormalSoftmaxDenomMargin xs εsum`,
which is strictly weaker than the `> 2·N·subnormalConst` margin of the
factor-of-2 version.

When subnormal contributions vanish (`N·subnormalConst → 0`), the tight mult
coefficient reduces to `softmaxErrorCoeff εsum` (vs. `2·softmaxErrorCoeff` in
the factor-of-2 bound). The tight bound is therefore roughly half as loose in
the typical regime.

The additive coefficient `subnormalSoftmaxAbs_tight` is similarly tighter: it
does not use `σ_i ≤ 1` to move the `N·sc` cross-term to the additive bucket. -/
theorem fpSoftmaxOf_error_bound_subnormal_tight
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs εsum)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff_tight xs εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs εsum * subnormalConst := by
  -- Apply core with m := subnormalSoftmaxDenomMargin xs εsum (= (1-δ)·S - Nsc)
  have hm_le : subnormalSoftmaxDenomMargin xs εsum ≤
      (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
        (∑ j, Real.exp ((xs j).toVal : ℝ)) -
      (1 + εsum) * (n : ℝ) * subnormalConst := le_of_eq rfl
  have h_core := fpSoftmax_apply_core_bound hn xs exps denom result εsum
    h_exp h_denom_close h_εsum_nn hd_m h_result
    (subnormalSoftmaxDenomMargin xs εsum) h_m_pos hm_le i
  -- Rewrite core conclusion to match target
  have h_eq :
      (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
         (∑ j, Real.exp ((xs j).toVal : ℝ)) +
       (1 + εsum) * (n : ℝ) * subnormalConst) / subnormalSoftmaxDenomMargin xs εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      ((1 + (η : ℝ)) / subnormalSoftmaxDenomMargin xs εsum + 1) * subnormalConst =
      softmaxErrorCoeff_tight xs εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs εsum * subnormalConst := by
    simp only [softmaxErrorCoeff_tight, subnormalSoftmaxAbs_tight]
    ring
  linarith [h_core, h_eq]

/-- When `S = ∑ exp((xs j).toVal) ≥ 1`, the `xs`-dependent additive coefficient
`subnormalSoftmaxAbs xs εsum` is bounded by an `xs`-independent quantity.

This situation arises naturally after the subtract-max trick: if `max_j xs_j = 0`,
then `exp(0) = 1` is among the summands, so `S ≥ 1`. -/
theorem subnormalSoftmaxAbs_le_of_S_ge_one {n : ℕ} (xs : Fin n → FiniteFp) (εsum : ℝ)
    (h_εsum_nn : 0 ≤ εsum)
    (h_1mδ_pos : 0 < 1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))
    (h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ)) :
    subnormalSoftmaxAbs xs εsum ≤
      1 + 2 * (1 + (η : ℝ) + (1 + εsum) * (n : ℝ)) /
        (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) := by
  unfold subnormalSoftmaxAbs
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnum_nn : 0 ≤ 2 * (1 + (η : ℝ) + (1 + εsum) * (n : ℝ)) := by
    have : 0 ≤ (1 + εsum) * (n : ℝ) := mul_nonneg (by linarith) hn_nn
    have : 0 ≤ 1 + (η : ℝ) + (1 + εsum) * (n : ℝ) := by linarith
    linarith
  have h_denom_le : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) ≤
                    (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
                    (∑ j, Real.exp ((xs j).toVal : ℝ)) := by
    calc (1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))
        = (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) * 1 := by ring
      _ ≤ (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
          (∑ j, Real.exp ((xs j).toVal : ℝ)) :=
        mul_le_mul_of_nonneg_left h_S_ge_one (le_of_lt h_1mδ_pos)
  have h_div_le : 2 * (1 + (η : ℝ) + (1 + εsum) * (n : ℝ)) /
      ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
       (∑ j, Real.exp ((xs j).toVal : ℝ))) ≤
      2 * (1 + (η : ℝ) + (1 + εsum) * (n : ℝ)) /
      (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) :=
    div_le_div_of_nonneg_left hnum_nn h_1mδ_pos h_denom_le
  linarith

/-- Under `S ≥ 1` and `N·sc < 1 - δ`, the `xs`-dependent tight additive
coefficient is bounded by an `xs`-independent quantity. -/
theorem subnormalSoftmaxAbs_tight_le_of_S_ge_one
    {n : ℕ} (xs : Fin n → FiniteFp) (εsum : ℝ)
    (h_εsum_nn : 0 ≤ εsum)
    (h_margin_ind : (1 + εsum) * (n : ℝ) * subnormalConst <
                     1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))
    (h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ)) :
    subnormalSoftmaxAbs_tight xs εsum ≤
      1 + (1 + (η : ℝ)) /
        ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
         (1 + εsum) * (n : ℝ) * subnormalConst) := by
  unfold subnormalSoftmaxAbs_tight subnormalSoftmaxDenomMargin
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hsc_nn : 0 ≤ subnormalConst := subnormalConst_nn
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hNsc_nn : 0 ≤ (1 + εsum) * (n : ℝ) * subnormalConst := by positivity
  have h_1mδ_pos : 0 < 1 - ((η : ℝ) + εsum * (1 + (η : ℝ))) := by linarith
  have h_m_ind_pos : 0 <
      (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
      (1 + εsum) * (n : ℝ) * subnormalConst := by linarith
  -- m_xs ≥ m_ind via S ≥ 1
  have h_m_xs_ge_m_ind :
      (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
      (1 + εsum) * (n : ℝ) * subnormalConst ≤
      (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
        (∑ j, Real.exp ((xs j).toVal : ℝ)) -
      (1 + εsum) * (n : ℝ) * subnormalConst := by
    have : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) * 1 ≤
           (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
             (∑ j, Real.exp ((xs j).toVal : ℝ)) :=
      mul_le_mul_of_nonneg_left h_S_ge_one (le_of_lt h_1mδ_pos)
    linarith
  -- (1+η)/m_xs ≤ (1+η)/m_ind
  have h1η_nn : (0 : ℝ) ≤ 1 + (η : ℝ) := by linarith
  have h_div_le : (1 + (η : ℝ)) /
      ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
        (∑ j, Real.exp ((xs j).toVal : ℝ)) -
       (1 + εsum) * (n : ℝ) * subnormalConst) ≤
      (1 + (η : ℝ)) /
      ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
       (1 + εsum) * (n : ℝ) * subnormalConst) :=
    div_le_div_of_nonneg_left h1η_nn h_m_ind_pos h_m_xs_ge_m_ind
  linarith

/-- Under `S ≥ 1` and `N·sc < 1 - δ`, the tight mult coefficient is bounded
by an `xs`-independent quantity.

The function `S ↦ ((η²+2η+δ)·S + N·sc) / ((1-δ)·S - N·sc)` is decreasing in `S`,
so the maximum over `S ≥ 1` is attained at `S = 1`. -/
theorem softmaxErrorCoeff_tight_le_of_S_ge_one
    {n : ℕ} (xs : Fin n → FiniteFp) (εsum : ℝ)
    (h_εsum_nn : 0 ≤ εsum)
    (h_margin_ind : (1 + εsum) * (n : ℝ) * subnormalConst <
                     1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))
    (h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ)) :
    softmaxErrorCoeff_tight xs εsum ≤
      ((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ))) +
       (1 + εsum) * (n : ℝ) * subnormalConst) /
      ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
       (1 + εsum) * (n : ℝ) * subnormalConst) := by
  unfold softmaxErrorCoeff_tight subnormalSoftmaxDenomMargin
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hsc_nn : 0 ≤ subnormalConst := subnormalConst_nn
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hNsc_nn : 0 ≤ (1 + εsum) * (n : ℝ) * subnormalConst := by positivity
  have h1ε_nn : (0 : ℝ) ≤ 1 + εsum := by linarith
  have h_1mδ_pos : 0 < 1 - ((η : ℝ) + εsum * (1 + (η : ℝ))) := by linarith
  have he_pos : ∀ j, 0 < Real.exp ((xs j).toVal : ℝ) := fun j => Real.exp_pos _
  have hS_pos : 0 < ∑ j, Real.exp ((xs j).toVal : ℝ) := by
    have hn0 : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ) := h_S_ge_one
    linarith
  -- Abbreviations
  set S : ℝ := ∑ j, Real.exp ((xs j).toVal : ℝ) with hS_def
  set δ : ℝ := (η : ℝ) + εsum * (1 + (η : ℝ)) with hδ_def
  set Nsc : ℝ := (1 + εsum) * (n : ℝ) * subnormalConst with hNsc_def
  set a : ℝ := (η : ℝ)^2 + 2 * (η : ℝ) + δ with ha_def
  have ha_nn : 0 ≤ a := by show 0 ≤ (η : ℝ)^2 + 2 * (η : ℝ) + δ; positivity
  have h_m_xs_pos : 0 < (1 - δ) * S - Nsc := by
    have h1 : (1 - δ) * 1 ≤ (1 - δ) * S :=
      mul_le_mul_of_nonneg_left h_S_ge_one (le_of_lt h_1mδ_pos)
    linarith [h_margin_ind]
  have h_m_ind_pos : 0 < (1 - δ) - Nsc := by linarith [h_margin_ind]
  -- Cross-multiply: show (a·S + Nsc)·((1-δ) - Nsc) ≤ (a + Nsc)·((1-δ)·S - Nsc)
  rw [div_le_div_iff₀ h_m_xs_pos h_m_ind_pos]
  -- Difference: RHS - LHS = Nsc · (a + (1-δ)) · (S - 1) ≥ 0
  have h_S_ge_1 : 1 ≤ S := h_S_ge_one
  nlinarith [hNsc_nn, ha_nn, h_1mδ_pos, h_S_ge_1, mul_nonneg hNsc_nn ha_nn,
             mul_nonneg hNsc_nn (le_of_lt h_1mδ_pos)]

set_option maxHeartbeats 800000 in
/-- **Shifted subnormal-tolerant softmax error bound** (S ≥ 1 case).

Variant of `fpSoftmaxOf_error_bound_subnormal` whose hypotheses are purely
`xs`-independent: `h_margin` uses `(1 - δ)` (not `(1-δ)·S`), and `h_S_ge_one`
states `1 ≤ ∑ exp((xs j).toVal)` — guaranteed after the subtract-max trick.

The resulting additive coefficient is correspondingly `xs`-independent. -/
theorem fpSoftmaxOf_error_bound_subnormal_shifted
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ))
    (h_margin : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) >
                2 * (1 + εsum) * (n : ℝ) * subnormalConst)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      2 * softmaxErrorCoeff εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      (1 + 2 * (1 + (η : ℝ) + (1 + εsum) * (n : ℝ)) /
         (1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))) * subnormalConst := by
  have hNsc_nn : 0 ≤ 2 * (1 + εsum) * (n : ℝ) * subnormalConst := by
    have h1 : 0 ≤ 1 + εsum := by linarith
    have h2 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ subnormalConst := subnormalConst_nn
    positivity
  have h_1mδ_pos : 0 < 1 - ((η : ℝ) + εsum * (1 + (η : ℝ))) := by linarith
  -- Upgrade h_margin to the xs-dep form using S ≥ 1
  have h_S_margin : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
                    (∑ j, Real.exp ((xs j).toVal : ℝ)) >
                    2 * (1 + εsum) * (n : ℝ) * subnormalConst := by
    calc 2 * (1 + εsum) * (n : ℝ) * subnormalConst
        < 1 - ((η : ℝ) + εsum * (1 + (η : ℝ))) := h_margin
      _ = (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) * 1 := by ring
      _ ≤ (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
          (∑ j, Real.exp ((xs j).toVal : ℝ)) :=
          mul_le_mul_of_nonneg_left h_S_ge_one (le_of_lt h_1mδ_pos)
  have h_main := fpSoftmaxOf_error_bound_subnormal hn xs exps denom result εsum
    h_exp h_denom_close h_εsum_nn h_S_margin hd_m h_result i
  have h_SSA_le := subnormalSoftmaxAbs_le_of_S_ge_one xs εsum h_εsum_nn h_1mδ_pos h_S_ge_one
  have hsc_nn : 0 ≤ subnormalConst := subnormalConst_nn
  linarith [mul_le_mul_of_nonneg_right h_SSA_le hsc_nn]

set_option maxHeartbeats 800000 in
/-- **Shifted tight subnormal-tolerant softmax error bound** (S ≥ 1 case).

Variant of `fpSoftmaxOf_error_bound_subnormal_tight` whose hypotheses and
conclusion are purely `xs`-independent: `h_margin_ind` uses `(1 - δ)` (not
`(1-δ)·S`), and `h_S_ge_one` states `1 ≤ ∑ exp((xs j).toVal)` — guaranteed
after the subtract-max trick.

The mult coefficient reduces to `softmaxErrorCoeff` as `N·sc → 0`, giving a
factor-of-2 improvement over `fpSoftmaxOf_error_bound_subnormal_shifted` in
the typical regime. -/
theorem fpSoftmaxOf_error_bound_subnormal_tight_shifted
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ))
    (h_margin_ind : (1 + εsum) * (n : ℝ) * subnormalConst <
                     1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ))) +
        (1 + εsum) * (n : ℝ) * subnormalConst) /
       ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
        (1 + εsum) * (n : ℝ) * subnormalConst)) *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      (1 + (1 + (η : ℝ)) /
        ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
         (1 + εsum) * (n : ℝ) * subnormalConst)) * subnormalConst := by
  have hsc_nn : 0 ≤ subnormalConst := subnormalConst_nn
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hη_nn : (0 : ℝ) ≤ η := by positivity
  have hNsc_nn : 0 ≤ (1 + εsum) * (n : ℝ) * subnormalConst := by positivity
  have h_1mδ_pos : 0 < 1 - ((η : ℝ) + εsum * (1 + (η : ℝ))) := by linarith
  -- Derive `h_m_pos` from `h_S_ge_one` and `h_margin_ind`.
  have h_m_pos : 0 < subnormalSoftmaxDenomMargin xs εsum := by
    unfold subnormalSoftmaxDenomMargin
    have h1 : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) * 1 ≤
              (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
                (∑ j, Real.exp ((xs j).toVal : ℝ)) :=
      mul_le_mul_of_nonneg_left h_S_ge_one (le_of_lt h_1mδ_pos)
    linarith
  have h_main := fpSoftmaxOf_error_bound_subnormal_tight hn xs exps denom result εsum
    h_exp h_denom_close h_εsum_nn h_m_pos hd_m h_result i
  have h_coeff_le := softmaxErrorCoeff_tight_le_of_S_ge_one xs εsum h_εsum_nn
    h_margin_ind h_S_ge_one
  have h_abs_le := subnormalSoftmaxAbs_tight_le_of_S_ge_one xs εsum h_εsum_nn
    h_margin_ind h_S_ge_one
  have h_sig_nn : 0 ≤ softmax (fun j => ((xs j).toVal : ℝ)) i :=
    softmax_nonneg _ hn i
  have h_step1 := mul_le_mul_of_nonneg_right h_coeff_le h_sig_nn
  have h_step2 := mul_le_mul_of_nonneg_right h_abs_le hsc_nn
  linarith

/-- **FpSumBound-taking wrapper** for the subnormal-tolerant bound. -/
theorem fpSoftmaxOf_error_bound_subnormal_of_sumBound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (sum : FpSum.FpSumBound exps ℝ)
    (result : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_S_margin : (1 - ((η : ℝ) + sum.relErr * (1 + (η : ℝ)))) *
                  (∑ j, Real.exp ((xs j).toVal : ℝ)) >
                  2 * (1 + sum.relErr) * (n : ℝ) * subnormalConst)
    (hd_m : sum.result.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) sum.result = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      2 * softmaxErrorCoeff sum.relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs xs sum.relErr * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal hn xs exps sum.result result sum.relErr
    h_exp sum.h_bound sum.h_relErr_nn h_S_margin hd_m h_result i

/-- **FpSumBound-taking wrapper** for the tight subnormal-tolerant bound. -/
theorem fpSoftmaxOf_error_bound_subnormal_tight_of_sumBound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (sum : FpSum.FpSumBound exps ℝ)
    (result : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs sum.relErr)
    (hd_m : sum.result.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) sum.result = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff_tight xs sum.relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs sum.relErr * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal_tight hn xs exps sum.result result sum.relErr
    h_exp sum.h_bound sum.h_relErr_nn h_m_pos hd_m h_result i

/-- **Convenience theorem**: combines exp-extraction, result-extraction, and error
bound in one. User supplies just `xs`, `h_nonpos`, `h_exp_nr`, a sum method,
and normal-range hypotheses for the quotient; gets the error bound for auto-extracted
`fpSoftmaxResults`.

Note: `h_bounded` (quotients in `[0, largestFiniteFloat]`) is still needed to
construct `fpSoftmaxResults`. In practice it follows from `h_quot_nr` combined
with positivity, but we keep it explicit for flexibility. -/
theorem fpSoftmax_shifted_error
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (h_nonpos : ∀ i, ((xs i).toVal : ℝ) ≤ 0)
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (sum : FpSum.FpSumBound (fpExpsFromXs xs h_nonpos) ℝ)
    (h_δ_lt : (η : ℝ) + sum.relErr * (1 + (η : ℝ)) < 1)
    (hd_m : sum.result.m ≠ 0)
    (h_quot_nr : ∀ i, isNormalRange
      (((fpExpsFromXs xs h_nonpos i).toVal : ℝ) / sum.result.toVal))
    (h_bounded : ∀ i, 0 ≤ (((fpExpsFromXs xs h_nonpos i).toVal : ℝ) / sum.result.toVal) ∧
                      (((fpExpsFromXs xs h_nonpos i).toVal : ℝ) / sum.result.toVal) ≤
                        FiniteFp.largestFiniteFloat.toVal (R := ℝ))
    (i : Fin n) :
    |((fpSoftmaxResults (fpExpsFromXs xs h_nonpos) sum.result hd_m h_bounded i).toVal : ℝ) -
      softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff sum.relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i :=
  fpSoftmaxOf_error_bound_of_sumBound hn xs (fpExpsFromXs xs h_nonpos) sum
    (fpSoftmaxResults (fpExpsFromXs xs h_nonpos) sum.result hd_m h_bounded)
    (fpExpsFromXs_correct xs h_nonpos) h_exp_nr h_δ_lt hd_m h_quot_nr
    (fpSoftmaxResults_correct (fpExpsFromXs xs h_nonpos) sum.result hd_m h_bounded) i

/-! ### Sum-to-1 invariant

FP softmax outputs approximately sum to 1, with the error bounded by the
per-component error coefficient. -/

/-- The sum of FP softmax outputs is within `softmaxErrorCoeff` of 1. -/
theorem fpSoftmax_sum_close_to_one
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_δ_lt : (η : ℝ) + εsum * (1 + (η : ℝ)) < 1)
    (hd_m : denom.m ≠ 0)
    (h_quot_nr : ∀ i, isNormalRange (((exps i).toVal : ℝ) / denom.toVal))
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i)) :
    |(∑ i, ((result i).toVal : ℝ)) - 1| ≤ softmaxErrorCoeff εsum := by
  have hσ_sum : ∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i = 1 :=
    softmax_sum_eq_one _ hn
  have hcoeff_nn : 0 ≤ softmaxErrorCoeff εsum := by
    have hη_nn : (0 : ℝ) ≤ η := by positivity
    have h1mδ : 0 < 1 - ((η : ℝ) + εsum * (1 + (η : ℝ))) := by linarith
    unfold softmaxErrorCoeff
    apply div_nonneg
    · have : 0 ≤ (η : ℝ) + εsum * (1 + (η : ℝ)) := by positivity
      positivity
    · linarith
  -- Per-i bound
  have hper : ∀ i, |((result i).toVal : ℝ) -
                    softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
                   softmaxErrorCoeff εsum *
                     softmax (fun j => ((xs j).toVal : ℝ)) i := by
    intro i
    exact fpSoftmaxOf_error_bound hn xs exps denom result εsum
      h_exp h_exp_nr h_denom_close h_εsum_nn h_δ_lt hd_m h_quot_nr h_result i
  -- Triangle inequality on the sum
  calc |(∑ i, ((result i).toVal : ℝ)) - 1|
      = |(∑ i, ((result i).toVal : ℝ)) -
          ∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i| := by rw [hσ_sum]
    _ = |∑ i, (((result i).toVal : ℝ) -
                softmax (fun j => ((xs j).toVal : ℝ)) i)| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |((result i).toVal : ℝ) -
                softmax (fun j => ((xs j).toVal : ℝ)) i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, softmaxErrorCoeff εsum *
                softmax (fun j => ((xs j).toVal : ℝ)) i :=
          Finset.sum_le_sum (fun i _ => hper i)
    _ = softmaxErrorCoeff εsum * ∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i := by
          rw [← Finset.mul_sum]
    _ = softmaxErrorCoeff εsum := by rw [hσ_sum]; ring

/-! ### Argmax preservation

If the math softmax has a sufficiently dominant argmax `i*` — specifically,
`σ_{i*} - σ_j > softmaxErrorCoeff · (σ_{i*} + σ_j)` for all `j ≠ i*` — then
the FP softmax has `result_{i*} > result_j` for the same `i*`. -/

/-- Argmax preservation (single pairwise comparison form).

Given the per-component error bound for indices `i*` and `j`, if
`σ_{i*} - σ_j > c · (σ_{i*} + σ_j)` where `c = softmaxErrorCoeff εsum`,
then the FP outputs satisfy `result_{i*} > result_j`. -/
theorem fpSoftmax_preserves_argmax_pair
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ)))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_δ_lt : (η : ℝ) + εsum * (1 + (η : ℝ)) < 1)
    (hd_m : denom.m ≠ 0)
    (h_quot_nr : ∀ i, isNormalRange (((exps i).toVal : ℝ) / denom.toVal))
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (istar j : Fin n)
    (h_gap : softmax (fun k => ((xs k).toVal : ℝ)) istar -
             softmax (fun k => ((xs k).toVal : ℝ)) j >
              softmaxErrorCoeff εsum *
                (softmax (fun k => ((xs k).toVal : ℝ)) istar +
                 softmax (fun k => ((xs k).toVal : ℝ)) j)) :
    ((result j).toVal : ℝ) < ((result istar).toVal : ℝ) := by
  set sig : Fin n → ℝ := fun k => softmax (fun k' => ((xs k').toVal : ℝ)) k with hsig_def
  set c : ℝ := softmaxErrorCoeff εsum with hc_def
  have h_i : |((result istar).toVal : ℝ) - sig istar| ≤ c * sig istar :=
    fpSoftmaxOf_error_bound hn xs exps denom result εsum
      h_exp h_exp_nr h_denom_close h_εsum_nn h_δ_lt hd_m h_quot_nr h_result istar
  have h_j : |((result j).toVal : ℝ) - sig j| ≤ c * sig j :=
    fpSoftmaxOf_error_bound hn xs exps denom result εsum
      h_exp h_exp_nr h_denom_close h_εsum_nn h_δ_lt hd_m h_quot_nr h_result j
  -- Unpack the absolute values
  have h_i_lo : sig istar - c * sig istar ≤ ((result istar).toVal : ℝ) := by
    have := (abs_le.mp h_i).1
    linarith
  have h_j_hi : ((result j).toVal : ℝ) ≤ sig j + c * sig j := by
    have := (abs_le.mp h_j).2
    linarith
  -- sig istar * (1 - c) > sig j * (1 + c) iff sig istar - sig j > c * (sig istar + sig j)
  linarith [h_gap]

/-- **Sum-close-to-1** for the subnormal-tolerant error bound.

`|Σ result_i - 1| ≤ 2·softmaxErrorCoeff εsum + n · subnormalSoftmaxAbs xs εsum · subnormalConst`. -/
theorem fpSoftmax_sum_close_to_one_subnormal
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_S_margin : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
                  (∑ j, Real.exp ((xs j).toVal : ℝ)) >
                  2 * (1 + εsum) * (n : ℝ) * subnormalConst)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i)) :
    |(∑ i, ((result i).toVal : ℝ)) - 1| ≤
      2 * softmaxErrorCoeff εsum +
      (n : ℝ) * (subnormalSoftmaxAbs xs εsum * subnormalConst) := by
  have hσ_sum : ∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i = 1 :=
    softmax_sum_eq_one _ hn
  have hper : ∀ i, |((result i).toVal : ℝ) -
                    softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
                   2 * softmaxErrorCoeff εsum *
                     softmax (fun j => ((xs j).toVal : ℝ)) i +
                   subnormalSoftmaxAbs xs εsum * subnormalConst := by
    intro i
    exact fpSoftmaxOf_error_bound_subnormal hn xs exps denom result εsum
      h_exp h_denom_close h_εsum_nn h_S_margin hd_m h_result i
  calc |(∑ i, ((result i).toVal : ℝ)) - 1|
      = |(∑ i, ((result i).toVal : ℝ)) -
          ∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i| := by rw [hσ_sum]
    _ = |∑ i, (((result i).toVal : ℝ) -
                softmax (fun j => ((xs j).toVal : ℝ)) i)| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |((result i).toVal : ℝ) -
                softmax (fun j => ((xs j).toVal : ℝ)) i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (2 * softmaxErrorCoeff εsum *
                softmax (fun j => ((xs j).toVal : ℝ)) i +
              subnormalSoftmaxAbs xs εsum * subnormalConst) :=
          Finset.sum_le_sum (fun i _ => hper i)
    _ = 2 * softmaxErrorCoeff εsum *
          (∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i) +
        (n : ℝ) * (subnormalSoftmaxAbs xs εsum * subnormalConst) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 2 * softmaxErrorCoeff εsum +
        (n : ℝ) * (subnormalSoftmaxAbs xs εsum * subnormalConst) := by
          rw [hσ_sum]; ring

/-- **Argmax preservation** for the subnormal-tolerant error bound.

The gap condition picks up a `2·subnormalSoftmaxAbs·subnormalConst` term on the
right-hand side, accounting for the worst-case additive errors at both indices. -/
theorem fpSoftmax_preserves_argmax_pair_subnormal
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_S_margin : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
                  (∑ j, Real.exp ((xs j).toVal : ℝ)) >
                  2 * (1 + εsum) * (n : ℝ) * subnormalConst)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (istar j : Fin n)
    (h_gap : softmax (fun k => ((xs k).toVal : ℝ)) istar -
             softmax (fun k => ((xs k).toVal : ℝ)) j >
              2 * softmaxErrorCoeff εsum *
                (softmax (fun k => ((xs k).toVal : ℝ)) istar +
                 softmax (fun k => ((xs k).toVal : ℝ)) j) +
              2 * (subnormalSoftmaxAbs xs εsum * subnormalConst)) :
    ((result j).toVal : ℝ) < ((result istar).toVal : ℝ) := by
  set sig : Fin n → ℝ := fun k => softmax (fun k' => ((xs k').toVal : ℝ)) k with hsig_def
  set c : ℝ := 2 * softmaxErrorCoeff εsum with hc_def
  set a : ℝ := subnormalSoftmaxAbs xs εsum * subnormalConst with ha_def
  have h_i : |((result istar).toVal : ℝ) - sig istar| ≤ c * sig istar + a :=
    fpSoftmaxOf_error_bound_subnormal hn xs exps denom result εsum
      h_exp h_denom_close h_εsum_nn h_S_margin hd_m h_result istar
  have h_j : |((result j).toVal : ℝ) - sig j| ≤ c * sig j + a :=
    fpSoftmaxOf_error_bound_subnormal hn xs exps denom result εsum
      h_exp h_denom_close h_εsum_nn h_S_margin hd_m h_result j
  have h_i_lo : sig istar - (c * sig istar + a) ≤ ((result istar).toVal : ℝ) := by
    have := (abs_le.mp h_i).1; linarith
  have h_j_hi : ((result j).toVal : ℝ) ≤ sig j + (c * sig j + a) := by
    have := (abs_le.mp h_j).2; linarith
  linarith [h_gap]

/-- **Sum-close-to-1** for the tight subnormal-tolerant error bound. -/
theorem fpSoftmax_sum_close_to_one_subnormal_tight
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs εsum)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i)) :
    |(∑ i, ((result i).toVal : ℝ)) - 1| ≤
      softmaxErrorCoeff_tight xs εsum +
      (n : ℝ) * (subnormalSoftmaxAbs_tight xs εsum * subnormalConst) := by
  have hσ_sum : ∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i = 1 :=
    softmax_sum_eq_one _ hn
  have hper : ∀ i, |((result i).toVal : ℝ) -
                    softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
                   softmaxErrorCoeff_tight xs εsum *
                     softmax (fun j => ((xs j).toVal : ℝ)) i +
                   subnormalSoftmaxAbs_tight xs εsum * subnormalConst := by
    intro i
    exact fpSoftmaxOf_error_bound_subnormal_tight hn xs exps denom result εsum
      h_exp h_denom_close h_εsum_nn h_m_pos hd_m h_result i
  calc |(∑ i, ((result i).toVal : ℝ)) - 1|
      = |(∑ i, ((result i).toVal : ℝ)) -
          ∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i| := by rw [hσ_sum]
    _ = |∑ i, (((result i).toVal : ℝ) -
                softmax (fun j => ((xs j).toVal : ℝ)) i)| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |((result i).toVal : ℝ) -
                softmax (fun j => ((xs j).toVal : ℝ)) i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (softmaxErrorCoeff_tight xs εsum *
                softmax (fun j => ((xs j).toVal : ℝ)) i +
              subnormalSoftmaxAbs_tight xs εsum * subnormalConst) :=
          Finset.sum_le_sum (fun i _ => hper i)
    _ = softmaxErrorCoeff_tight xs εsum *
          (∑ i, softmax (fun j => ((xs j).toVal : ℝ)) i) +
        (n : ℝ) * (subnormalSoftmaxAbs_tight xs εsum * subnormalConst) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = softmaxErrorCoeff_tight xs εsum +
        (n : ℝ) * (subnormalSoftmaxAbs_tight xs εsum * subnormalConst) := by
          rw [hσ_sum]; ring

/-- **Argmax preservation** for the tight subnormal-tolerant error bound. -/
theorem fpSoftmax_preserves_argmax_pair_subnormal_tight
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs εsum)
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (istar j : Fin n)
    (h_gap : softmax (fun k => ((xs k).toVal : ℝ)) istar -
             softmax (fun k => ((xs k).toVal : ℝ)) j >
              softmaxErrorCoeff_tight xs εsum *
                (softmax (fun k => ((xs k).toVal : ℝ)) istar +
                 softmax (fun k => ((xs k).toVal : ℝ)) j) +
              2 * (subnormalSoftmaxAbs_tight xs εsum * subnormalConst)) :
    ((result j).toVal : ℝ) < ((result istar).toVal : ℝ) := by
  set sig : Fin n → ℝ := fun k => softmax (fun k' => ((xs k').toVal : ℝ)) k with hsig_def
  set c : ℝ := softmaxErrorCoeff_tight xs εsum with hc_def
  set a : ℝ := subnormalSoftmaxAbs_tight xs εsum * subnormalConst with ha_def
  have h_i : |((result istar).toVal : ℝ) - sig istar| ≤ c * sig istar + a :=
    fpSoftmaxOf_error_bound_subnormal_tight hn xs exps denom result εsum
      h_exp h_denom_close h_εsum_nn h_m_pos hd_m h_result istar
  have h_j : |((result j).toVal : ℝ) - sig j| ≤ c * sig j + a :=
    fpSoftmaxOf_error_bound_subnormal_tight hn xs exps denom result εsum
      h_exp h_denom_close h_εsum_nn h_m_pos hd_m h_result j
  have h_i_lo : sig istar - (c * sig istar + a) ≤ ((result istar).toVal : ℝ) := by
    have := (abs_le.mp h_i).1; linarith
  have h_j_hi : ((result j).toVal : ℝ) ≤ sig j + (c * sig j + a) := by
    have := (abs_le.mp h_j).2; linarith
  linarith [h_gap]

end ErrorBound

/-! ## `FpSoftmaxResult` Bundle

Packages a complete, valid FP softmax computation: inputs, intermediate FP values,
outputs, and all correctness witnesses. Lets downstream results take a single
`FpSoftmaxResult` argument instead of 10+ separate hypotheses.

Use `fpSoftmaxResult_apply_error_bound` to extract the componentwise bound from
a bundle. -/

section Bundle

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

/-- A complete, valid FP softmax computation for a given `xs`. -/
structure FpSoftmaxResult {n : ℕ} (xs : Fin n → FiniteFp) where
  /-- FP exp values: `fpExpFinite (xs i) = Fp.finite (exps i)`. -/
  exps : Fin n → FiniteFp
  /-- FP denominator: the summation result. -/
  denom : FiniteFp
  /-- FP softmax outputs. -/
  result : Fin n → FiniteFp
  /-- Relative error coefficient of the sum. -/
  εsum : ℝ
  εsum_nn : 0 ≤ εsum
  h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i)
  h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ))
  h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                   εsum * ∑ j, |((exps j).toVal : ℝ)|
  h_δ_lt : (η : ℝ) + εsum * (1 + (η : ℝ)) < 1
  hd_m : denom.m ≠ 0
  h_quot_nr : ∀ i, isNormalRange (((exps i).toVal : ℝ) / denom.toVal)
  h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i)

/-- Main error bound, applied to a bundled result. -/
theorem FpSoftmaxResult.error_bound {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResult xs) (i : Fin n) :
    |((r.result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff r.εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i :=
  fpSoftmaxOf_error_bound hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_exp_nr r.h_denom_close r.εsum_nn r.h_δ_lt r.hd_m r.h_quot_nr r.h_result i

/-- Sum-to-1 bound, applied to a bundled result. -/
theorem FpSoftmaxResult.sum_close_to_one {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResult xs) :
    |(∑ i, ((r.result i).toVal : ℝ)) - 1| ≤ softmaxErrorCoeff r.εsum :=
  fpSoftmax_sum_close_to_one hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_exp_nr r.h_denom_close r.εsum_nn r.h_δ_lt r.hd_m r.h_quot_nr r.h_result

/-- Argmax preservation, applied to a bundled result. -/
theorem FpSoftmaxResult.preserves_argmax_pair {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResult xs) (istar j : Fin n)
    (h_gap : softmax (fun k => ((xs k).toVal : ℝ)) istar -
             softmax (fun k => ((xs k).toVal : ℝ)) j >
              softmaxErrorCoeff r.εsum *
                (softmax (fun k => ((xs k).toVal : ℝ)) istar +
                 softmax (fun k => ((xs k).toVal : ℝ)) j)) :
    ((r.result j).toVal : ℝ) < ((r.result istar).toVal : ℝ) :=
  fpSoftmax_preserves_argmax_pair hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_exp_nr r.h_denom_close r.εsum_nn r.h_δ_lt r.hd_m r.h_quot_nr r.h_result istar j h_gap

/-- A subnormal-tolerant FP softmax computation for a given `xs`.

Unlike `FpSoftmaxResult`, drops the normal-range assumptions on exp outputs and
quotients in favor of the `h_S_margin` denominator-positivity witness.
Tolerates exp underflow to zero. -/
structure FpSoftmaxResultSubnormal {n : ℕ} (xs : Fin n → FiniteFp) where
  /-- FP exp values. -/
  exps : Fin n → FiniteFp
  /-- FP denominator. -/
  denom : FiniteFp
  /-- FP softmax outputs. -/
  result : Fin n → FiniteFp
  /-- Relative error coefficient of the sum. -/
  εsum : ℝ
  εsum_nn : 0 ≤ εsum
  h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i)
  h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                   εsum * ∑ j, |((exps j).toVal : ℝ)|
  h_S_margin : (1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) *
               (∑ j, Real.exp ((xs j).toVal : ℝ)) >
               2 * (1 + εsum) * (n : ℝ) * subnormalConst
  hd_m : denom.m ≠ 0
  h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i)

/-- Subnormal-tolerant error bound, applied to a bundled result. -/
theorem FpSoftmaxResultSubnormal.error_bound {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResultSubnormal xs) (i : Fin n) :
    |((r.result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      2 * softmaxErrorCoeff r.εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs xs r.εsum * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_denom_close r.εsum_nn r.h_S_margin r.hd_m r.h_result i

/-- Sum-close-to-1 bound, applied to a bundled subnormal-tolerant result. -/
theorem FpSoftmaxResultSubnormal.sum_close_to_one {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResultSubnormal xs) :
    |(∑ i, ((r.result i).toVal : ℝ)) - 1| ≤
      2 * softmaxErrorCoeff r.εsum +
      (n : ℝ) * (subnormalSoftmaxAbs xs r.εsum * subnormalConst) :=
  fpSoftmax_sum_close_to_one_subnormal hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_denom_close r.εsum_nn r.h_S_margin r.hd_m r.h_result

/-- Argmax preservation, applied to a bundled subnormal-tolerant result. -/
theorem FpSoftmaxResultSubnormal.preserves_argmax_pair {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResultSubnormal xs) (istar j : Fin n)
    (h_gap : softmax (fun k => ((xs k).toVal : ℝ)) istar -
             softmax (fun k => ((xs k).toVal : ℝ)) j >
              2 * softmaxErrorCoeff r.εsum *
                (softmax (fun k => ((xs k).toVal : ℝ)) istar +
                 softmax (fun k => ((xs k).toVal : ℝ)) j) +
              2 * (subnormalSoftmaxAbs xs r.εsum * subnormalConst)) :
    ((r.result j).toVal : ℝ) < ((r.result istar).toVal : ℝ) :=
  fpSoftmax_preserves_argmax_pair_subnormal hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_denom_close r.εsum_nn r.h_S_margin r.hd_m r.h_result istar j h_gap

/-- A tight subnormal-tolerant FP softmax computation for a given `xs`.

Variant of `FpSoftmaxResultSubnormal` using the minimal margin hypothesis
`h_m_pos : 0 < subnormalSoftmaxDenomMargin xs εsum`. The coefficients are
`xs`-dependent but tight — `softmaxErrorCoeff_tight` reduces to `softmaxErrorCoeff`
when `N·subnormalConst → 0`. -/
structure FpSoftmaxResultSubnormalTight {n : ℕ} (xs : Fin n → FiniteFp) where
  exps : Fin n → FiniteFp
  denom : FiniteFp
  result : Fin n → FiniteFp
  εsum : ℝ
  εsum_nn : 0 ≤ εsum
  h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i)
  h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                   εsum * ∑ j, |((exps j).toVal : ℝ)|
  h_m_pos : 0 < subnormalSoftmaxDenomMargin xs εsum
  hd_m : denom.m ≠ 0
  h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i)

/-- Tight error bound, applied to a bundled result. -/
theorem FpSoftmaxResultSubnormalTight.error_bound {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResultSubnormalTight xs) (i : Fin n) :
    |((r.result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff_tight xs r.εsum *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs r.εsum * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal_tight hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_denom_close r.εsum_nn r.h_m_pos r.hd_m r.h_result i

/-- Tight sum-close-to-1 bound, applied to a bundled result. -/
theorem FpSoftmaxResultSubnormalTight.sum_close_to_one {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResultSubnormalTight xs) :
    |(∑ i, ((r.result i).toVal : ℝ)) - 1| ≤
      softmaxErrorCoeff_tight xs r.εsum +
      (n : ℝ) * (subnormalSoftmaxAbs_tight xs r.εsum * subnormalConst) :=
  fpSoftmax_sum_close_to_one_subnormal_tight hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_denom_close r.εsum_nn r.h_m_pos r.hd_m r.h_result

/-- Tight argmax preservation, applied to a bundled result. -/
theorem FpSoftmaxResultSubnormalTight.preserves_argmax_pair {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResultSubnormalTight xs) (istar j : Fin n)
    (h_gap : softmax (fun k => ((xs k).toVal : ℝ)) istar -
             softmax (fun k => ((xs k).toVal : ℝ)) j >
              softmaxErrorCoeff_tight xs r.εsum *
                (softmax (fun k => ((xs k).toVal : ℝ)) istar +
                 softmax (fun k => ((xs k).toVal : ℝ)) j) +
              2 * (subnormalSoftmaxAbs_tight xs r.εsum * subnormalConst)) :
    ((r.result j).toVal : ℝ) < ((r.result istar).toVal : ℝ) :=
  fpSoftmax_preserves_argmax_pair_subnormal_tight hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_denom_close r.εsum_nn r.h_m_pos r.hd_m r.h_result istar j h_gap

/-- **Shifted tight error bound** applied to a bundled result. Produces a
purely `xs`-independent bound under `S ≥ 1` and the `xs`-free margin
hypothesis. -/
theorem FpSoftmaxResultSubnormalTight.shifted {n : ℕ} (hn : 0 < n)
    {xs : Fin n → FiniteFp} (r : FpSoftmaxResultSubnormalTight xs)
    (h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ))
    (h_margin_ind : (1 + r.εsum) * (n : ℝ) * subnormalConst <
                     1 - ((η : ℝ) + r.εsum * (1 + (η : ℝ))))
    (i : Fin n) :
    |((r.result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + r.εsum * (1 + (η : ℝ))) +
        (1 + r.εsum) * (n : ℝ) * subnormalConst) /
       ((1 - ((η : ℝ) + r.εsum * (1 + (η : ℝ)))) -
        (1 + r.εsum) * (n : ℝ) * subnormalConst)) *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      (1 + (1 + (η : ℝ)) /
        ((1 - ((η : ℝ) + r.εsum * (1 + (η : ℝ)))) -
         (1 + r.εsum) * (n : ℝ) * subnormalConst)) * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal_tight_shifted hn xs r.exps r.denom r.result r.εsum
    r.h_exp r.h_denom_close r.εsum_nn h_S_ge_one h_margin_ind r.hd_m r.h_result i

end Bundle

/-! ## Pre-shift Helpers: `fpMax` and `fpSoftmaxShift` -/

section Shift

variable [FloatFormat] [RModeExec]

/-- Max of a `Fin n → FiniteFp` via `Finset.sup'`, using the FP order. -/
noncomputable def fpMax {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n) : FiniteFp :=
  (Finset.univ : Finset (Fin n)).sup' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (fun i => (xs i))

/-- `fpSoftmaxShift xs c i = fpSubFinite (xs i) c` — subtracts `c` from each input. -/
def fpSoftmaxShift {n : ℕ} (xs : Fin n → FiniteFp) (c : FiniteFp) : Fin n → Fp :=
  fun i => fpSubFinite (xs i) c

@[simp] theorem fpSoftmaxShift_apply {n : ℕ} (xs : Fin n → FiniteFp) (c : FiniteFp) (i : Fin n) :
    fpSoftmaxShift xs c i = fpSubFinite (xs i) c := rfl

end Shift

/-! ## End-to-End Pipeline

`fpSoftmax_end_to_end_error_bound` takes raw inputs `xs` (not pre-shifted) and
produces the `xs`-independent tight subnormal-tolerant bound. The shift step
`xs' i = fpSubFinite (xs i) (fpMax xs hn)` is assumed exact via `h_shift_exact`
— this typically holds under Sterbenz when the max is close in magnitude to
each input, and is the regime the subtract-max trick was designed for.

Users needing to track the shift rounding error separately should combine
`fpSoftmaxOf_error_bound_subnormal_tight_shifted` directly with their own
analysis of `fpSubFinite`. -/

section EndToEnd

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

/-- The FP-order max `fpMax xs hn` is attained at some index `i₀`. -/
private lemma fpMax_attained {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n) :
    ∃ i₀ : Fin n, fpMax xs hn = xs i₀ := by
  have h_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  obtain ⟨i₀, _, h_max⟩ := Finset.exists_max_image Finset.univ xs h_ne
  refine ⟨i₀, le_antisymm ?_ ?_⟩
  · exact Finset.sup'_le h_ne xs (fun j _ => h_max j (Finset.mem_univ j))
  · exact Finset.le_sup' xs (Finset.mem_univ i₀)

/-- **End-to-end softmax error bound**: raw `xs` input, with exact shift
witness `xs'`. Conclusion is purely `xs`-independent.

Takes an explicit shifted-input function `xs' : Fin n → FiniteFp` satisfying
`(xs' j).toVal = (xs j).toVal - (fpMax xs hn).toVal`. In practice the user
computes `xs' i` from `fpSoftmaxShift xs (fpMax xs hn) i` plus a finiteness
witness; exactness comes from Sterbenz or from the caller's own analysis.

The FP pipeline `xs' → exps → sum → result` is identical to the one in
`fpSoftmaxOf_error_bound_subnormal_tight_shifted`, so `exps`, `denom`, and
`result` plus their witnesses are standard. -/
theorem fpSoftmax_end_to_end_error_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp) (denom : FiniteFp)
    (result : Fin n → FiniteFp) (εsum : ℝ)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    (h_denom_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                     εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (h_εsum_nn : 0 ≤ εsum)
    (h_margin_ind : (1 + εsum) * (n : ℝ) * subnormalConst <
                     1 - ((η : ℝ) + εsum * (1 + (η : ℝ))))
    (hd_m : denom.m ≠ 0)
    (h_result : ∀ i, fpDivFinite (exps i) denom = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + εsum * (1 + (η : ℝ))) +
        (1 + εsum) * (n : ℝ) * subnormalConst) /
       ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
        (1 + εsum) * (n : ℝ) * subnormalConst)) *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      (1 + (1 + (η : ℝ)) /
        ((1 - ((η : ℝ) + εsum * (1 + (η : ℝ)))) -
         (1 + εsum) * (n : ℝ) * subnormalConst)) * subnormalConst := by
  -- The softmax on `xs'` matches the softmax on `xs` via `shift`.
  have h_fun_eq :
      (fun j => ((xs' j).toVal : ℝ)) =
      shift (fun j => ((xs j).toVal : ℝ)) ((fpMax xs hn).toVal : ℝ) := by
    funext j; exact h_shift_exact j
  have h_sm_eq : softmax (fun j => ((xs' j).toVal : ℝ)) i =
                 softmax (fun j => ((xs j).toVal : ℝ)) i := by
    rw [h_fun_eq]; exact softmax_shift_eq _ _ _
  -- Σ exp((xs' j).toVal) ≥ 1: argmax i₀ gives (xs' i₀).toVal = 0.
  have h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs' j).toVal : ℝ) := by
    obtain ⟨i₀, h_i₀⟩ := fpMax_attained xs hn
    have h_zero : ((xs' i₀).toVal : ℝ) = 0 := by
      rw [h_shift_exact i₀]
      have : ((fpMax xs hn).toVal : ℝ) = ((xs i₀).toVal : ℝ) := by rw [h_i₀]
      linarith
    have h_exp_zero : Real.exp ((xs' i₀).toVal : ℝ) = 1 := by
      rw [h_zero]; exact Real.exp_zero
    calc (1 : ℝ) = Real.exp ((xs' i₀).toVal : ℝ) := h_exp_zero.symm
      _ ≤ ∑ j, Real.exp ((xs' j).toVal : ℝ) :=
        Finset.single_le_sum
          (f := fun j => Real.exp ((xs' j).toVal : ℝ))
          (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i₀)
  -- Apply the shifted tight bound on `xs'`, then rewrite the softmax.
  have h_main := fpSoftmaxOf_error_bound_subnormal_tight_shifted hn xs' exps denom
    result εsum h_exp h_denom_close h_εsum_nn h_S_ge_one h_margin_ind hd_m h_result i
  rw [h_sm_eq] at h_main
  exact h_main

end EndToEnd

/-! ## Concrete Adapters

Demonstrates plugging `FpSumBound.ofNaive` into the softmax error framework.
These theorems make the library usable end-to-end with no manual bridging:
given a `NaiveSum` witness on the `exps`, you get a softmax error bound directly. -/

section Demo

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]

/-- **NaiveSum demo** (tight subnormal-tolerant): a `NaiveSum` witness on the
`exps` composes with `fpSoftmaxOf_error_bound_subnormal_tight_of_sumBound` via
`FpSumBound.ofNaive`. The resulting `sum.relErr = (1+η)^(trace.toPairwise.depth) - 1`,
with `trace.toPairwise.depth + 1 = n` (see `NaiveSum.toPairwise_depth`). -/
theorem fpSoftmax_naiveSum_error_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    {sumResult : FiniteFp}
    (trace : FpSum.NaiveSum (List.ofFn exps) sumResult)
    (hnr : trace.AllNormalRange (R := ℝ))
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs
      (FpSum.FpSumBound.ofNaive exps trace hnr).relErr)
    (hd_m : sumResult.m ≠ 0)
    (result : Fin n → FiniteFp)
    (h_result : ∀ i, fpDivFinite (exps i) sumResult = Fp.finite (result i))
    (i : Fin n) :
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff_tight xs
        (FpSum.FpSumBound.ofNaive exps trace hnr).relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs
        (FpSum.FpSumBound.ofNaive exps trace hnr).relErr * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal_tight_of_sumBound hn xs exps
    (FpSum.FpSumBound.ofNaive exps trace hnr) result
    h_exp h_m_pos hd_m h_result i

/-- **NaiveSum demo** (shifted tight, xs-independent bound): same as
`fpSoftmax_naiveSum_error_bound` but with the xs-independent shifted variant.
Requires `S ≥ 1` (e.g. after subtract-max) and an xs-free margin. -/
theorem fpSoftmax_naiveSum_error_bound_shifted
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    {sumResult : FiniteFp}
    (trace : FpSum.NaiveSum (List.ofFn exps) sumResult)
    (hnr : trace.AllNormalRange (R := ℝ))
    (h_S_ge_one : 1 ≤ ∑ j, Real.exp ((xs j).toVal : ℝ))
    (h_margin_ind :
      (1 + (FpSum.FpSumBound.ofNaive exps trace hnr).relErr) * (n : ℝ) *
          subnormalConst <
        1 - ((η : ℝ) +
          (FpSum.FpSumBound.ofNaive exps trace hnr).relErr * (1 + (η : ℝ))))
    (hd_m : sumResult.m ≠ 0)
    (result : Fin n → FiniteFp)
    (h_result : ∀ i, fpDivFinite (exps i) sumResult = Fp.finite (result i))
    (i : Fin n) :
    letI sum := FpSum.FpSumBound.ofNaive exps trace hnr
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      (((η : ℝ)^2 + 2 * (η : ℝ) + ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * subnormalConst) /
       ((1 - ((η : ℝ) + sum.relErr * (1 + (η : ℝ)))) -
        (1 + sum.relErr) * (n : ℝ) * subnormalConst)) *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      (1 + (1 + (η : ℝ)) /
        ((1 - ((η : ℝ) + sum.relErr * (1 + (η : ℝ)))) -
         (1 + sum.relErr) * (n : ℝ) * subnormalConst)) * subnormalConst := by
  have hsum_bound : |(sumResult.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                    (FpSum.FpSumBound.ofNaive exps trace hnr).relErr *
                      ∑ j, |((exps j).toVal : ℝ)| :=
    (FpSum.FpSumBound.ofNaive exps trace hnr).h_bound
  exact fpSoftmaxOf_error_bound_subnormal_tight_shifted hn xs exps sumResult result
    (FpSum.FpSumBound.ofNaive exps trace hnr).relErr
    h_exp hsum_bound
    (FpSum.FpSumBound.ofNaive exps trace hnr).h_relErr_nn
    h_S_ge_one h_margin_ind hd_m h_result i

/-- **Kahan demo** (tight subnormal-tolerant): a Kahan compensated-summation
`Trace` on `exps` composes with the softmax framework via
`FpSumBound.ofKahanTrace`. The resulting `sum.relErr = 2η + n·η²`. -/
theorem fpSoftmax_kahanSum_error_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
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
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs
      (FpSum.FpSumBound.ofKahanTrace exps trace
        hinit_sum hinit_comp hexact hnr hM).relErr)
    (hd_m : final.sum.m ≠ 0)
    (result : Fin n → FiniteFp)
    (h_result : ∀ i, fpDivFinite (exps i) final.sum = Fp.finite (result i))
    (i : Fin n) :
    letI sum := FpSum.FpSumBound.ofKahanTrace exps trace
                  hinit_sum hinit_comp hexact hnr hM
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff_tight xs sum.relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs sum.relErr * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal_tight_of_sumBound hn xs exps
    (FpSum.FpSumBound.ofKahanTrace exps trace
      hinit_sum hinit_comp hexact hnr hM) result
    h_exp h_m_pos hd_m h_result i

/-- **Neumaier demo** (loose): a Neumaier `NTrace` on `exps` composes with the
softmax framework via `FpSumBound.ofNeumaierTrace`. See the `NeumaierAdapter`
docstring in `FpSum.lean`: the bound is loose because `FpSumBound` cannot
expose the compensator. For tight bounds prefer `fpSoftmax_kahanSum_error_bound`. -/
theorem fpSoftmax_neumaierSum_error_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
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
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs
      (FpSum.FpSumBound.ofNeumaierTrace exps trace
        hinit_sum hinit_comp hnr hM).relErr)
    (hd_m : final.sum.m ≠ 0)
    (result : Fin n → FiniteFp)
    (h_result : ∀ i, fpDivFinite (exps i) final.sum = Fp.finite (result i))
    (i : Fin n) :
    letI sum := FpSum.FpSumBound.ofNeumaierTrace exps trace
                  hinit_sum hinit_comp hnr hM
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff_tight xs sum.relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs sum.relErr * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal_tight_of_sumBound hn xs exps
    (FpSum.FpSumBound.ofNeumaierTrace exps trace
      hinit_sum hinit_comp hnr hM) result
    h_exp h_m_pos hd_m h_result i

/-- **Compensated-Neumaier demo** (tight): Neumaier via
`FpSumBoundCompensated.ofNeumaierTrace` + `compensateAndRound`. Unlike
`fpSoftmax_neumaierSum_error_bound` (loose, discards the compensator), this
preserves Neumaier's `O(n²η²)` accuracy at the cost of one extra
`fpAdd(sum, comp)` step. Final `relErr = η + O(n²η²)` — Kahan-comparable. -/
theorem fpSoftmax_neumaierCompensated_error_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp) (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
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
    (h_m_pos : 0 < subnormalSoftmaxDenomMargin xs
      ((FpSum.FpSumBoundCompensated.ofNeumaierTrace exps trace
          hinit_sum hinit_comp hnr hM).compensateAndRound hadd hnr_add).relErr)
    (hd_m : combinedResult.m ≠ 0)
    (result : Fin n → FiniteFp)
    (h_result : ∀ i, fpDivFinite (exps i) combinedResult = Fp.finite (result i))
    (i : Fin n) :
    letI sum := (FpSum.FpSumBoundCompensated.ofNeumaierTrace exps trace
                   hinit_sum hinit_comp hnr hM).compensateAndRound hadd hnr_add
    |((result i).toVal : ℝ) - softmax (fun j => ((xs j).toVal : ℝ)) i| ≤
      softmaxErrorCoeff_tight xs sum.relErr *
        softmax (fun j => ((xs j).toVal : ℝ)) i +
      subnormalSoftmaxAbs_tight xs sum.relErr * subnormalConst :=
  fpSoftmaxOf_error_bound_subnormal_tight_of_sumBound hn xs exps
    ((FpSum.FpSumBoundCompensated.ofNeumaierTrace exps trace
        hinit_sum hinit_comp hnr hM).compensateAndRound hadd hnr_add) result
    h_exp h_m_pos hd_m h_result i

end Demo

end Softmax
