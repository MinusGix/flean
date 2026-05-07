import Flean.Operations.BackwardErrorCore
import Flean.Operations.DotProduct
import Flean.Operations.Horner
import Flean.Operations.HornerFMA
import Flean.Operations.FpSum
import Flean.Operations.FpDotProduct

/-!
# Backward Error — Floating-Point Instances

Concrete backward error theorems for floating-point algorithms, building on
the generic framework in `BackwardErrorCore.lean`.

## Main results

- `dp_backward_error`: dot product backward error `|μᵢ| ≤ (1+η)^n - 1`
- `dp_backward_error_gamma`: dot product backward error `|μᵢ| ≤ γ_n`
- `horner_backward_error`: Horner coefficient perturbation `|μᵢ| ≤ (1+η)^{2n} - 1`
- `horner_compose_round`: Horner + scalar rounding, `|μᵢ| ≤ (1+η)^{2n+1} - 1`

## Linking lemmas

- `hornerPoly_eq_fin_sum`: `hornerPoly cs 0 x = Σ cs[i] · x^{n-1-i}`
- `hornerPoly_abs_eq_fin_sum`: absolute version
- `abs_horner_sum_eq`: `Σ|cᵢ|·|x|^k = Σ|cᵢ·x^k|`
-/

namespace BackwardError

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ### Dot Product Backward Error -/

/-- **Backward error for dot product**: the computed dot product equals the exact
    dot product of slightly perturbed input pairs:

    `fl(x · y) = Σ(1 + μᵢ) · xᵢyᵢ` where `|μᵢ| ≤ (1+η)^n - 1`.

    This attributes all backward error to the products `xᵢyᵢ`. The perturbation
    bound `(1+η)^n - 1` is the same as the forward error constant from
    `DotProduct.dp_error_bound` (Higham's Theorem 3.1). -/
theorem dp_backward_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DotProduct.DPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    ∃ mu : Fin pairs.length → R,
      (final.toVal : R) =
        ∑ i : Fin pairs.length,
          (1 + mu i) * ((pairs.get i).1.toVal (R := R) * (pairs.get i).2.toVal) ∧
      ∀ i, |mu i| ≤ (1 + η) ^ pairs.length - 1 :=
  backwardResult_of_forward_bilinear_bound
    pairs (fun p => p.1.toVal) (fun p => p.2.toVal)
    (final.toVal : R) ((1 + η) ^ pairs.length - 1)
    (by have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
        exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith)))
    (DotProduct.dp_error_bound trace hinit hnr)

/-- **Backward error for dot product (γ form)**: `|μᵢ| ≤ γ_n = nη/(1-nη)`. -/
theorem dp_backward_error_gamma
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DotProduct.DPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (pairs.length : R) * η < 1) :
    ∃ mu : Fin pairs.length → R,
      (final.toVal : R) =
        ∑ i : Fin pairs.length,
          (1 + mu i) * ((pairs.get i).1.toVal (R := R) * (pairs.get i).2.toVal) ∧
      ∀ i, |mu i| ≤ gamma_n (R := R) pairs.length := by
  obtain ⟨mu, heq, hbnd⟩ := dp_backward_error trace hinit hnr
  exact ⟨mu, heq, fun i => le_trans (hbnd i) (pow_sub_one_le_gamma pairs.length hsmall)⟩

/-- **Structured backward error for dot product**: returns a `BackwardResult`
    on the **product space** with componentwise relative gauge.

    `fl(x·y) = Σ(1+μᵢ)·xᵢyᵢ` where `max_i |μᵢ| ≤ (1+η)^n - 1`. -/
noncomputable def dp_backward_result
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (hpairs : 0 < pairs.length)
    (trace : DotProduct.DPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    BackwardResult
      (componentwiseRelGauge pairs.length hpairs)
      (fun w => ∑ i : Fin pairs.length, w i)
      (fun i => (pairs.get i).1.toVal (R := R) * (pairs.get i).2.toVal)
      (final.toVal : R) := by
  have hfwd := DotProduct.dp_error_bound trace hinit hnr
  rw [list_map_sum_eq_finset_sum', list_map_sum_eq_finset_sum'] at hfwd
  exact backwardResult_struct_of_forward_fin_bound hpairs _ _ _
    (by have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
        exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith)))
    hfwd

/-! ### Horner Polynomial ↔ Fin Sum -/

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- Helper: `hornerPoly cs acc x = acc * x^n + hornerPoly cs 0 x`. -/
private theorem hornerPoly_acc_eq (cs : List R) (acc x : R) :
    Horner.hornerPoly cs acc x =
      acc * x ^ cs.length + Horner.hornerPoly cs 0 x := by
  induction cs generalizing acc with
  | nil => simp [Horner.hornerPoly]
  | cons c cs ih =>
    simp only [Horner.hornerPoly, zero_mul, zero_add, List.length_cons]
    rw [ih (acc * x + c), ih c]
    ring

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- `hornerPoly cs 0 x` as a Finset sum over `Fin cs.length`. -/
theorem hornerPoly_eq_fin_sum (cs : List R) (x : R) :
    Horner.hornerPoly cs 0 x =
      ∑ i : Fin cs.length, cs.get i * x ^ (cs.length - 1 - i.val) := by
  induction cs with
  | nil => simp [Horner.hornerPoly]
  | cons c cs ih =>
    simp only [Horner.hornerPoly, zero_mul, zero_add, List.length_cons]
    rw [hornerPoly_acc_eq cs c x, ih, add_comm, Fin.sum_univ_succ]
    simp only [List.get_cons_zero, Fin.val_zero, Nat.sub_zero]
    rw [show c * x ^ cs.length = c * x ^ (cs.length + 1 - 1) by
      simp]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val < cs.length := i.isLt
    have hexp : cs.length - 1 - i.val = cs.length + 1 - 1 - i.succ.val := by
      simp [Fin.val_succ]
      omega
    rw [hexp]
    rfl

omit [FloatFormat] [IsStrictOrderedRing R] [FloorRing R] in
/-- Absolute version: `hornerPoly |cs| 0 |x| = Σ |cs[i]| · |x|^{n-1-i}`. -/
theorem hornerPoly_abs_eq_fin_sum (cs : List R) (x : R) :
    Horner.hornerPoly (cs.map (fun c => |c|)) 0 |x| =
      ∑ i : Fin cs.length, |cs.get i| * |x| ^ (cs.length - 1 - i.val) := by
  induction cs with
  | nil => simp [Horner.hornerPoly]
  | cons c cs ih =>
    simp only [Horner.hornerPoly, zero_mul, zero_add, List.map_cons, List.length_cons]
    rw [hornerPoly_acc_eq, ih, add_comm, Fin.sum_univ_succ]
    simp only [List.get_cons_zero, Fin.val_zero, Nat.sub_zero, List.length_map]
    rw [show |c| * |x| ^ cs.length = |c| * |x| ^ (cs.length + 1 - 1) by simp]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hexp : cs.length - 1 - i.val = cs.length + 1 - 1 - i.succ.val := by
      simp [Fin.val_succ]; omega
    rw [hexp]; rfl

omit [FloatFormat] [FloorRing R] in
/-- `Σ |cs[i]| · |x|^k = Σ |cs[i] · x^k|`. -/
theorem abs_horner_sum_eq (cs : List R) (x : R) :
    (∑ i : Fin cs.length, |cs.get i| * |x| ^ (cs.length - 1 - i.val)) =
      ∑ i : Fin cs.length, |cs.get i * x ^ (cs.length - 1 - i.val)| := by
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_mul, abs_pow]

/-! ### Horner Backward Error -/

/-- **Backward error for Horner evaluation**: the computed polynomial evaluation
    equals a polynomial with perturbed coefficients evaluated at the exact `x`:

    `fl(p(x)) = Σ(1 + μᵢ) · cᵢ · x^{n-1-i}` where `|μᵢ| ≤ (1+η)^{2n} - 1`.

    Requires `init = 0` (standard polynomial evaluation, not accumulated). -/
theorem horner_backward_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : Horner.HornerTrace x coeffs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    ∃ mu : Fin coeffs.length → R,
      (final.toVal : R) =
        ∑ i : Fin coeffs.length,
          (1 + mu i) * ((coeffs.get i).toVal (R := R) *
            (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)) ∧
      ∀ i, |mu i| ≤ (1 + η) ^ (2 * coeffs.length) - 1 := by
  -- Forward error bound from Horner.horner_error_bound
  have hfwd := Horner.horner_error_bound trace hnr
  -- Simplify with init = 0
  simp only [hinit, abs_zero] at hfwd
  -- Rewrite the value-side hornerPoly to a Fin sum
  set vfun : Fin coeffs.length → R :=
    fun i => (coeffs.get i).toVal (R := R) *
      (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)
  -- Restate the forward bound using vfun
  have hval : Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
      ∑ i, vfun i := by
    calc
      Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
          ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            (coeffs.map (fun c => c.toVal (R := R))).get i *
              (x.toVal (R := R)) ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            exact hornerPoly_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, vfun i := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i
          simp
        · intro i _
          simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map]
  have habs : Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
      ∑ i, |vfun i| := by
    calc
      Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
          ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            |(coeffs.map (fun c => c.toVal (R := R))).get i| *
              |x.toVal (R := R)| ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            simpa [List.map_map]
              using hornerPoly_abs_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, |vfun i| := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i
          simp
        · intro i _
          simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map, abs_mul, abs_pow]
  have hfwd' : |(final.toVal : R) - ∑ i, vfun i| ≤
      ((1 + η) ^ (2 * coeffs.length) - 1) * ∑ i, |vfun i| := by
    rw [← hval, ← habs]; exact hfwd
  -- Apply the Fin-indexed bridge
  have heps_nn : (0 : R) ≤ (1 + η) ^ (2 * coeffs.length) - 1 := by
    have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
    exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith))
  exact backwardResult_of_forward_fin_bound coeffs.length vfun
    (final.toVal : R) _ heps_nn hfwd'

/-- **Structured backward error for Horner evaluation**: returns a `BackwardResult`
    on the **coefficient space** with componentwise relative gauge.

    The computed polynomial evaluation equals the exact evaluation of a polynomial
    with perturbed coefficients: `fl(p(x)) = p̃(x)` where `c̃ᵢ = (1+μᵢ)·cᵢ`
    and `max_i |μᵢ| ≤ (1+η)^{2n} - 1`.

    The function maps coefficient vectors to polynomial values at fixed `x`. -/
noncomputable def horner_backward_result
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (hcoeffs : 0 < coeffs.length)
    (trace : Horner.HornerTrace x coeffs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    BackwardResult
      (componentwiseRelGauge coeffs.length hcoeffs)
      (fun c => ∑ i : Fin coeffs.length,
        c i * (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val))
      (fun i => (coeffs.get i).toVal)
      (final.toVal : R) := by
  -- Get the forward error bound in Fin-indexed form
  have hfwd := Horner.horner_error_bound trace hnr
  simp only [hinit, abs_zero] at hfwd
  set vfun : Fin coeffs.length → R :=
    fun i => (coeffs.get i).toVal (R := R) *
      (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)
  -- Restate using Fin sums (from horner_backward_error proof)
  have hval : Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
      ∑ i, vfun i := by
    calc _ = ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            (coeffs.map (fun c => c.toVal (R := R))).get i *
              (x.toVal (R := R)) ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) :=
            hornerPoly_eq_fin_sum _ _
      _ = ∑ i : Fin coeffs.length, vfun i := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i; simp
        · intro i _; simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map]
  have habs : Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
      ∑ i, |vfun i| := by
    calc _ = ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            |(coeffs.map (fun c => c.toVal (R := R))).get i| *
              |x.toVal (R := R)| ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            simpa [List.map_map]
              using hornerPoly_abs_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, |vfun i| := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i; simp
        · intro i _; simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map, abs_mul, abs_pow]
  have hfwd' : |(final.toVal : R) - ∑ i, vfun i| ≤
      ((1 + η) ^ (2 * coeffs.length) - 1) * ∑ i, |vfun i| := by
    rw [← hval, ← habs]; exact hfwd
  have heps_nn : (0 : R) ≤ (1 + η) ^ (2 * coeffs.length) - 1 := by
    have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
    exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith))
  exact backwardResult_struct_of_forward_weighted_bound hcoeffs
    (fun i => (coeffs.get i).toVal) (fun i => (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val))
    _ _ heps_nn hfwd'

/-- **Horner + scalar rounding composition**: if Horner evaluation produces a
    backward error of `(1+η)^{2n} - 1` on coefficients, and one more rounding
    introduces a factor `(1+δ)` with `|δ| ≤ η`, the composed backward error
    on coefficients is `(1+η)^{2n+1} - 1`.

    This demonstrates `compose_scalar_weighted_sum` on a concrete algorithm.
    A typical use case: `fl(c · p(x)) = (1+δ) · fl(p(x))` where `fl(p(x))`
    is computed by Horner's method. -/
noncomputable def horner_compose_round
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (hcoeffs : 0 < coeffs.length)
    (trace : Horner.HornerTrace x coeffs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (delta : R) (hdelta : |delta| ≤ η) :
    BackwardResult
      (componentwiseRelGauge coeffs.length hcoeffs)
      (fun c => ∑ i : Fin coeffs.length,
        c i * (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val))
      (fun i => (coeffs.get i).toVal)
      ((1 + delta) * (final.toVal : R)) :=
  (horner_backward_result (R := R) hcoeffs trace hinit hnr).compose_scalar_weighted_sum
    hcoeffs delta η hdelta (by simp only [FloatFormat.hEps_def]; positivity)

/-- The epsilon bound for `horner_compose_round` is `(1+η)^{2n+1} - 1`:
    `ε_A + η + ε_A·η = ((1+η)^{2n} - 1)·(1+η) + η = (1+η)^{2n+1} - 1`.

    Note: stated as `≤` because the internal eps comes from a tactic proof
    and doesn't reduce definitionally. The bound is tight (equality holds). -/
theorem horner_compose_round_eps
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (hcoeffs : 0 < coeffs.length)
    (trace : Horner.HornerTrace x coeffs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (delta : R) (hdelta : |delta| ≤ η) :
    (horner_compose_round hcoeffs trace hinit hnr delta hdelta).eps =
    (1 + η) ^ (2 * coeffs.length + 1) - 1 := by
  -- compose_scalar_weighted_sum sets eps = brA.eps + η + brA.eps * η
  -- horner_compose_round unfolds to (horner_backward_result ...).compose_scalar_weighted_sum ...
  -- but horner_backward_result is a tactic proof that doesn't reduce.
  -- Instead, use the structure directly:
  show ((horner_backward_result (R := R) hcoeffs trace hinit hnr).eps + η +
    (horner_backward_result (R := R) hcoeffs trace hinit hnr).eps * η) =
    (1 + η) ^ (2 * coeffs.length + 1) - 1
  -- horner_backward_result.eps = (1+η)^{2n} - 1, proved via the forward error bound
  -- We need to know this value. Extract it:
  have heps : (horner_backward_result (R := R) hcoeffs trace hinit hnr).eps =
      (1 + η) ^ (2 * coeffs.length) - 1 := by
    simp only [horner_backward_result, backwardResult_struct_of_forward_weighted_bound]
  rw [heps, pow_succ]; ring

/-! ### HornerFMA Backward Error -/

/-- **Backward error for FMA-Horner evaluation**: with one rounding per step
    instead of two, the exponent halves to `(1+η)^n - 1`.

    `fl(p(x)) = Σ(1 + μᵢ) · cᵢ · x^{n-1-i}` where `|μᵢ| ≤ (1+η)^n - 1`. -/
theorem hornerFMA_backward_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : HornerFMA.FMATrace x coeffs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    ∃ mu : Fin coeffs.length → R,
      (final.toVal : R) =
        ∑ i : Fin coeffs.length,
          (1 + mu i) * ((coeffs.get i).toVal (R := R) *
            (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)) ∧
      ∀ i, |mu i| ≤ (1 + η) ^ coeffs.length - 1 := by
  have hfwd := HornerFMA.fma_horner_error_bound trace hnr
  simp only [hinit, abs_zero] at hfwd
  set vfun : Fin coeffs.length → R :=
    fun i => (coeffs.get i).toVal (R := R) *
      (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)
  have hval : Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
      ∑ i, vfun i := by
    calc
      Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
          ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            (coeffs.map (fun c => c.toVal (R := R))).get i *
              (x.toVal (R := R)) ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            exact hornerPoly_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, vfun i := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i; simp
        · intro i _
          simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map]
  have habs : Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
      ∑ i, |vfun i| := by
    calc
      Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
          ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            |(coeffs.map (fun c => c.toVal (R := R))).get i| *
              |x.toVal (R := R)| ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            simpa [List.map_map]
              using hornerPoly_abs_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, |vfun i| := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i; simp
        · intro i _
          simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map, abs_mul, abs_pow]
  have hfwd' : |(final.toVal : R) - ∑ i, vfun i| ≤
      ((1 + η) ^ coeffs.length - 1) * ∑ i, |vfun i| := by
    rw [← hval, ← habs]; exact hfwd
  have heps_nn : (0 : R) ≤ (1 + η) ^ coeffs.length - 1 := by
    have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
    exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith))
  exact backwardResult_of_forward_fin_bound coeffs.length vfun
    (final.toVal : R) _ heps_nn hfwd'

/-- **Structured backward error for FMA-Horner**: returns a `BackwardResult`
    on the **coefficient space** with componentwise relative gauge.

    `fl(p(x)) = p̃(x)` where `c̃ᵢ = (1+μᵢ)·cᵢ` and `max_i |μᵢ| ≤ (1+η)^n - 1`. -/
noncomputable def hornerFMA_backward_result
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (hcoeffs : 0 < coeffs.length)
    (trace : HornerFMA.FMATrace x coeffs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    BackwardResult
      (componentwiseRelGauge coeffs.length hcoeffs)
      (fun c => ∑ i : Fin coeffs.length,
        c i * (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val))
      (fun i => (coeffs.get i).toVal)
      (final.toVal : R) := by
  have hfwd := HornerFMA.fma_horner_error_bound trace hnr
  simp only [hinit, abs_zero] at hfwd
  set vfun : Fin coeffs.length → R :=
    fun i => (coeffs.get i).toVal (R := R) *
      (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)
  have hval : Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
      ∑ i, vfun i := by
    calc _ = ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            (coeffs.map (fun c => c.toVal (R := R))).get i *
              (x.toVal (R := R)) ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) :=
            hornerPoly_eq_fin_sum _ _
      _ = ∑ i : Fin coeffs.length, vfun i := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i; simp
        · intro i _; simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map]
  have habs : Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
      ∑ i, |vfun i| := by
    calc _ = ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            |(coeffs.map (fun c => c.toVal (R := R))).get i| *
              |x.toVal (R := R)| ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            simpa [List.map_map]
              using hornerPoly_abs_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, |vfun i| := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i; simp
        · intro i _; simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map, abs_mul, abs_pow]
  have hfwd' : |(final.toVal : R) - ∑ i, vfun i| ≤
      ((1 + η) ^ coeffs.length - 1) * ∑ i, |vfun i| := by
    rw [← hval, ← habs]; exact hfwd
  have heps_nn : (0 : R) ≤ (1 + η) ^ coeffs.length - 1 := by
    have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
    exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith))
  exact backwardResult_struct_of_forward_weighted_bound hcoeffs
    (fun i => (coeffs.get i).toVal) (fun i => (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val))
    _ _ heps_nn hfwd'

/-! ### FpSumBound → Backward Error -/

/-- **Backward error for any FpSumBound**: every bundled FP summation immediately
    yields a Wilkinson-style backward result. The computed sum equals the exact
    sum of perturbed inputs `x'_i = (1 + μ_i) · x_i` with `|μ_i| ≤ b.relErr`.

    Generic — works for naive, pairwise, Kahan, Neumaier, or any future summation
    algorithm that produces an `FpSumBound`. -/
theorem FpSumBound_backward_error
    {n : ℕ} {xs : Fin n → FiniteFp} (b : FpSum.FpSumBound xs R) :
    ∃ mu : Fin n → R,
      (b.result.toVal : R) =
        ∑ i : Fin n, (1 + mu i) * ((xs i).toVal : R) ∧
      ∀ i, |mu i| ≤ b.relErr :=
  backwardResult_of_forward_fin_bound n
    (fun i => ((xs i).toVal : R)) (b.result.toVal : R) b.relErr
    b.h_relErr_nn b.h_bound

/-- **Structured backward result for any FpSumBound**: returns a `BackwardResult`
    on the input space `Fin n → R` with componentwise relative gauge.

    `fl(Σ xs) = Σ x'_i` where `max_i |μ_i| ≤ b.relErr` and `x'_i = (1+μ_i)·xs_i.toVal`. -/
noncomputable def FpSumBound.toBackwardResult
    {n : ℕ} (hn : 0 < n) {xs : Fin n → FiniteFp} (b : FpSum.FpSumBound xs R) :
    BackwardResult
      (componentwiseRelGauge n hn)
      (fun w => ∑ i : Fin n, w i)
      (fun i => ((xs i).toVal : R))
      ((b.result.toVal : R)) :=
  backwardResult_struct_of_forward_fin_bound hn
    (fun i => ((xs i).toVal : R)) (b.result.toVal : R) b.relErr
    b.h_relErr_nn b.h_bound

/-! ### FpDotProductBound → Backward Error -/

/-- **Backward error for any FpDotProductBound**: every bundled FP dot product
    yields a backward result attributing all error to the products. The computed
    dot product equals `Σ (1 + μ_i) · xs_i · ys_i` with `|μ_i| ≤ b.relErr`.

    Generic — works for sequential dot product, FMA dot product, or any future
    algorithm producing an `FpDotProductBound`. -/
theorem FpDotProductBound_backward_error
    {n : ℕ} {xs ys : Fin n → FiniteFp}
    (b : FpDotProduct.FpDotProductBound xs ys R) :
    ∃ mu : Fin n → R,
      (b.result.toVal : R) =
        ∑ i : Fin n, (1 + mu i) *
          (((xs i).toVal : R) * ((ys i).toVal : R)) ∧
      ∀ i, |mu i| ≤ b.relErr :=
  backwardResult_of_forward_fin_bound n
    (fun i => ((xs i).toVal : R) * ((ys i).toVal : R))
    (b.result.toVal : R) b.relErr b.h_relErr_nn b.h_bound

/-- **Structured backward result for any FpDotProductBound**: returns a
    `BackwardResult` on the **product space** `Fin n → R` with componentwise
    relative gauge.

    `fl(x · y) = Σ p'_i` where `p'_i = (1+μ_i)·xs_i.toVal·ys_i.toVal` and
    `max_i |μ_i| ≤ b.relErr`. Mirrors `dp_backward_result`. -/
noncomputable def FpDotProductBound.toBackwardResult
    {n : ℕ} (hn : 0 < n) {xs ys : Fin n → FiniteFp}
    (b : FpDotProduct.FpDotProductBound xs ys R) :
    BackwardResult
      (componentwiseRelGauge n hn)
      (fun w => ∑ i : Fin n, w i)
      (fun i => ((xs i).toVal : R) * ((ys i).toVal : R))
      ((b.result.toVal : R)) :=
  backwardResult_struct_of_forward_fin_bound hn
    (fun i => ((xs i).toVal : R) * ((ys i).toVal : R))
    (b.result.toVal : R) b.relErr b.h_relErr_nn b.h_bound

/-! ### Side-Attributed Backward Error (all-to-x / all-to-y)

These attribute the entire backward error to a single side instead of to the
products. Standard Higham presentation (Theorem 3.5 family): when one side has
known structure (e.g., `ys` are fixed weights), it's natural to express
`fl(x · y) = (x̃) · y` with `x̃ᵢ = (1+μᵢ)·xᵢ` — and symmetrically for `y`.

Both forms follow trivially from the asymmetric attribution-to-products form by
distributing `(1+μᵢ)` onto whichever factor. The bound `|μᵢ| ≤ b.relErr` is
unchanged — what changes is only the algebraic shape of the result. -/

/-- **All-to-x backward error**: attribute the dot-product error to perturbations
    of the `xs` factors only, leaving `ys` exact. -/
theorem FpDotProductBound_backward_error_to_x
    {n : ℕ} {xs ys : Fin n → FiniteFp}
    (b : FpDotProduct.FpDotProductBound xs ys R) :
    ∃ mu : Fin n → R,
      (b.result.toVal : R) =
        ∑ i : Fin n,
          ((1 + mu i) * ((xs i).toVal : R)) * ((ys i).toVal : R) ∧
      ∀ i, |mu i| ≤ b.relErr := by
  obtain ⟨mu, heq, hbnd⟩ := FpDotProductBound_backward_error b
  refine ⟨mu, ?_, hbnd⟩
  rw [heq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **All-to-y backward error**: attribute the dot-product error to perturbations
    of the `ys` factors only, leaving `xs` exact. -/
theorem FpDotProductBound_backward_error_to_y
    {n : ℕ} {xs ys : Fin n → FiniteFp}
    (b : FpDotProduct.FpDotProductBound xs ys R) :
    ∃ mu : Fin n → R,
      (b.result.toVal : R) =
        ∑ i : Fin n,
          ((xs i).toVal : R) * ((1 + mu i) * ((ys i).toVal : R)) ∧
      ∀ i, |mu i| ≤ b.relErr := by
  obtain ⟨mu, heq, hbnd⟩ := FpDotProductBound_backward_error b
  refine ⟨mu, ?_, hbnd⟩
  rw [heq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Structured all-to-x backward result**: `BackwardResult` on the `xs`-space
    only. Function maps `xs'` to `Σ xs'_i · ys_i`; `ys` are fixed weights. -/
noncomputable def FpDotProductBound.toBackwardResult_x
    {n : ℕ} (hn : 0 < n) {xs ys : Fin n → FiniteFp}
    (b : FpDotProduct.FpDotProductBound xs ys R) :
    BackwardResult
      (componentwiseRelGauge n hn)
      (fun x' => ∑ i : Fin n, x' i * ((ys i).toVal : R))
      (fun i => ((xs i).toVal : R))
      ((b.result.toVal : R)) :=
  backwardResult_struct_of_forward_weighted_bound hn
    (fun i => ((xs i).toVal : R)) (fun i => ((ys i).toVal : R))
    (b.result.toVal : R) b.relErr b.h_relErr_nn b.h_bound

/-- **Structured all-to-y backward result**: `BackwardResult` on the `ys`-space
    only. Function maps `ys'` to `Σ ys'_i · xs_i`; `xs` are fixed weights. -/
noncomputable def FpDotProductBound.toBackwardResult_y
    {n : ℕ} (hn : 0 < n) {xs ys : Fin n → FiniteFp}
    (b : FpDotProduct.FpDotProductBound xs ys R) :
    BackwardResult
      (componentwiseRelGauge n hn)
      (fun y' => ∑ i : Fin n, y' i * ((xs i).toVal : R))
      (fun i => ((ys i).toVal : R))
      ((b.result.toVal : R)) := by
  have h_bound' : |(b.result.toVal : R) -
        ∑ i, ((ys i).toVal : R) * ((xs i).toVal : R)| ≤
      b.relErr * ∑ i, |((ys i).toVal : R) * ((xs i).toVal : R)| := by
    have h := b.h_bound
    simp_rw [mul_comm ((xs _).toVal : R) ((ys _).toVal : R)] at h
    exact h
  exact backwardResult_struct_of_forward_weighted_bound hn
    (fun i => ((ys i).toVal : R)) (fun i => ((xs i).toVal : R))
    (b.result.toVal : R) b.relErr b.h_relErr_nn h_bound'

end BackwardError
