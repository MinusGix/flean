import Flean.Operations.BackwardErrorCore
import Flean.Operations.DotProduct
import Flean.Operations.Horner

/-!
# Backward Error — Floating-Point Instances

Concrete backward error theorems for floating-point algorithms, building on
the generic framework in `BackwardErrorCore.lean`.

## Main results

- `dp_backward_error`: dot product backward error `|μᵢ| ≤ (1+η)^n - 1`
- `dp_backward_error_gamma`: dot product backward error `|μᵢ| ≤ γ_n`
- `horner_backward_error`: Horner coefficient perturbation `|μᵢ| ≤ (1+η)^{2n} - 1`

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

/-! ### Horner Polynomial ↔ Fin Sum -/

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

end BackwardError
