import Flean.Operations.NewtonHorner
import Flean.Operations.CompensatedHorner

/-!
# Compensated Newton's Method

Newton's method using **compensated Horner evaluation** for the polynomial value.
This gives `O(η)` evaluation error on `p(x)` instead of `O(nη)`, tightening the
Newton convergence ball from `O(nη·|x*/p'(x*)|)` to `O(η·|x*/p'(x*)|)`.

## Key theorem

- `comp_newton_perturbation`: per-step perturbation bound for compensated Newton
- Uses `comp_horner_bound` (compensated evaluation) + `horner_error_bound` (derivative)
  + `newton_perturbation_from_eval_errors` (generic composition)

## Algorithm

Each step:
1. Standard Horner for `p(x)` → `s_n` with errors `e_k`
2. Standard Horner on errors `e_k` → `r̃_n` (correction)
3. Compensated value: `v_comp = fl(s_n + r̃_n)`
4. Standard Horner for `p'(x)` → `d`
5. Division: `q = fl(v_comp / d)`
6. Update: `x_next = fl(x - q)`

## References

- Graillat, Langlois, Louvet, "Compensated Horner scheme" (2006)
- Higham, *Accuracy and Stability*, Ch. 5
-/

namespace CompensatedNewton

open Horner NewtonHorner CompensatedHorner

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- One step of compensated Newton's method.

    Uses compensated Horner for the polynomial value and standard Horner
    for the derivative. The compensation gives `O(η)` value error near roots. -/
structure CompNewtonStep [RModeExec]
    (val_coeffs : List FiniteFp)
    (deriv_coeffs : List FiniteFp)
    (x_cur : FiniteFp) where
  -- Primary Horner evaluation of p(x)
  v_final : FiniteFp
  v_trace : HornerTrace x_cur val_coeffs (0 : FiniteFp) v_final
  -- Correction Horner on step errors
  corr_coeffs : List FiniteFp
  corr_final : FiniteFp
  corr_trace : HornerTrace x_cur corr_coeffs (0 : FiniteFp) corr_final
  hcorr_len : corr_coeffs.length = val_coeffs.length
  hcorr_approx : ∀ i : Fin corr_coeffs.length,
    corr_coeffs[i].toVal (R := R) =
      (stepErrors (R := R) v_trace)[i]'(by rw [stepErrors_length]; omega)
  -- Compensated sum: v_comp = fl(v_final + corr_final)
  v_comp : FiniteFp
  hv_comp : v_final + corr_final = Fp.finite v_comp
  hv_comp_nr : isNormalRange ((v_final.toVal : R) + corr_final.toVal) ∨
               (v_final.toVal : R) + corr_final.toVal = 0
  -- Derivative evaluation: standard Horner on derivative coefficients
  d_final : FiniteFp
  d_trace : HornerTrace x_cur deriv_coeffs (0 : FiniteFp) d_final
  -- Division and subtraction
  hd_nonzero : d_final.m ≠ 0
  quot : FiniteFp
  hquot : v_comp / d_final = Fp.finite quot
  hquot_nr : isNormalRange ((v_comp.toVal : R) / d_final.toVal) ∨
             (v_comp.toVal : R) / d_final.toVal = 0
  x_next : FiniteFp
  hx_next : x_cur - quot = Fp.finite x_next
  hx_next_nr : isNormalRange ((x_cur.toVal : R) - quot.toVal) ∨
               (x_cur.toVal : R) - quot.toVal = 0

/-- Normal range conditions for the traces within a compensated Newton step. -/
structure CompNewtonStepNR [RModeExec]
    {val_coeffs deriv_coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : CompNewtonStep (R := R) val_coeffs deriv_coeffs x_cur) where
  v_nr : step.v_trace.AllNormalRange (R := R)
  corr_nr : step.corr_trace.AllNormalRange (R := R)
  d_nr : step.d_trace.AllNormalRange (R := R)

/-- **Compensated Newton perturbation bound.**

    The per-step perturbation of compensated Newton is:

    `|x_next - N(x)| ≤ η|x-q| + η|v_comp/d| + (δ_v·|p'(x)| + |p(x)|·δ_d) / (|d̂|·|p'(x)|)`

    where `δ_v` is the compensated Horner error (O(η) near roots) and `δ_d` is the
    standard Horner derivative error (O(nη)).

    Near a root (`|p(x)| → 0`), the `|p(x)|·δ_d` term vanishes and the
    perturbation is dominated by `δ_v/|d̂| ≈ O(η)/|p'(x*)|` — n times
    smaller than standard Newton-Horner. -/
theorem comp_newton_perturbation
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeSticky R]
    {val_coeffs deriv_coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : CompNewtonStep (R := R) val_coeffs deriv_coeffs x_cur)
    (hnr : CompNewtonStepNR step)
    (hd_hat_ne : (step.d_final.toVal : R) ≠ 0)
    -- Exact derivative is nonzero (we're not at a critical point)
    {p'_exact : R} (hp'_ne : p'_exact ≠ 0)
    (hderiv : p'_exact = hornerPoly (deriv_coeffs.map (fun c => c.toVal (R := R)))
        0 (x_cur.toVal (R := R))) :
    let x_v := (x_cur.toVal : R)
    let p_exact := hornerPoly (val_coeffs.map (fun c => c.toVal (R := R)))
        0 x_v
    let v_comp := (step.v_comp.toVal : R)
    let d_hat := (step.d_final.toVal : R)
    let δ_v := η * |(step.v_final.toVal : R) + step.corr_final.toVal| +
        ((1 + η) ^ (2 * step.corr_coeffs.length) - 1) *
          hornerPoly (step.corr_coeffs.map (fun c => |c.toVal (R := R)|))
            0 |x_v|
    let δ_d := ((1 + η) ^ (2 * deriv_coeffs.length) - 1) *
        hornerPoly (deriv_coeffs.map (fun c => |c.toVal (R := R)|))
          0 |x_v|
    |(step.x_next.toVal : R) - (x_v - p_exact / p'_exact)| ≤
      η * |x_v - step.quot.toVal| + η * |v_comp / d_hat| +
      (δ_v * |p'_exact| + |p_exact| * δ_d) / (|d_hat| * |p'_exact|) := by
  intro x_v p_exact v_comp d_hat δ_v δ_d
  -- Subtraction rounding: |x_next - (x - q)| ≤ η|x - q|
  have hsub := KahanSum.fpSub_error_or_zero (R := R)
    x_cur step.quot step.x_next step.hx_next step.hx_next_nr
  -- Division rounding: |q - v_comp/d| ≤ η|v_comp/d|
  have hdiv := KahanSum.fpDiv_error_or_zero (R := R)
    step.v_comp step.d_final step.quot step.hd_nonzero step.hquot step.hquot_nr
  -- Compensated Horner value error: |v_comp - p(x)| ≤ δ_v
  have hv_err := comp_horner_bound (R := R) step.v_trace
    step.corr_trace hnr.corr_nr FiniteFp.toVal_zero
    step.hcorr_len step.hcorr_approx step.hv_comp step.hv_comp_nr
  simp only [FiniteFp.toVal_zero] at hv_err
  -- Standard Horner derivative error: |d - p'(x)| ≤ δ_d
  have hd_err := horner_error_bound step.d_trace hnr.d_nr
  simp only [FiniteFp.toVal_zero, abs_zero] at hd_err
  -- Apply generic Newton perturbation theorem
  exact newton_perturbation_from_eval_errors hp'_ne hd_hat_ne
    hsub hdiv hv_err (by rw [hderiv]; exact hd_err)

end CompensatedNewton
