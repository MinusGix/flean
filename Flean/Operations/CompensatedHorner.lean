import Flean.Operations.Horner

/-!
# Compensated Horner Evaluation

The exact decomposition theorem for Horner's method:
```
p(x) = sₙ + hornerPoly([e₁, ..., eₙ], 0, x)
```
where `eₖ = (s_{k-1}·x + a_{n-k}) - sₖ` is the per-step rounding error and
`sₖ` is the computed Horner value. The error polynomial `Σeₖ·x^{n-k}` can be
evaluated by a second Horner pass to give a compensated result accurate to `O(nη²)`.

This follows from the affine structure of Horner evaluation (`hornerPoly_affine`):
each per-step perturbation `-eₖ` propagates as `-eₖ·x^{n-k}` to the final result.

## References

- Langlois, Louvet, Graillat, "Compensated Horner Scheme" (2006)
- Higham, "Accuracy and Stability of Numerical Algorithms", §5.4
-/

namespace CompensatedHorner

open Horner

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Error Extraction -/

/-- Extract per-step rounding errors from a Horner trace.

    `eₖ = (s_{k-1} · x + a_{n-k}) - sₖ` (the exact rounding error at step k).
    Returns errors in step order `[e₁, ..., eₙ]`. -/
def stepErrors [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {acc final : FiniteFp} →
    HornerTrace x coeffs acc final → List R
  | _, _, _, .nil _ => []
  | _, _, _, .cons (acc := acc) (coeff := coeff) step rest =>
    let e := (acc.toVal (R := R)) * x.toVal + coeff.toVal - step.next.toVal
    e :: stepErrors rest

/-- The step errors list has the same length as the coefficient list. -/
theorem stepErrors_length [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : HornerTrace x coeffs acc final) :
    (stepErrors (R := R) trace).length = coeffs.length := by
  induction trace with
  | nil => simp [stepErrors]
  | cons _ _ ih => simp [stepErrors, ih]

/-! ## Exact Decomposition -/

/-- **Exact decomposition theorem for Horner evaluation.**

    The computed result `sₙ` plus the error polynomial equals the exact value:
    ```
    sₙ + hornerPoly([e₁,...,eₙ], 0, x) = p(x)
    ```
    where `eₖ` is the per-step rounding error. This is the core identity
    underlying compensated Horner evaluation.

    Proof: by induction using `hornerPoly_affine`. Each step perturbs the
    accumulator by `-eₖ`, which shifts the final result by `-eₖ · x^{n-k}`.
    Summing these shifts gives the error polynomial. -/
theorem comp_horner_exact_decomposition [RModeExec]
    {x : FiniteFp} {coeffs : List FiniteFp} {init final : FiniteFp}
    (trace : HornerTrace x coeffs init final) :
    (final.toVal : R) +
      hornerPoly (stepErrors trace (R := R)) 0 (x.toVal (R := R)) =
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal) := by
  induction trace with
  | nil => simp [stepErrors, hornerPoly]
  | @cons acc coeff coeffs final step rest ih =>
    simp only [stepErrors, hornerPoly, List.map_cons]
    -- IH: final + hornerPoly(rest.errors, 0, x) = hornerPoly(rest_map, next, x)
    -- Goal: final + hornerPoly(e :: rest.errors, 0, x) = hornerPoly(rest_map, acc*x + c, x)
    -- Strategy: use affine structure on both sides.
    --   LHS: hornerPoly(e::errs, 0, x) = hornerPoly(errs, 0, x) + e * x^n
    --   IH + next=acc*x+c-e: final + hornerPoly(errs, 0, x) = hornerPoly(map, acc*x+c, x) - e*x^n
    --   Sum: final + hornerPoly(errs, 0, x) + e*x^n = hornerPoly(map, acc*x+c, x)  ✓
    set e := (acc.toVal (R := R)) * x.toVal + coeff.toVal - step.next.toVal
    set n := coeffs.length
    have herr_len := stepErrors_length (R := R) rest
    -- By affine: hornerPoly(errs, 0+e, x) = hornerPoly(errs, 0, x) + e * x^n
    have haffine_err := hornerPoly_affine (stepErrors (R := R) rest) 0 e (x.toVal (R := R))
    simp only [zero_add] at haffine_err
    -- IH rewrites: step.next = acc*x + coeff - e, so
    --   final + P0 = hornerPoly(map, (acc*x+c) + (-e), x)
    have hnext_sub : (step.next.toVal : R) =
        (acc.toVal : R) * x.toVal + coeff.toVal + -e := by simp only [e]; ring
    rw [hnext_sub] at ih
    -- By affine: hornerPoly(map, (acc*x+c) + (-e), x) = hornerPoly(map, acc*x+c, x) + (-e)*x^n
    have haffine_main := hornerPoly_affine
      (coeffs.map (fun c => c.toVal (R := R)))
      ((acc.toVal : R) * x.toVal + coeff.toVal)
      (-e)
      (x.toVal (R := R))
    have hlen_map : (coeffs.map (fun c => c.toVal (R := R))).length = n := List.length_map _
    rw [hlen_map] at haffine_main
    -- Set shorthand for the polynomial values to help linarith
    set P0 := hornerPoly (stepErrors (R := R) rest) 0 (x.toVal (R := R))
    set Pmain := hornerPoly (coeffs.map (fun c => c.toVal (R := R)))
      ((acc.toVal : R) * x.toVal + coeff.toVal) (x.toVal (R := R))
    -- Unfold goal: 0*x + e = e, so hornerPoly(e::errs, 0, x) = hornerPoly(errs, e, x)
    simp only [zero_mul, zero_add]
    -- Rewrite hornerPoly(errs, e, x) = P0 + e * x^n
    rw [haffine_err, herr_len]
    -- From IH and haffine_main: final + P0 = Pmain + (-e) * x^n
    -- Goal: final + (P0 + e * x^n) = Pmain
    linarith [haffine_main, ih]

/-! ## Compensated Error Bound

The compensated algorithm evaluates `sₙ + r̃ₙ` where `r̃ₙ` is a second Horner pass
on fp approximations of the error coefficients `eₖ`. The bound is:

  `|fl(sₙ + r̃ₙ) - p(x)| ≤ η|sₙ + r̃ₙ| + γ_{2n} · Σ|ẽₖ - eₖ| · |x|^{n-k} + γ_{2n} · Σ|eₖ|·|x|^{n-k}`

When each `|eₖ| ≤ 2η · (|s_{k-1}||x| + |aₖ|)` (from the two rounding errors per step),
this gives the compensated bound `O(η + n²η²) · p̃(|x|)`.

The infrastructure for this (TwoProduct/TwoSum representations of `eₖ`) is in
`MulErrorRepresentable.lean` and `AddErrorRepresentable.lean`. -/

end CompensatedHorner
