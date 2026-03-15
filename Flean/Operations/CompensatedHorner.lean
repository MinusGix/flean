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

The compensated algorithm:
1. Run Horner, collecting per-step errors `eₖ` via EFT (TwoProduct + TwoSum)
2. Run a second (standard) Horner pass on the error coefficients: `r̃ₙ ≈ hornerPoly(errors, 0, x)`
3. Return `fl(sₙ + r̃ₙ)` as the compensated result

The bound follows from composing the exact decomposition with the correction error. -/

/-- **Compensated Horner error bound.**

    Given:
    - A Horner trace computing `sₙ`
    - FP approximations `ẽₖ` of the per-step errors (e.g. from TwoProduct + TwoSum)
    - A correction Horner trace computing `r̃ₙ = fl(Horner(ẽ, 0, x))`
    - A final addition `result = fl(sₙ + r̃ₙ)`

    The compensated result satisfies:
    `|result - p(x)| ≤ η|sₙ + r̃ₙ| + correction_error`

    where `correction_error ≤ γ_{2m} · hornerPoly(|ẽ|, 0, |x|)` (from `horner_error_bound`
    on the correction pass, with `m = number of error coefficients`).

    When EFTs give exact `ẽₖ = eₖ`, and each `|eₖ| ≤ (2η + η²)(|sₖ₋₁||x| + |aₖ|)`,
    this yields the `O(η + n²η²) · p̃(|x|)` compensated bound. -/
theorem comp_horner_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : HornerTrace x coeffs init final)
    -- Correction pass: r̃ₙ computed by standard Horner on error approximations
    {corr_coeffs : List FiniteFp} {corr_init corr_final : FiniteFp}
    (corr_trace : HornerTrace x corr_coeffs corr_init corr_final)
    (corr_hnr : corr_trace.AllNormalRange (R := R))
    (hcorr_init : corr_init.toVal (R := R) = 0)
    -- The correction coefficients approximate the actual errors
    (hlen : corr_coeffs.length = coeffs.length)
    (herr_approx : ∀ i : Fin corr_coeffs.length,
      corr_coeffs[i].toVal (R := R) =
        (stepErrors (R := R) trace)[i]'(by rw [stepErrors_length]; omega))
    -- Final addition: result = fl(sₙ + r̃ₙ)
    {result : FiniteFp}
    (hresult : final + corr_final = Fp.finite result)
    (hresult_nr : isNormalRange ((final.toVal : R) + corr_final.toVal) ∨
                  (final.toVal : R) + corr_final.toVal = 0) :
    |(result.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      η * |(final.toVal : R) + corr_final.toVal| +
      ((1 + η) ^ (2 * corr_coeffs.length) - 1) *
        hornerPoly (corr_coeffs.map (fun c => |c.toVal (R := R)|))
          0 |x.toVal (R := R)| := by
  -- Step 1: |result - (sₙ + r̃ₙ)| ≤ η|sₙ + r̃ₙ|
  have hfinal_round := KahanSum.fpAdd_error_or_zero (R := R)
    final corr_final result hresult hresult_nr
  -- Step 2: sₙ + r̃ₙ - p(x) = r̃ₙ - hornerPoly(errors, 0, x)  [by exact decomposition]
  have hdecomp := comp_horner_exact_decomposition (R := R) trace
  -- Step 3: |r̃ₙ - hornerPoly(errors, 0, x)| ≤ correction_error  [by horner_error_bound on corr]
  have hcorr := horner_error_bound corr_trace corr_hnr
  -- Step 4: r̃ₙ evaluates the same polynomial as errors (since ẽₖ = eₖ)
  -- so the correction error uses |ẽₖ| = |eₖ|
  -- Triangle: |result - p(x)| ≤ |result - (sₙ+r̃ₙ)| + |sₙ+r̃ₙ - p(x)|
  -- = |result - (sₙ+r̃ₙ)| + |r̃ₙ - (p(x) - sₙ)|
  -- = |result - (sₙ+r̃ₙ)| + |r̃ₙ - hornerPoly(errors, 0, x)|
  have htri : |(result.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      |(result.toVal : R) - ((final.toVal : R) + corr_final.toVal)| +
      |(corr_final.toVal : R) -
        hornerPoly (stepErrors (R := R) trace) 0 (x.toVal)| := by
    have heq : (result.toVal : R) -
        hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal) =
        ((result.toVal : R) - (final.toVal + corr_final.toVal)) +
        (corr_final.toVal - hornerPoly (stepErrors (R := R) trace) 0 (x.toVal)) := by
      linarith
    rw [heq]; exact abs_add_le _ _
  -- The correction coefficients map to exactly the step errors (list equality)
  have hmap_eq : corr_coeffs.map (fun c => c.toVal (R := R)) = stepErrors (R := R) trace := by
    apply List.ext_getElem
    · simp only [List.length_map, stepErrors_length, hlen]
    · intro i hi1 hi2
      simp only [List.getElem_map]
      have hlen_err : (stepErrors (R := R) trace).length = corr_coeffs.length := by
        rw [stepErrors_length]; exact hlen.symm
      exact herr_approx ⟨i, by rwa [List.length_map] at hi1⟩
  -- hcorr after substituting corr_init.toVal = 0:
  -- |corr_final - hornerPoly(corr_map, 0, x)| ≤ ((1+η)^{2m}-1) * hornerPoly(|corr_map|, 0, |x|)
  rw [hcorr_init, abs_zero] at hcorr
  -- The correction map polynomial equals the error polynomial (by hmap_eq)
  rw [hmap_eq] at hcorr
  -- Now hcorr : |corr_final - hornerPoly(errors, 0, x)| ≤ ((1+η)^{2m}-1) * hornerPoly(|corr_map|, 0, |x|)
  -- Combine via triangle inequality
  linarith [htri, hfinal_round, hcorr]

end CompensatedHorner
