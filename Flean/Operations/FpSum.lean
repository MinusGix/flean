import Flean.Operations.PairwiseSum
import Flean.Util

/-!
# Generic Floating-Point Summation with Error Bound

This module introduces a small abstraction for "an FP summation of a list of
finite floats, together with a relative error bound". It is meant to decouple
downstream algorithms (e.g. softmax, mean, log-sum-exp) from the specific
summation method used — users can plug in naive sequential sum, pairwise sum,
Kahan/Neumaier summation, etc., and the downstream error analysis composes.

## Main definitions

* `FpSumBound xs R` — bundles a `FiniteFp` result with a relative error bound
  `|result - Σ xs_i| ≤ relErr · Σ|xs_i|`.
* `FpSumBound.ofPairwise` — construct from a `PairwiseSum.Trace`.
* `FpSumBound.ofList` — specialise a list-based bound to `Fin n → FiniteFp`.

Naive sequential sum is obtained from `PairwiseSum.Trace` with a right-spine
shape (each `combine` has a single-element right subtree); the depth of such
a trace is `n - 1`, matching the standard `γ_{n-1}` naive-sum error.
-/

set_option autoImplicit false

namespace FpSum

open Finset BigOperators

variable [FloatFormat]

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The `FpSumBound` structure -/

/-- Bundles a computed FP sum with a relative error bound.

`relErr · Σ|xs_i|` is the guaranteed upper bound on `|result - Σ xs_i|`.
Downstream error analyses (e.g. softmax, mean) can be written once against
this abstraction and instantiated with any summation method. -/
structure FpSumBound {n : ℕ} (xs : Fin n → FiniteFp) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] where
  /-- The FP result of the summation. -/
  result : FiniteFp
  /-- Relative error coefficient (e.g. `γ_n` for naive, `(1+η)^d - 1` for pairwise). -/
  relErr : R
  /-- Nonnegativity of `relErr`. -/
  h_relErr_nn : (0 : R) ≤ relErr
  /-- The relative error bound, relative to `Σ|xs_i|`. -/
  h_bound : |(result.toVal : R) - ∑ i, ((xs i).toVal : R)| ≤
              relErr * ∑ i, |((xs i).toVal : R)|

/-! ## Adapter: `PairwiseSum.Trace` → `FpSumBound` -/

section Adapter

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R] in
/-- Convert a list-indexed sum into a `Fin n`-indexed sum via `List.ofFn`. -/
private lemma sum_ofFn_toVal {n : ℕ} (xs : Fin n → FiniteFp) :
    ((List.ofFn xs).map (fun x => (x.toVal : R))).sum = ∑ i, ((xs i).toVal : R) := by
  simp [List.map_ofFn, List.sum_ofFn]

omit [IsStrictOrderedRing R] [FloorRing R]
  [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R] in
private lemma sum_ofFn_abs_toVal {n : ℕ} (xs : Fin n → FiniteFp) :
    ((List.ofFn xs).map (fun x => |(x.toVal : R)|)).sum = ∑ i, |((xs i).toVal : R)| := by
  simp [List.map_ofFn, List.sum_ofFn]

/-- **Constructor**: a `PairwiseSum.Trace` over `List.ofFn xs` gives an `FpSumBound`. -/
def FpSumBound.ofPairwise {n : ℕ} (xs : Fin n → FiniteFp)
    {result : FiniteFp}
    (trace : PairwiseSum.Trace (List.ofFn xs) result)
    (hnr : trace.AllNormalRange (R := R)) :
    FpSumBound xs R :=
  let err := (1 + η : R) ^ trace.depth - 1
  have hη : (0 : R) ≤ η := by positivity
  have h1η : (1 : R) ≤ 1 + η := by linarith
  have herr_nn : (0 : R) ≤ err := by
    have hp : (1 : R) ≤ (1 + η) ^ trace.depth := one_le_pow₀ h1η
    linarith
  have h_bnd : |(result.toVal : R) - ∑ i, ((xs i).toVal : R)| ≤
               err * ∑ i, |((xs i).toVal : R)| := by
    have h := PairwiseSum.pairwise_error_bound (R := R) trace hnr
    rw [sum_ofFn_toVal (R := R) xs, sum_ofFn_abs_toVal (R := R) xs] at h
    exact h
  { result := result
    relErr := err
    h_relErr_nn := herr_nn
    h_bound := h_bnd }

end Adapter

/-! ## Naive Sequential Sum (right-spine of a PairwiseSum trace) -/

section NaiveSum

variable [RModeExec]

/-- Naive left-fold summation trace: `single` starts at a single element,
each `step` appends one more element to the accumulator. -/
inductive NaiveSum : List FiniteFp → FiniteFp → Type where
  | single (x : FiniteFp) : NaiveSum [x] x
  | step {xs : List FiniteFp} {acc : FiniteFp}
      (h_prior : NaiveSum xs acc)
      (x : FiniteFp) (next : FiniteFp)
      (hadd : acc + x = Fp.finite next) :
      NaiveSum (xs ++ [x]) next

/-- Every addition step's operand sum is either in normal range or zero.
R-dependent predicate needed for `fpAdd_error_or_zero`. -/
def NaiveSum.AllNormalRange :
    {xs : List FiniteFp} → {result : FiniteFp} → NaiveSum xs result → Prop
  | _, _, .single _ => True
  | _, _, @NaiveSum.step _ _ _ acc h_prior x _ _ =>
      h_prior.AllNormalRange ∧
        (isNormalRange ((acc.toVal : R) + x.toVal) ∨ (acc.toVal : R) + x.toVal = 0)

/-- Convert a `NaiveSum` into a `PairwiseSum.Trace` (right-spine shape). -/
def NaiveSum.toPairwise :
    {xs : List FiniteFp} → {result : FiniteFp} → NaiveSum xs result →
    PairwiseSum.Trace xs result
  | _, _, .single x => .single x
  | _, _, .step h_prior x next hadd => .combine h_prior.toPairwise (.single x) next hadd

/-- Depth of the `PairwiseSum.Trace` obtained from a `NaiveSum`: equal to
`length - 1`. This is the standard naive-sum depth (one add per element after
the first). -/
lemma NaiveSum.toPairwise_depth :
    {xs : List FiniteFp} → {result : FiniteFp} → (t : NaiveSum xs result) →
    t.toPairwise.depth + 1 = xs.length
  | _, _, .single _ => by simp [toPairwise, PairwiseSum.Trace.depth]
  | _, _, .step h_prior x _ _ => by
      simp only [toPairwise, PairwiseSum.Trace.depth]
      have ih := h_prior.toPairwise_depth
      simp [List.length_append, ← ih]

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- `AllNormalRange` transports through `toPairwise`. -/
lemma NaiveSum.allNormalRange_toPairwise {xs : List FiniteFp} {result : FiniteFp}
    (t : NaiveSum xs result) (hnr : t.AllNormalRange (R := R)) :
    t.toPairwise.AllNormalRange (R := R) := by
  induction t with
  | single x => simp [toPairwise, PairwiseSum.Trace.AllNormalRange]
  | @step xs acc h_prior x next hadd ih =>
    simp only [AllNormalRange] at hnr
    obtain ⟨hnr_prior, hnr_step⟩ := hnr
    refine ⟨ih hnr_prior, ?_, hnr_step⟩
    simp [PairwiseSum.Trace.AllNormalRange]

end NaiveSum

/-! ## `FpSumBound.ofNaive` — construct from a `NaiveSum` witness -/

section OfNaive

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: a `NaiveSum` witness gives an `FpSumBound` with
`relErr = (1+η)^(n-1) - 1`, which is `≤ γ_{n-1}` when `(n-1)η < 1`. -/
def FpSumBound.ofNaive {n : ℕ} (xs : Fin n → FiniteFp)
    {result : FiniteFp}
    (t : NaiveSum (List.ofFn xs) result)
    (hnr : t.AllNormalRange (R := R)) :
    FpSumBound xs R :=
  FpSumBound.ofPairwise xs t.toPairwise (t.allNormalRange_toPairwise hnr)

end OfNaive

end FpSum
