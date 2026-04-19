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

/-! ## Compositional Adapters -/

section Adapters

/-- **Weaken** the relative error of a `FpSumBound` to a larger coefficient. -/
def FpSumBound.weaken {n : ℕ} {xs : Fin n → FiniteFp}
    (b : FpSumBound xs R)
    (newRelErr : R) (h_ge : b.relErr ≤ newRelErr) :
    FpSumBound xs R :=
  { result := b.result
    relErr := newRelErr
    h_relErr_nn := le_trans b.h_relErr_nn h_ge
    h_bound := by
      have habs_nn : (0 : R) ≤ ∑ i, |((xs i).toVal : R)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      calc |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)|
          ≤ b.relErr * ∑ i, |((xs i).toVal : R)| := b.h_bound
        _ ≤ newRelErr * ∑ i, |((xs i).toVal : R)| :=
            mul_le_mul_of_nonneg_right h_ge habs_nn }

/-- **Reindex** a `FpSumBound` through a permutation `e : Fin n ≃ Fin n`. -/
def FpSumBound.reindex {n : ℕ} {xs : Fin n → FiniteFp}
    (b : FpSumBound xs R) (e : Fin n ≃ Fin n) :
    FpSumBound (xs ∘ e) R :=
  { result := b.result
    relErr := b.relErr
    h_relErr_nn := b.h_relErr_nn
    h_bound := by
      have hsum : ∑ i, ((xs (e i)).toVal : R) = ∑ i, ((xs i).toVal : R) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      have habs : ∑ i, |((xs (e i)).toVal : R)| = ∑ i, |((xs i).toVal : R)| :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      simpa [Function.comp, hsum, habs] using b.h_bound }

/-- **Congr**: transport an `FpSumBound` when inputs are pointwise equal. -/
def FpSumBound.congr {n : ℕ} {xs ys : Fin n → FiniteFp}
    (b : FpSumBound xs R) (h : xs = ys) :
    FpSumBound ys R :=
  h ▸ b

end Adapters

/-! ## Append — combining two independent sums

If `xs` and `ys` each come with an `FpSumBound`, and their partial results
sum correctly in FP, the concatenated `Fin.append xs ys` has a combined bound.

The combined relative error is bounded by `max(εx, εy) + η + εx·η + εy·η`
(loosely: `max(εx,εy) + 2η` for small errors). -/

section Append

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Append two sum bounds via a single fpAdd of the partial results.**

Hypotheses:
- `bx : FpSumBound xs R` — bound for first segment's partial sum
- `by_ : FpSumBound ys R` — bound for second segment
- `hadd : bx.result + by_.result = Fp.finite combinedResult` — the combining add
- `hnr_add : isNormalRange (bx.result.toVal + by_.result.toVal) ∨ ... = 0`
  — normality for the combining add

Result: `FpSumBound (Fin.append xs ys) R` with relErr = `max(εx, εy) + η + η · max(εx, εy)`
(safe loose bound).
-/
def FpSumBound.append {m n : ℕ} {xs : Fin m → FiniteFp} {ys : Fin n → FiniteFp}
    (bx : FpSumBound xs R) (by_ : FpSumBound ys R)
    (combinedResult : FiniteFp)
    (hadd : bx.result + by_.result = Fp.finite combinedResult)
    (hnr_add : isNormalRange ((bx.result.toVal : R) + by_.result.toVal) ∨
               (bx.result.toVal : R) + by_.result.toVal = 0) :
    FpSumBound (Fin.append xs ys) R :=
  let εM : R := max bx.relErr by_.relErr
  have hη_nn : (0 : R) ≤ η := by positivity
  have hεM_nn : 0 ≤ εM := le_trans bx.h_relErr_nn (le_max_left _ _)
  have hmul_nn : 0 ≤ (η : R) * εM := mul_nonneg hη_nn hεM_nn
  { result := combinedResult
    relErr := εM + (η : R) + (η : R) * εM
    h_relErr_nn := by positivity
    h_bound := by
      -- Combined add error
      have hadd_err : |(combinedResult.toVal : R) -
                       (bx.result.toVal + by_.result.toVal)| ≤
                      (η : R) * |(bx.result.toVal : R) + by_.result.toVal| :=
        KahanSum.fpAdd_error_or_zero (R := R) bx.result by_.result combinedResult hadd hnr_add
      -- Sum splits
      have hsum_split : ∑ i, ((Fin.append xs ys) i).toVal (R := R) =
                        (∑ i, ((xs i).toVal : R)) + (∑ i, ((ys i).toVal : R)) := by
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right]
      have habs_split : ∑ i, |((Fin.append xs ys) i).toVal (R := R)| =
                        (∑ i, |((xs i).toVal : R)|) + (∑ i, |((ys i).toVal : R)|) := by
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right]
      set Sx : R := ∑ i, ((xs i).toVal : R) with hSx_def
      set Sy : R := ∑ i, ((ys i).toVal : R) with hSy_def
      set Ax : R := ∑ i, |((xs i).toVal : R)| with hAx_def
      set Ay : R := ∑ i, |((ys i).toVal : R)| with hAy_def
      have hAx_nn : 0 ≤ Ax := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hAy_nn : 0 ≤ Ay := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hSx_le : |Sx| ≤ Ax := Finset.abs_sum_le_sum_abs _ _
      have hSy_le : |Sy| ≤ Ay := Finset.abs_sum_le_sum_abs _ _
      -- Bounds on partial results
      have hx_bd : |(bx.result.toVal : R) - Sx| ≤ bx.relErr * Ax := bx.h_bound
      have hy_bd : |(by_.result.toVal : R) - Sy| ≤ by_.relErr * Ay := by_.h_bound
      -- Triangle: |combined - (Sx + Sy)| ≤ add_err + |bx.result - Sx| + |by_.result - Sy|
      have htri : |(combinedResult.toVal : R) - (Sx + Sy)| ≤
          (η : R) * |(bx.result.toVal : R) + by_.result.toVal| +
          |(bx.result.toVal : R) - Sx| + |(by_.result.toVal : R) - Sy| := by
        have hstep1 := abs_add_le ((combinedResult.toVal : R) -
          (bx.result.toVal + by_.result.toVal))
          (((bx.result.toVal : R) - Sx) + ((by_.result.toVal : R) - Sy))
        have hstep2 := abs_add_le ((bx.result.toVal : R) - Sx) ((by_.result.toVal : R) - Sy)
        have heq : (combinedResult.toVal : R) - (Sx + Sy) =
          ((combinedResult.toVal : R) - (bx.result.toVal + by_.result.toVal)) +
          (((bx.result.toVal : R) - Sx) + ((by_.result.toVal : R) - Sy)) := by ring
        rw [heq]
        linarith [hadd_err]
      -- Bound bx.result.toVal by Sx + error
      have hbx_le : |(bx.result.toVal : R)| ≤ |Sx| + bx.relErr * Ax := by
        have := abs_sub_abs_le_abs_sub (bx.result.toVal : R) Sx
        linarith
      have hby_le : |(by_.result.toVal : R)| ≤ |Sy| + by_.relErr * Ay := by
        have := abs_sub_abs_le_abs_sub (by_.result.toVal : R) Sy
        linarith
      -- |bx.result + by_.result| ≤ |bx.result| + |by_.result|
      have hsum_bd : |(bx.result.toVal : R) + by_.result.toVal| ≤
          Ax + bx.relErr * Ax + Ay + by_.relErr * Ay := by
        have := abs_add_le (bx.result.toVal : R) by_.result.toVal
        linarith [hSx_le, hSy_le]
      -- Put it together: bound ≤ η·(Ax + εx·Ax + Ay + εy·Ay) + εx·Ax + εy·Ay
      --                 = (η + εx + εx·η)·Ax + (η + εy + εy·η)·Ay
      --                 ≤ (η + εM + εM·η)·Ax + (η + εM + εM·η)·Ay
      have hεx_le_M : bx.relErr ≤ εM := le_max_left _ _
      have hεy_le_M : by_.relErr ≤ εM := le_max_right _ _
      have hεx_nn := bx.h_relErr_nn
      have hεy_nn := by_.h_relErr_nn
      rw [hsum_split, habs_split]
      calc |(combinedResult.toVal : R) - (Sx + Sy)|
          ≤ (η : R) * |(bx.result.toVal : R) + by_.result.toVal| +
            |(bx.result.toVal : R) - Sx| + |(by_.result.toVal : R) - Sy| := htri
        _ ≤ (η : R) * (Ax + bx.relErr * Ax + Ay + by_.relErr * Ay) +
            bx.relErr * Ax + by_.relErr * Ay := by
              have : (η : R) * |(bx.result.toVal : R) + by_.result.toVal| ≤
                  (η : R) * (Ax + bx.relErr * Ax + Ay + by_.relErr * Ay) :=
                mul_le_mul_of_nonneg_left hsum_bd hη_nn
              linarith
        _ = ((η : R) + bx.relErr + (η : R) * bx.relErr) * Ax +
            ((η : R) + by_.relErr + (η : R) * by_.relErr) * Ay := by ring
        _ ≤ ((η : R) + εM + (η : R) * εM) * Ax +
            ((η : R) + εM + (η : R) * εM) * Ay := by
              have hmulx : (η : R) * bx.relErr ≤ (η : R) * εM :=
                mul_le_mul_of_nonneg_left hεx_le_M hη_nn
              have hmuly : (η : R) * by_.relErr ≤ (η : R) * εM :=
                mul_le_mul_of_nonneg_left hεy_le_M hη_nn
              have : ((η : R) + bx.relErr + (η : R) * bx.relErr) ≤
                     ((η : R) + εM + (η : R) * εM) := by linarith
              have hbd_x : ((η : R) + bx.relErr + (η : R) * bx.relErr) * Ax ≤
                           ((η : R) + εM + (η : R) * εM) * Ax :=
                mul_le_mul_of_nonneg_right this hAx_nn
              have : ((η : R) + by_.relErr + (η : R) * by_.relErr) ≤
                     ((η : R) + εM + (η : R) * εM) := by linarith
              have hbd_y : ((η : R) + by_.relErr + (η : R) * by_.relErr) * Ay ≤
                           ((η : R) + εM + (η : R) * εM) * Ay :=
                mul_le_mul_of_nonneg_right this hAy_nn
              linarith
        _ = (εM + (η : R) + (η : R) * εM) * (Ax + Ay) := by ring }

end Append

end FpSum
