import Flean.Operations.PairwiseSum
import Flean.Operations.NeumaierSum
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

/-- Bundles a *compensated* FP sum: a pair `(sum, comp) : FiniteFp × FiniteFp`
whose compensated value `sigma := sum.toVal + comp.toVal` approximates the true
sum with a relative error bound.

Neumaier and similar algorithms naturally produce this pair: the running `sum`
drops rounding errors that are captured by the compensator `comp`, and only
the combined `sigma = sum + comp` reflects the accumulated value accurately.

The separate `compErr` field bounds `|comp|` alone (not just `|sum + comp|`).
This enables compositional operations like compensated-compensated `append`
that need to reason about `|sum_x + sum_y|` and `|comp_x + comp_y|`
independently.

Bridges to `FpSumBound` via `FpSumBoundCompensated.compensateAndRound`, which
performs one final `fpAdd(sum, comp)` at the cost of a single `η·|sigma|`
rounding step (small compared to the accumulated `relErr`). -/
structure FpSumBoundCompensated {n : ℕ} (xs : Fin n → FiniteFp) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] where
  /-- Running FP sum. -/
  sum : FiniteFp
  /-- Accumulated FP compensator. -/
  comp : FiniteFp
  /-- Relative error of the compensated value `sum.toVal + comp.toVal`. -/
  relErr : R
  /-- Relative bound on `|comp|` alone. -/
  compErr : R
  /-- Nonnegativity of `relErr`. -/
  h_relErr_nn : (0 : R) ≤ relErr
  /-- Nonnegativity of `compErr`. -/
  h_compErr_nn : (0 : R) ≤ compErr
  /-- `|(sum + comp) - Σ xs| ≤ relErr · Σ|xs|`. -/
  h_bound : |((sum.toVal : R) + comp.toVal) - ∑ i, ((xs i).toVal : R)| ≤
              relErr * ∑ i, |((xs i).toVal : R)|
  /-- `|comp| ≤ compErr · Σ|xs|`. -/
  h_comp_bound : |(comp.toVal : R)| ≤ compErr * ∑ i, |((xs i).toVal : R)|

/-- The compensated value `sigma = sum.toVal + comp.toVal`. -/
@[simp] def FpSumBoundCompensated.sigma {n : ℕ} {xs : Fin n → FiniteFp}
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (cb : FpSumBoundCompensated xs R) : R :=
  (cb.sum.toVal : R) + cb.comp.toVal

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

/-! ## Kahan Adapter

Kahan's compensated summation admits a tight `(2η + n·η²)·Σ|x|` error bound
(Higham, Thm 4.3). This adapter wraps `KahanSum.kahan_higham_bound` into an
`FpSumBound`. The `hexact`, `hnr`, and `hM` hypotheses are typically discharged
from the surrounding computation's structure. -/

section KahanAdapter

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: a Kahan `Trace` on `List.ofFn xs` with the TwoSum-exact
and magnitude hypotheses gives an `FpSumBound` with tight `relErr = 2η + n·η²`.

Hypotheses mirror `KahanSum.kahan_higham_bound`:
* `hinit_sum`, `hinit_comp` — zero-initialized state;
* `hexact` — per-step TwoSum-exactness (holds under Dekker, or provable via
  `step_twosum_exact_of_sub_exact`);
* `hnr` — per-step normal-range;
* `hM` — `|sum_k + y_k| ≤ Σ|x_i|` at each step (typically proved by
  induction on the prefix). -/
def FpSumBound.ofKahanTrace {n : ℕ} (xs : Fin n → FiniteFp)
    {init final : KahanSum.State}
    (trace : KahanSum.Trace (List.ofFn xs) init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : KahanSum.State) (x : FiniteFp)
                (step : KahanSum.StepWitness st x),
      KahanSum.StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : KahanSum.State) (x : FiniteFp)
             (step : KahanSum.StepWitness st x),
      KahanSum.StepNormalRange (R := R) st x step)
    (hM : ∀ (st : KahanSum.State) (x : FiniteFp)
            (step : KahanSum.StepWitness st x),
      |(st.sum.toVal : R) + step.y.toVal| ≤
        ((List.ofFn xs).map (fun x => |x.toVal (R := R)|)).sum) :
    FpSumBound xs R :=
  { result := final.sum
    relErr := 2 * η + (n : R) * η ^ 2
    h_relErr_nn := by
      have hη : (0 : R) ≤ η := by positivity
      have hn_nn : (0 : R) ≤ (n : R) := Nat.cast_nonneg _
      positivity
    h_bound := by
      have h := KahanSum.kahan_higham_bound trace hinit_sum hinit_comp hexact hnr hM
      rw [sum_ofFn_toVal (R := R) xs, sum_ofFn_abs_toVal (R := R) xs] at h
      have hlen : ((List.ofFn xs).length : R) = (n : R) := by
        exact_mod_cast List.length_ofFn
      rw [hlen] at h
      exact h }

end KahanAdapter

/-! ## Neumaier Adapter (loose)

`FpSumBound` can only hold a `FiniteFp` result, which forces this adapter to
return Neumaier's `final.sum` and discard the compensator `final.comp`. That
is lossy: Neumaier's virtue is that the compensated value
`sigma = sum + comp` is accurate to `O(n·η²·S)`, but `|sum - sigma| = |comp|`
is `O(n·η·S)` by `comp_growth`. The resulting adapter bound is

  `(n·η·((1+η)^{n+1} - 1) + (1+η)·((1+η)^n - 1)) · S`

whose leading term is `O((n+1)·η·S)` — **not** better than `ofNaive`'s
`(1+η)^(n-1) - 1` and strictly worse than `ofKahanTrace`'s `2η + n·η²`.

For tight bounds, prefer either:
  - `FpSumBoundCompensated.ofNeumaierTrace` + `compensateAndRound` — preserves
    Neumaier's `O(n²η²)` accuracy, collapsing to `FpSumBound` with
    `relErr = η + O(n²η²)` via one final `fpAdd(sum, comp)`.
  - `FpSumBound.ofKahanTrace` — Kahan's tight `2η + n·η²` bound directly
    (no extra rounding required). -/

section NeumaierAdapter

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor** (loose): Neumaier `NTrace` on `List.ofFn xs` → `FpSumBound`
with `relErr = n·η·((1+η)^{n+1}-1) + (1+η)·((1+η)^n - 1)`.

See the section docstring: this bound is loose because `FpSumBound` cannot
expose the compensator. -/
def FpSumBound.ofNeumaierTrace {n : ℕ} (xs : Fin n → FiniteFp)
    {init final : NeumaierSum.NState}
    (trace : NeumaierSum.NTrace (R := R) (List.ofFn xs) init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hnr : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
             (step : NeumaierSum.NStepWitness (R := R) st x),
      NeumaierSum.NStepNormalRange (R := R) st x step)
    (hM : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
            (_step : NeumaierSum.NStepWitness (R := R) st x),
      |(st.sum.toVal : R) + x.toVal| ≤
        ((List.ofFn xs).map (fun x => |x.toVal (R := R)|)).sum) :
    FpSumBound xs R :=
  { result := final.sum
    relErr := (n : R) * η * ((1 + η) ^ (n + 1) - 1) +
              (1 + η) * ((1 + η) ^ n - 1)
    h_relErr_nn := by
      have hη : (0 : R) ≤ η := by positivity
      have hn_nn : (0 : R) ≤ (n : R) := Nat.cast_nonneg _
      have h_pow_n : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ (by linarith)
      have h_pow_n1 : (1 : R) ≤ (1 + η) ^ (n + 1) := one_le_pow₀ (by linarith)
      have h1 : (0 : R) ≤ (n : R) * η * ((1 + η) ^ (n + 1) - 1) := by
        have : (0 : R) ≤ (1 + η) ^ (n + 1) - 1 := by linarith
        positivity
      have h2 : (0 : R) ≤ (1 + η) * ((1 + η) ^ n - 1) := by
        have : (0 : R) ≤ (1 + η) ^ n - 1 := by linarith
        have : (0 : R) ≤ 1 + η := by linarith
        positivity
      linarith
    h_bound := by
      set S : R := ((List.ofFn xs).map (fun x => |x.toVal (R := R)|)).sum with hS_def
      have hS_nn : (0 : R) ≤ S := by
        rw [hS_def]
        apply List.sum_nonneg
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨_, _, rfl⟩ := hy
        exact abs_nonneg _
      -- Neumaier concrete bound on sigma, with length = n
      have h_sigma := NeumaierSum.neumaier_concrete_bound (R := R) trace
        hinit_sum hinit_comp hnr S hS_nn hM
      -- comp_growth with init.comp = 0 → |comp| ≤ (1+η)·((1+η)^n - 1)·S
      have h_comp := NeumaierSum.comp_growth (R := R) trace hnr S hM
      rw [hinit_comp, abs_zero, mul_zero, zero_add] at h_comp
      -- Convert list sums/length to Fin-form
      have h_sum_eq : ((List.ofFn xs).map (fun x => x.toVal (R := R))).sum =
                      ∑ i, ((xs i).toVal : R) := by
        simp [List.map_ofFn, List.sum_ofFn]
      have h_abs_eq : S = ∑ i, |((xs i).toVal : R)| := by
        rw [hS_def]; simp [List.map_ofFn, List.sum_ofFn]
      have h_len : (List.ofFn xs).length = n := List.length_ofFn
      rw [h_sum_eq, h_len] at h_sigma
      rw [h_len] at h_comp
      -- h_sigma : |final.sigma - ∑ i, (xs i).toVal| ≤
      --             n · η · ((1+η)^(n+1) - 1) · S
      -- h_comp : |final.comp.toVal| ≤ (1+η) · ((1+η)^n - 1) · S
      -- Triangle: final.sum.toVal - Σ = (sigma - Σ) - comp
      have h_sigma_eq : NeumaierSum.NState.sigma (R := R) final =
                        (final.sum.toVal : R) + final.comp.toVal := rfl
      rw [h_sigma_eq] at h_sigma
      rw [h_abs_eq] at h_sigma h_comp
      -- Triangle: |sum - Σ| ≤ |(sum + comp) - Σ| + |comp|
      have h_tri : |(final.sum.toVal : R) - ∑ i, ((xs i).toVal : R)| ≤
          |(final.sum.toVal : R) + final.comp.toVal - ∑ i, ((xs i).toVal : R)| +
          |(final.comp.toVal : R)| := by
        have h_decomp : (final.sum.toVal : R) - ∑ i, ((xs i).toVal : R) =
            ((final.sum.toVal : R) + final.comp.toVal -
              ∑ i, ((xs i).toVal : R)) + (-(final.comp.toVal : R)) := by ring
        rw [h_decomp]
        have h := abs_add_le ((final.sum.toVal : R) + final.comp.toVal -
          ∑ i, ((xs i).toVal : R)) (-(final.comp.toVal : R))
        rw [abs_neg] at h
        exact h
      nlinarith [h_sigma, h_comp, h_tri] }

end NeumaierAdapter

/-! ## `FpSumBoundCompensated` Constructors and Conversions

The compensated-sum bundle preserves Neumaier's `O(n²η²)` accuracy that
`FpSumBound.ofNeumaierTrace` throws away by discarding `comp`. Usage:

1. Build `FpSumBoundCompensated` via `ofNeumaierTrace`.
2. Perform one final `fpAdd(sum, comp)` to collapse into `FpSumBound` via
   `compensateAndRound`. The resulting `relErr` is `cb.relErr·(1+η) + η`,
   so for Neumaier's `cb.relErr = O(n²η²)` the collapsed bound is
   `η + O(n²η²)` — comparable to `ofKahanTrace`'s `2η + n·η²` at moderate
   `n`, and strictly better when `n·η` is small. -/

section CompensatedSum

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: a Neumaier `NTrace` on `List.ofFn xs` with the standard
hypotheses gives a tight `FpSumBoundCompensated` with
`relErr = n·η·((1+η)^{n+1}-1) ≈ O(n²η²)`.

This is the recommended Neumaier adapter — it keeps the compensator so
downstream consumers can recover Neumaier's full accuracy. Convert to
`FpSumBound` via `compensateAndRound` when interfacing with non-compensated
frameworks. -/
def FpSumBoundCompensated.ofNeumaierTrace {n : ℕ} (xs : Fin n → FiniteFp)
    {init final : NeumaierSum.NState}
    (trace : NeumaierSum.NTrace (R := R) (List.ofFn xs) init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hnr : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
             (step : NeumaierSum.NStepWitness (R := R) st x),
      NeumaierSum.NStepNormalRange (R := R) st x step)
    (hM : ∀ (st : NeumaierSum.NState) (x : FiniteFp)
            (_step : NeumaierSum.NStepWitness (R := R) st x),
      |(st.sum.toVal : R) + x.toVal| ≤
        ((List.ofFn xs).map (fun x => |x.toVal (R := R)|)).sum) :
    FpSumBoundCompensated xs R :=
  { sum := final.sum
    comp := final.comp
    relErr := (n : R) * η * ((1 + η) ^ (n + 1) - 1)
    compErr := (1 + η) * ((1 + η) ^ n - 1)
    h_relErr_nn := by
      have hη : (0 : R) ≤ η := by positivity
      have hn_nn : (0 : R) ≤ (n : R) := Nat.cast_nonneg _
      have h_pow : (1 : R) ≤ (1 + η) ^ (n + 1) := one_le_pow₀ (by linarith)
      have : (0 : R) ≤ (1 + η) ^ (n + 1) - 1 := by linarith
      positivity
    h_compErr_nn := by
      have hη : (0 : R) ≤ η := by positivity
      have h_pow : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ (by linarith)
      have h1 : (0 : R) ≤ (1 + η) ^ n - 1 := by linarith
      have h2 : (0 : R) ≤ 1 + η := by linarith
      positivity
    h_bound := by
      set S : R := ((List.ofFn xs).map (fun x => |x.toVal (R := R)|)).sum with hS_def
      have hS_nn : (0 : R) ≤ S := by
        rw [hS_def]
        apply List.sum_nonneg
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨_, _, rfl⟩ := hy
        exact abs_nonneg _
      have h_sigma := NeumaierSum.neumaier_concrete_bound (R := R) trace
        hinit_sum hinit_comp hnr S hS_nn hM
      have h_sum_eq : ((List.ofFn xs).map (fun x => x.toVal (R := R))).sum =
                      ∑ i, ((xs i).toVal : R) := by
        simp [List.map_ofFn, List.sum_ofFn]
      have h_abs_eq : S = ∑ i, |((xs i).toVal : R)| := by
        rw [hS_def]; simp [List.map_ofFn, List.sum_ofFn]
      have h_len : (List.ofFn xs).length = n := List.length_ofFn
      have h_sigma_eq : NeumaierSum.NState.sigma (R := R) final =
                        (final.sum.toVal : R) + final.comp.toVal := rfl
      rw [h_sigma_eq, h_sum_eq, h_len, h_abs_eq] at h_sigma
      exact h_sigma
    h_comp_bound := by
      set S : R := ((List.ofFn xs).map (fun x => |x.toVal (R := R)|)).sum with hS_def
      have h_comp := NeumaierSum.comp_growth (R := R) trace hnr S hM
      rw [hinit_comp, abs_zero, mul_zero, zero_add] at h_comp
      have h_abs_eq : S = ∑ i, |((xs i).toVal : R)| := by
        rw [hS_def]; simp [List.map_ofFn, List.sum_ofFn]
      have h_len : (List.ofFn xs).length = n := List.length_ofFn
      rw [h_len, h_abs_eq] at h_comp
      exact h_comp }

/-- **Conversion**: collapse a compensated sum into an `FpSumBound` via one
final `fpAdd(sum, comp)`. The new relative error is `cb.relErr·(1+η) + η`.

For Neumaier inputs (`cb.relErr = O(n²η²)`), the collapsed bound is
`η + O(n²η²)`, Kahan-comparable.

Requires `hadd : cb.sum + cb.comp = Fp.finite finalResult` and a normal-range
witness for the combining addition. -/
def FpSumBoundCompensated.compensateAndRound {n : ℕ} {xs : Fin n → FiniteFp}
    (cb : FpSumBoundCompensated xs R)
    {finalResult : FiniteFp}
    (hadd : cb.sum + cb.comp = Fp.finite finalResult)
    (hnr_add : isNormalRange ((cb.sum.toVal : R) + cb.comp.toVal) ∨
               (cb.sum.toVal : R) + cb.comp.toVal = 0) :
    FpSumBound xs R :=
  { result := finalResult
    relErr := cb.relErr * (1 + η) + η
    h_relErr_nn := by
      have hη : (0 : R) ≤ η := by positivity
      have h1η : (0 : R) ≤ 1 + η := by linarith
      have : 0 ≤ cb.relErr * (1 + η) := mul_nonneg cb.h_relErr_nn h1η
      linarith
    h_bound := by
      set A : R := ∑ i, |((xs i).toVal : R)| with hA_def
      have hA_nn : 0 ≤ A := by
        rw [hA_def]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hsum_abs_le : |∑ i, ((xs i).toVal : R)| ≤ A := by
        rw [hA_def]; exact Finset.abs_sum_le_sum_abs _ _
      -- `|sum + comp| ≤ (1 + relErr) · A`
      have h_sigma_bd : |(cb.sum.toVal : R) + cb.comp.toVal| ≤
          (1 + cb.relErr) * A := by
        have h := abs_sub_abs_le_abs_sub
          ((cb.sum.toVal : R) + cb.comp.toVal) (∑ i, ((xs i).toVal : R))
        have : |(cb.sum.toVal : R) + cb.comp.toVal| -
               |∑ i, ((xs i).toVal : R)| ≤ cb.relErr * A := by
          calc _ ≤ |((cb.sum.toVal : R) + cb.comp.toVal) -
                   ∑ i, ((xs i).toVal : R)| := h
            _ ≤ cb.relErr * A := cb.h_bound
        linarith
      -- fpAdd rounding: `|finalResult - (sum + comp)| ≤ η · |sum + comp|`
      have h_add_err := KahanSum.fpAdd_error_or_zero (R := R) cb.sum cb.comp
        finalResult hadd hnr_add
      -- Triangle: `|finalResult - Σ| ≤ |finalResult - (sum + comp)| + |(sum + comp) - Σ|`
      have hη : (0 : R) ≤ η := by positivity
      have h_round : |(finalResult.toVal : R) - ((cb.sum.toVal : R) + cb.comp.toVal)| ≤
                     η * (1 + cb.relErr) * A := by
        calc |(finalResult.toVal : R) - ((cb.sum.toVal : R) + cb.comp.toVal)|
            ≤ η * |(cb.sum.toVal : R) + cb.comp.toVal| := h_add_err
          _ ≤ η * ((1 + cb.relErr) * A) :=
              mul_le_mul_of_nonneg_left h_sigma_bd hη
          _ = η * (1 + cb.relErr) * A := by ring
      have h_decomp : (finalResult.toVal : R) - ∑ i, ((xs i).toVal : R) =
          ((finalResult.toVal : R) - ((cb.sum.toVal : R) + cb.comp.toVal)) +
          (((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R)) := by ring
      calc |(finalResult.toVal : R) - ∑ i, ((xs i).toVal : R)|
          = |((finalResult.toVal : R) - ((cb.sum.toVal : R) + cb.comp.toVal)) +
             (((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R))| := by
            rw [h_decomp]
        _ ≤ |(finalResult.toVal : R) - ((cb.sum.toVal : R) + cb.comp.toVal)| +
            |((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R)| :=
            abs_add_le _ _
        _ ≤ η * (1 + cb.relErr) * A + cb.relErr * A := by linarith [cb.h_bound]
        _ = (cb.relErr * (1 + η) + η) * A := by ring }

/-- **Sigma bound**: `|sum + comp| ≤ (1 + relErr) · Σ|xs|`, derived from the
main bound and the triangle inequality `|sigma| ≤ |Σ| + |sigma - Σ|`. -/
theorem FpSumBoundCompensated.sigma_abs_le {n : ℕ} {xs : Fin n → FiniteFp}
    (cb : FpSumBoundCompensated xs R) :
    |((cb.sum.toVal : R) + cb.comp.toVal)| ≤
      (1 + cb.relErr) * ∑ i, |((xs i).toVal : R)| := by
  set A : R := ∑ i, |((xs i).toVal : R)| with hA_def
  have hA_nn : 0 ≤ A := by
    rw [hA_def]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsum_abs_le : |∑ i, ((xs i).toVal : R)| ≤ A := by
    rw [hA_def]; exact Finset.abs_sum_le_sum_abs _ _
  have h_abs_diff := abs_sub_abs_le_abs_sub
    ((cb.sum.toVal : R) + cb.comp.toVal) (∑ i, ((xs i).toVal : R))
  calc |((cb.sum.toVal : R) + cb.comp.toVal)|
      ≤ |∑ i, ((xs i).toVal : R)| +
        |((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R)| := by
          linarith
    _ ≤ A + cb.relErr * A := by linarith [cb.h_bound]
    _ = (1 + cb.relErr) * A := by ring

/-- **Sum bound**: `|sum| ≤ (1 + relErr + compErr) · Σ|xs|`. Follows from
`sigma_abs_le` and `h_comp_bound` via `sum = sigma - comp`. -/
theorem FpSumBoundCompensated.sum_abs_le {n : ℕ} {xs : Fin n → FiniteFp}
    (cb : FpSumBoundCompensated xs R) :
    |(cb.sum.toVal : R)| ≤
      (1 + cb.relErr + cb.compErr) * ∑ i, |((xs i).toVal : R)| := by
  have h_abs : |(cb.sum.toVal : R)| ≤
      |((cb.sum.toVal : R) + cb.comp.toVal)| + |(cb.comp.toVal : R)| := by
    have key := abs_add_le ((cb.sum.toVal : R) + cb.comp.toVal) (-(cb.comp.toVal : R))
    rw [abs_neg] at key
    have heq : ((cb.sum.toVal : R) + cb.comp.toVal) + (-(cb.comp.toVal : R)) =
               (cb.sum.toVal : R) := by ring
    rw [heq] at key
    exact key
  have h_sig := cb.sigma_abs_le
  have h_comp := cb.h_comp_bound
  nlinarith [h_abs, h_sig, h_comp,
    Finset.sum_nonneg (fun (i : Fin n) (_ : i ∈ Finset.univ) => abs_nonneg ((xs i).toVal (R := R)))]

/-- **Weaken** the relative error of an `FpSumBoundCompensated`.
Only `relErr` is weakened; `compErr` is left alone. -/
def FpSumBoundCompensated.weaken {n : ℕ} {xs : Fin n → FiniteFp}
    (cb : FpSumBoundCompensated xs R)
    (newRelErr : R) (h_ge : cb.relErr ≤ newRelErr) :
    FpSumBoundCompensated xs R :=
  { sum := cb.sum
    comp := cb.comp
    relErr := newRelErr
    compErr := cb.compErr
    h_relErr_nn := le_trans cb.h_relErr_nn h_ge
    h_compErr_nn := cb.h_compErr_nn
    h_bound := by
      have habs_nn : (0 : R) ≤ ∑ i, |((xs i).toVal : R)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      calc |((cb.sum.toVal : R) + cb.comp.toVal) - ∑ i, ((xs i).toVal : R)|
          ≤ cb.relErr * ∑ i, |((xs i).toVal : R)| := cb.h_bound
        _ ≤ newRelErr * ∑ i, |((xs i).toVal : R)| :=
            mul_le_mul_of_nonneg_right h_ge habs_nn
    h_comp_bound := cb.h_comp_bound }

/-- **Weaken** the compensator error of an `FpSumBoundCompensated`. -/
def FpSumBoundCompensated.weakenComp {n : ℕ} {xs : Fin n → FiniteFp}
    (cb : FpSumBoundCompensated xs R)
    (newCompErr : R) (h_ge : cb.compErr ≤ newCompErr) :
    FpSumBoundCompensated xs R :=
  { sum := cb.sum
    comp := cb.comp
    relErr := cb.relErr
    compErr := newCompErr
    h_relErr_nn := cb.h_relErr_nn
    h_compErr_nn := le_trans cb.h_compErr_nn h_ge
    h_bound := cb.h_bound
    h_comp_bound := by
      have habs_nn : (0 : R) ≤ ∑ i, |((xs i).toVal : R)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      calc |(cb.comp.toVal : R)|
          ≤ cb.compErr * ∑ i, |((xs i).toVal : R)| := cb.h_comp_bound
        _ ≤ newCompErr * ∑ i, |((xs i).toVal : R)| :=
            mul_le_mul_of_nonneg_right h_ge habs_nn }

/-- **Reindex** a `FpSumBoundCompensated` through a permutation `e : Fin n ≃ Fin n`.
The pair `(sum, comp)` and error coefficients are unchanged; only the input
sequence is permuted. -/
def FpSumBoundCompensated.reindex {n : ℕ} {xs : Fin n → FiniteFp}
    (cb : FpSumBoundCompensated xs R) (e : Fin n ≃ Fin n) :
    FpSumBoundCompensated (xs ∘ e) R :=
  { sum := cb.sum
    comp := cb.comp
    relErr := cb.relErr
    compErr := cb.compErr
    h_relErr_nn := cb.h_relErr_nn
    h_compErr_nn := cb.h_compErr_nn
    h_bound := by
      have hsum : ∑ i, ((xs (e i)).toVal : R) = ∑ i, ((xs i).toVal : R) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      have habs : ∑ i, |((xs (e i)).toVal : R)| = ∑ i, |((xs i).toVal : R)| :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      simpa [Function.comp, hsum, habs] using cb.h_bound
    h_comp_bound := by
      have habs : ∑ i, |((xs (e i)).toVal : R)| = ∑ i, |((xs i).toVal : R)| :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      simpa [Function.comp, habs] using cb.h_comp_bound }

/-- **Congr**: transport an `FpSumBoundCompensated` when inputs are pointwise equal. -/
def FpSumBoundCompensated.congr {n : ℕ} {xs ys : Fin n → FiniteFp}
    (cb : FpSumBoundCompensated xs R) (h : xs = ys) :
    FpSumBoundCompensated ys R :=
  h ▸ cb

/-- **Compensated append**: combine two `FpSumBoundCompensated` into one,
preserving the compensator structure via two separate `fpAdd`s on the sum
and comp parts.

Given `hSumAdd : cb_x.sum + cb_y.sum = Fp.finite newSum` and
`hCompAdd : cb_x.comp + cb_y.comp = Fp.finite newComp` (plus normal-range),
the combined error coefficients are:
* `relErr = εM·(1+η) + η·(1 + 2·cεM)` where `εM = max(relErr_x, relErr_y)`
* `compErr = (1+η)·cεM` where `cεM = max(compErr_x, compErr_y)`

For typical Neumaier inputs (`relErr = O(n²η²)`, `compErr = O(nη)`), this
gives `O(η) + O(n²η²)` relative error — a modest loss from a single `fpAdd`
pair compared to running one large Neumaier trace end-to-end. -/
def FpSumBoundCompensated.append {m n : ℕ}
    {xs : Fin m → FiniteFp} {ys : Fin n → FiniteFp}
    (cb_x : FpSumBoundCompensated xs R) (cb_y : FpSumBoundCompensated ys R)
    (newSum : FiniteFp)
    (hSumAdd : cb_x.sum + cb_y.sum = Fp.finite newSum)
    (hnr_sum : isNormalRange ((cb_x.sum.toVal : R) + cb_y.sum.toVal) ∨
               (cb_x.sum.toVal : R) + cb_y.sum.toVal = 0)
    (newComp : FiniteFp)
    (hCompAdd : cb_x.comp + cb_y.comp = Fp.finite newComp)
    (hnr_comp : isNormalRange ((cb_x.comp.toVal : R) + cb_y.comp.toVal) ∨
                (cb_x.comp.toVal : R) + cb_y.comp.toVal = 0) :
    FpSumBoundCompensated (Fin.append xs ys) R :=
  { sum := newSum
    comp := newComp
    relErr := (max cb_x.relErr cb_y.relErr) * (1 + (η : R)) +
              (η : R) * (1 + 2 * max cb_x.compErr cb_y.compErr)
    compErr := (1 + (η : R)) * max cb_x.compErr cb_y.compErr
    h_relErr_nn := by
      have hη : (0 : R) ≤ η := by positivity
      have hεM_nn : 0 ≤ max cb_x.relErr cb_y.relErr :=
        le_trans cb_x.h_relErr_nn (le_max_left _ _)
      have hcεM_nn : 0 ≤ max cb_x.compErr cb_y.compErr :=
        le_trans cb_x.h_compErr_nn (le_max_left _ _)
      positivity
    h_compErr_nn := by
      have hη : (0 : R) ≤ η := by positivity
      have hcεM_nn : 0 ≤ max cb_x.compErr cb_y.compErr :=
        le_trans cb_x.h_compErr_nn (le_max_left _ _)
      positivity
    h_bound := by
      set εM : R := max cb_x.relErr cb_y.relErr with hεM_def
      set cεM : R := max cb_x.compErr cb_y.compErr with hcεM_def
      set Sx : R := ∑ i, ((xs i).toVal : R) with hSx_def
      set Sy : R := ∑ i, ((ys i).toVal : R) with hSy_def
      set Ax : R := ∑ i, |((xs i).toVal : R)| with hAx_def
      set Ay : R := ∑ i, |((ys i).toVal : R)| with hAy_def
      have hη : (0 : R) ≤ η := by positivity
      have hAx_nn : 0 ≤ Ax := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hAy_nn : 0 ≤ Ay := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hεx_le : cb_x.relErr ≤ εM := le_max_left _ _
      have hεy_le : cb_y.relErr ≤ εM := le_max_right _ _
      have hcεx_le : cb_x.compErr ≤ cεM := le_max_left _ _
      have hcεy_le : cb_y.compErr ≤ cεM := le_max_right _ _
      have hsum_split : ∑ i, ((Fin.append xs ys) i).toVal (R := R) = Sx + Sy := by
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right, hSx_def, hSy_def]
      have habs_split : ∑ i, |((Fin.append xs ys) i).toVal (R := R)| = Ax + Ay := by
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right, hAx_def, hAy_def]
      rw [hsum_split, habs_split]
      have h_add_sum : |(newSum.toVal : R) - ((cb_x.sum.toVal : R) + cb_y.sum.toVal)| ≤
          η * |(cb_x.sum.toVal : R) + cb_y.sum.toVal| :=
        KahanSum.fpAdd_error_or_zero (R := R) cb_x.sum cb_y.sum newSum hSumAdd hnr_sum
      have h_add_comp : |(newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal)| ≤
          η * |(cb_x.comp.toVal : R) + cb_y.comp.toVal| :=
        KahanSum.fpAdd_error_or_zero (R := R) cb_x.comp cb_y.comp newComp hCompAdd hnr_comp
      have h_sigx : |((cb_x.sum.toVal : R) + cb_x.comp.toVal) - Sx| ≤ cb_x.relErr * Ax := by
        have := cb_x.h_bound; rwa [← hSx_def, ← hAx_def] at this
      have h_sigy : |((cb_y.sum.toVal : R) + cb_y.comp.toVal) - Sy| ≤ cb_y.relErr * Ay := by
        have := cb_y.h_bound; rwa [← hSy_def, ← hAy_def] at this
      have h_comp_x : |(cb_x.comp.toVal : R)| ≤ cb_x.compErr * Ax := by
        have := cb_x.h_comp_bound; rwa [← hAx_def] at this
      have h_comp_y : |(cb_y.comp.toVal : R)| ≤ cb_y.compErr * Ay := by
        have := cb_y.h_comp_bound; rwa [← hAy_def] at this
      have h_compsum_bd : |(cb_x.comp.toVal : R) + cb_y.comp.toVal| ≤ cεM * (Ax + Ay) := by
        calc |(cb_x.comp.toVal : R) + cb_y.comp.toVal|
            ≤ |(cb_x.comp.toVal : R)| + |(cb_y.comp.toVal : R)| := abs_add_le _ _
          _ ≤ cb_x.compErr * Ax + cb_y.compErr * Ay := by linarith
          _ ≤ cεM * Ax + cεM * Ay := by
              have hxm := mul_le_mul_of_nonneg_right hcεx_le hAx_nn
              have hym := mul_le_mul_of_nonneg_right hcεy_le hAy_nn
              linarith
          _ = cεM * (Ax + Ay) := by ring
      have h_sumx_bd : |(cb_x.sum.toVal : R)| ≤ (1 + cb_x.relErr + cb_x.compErr) * Ax := by
        have := cb_x.sum_abs_le; rwa [← hAx_def] at this
      have h_sumy_bd : |(cb_y.sum.toVal : R)| ≤ (1 + cb_y.relErr + cb_y.compErr) * Ay := by
        have := cb_y.sum_abs_le; rwa [← hAy_def] at this
      have h_sums_bd : |(cb_x.sum.toVal : R) + cb_y.sum.toVal| ≤ (1 + εM + cεM) * (Ax + Ay) := by
        have hx_le : 1 + cb_x.relErr + cb_x.compErr ≤ 1 + εM + cεM := by linarith
        have hy_le : 1 + cb_y.relErr + cb_y.compErr ≤ 1 + εM + cεM := by linarith
        calc |(cb_x.sum.toVal : R) + cb_y.sum.toVal|
            ≤ |(cb_x.sum.toVal : R)| + |(cb_y.sum.toVal : R)| := abs_add_le _ _
          _ ≤ (1 + cb_x.relErr + cb_x.compErr) * Ax +
              (1 + cb_y.relErr + cb_y.compErr) * Ay := by linarith
          _ ≤ (1 + εM + cεM) * Ax + (1 + εM + cεM) * Ay := by
              have hxm := mul_le_mul_of_nonneg_right hx_le hAx_nn
              have hym := mul_le_mul_of_nonneg_right hy_le hAy_nn
              linarith
          _ = (1 + εM + cεM) * (Ax + Ay) := by ring
      have h_decomp : (newSum.toVal : R) + newComp.toVal - (Sx + Sy) =
          (((cb_x.sum.toVal : R) + cb_x.comp.toVal) - Sx) +
          (((cb_y.sum.toVal : R) + cb_y.comp.toVal) - Sy) +
          ((newSum.toVal : R) - ((cb_x.sum.toVal : R) + cb_y.sum.toVal)) +
          ((newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal)) := by ring
      have htri1 := abs_add_le
        ((((cb_x.sum.toVal : R) + cb_x.comp.toVal) - Sx) +
         (((cb_y.sum.toVal : R) + cb_y.comp.toVal) - Sy) +
         ((newSum.toVal : R) - ((cb_x.sum.toVal : R) + cb_y.sum.toVal)))
        ((newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal))
      have htri2 := abs_add_le
        ((((cb_x.sum.toVal : R) + cb_x.comp.toVal) - Sx) +
         (((cb_y.sum.toVal : R) + cb_y.comp.toVal) - Sy))
        ((newSum.toVal : R) - ((cb_x.sum.toVal : R) + cb_y.sum.toVal))
      have htri3 := abs_add_le
        (((cb_x.sum.toVal : R) + cb_x.comp.toVal) - Sx)
        (((cb_y.sum.toVal : R) + cb_y.comp.toVal) - Sy)
      have hεxax := mul_le_mul_of_nonneg_right hεx_le hAx_nn
      have hεyay := mul_le_mul_of_nonneg_right hεy_le hAy_nn
      have hsum_mul := mul_le_mul_of_nonneg_left h_sums_bd hη
      have hcomp_mul := mul_le_mul_of_nonneg_left h_compsum_bd hη
      calc |(newSum.toVal : R) + newComp.toVal - (Sx + Sy)|
          = |(((cb_x.sum.toVal : R) + cb_x.comp.toVal) - Sx) +
             (((cb_y.sum.toVal : R) + cb_y.comp.toVal) - Sy) +
             ((newSum.toVal : R) - ((cb_x.sum.toVal : R) + cb_y.sum.toVal)) +
             ((newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal))| := by
               rw [h_decomp]
        _ ≤ |((cb_x.sum.toVal : R) + cb_x.comp.toVal) - Sx| +
            |((cb_y.sum.toVal : R) + cb_y.comp.toVal) - Sy| +
            |(newSum.toVal : R) - ((cb_x.sum.toVal : R) + cb_y.sum.toVal)| +
            |(newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal)| := by
              linarith
        _ ≤ cb_x.relErr * Ax + cb_y.relErr * Ay +
            η * |(cb_x.sum.toVal : R) + cb_y.sum.toVal| +
            η * |(cb_x.comp.toVal : R) + cb_y.comp.toVal| := by linarith
        _ ≤ εM * Ax + εM * Ay +
            η * ((1 + εM + cεM) * (Ax + Ay)) +
            η * (cεM * (Ax + Ay)) := by linarith
        _ = (εM * (1 + η) + η * (1 + 2 * cεM)) * (Ax + Ay) := by ring
    h_comp_bound := by
      set cεM : R := max cb_x.compErr cb_y.compErr with hcεM_def
      set Ax : R := ∑ i, |((xs i).toVal : R)| with hAx_def
      set Ay : R := ∑ i, |((ys i).toVal : R)| with hAy_def
      have hη : (0 : R) ≤ η := by positivity
      have hAx_nn : 0 ≤ Ax := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hAy_nn : 0 ≤ Ay := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hcεx_le : cb_x.compErr ≤ cεM := le_max_left _ _
      have hcεy_le : cb_y.compErr ≤ cεM := le_max_right _ _
      have habs_split : ∑ i, |((Fin.append xs ys) i).toVal (R := R)| = Ax + Ay := by
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right, hAx_def, hAy_def]
      rw [habs_split]
      have h_comp_x : |(cb_x.comp.toVal : R)| ≤ cb_x.compErr * Ax := by
        have := cb_x.h_comp_bound; rwa [← hAx_def] at this
      have h_comp_y : |(cb_y.comp.toVal : R)| ≤ cb_y.compErr * Ay := by
        have := cb_y.h_comp_bound; rwa [← hAy_def] at this
      have h_compsum_bd : |(cb_x.comp.toVal : R) + cb_y.comp.toVal| ≤ cεM * (Ax + Ay) := by
        calc |(cb_x.comp.toVal : R) + cb_y.comp.toVal|
            ≤ |(cb_x.comp.toVal : R)| + |(cb_y.comp.toVal : R)| := abs_add_le _ _
          _ ≤ cb_x.compErr * Ax + cb_y.compErr * Ay := by linarith
          _ ≤ cεM * Ax + cεM * Ay := by
              have hxm := mul_le_mul_of_nonneg_right hcεx_le hAx_nn
              have hym := mul_le_mul_of_nonneg_right hcεy_le hAy_nn
              linarith
          _ = cεM * (Ax + Ay) := by ring
      have h_add_comp : |(newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal)| ≤
          η * |(cb_x.comp.toVal : R) + cb_y.comp.toVal| :=
        KahanSum.fpAdd_error_or_zero (R := R) cb_x.comp cb_y.comp newComp hCompAdd hnr_comp
      have h1η_nn : (0 : R) ≤ 1 + η := by linarith
      have h_key : |(newComp.toVal : R)| ≤
          (1 + η) * |(cb_x.comp.toVal : R) + cb_y.comp.toVal| := by
        have htri := abs_add_le
          ((newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal))
          ((cb_x.comp.toVal : R) + cb_y.comp.toVal)
        have heq : (newComp.toVal : R) - ((cb_x.comp.toVal : R) + cb_y.comp.toVal) +
                   ((cb_x.comp.toVal : R) + cb_y.comp.toVal) = (newComp.toVal : R) := by ring
        rw [heq] at htri
        linarith
      calc |(newComp.toVal : R)|
          ≤ (1 + η) * |(cb_x.comp.toVal : R) + cb_y.comp.toVal| := h_key
        _ ≤ (1 + η) * (cεM * (Ax + Ay)) :=
            mul_le_mul_of_nonneg_left h_compsum_bd h1η_nn
        _ = (1 + η) * cεM * (Ax + Ay) := by ring }

/-- **Append via collapse**: combine two `FpSumBoundCompensated` by collapsing
each via `compensateAndRound` and then using `FpSumBound.append`.

Returns an `FpSumBound` (not a `FpSumBoundCompensated`) because combining two
compensated sums without losing information would require either (a) an extra
`|comp|` bound on each side, or (b) doing a full Neumaier-style combining
step rather than plain `fpAdd`. Neither fits cleanly into this abstraction;
in practice a single Neumaier pass over the concatenated list is the
preferred construction.

Takes three `fpAdd` witnesses: one for each side's collapse, plus one for
the combining add. -/
def FpSumBoundCompensated.appendCollapsed {m n : ℕ}
    {xs : Fin m → FiniteFp} {ys : Fin n → FiniteFp}
    (cb_x : FpSumBoundCompensated xs R) (cb_y : FpSumBoundCompensated ys R)
    {resultX : FiniteFp} (haddX : cb_x.sum + cb_x.comp = Fp.finite resultX)
    (hnrX : isNormalRange ((cb_x.sum.toVal : R) + cb_x.comp.toVal) ∨
            (cb_x.sum.toVal : R) + cb_x.comp.toVal = 0)
    {resultY : FiniteFp} (haddY : cb_y.sum + cb_y.comp = Fp.finite resultY)
    (hnrY : isNormalRange ((cb_y.sum.toVal : R) + cb_y.comp.toVal) ∨
            (cb_y.sum.toVal : R) + cb_y.comp.toVal = 0)
    (combinedResult : FiniteFp)
    (hadd : resultX + resultY = Fp.finite combinedResult)
    (hnr_add : isNormalRange ((resultX.toVal : R) + resultY.toVal) ∨
               (resultX.toVal : R) + resultY.toVal = 0) :
    FpSumBound (Fin.append xs ys) R :=
  (cb_x.compensateAndRound haddX hnrX).append
    (cb_y.compensateAndRound haddY hnrY)
    combinedResult hadd hnr_add

end CompensatedSum

end FpSum
