import Flean.Operations.DotProduct
import Flean.Operations.DotProductFMA
import Flean.Operations.FpSum
import Flean.Util

/-!
# Generic Floating-Point Dot Product with Error Bound

Parallel to `Flean/Operations/FpSum.lean`. Bundles a `FiniteFp` result of
a floating-point dot product with a relative error bound against the true
real-valued dot product, so downstream analyses (e.g. matrix-vector products,
bilinear forms) can be written once against the abstraction.

## Main definitions

* `FpDotProductBound xs ys R` — bundles a `FiniteFp` result with a bound
  `|result - Σ xs_i · ys_i| ≤ relErr · Σ|xs_i · ys_i|`.
* `FpDotProductBound.ofDotProduct` — build one from a `DotProduct.DPTrace`
  (sequential multiply-add). Gives `relErr = (1+η)^n - 1`.
* `FpDotProductBound.ofDotProductFMA` — build one from a
  `DotProductFMA.FMADPTrace` (fused multiply-add). Same `(1+η)^n - 1` bound
  but without the zero-init exact-step trick (FMA rounds once per step).
-/

set_option autoImplicit false

namespace FpDotProduct

open Finset BigOperators

variable [FloatFormat]

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The `FpDotProductBound` structure -/

/-- Bundles a computed FP dot product with a relative error bound, relative
to the *true* real dot product `Σ (xs i).toVal · (ys i).toVal`. -/
structure FpDotProductBound {n : ℕ} (xs ys : Fin n → FiniteFp) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] where
  /-- The FP result of the dot product. -/
  result : FiniteFp
  /-- Relative error coefficient (e.g. `(1+η)^n - 1`). -/
  relErr : R
  /-- Nonnegativity of `relErr`. -/
  h_relErr_nn : (0 : R) ≤ relErr
  /-- The relative error bound, relative to `Σ |xs_i · ys_i|`. -/
  h_bound : |(result.toVal : R) -
              ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
              relErr * ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)|

/-! ## Adapter helpers -/

section Adapter

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- Sum of real products over a pair list built via `List.ofFn`. -/
private lemma sum_ofFn_pair_prod {n : ℕ} (xs ys : Fin n → FiniteFp) :
    ((List.ofFn (fun i => (xs i, ys i))).map
        (fun p => ((p.1.toVal : R)) * p.2.toVal)).sum =
      ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R) := by
  simp [List.map_ofFn, List.sum_ofFn]

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Sum of absolute real products over a pair list built via `List.ofFn`. -/
private lemma sum_ofFn_pair_abs_prod {n : ℕ} (xs ys : Fin n → FiniteFp) :
    ((List.ofFn (fun i => (xs i, ys i))).map
        (fun p => |((p.1.toVal : R)) * p.2.toVal|)).sum =
      ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| := by
  simp [List.map_ofFn, List.sum_ofFn]

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- Length of a pair list built via `List.ofFn` equals `n`. -/
private lemma ofFn_pair_length {n : ℕ} (xs ys : Fin n → FiniteFp) :
    (List.ofFn (fun i => (xs i, ys i))).length = n :=
  List.length_ofFn

end Adapter

/-! ## Adapter: `DotProduct.DPTrace` → `FpDotProductBound` -/

section OfDotProduct

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]

/-- **Constructor**: a `DotProduct.DPTrace` over the pair list built from
`xs`/`ys` with zero initial accumulator gives an `FpDotProductBound` with
`relErr = (1+η)^n - 1`. -/
def FpDotProductBound.ofDotProduct {n : ℕ} (xs ys : Fin n → FiniteFp)
    {init result : FiniteFp}
    (trace : DotProduct.DPTrace (List.ofFn (fun i => (xs i, ys i))) init result)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    FpDotProductBound xs ys R :=
  let err := (1 + η : R) ^ n - 1
  have hη : (0 : R) ≤ η := by positivity
  have h1η : (1 : R) ≤ 1 + η := by linarith
  have herr_nn : (0 : R) ≤ err := by
    have hp : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
    linarith
  have h_bnd : |(result.toVal : R) -
                ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
               err * ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| := by
    have h := DotProduct.dp_error_bound (R := R) trace hinit hnr
    rw [sum_ofFn_pair_prod (R := R) xs ys,
        sum_ofFn_pair_abs_prod (R := R) xs ys,
        ofFn_pair_length xs ys] at h
    exact h
  { result := result
    relErr := err
    h_relErr_nn := herr_nn
    h_bound := h_bnd }

end OfDotProduct

/-! ## Adapter: `DotProductFMA.FMADPTrace` → `FpDotProductBound` -/

section OfDotProductFMA

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: a `DotProductFMA.FMADPTrace` over the pair list built
from `xs`/`ys` with zero initial accumulator gives an `FpDotProductBound`
with `relErr = (1+η)^n - 1`.

Unlike the non-FMA adapter, this does not require `RModeIdem`: the FMA step
rounds exactly once per pair, so the `n`-power bound is direct (no
zero-add exact-step trick needed). -/
def FpDotProductBound.ofDotProductFMA {n : ℕ} (xs ys : Fin n → FiniteFp)
    {init result : FiniteFp}
    (trace : DotProductFMA.FMADPTrace
        (List.ofFn (fun i => (xs i, ys i))) init result)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    FpDotProductBound xs ys R :=
  let err := (1 + η : R) ^ n - 1
  have hη : (0 : R) ≤ η := by positivity
  have h1η : (1 : R) ≤ 1 + η := by linarith
  have herr_nn : (0 : R) ≤ err := by
    have hp : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
    linarith
  have h_bnd : |(result.toVal : R) -
                ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
               err * ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| := by
    have h := DotProductFMA.fma_dp_error_bound (R := R) trace hinit hnr
    rw [sum_ofFn_pair_prod (R := R) xs ys,
        sum_ofFn_pair_abs_prod (R := R) xs ys,
        ofFn_pair_length xs ys] at h
    exact h
  { result := result
    relErr := err
    h_relErr_nn := herr_nn
    h_bound := h_bnd }

end OfDotProductFMA

/-! ## Adapter: products-then-sum → `FpDotProductBound`

Generic helper: take rounded per-pair products `ps i = fl(xs i · ys i)` plus
an `FpSumBound` on `ps`, and compose the per-product mul error (η each) with
the sum bound to get an `FpDotProductBound xs ys R` against the *true* real
dot product `Σ xs_i · ys_i`.

Composed coefficient: `relErr = sb.relErr · (1 + η) + η`.

Mirrors the compensated-case `FpDotProductBoundCompensated.ofProducts`.
Used below by `ofKahan` and `ofPairwiseSum` to wrap tighter sum primitives
into the dot-product abstraction.
-/

section OfProductsBound

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: given rounded per-pair products `ps i = fl(xs i · ys i)`
with rounding witnesses, and an `FpSumBound` over `ps`, package the
composition as an `FpDotProductBound xs ys R`.

Composed coefficient: `relErr = sb.relErr · (1 + η) + η`. -/
def FpDotProductBound.ofProductsBound {n : ℕ} (xs ys : Fin n → FiniteFp)
    {ps : Fin n → FiniteFp}
    (hprod : ∀ i, xs i * ys i = Fp.finite (ps i))
    (hnr_mul : ∀ i, isNormalRange ((xs i).toVal * (ys i).toVal : R) ∨
                     ((xs i).toVal : R) * (ys i).toVal = 0)
    (sb : FpSum.FpSumBound ps R) :
    FpDotProductBound xs ys R :=
  have hη : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  { result := sb.result
    relErr := sb.relErr * (1 + η) + η
    h_relErr_nn := by
      have h1 : 0 ≤ sb.relErr * (1 + η) := mul_nonneg sb.h_relErr_nn h1η_nn
      linarith
    h_bound := by
      set T : R := ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| with hT_def
      set T' : R := ∑ i, |((ps i).toVal : R)| with hT'_def
      set S : R := ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R) with hS_def
      set S' : R := ∑ i, ((ps i).toVal : R) with hS'_def
      have hT_nn : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hmul_err : ∀ i, |((ps i).toVal : R) -
                             (xs i).toVal * (ys i).toVal| ≤
                           η * |((xs i).toVal : R) * (ys i).toVal| := fun i =>
        KahanSum.fpMul_error_or_zero (R := R) (xs i) (ys i) (ps i)
          (hprod i) (hnr_mul i)
      have hT'_le : T' ≤ (1 + η) * T := by
        have hbd : ∀ i ∈ Finset.univ,
            |((ps i).toVal : R)| ≤
            (1 + η) * |((xs i).toVal : R) * ((ys i).toVal : R)| := by
          intro i _
          have h1 := abs_sub_abs_le_abs_sub ((ps i).toVal : R)
            ((xs i).toVal * (ys i).toVal)
          have h2 := hmul_err i
          linarith
        calc T' = ∑ i, |((ps i).toVal : R)| := rfl
          _ ≤ ∑ i, (1 + η) * |((xs i).toVal : R) * ((ys i).toVal : R)| :=
              Finset.sum_le_sum hbd
          _ = (1 + η) * T := by rw [← Finset.mul_sum]
      have hS_sub : |S' - S| ≤ η * T := by
        have hsum_sub : S' - S =
            ∑ i, (((ps i).toVal : R) - ((xs i).toVal : R) * ((ys i).toVal : R)) := by
          rw [Finset.sum_sub_distrib]
        calc |S' - S| = |∑ i,
                (((ps i).toVal : R) - ((xs i).toVal : R) * ((ys i).toVal : R))| := by
              rw [hsum_sub]
          _ ≤ ∑ i, |((ps i).toVal : R) - ((xs i).toVal : R) * ((ys i).toVal : R)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, η * |((xs i).toVal : R) * ((ys i).toVal : R)| :=
              Finset.sum_le_sum (fun i _ => hmul_err i)
          _ = η * T := by rw [← Finset.mul_sum]
      have hsb : |(sb.result.toVal : R) - S'| ≤ sb.relErr * T' := sb.h_bound
      calc |(sb.result.toVal : R) - S|
          = |((sb.result.toVal : R) - S') + (S' - S)| := by ring_nf
        _ ≤ |(sb.result.toVal : R) - S'| + |S' - S| := abs_add_le _ _
        _ ≤ sb.relErr * T' + η * T := by linarith [hsb, hS_sub]
        _ ≤ sb.relErr * ((1 + η) * T) + η * T := by
            have := mul_le_mul_of_nonneg_left hT'_le sb.h_relErr_nn
            linarith
        _ = (sb.relErr * (1 + η) + η) * T := by ring }

end OfProductsBound

/-! ## Adapter: Kahan-summed products → `FpDotProductBound`

Per-pair multiply, then Kahan-accumulate.

Composed bound: `relErr = (2η + n·η²)·(1 + η) + η ≈ 3η + (n+2)·η²`.

For very small `n` this can exceed `ofDotProduct`'s `(1+η)^n - 1` bound:
* **n=2**: ofDotProduct gives `2η + η²`; ofKahan gives `~3η + 4η² + 2η³`.
  Caller should prefer `ofDotProduct`/`ofDotProductFMA` at n ≤ 2.
* **n=3**: roughly equivalent (both leading-order `3η`).
* **n ≥ 4**: ofKahan's `O(n·η²)` term beats `ofDotProduct`'s `O(n·(n−1)·η²)`.

Pairwise (`ofPairwiseSum`, below) is asymptotically tighter than Kahan due
to `log₂ n` depth versus Kahan's linear `n·η²` term, but Kahan is one-pass
and uses the compensator state directly. -/

section OfKahan

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: rounded per-pair products `ps` followed by a
`KahanSum.Trace` on those products gives an `FpDotProductBound` with
`relErr = (2η + n·η²)·(1 + η) + η`.

Hypotheses:
* `hprod` / `hnr_mul` — per-pair mul rounding witnesses (each contributing η).
* `trace` — Kahan summation of `List.ofFn ps`.
* `hinit_sum` / `hinit_comp` — zero-initialized Kahan state.
* `hexact` / `hnr_kahan` / `hM` — mirrors `FpSumBound.ofKahanTrace`. -/
def FpDotProductBound.ofKahan {n : ℕ} (xs ys : Fin n → FiniteFp)
    {ps : Fin n → FiniteFp}
    (hprod : ∀ i, xs i * ys i = Fp.finite (ps i))
    (hnr_mul : ∀ i, isNormalRange ((xs i).toVal * (ys i).toVal : R) ∨
                     ((xs i).toVal : R) * (ys i).toVal = 0)
    {init final : KahanSum.State}
    (trace : KahanSum.Trace (List.ofFn ps) init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : KahanSum.State) (x : FiniteFp)
                (step : KahanSum.StepWitness st x),
      KahanSum.StepTwoSumExact (R := R) st x step)
    (hnr_kahan : ∀ (st : KahanSum.State) (x : FiniteFp)
                   (step : KahanSum.StepWitness st x),
      KahanSum.StepNormalRange (R := R) st x step)
    (hM : ∀ (st : KahanSum.State) (x : FiniteFp)
            (step : KahanSum.StepWitness st x),
      |(st.sum.toVal : R) + step.y.toVal| ≤
        ((List.ofFn ps).map (fun x => |x.toVal (R := R)|)).sum) :
    FpDotProductBound xs ys R :=
  FpDotProductBound.ofProductsBound xs ys hprod hnr_mul
    (FpSum.FpSumBound.ofKahanTrace ps trace
      hinit_sum hinit_comp hexact hnr_kahan hM)

end OfKahan

/-! ## Adapter: pairwise-summed products → `FpDotProductBound`

Per-pair multiply, then balanced/tree summation of the products.

Composed bound: `relErr = ((1+η)^d - 1)·(1+η) + η` where `d = trace.depth`.
For balanced trees with `n` leaves, `d = ⌈log₂ n⌉`, so the leading-order
term is `O((⌈log₂ n⌉ + 1)·η)` — asymptotically tighter than both
`ofDotProduct` (`O(n·η)`) and `ofKahan` (`O(η + n·η²)`).

For depth-1 trees (n=2 leaves) this collapses to `2η + η²` — same as
`ofDotProduct` at n=2, and tighter than `ofKahan` at n=2. -/

section OfPairwiseSum

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: rounded per-pair products `ps` followed by a
`PairwiseSum.Trace` over `List.ofFn ps` gives an `FpDotProductBound` with
`relErr = ((1+η)^d - 1)·(1+η) + η`, where `d = trace.depth`. -/
def FpDotProductBound.ofPairwiseSum {n : ℕ} (xs ys : Fin n → FiniteFp)
    {ps : Fin n → FiniteFp}
    (hprod : ∀ i, xs i * ys i = Fp.finite (ps i))
    (hnr_mul : ∀ i, isNormalRange ((xs i).toVal * (ys i).toVal : R) ∨
                     ((xs i).toVal : R) * (ys i).toVal = 0)
    {sumResult : FiniteFp}
    (trace : PairwiseSum.Trace (List.ofFn ps) sumResult)
    (hnr_sum : trace.AllNormalRange (R := R)) :
    FpDotProductBound xs ys R :=
  FpDotProductBound.ofProductsBound xs ys hprod hnr_mul
    (FpSum.FpSumBound.ofPairwise ps trace hnr_sum)

end OfPairwiseSum

/-! ## Structural adapters: `weaken`, `reindex`, `congr` -/

section Adapters

/-- Relax the relative-error coefficient. -/
def FpDotProductBound.weaken {n : ℕ} {xs ys : Fin n → FiniteFp}
    (b : FpDotProductBound xs ys R) (newRelErr : R)
    (h_ge : b.relErr ≤ newRelErr) :
    FpDotProductBound xs ys R :=
  { result := b.result
    relErr := newRelErr
    h_relErr_nn := le_trans b.h_relErr_nn h_ge
    h_bound := by
      have habs_nn : (0 : R) ≤ ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      calc |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)|
          ≤ b.relErr * ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| := b.h_bound
        _ ≤ newRelErr * ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| :=
            mul_le_mul_of_nonneg_right h_ge habs_nn }

/-- Reindex both input vectors by a single permutation of `Fin n`. -/
def FpDotProductBound.reindex {n : ℕ} {xs ys : Fin n → FiniteFp}
    (b : FpDotProductBound xs ys R) (e : Fin n ≃ Fin n) :
    FpDotProductBound (xs ∘ e) (ys ∘ e) R :=
  { result := b.result
    relErr := b.relErr
    h_relErr_nn := b.h_relErr_nn
    h_bound := by
      have hsum : ∑ i, (((xs ∘ e) i).toVal : R) * (((ys ∘ e) i).toVal : R) =
                  ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      have habs : ∑ i, |(((xs ∘ e) i).toVal : R) * (((ys ∘ e) i).toVal : R)| =
                  ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      rw [hsum, habs]
      exact b.h_bound }

/-- Rewrite the inputs along pointwise equalities `xs = xs'` and `ys = ys'`. -/
def FpDotProductBound.congr {n : ℕ} {xs xs' ys ys' : Fin n → FiniteFp}
    (b : FpDotProductBound xs ys R) (hxs : xs = xs') (hys : ys = ys') :
    FpDotProductBound xs' ys' R :=
  hys ▸ hxs ▸ b

end Adapters

/-! ## Append — combining two independent dot products

If `(xs₁, ys₁)` and `(xs₂, ys₂)` each come with an `FpDotProductBound`, and
their partial results sum correctly in FP, the concatenated pair list has a
combined bound. Parallels `FpSumBound.append`.

The combined relative error is bounded by
`max(εx, εy) + η + η·max(εx, εy)` (loosely: `max(εx,εy) + 2η`). -/

section Append

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Append two dot-product bounds** via a single `fpAdd` of the partial
results. -/
def FpDotProductBound.append {m n : ℕ}
    {xs₁ ys₁ : Fin m → FiniteFp} {xs₂ ys₂ : Fin n → FiniteFp}
    (bx : FpDotProductBound xs₁ ys₁ R)
    (by_ : FpDotProductBound xs₂ ys₂ R)
    (combinedResult : FiniteFp)
    (hadd : bx.result + by_.result = Fp.finite combinedResult)
    (hnr_add : isNormalRange ((bx.result.toVal : R) + by_.result.toVal) ∨
               (bx.result.toVal : R) + by_.result.toVal = 0) :
    FpDotProductBound (Fin.append xs₁ xs₂) (Fin.append ys₁ ys₂) R :=
  let εM : R := max bx.relErr by_.relErr
  have hη_nn : (0 : R) ≤ η := by positivity
  have hεM_nn : 0 ≤ εM := le_trans bx.h_relErr_nn (le_max_left _ _)
  have hmul_nn : 0 ≤ (η : R) * εM := mul_nonneg hη_nn hεM_nn
  { result := combinedResult
    relErr := εM + (η : R) + (η : R) * εM
    h_relErr_nn := by positivity
    h_bound := by
      have hadd_err : |(combinedResult.toVal : R) -
                       (bx.result.toVal + by_.result.toVal)| ≤
                      (η : R) * |(bx.result.toVal : R) + by_.result.toVal| :=
        KahanSum.fpAdd_error_or_zero (R := R) bx.result by_.result combinedResult hadd hnr_add
      -- Split appended product sums into the two pieces.
      have hsum_split : ∑ i, ((Fin.append xs₁ xs₂) i).toVal (R := R) *
                              ((Fin.append ys₁ ys₂) i).toVal =
                        (∑ i, ((xs₁ i).toVal : R) * ((ys₁ i).toVal : R)) +
                        (∑ i, ((xs₂ i).toVal : R) * ((ys₂ i).toVal : R)) := by
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right]
      have habs_split : ∑ i, |((Fin.append xs₁ xs₂) i).toVal (R := R) *
                              ((Fin.append ys₁ ys₂) i).toVal| =
                        (∑ i, |((xs₁ i).toVal : R) * ((ys₁ i).toVal : R)|) +
                        (∑ i, |((xs₂ i).toVal : R) * ((ys₂ i).toVal : R)|) := by
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right]
      set Sx : R := ∑ i, ((xs₁ i).toVal : R) * ((ys₁ i).toVal : R) with hSx_def
      set Sy : R := ∑ i, ((xs₂ i).toVal : R) * ((ys₂ i).toVal : R) with hSy_def
      set Ax : R := ∑ i, |((xs₁ i).toVal : R) * ((ys₁ i).toVal : R)| with hAx_def
      set Ay : R := ∑ i, |((xs₂ i).toVal : R) * ((ys₂ i).toVal : R)| with hAy_def
      have hAx_nn : 0 ≤ Ax := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hAy_nn : 0 ≤ Ay := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hSx_le : |Sx| ≤ Ax := Finset.abs_sum_le_sum_abs _ _
      have hSy_le : |Sy| ≤ Ay := Finset.abs_sum_le_sum_abs _ _
      have hx_bd : |(bx.result.toVal : R) - Sx| ≤ bx.relErr * Ax := bx.h_bound
      have hy_bd : |(by_.result.toVal : R) - Sy| ≤ by_.relErr * Ay := by_.h_bound
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
      have hbx_le : |(bx.result.toVal : R)| ≤ |Sx| + bx.relErr * Ax := by
        have := abs_sub_abs_le_abs_sub (bx.result.toVal : R) Sx
        linarith
      have hby_le : |(by_.result.toVal : R)| ≤ |Sy| + by_.relErr * Ay := by
        have := abs_sub_abs_le_abs_sub (by_.result.toVal : R) Sy
        linarith
      have hsum_bd : |(bx.result.toVal : R) + by_.result.toVal| ≤
          Ax + bx.relErr * Ax + Ay + by_.relErr * Ay := by
        have := abs_add_le (bx.result.toVal : R) by_.result.toVal
        linarith [hSx_le, hSy_le]
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

/-! ## `gamma_n`-form constructors -/

section Gamma

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor (γₙ form)**: a `DotProduct.DPTrace` with zero initial
accumulator gives an `FpDotProductBound` with `relErr = γₙ = n·η / (1 − n·η)`,
provided `n·η < 1`. -/
noncomputable def FpDotProductBound.ofDotProduct_gamma [RModeIdem R] {n : ℕ}
    (xs ys : Fin n → FiniteFp) {init result : FiniteFp}
    (trace : DotProduct.DPTrace (List.ofFn (fun i => (xs i, ys i))) init result)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (n : R) * η < 1) :
    FpDotProductBound xs ys R :=
  have hlen : (List.ofFn (fun i => (xs i, ys i))).length = n := ofFn_pair_length xs ys
  have hsmall' : ((List.ofFn (fun i => (xs i, ys i))).length : R) * η < 1 := by
    rw [hlen]; exact hsmall
  have hη : (0 : R) ≤ η := by positivity
  have h1η : (1 : R) ≤ 1 + η := by linarith
  have hpow : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
  have h_err_le : (1 + η : R) ^ n - 1 ≤ gamma_n (R := R) n :=
    pow_sub_one_le_gamma (R := R) n hsmall
  have hgamma_nn : (0 : R) ≤ gamma_n (R := R) n := by linarith
  have h_bnd : |(result.toVal : R) -
                ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
               gamma_n (R := R) n *
                 ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| := by
    have h := DotProduct.dp_error_bound_gamma (R := R) trace hinit hnr hsmall'
    rw [sum_ofFn_pair_prod (R := R) xs ys,
        sum_ofFn_pair_abs_prod (R := R) xs ys, hlen] at h
    exact h
  { result := result
    relErr := gamma_n (R := R) n
    h_relErr_nn := hgamma_nn
    h_bound := h_bnd }

/-- **Constructor (γₙ form)**: a `DotProductFMA.FMADPTrace` with zero initial
accumulator gives an `FpDotProductBound` with `relErr = γₙ`, provided
`n·η < 1`. -/
noncomputable def FpDotProductBound.ofDotProductFMA_gamma {n : ℕ}
    (xs ys : Fin n → FiniteFp) {init result : FiniteFp}
    (trace : DotProductFMA.FMADPTrace
        (List.ofFn (fun i => (xs i, ys i))) init result)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (n : R) * η < 1) :
    FpDotProductBound xs ys R :=
  have hlen : (List.ofFn (fun i => (xs i, ys i))).length = n := ofFn_pair_length xs ys
  have hsmall' : ((List.ofFn (fun i => (xs i, ys i))).length : R) * η < 1 := by
    rw [hlen]; exact hsmall
  have hη : (0 : R) ≤ η := by positivity
  have h1η : (1 : R) ≤ 1 + η := by linarith
  have hpow : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
  have h_err_le : (1 + η : R) ^ n - 1 ≤ gamma_n (R := R) n :=
    pow_sub_one_le_gamma (R := R) n hsmall
  have hgamma_nn : (0 : R) ≤ gamma_n (R := R) n := by linarith
  have h_bnd : |(result.toVal : R) -
                ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
               gamma_n (R := R) n *
                 ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| := by
    have h := DotProductFMA.fma_dp_error_bound_gamma (R := R) trace hinit hnr hsmall'
    rw [sum_ofFn_pair_prod (R := R) xs ys,
        sum_ofFn_pair_abs_prod (R := R) xs ys, hlen] at h
    exact h
  { result := result
    relErr := gamma_n (R := R) n
    h_relErr_nn := hgamma_nn
    h_bound := h_bnd }

end Gamma

/-! ## Compensated dot product

Mirrors `FpSumBoundCompensated`: bundles a pair `(sum, comp)` whose
compensated value `sigma := sum.toVal + comp.toVal` approximates the real
dot product `Σ xs_i · ys_i`. The natural way to build one is via
`ofProducts`: supply rounded products `ps_i = fl(xs_i · ys_i)` and a
compensated sum bound over `ps`, and the two errors compose. -/

/-- Bundles a *compensated* FP dot product `(sum, comp)` with two bounds:
a relative error on `|(sum + comp) − Σ xs_i·ys_i|`, and a separate relative
bound on `|comp|`. Both are stated against `Σ |xs_i·ys_i|`. -/
structure FpDotProductBoundCompensated {n : ℕ}
    (xs ys : Fin n → FiniteFp) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] where
  /-- Running FP dot product. -/
  sum : FiniteFp
  /-- Accumulated FP compensator. -/
  comp : FiniteFp
  /-- Relative error of the compensated value `sum.toVal + comp.toVal`. -/
  relErr : R
  /-- Relative bound on `|comp|`. -/
  compErr : R
  /-- Nonnegativity of `relErr`. -/
  h_relErr_nn : (0 : R) ≤ relErr
  /-- Nonnegativity of `compErr`. -/
  h_compErr_nn : (0 : R) ≤ compErr
  /-- `|(sum + comp) − Σ xs_i·ys_i| ≤ relErr · Σ |xs_i·ys_i|`. -/
  h_bound : |((sum.toVal : R) + comp.toVal) -
              ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R)| ≤
              relErr * ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)|
  /-- `|comp| ≤ compErr · Σ |xs_i·ys_i|`. -/
  h_comp_bound : |(comp.toVal : R)| ≤
              compErr * ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)|

/-- The compensated value `sigma = sum.toVal + comp.toVal`. -/
@[simp] def FpDotProductBoundCompensated.sigma {n : ℕ}
    {xs ys : Fin n → FiniteFp} {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (cb : FpDotProductBoundCompensated xs ys R) : R :=
  (cb.sum.toVal : R) + cb.comp.toVal

/-! ## Adapter: rounded products + compensated sum → compensated dot product -/

section OfProducts

variable [RMode R] [RModeExec] [RModeNearest R] [RoundIntSigMSound R]

/-- **Constructor**: given rounded products `ps i = fl(xs i · ys i)` with
their rounding witnesses, and an `FpSumBoundCompensated` over `ps`, package
the composition as an `FpDotProductBoundCompensated`.

Per-product mul rounding contributes `η`; the sum's compensated bound
contributes `cb.relErr`/`cb.compErr`. These compose to:
- `relErr = cb.relErr · (1 + η) + η`
- `compErr = cb.compErr · (1 + η)`

all stated against the *true* real dot product `Σ xs_i · ys_i`. -/
def FpDotProductBoundCompensated.ofProducts {n : ℕ} (xs ys : Fin n → FiniteFp)
    {ps : Fin n → FiniteFp}
    (hprod : ∀ i, xs i * ys i = Fp.finite (ps i))
    (hnr : ∀ i, isNormalRange ((xs i).toVal * (ys i).toVal : R) ∨
                 ((xs i).toVal : R) * (ys i).toVal = 0)
    (cb : FpSum.FpSumBoundCompensated ps R) :
    FpDotProductBoundCompensated xs ys R :=
  have hη : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  { sum := cb.sum
    comp := cb.comp
    relErr := cb.relErr * (1 + η) + η
    compErr := cb.compErr * (1 + η)
    h_relErr_nn := by
      have h1 : 0 ≤ cb.relErr * (1 + η) := mul_nonneg cb.h_relErr_nn h1η_nn
      linarith
    h_compErr_nn := mul_nonneg cb.h_compErr_nn h1η_nn
    h_bound := by
      set T : R := ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| with hT_def
      set T' : R := ∑ i, |((ps i).toVal : R)| with hT'_def
      set S : R := ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R) with hS_def
      set S' : R := ∑ i, ((ps i).toVal : R) with hS'_def
      set σ : R := ((cb.sum.toVal : R) + cb.comp.toVal) with hσ_def
      have hT_nn : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hmul_err : ∀ i, |((ps i).toVal : R) -
                             (xs i).toVal * (ys i).toVal| ≤
                           η * |((xs i).toVal : R) * (ys i).toVal| := fun i =>
        KahanSum.fpMul_error_or_zero (R := R) (xs i) (ys i) (ps i) (hprod i) (hnr i)
      have hT'_le : T' ≤ (1 + η) * T := by
        have hbd : ∀ i ∈ Finset.univ,
            |((ps i).toVal : R)| ≤
            (1 + η) * |((xs i).toVal : R) * ((ys i).toVal : R)| := by
          intro i _
          have h1 := abs_sub_abs_le_abs_sub ((ps i).toVal : R)
            ((xs i).toVal * (ys i).toVal)
          have h2 := hmul_err i
          linarith
        calc T' = ∑ i, |((ps i).toVal : R)| := rfl
          _ ≤ ∑ i, (1 + η) * |((xs i).toVal : R) * ((ys i).toVal : R)| :=
              Finset.sum_le_sum hbd
          _ = (1 + η) * T := by rw [← Finset.mul_sum]
      have hS_sub : |S' - S| ≤ η * T := by
        have hsum_sub : S' - S =
            ∑ i, (((ps i).toVal : R) - ((xs i).toVal : R) * ((ys i).toVal : R)) := by
          rw [Finset.sum_sub_distrib]
        calc |S' - S| = |∑ i,
                (((ps i).toVal : R) - ((xs i).toVal : R) * ((ys i).toVal : R))| := by
              rw [hsum_sub]
          _ ≤ ∑ i, |((ps i).toVal : R) - ((xs i).toVal : R) * ((ys i).toVal : R)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, η * |((xs i).toVal : R) * ((ys i).toVal : R)| :=
              Finset.sum_le_sum (fun i _ => hmul_err i)
          _ = η * T := by rw [← Finset.mul_sum]
      have hcb : |σ - S'| ≤ cb.relErr * T' := cb.h_bound
      calc |σ - S|
          = |(σ - S') + (S' - S)| := by ring_nf
        _ ≤ |σ - S'| + |S' - S| := abs_add_le _ _
        _ ≤ cb.relErr * T' + η * T := by linarith [hcb, hS_sub]
        _ ≤ cb.relErr * ((1 + η) * T) + η * T := by
            have := mul_le_mul_of_nonneg_left hT'_le cb.h_relErr_nn
            linarith
        _ = (cb.relErr * (1 + η) + η) * T := by ring
    h_comp_bound := by
      set T : R := ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| with hT_def
      set T' : R := ∑ i, |((ps i).toVal : R)| with hT'_def
      have hmul_err : ∀ i, |((ps i).toVal : R) -
                             (xs i).toVal * (ys i).toVal| ≤
                           η * |((xs i).toVal : R) * (ys i).toVal| := fun i =>
        KahanSum.fpMul_error_or_zero (R := R) (xs i) (ys i) (ps i) (hprod i) (hnr i)
      have hT'_le : T' ≤ (1 + η) * T := by
        have hbd : ∀ i ∈ Finset.univ,
            |((ps i).toVal : R)| ≤
            (1 + η) * |((xs i).toVal : R) * ((ys i).toVal : R)| := by
          intro i _
          have h1 := abs_sub_abs_le_abs_sub ((ps i).toVal : R)
            ((xs i).toVal * (ys i).toVal)
          have h2 := hmul_err i
          linarith
        calc T' = ∑ i, |((ps i).toVal : R)| := rfl
          _ ≤ ∑ i, (1 + η) * |((xs i).toVal : R) * ((ys i).toVal : R)| :=
              Finset.sum_le_sum hbd
          _ = (1 + η) * T := by rw [← Finset.mul_sum]
      calc |(cb.comp.toVal : R)|
          ≤ cb.compErr * T' := cb.h_comp_bound
        _ ≤ cb.compErr * ((1 + η) * T) :=
            mul_le_mul_of_nonneg_left hT'_le cb.h_compErr_nn
        _ = cb.compErr * (1 + η) * T := by ring }

/-- **Collapse** a compensated dot-product bound into a plain
`FpDotProductBound` via one final `fpAdd(sum, comp)`. Mirrors
`FpSumBoundCompensated.compensateAndRound`. New `relErr = cb.relErr·(1+η) + η`. -/
def FpDotProductBoundCompensated.compensateAndRound {n : ℕ}
    {xs ys : Fin n → FiniteFp}
    (cb : FpDotProductBoundCompensated xs ys R) {finalResult : FiniteFp}
    (hadd : cb.sum + cb.comp = Fp.finite finalResult)
    (hnr_add : isNormalRange ((cb.sum.toVal : R) + cb.comp.toVal) ∨
               (cb.sum.toVal : R) + cb.comp.toVal = 0) :
    FpDotProductBound xs ys R :=
  have hη : (0 : R) ≤ η := by positivity
  have h1η : (0 : R) ≤ 1 + η := by linarith
  { result := finalResult
    relErr := cb.relErr * (1 + η) + η
    h_relErr_nn := by
      have : 0 ≤ cb.relErr * (1 + η) := mul_nonneg cb.h_relErr_nn h1η
      linarith
    h_bound := by
      set T : R := ∑ i, |((xs i).toVal : R) * ((ys i).toVal : R)| with hT_def
      set S : R := ∑ i, ((xs i).toVal : R) * ((ys i).toVal : R) with hS_def
      set σ : R := ((cb.sum.toVal : R) + cb.comp.toVal) with hσ_def
      have hT_nn : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hS_le : |S| ≤ T := Finset.abs_sum_le_sum_abs _ _
      -- fpAdd error on the sum+comp rounding
      have hadd_err : |(finalResult.toVal : R) - σ| ≤ η * |σ| :=
        KahanSum.fpAdd_error_or_zero (R := R) cb.sum cb.comp finalResult hadd hnr_add
      have hcb := cb.h_bound
      -- |σ - S| ≤ cb.relErr · T
      have hσ_sub : |σ - S| ≤ cb.relErr * T := hcb
      -- |σ| ≤ |S| + cb.relErr · T ≤ (1 + cb.relErr) · T
      have hσ_le : |σ| ≤ (1 + cb.relErr) * T := by
        have h1 := abs_sub_abs_le_abs_sub σ S
        have : |σ| ≤ |S| + cb.relErr * T := by linarith
        have hSleT : |S| ≤ T := hS_le
        linarith
      -- Triangle: |finalResult - S| ≤ |finalResult - σ| + |σ - S|
      calc |(finalResult.toVal : R) - S|
          = |((finalResult.toVal : R) - σ) + (σ - S)| := by ring_nf
        _ ≤ |(finalResult.toVal : R) - σ| + |σ - S| := abs_add_le _ _
        _ ≤ η * |σ| + cb.relErr * T := by linarith [hadd_err, hσ_sub]
        _ ≤ η * ((1 + cb.relErr) * T) + cb.relErr * T := by
            have := mul_le_mul_of_nonneg_left hσ_le hη
            linarith
        _ = (cb.relErr * (1 + η) + η) * T := by ring }

end OfProducts

end FpDotProduct
