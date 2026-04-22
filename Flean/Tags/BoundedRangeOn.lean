import Flean.Tags.Attributes
import Flean.Tags.BoundedRange
import Flean.Tags.AbsBound
import Flean.Operations.FpSum

/-!
# Tag: `IsBoundedRangeOn` (partitioned)

R-parametric tag asserting the interval bound `I` holds only on a
designated subset `S ⊆ Fin n` of the indices.  The complement `Sᶜ`
can carry arbitrary values — "possibly subnormal" or otherwise
ill-behaved — and consumer theorems that need per-index structural
information branch on S-membership.

## Framework novelty

Prior vector-level tags (`IsBoundedRange`, `IsSimplex`, `IsOneHot`,
`IsProb`) assume a *uniform* property over all `Fin n` indices.
`IsBoundedRangeOn` is the first tag in the framework that composes
with `Finset`-subsetting, allowing **heterogeneous per-index
tagging**: the same vector can carry `IsBoundedRangeOn S I` and
`IsBoundedRangeOn S' I'` simultaneously for different (S, I) pairs.

This is the Phase 2 "Candidate A" exploration (backlog T-M3),
formerly queued and now shipped.

## Position in the tag lattice

Generalizes `IsBoundedRange` via `IsBoundedRange.toBoundedRangeOn_univ`
(holding on the full domain).  Projects to per-index `HasAbsBound`
via `IsBoundedRangeOn.toHasAbsBound_of_mem`.

## Payoff

Downstream theorems can branch per-i:
- `i ∈ S`: use the tight/bounded path.
- `i ∉ S`: fall back to the general (looser) bound.

Demonstrated by `sum_abs_le_on`: the weighted sum over `S` is bounded
by `|S| · I.maxMag`, while the full sum would blow up if the
complement carried arbitrary magnitudes.
-/

set_option autoImplicit false

namespace Flean.Tags

open Finset BigOperators

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## The tag -/

/-- `IsBoundedRangeOn (R := R) S I xs` asserts `I.lo ≤ (xs i).toVal ≤ I.hi`
for every `i ∈ S`.  Indices outside `S` are not constrained.

Special cases:
- `S = Finset.univ`: equivalent to `IsBoundedRange I xs`.
- `S = ∅`: trivially true.
-/
structure IsBoundedRangeOn {n : ℕ} (S : Finset (Fin n))
    (I : FpInterval R) (xs : Fin n → FiniteFp) : Prop where
  /-- Pointwise lower bound on `S`. -/
  lower_on : ∀ i ∈ S, I.lo ≤ ((xs i).toVal : R)
  /-- Pointwise upper bound on `S`. -/
  upper_on : ∀ i ∈ S, ((xs i).toVal : R) ≤ I.hi

/-! ## Basic properties -/

/-- Per-index magnitude bound via `maxMag`.  Analog of
`IsBoundedRange.toVal_abs_le` restricted to `i ∈ S`. -/
theorem IsBoundedRangeOn.toVal_abs_le_of_mem {n : ℕ}
    {S : Finset (Fin n)} {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRangeOn (R := R) S I xs) {i : Fin n} (hi : i ∈ S) :
    |((xs i).toVal : R)| ≤ I.maxMag := by
  rcases le_or_gt 0 ((xs i).toVal : R) with h_nn | h_neg
  · have : |((xs i).toVal : R)| = (xs i).toVal := abs_of_nonneg h_nn
    rw [this, FpInterval.maxMag]
    exact le_trans (le_trans (h.upper_on i hi) (le_abs_self _)) (le_max_right _ _)
  · have : |((xs i).toVal : R)| = -((xs i).toVal : R) := abs_of_neg h_neg
    rw [this, FpInterval.maxMag]
    have h1 : -((xs i).toVal : R) ≤ -I.lo := neg_le_neg (h.lower_on i hi)
    exact le_trans (le_trans h1 (neg_le_abs _)) (le_max_left _ _)

/-- **Generator**: for `i ∈ S`, `IsBoundedRangeOn S I xs` yields
`HasAbsBound I.maxMag (xs i)`.  The partitioned analog of
`IsBoundedRange.toHasAbsBound`. -/
@[tag_generator]
theorem IsBoundedRangeOn.toHasAbsBound_of_mem {n : ℕ}
    {S : Finset (Fin n)} {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRangeOn (R := R) S I xs) {i : Fin n} (hi : i ∈ S) :
    HasAbsBound (R := R) I.maxMag (xs i) :=
  ⟨h.toVal_abs_le_of_mem hi⟩

/-! ## Subsetting algebra -/

/-- Shrinking `S` preserves the tag: if the tag holds on `S` and
`S' ⊆ S`, then the tag holds on `S'`. -/
theorem IsBoundedRangeOn.subset {n : ℕ}
    {S S' : Finset (Fin n)} {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRangeOn (R := R) S I xs) (hSS' : S' ⊆ S) :
    IsBoundedRangeOn (R := R) S' I xs where
  lower_on := fun i hi => h.lower_on i (hSS' hi)
  upper_on := fun i hi => h.upper_on i (hSS' hi)

/-- Two bounds on disjoint sets combine.  Useful when separately
characterizing "small" and "large" regions of the index set. -/
theorem IsBoundedRangeOn.union {n : ℕ}
    {S S' : Finset (Fin n)} {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRangeOn (R := R) S I xs)
    (h' : IsBoundedRangeOn (R := R) S' I xs) :
    IsBoundedRangeOn (R := R) (S ∪ S') I xs where
  lower_on := fun i hi => by
    rcases Finset.mem_union.mp hi with hS | hS'
    · exact h.lower_on i hS
    · exact h'.lower_on i hS'
  upper_on := fun i hi => by
    rcases Finset.mem_union.mp hi with hS | hS'
    · exact h.upper_on i hS
    · exact h'.upper_on i hS'

/-- `IsBoundedRangeOn ∅ I xs` is trivially true. -/
theorem IsBoundedRangeOn.empty {n : ℕ}
    (I : FpInterval R) (xs : Fin n → FiniteFp) :
    IsBoundedRangeOn (R := R) ∅ I xs where
  lower_on := fun _ hi => absurd hi (Finset.not_mem_empty _)
  upper_on := fun _ hi => absurd hi (Finset.not_mem_empty _)

/-! ## Bridges to/from `IsBoundedRange` -/

/-- Any `IsBoundedRange I xs` implies `IsBoundedRangeOn S I xs` for
every subset `S`. -/
theorem IsBoundedRange.toBoundedRangeOn {n : ℕ}
    {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRange (R := R) I xs) (S : Finset (Fin n)) :
    IsBoundedRangeOn (R := R) S I xs where
  lower_on := fun i _ => h.lower i
  upper_on := fun i _ => h.upper i

/-- Conversely, `IsBoundedRangeOn univ I xs` is the full `IsBoundedRange`. -/
theorem IsBoundedRangeOn.toBoundedRange_of_univ {n : ℕ}
    {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRangeOn (R := R) Finset.univ I xs) :
    IsBoundedRange (R := R) I xs where
  lower := fun i => h.lower_on i (Finset.mem_univ i)
  upper := fun i => h.upper_on i (Finset.mem_univ i)

/-! ## Partial-sum magnitude bound

Demonstration of the partitioned-tag payoff: the weighted sum over
`S` is bounded by `|S| · I.maxMag`, even when the complement carries
arbitrary magnitudes.  This is the core structural observation that
enables partitioned downstream bounds. -/

/-- `Σ i ∈ S, |(xs i).toVal| ≤ |S| · I.maxMag`.  The bound depends
only on the tagged subset, not on the whole-vector length. -/
theorem IsBoundedRangeOn.sum_abs_le_on {n : ℕ}
    {S : Finset (Fin n)} {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRangeOn (R := R) S I xs) :
    (∑ i ∈ S, |((xs i).toVal : R)|) ≤ (S.card : R) * I.maxMag := by
  have h_bound : ∀ i ∈ S, |((xs i).toVal : R)| ≤ I.maxMag :=
    fun i hi => h.toVal_abs_le_of_mem hi
  calc (∑ i ∈ S, |((xs i).toVal : R)|)
      ≤ ∑ _i ∈ S, I.maxMag := Finset.sum_le_sum h_bound
    _ = (S.card : R) * I.maxMag := by
          rw [Finset.sum_const]; simp [mul_comm]

/-- Variant stating the bound against the **full domain** sum when
values outside `S` are known bounded by `c` separately. -/
theorem IsBoundedRangeOn.sum_abs_full_le {n : ℕ}
    {S : Finset (Fin n)} {I : FpInterval R} {xs : Fin n → FiniteFp}
    (h : IsBoundedRangeOn (R := R) S I xs) (c : R)
    (h_comp : ∀ i ∉ S, |((xs i).toVal : R)| ≤ c)
    (hc_nn : 0 ≤ c) :
    (∑ i, |((xs i).toVal : R)|) ≤ (S.card : R) * I.maxMag +
      ((Finset.univ \ S).card : R) * c := by
  have h_split :
      (∑ i, |((xs i).toVal : R)|) =
        (∑ i ∈ S, |((xs i).toVal : R)|) +
        (∑ i ∈ Finset.univ \ S, |((xs i).toVal : R)|) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    exact (Finset.union_sdiff_of_subset S.subset_univ).symm
  rw [h_split]
  have h_S := h.sum_abs_le_on
  have h_comp_sum : (∑ i ∈ Finset.univ \ S, |((xs i).toVal : R)|) ≤
      ((Finset.univ \ S).card : R) * c := by
    have h_bound : ∀ i ∈ Finset.univ \ S, |((xs i).toVal : R)| ≤ c :=
      fun i hi => h_comp i (Finset.mem_sdiff.mp hi).2
    calc (∑ i ∈ Finset.univ \ S, |((xs i).toVal : R)|)
        ≤ ∑ _i ∈ Finset.univ \ S, c := Finset.sum_le_sum h_bound
      _ = ((Finset.univ \ S).card : R) * c := by
            rw [Finset.sum_const]; simp [mul_comm]
  linarith

end Flean.Tags

/-! ## Partitioned bundle bridge

`FpSumBound xs` + partitioned magnitude tag gives a bound that
sharpens as `S` grows: the `S`-indices contribute the tight
`|S| · I.maxMag`, the complement contributes via a user-supplied
fallback `c`.  Uses `FpSumBound.h_bound` + triangle. -/

namespace FpSum

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- **Partitioned bundle bridge**: per-index magnitude bounds held only
on `S` (via `IsBoundedRangeOn`), plus a fallback bound on the
complement, give a magnitude bound on the FP sum result.  The `S`-side
contributes `I.maxMag`-weighted terms; the complement-side contributes
`c`-weighted terms.

Strictly more powerful than `hasAbsBound_of_isBoundedRange`: if the
user has a tight bound on `S` and a looser bound on everything (via
`IsBoundedRange`'s `maxMag`), they can supply both and the partitioned
theorem gives the strictly tighter `|S| · I.maxMag + |S^c| · c` form. -/
theorem FpSumBound.hasAbsBound_of_boundedRangeOn {n : ℕ}
    {xs : Fin n → FiniteFp} (b : FpSumBound xs R)
    {S : Finset (Fin n)} {I : FpInterval R}
    (h_on : IsBoundedRangeOn (R := R) S I xs)
    {c : R} (h_comp : ∀ i ∉ S, |((xs i).toVal : R)| ≤ c)
    (hc_nn : 0 ≤ c) :
    |(b.result.toVal : R)| ≤
      (1 + b.relErr) *
        ((S.card : R) * I.maxMag + ((Finset.univ \ S).card : R) * c) := by
  -- Triangle + bundle bound.
  have h_tri : |(b.result.toVal : R)| ≤
      |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| +
        |∑ i, ((xs i).toVal : R)| := by
    have : |((b.result.toVal : R) - ∑ i, ((xs i).toVal : R)) +
             ∑ i, ((xs i).toVal : R)| ≤
           |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| +
             |∑ i, ((xs i).toVal : R)| := abs_add_le _ _
    simpa using this
  have h_sum_abs : |∑ i, ((xs i).toVal : R)| ≤ ∑ i, |((xs i).toVal : R)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_partitioned := h_on.sum_abs_full_le c h_comp hc_nn
  have h_sum_le : |∑ i, ((xs i).toVal : R)| ≤
      (S.card : R) * I.maxMag + ((Finset.univ \ S).card : R) * c :=
    le_trans h_sum_abs h_partitioned
  have h_err := b.h_bound
  have h_relErr_nn := b.h_relErr_nn
  have h_err_bound :
      |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| ≤
        b.relErr * ((S.card : R) * I.maxMag +
          ((Finset.univ \ S).card : R) * c) := by
    have h_sum_bound : ∑ i, |((xs i).toVal : R)| ≤
        (S.card : R) * I.maxMag + ((Finset.univ \ S).card : R) * c :=
      h_partitioned
    have := mul_le_mul_of_nonneg_left h_sum_bound h_relErr_nn
    linarith
  calc |(b.result.toVal : R)|
      ≤ |(b.result.toVal : R) - ∑ i, ((xs i).toVal : R)| +
          |∑ i, ((xs i).toVal : R)| := h_tri
    _ ≤ b.relErr * ((S.card : R) * I.maxMag +
          ((Finset.univ \ S).card : R) * c) +
        ((S.card : R) * I.maxMag +
          ((Finset.univ \ S).card : R) * c) := by linarith
    _ = (1 + b.relErr) * ((S.card : R) * I.maxMag +
          ((Finset.univ \ S).card : R) * c) := by ring

/-- Corollary: when the complement is **empty** (`S = univ`), the
partitioned bound collapses to the standard uniform magnitude bound
over the full-domain `IsBoundedRange`. -/
theorem FpSumBound.hasAbsBound_of_boundedRangeOn_univ {n : ℕ}
    {xs : Fin n → FiniteFp} (b : FpSumBound xs R)
    {I : FpInterval R}
    (h_on : IsBoundedRangeOn (R := R) Finset.univ I xs) :
    |(b.result.toVal : R)| ≤
      (1 + b.relErr) * ((Finset.univ : Finset (Fin n)).card : R) * I.maxMag := by
  have h := b.hasAbsBound_of_boundedRangeOn h_on
    (c := 0) (h_comp := fun i hi => absurd (Finset.mem_univ i) hi)
    (hc_nn := le_refl 0)
  have h_reshape :
      (1 + b.relErr) * ((Finset.univ : Finset (Fin n)).card * I.maxMag +
        (Finset.univ \ Finset.univ : Finset (Fin n)).card * 0) =
      (1 + b.relErr) * ((Finset.univ : Finset (Fin n)).card : R) * I.maxMag := by
    ring
  rw [h_reshape] at h
  exact h
