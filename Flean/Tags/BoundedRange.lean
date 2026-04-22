import Flean.ToVal
import Flean.Tags.FpInterval

/-!
# Tag: `IsBoundedRange`

R-parametric tag asserting each entry of a vector `xs : Fin n → FiniteFp`
lies in the closed interval `I : FpInterval R`, measured in `R`.

This file holds only the tag definition + basic struct-API properties.
The interval-arithmetic machinery backing propagation lemmas lives in
`Flean/Tags/FpInterval.lean`; the propagation theorems themselves are
in `Flean/Tags/BoundedRangePropagate.lean`.  Bridges *from*
`IsBoundedRange` to pre-existing-theorem hypotheses (e.g.
`isNormalRange (Real.exp ·)`) live in `Flean/Tags/Bridges/`, organized
by target hypothesis per design doc §1.3 / §3.3.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## The tag -/

/-- `IsBoundedRange (R := R) I xs` asserts each entry of
`xs : Fin n → FiniteFp` satisfies `I.lo ≤ (xs i).toVal ≤ I.hi`, measured
in `R`.  Closed interval.

Per design doc §1.8, all tags parameterize over `R`; bridges into
ℝ-specific hypotheses (like `isNormalRange (Real.exp ·)`) specialize
the tag to `R := ℝ` at the call site. -/
structure IsBoundedRange {n : ℕ} (I : FpInterval R) (xs : Fin n → FiniteFp) : Prop where
  /-- Pointwise lower bound. -/
  lower : ∀ i, I.lo ≤ ((xs i).toVal : R)
  /-- Pointwise upper bound. -/
  upper : ∀ i, ((xs i).toVal : R) ≤ I.hi

/-! ## Basic properties -/

/-- When the vector is nonempty, the interval is nontrivial: `I.lo ≤ I.hi`.
Derivable from any witness.  Useful for discharging `lo ≤ hi` side
conditions that sometimes arise in interval-arithmetic reasoning. -/
theorem IsBoundedRange.lo_le_hi {n : ℕ} (hn : 0 < n) {I : FpInterval R}
    {xs : Fin n → FiniteFp} (h : IsBoundedRange (R := R) I xs) :
    I.lo ≤ I.hi := by
  have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  exact le_trans (h.lower ⟨0, hn⟩) (h.upper ⟨0, hn⟩)

/-- Every tagged entry's magnitude is bounded by `maxMag I`.  The
single general magnitude corollary — per-op magnitude bounds fall out
by instantiating this on the output interval of the propagation
lemma. -/
theorem IsBoundedRange.toVal_abs_le {n : ℕ} {I : FpInterval R}
    {xs : Fin n → FiniteFp} (h : IsBoundedRange (R := R) I xs) (i : Fin n) :
    |((xs i).toVal : R)| ≤ I.maxMag := by
  rcases le_or_gt 0 ((xs i).toVal : R) with hi_nn | hi_neg
  · have : |((xs i).toVal : R)| = (xs i).toVal := abs_of_nonneg hi_nn
    rw [this, FpInterval.maxMag]
    exact le_trans (le_trans (h.upper i) (le_abs_self _)) (le_max_right _ _)
  · have : |((xs i).toVal : R)| = -((xs i).toVal : R) := abs_of_neg hi_neg
    rw [this, FpInterval.maxMag]
    have : -((xs i).toVal : R) ≤ -I.lo := neg_le_neg (h.lower i)
    exact le_trans (le_trans this (neg_le_abs _)) (le_max_left _ _)

end Flean.Tags
