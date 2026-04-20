import Flean.ToVal

/-!
# Tag: `IsBoundedRange`

R-parametric tag asserting each entry of a vector `xs : Fin n → FiniteFp`
lies in a closed interval `[lo, hi]` measured in `R`.

This file holds only the tag definition + basic struct-API properties.
Bridges *from* `IsBoundedRange` to pre-existing-theorem hypotheses
(e.g. `isNormalRange (Real.exp ·)`) live in `Flean/Tags/Bridges/`,
organized by target hypothesis per design doc §1.3 / §3.3.

Parametric propagation lemmas (`IsBoundedRange.fpAdd` etc.) are locked
in the design doc as signatures and will land in a sibling file when
the focused FP-error-analysis session proves them (design doc §1.4).
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## The tag -/

/-- `IsBoundedRange (R := R) lo hi xs` asserts each entry of
`xs : Fin n → FiniteFp` satisfies `lo ≤ (xs i).toVal ≤ hi`, measured
in `R`. Closed interval.

Per design doc §1.8, all tags parameterize over `R`; bridges into
ℝ-specific hypotheses (like `isNormalRange (Real.exp ·)`) specialize
the tag to `R := ℝ` at the call site. -/
structure IsBoundedRange {n : ℕ} (lo hi : R) (xs : Fin n → FiniteFp) : Prop where
  /-- Pointwise lower bound. -/
  lower : ∀ i, lo ≤ ((xs i).toVal : R)
  /-- Pointwise upper bound. -/
  upper : ∀ i, ((xs i).toVal : R) ≤ hi

end Flean.Tags
