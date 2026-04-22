import Flean.Tags.Attributes
import Flean.Tags.AbsBound
import Flean.Tags.AbsBoundPropagate
import Flean.Tags.BoundedRange
import Flean.Tags.Nonneg
import Flean.Tags.Simplex
import Flean.Tags.Sterbenz
import Flean.Tags.OneHot

/-!
# Tag Generators + Forward-Compatible Attributes

The **tag-generator pattern**: strong tags yield weaker tags via
canonically-named `.toX` lemmas.  Makes implicit relationships
explicit and seeds the tag-lattice registry that a future tag
inference engine would consume.

## Attributes

Three label attributes, registered as environment extensions:

* `@[tag_generator]` — marks a `toStrong → toWeak` lemma.
* `@[tag_propagate]` — marks a propagation through FP ops.
* `@[tag_bridge]`   — marks a bridge to a pre-existing hypothesis.

These are **inert** today (no tactic consumes them) but zero-cost to
add, and populate the registry for when a tag-inference engine is
built (post-15-tag threshold, per the backlog).

## Generator lemmas

Each generator captures an implication "tag X implies tag Y" where Y
is weaker / more general.

| Source | Target | Content |
|---|---|---|
| `IsOneHot j y` | `∀ i, IsNonneg (y i)` | all entries are 0 or 1 |
| `IsOneHot j y` | `∀ i, HasAbsBound 1 (y i)` | magnitude bound |
| `IsSimplex ws` | `∀ i, IsNonneg (ws i)` | simplex entries are nonneg |
| `IsSterbenz a b` | `HasAbsBound (2 · toVal_mag b) a` | ratio bound |
| `IsBoundedRange I xs` | `∀ i, HasAbsBound I.maxMag (xs i)` | pointwise magnitude |

These are **derivable** in one line each — their value is the naming
convention and the attribute mark.
-/

/-! ## Generator lemmas -/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Generator**: `IsOneHot j y` → each entry is non-negative.

The hot entry is `1 ≥ 0`; every cold entry is `0 ≥ 0`.  Follows
directly from `IsOneHot.toVal_nonneg`. -/
@[tag_generator]
theorem IsOneHot.toIsNonneg {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) (i : Fin n) :
    IsNonneg (R := R) (y i) :=
  ⟨h.toVal_nonneg i⟩

/-- **Generator**: `IsOneHot j y` → each entry has magnitude ≤ 1.

The hot entry has `|y_j.toVal| = 1`; every cold entry has
`|y_i.toVal| = 0 ≤ 1`.  `HasAbsBound 1 (y i)` directly. -/
@[tag_generator]
theorem IsOneHot.toHasAbsBound_one {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) (i : Fin n) :
    HasAbsBound (R := R) 1 (y i) := by
  refine ⟨?_⟩
  rcases eq_or_ne i j with hij | hij
  · rw [hij, h.hot]; simp
  · rw [h.cold i hij]; simp

end Flean.Tags

/-! ## Marking existing generators

`IsBoundedRange.toHasAbsBound` (in `AbsBoundPropagate.lean`) is a
generator — mark it now that the attribute is registered. -/

attribute [tag_generator] Flean.Tags.IsBoundedRange.toHasAbsBound
