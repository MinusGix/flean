import Flean.Operations.ExactIntSignMag
import Flean.Tags.Nonneg
import Flean.Tags.AbsBound

/-! # Bridges: the exact-integer domains *refine* the Tags domains (one abstract-interpretation spine)

Flean contains two abstract-domain systems built independently:

* the **Tags** framework — `IsNonneg`, `HasAbsBound`, `IsBoundedRange`, … — abstract interpretation
  on the *real value* of a float (`FiniteFp.toVal`), the metric face used by the big error analyses
  (softmax, the MLP layer);
* the **exact-integer reduction** stack — `HasSign`, `HasSignMag`, `IsResidue`, … — abstract
  interpretation on the *integer shadow* `ExactInt.n`, the structural face.

They are the *same idea* (shadow + concretization γ + sound transformers) instantiated in two
places. This file makes the connection load-bearing: the exact-integer domains **refine** the Tags
domains, and projecting an exact-int fact (forgetting the integer shadow, keeping only what it says
about the real value) lands exactly in a Tags fact. The γ-collapse `ExactInt.n → FiniteFp.toVal`:

| exact-int (structural, on `a.n : ℤ`) | Tags (metric, on `a.fp.toVal : R`) |
|---|---|
| `HasSign s` (3-valued sign) | `IsNonneg` (its nonneg cone, when `0 ≤ s`) |
| `HasSignMag s lo hi` (sign × interval `[lo,hi]`) | `HasAbsBound hi` (its magnitude face) |

The exact-int side carries strictly more (the exact integer, hence a *discrete* invariant); the
Tags side is the metric residue. So the two systems are one lattice over `FiniteFp`, with the
exact-int domains sitting above the Tags domains under this refinement.
-/

namespace ExactInt

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open SignType Flean.Tags

/-- **`HasSign` ↦ `IsNonneg`.** A nonnegative sign (`0 ≤ s`, i.e. `s ∈ {0, +1}`) projects to the
Tags positivity tag on the underlying float. The discrete sign refines the metric nonnegativity. -/
theorem HasSign.isNonneg {s : SignType} {a : ExactInt R} (h : HasSign s a) (hs : 0 ≤ s) :
    IsNonneg (R := R) a.fp := by
  refine ⟨?_⟩
  rw [a.agree]
  have hn : (0 : ℤ) ≤ a.n := sign_nonneg_iff.mp (by rw [h]; exact hs)
  exact_mod_cast hn

/-- **`HasSignMag` ↦ `HasAbsBound`.** The magnitude interval's upper bound `hi` projects to the
Tags magnitude tag on the underlying float. The discrete interval refines the metric bound. -/
theorem HasSignMag.hasAbsBound {s : SignType} {lo hi : ℤ} {a : ExactInt R}
    (h : HasSignMag s lo hi a) : HasAbsBound (R := R) (hi : R) a.fp := by
  refine ⟨?_⟩
  rw [a.agree]
  exact_mod_cast h.le_hi

/-- **`HasSignMag` ↦ `IsNonneg`** (via the sign factor). A positive-sign magnitude-bounded value is
both nonneg and abs-bounded — its real value lands in the Tags interval `[0, hi]` (the scalar
shadow of `IsBoundedRange`). -/
theorem HasSignMag.isNonneg {s : SignType} {lo hi : ℤ} {a : ExactInt R}
    (h : HasSignMag s lo hi a) (hs : 0 ≤ s) : IsNonneg (R := R) a.fp :=
  h.toSign.isNonneg hs

end ExactInt
