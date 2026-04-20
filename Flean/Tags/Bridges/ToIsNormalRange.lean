import Flean.Tags.BoundedRange
import Flean.Util
import Flean.Rounding.Rounding

/-!
# Bridges to `isNormalRange`

Theorems that discharge an `isNormalRange (...)` hypothesis given a
tag on some input value. Organized by **target hypothesis** per
design doc §1.3:

> A user hitting `h_exp_nr : isNormalRange (...)` on a call site wants
> to ask "which tags can give me this?" Indexing by target makes that
> question answerable via file navigation. Indexing by source forces
> the user to pre-guess the answer.

## Current contents

- `IsBoundedRange.exp_isNormalRange` — if `xs` is in `[lo, hi]` with
  `lo ≥ min_exp · log 2` and `hi < (max_exp + 1) · log 2`, then
  `isNormalRange (Real.exp ((xs i).toVal : ℝ))` for all `i`.

## Future additions (locked signatures in design doc §3.3)

- `IsBoundedRange.quot_isNormalRange` — bounded `xs` + softmax-denom
  hypotheses + separation condition → `isNormalRange (exps_i / denom)`.
  Proof deferred to a focused FP-error-analysis session; library
  remains sorry-free.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]

/-- **Bridge theorem**: if `xs` lies in `[lo, hi]` (measured in ℝ) with
`lo ≥ min_exp · log 2` and `hi < (max_exp+1) · log 2`, then
`Real.exp ((xs i).toVal)` is in the normal range for all `i`.

Discharges the `h_exp_nr` precondition of `fpSoftmaxOf_error_bound`
from an input `IsBoundedRange` tag automatically. -/
theorem IsBoundedRange.exp_isNormalRange
    {n : ℕ} {lo hi : ℝ} {xs : Fin n → FiniteFp}
    (h : IsBoundedRange (R := ℝ) lo hi xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ lo)
    (hhi : hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (i : Fin n) : isNormalRange (Real.exp ((xs i).toVal : ℝ)) := by
  refine ⟨?_, ?_⟩
  · have hy_ge : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ ((xs i).toVal : ℝ) :=
      le_trans hlo (h.lower i)
    have hexp_step : Real.exp ((FloatFormat.min_exp : ℝ) * Real.log 2) ≤
                     Real.exp ((xs i).toVal : ℝ) :=
      Real.exp_le_exp_of_le hy_ge
    rwa [exp_int_mul_log2] at hexp_step
  · have hy_lt : ((xs i).toVal : ℝ) <
                 ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2 :=
      lt_of_le_of_lt (h.upper i) hhi
    have hexp_step : Real.exp ((xs i).toVal : ℝ) <
                     Real.exp (((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2) :=
      Real.exp_strictMono hy_lt
    rwa [exp_int_mul_log2] at hexp_step

end Flean.Tags
