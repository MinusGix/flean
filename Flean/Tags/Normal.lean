import Flean.Ulp
import Flean.Rounding.Rounding

/-!
# Phase 0 Pilot: Constraint-Tagged Values — IsNormal

**Status**: Phase 0 companion to `Flean/Tags/Simplex.lean`. This pilot
tests the pattern for a case where the tag-specialized bound is
**strictly numerically tighter** than the general bound in the codebase.

## What this pilot tightens

The general subnormal-tolerant unified ulp bound (in `Flean/Operations/Softmax.lean`
line 569, for `v : ℝ` with `0 < v`) is

  `Fp.ulp v / 2 ≤ η · v + subnormalConst`

where `subnormalConst = 2^(min_exp - prec) > 0` absorbs the subnormal
range's additive error. This "unified" shape lets bounds hold regardless
of whether `v` falls in the subnormal or normal range.

When `v` is in the normal range (`2^min_exp ≤ v`), the subnormal tail is
spurious: `Fp.ulp v / 2 ≤ η · v` alone suffices. This file provides the
`IsNormal`-tagged version, `ulp_half_le_of_normal`, which drops the tail.

This is a **strict** tightening because `subnormalConst > 0`: the tagged
bound is smaller by exactly `subnormalConst`. Downstream consumers who
carry an `IsNormal` certificate get a sharper bound with the same proof
obligation budget.

## Design choices vs. IsSimplex

- `IsSimplex` is a `structure` because it bundles two conditions
  (non-negativity + sum-to-one). `IsNormal` bundles two as well
  (positivity + lower-bound), but conceptually just one ("in normal
  range"). Using a structure anyway for uniformity with the pattern.
- Deliberately *weaker* than the codebase's `isNormalRange`: we drop the
  overflow upper bound (`v < 2^(max_exp+1)`), since the ulp half bound
  doesn't need it. The bridge `IsNormal.of_isNormalRange` lets callers
  with a full `isNormalRange` certificate lift in.
- Preservation lemma is `IsNormal.add_nonneg`: adding a non-negative
  value preserves the normal-range lower bound without any overflow
  check (the `pos` and `ge_min` fields both propagate monotonically).
-/

set_option autoImplicit false

namespace Flean.Tags

open Fp

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag -/

/-- `IsNormal v` asserts that the real value `v` is positive and lies at
or above the normal-range lower bound `2^min_exp`. Weaker than
`isNormalRange v` because it omits the overflow upper bound — the ulp
tightening only needs the lower bound. -/
structure IsNormal (v : R) : Prop where
  /-- `v` is positive. -/
  pos : 0 < v
  /-- `v` is at least the smallest normal magnitude. -/
  ge_min : (2 : R) ^ FloatFormat.min_exp ≤ v

/-! ## Derived facts and bridge lemmas -/

omit [FloorRing R] in
/-- Any `isNormalRange` witness yields an `IsNormal` certificate. -/
theorem IsNormal.of_isNormalRange {v : R} (h : isNormalRange v) : IsNormal v where
  pos := isNormalRange_pos v h
  ge_min := h.1

/-! ## Preservation: addition of a non-negative increment -/

omit [FloorRing R] in
/-- Adding a non-negative real to an `IsNormal` value yields another
`IsNormal` value. Monotone in both fields. No overflow check needed. -/
theorem IsNormal.add_nonneg {v y : R} (hv : IsNormal v) (hy : 0 ≤ y) :
    IsNormal (v + y) where
  pos := by linarith [hv.pos]
  ge_min := by linarith [hv.ge_min]

/-! ## Tag-specialized ulp bound (strictly tighter) -/

/-- **Tag-specialized ulp bound (normal case).**

Given `IsNormal v`, the standard "half-ulp" rounding bound sharpens to
`Fp.ulp v / 2 ≤ η · v` — no additive subnormal tail.

Compare to `Softmax.ulp_half_le_unified` (which requires only `0 < v`),
giving the looser `η · v + subnormalConst`. Since `subnormalConst > 0`,
this tag-specialized version is **strictly numerically tighter** on the
same inputs. -/
theorem ulp_half_le_of_normal (v : R) (hv : IsNormal v) :
    Fp.ulp v / 2 ≤ (η : R) * v := by
  have hv_pos : 0 < v := hv.pos
  have hv_abs_ge : (2 : R) ^ FloatFormat.min_exp ≤ |v| := by
    rw [abs_of_pos hv_pos]; exact hv.ge_min
  -- From `ulp_div_abs_le`: ulp v / |v| ≤ ε = 2^(1 - prec).
  have h_div := Fp.ulp_div_abs_le v hv_abs_ge
  rw [abs_of_pos hv_pos, div_le_iff₀ hv_pos] at h_div
  -- h_div : Fp.ulp v ≤ ε · v
  -- Rewrite ε = 2·η so ulp/2 ≤ η·v.
  have hε_eq : (ε : R) = 2 * (η : R) := by
    simp only [FloatFormat.eps_def, FloatFormat.hEps_def]
    rw [show (1 - (FloatFormat.prec : ℤ)) = 1 + (-(FloatFormat.prec : ℤ)) from by ring,
        zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
    norm_num
  rw [hε_eq] at h_div
  linarith

/-! ## Sanity demo: strict tightening -/

/-- Demonstrates that the tagged bound is strictly tighter than the
general one would have been (subnormalConst is positive). Expressed
without importing Softmax by inlining the extra tail as a positive
parameter `sc > 0`. -/
example (v : R) (hv : IsNormal v) (sc : R) (hsc : 0 < sc) :
    -- Tag-specialized bound holds:
    Fp.ulp v / 2 ≤ (η : R) * v
    -- And is strictly smaller than the general "+ positive tail" version:
    ∧ (η : R) * v < (η : R) * v + sc := by
  refine ⟨ulp_half_le_of_normal v hv, ?_⟩
  linarith

end Flean.Tags
