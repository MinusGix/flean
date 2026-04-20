import Flean.Operations.Sterbenz

/-!
# Phase 0 Pilot: Constraint-Tagged Values — Sterbenz

**Status**: Phase 0 companion to `Flean/Tags/Simplex.lean` and
`Flean/Tags/Normal.lean`. Third pilot, testing a third tag flavor:
**tags that unlock exactness** (error collapses to 0).

## What this pilot tightens

The general `fpSubFinite_correct` (in `Flean/Operations/Sub.lean`) gives

  `fpSubFinite a b = ○(a.toVal - b.toVal)`

— the FP subtraction of two finite floats equals the rounding of the
true real difference. In general this rounding can introduce up to
`η · |a - b|` relative error (plus a subnormal tail in the subnormal
regime).

When `a` and `b` satisfy the Sterbenz preconditions (same sign,
magnitudes within a factor of 2), the classical Sterbenz lemma gives
`fpSubFinite a b = Fp.finite f` with `f.toVal = a.toVal - b.toVal` **exactly**
— no rounding. This is strictly tighter: error = 0 vs the general η-bound.

`sterbenz_same_sign` in `Flean/Operations/Sterbenz.lean` already proves
this; the pilot repackages it as a tag-specialized theorem that consumers
can reach via `fpSubFinite_exact_of_sterbenz`.

## Why this is a meaningfully different pilot flavor

- `IsSimplex` delivered *structural isolation* (same-magnitude bound,
  different RHS shape).
- `IsNormal` delivered *additive-tail elimination* (drop `+ subnormalConst`).
- `IsSterbenz` delivers *multiplicative-tail elimination* — the whole
  `relErr · |...|` term drops to 0. This is the strongest kind of
  tightening: "error = 0 when tag holds."

The three pilots together span the taxonomy of tag-specialized bound
shapes: pure-structural (bound RHS shape change), additive (drop a
`+ c` term), multiplicative (drop a `· ε` factor).

## Design notes

- Tag is a 5-field structure matching `sterbenz_same_sign`'s hypotheses
  verbatim. Could factor further (e.g. bundle `|b|/2 ≤ |a|` and `|a| ≤ 2|b|`
  as a single "close_in_magnitude" fact), but five named fields beat
  opaque conjunctions for documentation.
- Preservation chosen: **negation of both operands**. Negation is a
  real FP op (exact — just sign-bit flip), magnitudes are preserved,
  so all five fields propagate transparently. More meaningful than
  "swap" (which is just tag symmetry, not an operation).
- The tag carries `R` because `toVal_mag` does. Same friction as
  `IsSimplex`.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag -/

/-- `IsSterbenz R a b` asserts the preconditions of the generalized
Sterbenz lemma: `a` and `b` are same-sign finite floats with non-zero
significands and magnitudes within a factor of 2 of each other. These
conditions are exactly what `sterbenz_same_sign` requires to conclude
that `a - b` is exactly representable. -/
structure IsSterbenz (a b : FiniteFp) : Prop where
  /-- `a` and `b` have the same sign bit. -/
  same_sign : a.s = b.s
  /-- `a` has non-zero significand. -/
  a_nz : 0 < a.m
  /-- `b` has non-zero significand. -/
  b_nz : 0 < b.m
  /-- Lower Sterbenz bound: `|b| / 2 ≤ |a|`. -/
  lb : FiniteFp.toVal_mag b (R := R) / 2 ≤ FiniteFp.toVal_mag a
  /-- Upper Sterbenz bound: `|a| ≤ 2 · |b|`. -/
  ub : FiniteFp.toVal_mag a (R := R) ≤ 2 * FiniteFp.toVal_mag b

/-! ## Magnitude helper -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- Magnitude is invariant under negation, since `(-x).m = x.m` and
`(-x).e = x.e`. Only the sign bit flips. -/
private lemma toVal_mag_neg_eq (x : FiniteFp) :
    FiniteFp.toVal_mag (-x) = FiniteFp.toVal_mag (R := R) x := by
  unfold FiniteFp.toVal_mag
  simp

/-! ## Preservation: negation of both operands -/

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Negating both operands preserves `IsSterbenz`. Negation is an exact
FP operation (`.s` flips, `.e`/`.m` preserved), so all five fields
propagate: sign-equality is preserved by flipping both, the significand
bounds are untouched, and magnitudes are invariant. -/
theorem IsSterbenz.neg {a b : FiniteFp} (h : IsSterbenz (R := R) a b) :
    IsSterbenz (R := R) (-a) (-b) where
  same_sign := by simp [h.same_sign]
  a_nz := by simpa using h.a_nz
  b_nz := by simpa using h.b_nz
  lb := by rw [toVal_mag_neg_eq, toVal_mag_neg_eq]; exact h.lb
  ub := by rw [toVal_mag_neg_eq, toVal_mag_neg_eq]; exact h.ub

/-! ## Tag-specialized bound: exact subtraction -/

/-- **Tag-specialized bound: subtraction is exact.**

Given `IsSterbenz R a b`, the FP subtraction `fpSubFinite a b` yields a
finite result whose `toVal` equals the real difference `a.toVal - b.toVal`
*exactly* — no rounding error, no subnormal tail.

This is strictly tighter than the general `fpSubFinite_correct`, which
delivers only `fpSubFinite a b = ○(a.toVal - b.toVal)` (an arbitrary
rounding of the difference).

Thin wrapper around `sterbenz_same_sign`, exposing the result in a form
that speaks tag vocabulary. -/
theorem fpSubFinite_exact_of_sterbenz
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]
    {a b : FiniteFp} (h : IsSterbenz (R := R) a b) :
    ∃ f : FiniteFp,
      fpSubFinite a b = Fp.finite f ∧
      (f.toVal : R) = a.toVal - b.toVal := by
  obtain ⟨f, hf_eq, hf_rep⟩ :=
    sterbenz_same_sign (R := R) a b h.same_sign h.a_nz h.b_nz h.lb h.ub
  refine ⟨f, ?_, hf_rep⟩
  simpa [sub_finite_eq_fpSubFinite] using hf_eq

/-! ## Sanity demo: strict tightening vs general bound -/

/-- Absolute error of the tagged bound is 0, whereas the general
`fpSubFinite_correct` only guarantees rounding-bounded error. -/
example [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]
    {a b : FiniteFp} (h : IsSterbenz (R := R) a b) :
    ∃ f : FiniteFp,
      fpSubFinite a b = Fp.finite f ∧
      |(f.toVal : R) - (a.toVal - b.toVal)| = 0 := by
  obtain ⟨f, hsub, hval⟩ := fpSubFinite_exact_of_sterbenz (R := R) h
  exact ⟨f, hsub, by rw [hval]; simp⟩

end Flean.Tags
