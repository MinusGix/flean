import Flean.Operations.FpDotProduct

/-!
# Phase 0 Pilot: Constraint-Tagged Values — Simplex

**Status**: Phase 0 pilot per `.claude/notes/tag-framework-plan.md`.

This file contains ONE tag + ONE preservation lemma + ONE tag-specialized
bound, written directly (no `Preserves` typeclass), to validate the
pattern end-to-end before committing to framework infrastructure.

## Assessment (for the reviewer)

**What this pilot tests.** Defining a structural predicate on a vector
`ws : Fin n → FiniteFp` (`IsSimplex R ws`), showing that a mundane FP
operation (permutation) propagates it, and using the tag to re-express
`FpDotProduct.FpDotProductBound`'s RHS in a tag-compatible form.

**Is the specialized bound "strictly tighter" than the general one?**
Not numerically — this is the key finding. `FpDotProductBound`'s RHS is
`relErr · Σ|wᵢ · xᵢ|`. For simplex `ws` we have
`Σ|wᵢ · xᵢ| = Σ wᵢ · |xᵢ| ≤ max |xᵢ|`, so the new bound
`relErr · max|xᵢ|` is an upper bound on the old one — strictly *looser*,
not tighter. The win is *structural*: the new RHS depends only on `xs`
(via `max|xᵢ|`), so downstream reasoning needs only an invariant on `xs`
(e.g. "V is range-bounded by K") to conclude, without having to derive
or carry the joint quantity `Σ|wᵢ · xᵢ|`.

This suggests the plan's "tag-specialized bounds are tighter" framing is
misleading. The real value is **structural isolation** (fewer joint
dependencies in the bound RHS), not raw tightening. Phase 2 language
should be re-scoped accordingly.

**Did the pattern feel natural?** Yes, at this tiny scale. Friction:

* `IsSimplex` carries `R` as a parameter because `toVal` does; if per-
  type tags become common, a typeclass-driven version (`R` inferred)
  would read cleaner.
* Nonempty-domain (`0 < n`) is derivable from the tag itself — the empty
  sum is `0 ≠ 1`, so any `IsSimplex` witness forces `0 < n`. Exposed as
  `IsSimplex.pos` and consumed by the specialized bound so consumers
  don't need a separate hypothesis.
* No `preserves`-style typeclass yet, so the permutation lemma is a
  plain theorem. It reads fine at this scale; the typeclass overhead
  would only earn its keep once we chain multiple tagged ops.

**Recommendation on Phase 1.** Proceed — BUT re-word the "tightness"
framing throughout the plan (it misdescribes what tags buy). Before
building the `Preserves` class, answer: can we pilot 2–3 more
tag-specialized bounds on different ops without the class, and see if
the *pattern* generalizes first? The class is load-bearing only once
composition matters (Phase 2+); the scalar-tag work may proceed with
plain theorems.

**Open design questions surfaced here.**

1. Carrying `R` in the tag vs. making it a typeclass — see above.
2. Nonempty / nondegeneracy preconditions — should they live on the tag
   (so `IsSimplex` of an empty vector is False-by-convention) or on the
   consuming theorem? Current file takes the latter.
3. Should `IsSimplex` include the positivity of each entry individually
   (as here) or just `Σ wᵢ = 1` plus `Σ |wᵢ| ≤ 1` (a weaker form that
   admits signed-but-normalized vectors)? For the dot-product bound, we
   genuinely need `wᵢ ≥ 0` pointwise to pull `|wᵢxᵢ| = wᵢ|xᵢ|`.
-/

set_option autoImplicit false

namespace Flean.Tags

open Finset BigOperators FpDotProduct

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag -/

/-- `IsSimplex R ws` asserts that `ws : Fin n → FiniteFp` lies on the
probability simplex over `R`: each entry is non-negative and the entries
sum to one. -/
structure IsSimplex {n : ℕ} (ws : Fin n → FiniteFp) : Prop where
  /-- Each entry's real value is non-negative. -/
  nonneg : ∀ i, (0 : R) ≤ (ws i).toVal
  /-- The real values sum to one. -/
  sum_one : ∑ i, ((ws i).toVal : R) = 1

/-! ## Derived facts -/

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Any simplex vector is non-empty: `∑ (empty) = 0 ≠ 1`. This lets
consumer theorems drop an explicit `0 < n` hypothesis. -/
theorem IsSimplex.pos {n : ℕ} {ws : Fin n → FiniteFp}
    (h : IsSimplex (R := R) ws) : 0 < n := by
  by_contra hle
  push_neg at hle
  interval_cases n
  have : ∑ i : Fin 0, ((ws i).toVal : R) = 0 := by simp
  have h_one : (0 : R) = 1 := this ▸ h.sum_one
  exact zero_ne_one h_one

/-! ## Preservation: permutation -/

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Reindexing a simplex vector by a permutation yields another simplex
vector. This is the pilot's single preservation lemma — a plain theorem,
no typeclass. -/
theorem IsSimplex.reindex {n : ℕ} {ws : Fin n → FiniteFp}
    (h : IsSimplex (R := R) ws) (e : Fin n ≃ Fin n) :
    IsSimplex (R := R) (ws ∘ e) where
  nonneg i := h.nonneg (e i)
  sum_one := by
    have hsum : ∑ i, (((ws ∘ e) i).toVal : R) = ∑ i, ((ws i).toVal : R) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [hsum]
    exact h.sum_one

/-! ## Tag-specialized dot-product bound

The arithmetic heart: for simplex `ws`, `Σ|wᵢ · xᵢ| ≤ max |xᵢ|`. Combined
with `FpDotProductBound.h_bound` this re-expresses the error bound in
terms of `max|xᵢ|` only. -/

omit [FloorRing R] in
/-- For simplex `ws` and arbitrary `xs`, the sum of absolute products is
bounded by the max absolute value of `xs`. Pure real-analysis statement;
no FP rounding involved. The nonempty witness is derived from `hws`. -/
private lemma sum_abs_mul_le_max {n : ℕ}
    {ws xs : Fin n → FiniteFp} (hws : IsSimplex (R := R) ws) :
    ∑ i, |((ws i).toVal : R) * ((xs i).toVal : R)| ≤
      (Finset.univ : Finset (Fin n)).sup'
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hws.pos))
        (fun i => |((xs i).toVal : R)|) := by
  have h_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hws.pos)
  set M : R := (Finset.univ : Finset (Fin n)).sup' h_ne
                 (fun i => |((xs i).toVal : R)|) with hM_def
  -- Step 1: |wᵢxᵢ| = wᵢ·|xᵢ| using wᵢ ≥ 0.
  have habs_eq : ∀ i,
      |((ws i).toVal : R) * ((xs i).toVal : R)|
        = ((ws i).toVal : R) * |((xs i).toVal : R)| := by
    intro i
    rw [abs_mul, abs_of_nonneg (hws.nonneg i)]
  have hsum_eq : ∑ i, |((ws i).toVal : R) * ((xs i).toVal : R)|
               = ∑ i, ((ws i).toVal : R) * |((xs i).toVal : R)| :=
    Finset.sum_congr rfl (fun i _ => habs_eq i)
  rw [hsum_eq]
  -- Step 2: Σ wᵢ · |xᵢ| ≤ Σ wᵢ · M.
  have h_step : ∑ i, ((ws i).toVal : R) * |((xs i).toVal : R)|
              ≤ ∑ i, ((ws i).toVal : R) * M := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hle : |((xs i).toVal : R)| ≤ M :=
      Finset.le_sup' (fun j => |((xs j).toVal : R)|) (Finset.mem_univ i)
    exact mul_le_mul_of_nonneg_left hle (hws.nonneg i)
  -- Step 3: Σ wᵢ · M = M (using sum_one).
  have h_collapse : ∑ i, ((ws i).toVal : R) * M = M := by
    rw [← Finset.sum_mul, hws.sum_one, one_mul]
  linarith

/-- **Tag-specialized dot-product error bound (simplex case).**

Given a floating-point dot product bound `b : FpDotProductBound ws xs R`
and a certificate `IsSimplex R ws`, the FP error is bounded by
`b.relErr · max|xᵢ|`. This re-expresses the general bound's
`relErr · Σ|wᵢ·xᵢ|` in terms that depend only on `xs`.

Note: strictly LOOSER than `FpDotProductBound.h_bound` on absolute
magnitude — the structural value is eliminating `ws` from the RHS, not
shrinking it. The nonempty witness for `max` is derived from `IsSimplex.pos`. -/
theorem FpDotProductBound.simplex_bound {n : ℕ}
    {ws xs : Fin n → FiniteFp} (hws : IsSimplex (R := R) ws)
    (b : FpDotProductBound ws xs R) :
    |(b.result.toVal : R) - ∑ i, ((ws i).toVal : R) * ((xs i).toVal : R)| ≤
      b.relErr * (Finset.univ : Finset (Fin n)).sup'
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hws.pos))
        (fun i => |((xs i).toVal : R)|) := by
  have h_bound := b.h_bound
  have h_le := sum_abs_mul_le_max (R := R) (xs := xs) hws
  calc |(b.result.toVal : R) - ∑ i, ((ws i).toVal : R) * ((xs i).toVal : R)|
      ≤ b.relErr * ∑ i, |((ws i).toVal : R) * ((xs i).toVal : R)| := h_bound
    _ ≤ b.relErr * (Finset.univ : Finset (Fin n)).sup'
          (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hws.pos))
          (fun i => |((xs i).toVal : R)|) :=
        mul_le_mul_of_nonneg_left h_le b.h_relErr_nn

end Flean.Tags
