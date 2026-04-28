import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Operations.FpFiniteRound
import Flean.Rounding.ModeClass
import Flean.Rounding.RoundPreserves
import Flean.Tags.Attributes

/-!
# Phase 0 Pilot: Constraint-Tagged Values — IsNonneg (Composition)

**Status**: Phase 0 composition test. Fourth pilot. Explicitly tests
that a tag propagates across **two different operations** in sequence —
not just through one op applied repeatedly.

## What this pilot tests

Previous pilots (`Simplex`, `Normal`, `Sterbenz`) each tagged ONE
operation, leaving composition unvalidated. This file tags two:
`fpMulFinite` and `fpAddFinite`. The end-to-end demo theorem
`fpMulAdd_isNonneg` chains them: `(x · y) + bias` stays `IsNonneg` when
all three inputs are.

The preservation lemmas thread `IsNonneg` from inputs to output
conditional on the op's result being finite. Downstream consumers who
track finiteness separately (via `FpSumBound.ofNaive`-style builders or
direct witnesses) get the tag-propagation "for free" once they hand
over finiteness witnesses.

## What composition tells us

With three single-op pilots and one two-op composition pilot in hand,
the pattern's open questions on composition are:

* **Preservation lemmas are boilerplate** — each is "result of round is
  nonneg if input was nonneg," varying only by which `fp*Finite` def
  you unfold. A typeclass (`IsNonneg.preserves`) + one meta-lemma could
  auto-discharge these from the correctness + monotonicity laws the
  operation already provides.
* **Finiteness is an orthogonal concern**. The tag says "if the result
  exists, it's non-negative." Finiteness witnesses come from a
  different chain (range bounds, `FpSumBound`-style abstraction).
  Framework design shouldn't bundle the two.
* **Zero-sum / zero-product cases need structural handling**, because
  `fp*Finite_correct` only applies to non-zero results. This pilot
  handles them via the existing `fpAddFinite_zero_left_val` helper
  (for fpAdd) and inline unfolding (for fpMul). A tag framework should
  factor this out as a reusable `round_preserves_nonneg` lemma.

## Retrofit (Phase 1 §3.2 step)

The zero-case friction flagged in the original pilot header has since
been absorbed by `Flean/Operations/FpFiniteRound.lean`'s unified
witnesses (`fpAddFinite_round_witness`, `fpMulFinite_round_witness`).
The preservation proofs below dropped from ~15 lines each to ~5,
validating the §1.6 design decision: one uniform rounding-witness per
op, consumed identically by every tag preservation.

The kernel lemma `round_preserves_nonneg` (previously `round_preserves_nonneg`
and private here) has been promoted to `Flean/Rounding/RoundPreserves.lean`
per Phase 1 §3.1. This file now imports + uses it.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag -/

/-- `IsNonneg R x` asserts that the real value of `x : FiniteFp`
(evaluated in `R`) is non-negative. -/
structure IsNonneg (x : FiniteFp) : Prop where
  /-- `0 ≤ x.toVal`. -/
  toVal_nonneg : (0 : R) ≤ x.toVal

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- The canonical zero float satisfies `IsNonneg`. -/
theorem IsNonneg.zero : IsNonneg (R := R) (0 : FiniteFp) :=
  ⟨by rw [FiniteFp.toVal_zero]⟩

/-! ## Preservation: `fpAddFinite`

After the §1.6 unified-round-witness helper (`fpAddFinite_round_witness`)
landed in `Flean/Operations/FpFiniteRound.lean`, these preservations no
longer need to case-split on zero vs nonzero sum / product — the helper
absorbs both cases via an existential witness `g` whose `toVal` matches
the result's.

See `.claude/notes/tag-framework-phase1-design.md` §3.2 for the retrofit
measurement: ~15 line proof bodies drop to ~5 lines each. -/

/-- Adding two non-negative floats yields a non-negative result,
conditional on finiteness. -/
@[tag_propagate]
theorem IsNonneg.fpAdd [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeMono R] [RModeZero R]
    {x y f : FiniteFp} (hx : IsNonneg (R := R) x) (hy : IsNonneg (R := R) y)
    (hf : fpAddFinite x y = Fp.finite f) :
    IsNonneg (R := R) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have hsum_nn : (0 : R) ≤ x.toVal + y.toVal :=
    add_nonneg hx.toVal_nonneg hy.toVal_nonneg
  exact ⟨hg_eq ▸ round_preserves_nonneg hsum_nn hg_round⟩

/-! ## Preservation: `fpMulFinite` -/

/-- Multiplying two non-negative floats yields a non-negative result,
conditional on finiteness. -/
@[tag_propagate]
theorem IsNonneg.fpMul [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeMono R] [RModeZero R]
    {x y f : FiniteFp} (hx : IsNonneg (R := R) x) (hy : IsNonneg (R := R) y)
    (hf : fpMulFinite x y = Fp.finite f) :
    IsNonneg (R := R) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have hprod_nn : (0 : R) ≤ x.toVal * y.toVal :=
    mul_nonneg hx.toVal_nonneg hy.toVal_nonneg
  exact ⟨hg_eq ▸ round_preserves_nonneg hprod_nn hg_round⟩

/-! ## Composition demo: mul then add -/

/-- **Composition**: `(x · y) + bias` is non-negative when all three
inputs are non-negative. The tag threads through `fpMulFinite` then
`fpAddFinite`, requiring two separate preservation applications. -/
@[tag_propagate]
theorem fpMulAdd_isNonneg [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeMono R] [RModeZero R]
    {x y bias prod result : FiniteFp}
    (hx : IsNonneg (R := R) x) (hy : IsNonneg (R := R) y)
    (hbias : IsNonneg (R := R) bias)
    (hprod : fpMulFinite x y = Fp.finite prod)
    (hresult : fpAddFinite prod bias = Fp.finite result) :
    IsNonneg (R := R) result :=
  (IsNonneg.fpMul hx hy hprod).fpAdd hbias hresult

end Flean.Tags
