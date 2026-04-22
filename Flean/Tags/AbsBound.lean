import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Operations.FpFiniteRound
import Flean.Rounding.ModeClass
import Flean.Rounding.RoundPreserves

/-!
# Greenfield Tag Pilot: `HasAbsBound`

**Status**: Phase 1 infrastructure validation. First NEW tag built from
scratch on top of:
- The unified rounding-witness helpers (`fpAddFinite_round_witness`,
  `fpMulFinite_round_witness` in `Flean/Operations/FpFiniteRound.lean`).
- The `round_preserves_P`-family meta-lemmas in
  `Flean/Rounding/RoundPreserves.lean`.

Designed to empirically test the design doc's claim (§1.2, §3.5) that a
new tag's preservations should cost ~5 lines of proof, not ~18 — and
that the meta-lemma pattern factors cleanly.

## The tag

`HasAbsBound R c x` asserts `|(x.toVal : R)| ≤ c`. Parametric over `R`
(per §1.8) and over the bound `c`.

## Preservation scope

Preservation through `fpAddFinite` / `fpMulFinite` is provided in the
**non-negative + normal-range** regime: both inputs non-negative, the
exact sum / product in normal range. This avoids sign-case-splits and
subnormal tails in the Phase 1 pilot; the generalization is future
work (see the design doc's "future additions" notes in
`RoundPreserves.lean`).

## Why parametric tags matter

`HasAbsBound c` carries a parameter `c`. The preservation lemmas
compute an output `c'` from input `c₁, c₂` plus the op's rounding
slack. This is the first pilot to exercise parametric-tag propagation
through an op — the load-bearing test flagged at the end of Phase 0.

## Measurement target

Per design doc §3.5: each preservation proof should be ≤ 7 lines.
Boilerplate reduction target is clear and measurable.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag -/

/-- `HasAbsBound R c x` asserts `|(x.toVal : R)| ≤ c`. Parametric over
`R` per design doc §1.8, parametric over the bound `c` to allow
per-value tagging. -/
structure HasAbsBound (c : R) (x : FiniteFp) : Prop where
  /-- `|x.toVal| ≤ c`. -/
  toVal_abs_le : |((x).toVal : R)| ≤ c

/-- **Vector-level** `HasAbsBound`: per-index magnitude tags packaged as
a single object.  Symmetric with the other vector-level tags
(`IsBoundedRange`, `IsSimplex`, `IsOneHot`).  Lets call sites pass
"per-index magnitude bounds" as one hypothesis rather than a `∀ i`. -/
structure HasAbsBoundVec {n : ℕ} (c : Fin n → R) (xs : Fin n → FiniteFp) : Prop where
  /-- Pointwise magnitude bound. -/
  pointwise : ∀ i, HasAbsBound (R := R) (c i) (xs i)

omit [IsStrictOrderedRing R] in
/-- Convenience projection: extract the scalar tag at index `i`. -/
theorem HasAbsBoundVec.at {n : ℕ} {c : Fin n → R} {xs : Fin n → FiniteFp}
    (h : HasAbsBoundVec (R := R) c xs) (i : Fin n) :
    HasAbsBound (R := R) (c i) (xs i) :=
  h.pointwise i

omit [IsStrictOrderedRing R] in
/-- Convenience projection: the raw inequality at index `i`. -/
theorem HasAbsBoundVec.toVal_abs_le {n : ℕ} {c : Fin n → R} {xs : Fin n → FiniteFp}
    (h : HasAbsBoundVec (R := R) c xs) (i : Fin n) :
    |((xs i).toVal : R)| ≤ c i :=
  (h.pointwise i).toVal_abs_le

/-! ## Basic properties -/

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Relaxing the bound preserves the tag. -/
theorem HasAbsBound.weaken {c c' : R} {x : FiniteFp}
    (hx : HasAbsBound (R := R) c x) (hcc : c ≤ c') :
    HasAbsBound (R := R) c' x :=
  ⟨le_trans hx.toVal_abs_le hcc⟩

/-- The bound is automatically non-negative: `|x.toVal| ≤ c` implies `0 ≤ c`
since `0 ≤ |x.toVal|`.  Derivable; named for convenient forward use. -/
theorem HasAbsBound.c_nonneg {c : R} {x : FiniteFp}
    (hx : HasAbsBound (R := R) c x) : (0 : R) ≤ c :=
  le_trans (abs_nonneg _) hx.toVal_abs_le

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Negation preserves the tag — `toVal` flips sign but magnitude is
invariant. No rounding, so no slack. -/
theorem HasAbsBound.neg {c : R} {x : FiniteFp}
    (hx : HasAbsBound (R := R) c x) :
    HasAbsBound (R := R) c (-x) := by
  refine ⟨?_⟩
  rw [FiniteFp.toVal_neg_eq_neg (R := R) x, abs_neg]
  exact hx.toVal_abs_le

/-! ## Preservation through `fpAddFinite`

Restricted regime: both operands non-negative, exact sum in normal
range. Output bound: `(1+η) · (c₁ + c₂)`. -/

/-- Preservation through `fpAddFinite` in the nonneg + normal-range
regime. Uses `fpAddFinite_round_witness` + `round_preserves_abs_bound_normal`. -/
theorem HasAbsBound.fpAdd_nonneg_normal
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeZero R]
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (hx_nn : 0 ≤ ((x).toVal : R)) (hy_nn : 0 ≤ ((y).toVal : R))
    (hsum_normal : isNormalRange ((x.toVal : R) + y.toVal))
    (hf : fpAddFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ + c₂)) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have hsum_abs : |(x.toVal : R) + y.toVal| = (x.toVal : R) + y.toVal :=
    abs_of_nonneg (add_nonneg hx_nn hy_nn)
  have hx_abs : |((x).toVal : R)| = x.toVal := abs_of_nonneg hx_nn
  have hy_abs : |((y).toVal : R)| = y.toVal := abs_of_nonneg hy_nn
  have hsum_le : |(x.toVal : R) + y.toVal| ≤ c₁ + c₂ := by
    rw [hsum_abs, ← hx_abs, ← hy_abs]
    exact add_le_add hx.toVal_abs_le hy.toVal_abs_le
  exact ⟨hg_eq ▸ round_preserves_abs_bound_normal hsum_le hsum_normal hg_round⟩

/-! ## Preservation through `fpMulFinite`

Same restricted regime as `fpAdd`. Output bound: `(1+η) · c₁ · c₂`. -/

/-- Preservation through `fpMulFinite` in the nonneg + normal-range
regime. Uses `fpMulFinite_round_witness` + `round_preserves_abs_bound_normal`. -/
theorem HasAbsBound.fpMul_nonneg_normal
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeZero R]
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (hx_nn : 0 ≤ ((x).toVal : R)) (hy_nn : 0 ≤ ((y).toVal : R))
    (hc₁_nn : 0 ≤ c₁)
    (hprod_normal : isNormalRange ((x.toVal : R) * y.toVal))
    (hf : fpMulFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ * c₂)) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have hprod_abs : |(x.toVal : R) * y.toVal| = x.toVal * y.toVal :=
    abs_of_nonneg (mul_nonneg hx_nn hy_nn)
  have hx_abs : |((x).toVal : R)| = x.toVal := abs_of_nonneg hx_nn
  have hy_abs : |((y).toVal : R)| = y.toVal := abs_of_nonneg hy_nn
  have hprod_le : |(x.toVal : R) * y.toVal| ≤ c₁ * c₂ := by
    rw [hprod_abs, ← hx_abs, ← hy_abs]
    exact mul_le_mul hx.toVal_abs_le hy.toVal_abs_le (abs_nonneg _) hc₁_nn
  exact ⟨hg_eq ▸ round_preserves_abs_bound_normal hprod_le hprod_normal hg_round⟩

end Flean.Tags
