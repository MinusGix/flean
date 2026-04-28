import Flean.Tags.Attributes
import Flean.Tags.AbsBound
import Flean.Tags.BoundedRange
import Flean.Operations.Sub
import Flean.Operations.FMA
import Flean.Operations.FpFiniteRound
import Flean.Rounding.RoundPreserves

/-!
# `HasAbsBound` Propagation Through FP Ops

The algebraic-tag calculus for `HasAbsBound`, parallel to
`BoundedRangePropagate.lean` but one-dimensional (a single magnitude
bound `c : R` instead of an `FpInterval`).

`HasAbsBound c x` asserts `|x.toVal| ≤ c`.  Under FP arithmetic, each
op introduces at most a `(1+η)` multiplicative slack in the normal-range
regime, or `(1+η)·_ + 2^(min_exp - prec)` in the subnormal-tolerant
regime.  The output constant is computed algebraically from the input
constants:

| Op     | Normal output bound               | Unified output bound                                 |
|--------|-----------------------------------|------------------------------------------------------|
| `Add`  | `(1+η)·(c₁ + c₂)`                 | `(1+η)·(c₁ + c₂) + subnormalConst`                   |
| `Sub`  | `(1+η)·(c₁ + c₂)`                 | `(1+η)·(c₁ + c₂) + subnormalConst`                   |
| `Mul`  | `(1+η)·(c₁ · c₂)`                 | `(1+η)·(c₁ · c₂) + subnormalConst`                   |
| `FMA`  | `(1+η)·(c₁·c₂ + c₃)`              | `(1+η)·(c₁·c₂ + c₃) + subnormalConst`                |

Normal-range variants require a magnitude lower bound on the exact
result (`2^min_exp ≤ |exact|`); unified variants drop it.

## Bridges to `IsBoundedRange`

* `HasAbsBound` is the magnitude projection of `IsBoundedRange`:
  `IsBoundedRange I xs → HasAbsBound I.maxMag (xs i)` for every `i`.
* Conversely, a scalar `HasAbsBound c x` yields a singleton
  `IsBoundedRange` with symmetric interval `[-c, c]`.

These bridges make `HasAbsBound` interoperable with any code already
written against `IsBoundedRange`.

## Design notes

The four-tag-specialization terminology from the Phase 1/2 docs:
`HasAbsBound`'s propagation is a **structural isolation** pattern — the
bound carries no subnormal tail in the normal-range variants, a
subnormal tail in the unified variants; the multiplicative `(1+η)` is
unavoidable as baseline rounding slack.  The normal-range variants
*eliminate the additive tail* under an extra hypothesis
(`2^min_exp ≤ |exact|`) — a pattern-2 "additive-tail elimination"
move.

This suite also reifies the third genuinely-algebraic tag (after
`IsBoundedRange` and `IsNonneg`), establishing the one-dimensional
"algebraic tag" pattern as a first-class framework notion.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
  [RModeZero R]

/-! ## Normal-range propagation

Each lemma takes a magnitude lower bound on the exact result
(`2^min_exp ≤ |exact|`) and produces the tight multiplicative bound
with no additive tail.  Uses `round_preserves_abs_bound_signed_normal`. -/

/-- `HasAbsBound` propagates through `fpAddFinite` in the normal-range
regime: `HasAbsBound c₁ x` + `HasAbsBound c₂ y` + `|x+y|` normal-range
+ `fpAddFinite x y = Fp.finite f` ⟹ `HasAbsBound ((1+η)·(c₁ + c₂)) f`. -/
@[tag_propagate]
theorem HasAbsBound.fpAdd_normal
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) + y.toVal|)
    (hf : fpAddFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ + c₂)) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have hsum_bound : |(x.toVal : R) + y.toVal| ≤ c₁ + c₂ :=
    le_trans (abs_add_le _ _) (add_le_add hx.toVal_abs_le hy.toVal_abs_le)
  refine ⟨?_⟩
  rw [← hg_eq]
  exact round_preserves_abs_bound_signed_normal hsum_bound h_normal hg_round

/-- `HasAbsBound` propagates through `fpSubFinite` in the normal-range regime. -/
@[tag_propagate]
theorem HasAbsBound.fpSub_normal
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) - y.toVal|)
    (hf : fpSubFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ + c₂)) f := by
  have hf : fpAddFinite x (-y) = Fp.finite f := hf
  exact hx.fpAdd_normal hy.neg
    (by rw [FiniteFp.toVal_neg_eq_neg, show (x.toVal : R) + -(y.toVal) =
      (x.toVal : R) - y.toVal from by ring]; exact h_normal)
    hf

/-- `HasAbsBound` propagates through `fpMulFinite` in the normal-range
regime: `HasAbsBound c₁ x` + `HasAbsBound c₂ y` + `|x·y|` normal-range
+ `fpMulFinite x y = Fp.finite f` ⟹ `HasAbsBound ((1+η)·(c₁ · c₂)) f`.

The nonnegativity of `c₁` needed for `mul_le_mul` is derived from the
tag via `HasAbsBound.c_nonneg`. -/
@[tag_propagate]
theorem HasAbsBound.fpMul_normal
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) * y.toVal|)
    (hf : fpMulFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ * c₂)) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have hprod_bound : |(x.toVal : R) * y.toVal| ≤ c₁ * c₂ := by
    rw [abs_mul]
    exact mul_le_mul hx.toVal_abs_le hy.toVal_abs_le (abs_nonneg _) hx.c_nonneg
  refine ⟨?_⟩
  rw [← hg_eq]
  exact round_preserves_abs_bound_signed_normal hprod_bound h_normal hg_round

/-- `HasAbsBound` propagates through `fpFMAFinite` in the normal-range regime.
Exact computation is `a·b + c`; bound is `(1+η)·(c_a·c_b + c_c)`.
`0 ≤ c_a` derived from `ha.c_nonneg`. -/
@[tag_propagate]
theorem HasAbsBound.fpFMA_normal
    {c_a c_b c_c : R} {a b c f : FiniteFp}
    (ha : HasAbsBound (R := R) c_a a) (hb : HasAbsBound (R := R) c_b b)
    (hc : HasAbsBound (R := R) c_c c)
    (h_normal :
      (2 : R) ^ FloatFormat.min_exp ≤ |(a.toVal : R) * b.toVal + c.toVal|)
    (hf : fpFMAFinite a b c = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c_a * c_b + c_c)) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpFMAFinite_round_witness (R := R) a b c hf
  have hab_bound : |(a.toVal : R) * b.toVal| ≤ c_a * c_b := by
    rw [abs_mul]
    exact mul_le_mul ha.toVal_abs_le hb.toVal_abs_le (abs_nonneg _) ha.c_nonneg
  have hexact_bound : |(a.toVal : R) * b.toVal + c.toVal| ≤ c_a * c_b + c_c :=
    le_trans (abs_add_le _ _) (add_le_add hab_bound hc.toVal_abs_le)
  refine ⟨?_⟩
  rw [← hg_eq]
  exact round_preserves_abs_bound_signed_normal hexact_bound h_normal hg_round

/-! ## Unified (subnormal-tolerant) propagation

Each lemma drops the magnitude lower bound in exchange for a
`subnormalConst = 2^(min_exp - prec)` additive tail.  Uses
`round_preserves_abs_bound_unified`. -/

/-- Unified `fpAddFinite` propagation: no magnitude hypothesis on the
exact sum; bound gets a `subnormalConst` additive tail. -/
@[tag_propagate]
theorem HasAbsBound.fpAdd_unified
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (hf : fpAddFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ + c₂) + FpInterval.subnormalConst) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have hsum_bound : |(x.toVal : R) + y.toVal| ≤ c₁ + c₂ :=
    le_trans (abs_add_le _ _) (add_le_add hx.toVal_abs_le hy.toVal_abs_le)
  refine ⟨?_⟩
  rw [← hg_eq]
  exact round_preserves_abs_bound_unified hsum_bound hg_round

/-- Unified `fpSubFinite` propagation. -/
@[tag_propagate]
theorem HasAbsBound.fpSub_unified
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (hf : fpSubFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ + c₂) + FpInterval.subnormalConst) f := by
  have hf : fpAddFinite x (-y) = Fp.finite f := hf
  exact hx.fpAdd_unified hy.neg hf

/-- Unified `fpMulFinite` propagation.  `0 ≤ c₁` derived from `hx.c_nonneg`. -/
@[tag_propagate]
theorem HasAbsBound.fpMul_unified
    {c₁ c₂ : R} {x y f : FiniteFp}
    (hx : HasAbsBound (R := R) c₁ x) (hy : HasAbsBound (R := R) c₂ y)
    (hf : fpMulFinite x y = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c₁ * c₂) + FpInterval.subnormalConst) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have hprod_bound : |(x.toVal : R) * y.toVal| ≤ c₁ * c₂ := by
    rw [abs_mul]
    exact mul_le_mul hx.toVal_abs_le hy.toVal_abs_le (abs_nonneg _) hx.c_nonneg
  refine ⟨?_⟩
  rw [← hg_eq]
  exact round_preserves_abs_bound_unified hprod_bound hg_round

/-- Unified `fpFMAFinite` propagation.  `0 ≤ c_a` derived from `ha.c_nonneg`. -/
@[tag_propagate]
theorem HasAbsBound.fpFMA_unified
    {c_a c_b c_c : R} {a b c f : FiniteFp}
    (ha : HasAbsBound (R := R) c_a a) (hb : HasAbsBound (R := R) c_b b)
    (hc : HasAbsBound (R := R) c_c c)
    (hf : fpFMAFinite a b c = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c_a * c_b + c_c) + FpInterval.subnormalConst) f := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpFMAFinite_round_witness (R := R) a b c hf
  have hab_bound : |(a.toVal : R) * b.toVal| ≤ c_a * c_b := by
    rw [abs_mul]
    exact mul_le_mul ha.toVal_abs_le hb.toVal_abs_le (abs_nonneg _) ha.c_nonneg
  have hexact_bound : |(a.toVal : R) * b.toVal + c.toVal| ≤ c_a * c_b + c_c :=
    le_trans (abs_add_le _ _) (add_le_add hab_bound hc.toVal_abs_le)
  refine ⟨?_⟩
  rw [← hg_eq]
  exact round_preserves_abs_bound_unified hexact_bound hg_round

/-! ## Bridges to/from `IsBoundedRange` -/

/-- Every tagged entry of an `IsBoundedRange` satisfies `HasAbsBound I.maxMag`.
The magnitude projection: a two-sided bound decays to the single-sided
magnitude tag. -/
theorem IsBoundedRange.toHasAbsBound {n : ℕ} {I : FpInterval R}
    {xs : Fin n → FiniteFp} (h : IsBoundedRange (R := R) I xs) (i : Fin n) :
    HasAbsBound (R := R) I.maxMag (xs i) :=
  ⟨h.toVal_abs_le i⟩

/-- Conversely, `HasAbsBound c x` gives a singleton `IsBoundedRange`
over the symmetric interval `[-c, c]`.  The reverse direction of the
magnitude projection: a single-sided magnitude tag recovers a
symmetric two-sided bound. -/
theorem HasAbsBound.toIsBoundedRange {c : R} {x : FiniteFp}
    (h : HasAbsBound (R := R) c x) :
    IsBoundedRange (R := R) ⟨-c, c⟩ (fun _ : Fin 1 => x) := by
  refine ⟨?_, ?_⟩
  · intro _
    have := h.toVal_abs_le
    have h_neg : -c ≤ (x.toVal : R) := by
      have := abs_le.mp this
      exact this.1
    exact h_neg
  · intro _
    have := h.toVal_abs_le
    exact (abs_le.mp this).2

/-! ## Bridges from `isNormalRange`

The reverse direction of `Flean/Tags/Bridges/ToIsNormalRange.lean`:
given an `isNormalRange` witness on a `FiniteFp`'s `.toVal`, recover a
`HasAbsBound` tag at the format's overflow boundary
`2^(max_exp + 1)`.

Closes the unidirectional gap flagged in the framework eval — callers
holding an `isNormalRange` hypothesis no longer need to re-derive
`|x.toVal| ≤ 2^(max_exp+1)` by hand. -/

omit [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec]
  [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeZero R] in
/-- **Bridge**: from a magnitude-form normal-range witness, recover a
magnitude tag at the overflow boundary.  Works for arbitrarily-signed
`f.toVal`. -/
@[tag_bridge]
theorem HasAbsBound.ofIsNormalRange_abs {f : FiniteFp}
    (h : isNormalRange (|((f.toVal : R))|)) :
    HasAbsBound (R := R) ((2 : R) ^ ((FloatFormat.max_exp : ℤ) + 1)) f :=
  ⟨le_of_lt h.right⟩

/-- **Bridge**: from a positive-value normal-range witness, recover a
magnitude tag at the overflow boundary.  `isNormalRange v` already
implies `0 < v`, so the absolute value is redundant. -/
@[tag_bridge]
theorem HasAbsBound.ofIsNormalRange {f : FiniteFp}
    (h : isNormalRange ((f.toVal : R))) :
    HasAbsBound (R := R) ((2 : R) ^ ((FloatFormat.max_exp : ℤ) + 1)) f := by
  refine ⟨?_⟩
  rw [abs_of_pos (isNormalRange_pos _ h)]
  exact le_of_lt h.right

/-! ## Demo: a chained bound via HasAbsBound algebra

Classical polynomial-like computation: `(x · y) + z`, where `x, y, z`
all have individual magnitude bounds.  The tagged output constant is
derived algebraically from the inputs — no manual magnitude chasing. -/

/-- Demo: chained FMA-like computation `(x · y) + z` yields a
bound mechanically computed from the input constants.  Since
`0 ≤ c_x` is now derived from the tag, the caller only supplies
the three tag witnesses + the FMA equation. -/
theorem HasAbsBound.demo_mul_add_unified
    {c_x c_y c_z : R} {x y z f : FiniteFp}
    (hx : HasAbsBound (R := R) c_x x) (hy : HasAbsBound (R := R) c_y y)
    (hz : HasAbsBound (R := R) c_z z)
    (hfma : fpFMAFinite x y z = Fp.finite f) :
    HasAbsBound (R := R) ((1 + η) * (c_x * c_y + c_z) + FpInterval.subnormalConst) f :=
  hx.fpFMA_unified hy hz hfma

end Flean.Tags
