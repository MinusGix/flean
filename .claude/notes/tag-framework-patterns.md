# Tag Framework — Pattern Guide

A teaching artifact synthesizing the design patterns that emerged
through Phase 0 pilots, Phase 1 infrastructure, Phase 2 (LayerNorm),
and the E-series enhancements.

**Target audience**: anyone adding a new tag or retrofitting existing
code to use tags.

See also:
- `tag-framework-plan.md` — original vision.
- `tag-framework-phase1-design.md` — framework decisions.
- `tag-framework-phase2-design.md` — LayerNorm design.
- `tag-framework-backlog.md` — live iteration log.

---

## 1. Two axes of taxonomy

Tags decompose along two orthogonal axes: what the tag **is**, and
what the tag **does for its consumer**.

### 1.1 Category axis (what the tag *is*)

| Category | Defining property | Examples |
|---|---|---|
| **Algebraic** | Has a parameter that transforms algebraically through FP ops. Composition is mechanical. | `HasAbsBound c x`, `IsBoundedRange I xs`, `IsNonneg x` |
| **Structural** | Describes input structure that collapses downstream bounds. Doesn't propagate through ops in the conventional sense. | `IsSimplex ws`, `IsOneHot j y`, `IsProb y` |
| **Regime** | Narrows the FP regime so ops become exact or tight. Preserves only under specific conditions. | `IsNormal v`, `IsSterbenz a b` |
| **Witness** | Bundles computational content needed to discharge downstream hypotheses. | `SterbenzShiftResult xs c` |
| **Partitioned** (new 2026-04-22) | Tag holds on a `Finset`-designated subset; enables heterogeneous per-index tagging. | `IsBoundedRangeOn S I xs` |

### 1.2 Payoff axis (what the tag *does for the consumer*)

| Pattern | Effect on bound | Examples |
|---|---|---|
| **Structural isolation** | RHS shape changes (e.g. `max|xᵢ|` instead of `Σ`); magnitude unchanged. | `IsSimplex`, `IsOneHot` (via `Σ y·r → r_j` collapse) |
| **Additive-tail elimination** | Drops a `+ c` term (e.g. `subnormalConst`). Strict tightening. | `IsNormal` → drops subnormalConst in `ulp_half_le` |
| **Multiplicative-tail elimination / exactness** | Drops a `· ε` factor; error collapses to 0. Strongest. | `IsSterbenz` → exact subtraction |
| **Precondition discharge** | Bound unchanged; tag absorbs a structural hypothesis the caller would otherwise supply. | `SterbenzShift` → discharges `h_shift_exact`, `IsBoundedRange` → discharges `isNormalRange(exp)` |

### 1.3 Using the axes

The axes are orthogonal — most tags belong to one category but can
deliver multiple payoffs at different call sites:

- `IsBoundedRange` is **algebraic** (category), but downstream it can
  deliver **precondition discharge** (exp stays in normal range), or
  via `toHasAbsBound`, **structural isolation** (pointwise magnitude).
- `IsOneHot` is **structural** (category), and delivers **structural
  isolation** (CE's `Σ|y·r|` collapses to `|r_j|`).

When designing a new tag: pick the category from the tag's *nature*,
then identify the payoff patterns available to consumers.

---

## 2. Tag lattice (generator relations)

Strong tags imply weaker tags.  Captured by `@[tag_generator]`-marked
`IsStrong.toWeak` lemmas.  Current lattice (2026-04-22):

```
       IsOneHot         IsSimplex
          │                 │
          └─────►IsProb◄────┘
                   │    │
                   ▼    ▼
              IsNonneg  HasAbsBound 1
              (ptwise)  (ptwise)

      IsBoundedRange
           │
           ▼
       HasAbsBound maxMag (ptwise)

        IsSterbenz (a b)
           │
           ▼
       HasAbsBound 2·|b| a      (future: via ub field)
```

Newly shipped generators:
- `IsOneHot.toIsNonneg` (E5)
- `IsOneHot.toHasAbsBound_one` (E5)
- `IsOneHot.toIsProb` (2026-04-22, T-M2)
- `IsSimplex.toIsProb` (2026-04-22, T-M2)
- `IsProb.toIsNonneg` (2026-04-22, T-M2)
- `IsProb.toHasAbsBound_one` (2026-04-22, T-M2)
- `IsSimplex.toIsNonneg` (2026-04-22, lattice cleanup)
- `IsSterbenz.toHasAbsBound` (2026-04-22, lattice cleanup)
- `IsBoundedRange.toHasAbsBound` (T-M1, retroactively marked E5)

All canonical generator relations now populated.

---

## 3. Algebraic tag propagation — the `⊞`/`⊠` model

Algebraic tags propagate through FP ops by naming the output
parameter as an algebraic function of the inputs.  Two instantiations:

### 3.1 `FpInterval` algebra for `IsBoundedRange`

`IsBoundedRange I xs` with `I : FpInterval R := { lo, hi }`.
Propagation through `fpAdd` yields `IsBoundedRange (A ⊞ B) _`, where
`⊞` is *interval addition* with rounding slack (scoped notation in
`Flean.Tags`).  Similar for `⊠` (mul), `⊟` (sub), `fpFMA`.

### 3.2 Scalar algebra for `HasAbsBound`

`HasAbsBound c x` one-dimensional analog.  Propagation through `fpAdd`
with magnitude bounds `c₁, c₂` yields `HasAbsBound ((1+η)·(c₁+c₂)) _`.
Unified variants add `+ subnormalConst`.

### 3.3 Template

Every algebraic-tag propagation theorem looks like:

```lean
theorem Tag.fpOp : Tag c₁ x → Tag c₂ y → ... →
    fpOp x y = Fp.finite f → Tag (algebra c₁ c₂) f
```

The `algebra` function is the algebraic core.  For `HasAbsBound`:
- Add: `c₁ + c₂` (with `(1+η)·` slack)
- Mul: `c₁ · c₂` (with `(1+η)·` slack)
- FMA: `c₁·c₂ + c₃` (with `(1+η)·` slack)

For `IsBoundedRange`: `fpAddN`, `fpMulN`, etc. (signed interval ops).

### 3.4 Bundle-level algebra

Extends from single ops to algorithm bundles via `magBound`:

```lean
FpSumBound.magBound b c := (1 + b.relErr) · n · c
FpDotProductBound.magBound b c_x c_y := (1 + b.relErr) · n · (c_x · c_y)
```

Bundle bridges (`BundleAbsBound.lean`, T-M4) propagate `HasAbsBound`
from inputs through the bundle's aggregate computation.

---

## 4. Structural tag specialization — the collapse pattern

Structural tags don't propagate; they **collapse** consumer-side
bounds by exploiting known structure.

### 4.1 The `Finset.sum_eq_single` toolkit

Under `IsOneHot j y`:
- `Σ (y i).toVal · f i = f j` (via `Finset.sum_eq_single j` + `hot`/`cold`)
- `Σ |(y i).toVal · f i| = |f j|`
- `Σ |(y i).toVal| = 1`
- `Σ |(y i).toVal| · g i = g j`

### 4.2 Specialization wrapper template

Every structural-tag specialization looks like:

```lean
theorem general_bound (yourHypotheses) : (loss - exact) ≤ Σ-expression

theorem structural_specialization_of_tag :
    tag j y → yourHypotheses → (loss - exact) ≤ collapsed-expression
```

where the proof calls `general_bound` then applies the collapse
lemmas.  `fpCrossEntropy_oneHot_error_bound` is the canonical
example.

### 4.3 Structural tags shine when

- The consumer's bound is an `∑ i, ...` where many terms vanish
  under the tag.
- The consumer is happy with a "single-index collapse" form, not a
  new absolute improvement.

---

## 5. Regime tag specialization — the exact/tight pattern

Regime tags narrow the FP regime so a specific op becomes exact
(error = 0) or much tighter than the general bound.

### 5.1 `IsSterbenz` pattern

`IsSterbenz a b` (same sign, magnitudes within factor 2) implies
`fpSubFinite a b` is exact: `(a - b).toVal = a.toVal - b.toVal`, no
rounding error.  Captured by `fpSubFinite_exact_of_sterbenz`.

### 5.2 Applied pattern: `SterbenzShift`

Vector-level application: if every `xs i` is Sterbenz-related to the
pivot `c`, then the entire shift is exact.  `SterbenzShiftResult`
bundles the witness; `sterbenzShift_of` extracts it.  Downstream
consumers (LSE, CE) replace `h_shift_exact` hypothesis with the tag.

### 5.3 Regime tag template

```lean
-- Regime tag → op becomes exact/tight
theorem tag_implies_exact : tag conditions → fpOp x y = Fp.finite f ∧ f.toVal = exact

-- Vector-level generalization
theorem vector_tag_to_witness : (∀ i, tag (x i) c) → witness-bundle
```

---

## 6. Witness tag specialization — the precondition-discharge pattern

Witness tags carry computational data (not just propositions) that
discharges a structural hypothesis downstream.

### 6.1 `SterbenzShiftResult`

```lean
structure SterbenzShiftResult xs c where
  xs' : Fin n → FiniteFp
  h_sub : ∀ i, fpSubFinite (xs i) c = Fp.finite (xs' i)
  h_exact : ∀ j, (xs' j).toVal = (xs j).toVal - c.toVal
```

Constructed from `∀ i, IsSterbenz (xs i) c` via `Classical.choose`.
Downstream wrappers pass `shift.xs'`, `shift.h_exact` to the general
theorem, eliminating the manual `h_shift_exact` hypothesis.

### 6.2 When to use witness tags

- When a consumer needs **both** a value and a proof about that
  value.
- When the value is easy to compute but the proof is delicate (tags
  amortize the proof once per tag witness).

### 6.3 Witness tag template

```lean
structure WitnessResult inputs where
  derived_data : ...
  h_semantics : ∀ i, ... derived_data ... = ...

def witnessFromTag : (tag-hypothesis inputs) → WitnessResult inputs
```

---

## 7. Retrofit playbook

When a consumer's existing proof has a hypothesis that a tag could
discharge:

1. **Identify the pattern** (axis 1.2): does the tag tighten the
   bound, collapse a sum, or just absorb a hypothesis?
2. **Name the wrapper**: `{existing_theorem}_{tag_name}_error_bound`
   (see `fpCrossEntropy_oneHot_error_bound`,
   `fpLogSumExp_sterbenzShift_error_bound`).
3. **Shape the hypothesis list**: keep the *call-site-facing* inputs
   the same; replace the tag-dischargeable hypothesis with the tag
   witness.
4. **Proof body**: derive the discharged hypotheses from the tag,
   call the general theorem.  For structural tags, use the
   `set`-then-`rw collapse` pattern (see CE-one-hot).  For witness
   tags, just substitute the derived witnesses.

Example (CE one-hot, ~30 lines):

```lean
theorem fpCrossEntropy_oneHot_error_bound :
    IsOneHot j ys → (general CE hypotheses) →
    |loss - CE| ≤ dp.relErr · |r_j| + (per-index term at j) := by
  set Δ_LSE := ...
  have h_gen := fpCrossEntropy_end_to_end_error_bound ...
  simp only [← hε_def, ← hDlog_def, ← hΔ_def] at h_gen
  rw [h_onehot.sum_abs_eq _, h_onehot.weighted_sum_eq _] at h_gen
  exact h_gen
```

---

## 8. When to use which pattern

| Scenario | Pattern | Recommended tag category |
|---|---|---|
| Consumer needs a magnitude bound on an output. | Algebraic propagation. | `HasAbsBound` (simplest), `IsBoundedRange` (if signed). |
| Consumer has a weighted sum where a known structure zeros many terms. | Structural isolation. | `IsOneHot`, `IsSimplex`, future `IsProb`. |
| Consumer has `+ subnormalConst` and wants to drop it. | Additive-tail elimination. | `IsNormal` on the exact value, or a magnitude lower bound. |
| Consumer has rounding error `η · |x|` on an op that could be exact. | Multiplicative-tail elimination. | `IsSterbenz`, or an exact-op witness. |
| Consumer has a structural hypothesis that's hard to supply directly. | Precondition discharge. | Witness tag or bridge lemma. |

---

## 9. Anti-patterns

### 9.1 Don't bundle finiteness with the tag

Finiteness of FP outputs is orthogonal — every preservation lemma
takes a separate `fp_op x = Fp.finite f` hypothesis.  Bundling would
couple unrelated concerns.

### 9.2 Don't force every precondition through a tag

Computed-quantity preconditions (like Softmax's `h_quot_nr`, which
depends on the runtime denominator) can't always be discharged by
input-side tags.  Accept that some hypotheses remain manual.

### 9.3 Don't make a tag a typeclass prematurely

Phase 1 explicitly rejected typeclass-inference-based tags for
performance reasons.  Plain structures compose fine for the pilot
set; typeclass inference over a growing tag lattice is a known Lean
perf trap.

### 9.4 Don't skip the generator lemma

When shipping a new tag, pair it with `.to<WeakerTag>` generator
lemmas (marked `@[tag_generator]`).  Zero-cost to add, high value for
the consumer and for the future tag-inference engine.

---

## 10. Quick-start checklist: adding a new tag

1. **Decide the category** (§1.1): algebraic / structural / regime /
   witness.  If it doesn't fit, reconsider whether it's really a tag.
2. **Name the tag**: `IsX`, `HasX`, or `X-Result` (witness).
   R-parametric unless the tag is inherently about a specific field.
3. **Structure definition**: plain `Prop`-valued struct unless
   witness category (then `Type` / data-valued).  Parameters for any
   data the user needs to name in statements.
4. **Basic facts**: `.weaken`, `.neg` (if applicable), magnitude
   extractors.  Mark obvious generators with `@[tag_generator]`.
5. **Propagation lemmas** (algebraic tags only): `fp{Add, Sub, Mul,
   FMA}_{normal, unified}`.  Mark with `@[tag_propagate]`.
6. **Bridges** (structural / regime tags): to pre-existing
   hypotheses in `Flean/Tags/Bridges/`.  Mark with `@[tag_bridge]`.
7. **Tag-specialized wrapper** for any downstream theorem: one per
   major consumer site.
8. **Register** in `Flean/Tags.lean` aggregator.

---

## 11. Further reading

- `Flean/Tags/AbsBound.lean` — the simplest algebraic tag (reference).
- `Flean/Tags/OneHot.lean` — the simplest structural tag (reference).
- `Flean/Tags/Sterbenz.lean` + `SterbenzShift.lean` — regime + witness
  example.
- `Flean/Tags/BundleAbsBound.lean` — tag-to-bundle bridges (T-M4).
- `.claude/notes/tag-framework-backlog.md` — live iteration log + a
  design-note section on a future tag-inference engine.
