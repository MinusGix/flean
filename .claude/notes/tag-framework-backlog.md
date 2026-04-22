# Tag Framework — Iteration Backlog

**Status**: live working list.  Updated as items land or get reprioritised.
Captures improvement ideas and open concerns from the post-Phase-2
overview (2026-04-22).  Not all items are good; ranked loosely within
each tier.

See also:
- `tag-framework-plan.md` — original vision.
- `tag-framework-phase1-design.md` — Phase 1 record-of-decisions.
- `tag-framework-phase2-design.md` — Phase 2 (LayerNorm) record-of-decisions.

---

## What's in hand (2026-04-22)

| File | Role | LOC |
|---|---|---|
| `Flean/Tags/FpInterval.lean` | interval algebra (`⊞`/`⊠`/`⊟`) | 175 |
| `Flean/Tags/BoundedRange.lean` | `IsBoundedRange I xs` | 59 |
| `Flean/Tags/BoundedRangePropagate.lean` | 6 propagations through fp ops | 554 |
| `Flean/Tags/AbsBound.lean` | `HasAbsBound c x` (scalar) | 133 |
| `Flean/Tags/Nonneg.lean` | `IsNonneg x` + fpAdd/fpMul preservation | 134 |
| `Flean/Tags/Normal.lean` | `IsNormal v` (real-valued) | 128 |
| `Flean/Tags/Simplex.lean` | `IsSimplex ws` | 185 |
| `Flean/Tags/Sterbenz.lean` | `IsSterbenz a b` + exact-sub | 145 |
| `Flean/Tags/SterbenzShift.lean` | vector shift extraction + LSE/CE wrappers | 206 |
| `Flean/Tags/SoftmaxBounded.lean` | softmax bridge | 114 |
| `Flean/Tags/LayerNorm.lean` | LayerNorm fully-tagged bound | 679 |
| `Flean/Tags/Bridges/ToIsNormalRange.lean` | bridges | 322 |
| `Flean/Rounding/RoundPreserves.lean` | meta-lemma kernel | 273 |

Four specialization patterns validated:
1. **Structural isolation** (`IsSimplex`)
2. **Additive-tail elimination** (`IsNormal`)
3. **Multiplicative-tail elimination / exactness** (`IsSterbenz`)
4. **Precondition discharge** (`SterbenzShift`, `IsBoundedRange` → `isNormalRange(exp ·)`)

---

## Short-term (incremental, bounded scope)

### T-S1: LSE/CE subnormal-tail elimination under separation [low scope, direct win]

Softmax has `fpSoftmax_bound_of_separated` (drops `subnormalConst` tail under
`IsBoundedRange I xs` + separation constant `4·n·2^min_exp`).  The
analogous LSE and CE wrappers don't exist yet.

**Scope**: ~300 lines across LSE + CE.  Mostly mechanical.

### T-S2: Softmax SterbenzShift wrapper [trivial]

Parallel to `fpLogSumExp_sterbenzShift_error_bound` /
`fpCrossEntropy_sterbenzShift_error_bound`.  Softmax's end-to-end
theorem (`fpSoftmax_end_to_end_error_bound`) takes the same
`h_shift_exact` hypothesis and would accept the same wrapper shape.

**Scope**: ~50 lines.  Copy-paste of the LSE wrapper.

### T-S3: Promote more meta-lemmas into `RoundPreserves.lean` [cleanup]

Candidates seen across pilots:
- `round_preserves_le_abs_bound_subnormal` — unified (subnormal-tolerant) variant
  of `round_preserves_abs_bound_normal`.
- Tag-independent finiteness-propagation helper (currently duplicated in
  `Nonneg.lean` + elsewhere).
- `round_preserves_sign` — if `x`'s sign is determined, `round x`'s sign is too.

Each would shave duplicate code from 2–3 files.

### T-S4: `HasAbsBound` fpAdd / fpMul sign-agnostic variants [API completeness]

Current propagations (`fpAdd_nonneg_normal`, `fpMul_nonneg_normal`) require
nonneg inputs.  A general magnitude-based version requires only
`isNormalRange` on the exact result.  The `|x+y| ≤ |x|+|y|` triangle plus
rounding slack covers the additive case; multiplication is `|x·y| = |x|·|y|`.

**Scope**: ~100 lines.  Sister theorems to the existing two.

### T-S5: `@[bridge_to]` attribute for discoverability [infra, defer unless demand]

Currently bridges are discoverable by filename navigation only.  An
attribute would enable queries like "which lemmas produce
`isNormalRange ?x`?"  Not urgent; add when lookup friction becomes real.

---

## Medium-term (new patterns)

### T-M1: Tag calculus elaboration [architectural, high elegance] — **SHIPPED 2026-04-22**

`Flean/Tags/AbsBoundPropagate.lean` (~248 lines, sorry-free).  Builds
the full propagation suite for `HasAbsBound`, parallel to
`BoundedRangePropagate.lean` but one-dimensional (a single
magnitude bound `c : R` instead of an interval).

Meta-lemma kernel extended with two new theorems in
`Flean/Rounding/RoundPreserves.lean`:
- `round_preserves_abs_bound_signed_normal` (sign-agnostic + normal range)
- `round_preserves_abs_bound_unified` (sign-agnostic + subnormal-tolerant)

Eight propagation theorems — `fp{Add,Sub,Mul,FMA}_{normal,unified}` —
plus bridges `IsBoundedRange.toHasAbsBound` (pointwise magnitude
projection) and `HasAbsBound.toIsBoundedRange` (singleton symmetric
interval).  Output constants computed algebraically:

| Op    | Normal output bound            | Unified output bound                        |
|-------|--------------------------------|---------------------------------------------|
| Add   | `(1+η)·(c₁+c₂)`                | `(1+η)·(c₁+c₂) + subnormalConst`            |
| Sub   | `(1+η)·(c₁+c₂)`                | `(1+η)·(c₁+c₂) + subnormalConst`            |
| Mul   | `(1+η)·(c₁·c₂)`                | `(1+η)·(c₁·c₂) + subnormalConst`            |
| FMA   | `(1+η)·(c₁·c₂+c₃)`             | `(1+η)·(c₁·c₂+c₃) + subnormalConst`         |

This reifies `HasAbsBound` as the third algebraic tag (after
`IsBoundedRange` and `IsNonneg`), establishing the one-dimensional
"algebraic tag" pattern as a first-class framework notion.  Each
propagation proof is 5–11 lines — meta-lemma kernel performance
validated.

**Original description** (kept for context):

Only `IsBoundedRange` currently has an algebraic propagation story
(`FpInterval` with `⊞`/`⊠`/`⊟`).  Other tags threaded through ops don't
name their output parameter algebraically — they're scheme-specific.

**Candidates for a lift**:
- **`HasAbsBound`**: cleanest lift after `IsBoundedRange`.  Output
  constant is `c₁ + c₂` (add, with rounding slack), `c₁ · c₂` (mul), `c`
  (neg).  One-dimensional — simpler algebra than `FpInterval`.
- **`IsNormal`**: non-propagatable in general (cancellation can zero
  the result), so skip unless a conditional variant (`IsNormal v ∧
  ¬near_cancellation → IsNormal (v + v')`) proves worth it.

**Deliverable shape**:
```lean
-- In AbsBoundPropagate.lean
theorem HasAbsBound.fpAdd [...] :
    HasAbsBound c₁ x → HasAbsBound c₂ y → fpAddFinite x y = Fp.finite f →
    HasAbsBound ((1 + η) · (c₁ + c₂)) f
-- Plus scalar helpers on the real-valued side.
```

**Synergy**: `HasAbsBound` and `IsBoundedRange` are algebraic duals —
the former tracks a single magnitude bound, the latter tracks an
interval.  A `HasAbsBound c x ↔ IsBoundedRange {lo = -c, hi = c} [x]`
coercion would connect them.

**Scope**: ~300–400 lines.  Mirrors `BoundedRangePropagate.lean` but
one-dimensional.

### T-M2: New fundamental tags [utility, pick carefully] — **IsOneHot SHIPPED 2026-04-22**

`Flean/Tags/OneHot.lean` (~229 lines, sorry-free).

- `IsOneHot (R := R) j y` — R-parametric tag: `(y j).toVal = 1` and
  `(y i).toVal = 0` for `i ≠ j`.  Hot index carried as explicit
  parameter (mirrors `IsBoundedRange`'s interval parameter).
- Sum-collapse suite: `sum_eq`, `sum_abs_eq`, `sum_abs_eq_one`,
  `weighted_sum_eq` (the four fundamental algebraic facts) plus
  `toVal_nonneg` and `toVal_le_one`.
- `fpCrossEntropy_oneHot_error_bound` — CE's general bound
  `dp.relErr · Σ|y·r| + Σ|y|·(...)` collapses to
  `dp.relErr · |r_j| + (η·|x_j − lse| + subnormalConst + Δ_LSE)`.
  Order-of-magnitude tighter for the standard ML classifier case.
- Instantiates the **structural isolation** pattern (Phase 0 finding 1):
  RHS sum shape changes, no magnitude tightening — but the collapse is
  dramatic.

**Remaining `IsProb`, `HasRangeBound`, `IsQuantized` not yet shipped.**

**Original description** (kept for context):

Candidates with demonstrable downstream demand:

- **`IsProb y`** (`IsNonneg y ∧ Σ y ≤ 1`): specializes CE's
  `Σ|y_i|` term (collapses to `Σ y_i ≤ 1`).  Natural for classifier
  target distributions.
- **`IsOneHot y`** (`∃ j, y_j = 1 ∧ ∀ i ≠ j, y_i = 0`): collapses CE's
  dot product to `-r_j` — the standard classifier-loss form.  Highest
  practical ML value.
- **`HasRangeBound c x v_center`** (`|x.toVal − v_center| ≤ c`):
  relaxes `IsBoundedRange` to asymmetric bounds around a known center.
  Useful for perturbation analyses (backward error).
- **`IsQuantized grid x`**: values on a coarser grid `grid ⊆ FP`.
  Necessary for StorageFormats ↔ Operations bridging and quantization
  error reasoning.

Rank by demand: `IsOneHot` > `IsProb` > `HasRangeBound` > `IsQuantized`.

### T-M3: Partitioned softmax (Candidate A from Phase 2 doc) [framework-novel]

Subset `S ⊆ Fin n` designates "possibly subnormal" indices.  Tag holds
on `i ∉ S`; per-index bound branches.  Framework novelty: tags
composing with `Finset` subsetting over a vector with a shared global
quantity (the denom).  Stress-tests the framework on per-index
partitioning.

**Scope**: ~500 lines.  Phase 2 design doc §1 has the candidate write-up.

### T-M4: Tag propagation through `FpSumBound` / `FpDotProductBound` [composition gap] — **SHIPPED 2026-04-22**

`Flean/Tags/BundleAbsBound.lean` (~201 lines, sorry-free).  Extrinsic
option (separate theorems per tag × bundle pair) per the plan.

Six bridge theorems, three per bundle:

* `FpSumBound.hasAbsBound_of_per_index` — per-index `HasAbsBound (c i)` → `(1 + relErr) · Σ c i`.
* `FpSumBound.hasAbsBound_of_uniform` — uniform `c` → `(1 + relErr) · n · c`.
* `FpSumBound.hasAbsBound_of_isBoundedRange` — `IsBoundedRange I xs` → `(1 + relErr) · n · I.maxMag`.
* `FpDotProductBound.hasAbsBound_of_per_index` — per-index bounds on both vectors → `(1 + relErr) · Σ c_x·c_y`.
* `FpDotProductBound.hasAbsBound_of_uniform` — uniform `c_x, c_y` → `(1 + relErr) · n · (c_x · c_y)`.
* `FpDotProductBound.hasAbsBound_of_isBoundedRange` — `IsBoundedRange` on both → `(1 + relErr) · n · (Ix.maxMag · Iy.maxMag)`.

The per-index theorem is primary; uniform and `IsBoundedRange`
corollaries via `HasAbsBound.weaken` + `Finset.sum_const`.  Proofs
share a triangle-inequality skeleton: `|result| ≤ |result - exact| +
|exact|`, then bound each piece by the bundle's `relErr · Σ |xs|`
and the per-index magnitude hypotheses.

Unlocks tagged composition across the algorithm boundary without
unbundling.  Option 2 (intrinsic tag fields on the bundles) not yet
attempted; revisit if extrinsic friction appears.

**Original description** (kept for context):

Currently these bundles carry `relErr` but no tag info.  Adding tag
propagation — e.g. `IsBoundedRange I xs → ∃ c, |FpSumBound.result| ≤ c`
— would let downstream tagged bounds compose without unbundling.

Two options:
1. **Extrinsic**: separate theorems per tag per bundle constructor
   (`IsBoundedRange.ofNaive`, `IsBoundedRange.ofKahan`, etc.).
2. **Intrinsic**: add optional tag fields to the bundle, carried
   through adapters.

Option 1 is less invasive, option 2 is more elegant.  Start with
option 1 for one tag (`HasAbsBound` probably), see if option 2 is
worth the refactor.

**Scope**: ~300 lines for option 1, per tag.

### T-M5: `IsSterbenz` generalization [API]

The current `IsSterbenz` requires `same_sign`.  Sterbenz's conclusion
holds more generally (mixed-sign regimes, cancellation-safe ranges).  A
tag hierarchy `IsSterbenzSameSign ⊂ IsSterbenz` — or relaxing the
structure — could unlock additional use cases without breaking existing
callers.

**Scope**: ~100 lines + retrofitting ~2 call sites.

---

## Long-term (architectural)

### T-L1: Pattern-guide document [teaching artifact]

The tetra of specialization patterns is currently only in Phase 0 file
headers + design docs.  A `tag-framework-patterns.md` crystallizing
which pattern applies to which downstream proof would make the
framework teachable.  Include: when to use each pattern, template
proof shape, retrofit strategy.

### T-L2: Tag transformer typeclass [if tag count grows]

If a fifth or sixth fundamental tag lands with algebraic propagation,
a `TagTransformer` typeclass (`class TagOp (t : TagInfo) (op : FpOp)
where out : TagInfo`) could unify the propagation story across tags.
Not yet warranted — `IsBoundedRange`'s bespoke `FpInterval` reads well
without a typeclass layer.  Revisit when the third algebraic tag
appears.

### T-L3: Typeclass-based chain composition [if demand appears]

Phase 1 explicitly left the door open to add a `Preserves` typeclass
*on top* of structures, not replacing them, if chain composition across
3+ ops becomes common.  Not yet observed in the pilots.  Revisit when
5+ users ask for `infer_instance`-driven tag flow.

---

## Technical debt / open concerns

### T-D1: `SterbenzShiftResult` required `[RModeExec]` in its `variable` block

The struct uses `fpSubFinite` in its fields.  Without `[RModeExec]` in
scope, elaboration fails with "failed to synthesize instance of type class
RModeExec".  Minor gotcha for anyone writing a similar tag struct.
Potential fix: a `[FloatFormat, RModeExec]` context macro.

### T-D2: No tag preservation through subnormal-producing ops

`IsNormal` doesn't propagate through `fpAdd` when the result is
subnormal.  For LayerNorm this is intrinsic (differences near the mean
can be arbitrarily small).  For other workloads, a weakened
`IsNormalOrSubnormal` (or `IsFinite`, but the latter is already
trivially true) could bridge the gap.  Low priority.

### T-D3: Bridges are unidirectional

`IsBoundedRange → isNormalRange(exp ·)` exists.  The reverse packaging
(`isNormalRange v → HasAbsBound _ v`) doesn't, and would let callers
with an `isNormalRange` witness recover a `HasAbsBound` without
re-deriving the magnitude.  Not critical, limits composability.

### T-D4: Five LayerNorm preconditions can't dematerialize structurally

The five remaining manual preconditions in LayerNorm (mean-div,
shift, square, variance-div, normalize normal-range) are all tied to
the `x_i − μ` factor, which can be arbitrarily small for inputs close
to the mean.  **This is a property of LayerNorm's math, not a framework
gap.**  Documented honestly in Phase 2 design doc §7 scorecard.  Listed
here for visibility, not as an action item.

### T-D5: Tag lookup / naming conventions are inconsistent

- `IsBoundedRange` uses a structure parameter (`FpInterval R`).
- `HasAbsBound c x` and `IsSterbenz a b` take R-parameters directly.
- `IsSimplex ws` / `IsNonneg x` take FP arguments.
- `IsNormal v` takes an R.

Not a bug, but the naming isn't systematic.  Convention proposal: tags
whose content is an R-valued predicate take R-parameters; tags whose
content is structural take FP.  Mostly matches current state.  Make it
explicit in T-L1.

### T-D6: No integration test suite

Each tag file has an `example` at the bottom as a sanity check, but
there's no systematic "tag calculus smoke test" checking that typical
chains type-check and produce the expected output tags.  A
`Flean/Tags/TestCases.lean` (parallel to `BoundCalc/TestCases.lean`)
would catch regressions when a propagation lemma's signature changes.

---

## Ranking snapshot (2026-04-22, post-T-M1, post-T-M2, post-T-M4)

Roughly in order of expected value:

1. ~~**T-M1** (tag calculus elaboration)~~ — **DONE**.
2. ~~**T-M2 `IsOneHot`**~~ — **DONE**.  Remaining T-M2 items (`IsProb`,
   `HasRangeBound`, `IsQuantized`) lower priority; pick on demand.
3. ~~**T-M4** (tag propagation through bundles)~~ — **DONE** (extrinsic
   option).  Revisit option 2 (intrinsic tag fields) only if friction.
4. **T-S1** (LSE/CE tail elimination) — direct win, low scope.
5. **T-M3** (partitioned softmax) — most framework-novel, large scope.
6. **T-L1** (pattern guide) — now a natural move; three major
   structural pieces shipped to document.
7. **T-D6** (integration test suite) — with five+ propagation-style
   files, a smoke-test file would catch signature regressions.
8. `IsProb` / `HasRangeBound` / `IsQuantized` — narrower ML-specific
   tags; lowest priority unless a concrete workload asks.

Items ≥ 5 are lower priority pending developer interest.
