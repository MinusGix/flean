# Tag Framework — Iteration Backlog

**Status**: live working list.  Updated as items land or get reprioritised.
Captures improvement ideas and open concerns from the post-Phase-2
overview (2026-04-22).  Not all items are good; ranked loosely within
each tier.

See also:
- `tag-framework-plan.md` — original vision.
- `tag-framework-phase1-design.md` — Phase 1 record-of-decisions.
- `tag-framework-phase2-design.md` — Phase 2 (LayerNorm) record-of-decisions.
- `tag-framework-patterns.md` — pattern guide (E1 / T-L1 deliverable).

---

## What's in hand (2026-04-22)

| File | Role | LOC |
|---|---|---|
| `Flean/Tags/FpInterval.lean` | interval algebra (`⊞`/`⊠`/`⊟`) | 175 |
| `Flean/Tags/BoundedRange.lean` | `IsBoundedRange I xs` | 59 |
| `Flean/Tags/BoundedRangePropagate.lean` | 6 propagations through fp ops | 554 |
| `Flean/Tags/AbsBound.lean` | `HasAbsBound c x` (scalar) | 133 |
| `Flean/Tags/AbsBoundPropagate.lean` | 8 HasAbsBound propagations (T-M1) | 248 |
| `Flean/Tags/BundleAbsBound.lean` | FpSum/FpDot bundle bridges (T-M4) | 201 |
| `Flean/Tags/Nonneg.lean` | `IsNonneg x` + fpAdd/fpMul preservation | 134 |
| `Flean/Tags/Normal.lean` | `IsNormal v` (real-valued) | 128 |
| `Flean/Tags/Simplex.lean` | `IsSimplex ws` | 185 |
| `Flean/Tags/Sterbenz.lean` | `IsSterbenz a b` + exact-sub | 145 |
| `Flean/Tags/SterbenzShift.lean` | vector shift extraction + LSE/CE wrappers | 206 |
| `Flean/Tags/OneHot.lean` | `IsOneHot j y` + CE specialization (T-M2) | 229 |
| `Flean/Tags/Prob.lean` | `IsProb y` + CE specialization (T-M2 cont.) | 271 |
| `Flean/Tags/SoftmaxBounded.lean` | softmax bridge | 114 |
| `Flean/Tags/LayerNorm.lean` | LayerNorm fully-tagged bound | 679 |
| `Flean/Tags/Bridges/ToIsNormalRange.lean` | bridges | 322 |
| `Flean/Rounding/RoundPreserves.lean` | meta-lemma kernel | 346 |

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

### T-M2: New fundamental tags [utility, pick carefully] — **IsOneHot + IsProb SHIPPED 2026-04-22**

- `Flean/Tags/OneHot.lean` (~229 lines) — `IsOneHot j y`.
- `Flean/Tags/Prob.lean` (~271 lines) — `IsProb y` (sub-probability:
  nonneg + Σ ≤ 1).  Fills the lattice gap between `IsOneHot`/`IsSimplex`
  and `IsNonneg`.
  - Ingress generators: `IsOneHot.toIsProb`, `IsSimplex.toIsProb`.
  - Egress generators: `IsProb.toIsNonneg`, `IsProb.toHasAbsBound_one`.
  - `abs_eq`, `sum_abs_le_one`, `toVal_le_one` derived facts.
  - `fpCrossEntropy_isProb_error_bound` — CE bound in
    "expectation under `ys`" form.  `|y_i|` drops to `y_i`,
    weighted sums preserved.

Remaining T-M2 items:

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

### T-M3: Partitioned softmax (Candidate A from Phase 2 doc) [framework-novel] — **SHIPPED 2026-04-22 (partial)**

`Flean/Tags/BoundedRangeOn.lean` (~286 lines, sorry-free).  Landed
the core partitioned-tag pattern; the "full softmax re-proof with
per-index case split" flagged in the Phase 2 doc is **not** attempted
here (that would be closer to the 500-line estimate).  What shipped:

* `IsBoundedRangeOn S I xs` — partitioned-domain tag.  Holds when
  the interval bound applies on `i ∈ S`, arbitrarily elsewhere.
  Framework-novel: **first tag that composes with `Finset`
  subsetting**, enabling heterogeneous per-index tagging.
* Lattice pieces: `IsBoundedRange.toBoundedRangeOn` (any S),
  `IsBoundedRangeOn.toBoundedRange_of_univ`,
  `IsBoundedRangeOn.toHasAbsBound_of_mem` (generator),
  `.subset`, `.union`, `.empty`.
* `sum_abs_le_on`: `Σ i ∈ S, |xs_i| ≤ |S| · I.maxMag`.
* `sum_abs_full_le`: full-domain sum with fallback `c` on complement.
* `FpSumBound.hasAbsBound_of_boundedRangeOn` — bundle bridge
  producing the sharpened `|S|·I.maxMag + |S^c|·c` output bound.
* `hasAbsBound_of_boundedRangeOn_univ` corollary collapsing to the
  standard full-domain bound when `S = univ`.

Remaining (deferred):
* A full `fpSoftmax_partitioned_error_bound` per-index case-split
  theorem that re-proves softmax with `i ∈ S` vs `i ∉ S` paths
  producing differently-tight coefficients.  Requires re-doing the
  softmax end-to-end chain with a non-uniform bound structure;
  ~200-300 additional lines.  Shelved unless a consumer workload
  appears.

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

---

## E-series: 2026-04-22 enhancements from post-T-M4 review

Nine items surfaced while shipping T-M1/T-M2/T-M4 back-to-back and
reflecting on what worked and what didn't.  Ranked in agreed priority
order (user confirmation 2026-04-22).

### E1: Pattern-guide doc [T-L1 realized] [priority 4]

Write `.claude/notes/tag-framework-patterns.md`.  Two axes of taxonomy:

* **Category axis** (what the tag *is*): algebraic / structural /
  regime / witness.
* **Payoff axis** (what the tag *does*): structural isolation /
  additive-tail elimination / exactness / precondition discharge.

Includes: when to use which pattern, retrofit playbook, tag-lattice
diagram grounded on the generator lemmas from E5.

Benefits from E5 landing first (lattice concrete) and E4 (`magBound`
named) for cleaner examples.

### E2: `HasAbsBound.c_nonneg` + `IsBoundedRange` dual [priority 1]

Scope: ~50 lines.  Add:
* `HasAbsBound.c_nonneg : HasAbsBound c x → 0 ≤ c`.
* `IsBoundedRange.lo_le_hi : IsBoundedRange I xs → 0 < n → I.lo ≤ I.hi`
  (only when `xs` is nonempty).

Retrofit T-M4's `FpDotProduct.hasAbsBound_of_*` to derive `hc_x_nn`
from the tag instead of taking it as a hypothesis.  Reduces friction
across all downstream consumers.

### E3: `letI` → `def` refactor [deferred, priority 10]

Symptom: downstream wrappers over `letI`-heavy end-to-end theorems
must `set`-rebind + `simp only [← hX_def]` to re-fold.  CE-one-hot
hit this three times.

Fix: promote `ε_sum`, `D_log`, `Δ_LSE`, etc. in LSE/CE end-to-end
theorems to named `def`s.  Touches ~5 files.

Deferred until a fifth wrapper hits the same pattern — 3 existing
wrappers isn't enough to justify the refactor.

### E4: Bundle `magBound` abbrev [priority 4]

T-M4's bundle bridges all conclude `HasAbsBound ((1 + b.relErr) · n · c)
b.result`.  That expression should have a name:

```lean
def FpSumBound.magBound (b : FpSumBound xs R) (c : R) : R :=
  (1 + b.relErr) * (n : R) * c
```

Reshapes the six bridge theorems.  Matches the "algebraic tag" ethos
from T-M1 (where `FpInterval.⊞` named the algebra).  ~100 lines.

### E5: Tag generator lemmas [priority 2]

Pattern: strong tags yield weaker ones via canonically-named `.toX`
lemmas.

First pass:
* `IsOneHot.toIsNonneg : IsOneHot j y → ∀ i, IsNonneg (y i)`
* `IsOneHot.toHasAbsBound_one : IsOneHot j y → ∀ i, HasAbsBound 1 (y i)`
* `IsSimplex.toIsNonneg : IsSimplex ws → ∀ i, IsNonneg (ws i)`
* `IsSterbenz.toHasAbsBound` (via magnitude ratio)

Forward-compatible `@[tag_generator]` attribute (zero cost now, seeds
the lattice registry for any future tag-inference work).

Prerequisite for E1's lattice diagram.  ~150 lines.

### E6: `IsBoundedRange` use-site audit [priority 5]

Empirical question: what fraction of `IsBoundedRange` consumers use
signed info (`lo`/`hi` separately) versus just magnitude (`maxMag`)?

Produce a short report.  If majority is magnitude-only,
`IsBoundedRange` is over-engineered for those sites — consider
recommending `HasAbsBound` as the default when signed info isn't
needed.  ~observational, no code.

### E7: `FpSumBoundCompensated` bundle bridge [priority 3]

Analog of T-M4 for the compensated bundle.  Three bridges
(per-index, uniform, `IsBoundedRange`), output bound on
`sigma := sum + comp` via triangle.

~50 lines; closes the bundle-bridge suite.

### E8: `HasAbsBoundVec` wrapper [priority 6]

Convenience for passing vector magnitude bounds as one object:

```lean
def HasAbsBoundVec {n} (c : Fin n → R) (xs : Fin n → FiniteFp) : Prop :=
  ∀ i, HasAbsBound (c i) (xs i)
```

Retrofit T-M4's per-index variants.  ~50 lines.  Symmetric with the
other vector-level tags (`IsBoundedRange`, `IsSimplex`, `IsOneHot`).

### E9: `[FPAxioms R]` typeclass bundle [priority 9]

Every propagation theorem repeats `[RMode R] [RModeExec]
[RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeZero R]`.
Bundle them:

```lean
class FPAxioms (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] extends RMode R, RModeExec, RoundIntSigMSound R,
    RModeNearest R, RModeConj R, RModeZero R
```

Cross-cutting refactor; potentially 20+ files.  Low priority, high
yield when touched.

---

## Design note: tag inference engine

Flagged by the user on 2026-04-22.  A real long-term question.

### What it would be

A tactic `tag_infer` that, given tags on inputs and an FP expression,
chains propagation/generator lemmas to produce tags on the result.
Analogous to `linearize` or `bound_calc` but for tags.

### Prerequisites (none exist yet)

1. Tag lattice documented (E1 / T-L1).
2. Canonical-name lemma registry (E5).
3. Attribute system: `@[tag_propagate]`, `@[tag_generator]`,
   `@[tag_bridge]`.
4. Normalization strategy for when multiple paths give different
   output tags.

### Scale thresholds

Currently: 7 tags, ~14 propagation theorems, ~6 bundle bridges, ~3
bridges-to-hypotheses.  Manageable by name.

Engine pays off around: 20+ tags OR users routinely chaining 4+ ops.
We're below threshold.

### Path forward

* **Now** (zero cost, forward-compatible): add `@[tag_propagate]`
  / `@[tag_generator]` / `@[tag_bridge]` attributes during E5.  When
  the engine is built, these are already populated.
* **Short-term**: keep building the lattice manually (E5 and friends).
* **Long-term** (post-15th tag): build the engine as a `bound_calc`-
  family tactic — attribute-driven dispatch, explicit in proofs,
  bounded search depth.  Rough estimate: 800–1200 lines of
  metaprogramming.

### What NOT to do

A typeclass-based inference engine (`TagInfer` class).  Rejected in
Phase 1 design doc §1.1 for performance reasons; the rejection still
applies.  Instance-synthesis over a growing tag lattice is a known
Lean perf trap.

### Trigger conditions to revisit

- 15th fundamental tag lands (lattice complexity).
- A real workload accumulates 5+ chained tag applications and the
  manual compositions become a meaningful fraction of proof length.
- User requests: "can the framework just figure this out?"

---

## E-series execution order (2026-04-22)

Priority-ordered, batch small items:

1. **E2** (`c_nonneg`) — small cleanup, done first.
2. **E5** (tag generators + attributes) — sets up lattice.
3. **E7** (compensated bundle) — closes bundle-bridge suite.
4. **E4** (`magBound` abbrev) — medium, retrofits T-M4.
5. **E8** (`HasAbsBoundVec`) — trivial convenience.
6. **E1** (pattern guide) — draws on E5 lattice.
7. **E6** (`IsBoundedRange` audit) — observational; informs future
   refactor decisions.
8. **E9** (`[FPAxioms R]` bundle) — cross-cutting, last to avoid
   constant rebase.
9. **E3** (`letI` → `def`) — deferred.
