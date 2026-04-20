# Flean Tag Framework — Focused Session: Phase 2 (Tag-Specialized Tightening)

## What you're doing

Phase 1 of the tag framework shipped: tag struct + propagation
theorems + bridges + interval algebra + consumer wrappers.  It's all
infrastructure — the framework can thread tags through a chain, but
no downstream end-to-end theorem has been *tightened* by a tag yet.

Phase 2's job is to **demonstrate actual tightening**: take a
pre-existing end-to-end theorem that carries a loose term (a
`subnormalConst` tail, an `η²` term, an outer `γₙ` factor), add a
tag that rules out the regime producing that term, and prove a
tighter companion theorem.  This is the claim the framework was
built to deliver on.

## Context you should absorb first

Read in order, each until you understand:

1. `.claude/notes/tag-framework-phase1-design.md` — the full design
   doc, including §3.5 measurement and the top-of-doc "shipped"
   summary.  Skim §1 (design decisions) and §3.4 (propagation)
   carefully, skim the rest.
2. `Flean/Tags/FpInterval.lean` — the interval algebra (`⊞`, `⊠`,
   `FpInterval.fpFMA`) and `subnormalConst`/`maxMag` helpers.
3. `Flean/Tags/BoundedRange.lean` — the primary parametric tag, now
   takes `FpInterval R`.  Note `IsBoundedRange.toVal_abs_le` as the
   general magnitude corollary.
4. `Flean/Tags/BoundedRangePropagate.lean` — six propagation
   theorems (normal-range + unified for Add/Mul/FMA) plus three demo
   chains.  Study one thoroughly (e.g. `fpAdd_unified`); the others
   are variations on the same skeleton.
5. `Flean/Rounding/RoundPreserves.lean` — the meta-lemma kernel.
   `round_preserves_nonneg`, `round_preserves_abs_bound_normal`,
   `round_preserves_abs_error_normal`, `round_preserves_abs_error_unified`.
6. `Flean/Tags/Bridges/ToIsNormalRange.lean` — both finished bridges:
   `exp_isNormalRange` and `quot_isNormalRange` (generic in `εsum ≤ 1/4`).
7. `Flean/Tags/AbsBound.lean` + `Flean/Tags/Nonneg.lean` — greenfield
   and retrofitted pilots, both ~9-line preservation proofs per op.

## Phase 1 accomplishments (for reference)

Everything below is landed, sorry-free, and in `master`.  Full Flean
build passes 2800+ jobs.

- **Infrastructure**: `fp{Add,Mul,FMA}Finite_round_witness` in
  `Flean/Operations/FpFiniteRound.lean`; meta-lemmas in
  `RoundPreserves.lean`; `FpInterval R` + algebra in
  `Flean/Tags/FpInterval.lean`.
- **Tags**: `IsBoundedRange`, `HasAbsBound`, `IsNonneg`, `IsSimplex`,
  `IsNormal`, `IsSterbenz`.  All parametric over `R`.
- **Propagation**: `IsBoundedRange.fp{Add,Mul,FMA}{,_unified}` (six
  theorems).
- **Bridges**: `IsBoundedRange.exp_isNormalRange`,
  `IsBoundedRange.quot_isNormalRange` (generic in `εsum ≤ 1/4`).
- **Consumers**: `fpSoftmax_bound_of_bounded`,
  `fpSoftmax_bound_of_separated`.
- **Tactics**: `η[R]` / `ε[R]` explicit-type notation in
  `FloatFormat.lean`; `close_interval_via_{abs,slack}` macros in
  `BoundedRangePropagate.lean`.

## What Phase 2 SHOULD deliver

Pick **exactly one** concrete tightening target, prove it
sorry-free, document the before/after comparison.  Candidates
ranked by estimated ROI:

### Candidate A: Softmax `subnormalConst` tail elimination (recommended)

`Flean/Operations/Softmax.lean` has two end-to-end softmax error
theorems:
- `fpSoftmaxOf_error_bound` — **clean form**, no `subnormalConst`
  tail, but requires every exp output in normal range
  (`h_exp_nr : ∀ i, isNormalRange (Real.exp ((xs i).toVal : ℝ))`).
- `fpSoftmaxOf_error_bound_subnormal` — **subnormal-tolerant**,
  drops `h_exp_nr` but pays a `subnormalSoftmaxAbs · sc` tail in the
  bound.

**Phase 2 target**: a tag-specialized subnormal softmax theorem
that partitions inputs into "large enough to stay normal" vs "maybe
subnormal", and only pays the `sc` tail on the subnormal subset.
In the all-normal case, the tail vanishes — matching
`fpSoftmaxOf_error_bound`'s clean form via a tag certificate
instead of a manual `h_exp_nr`.

Natural tag: `IsNormal v` (already defined in
`Flean/Tags/Normal.lean`) applied elementwise to a partition of
the input vector.

**Scope estimate**: 300–500 lines, mostly real-analysis
bookkeeping around the partition.  High-value: it's the design
doc's own named example of what Phase 2 is for (§6 parenthetical).

### Candidate B: LayerNorm as a new tagged ML primitive

Define FP-rounded LayerNorm (`mean`, `variance`, normalize via
`(x − mean) / √(variance + eps) * γ + β`), prove a per-component
error bound using the tag framework throughout.  Exercises:

- Sum + divide (for mean): `FpSum.FpSumBound` adapters + `fpDiv`.
- Sum of squares + subtract + divide + sqrt (for variance): threads
  through `fpMul`, `fpSub`, `fpSqrt`, `fpDiv`.
- Tag inputs with `IsBoundedRange` to get normal-range preconditions
  for free via the bridges.

**Scope estimate**: 500–800 lines.  Higher value long-term (ML
users care), but greenfield — so more up-front design work.

### Candidate C: Horner with `IsBoundedRange` coefficient tag

`Flean/Operations/Horner.lean` has polynomial evaluation error
bounds using the `AffineFold` framework.  If all coefficients are
tagged with `IsBoundedRange`, the `γₙ`-flavored error bound could
tighten to a cleaner form (coefficient magnitudes absorbed into
the bound, not left as a free `Σ |coeffs|·|x|^k`).

**Scope estimate**: 200–400 lines.  Narrow-but-clean target;
good if you want a tight scoped win.

### Candidate D: Kahan/Neumaier with `IsNonneg` input tag

Kahan summation's error bound has a `2η + nη²` coefficient.  If
inputs are all tagged `IsNonneg`, no cancellation can happen and
the bound might sharpen (e.g. to `nη` — first-order only).

**Scope estimate**: 200–300 lines.  Smaller but the payoff depends
on whether Kahan's analysis actually admits this tightening
(verify first before committing).

## Picking a candidate

Candidate A is the canonical Phase 2 deliverable (explicitly named
in the design doc).  Candidates B–D are valid alternatives if
A's scope feels too large for the session.

If you pick A, the natural arc is:

1. Read `fpSoftmaxOf_error_bound_subnormal` and identify where
   `subnormalConst` enters the bound.
2. Define a "normal-range partition" tag: a predicate saying
   `{i | Real.exp (xs i) < 2^min_exp}` is a known (possibly empty)
   subset `S`.
3. Prove a core lemma `fpSoftmax_apply_core_bound` variant that
   absorbs the `sc` tail only for `i ∈ S` and gives the clean bound
   for `i ∉ S`.
4. Deliver a bundled theorem `fpSoftmaxOf_error_bound_partitioned`
   that takes the partition as a hypothesis and produces
   per-component bounds.
5. Corollary: the all-normal case (`S = ∅`) recovers
   `fpSoftmaxOf_error_bound` exactly.

## Hard constraints

- **Sorry-free**: ~47k-line library invariant.  If stuck, narrow
  scope (e.g. "normal-range-only" version) or add a hypothesis to
  the signature.  Do NOT leave a `sorry`.
- `lake build Flean` must pass at session end (2800+ jobs).
- `set_option autoImplicit false` in new files.
- Update `Flean/Tags.lean` aggregator if you add a new file.
- Commit with a descriptive message (see `git log --oneline -10`
  for project style).
- Keep scope bounded — ~500 lines total is plenty; if it's ballooning,
  narrow the target.  Prefer finishing a small thing over sketching
  a big thing.
- Don't refactor existing Phase 1 files unless the new work
  genuinely requires it.  The infrastructure is stable.
- Update `.claude/notes/tag-framework-phase1-design.md` §6 noting
  which Phase 2 target landed (move it from "out of scope" to a
  new "Phase 2 done" section, or start
  `.claude/notes/tag-framework-phase2-design.md` if this grows).

## Known gotchas (from Phase 1 sessions)

- `η` notation defaults its type parameter inconsistently in tactic
  blocks.  Use `η[R]` / `η[ℝ]` from `FloatFormat.lean` where ambient
  elaboration is ambiguous.  Also: can't use `η` as a bound-variable
  name in theorem signatures (parser error) — pick a different letter.
- `FiniteFp.toVal_neg_eq_neg` needs explicit `(R := R)` in `linarith`
  hint lists.
- `FpInterval` ops (`⊞`, `⊠`, `fpFMA`) carry rounding-slack semantics
  — they're NOT ordinary interval arithmetic.  Non-associative, like
  FP itself.
- `abs_add_le`, not `abs_add`; often needs `convert ... using 2; ring`
  to match an applied form.
- `isNormalRange x` requires `0 < x`.  For sign-agnostic bounds on
  `|x|`, use the `2^min_exp ≤ |x|` formulation or dispatch via
  `RModeConj`.
- `close_interval_via_{abs,slack}` macros take keyword args
  (`rw:hg_eq from:h_abs unfolding FpInterval.fpMul`) — not space-
  separated positional (parser reads consecutive `term`s as
  application).
- `nlinarith` needs `sq_nonneg` / `mul_nonneg` hints for quadratic
  polynomial goals.

## Success criteria

- Chosen target fully proven sorry-free.
- `lake build Flean` passes.
- LOC ≤ ~500 lines (Candidate A target) or ≤ ~800 (Candidate B).
- Before/after comparison explicit in the commit message: what term
  of the old bound got dematerialized and under what tag.
- Corollary: the empty-tag case (or trivial-tag case) recovers the
  pre-existing bound exactly, validating the tightening is strict
  (not just a restatement).
- Design doc updated: mark Phase 2 target done.

## How to report back

At session end, summarize:
- Which candidate you chose and why.
- What tag condition dematerialized what term.
- Whether scope got narrowed, and what a fuller version would need.
- Any new meta-lemma added to `RoundPreserves.lean` (or other
  infrastructure changes).
- LOC of the proof file and any modified files.
- Any commit-or-two reference hash.
