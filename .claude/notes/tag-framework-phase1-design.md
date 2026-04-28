# Tag Framework — Phase 1 Design

**Status**: **Phase 1 COMPLETE** (2026-04-20).  Every §3 item landed
sorry-free, library-green, committed to `master`.  This doc now serves
as record-of-decisions for Phase 2 planning.

**Summary of what shipped**:
- §3.1: `round_preserves_nonneg` meta-lemma.
- §3.2: unified `fp{Add,Mul,FMA}Finite_round_witness` helpers.
- §3.3: `Flean/Tags/Bridges/` reorganization + `exp_isNormalRange` +
  `quot_isNormalRange` (generic in `εsum ≤ 1/4`).
- §3.4: six `IsBoundedRange.fp{Add,Mul,FMA}{,_unified}` propagation
  theorems, expressed via a new `FpInterval` interval-algebra layer
  with scoped unicode notation (`⊞`/`⊠`).  Three demo chains (3-op
  normal-range, 3-op unified, 2-FMA unified).
- §3.5: retrofit measurement on `Nonneg.lean` — 72% proof-body
  reduction, 100% local-helper elimination.  (Total-file target of
  30% was docstring-dominated; see §3.5 for the revised metric.)

**Purpose (original)**: forcing function. Crystallize what the framework should be
before writing framework code. If this doc is hard to write, it means
we don't know enough; go back to pilots. If it writes cleanly, we've
earned the right to implement.

**Audience**: reviewer (MinusGix) + future-me.

---

## 0. What Phase 0 established

Five pilots in `Flean/Tags/`, all sorry-free, all wired into `Flean.lean`:

| File | Tag | Preservation | Tightening / Threading |
|---|---|---|---|
| `Simplex.lean` | `IsSimplex ws` | permutation | `max|xᵢ|` RHS shape (structural isolation, not magnitude) |
| `Normal.lean` | `IsNormal v` | add-nonneg | drops `+ subnormalConst` in `ulp_half_le` |
| `Sterbenz.lean` | `IsSterbenz a b` | negation | exact subtraction (error = 0) |
| `Nonneg.lean` | `IsNonneg x` | fpMul + fpAdd | cross-op composition demo |
| `SoftmaxBounded.lean` | `IsBoundedRange lo hi xs` | (none yet) | bridge to existing `h_exp_nr` hypothesis of `fpSoftmaxOf_error_bound` |

Nine concrete findings across the pilots (pilot-file assessments have full text):

1. **"Tag-specialized bounds are tighter" is misleading as a blanket claim.**
   Three distinct shapes: structural isolation, additive-tail elimination,
   multiplicative-tail elimination (exactness). Only the latter two tighten
   magnitude; structural isolation rearranges.

2. **Degeneracy preconditions can be absorbed into tags.** `IsSimplex.pos`
   derives `0 < n`. Structural tags should eat preconditions they imply.

3. **Preservation lemmas are boilerplate** for tags-through-rounding.
   Every `IsNonneg` preservation reduces to "round preserves nonneg via
   `RModeMono` + `RModeZero`." One meta-lemma per tag would collapse the
   family.

4. **Finiteness is orthogonal to the tag.** Every pilot's preservation
   takes a separate `fp_op x = Fp.finite f` hypothesis. Don't bundle.

5. **Zero-case handling is per-op ad-hoc.** `fpAddFinite` has a helper
   (`fpAddFinite_zero_left_val`); `fpMulFinite` needed inline `roundIntSigM`
   unfolding. A uniform `fp*Finite_toVal` helper would simplify.

6. **Bridges from input tags to existing hypotheses are cheap.** The
   `IsBoundedRange → isNormalRange(exp ·)` bridge is ~15 lines of real
   analysis and discharges a real softmax precondition automatically.

7. **Not all preconditions factor cleanly.** `h_quot_nr` depends on a
   computed quantity (`denom`). Phase 1 must accept that some hypotheses
   remain manual — don't force everything through tags.

8. **Tag representation can be plain structures.** All 5 pilots used
   structures. No typeclass inference needed yet.

9. **Parametric tag composition is untested.** `IsBoundedRange lo hi`
   carries parameters; nothing in Phase 0 propagated them through an op
   (a test case is queued as Phase 0.5 work).

---

## 1. Design decisions

Each decision is paired with rationale and the finding(s) it addresses.

### 1.1 Tags are structures, not typeclasses

**Decision**: `structure` remains the canonical representation. No
`Preserves P Q f` typeclass in Phase 1.

**Rationale**:
- All 5 pilots use structures and read cleanly. Typeclass inference
  wasn't needed for any of them.
- User flagged typeclass-inference perf concerns from a prior ML project
  (`tag-framework-plan.md` §Concern). Avoiding typeclass chain-composition
  eliminates that risk entirely for Phase 1.
- Chaining across 3+ ops hasn't appeared in pilots. If it becomes common,
  add a typeclass ON TOP without replacing structures.

**Addresses**: finding 8.

**What this gives up**: no automatic tag propagation through function
composition via `infer_instance`. Users call preservation lemmas
explicitly by name. Observation: this matched what we actually wanted
in all 5 pilots.

### 1.2 Preservation-lemma meta-factoring (by tag, not by op)

**Decision**: for each tag with a "round preserves P" semantics, write
ONE meta-lemma taking a rounding-output witness. Per-op preservations
become trivial instantiations.

**Example** (to be built):

```lean
-- In Flean/Rounding/RoundPreserves.lean
theorem round_preserves_nonneg {R} [...] [RMode R] [RModeMono R] [RModeZero R]
    {x : R} (hx : 0 ≤ x) {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    0 ≤ (f.toVal : R)
```

Per-op preservations (currently ~20 lines each) reduce to ~5 lines:

```lean
theorem IsNonneg.fpAdd [...] (hx : IsNonneg x) (hy : IsNonneg y)
    (hf : fpAddFinite x y = Fp.finite f) : IsNonneg f := ⟨by
  have hsum_nn := add_nonneg hx.toVal_nonneg hy.toVal_nonneg
  exact round_preserves_nonneg hsum_nn (fpAddFinite_toVal_round.mp hf)⟩
```

**Rationale**: addresses finding 3 directly. Expected savings: 2n - 1
lemmas for n ops, each becoming a 5-line application of the meta-lemma.

**Open question**: which tags factor this way?
- `IsNonneg`: yes (uses `RModeMono` + `RModeZero`).
- `IsBoundedRange`: unclear — may need more than just `RModeMono`; the
  output interval grows with each op's rounding slack.
- `IsSimplex`: n/a; preservation isn't through a rounding op.

**Addresses**: findings 3, 5 (via the uniform toVal helpers below).

### 1.3 Bridges organized by TARGET hypothesis

**Decision**: bridges live in `Flean/Tags/Bridges/ToIsNormalRange.lean`
(etc.), indexed by the hypothesis they discharge, not by the input tag.

**Rationale**: a user hitting `h_exp_nr : isNormalRange (...)` on a softmax
call site wants to ask "which tags can give me this?" Indexing by target
makes that question answerable via file navigation. Indexing by source
forces the user to pre-guess the answer.

**Example structure**:
```
Flean/Tags/Bridges/
  ToIsNormalRange.lean   -- contains exp_isNormalRange_of_bounded, etc.
  ToIsSimplex.lean       -- empty to start
  ToIsFinite.lean        -- contains fpAddFinite_of_bounded, etc.
```

**Alternative rejected**: flat `Flean/Tags/Bridges.lean`. Would grow
unbounded; target-keyed navigation loses.

**Alternative rejected**: organize by source tag (`IsBoundedRange.lean`
carries all bridges FROM IsBoundedRange). Forces users to already know
the answer.

**Addresses**: finding 6, enables the "discoverable bridge library"
story.

**Open**: `@[tag_bridge]` attribute for programmatic discovery? Defer
unless Phase 2 shows it matters.

### 1.4 Parametric tags propagate via per-op theorem libraries

**Decision**: for each parametric tag, Phase 1 specifies the *shape* of
the propagation lemmas; Phase 2 (or a dedicated focused session) works
out the exact rounding-slack formulas.

**Scope discipline**: this design doc is about *architecture*, not *new
regimes*. The framework's job is to make the per-op propagation proofs
easy to write when the user (or a follow-up session) sits down to do
them. Deriving the correct output interval for `IsBoundedRange.fpAdd`
is real FP-error-analysis work that belongs in its own session, not
bundled with framework-building.

**What Phase 1 DOES deliver**:
- The TAG (struct + R-parameterized — see §1.8).
- The *signature* of per-op propagation lemmas (expected input tags,
  expected output tag shape).
- Stubs / `sorry`-placeholder versions if useful to validate the
  framework shape before the proofs land.
- Integration with the bridges and meta-lemma machinery.

**Canonical signatures** (post-refactor): the existential form was
retired once the focused session pinned down the output-interval
formulas.  Those formulas now live as interval-algebra operations on
a dedicated `FpInterval R := { lo : R; hi : R }` structure
(`Flean/Tags/FpInterval.lean`), and `IsBoundedRange` takes an
`FpInterval` directly:

```lean
-- Flean/Tags/BoundedRange.lean
structure IsBoundedRange {n : ℕ} (I : FpInterval R) (xs : Fin n → FiniteFp) : Prop where
  lower : ∀ i, I.lo ≤ ((xs i).toVal : R)
  upper : ∀ i, ((xs i).toVal : R) ≤ I.hi

-- Flean/Tags/BoundedRangePropagate.lean
theorem IsBoundedRange.fpAdd_unified ... :
    IsBoundedRange (A ⊞ B) (fun (_ : Fin 1) => f)
theorem IsBoundedRange.fpMul_unified ... :
    IsBoundedRange (A ⊠ B) (fun (_ : Fin 1) => f)
theorem IsBoundedRange.fpFMA_unified ... :
    IsBoundedRange (FpInterval.fpFMA A B C) (fun (_ : Fin 1) => f)
```

where `⊞` / `⊠` are scoped unicode notation for `FpInterval.fpAdd` /
`FpInterval.fpMul` (subnormal-tolerant).  Normal-range variants use
`fpAddN` / `fpMulN` / `fpFMAN` explicitly.

Chained propagation reads as algebra: `(A ⊠ B) ⊞ (C ⊠ D)` in the
output type of the 3-op demo, `FpInterval.fpFMA A B (FpInterval.fpFMA C D E)`
for the 2-FMA chain.  No `obtain` dance; tags chain via function
composition.

**Outward-widening invariants** (`lo' ≤ A.lo + B.lo`, etc.) are no
longer part of the theorem conclusion — they fall out of the
`FpInterval.fpAdd` definition and are available as separate lemmas
(`FpInterval.fpAdd_lo_le` / `fpAdd_hi_ge`) when callers need them.

**Magnitude corollary**: `IsBoundedRange.toVal_abs_le` in
`BoundedRange.lean` gives `|((xs i).toVal : R)| ≤ I.maxMag` for any
tagged vector.  Per-op magnitude bounds fall out by applying this to
the output interval of the propagation lemma.

**Rationale**: the only alternative — interval arithmetic as a first-class
abstraction — is over-engineered for the FP-error domain. Pilots work
directly with concrete bounds; the framework preserves that style.

**Addresses**: finding 9 (architecturally; proofs come later).

### 1.5 Finiteness stays explicit

**Decision**: tags never bundle `Fp.finite f` witnesses. Preservation
lemmas always take finiteness as a separate hypothesis.

**Rationale**: directly from finding 4. Semantic structure (tags) and
numerical well-definedness (finiteness) are orthogonal concerns.

**Consequence**: helper lemmas like `fpAddFinite_of_range_bounded` (which
derives finiteness from an input range tag) live in the Bridges directory,
not bundled into tags.

### 1.6 Zero-case handler (new infrastructure)

**Decision**: add two helpers to `Flean/Operations/Add.lean` and
`Flean/Operations/Mul.lean` that cover both zero and nonzero result
cases uniformly:

```lean
theorem fpAddFinite_toVal {x y f : FiniteFp}
    (hf : fpAddFinite x y = Fp.finite f) :
    (f.toVal : R) = (RMode.round ((x.toVal : R) + y.toVal)).toVal?... -- shape TBD
```

Shape needs refinement — the payoff is: tag preservations no longer
case-split on zero vs nonzero, they just cite the helper.

**Rationale**: finding 5. Reusable infrastructure, not tag-specific.

**Open**: right signature is unclear. Options:
- Return `(f.toVal : R) = roundedValue` where rounded Value is defined
  via round-with-default-for-zero.
- Return a disjunction: `(nonzero ∧ fpAddFinite = ○...) ∨ (zero ∧ f.m = 0)`.
- Return a single equation using a `rounded` abbreviation that covers both.

Phase 1 implementation starts here; prototype the signature first.

### 1.7 Tag weakening / meets / joins: Phase 2

**Decision**: defer. No instance-based tag-subtype reasoning in Phase 1.

**Rationale**: no pilot needed it. Adding framework for unused abstractions
is the opposite of what this design doc is meant to prevent.

**Concrete Phase 2 trigger**: when two pilots each have 3+ tags and we
observe users manually weakening `IsSimplex → IsNonneg` etc., that's the
signal to add.

### 1.8 All tags parameterize over `R` (no ℝ hardcoding)

**Decision**: every tag carries `{R : Type*}` as a type parameter.
`IsBoundedRange` (currently ℝ-hardcoded) gets refactored to
`IsBoundedRange (R := R) lo hi xs` as part of the Phase 1 retrofit.

**Rationale**: matches the rest of the Flean codebase (`FpSumBound`,
`FpDotProductBound`, etc. are all R-parametric). Also:
- **Generality** — tags work in ℚ, ℝ, etc. without duplication.
- **Computability / constructivity** — ℚ computations stay computable;
  ℝ results follow the codebase's existing `(R := R)` discipline.
- **Consistency** — tag-to-hypothesis bridges can produce hypotheses
  in whichever R the caller is working in.

**Caveat**: some bridges will need real-analysis lemmas that are
ℝ-specific (e.g., `Real.exp`). In those cases the bridge is stated at
R = ℝ but the tag remains R-parametric; an R-generic bridge exists
for bounds that don't involve transcendentals.

**Retrofit**: `IsBoundedRange` in `SoftmaxBounded.lean` gets rewritten
to carry `R`. The `exp_isNormalRange` bridge stays ℝ-specific.

**Addresses**: finding that was previously §5.4 (open question),
now resolved.

### 1.9 Degeneracy absorption into tags

**Decision**: adopt ad-hoc + struct-dot-notation approach (Option A+C
below). Revisit if we see multiple tags discharging the same precondition.

Finding 2 noted that `IsSimplex.pos : IsSimplex ws → 0 < n` absorbs the
nonempty-vector precondition directly into the tag. Should this be a
general framework pattern?

**Options considered**:

- **A. Ad-hoc lemmas per tag.** What `IsSimplex.pos` currently is. Each
  tag gets its own `Foo.implies_Bar` lemmas as they're needed.
  - Pros: simple; zero infrastructure cost; discoverable via file
    navigation of the tag's own file.
  - Cons: user hitting `0 < n` elsewhere can't ask "which tags give me
    this?"; potential repetition if multiple tags imply the same
    precondition.

- **B. Target-indexed derivation library** (parallel to §1.3 bridges).
  Organize "tag → precondition" lemmas by target, like bridges.
  `Flean/Tags/Derived/Pos.lean` would hold all "→ `0 < n`" style lemmas.
  - Pros: discoverable by target; parallel structure to bridges.
  - Cons: subtle distinction from bridges — bridges go "tag on X →
    hypothesis on external value," derivations go "tag on X → extra
    property of X." Framework grows twin directories with overlapping
    intent.

- **C. Struct dot-notation API.** Absorb as methods on the tag struct.
  `IsSimplex.pos` is already this.
  - Pros: idiomatic Lean; dot-notation discovery; each tag owns its API.
  - Cons: relies on user knowing which tag to look at.

- **D. Subsume into bridges.** Treat `IsSimplex ws → 0 < n` as a special
  case of "tag → hypothesis," filed alongside other bridges.
  - Pros: unified framework; single discharge mechanism.
  - Cons: conflates meta-properties (size, structure) with
    value-hypotheses; bridges directory grows heterogeneous.

**Chosen**: **A + C** in combination. Tag-method dot-notation
(`IsSimplex.pos`) is the natural primary API; ad-hoc lemmas for anything
that doesn't fit as a struct method. Don't build Option B or D
infrastructure until we see the specific pain point they'd address —
which requires multiple tags implying the same precondition, which
hasn't happened yet.

**Revisit trigger**: first time two distinct tags discharge the same
precondition, add Option B directory.

**Addresses**: finding 2.

---

## 2. Non-goals (explicit)

Things this framework deliberately does NOT do:

- **No typeclass inference for `Preserves P Q f`.** Rationale §1.1.
  Revisit if chain composition becomes common.
- **No automatic tag derivation from external hypotheses.** Bridges are
  explicit theorem applications. The framework doesn't scan context.
- **No computed-quantity tags as preconditions.** Things like `h_quot_nr`
  (quotient-in-normal-range, depends on a computed denom) stay manual.
  Framework supports tagging them once computed but doesn't derive them.
- **No interval-arithmetic abstraction layer.** Parametric tags carry
  bounds directly; per-op propagation lemmas compute output bounds.
  Interval arithmetic as a separate abstraction is out of scope.
- **No tag discovery / search tactic.** Users find bridges via file
  navigation and doc comments. `@[tag_bridge]` attribute deferred to
  Phase 2.

---

## 3. Proposed Phase 1 implementation sequence

Ordered by dependencies:

### 3.1 `Flean/Rounding/RoundPreserves.lean` (small, ~50 lines)

- Promote `round_nonneg_of_nonneg` from `Flean/Tags/Nonneg.lean`.
- Rename to `round_preserves_nonneg`.
- Add companion `round_preserves_pos` if needed (strict version).
- Relies only on `RModeMono` + `RModeZero`.

**Success criterion**: Nonneg pilot refactors to use this, saving ~10
lines per preservation lemma.

### 3.2 `Flean/Operations/FpFiniteRound.lean` zero-case helpers — DONE

Prototyped in `Flean/Operations/FpFiniteRound.lean` (124 lines, both
`fpAddFinite_round_witness` and `fpMulFinite_round_witness`). Signature:

```lean
theorem fpAddFinite_round_witness [RModeZero R] ...
    (hf : fpAddFinite x y = Fp.finite f) :
    ∃ g : FiniteFp,
      (RMode.round ((x.toVal : R) + y.toVal) : Fp) = Fp.finite g ∧
      (g.toVal : R) = f.toVal
```

The existential wraps the signed-zero ambiguity: `g` may differ from
`f` only in sign bit, but `g.toVal = f.toVal` in `R`. Consumer
preservations no longer case-split.

**Measurement**: retrofitting `Nonneg.lean`:
- `Nonneg.lean`: 175 → 149 → 132 lines (−43 cumulative, ~25%).
- Per-preservation proof body: ~18 → ~7 lines each.
- Local `roundIntSigM_mag_zero_m` helper (9 lines) eliminated entirely.
- `RModeIdem` typeclass requirement dropped (zero-case no longer
  needs idempotence — `RModeZero` suffices via the helper).

Infrastructure cost: 124 lines in new file, amortized across all
future tag preservations using `fp{Add,Mul}Finite`.

**Greenfield validation (`Flean/Tags/AbsBound.lean`)**: a new
parametric tag `HasAbsBound c` built on the same infrastructure.
Preservation proofs are ~9 lines each (vs ~18 for the pre-infrastructure
style). The 2-line excess over `IsNonneg`'s ~7 is genuine parametric-tag
arithmetic (`|x+y| ≤ c₁ + c₂`), not infrastructure overhead — the
case-split / round-witness / meta-lemma plumbing is ~0 lines per
preservation, confirming the design claim.

Meta-lemma addition (`round_preserves_abs_bound_normal`): ~20 lines
of kernel, reused by the original Phase 1 pilots
`HasAbsBound.fpAdd_nonneg_normal` / `HasAbsBound.fpMul_nonneg_normal`
(removed during T-S4 cleanup, 2026-04-27, after T-M1 shipped the
sign-agnostic propagation suite in
`Flean/Tags/AbsBoundPropagate.lean`).  Pattern validated: one
meta-lemma per tag, N=2 ops supported from it.

### 3.3 `Flean/Tags/Bridges/` directory — DONE

Split implemented. Current layout:
- `Flean/Tags/BoundedRange.lean` (~41 lines): `IsBoundedRange` tag
  definition only. Minimal imports.
- `Flean/Tags/Bridges/ToIsNormalRange.lean` (~64 lines):
  `IsBoundedRange.exp_isNormalRange` bridge. Module docstring calls
  out the "organize by target hypothesis" principle and flags
  `quot_isNormalRange` as the next addition (signature locked below).
- `Flean/Tags/SoftmaxBounded.lean` (~73 lines): consumer wrapper
  `fpSoftmax_bound_of_bounded` only.

**Success criterion met**: a user hitting `h_exp_nr : isNormalRange (...)`
can navigate to `Flean/Tags/Bridges/ToIsNormalRange.lean` and find
every discharging bridge (currently one) in one place; future bridges
to `isNormalRange` targets (including the locked `quot_isNormalRange`)
slot in alongside without hunting across files.

The reorganization proves the framework's organizational principle is
implementable, not just paper-plan.

**`IsBoundedRange.quot_isNormalRange` — DONE** (landed in
`Flean/Tags/Bridges/ToIsNormalRange.lean`).  Final signature (after
Phase 1 εsum generalization):

```lean
theorem IsBoundedRange.quot_isNormalRange
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]
    {n : ℕ} (hn : 0 < n) {I : FpInterval ℝ} {εsum : ℝ}
    {xs : Fin n → FiniteFp} {exps : Fin n → FiniteFp} {denom : FiniteFp}
    (hxs : IsBoundedRange (R := ℝ) I xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ I.lo)
    (hhi : I.hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (h_εsum_nn : 0 ≤ εsum) (h_εsum_le : εsum ≤ 1/4)
    (hd_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                εsum * ∑ j, |((exps j).toVal : ℝ)|)
    (hd_pos : 0 < (denom.toVal : ℝ))
    (h_separation : 4 * (n : ℝ) * (2 : ℝ) ^ (FloatFormat.min_exp : ℤ) ≤
                    Real.exp (I.lo - I.hi))
    (i : Fin n) :
    isNormalRange (((exps i).toVal : ℝ) / denom.toVal)
```

**Separation constant**: `4·n·2^min_exp` (tightened from the
originally-sketched `2·n·2^min_exp`).  The lower-bound chain needs
`4(1−η) ≥ (1+εsum)(1+η)`, which holds for both `η, εsum ≤ 1/4` (η's
bound is universal via `FloatFormat.valid_prec`; εsum's is explicit).
The original constant 2 was tight only for `prec ≥ 3` and `εsum = η`;
4 is the smallest clean integer that works universally.  Tighter
formats or tighter `εsum` admit smaller constants.

**εsum generalization**: the single-fp-add-equivalent (`εsum = η`) case
was the original focus, but summation-based denoms (Kahan's
`εsum = 2η + nη²`, Neumaier, etc.) plug in directly as long as their
`εsum` stays `≤ 1/4`.  This covers every practical summation at any
reasonable `n·η` budget — e.g., Kahan at `n·η ≤ 1/4` gives
`εsum ≤ 2η + η/4 ≤ 1/4 + ...` (tight at small `η`).

**Consumer wrapper**: `fpSoftmax_bound_of_separated` in
`Flean/Tags/SoftmaxBounded.lean` is the lighter companion to
`fpSoftmax_bound_of_bounded` — discharges both `h_exp_nr` and
`h_quot_nr` automatically, taking `εsum` as a parameter so any
summation-based denom works.  Callers supply:
`IsBoundedRange` + log-bounds + separation + denom closeness +
`εsum ≤ 1/4` + the usual div/finiteness hypotheses.

The `h_separation` hypothesis says "the spread of xs is not so extreme
that the smallest softmax entry underflows."

### 3.4 Parametric propagation library (per §1.4) — PARTIAL DONE

Implemented in `Flean/Tags/BoundedRangePropagate.lean` (~190 lines,
sorry-free).

- `IsBoundedRange.fpAdd` / `fpAdd_unified` — **done**.  Output
  intervals `A.fpAddN B` / `A ⊞ B` respectively.
- `IsBoundedRange.fpMul` / `fpMul_unified` — **done**.  Output
  intervals `A.fpMulN B` / `A ⊠ B` respectively.  Symmetric-around-0.
- `IsBoundedRange.fpFMA` / `fpFMA_unified` — **done**.  Output
  intervals `A.fpFMAN B C` / `FpInterval.fpFMA A B C` respectively.
  Same symmetric-around-0 form as `fpMul` (single rounding step over
  `a·b + c` whose directional structure is lost via the product).
  Supporting infrastructure: `fpFMAFinite_round_witness` in
  `Flean/Operations/FpFiniteRound.lean`.

All six live in `Flean/Tags/BoundedRangePropagate.lean`; output
formulas are in `FpInterval.{fpAddN, fpAdd, fpMulN, fpMul, fpFMAN, fpFMA}`
in `Flean/Tags/FpInterval.lean`.

Both lemmas take an additional hypothesis
`(2 : R)^min_exp ≤ |exact result|` — the sign-agnostic normal-range
lower bound. The upper bound of the normal range is derived inside
the meta-lemma from finiteness of the rounded result. Subnormal and
zero inputs are not covered (punted, per the session prompt's
"scope drift" guidance).

Infrastructure added: `round_preserves_abs_error_normal` in
`Flean/Rounding/RoundPreserves.lean` (~55 lines) — sign-agnostic
additive error bound via `RModeNearest` + `RModeConj`. Companion to
the magnitude-only `round_preserves_abs_bound_normal`.

**Success criterion**: a 3-op chain (e.g., `fpAdd (fpMul x y) bias`) can
thread `IsBoundedRange` through via three explicit calls, and the proof
reads as interval arithmetic. — **MET**

`IsBoundedRange.demo_mul_mul_add` in `BoundedRangePropagate.lean`
threads the tag through `r = fpAdd (fpMul x y) (fpMul z w)` via three
explicit propagation calls.  Proof body: three `obtain`s on the
propagation lemmas + one `exact`.  Reads as interval arithmetic.

**UX findings from the demo**:

- **One normal-range hypothesis per op — ADDRESSED by unified
  variants.**  The first demo needed three `(2:R)^min_exp ≤ |·|`
  hypotheses.  `IsBoundedRange.fp{Add,Mul}_unified` drop these in
  exchange for an additive `sc := 2^(min_exp - prec)` tail in the
  slack.  A side-by-side `demo_mul_mul_add_unified` in the file has
  no normal-range hypotheses at all.  Infrastructure: new meta-lemma
  `round_preserves_abs_error_unified` in `RoundPreserves.lean`
  (subnormal-tolerant sign-agnostic `|f.toVal - x| ≤ η·|x| + sc`,
  handling `x = 0` / subnormal / normal uniformly via `RModeZero` +
  `RModeConj` + `RModeNearest`).  Helper: R-generic
  `ulp_half_le_unified_gen` (generalizes `Softmax.ulp_half_le_unified`
  from ℝ to any `Field + LinearOrder + FloorRing`).

- **Existential unpacking is manual but tolerable.**  Each
  propagation lemma returns `∃ lo' hi', ...`; the user `obtain`s to
  thread the downstream tag.  Scales linearly, no obvious framework
  fix warranted yet.

- **No tag-weakening step needed.**  Because `IsBoundedRange` is
  parametric over `lo`/`hi`, the downstream `fpAdd` call accepts the
  `fpMul` output intervals directly — no explicit bridge.  Confirms
  §1.7's deferral (no typeclass weakening infrastructure) was the
  right call for same-tag chains.

### 3.5 Retrofit pilots — DONE

Measurement on `Flean/Tags/Nonneg.lean`, the one pilot with a pre-retrofit
baseline (the others — `AbsBound`, `BoundedRange{,Propagate}` — were
built greenfield on the retrofitted infrastructure and don't have a
"before"):

| Scope | Before (commit `31d3485`) | After (retrofit landed) | Change |
|---|---|---|---|
| **Total file** | 175 lines | 134 lines | **−23%** |
| **Proof bodies only** (`fpAdd` + `fpMul`) | 29 lines | 8 lines | **−72%** |
| **Local helper mass** | 18 lines | 0 | **−100%** (moved to shared infra) |

**On the stated 30% total-LOC target**: not hit at the file level — 23%,
not 30% — because `Nonneg.lean`'s total is docstring-dominated (the
file is ~76% docstring / blank / structure, only 24% code).  The
retrofit trimmed the *code* aggressively (72% on proof bodies, 100%
on local helpers) but left the docstring mass untouched; the
30% file-total figure was aspirational without adjusting for that
composition.

**On "proofs more mechanical"**: met cleanly.  Each preservation is
now three lines:
```lean
obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
have hsum_nn : (0 : R) ≤ x.toVal + y.toVal := add_nonneg hx.toVal_nonneg hy.toVal_nonneg
exact ⟨hg_eq ▸ round_preserves_nonneg hsum_nn hg_round⟩
```
— purely structural, no zero-case reasoning, no op-specific unfolding.

**Infrastructure amortization**: the retrofit shifted mass into shared
infra (`FpFiniteRound.lean` ~170 lines of unified witnesses,
`RoundPreserves.lean` ~270 lines of meta-lemmas).  First preservation
pays the infrastructure cost; subsequent ones pay only the thin ~5-line
proof.  Concrete evidence of payoff downstream:
- `AbsBound.lean`: ~9-line proofs per op (two preservations).  Would
  have been ~18 lines each without the infra.
- `BoundedRangePropagate.lean`: six propagation theorems all consume
  `fp{Add,Mul,FMA}Finite_round_witness`, sparing ~15 lines of
  case-split bookkeeping per theorem — ≥90 lines saved across the
  file.

**Revised takeaway for the design doc**: the "pilot LOC reduction" as
a target metric over-weights docstring bulk.  The meaningful figure is
"per-preservation proof-body cost after infrastructure lands": that
dropped from ~18 lines to ~5 lines (~72%), which is the number to cite
when justifying the framework pattern to future readers.

---

## 4. Review criteria

This design is successful if:

- [ ] Every one of the 9 Phase 0 findings maps to a specific decision
  above (check: 1→§1.1+§1.2, 2→§1.9, 3→§1.2, 4→§1.5, 5→§1.6, 6→§1.3,
  7→§2, 8→§1.1, 9→§1.4).
- [ ] Non-goals are explicit enough that Phase 1 work cannot drift into
  framework-for-its-own-sake.
- [ ] Each sequence item in §3 has a measurable success criterion.
- [ ] The typeclass-inference perf risk is documented and avoided
  (§1.1 defers it).

---

## 5. Open questions for review

These are the genuine uncertainties in the design. Flagging them rather
than handwaving.

1. ~~**Finding 2 (degeneracy absorption) is unaddressed.**~~ — RESOLVED
   (§1.9): ad-hoc + struct dot-notation (Options A+C), revisit if
   multiple tags share a precondition.

2. **§1.6 signature is unknown.** `fpAddFinite_toVal` needs prototyping
   to find the right shape. Could be blocking for §3.2.

3. **§1.4 rounding slack formulas are non-trivial work.** Writing
   `IsBoundedRange.fpAdd` correctly requires deriving the output
   interval given input intervals + a rounding-step slack. Is there
   existing machinery in `Flean/RelativeError.lean` for this, or do we
   derive from scratch?

4. ~~**Tags that carry `R`**~~ — RESOLVED (§1.8): all tags parameterize
   over R. Retrofit `IsBoundedRange` accordingly.

5. **Discoverability of bridges** without an attribute or tactic.
   Mitigation: doc comments and the `Flean/Tags/Bridges/` layout.
   Worth evaluating after Phase 1 lands — can users actually find
   what they need?

6. ~~**Retrofitting vs. leaving pilots alone.**~~ — RESOLVED: retrofit
   for experimental evidence of LOC reduction. §3.5 stays in sequence.

---

## 6. Out of scope / deferred

Moved out of scope at Phase 1 close; deferred targets annotated with
landing status as of Phase 2.

### Phase 2: substantially landed (2026-04-20)

- ~~Tag-specialized bounds that tighten end-to-end theorems like
  Softmax's `subnormalConst`~~ — **delivered in Phase 1** via
  `fpSoftmax_bound_of_separated` (`IsBoundedRange` + log-bound +
  separation → clean softmax form with no `sc` tail).
- **LayerNorm as a new tagged ML primitive** — Phase 2 Stages 1–6
  + follow-up tag-tightening push all landed sorry-free.  Seven
  per-step rounding error bounds (mean, shift, square, variance,
  eps-add, sqrt, normalize), an end-to-end composition theorem, a
  cascaded tag-tightened stddev bound, and a fully-tagged end-to-end
  wrapper that dematerializes 4/9 preconditions under `IsNormal` tag
  pair.  `IsBoundedRange.fpSub` propagation added to close the
  framework gap.  Full scorecard + honest limits
  (5 remaining preconditions tied to LayerNorm's `(x_i − μ)` factor
  that can be arbitrarily small) in
  `.claude/notes/tag-framework-phase2-design.md` §7.

### Still out of scope

- Other ML primitives (attention, cross-attention, etc.).
- Tag export to external tools.
- Any tactic or elaborator work.
- Candidate A-partitioned (per-index `IsBoundedRange` subsetting in
  softmax).  Framework-novel but unrequested — deferred pending
  evidence that per-subset bounds are needed in practice.
- Automatic discharging of LayerNorm's normal-range preconditions
  from `IsBoundedRange` + separation (Phase 3 work).
