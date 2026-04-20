# Tag Framework — Phase 1 Design

**Status**: Post-Phase-0 design proposal. Supersedes the speculative
Phase-1 sketch in `tag-framework-plan.md` (which was written before any
pilots existed).

**Purpose**: forcing function. Crystallize what the framework should be
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

**Canonical signatures** (locked here; library stays sorry-free per
the codebase invariant — proofs land in a focused session):

```lean
-- Intended location: Flean/Tags/BoundedRange.lean (or a propagation
-- sibling file). Current home: recorded here only.

theorem IsBoundedRange.fpAdd {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [FloatFormat]
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    {lo₁ hi₁ lo₂ hi₂ : R} {x y : FiniteFp} {f : FiniteFp}
    (hx : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => y))
    (hf : fpAddFinite x y = Fp.finite f) :
    ∃ (lo' hi' : R),
      lo' ≤ lo₁ + lo₂ ∧ hi₁ + hi₂ ≤ hi' ∧
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f)

theorem IsBoundedRange.fpMul {R : Type*} [...]
    {lo₁ hi₁ lo₂ hi₂ : R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => y))
    (hf : fpMulFinite x y = Fp.finite f) :
    ∃ (lo' hi' : R),
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f)
```

The ∃-form lets the focused session pin down exact output intervals
without committing to a closed-form expression in the signature. If
closed forms are found, the theorem can be re-stated without the
existential.

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
of kernel, reused by both `HasAbsBound.fpAdd_nonneg_normal` and
`HasAbsBound.fpMul_nonneg_normal`. Pattern validated: one meta-lemma
per tag, N=2 ops supported from it.

### 3.3 `Flean/Tags/Bridges/` directory

- Move `IsBoundedRange.exp_isNormalRange` from `SoftmaxBounded.lean` to
  `ToIsNormalRange.lean`.
- Add the `h_quot_nr` bridge (signature below; proof in a focused
  session — library stays sorry-free).
- Leave `SoftmaxBounded.lean` as the consumer-side wrapper.

**Success criterion**: user hitting `h_exp_nr` can find all discharging
bridges in one file.

**Canonical `h_quot_nr` bridge signature** (locked here for future
implementation):

```lean
-- Intended location: Flean/Tags/Bridges/ToIsNormalRange.lean
theorem IsBoundedRange.quot_isNormalRange [FloatFormat]
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [ExpApprox] [ExpApproxSound]
    {n : ℕ} (hn : 0 < n) {lo hi : ℝ}
    {xs : Fin n → FiniteFp} {exps : Fin n → FiniteFp} {denom : FiniteFp}
    (hxs : IsBoundedRange (R := ℝ) lo hi xs)
    (hlo : (FloatFormat.min_exp : ℝ) * Real.log 2 ≤ lo)
    (hhi : hi < ((FloatFormat.max_exp + 1 : ℤ) : ℝ) * Real.log 2)
    (h_exp : ∀ i, fpExpFinite (xs i) = Fp.finite (exps i))
    (hd_close : |(denom.toVal : ℝ) - ∑ j, ((exps j).toVal : ℝ)| ≤
                (η : ℝ) * ∑ j, |((exps j).toVal : ℝ)|)
    (hd_pos : 0 < (denom.toVal : ℝ))
    (h_separation : (2 : ℝ) * n * (2 : ℝ) ^ (FloatFormat.min_exp : ℤ) ≤
                    Real.exp (lo - hi))
    (i : Fin n) :
    isNormalRange (((exps i).toVal : ℝ) / denom.toVal)
```

The `h_separation` hypothesis says "the spread of xs is not so extreme
that the smallest softmax entry underflows." Sufficient but possibly
not necessary; the focused session will tighten if needed.

### 3.4 Parametric propagation library (per §1.4)

- Start with `IsBoundedRange.{fpAdd, fpMul, fpFMA}`.
- Exact rounding-slack formulas derived from `RelativeError.lean`.
- Separate file: `Flean/Tags/BoundedRangePropagate.lean`.

**Success criterion**: a 3-op chain (e.g., `fpAdd (fpMul x y) bias`) can
thread `IsBoundedRange` through via three explicit calls, and the proof
reads as interval arithmetic.

### 3.5 Retrofit pilots

- Rewrite `Nonneg.lean` preservations to use the meta-lemma + helpers.
- Measure total LOC before vs. after.

**Success criterion**: 30%+ reduction in pilot LOC, with proofs more
mechanical.

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

## 6. Out of scope (for clarity)

- Phase 2 (tag-specialized bounds that actually tighten end-to-end
  theorems like Softmax's `subnormalConst`).
- ML primitives (attention, layer norm, etc.).
- Tag export to external tools.
- Any tactic or elaborator work.

These come later. Keeping this doc scoped to "what does Phase 1
infrastructure look like" prevents the scope creep the pilot phase was
designed to prevent.
