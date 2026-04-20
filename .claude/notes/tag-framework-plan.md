# Constraint-Tagged Values — Design Plan

A design doc for adding *structural tags* to floating-point values and
propagating them through operations, so that error bounds can specialize
when the caller has extra structural information (inputs are on the
simplex, unit-norm, non-negative, range-bounded, etc.).

---

## Motivation

### What's wrong with the alternatives

**Interval arithmetic** (`[a, b]`-tags) is the first thing to reach for, but
it has well-known pathologies:

- **Dependency problem**: `x - x` computed intervally becomes `[a-b, b-a]`,
  not `[0, 0]`. Operations lose correlations between operands.
- **Wrapping effect**: composing intervals across many ops produces
  catastrophic over-approximation, because an interval can't express
  "these two values are correlated."
- **Non-box reachable sets**: in reals (let alone FP) the actual input
  distributions for real problems are rarely axis-aligned boxes. ML inputs
  live on:
  - The probability simplex (softmax outputs, attention weights)
  - The unit sphere (normalized embeddings)
  - Non-negative orthants (post-ReLU, variances, norms)
  - L2-norm balls (post-clipping gradients)
  - `{−1, 0, 1}` tensors (masks, categorical labels)
  - Affine subspaces (zero-mean outputs of normalization layers)

  None of these are well-captured by a scalar `[a, b]`.

**Affine arithmetic / Taylor models** fix the dependency problem by
tracking values as `center + Σᵢ εᵢ·cᵢ` with `εᵢ ∈ [−1, 1]`. This is the
standard rigorous-numerics upgrade. It's interesting to formalize but still
a *scalar* abstraction — doesn't capture "on the simplex."

### What we want instead

**Tagged values**: attach `P : FiniteFp → Prop` or `P : (Fin n → FiniteFp) → Prop`
predicates that capture meaningful structural properties. Key idea:

1. Predicates are arbitrary, so they can express structural constraints
   (simplex membership, unit norm) that intervals can't.
2. Operations that preserve structural tags propagate them automatically.
3. **The real payoff**: error bounds can be *tag-specialized* — a softmax
   on bounded-range inputs has a cleaner bound than on arbitrary inputs;
   a weighted sum with simplex weights bounds against `max|xᵢ|` instead of
   `Σ|wᵢ·xᵢ|`.

The design pattern is a decades-old idea (*abstract interpretation*,
*shape analysis*) applied to FP error analysis. The novelty here is
(a) integrating with our existing `FpSumBound` / `FpDotProductBound`
abstraction layer and (b) targeting ML's particular vocabulary of shapes.

---

## Design

### Core: `Preserves` typeclass

```lean
class Preserves {α β : Type*} (P : α → Prop) (Q : β → Prop) (f : α → β) : Prop where
  preserves : ∀ x, P x → Q (f x)

-- Automatic composition: one instance, every chain works
instance {α β γ} {P : α → Prop} {Q : β → Prop} {R : γ → Prop}
    {f : α → β} {g : β → γ}
    [hfg : Preserves P Q f] [hgh : Preserves Q R g] :
    Preserves P R (g ∘ f) where
  preserves x hx := hgh.preserves _ (hfg.preserves _ hx)

-- Tag weakening (subset implications): if P → Q, then id preserves P → Q
instance {α} {P Q : α → Prop} (h : ∀ x, P x → Q x) : Preserves P Q id where
  preserves := h
```

### Tag vocabulary (first pass for ML)

Target ~10 tags that cover the common structural facts in ML pipelines:

**Scalar tags** (on `FiniteFp`):
- `IsNonneg` — `0 ≤ toVal`
- `IsProb` — `0 ≤ toVal ≤ 1`
- `HasAbsBound c` — `|toVal| ≤ c`
- `IsNormal` — magnitude in the normal range (no subnormals). This is the
  "normalness certificate" from the roadmap.

**Vector tags** (on `Fin n → FiniteFp`):
- `IsNonneg` — pointwise
- `IsSimplex_ε` — non-negative + `|Σᵢ toVal − 1| ≤ ε`. Parametrized by
  tolerance because softmax outputs only *approximately* sum to 1 in FP.
- `IsUnit_ε` — `|‖·‖₂ − 1| ≤ ε`
- `HasRangeBound [a, b]` — all components in `[a, b]`
- `HasL2Bound c` — `‖·‖₂ ≤ c`
- `IsPostReLU` — equivalent to `IsNonneg`; tag name for readability at
  use sites
- `IsZeroMean_ε` — `|Σᵢ toVal / n| ≤ ε`

### Tag-preservation instances

Each ML operation gets instances stating which tags it preserves/creates:

```lean
-- Softmax always outputs an approximate simplex
instance : Preserves (fun _ : Fin n → FiniteFp => True)
                     (IsSimplex_ε softmax_ε_bound) fpSoftmax := ...

-- ReLU creates non-negative output from arbitrary input
instance : Preserves (fun _ : FiniteFp => True) IsNonneg fpReLU := ...

-- Normalize preserves nothing in the input but creates a near-unit output
instance : Preserves (fun _ => True) (IsUnit_ε normalize_ε_bound) fpNormalize := ...

-- LayerNorm creates zero-mean + near-unit-variance (two tags via product)
-- ...and so on
```

### Tag-specialized error bounds

Each tightening is a separate theorem that picks up the tag from context:

```lean
-- General bound (already exists): relErr · Σ|wᵢ·xᵢ|
theorem fpDotProduct_error_bound (b : FpDotProductBound ws xs ℝ) : ...

-- Simplex-specialized: relErr · max|xᵢ|
-- (exploits Σwᵢ = 1 and wᵢ ≥ 0)
theorem fpDotProduct_error_bound_simplex
    (hws : IsSimplex_ε ε ws) (b : FpDotProductBound ws xs ℝ) :
    |b.result.toVal - ⟨true inner product⟩| ≤ b.relErr · max|xᵢ| + O(ε · max|xᵢ|)
```

A consumer's typical call site:

```lean
-- Attention head: scores → softmax → weighted sum with V
def fpAttention (scores V : Fin n → FiniteFp) : FiniteFp :=
  fpDotProduct (fpSoftmax scores) V

theorem fpAttention_bound (...) :
    |fpAttention scores V - true_attention| ≤ relErr · max|V| + O(softmax_ε · max|V|) := by
  -- The `IsSimplex_ε` tag on `fpSoftmax scores` is synthesized automatically
  -- via `Preserves True IsSimplex_ε fpSoftmax`; the simplex-specialized
  -- dot-product bound applies.
  exact fpDotProduct_error_bound_simplex (by infer_instance) ...
```

---

## Worked example: weighted sum with simplex weights

This is the key structural insight underlying softmax-attention's
numerical stability. The tight bound depends on the weights summing to 1.

```lean
-- Setup
variable {n : ℕ} (ws xs : Fin n → FiniteFp)

-- Generic FpDotProductBound bounds against Σ|wᵢ·xᵢ|
-- which can grow with n. For ws on the simplex with xs arbitrary, we
-- want the tighter bound against max|xᵢ|.

theorem fpDotProduct_error_bound_simplex
    (hn : 0 < n) (hws : IsSimplex ws)
    (b : FpDotProductBound ws xs ℝ) :
    let M : ℝ := Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
                   (fun i => |(xs i).toVal|)
    |(b.result.toVal : ℝ) - ∑ i, (ws i).toVal * (xs i).toVal| ≤
      b.relErr * M := by
  obtain ⟨hnn, hsum⟩ := hws
  -- Key: Σ|wᵢ·xᵢ| = Σ wᵢ·|xᵢ|  (since wᵢ ≥ 0)
  --              ≤ (Σ wᵢ) · M   (since each |xᵢ| ≤ M)
  --              = 1 · M = M     (by hsum)
  have habs_eq : ∀ i, |(ws i).toVal * (xs i).toVal (R := ℝ)|
                    = (ws i).toVal * |(xs i).toVal| := fun i => by
    rw [abs_mul, abs_of_nonneg (hnn i)]
  have hle : ∑ i, |(ws i).toVal * (xs i).toVal (R := ℝ)|
           ≤ ∑ i, (ws i).toVal * M := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [habs_eq]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' _ (Finset.mem_univ i)) (hnn i)
  have hsimp : ∑ i, (ws i).toVal * M = M := by
    rw [← Finset.sum_mul, hsum, one_mul]
  calc |(b.result.toVal : ℝ) - ∑ i, (ws i).toVal * (xs i).toVal|
      ≤ b.relErr * ∑ i, |(ws i).toVal * (xs i).toVal| := b.h_bound
    _ ≤ b.relErr * M := by
        rw [← hsimp]
        exact mul_le_mul_of_nonneg_left hle b.h_relErr_nn
```

Two things to notice:

1. The hypothesis is `IsSimplex ws` — a *tag*, not interval data. In a
   typeclass-driven version, this is picked up automatically from the
   context (`fpSoftmax`'s output has an `IsSimplex` tag).

2. The bound is in `max|xᵢ|`, *not* `Σ|wᵢ·xᵢ|`. This is the classical
   result that attention is numerically stable w.r.t. the sequence length:
   adding more tokens doesn't inflate the bound (it only grows with
   `max|V|`, which is an input-data property, not an algorithm property).

---

## Concern: typeclass inference performance

**User's flagged concern**: complex Layer typeclass chaining in a related
ML formalization project hit search-limit and perf issues. This is a real
risk — the composition instance is potentially search-explosive.

### Why it *might* work anyway

For a tag-propagation use case, inference is mostly linear-in-depth:

- Chain `f₁ ∘ f₂ ∘ ... ∘ fₙ`: at each step, we're asking `Preserves ? ? fᵢ`
  for a *specific* function `fᵢ`. The search is function-directed, not
  proposition-directed.
- Tag weakening (P → Q) is also linear, and we can keep the implication
  lattice small.
- There's no backtracking through a large search space if instances are
  structured so each function has ≤ 2-3 direct preservation instances.

### Mitigations if it doesn't

Several fallbacks, in order of increasing intervention:

1. **Instance priorities** — mark the chain-composition instance with low
   priority so direct instances are preferred.

2. **Scoped typeclasses** — put `Preserves` in an opt-in namespace; only
   open when doing tag reasoning, so ambient typeclass search isn't
   burdened.

3. **Explicit carrier struct** — instead of typeclass instances, bundle
   tags *on the value*:
   ```lean
   structure TaggedFp (P : FiniteFp → Prop) where
     val : FiniteFp
     tag : P val
   ```
   Tagged versions of each op propagate tags explicitly. No search, just
   function composition. The cost is re-declaring types (`TaggedFp
   IsSimplex`, `TaggedFp IsProb`, etc.).

4. **Custom `tag_infer` tactic** — a domain-specific elaborator that
   walks an expression, matches against a hand-curated table of
   preservation lemmas, and synthesizes the tag proof. Doesn't use
   typeclass search at all; just a controlled forward-chaining procedure.
   More work up-front but fastest at use sites.

5. **Macro sugar** — a macro that annotates function definitions with
   their preservation properties and generates both the instance and the
   specialized bound lookup automatically.

**Recommended incremental path**: start with (1) + (2). If those suffice
for ~5 tags, great. If perf degrades at scale, jump to (4) — a custom
tactic — because it's the most control for the intervention cost.

---

## Composition with existing abstractions

The tag framework plugs into the existing bound abstractions:

- `FpSumBound`, `FpSumBoundCompensated`, `FpDotProductBound`,
  `FpDotProductBoundCompensated`, `FpMatVecBound` — these stay as they
  are. Each grows *tag-specialized variants* alongside the general bound.

- The **normalness certificate** roadmap item is the first concrete tag;
  it drops the `subnormalConst` additive tail from Softmax/LogSumExp.
  It's a natural pilot because it's a single-tag win with no composition
  complexity.

- The **interval/affine arithmetic** track can still happen independently
  — it's an orthogonal abstraction domain. Affine arithmetic + tags
  compose well: affine gives tighter numeric ranges, tags give structural
  constraints.

---

## Proposed phased implementation

### Phase 0 — Pilot (one tag, one op, one specialized bound)

Pick the simplest non-trivial case that exercises the pattern end-to-end.
Candidate: `IsNonneg` + `fpReLU` + "ReLU on non-negative input is
identity" (exact error).

- Define `IsNonneg : FiniteFp → Prop`
- Show `Preserves (fun _ => True) IsNonneg fpReLU`
- Prove `fpReLU_exact_on_nonneg : IsNonneg x → fpReLU x = x`
- Add *no* framework machinery yet; just write it direct to confirm the
  pattern feels right.

**Deliverable**: ~100 lines, one new file. Exercises the core pattern
without framework commitment.

### Phase 1 — Framework (Preserves class, composition, weakening)

- Define the `Preserves` class + composition + weakening instances.
- Rewrite Phase 0's `fpReLU_exact_on_nonneg` to *use* the class.
- Add 2-3 more tags (`IsProb`, `IsSimplex`) and one more op
  (`fpSoftmax` preserves `True → IsSimplex_ε`).
- Demo: auto-chain `fpReLU ∘ fpSoftmax` to show composition works.

**Deliverable**: ~300-500 lines. First real test of typeclass inference
performance — benchmark here.

### Phase 2 — Tag-specialized bounds

- `fpDotProduct_error_bound_simplex` (the worked example above).
- `fpSoftmax_error_bound_range_bounded` (tighter softmax bound when
  input range is bounded, avoiding saturation).
- `fpReLU_exact_on_nonneg` + the implication that a chain of
  `fpReLU`s adds no error on non-negative inputs.

**Deliverable**: ~500 lines. These are the first cases where tags
actually *buy something* over the general bounds.

### Phase 3 — ML primitives

- Layer norm tags (zero-mean, near-unit-variance outputs).
- Attention block (full pipeline: Q·Kᵀ → scale → softmax → weighted V).
- Cross-entropy loss (log-softmax + NLL with probability tag).

**Deliverable**: ~1000-1500 lines per primitive. At this point, the
framework's value is load-bearing — without tags, each primitive's bound
is O(n) ugly; with tags, each is O(1) clean.

### Phase 4 — Perf audit + mitigation

Run benchmarks on typical use sites. If typeclass search is ≥ few hundred
ms on Phase 3 examples, implement mitigation (2) or (4) from above.

### Phase 5 — Tool integration (goal 1)

Expose tag information to an external consumer (Python-side analyzer)
via JSON dump of `Preserves` instances + specialized bounds. Lets a
static analyzer on user code say "I can prove your softmax output is a
simplex, so this downstream dot product has a tight bound — your current
implementation uses the loose bound, consider swapping algorithms."

---

## Design questions to resolve before starting

- **Parametric tags vs. multiple tags**: `IsSimplex_ε` vs. `IsSimplex` +
  `SumEqOne_ε` composed. Parametric is more convenient; composed is more
  compositional. Default to parametric; split only if needed.

- **Quantitative vs. qualitative tags**: e.g., `HasAbsBound c` carries
  numeric data `c`. Some designs keep the numeric data in the tag; others
  separate (tag says "bounded", a separate dependent type carries `c`).
  Default: numeric data in the tag, accessed via field projection.

- **Tag algebra**: is there a meet/join lattice on tags? Probably yes
  (e.g., `IsSimplex ≤ IsNonneg`, `IsProb ≤ IsNonneg`). If we formalize
  this, tag weakening becomes `Preorder` reasoning. Could be useful
  but may be overkill for Phase 1.

- **Tags on unknowns vs. tags on computations**: tags can attach to
  *values* (this specific vector is a simplex) or to *operations* (the
  output of `fpSoftmax` is always a simplex). The `Preserves` typeclass
  handles operations; value tags are just proofs. Make sure both work
  ergonomically.

---

## References for methodology

- Abstract interpretation literature (Cousot & Cousot's original work;
  industrial tools: Astrée, Frama-C)
- Gappa, FPTaylor, Daisy — FP-specific verification tools using
  interval/affine abstractions
- Lean 4 typeclass mechanics (see `simp_classes.lean` for advanced
  composition patterns, and mathlib's `Order.Hom` for
  preserves-style classes done at scale)
- Existing normalness-adjacent work in Flean: `isNormalRange`,
  `isNormal`, `isSubnormal` predicates and propagation lemmas
