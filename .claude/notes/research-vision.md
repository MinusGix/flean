# Research Vision — Flean / Wick / Wisp

**Canonical cross-repo vision doc.** Identical copy lives in each of the
three repos' `.claude/notes/research-vision.md`. Captures the *animating
inspirations* (not the tactical backlog) so future sessions — in any of
the three repos — know what the whole program is *for*.

Authored 2026-06-14 from a long-form articulation by the user. Quotes
below are close paraphrases of his own framing; treat them as the source
of truth about intent, above any individual repo's accumulated backlog.

---

## The through-line: a reductionist, FP-aware physics of machine learning

The three repos are **one research program**, not three projects. The
unifying bet:

> Floating point is not noise to be bounded away — it is a more honest,
> finite, sometimes-*simpler* substrate. Taking it seriously (reductively)
> can both **reduce computation** and **clarify theory**.

Three layers of reduction / abstraction over the same object (a neural net):

| Repo | Lens | "ML is really…" |
|------|------|-----------------|
| **Flean** | substrate | …circuits / integer & logical ops / bounded intervals |
| **Wick** | field theory | …statistical physics (PDLT — macroscopic laws of training/inference) |
| **Wisp** | the meeting point | …the physics *computed on the actual finite substrate*, where FP's finiteness changes the physics |

Flean supplies the reduced substrate. Wick supplies the theory worth
reducing. Wisp is where they collide — and the most novel ideas live in
that collision (e.g. "this PDLT term vanishes past scale X because FP
precision naturally cuts it off").

The error-bounds ML stack already shipped in Flean (softmax / LSE / CE /
MLP forward-error, tag framework) and Wisp's drift theorems are **useful
infrastructure but a partial detour** from the animating vision. They are
worth keeping and reusing, but they are not the soul. The soul is
*reduction* and *reinterpretation*, not *bounding*.

---

## Flean — floats as aggressively reductionist substrate

> "Floats are just an abstraction over the circuitry you're actually
> *running*, which happen to have a nice mathematical gradient-update form."

Two intertwined interests, both years-old:

1. **Circuit / integer reduction.** Stop seeing a computation as
   float-ops; see it as logical/integer ops, then optimize.
   - Naive: throw away "this is a floating-point op" → "this is a bunch of
     logical ops" and delete the useless ones *for a concrete model*
     (circuit-synthesis flavor).
   - Arcane / more interesting: turn multi-step float add/mul/activation
     sequences into a **simpler integer function with a small correcting
     factor** at the end.

2. **Interval / range analysis.** The internal representations of a
   (general, or specific concrete) network never exceed certain bounds.
   That structural knowledge enables optimization — and, more
   speculatively, **reinterpretation**: "in this float range, this op
   region *is* a sine with amplitude A, phase φ, and a slight
   discretization factor α." Treating realized ranges as a place to
   discover simpler closed forms.

The integer-equivalence / bit-exactness thread (the recent `IntegerEquivalence/`
work — fpNeg/fpAbs as bitops, ×2^k as exponent shifts, ReLU as masked
select, trunc/frexp/libm, Phase 6 flagship "binary-weight ReLU layer =
XNOR + popcount") is **on-vision, not a side quest.** It is the
bit-formalization groundwork the reductionist program needs.

Some of this is "just needs lots of bits formalized." Some is genuine
**research / probing questions** (what reductions actually exist in real
networks' realized ranges?).

### Flean big-thing candidate (recalibrated to the real interest)

**Range-conditioned reduction on a concrete tiny network.** Unifies both
sub-interests:
1. Interval-propagate input bounds through a small concrete net → bound
   each op's *realized* input range.
2. Within a realized range, replace one FP op (or a multi-op chain) with a
   reduced surrogate — integer/bitop/affine — carrying an **explicit
   correction bound**.
3. Headline: "given input bounds, this float multiply-add-by-fixed-weight
   *equals* this integer/bit expression + bounded correction, on its
   realized range."

That is the first real *payoff* of the bit-formalization grind — it turns
"lots of bits formalized" into a result. The "sin with amplitude A, phase
φ, discretization α" reinterpretation is the stretch/research probe past it.

---

## Wick — a fully formalized physics of machine learning

> "A core thing is understanding machine learning *deeply* — a fully
> formalized 'physics of machine learning.'"

Inspired by **PDLT** (*The Principles of Deep Learning Theory*). The
specific joy:

> "There are many parts the authors skip or approximate merely because
> they're *tedious* — but **computers are great at tedious formal
> expansions**. There are whole papers to be drummed out of expanding an
> approximation to thirty terms and finding a better small-scale
> approximation than the naive cutoff. Or applying the model in ever more
> generality, to ever more model kinds."

**The pain (the real blocker, be honest about it):** formalizing physics
is hard. Combinatorics in Lean is miserable. The files blow up — a dozen
baseline parameters on everything — and the blowup compounds (easy to
blow up *more*). There are simplifications to be made, but the blowup
makes further blowup easier. Taming the ergonomics is itself part of the
work, not a distraction from it.

Current frontier: gradient correctness (`backward = fderiv-adjoint`,
building param-side adjoints up through `Residual(LayerNorm ⋙ FFN)`) and
the PDLT theory files (`PDLT/`, linked-cluster FPS / `WickCauchyProduct.lean`,
which still carries ~8 `sorry`s — exactly the combinatorial frontier).

### Wick big-thing candidate

**Push one PDLT computation past where the book stops.** Expand a specific
approximation to many terms and *extract a novel finite-width correction
the book never wrote down* — the thing the user explicitly wants. The
enabling investment is the combinatorics-taming machinery (Wick-contraction
/ FPS / the `WickCauchyProduct` frontier). Success = "the first formally
derived higher-order PDLT result beyond the book's cutoff," with the
blowup-control infrastructure as the reusable byproduct.

---

## Wisp — neural nets *under* floating point (where Flean meets Wick)

Two motivations, the second being the most novel idea in the whole program.

1. **Reductionist FP applied to real networks** (Flean's original
   inspiration, instantiated on actual nets) + **systematic study of how
   networks behave differently under FP**: where they diverge from the
   reals; activation functions that are unbiased/well-behaved in ℝ but
   **biased in floating point**; etc. There are dozens of papers on such
   topics — a proper library could explore them *far more systematically*
   than any single paper.

2. **PDLT under floating point.** The exciting frontier:
   > "There are very possibly simplifications to PDLT — and complications! —
   > via the nature of floating point as much more *docile*, even if also
   > combinatorially finite-yet-large. (Continuity can be a godsend at
   > times.) There may be aspects of PDLT that turn into 'oh, guess that
   > doesn't matter past this scale because it gets naturally cut off by
   > floating-point precision.'"

FP as *docile-but-finite*: finiteness can make things tractable (sums not
integrals, no measure-theoretic tail); precision can *kill* terms a
continuous theory has to carry.

Current state: Wisp already proves forward / backward / SGD-step / multi-step
**training-drift** divergence — but only for Linear/MLP chains. That
machinery is reusable scaffolding; it is *not yet* pointed at the novel
questions above.

### Wisp big-thing candidate

**Demonstrate one place where FP qualitatively changes a prediction.**
Either:
- *Activation bias* (more tractable entry): pick a concrete activation,
  show its FP expectation differs measurably from its ℝ expectation, and
  propagate that bias one step into a PDLT moment / layer statistic. "This
  activation is unbiased in ℝ, biased in FP, by this much, with this
  downstream effect."
- *Precision cutoff* (the dream): identify a PDLT term that *vanishes*
  under FP past some scale — formalize the "doesn't matter past here"
  statement.

Either is a genuinely novel research result, not an error bound.

---

## Dependency / sequencing reality

- **Wisp depends on both** Flean and Wick (path deps in its lakefile). Its
  novel questions (PDLT-under-FP) need *both* a reduced FP substrate
  (Flean) and PDLT theory mature enough to perturb (Wick). So Wisp's
  deepest payoff is gated on progress in the other two.
- **Wick's PDLT frontier is the hardest** (combinatorics blowup) and the
  most upstream for Wisp's dream result.
- **Flean is the most self-contained** and has the most momentum on its
  on-vision thread (integer-equivalence). It can produce a reductionist
  *result* (range-conditioned reduction) without waiting on anyone.

Implication: the three "big things" are not equally ready. Flean's is
shippable now and on-soul; Wick's is the long pole; Wisp's best work waits
on Wick. A reasonable cadence is **Flean reductionist result now → Wick
combinatorics-taming + one beyond-the-book expansion → Wisp PDLT-under-FP
once Wick has something to perturb** — while keeping the already-shipped
error-bounds/drift infrastructure as reusable plumbing rather than the goal.

---

## What this doc is *not*

Not a backlog. Per-repo tactical backlogs live elsewhere:
- Flean: `.claude/notes/directions.md`, `strategic-directions.md`,
  `fp-integer-equivalence.md`, and the memory index.
- Wick: `ROADMAP.md`.
- Wisp: `CLAUDE.md` long-term list, `BACKLOG.md`, `UPSTREAM_ASKS.md`.

When those backlogs and this doc disagree about *what matters*, this doc
wins — the backlogs optimize locally; this records the global why.

---

## Refinements (2026-06-14, session 2) — working *in pieces*

The user's correction: he wants to work in **pieces**, not chase a
big-thing directly. Per-repo sharpening:

**Flean.** Method = *handcrafted first concrete class → then generalize
"what range of things behaves in this simplified manner."* Start with one
concrete reduction theorem, then widen the range it covers. Aspirational
concrete target named: a **modular-arithmetic network** — extract "this
float net is really doing mod-p arithmetic." But that needs intermediate
substrate first (interval/representability machinery + the base
reduction theorems). Stage it; don't jump to the net.

**Wick.** Three distinct sub-directions, all valid, different effort/payoff:
1. *Mundane-but-tedious*: implement common layers, prove basic properties.
   Low risk, steady velocity, broadens coverage.
2. *Wacky layer properties*: prove interesting/non-obvious things about
   specific layers. Medium effort, high interest.
3. *PDLT*: the hard one — complex, careful, brain-melting combinatorics.
   Highest payoff, longest pole.

**Wisp.** Near-term = the activation-bias target (unbiased in ℝ, biased in
FP). The bigger dream: discover a **correction term** applied to gradient
updates (every step, or every Nth step, or paired with a tracked statistic)
that makes FP training track the idealized-ℝ trajectory much more closely —
then *experiment*: does closer-to-ℝ actually train better, or worse
(because FP's deviation is acting as implicit regularization)? **Quantify
FP-as-regularization** — the effect/amount of the implicit regularization
floats impose on training. This reframes "FP divergence" from a defect to
a measurable, possibly-beneficial phenomenon.

