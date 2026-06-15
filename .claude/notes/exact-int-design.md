# Exact-Int / Reduction Area — Design Notes

Architectural thinking behind the exact-integer + fixed-point reduction stack (the Flean
"reductionist substrate" thread — see `research-vision.md`). Captured 2026-06-15 from a
design discussion. This is the *why* and the *shape*; the tactical log is in
`exact-int-reduction.md`.

---

## What this area actually is: abstract interpretation for floating point

Strip away the individual structures and there is one idea. Each structure pairs a `FiniteFp`
with a **simpler shadow value** plus an **invariant** (a concretization relation γ):

| Structure | Shadow | Invariant γ |
|---|---|---|
| `ExactInt` | integer `n` | `fp.toVal = n` |
| `ScaledExact` | fixed-point `m·2^s` | `fp.toVal = m·2^s` |
| `ScaledInt` | `m·2^s` + error `err` | `\|fp.toVal − m·2^s\| ≤ err` |
| `ExactIntB` | integer `n` + bound `B` | `fp.toVal = n ∧ \|n\| ≤ B` |

Every `add`/`mul` is a **sound abstract transformer**: it runs the op in the shadow domain
(integer / fixed-point arithmetic) and re-establishes γ — exactly, or with a growing `err`,
or with a growing `B`. The "`.n` is a ring hom" fact, the `err` closed forms, the
propagating `bound` — all are "the abstract transformer is sound."

So the four structures are **four abstract domains of differing precision**, points in one
lattice. The "reduction" payoff: run the computation in the abstract (integer/fixed-point)
domain and you get a simpler computation that soundly characterizes the float one — exactly
(lossless) or up to a tracked error (lossy).

**Idea-extraction**, in this lens, is just: *does the computation fit a given shadow
domain?* "This float net is really doing mod-p arithmetic" = the net's shadow respects a
mod-p domain. So extracting structure = adding domains and checking which the computation
lives in cleanly.

---

## The central distinction: two families of domain → two pillars

Domains come in two kinds, and the kind dictates which pillar can host it.

**Metric / continuous domains** — interval, magnitude, near-affine, near-sine. About
*closeness*. **Robust to error** (error widens the envelope). Live on the **approximate
pillar** (`ScaledInt`); `err` composes through them smoothly.

**Discrete / structural domains** — mod-p, exact sign, exact equality, exact periodicity.
About a *discrete invariant of the exact integer*. **Brittle to error**: a ±1 shadow drift
flips the invariant catastrophically. To even *speak* of `n mod p` you must recover `n`
exactly, which needs `err < ½ ulp`. So discrete domains effectively demand the **precise
pillar** (`ExactInt` / `ScaledExact`).

This is the real meaning of the two pillars — not lossless-vs-lossy convenience, but **two
different families of invariant**:
- discrete structure ⇒ precise pillar (or sub-ulp snapping into it),
- metric structure ⇒ approximate pillar.

### The recoverability / snapping threshold (hybrid structural-with-error)

"mod-p with error" *is* meaningful, but only below a recoverability threshold. If `fp.toVal`
is within `err` of a discrete lattice and `err < ½ ulp at the scale`, you can **snap** the
noisy value back to the exact integer and reason discretely; above the threshold the
structure is genuinely lost. So a real modular-net analysis routes through the precise
pillar: prove the computation is **exact** on the range (no rounding) → mod-p is clean; *or*
prove `err < threshold` → snap → reduce to the exact case.

That snapping threshold is exactly the **"discretization factor α"** from the
"this region is a sine with amplitude A, phase φ, discretization α" dream. The "near a
discrete lattice, recoverable below threshold" pattern covers both mod-p and sine-shape.

---

## Design decisions

1. **Precise and approximate stay as two structures + an embedding — NOT a subtype.**
   A subtype `{x : ScaledInt // x.err = 0}` fights Lean exactly where the precise layer earns
   its keep: reductions go through `.val`, so the `rfl`-clean "`.n` is a ring hom"
   *evaporates* (no longer definitional through the wrapper), and integer-ness needs a second
   condition (`s = 0`) compounding the clunk. The abstract-interpretation lens agrees: these
   are two domains connected by an **abstraction map** (`ExactInt ↪ ScaledInt`, `err := 0`),
   not a subset relation. Keep each first-class; provide the one-way embedding. (This is
   essentially what we have — make it deliberate.)

2. **Do NOT make the abstraction explicit (a `class AbstractFp`) yet.** The blocker: the
   **soundness preconditions don't factor uniformly**. A clean `class AbstractFp (A) where γ;
   add; add_sound` wants unconditional `add_sound`, but every transformer is sound only under
   *domain-specific* side conditions — no-overflow (ExactInt), finiteness (ScaledInt),
   *exactness* (mod-p), `err < threshold` (hybrids). A uniform typeclass either bakes in the
   union (ugly) or is too weak. Precedent: the tag framework deliberately rejected a heavy
   `Preserves` typeclass after its pilots. So: build the **second structural instance
   (mod-p) concretely first**; what it shares with `ExactInt` then reveals whether the
   framework is worth it (likely a documented pattern + light helpers, not a typeclass). The
   abstract-interpretation framing is the right **mental model and doc**, probably the wrong
   thing to *encode* until mod-p forces its hand.

3. **Vectors are orthogonal** to the domain question — you can vectorize any domain
   (`Fin n → ExactInt`, …). The real content is the *interplay* (cross-element bounds in a
   dot product, uniform vs per-index magnitude bound) — `dotN` + a matvec layer. Worth
   building as substrate, independent of the framework question.

---

## Where the area stands vs the north star

We've built the **lower half** — value-fidelity domains (is it an integer? how far off?).
The *goal* (idea-extraction: mod-p, periodic, affine) lives in the **upper half** —
structural domains. The abstract-interpretation lens connects them and reframes the
modular-net target: not a distant capstone needing tons of new machinery, but **"one more
domain"** on the substrate we now have.

Open threads (also in `exact-int-reduction.md`): zero-sum handling; n-ary `dotN` / vector
layer; `ScaledExact` sub/neg; and the structural frontier below.

**Next concrete step:** a minimal mod-p domain on the precise pillar (see
`mod-p-session-prompt.md`). It does triple duty — first idea-extraction, second structural
instance (informs the framework question), and a test of the "does it fit the shadow?"
question.
