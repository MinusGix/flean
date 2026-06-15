# Session Prompt — Minimal mod-p Domain (first idea-extraction)

**Goal:** build the first *structural* abstract domain on the precise pillar — track `n mod
p` through exact integer-valued float computations — so the stack can *extract* "this float
computation is mod-p arithmetic", not just bound it. This is the first time the reduction
stack says something **structural** about a shadow rather than metric.

Read first: `exact-int-design.md` (the two-domain-families distinction — mod-p is a
*discrete* domain, so it lives on the **precise** pillar, exact only) and
`exact-int-reduction.md` (what's shipped).

## Why this piece (triple duty)

1. **First idea-extraction.** "This float net's shadow is a fixed residue mod p" — extraction,
   not bounding.
2. **Second structural instance.** It's the test case for whether the explicit
   `AbstractFp`/Galois-connection framework is worth building. Build it *concretely*; then
   compare with `ExactInt` to see what genuinely factors. Do NOT build the framework first
   (preconditions don't factor uniformly — see design note §Decision 2).
3. **Tests "does it fit the shadow?"** — the extraction question, concretely.

## What to build on

- `ExactInt R` (`Flean/Operations/ExactIntAlgebra.lean`): `fp`, `n : ℤ`, `agree : fp.toVal =
  n`; total `Zero/One/Neg`; partial `mul`/`add`/`sub` (no `≠0` side conditions — zero-admitting
  via `ExactIntZero.lean`); `.n` is a (partial) ring hom by `rfl` (`mul_n`/`add_n`/… simp).
  `dot2` exists.
- The whole point: `n mod p` rides on the EXACT integer `n` that `ExactInt` already tracks.
  The mod-p transformer is just the ℤ → `ZMod p` ring map applied to `.n` — and `.n` already
  commutes with the ops, so the mod-p invariant propagates almost for free.

## Concrete deliverables (suggested)

1. A residue predicate / wrapper on `ExactInt`: e.g. `IsResidue (p : ℕ) (r : ZMod p) (a :
   ExactInt R) : Prop := (a.n : ZMod p) = r`. (Predicate first — lighter than a new struct;
   decide struct-vs-predicate as you go, mirroring the design note's "concrete first".)
2. Propagation lemmas: `IsResidue p r_a a → IsResidue p r_b b → IsResidue p (r_a + r_b)
   (a.add b …)` and the `*` analogue. These should be near-trivial given `add_n`/`mul_n` are
   `rfl` and `Int.cast` is a ring hom `ℤ → ZMod p` (`Int.cast_add`/`Int.cast_mul`). Negation
   too.
3. **The headline (extraction):** a tiny concrete exact computation (e.g. a 2- or 3-term
   integer dot product or a small polynomial via `dot2`/`mul`/`add` on `ExactInt`s) whose
   result is provably `≡ r (mod p)` for a fixed `r` — i.e. the float computation's shadow
   *is* a specific residue. Keep inputs abstract-shape (integer-valued `ExactInt`s with the
   representability hyps), not `FiniteFp` numeral literals (literal construction is verbose —
   noted in earlier sessions).
4. (Optional) the snapping bridge: if a value is within `err < ½ ulp` of an `ExactInt` (i.e.
   a `ScaledInt` with small enough `err`), recover the exact `n`, hence its residue — the
   "mod-p tolerates error only below threshold" story. Likely its own follow-up; needs a
   "round/snap noisy value to nearest integer when err < ½ ulp" lemma. Defer unless quick.

## Design constraints / reminders

- **Precise pillar only.** mod-p does NOT compose with a growing `err` (a ±1 shadow drift
  flips the residue). Build it on `ExactInt` (exact), not `ScaledInt`. The error story is the
  snapping bridge (deliverable 4), which *reduces* to the exact case.
- Mirror the successful method: **handcraft the concrete extraction first, feel it, then
  generalize.** Don't pre-build an abstraction.
- Watch the unused-section-variable lint (use `omit … in` for lemmas not needing the rounding
  typeclasses — propagation lemmas likely need none beyond `ExactInt`'s).
- `ZMod p` for `p` a literal vs general `p` — start with general `p` if the ring-hom lemmas
  go through cleanly (they should); the headline can fix a concrete `p`.

## The meta-question to answer by the end

After building mod-p concretely: **what did it share with `ExactInt`'s structure, and does an
explicit `AbstractFp` (γ + sound transformer, with per-domain preconditions) now look worth
factoring — or is a documented pattern + light helpers the right call?** Record the verdict
in `exact-int-design.md`.
