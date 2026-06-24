# Exact-Int / Reduction Area — Design Notes

Architectural thinking behind the exact-integer + fixed-point reduction stack (the Flean
"reductionist substrate" thread — see `research-vision.md`). Captured 2026-06-15 from a
design discussion. This is the *why* and the *shape*; the tactical log is in
`exact-int-reduction.md`.

---

## Regime map (2026-06-15) — the domain lattice as built

Quick orientation for the whole area. Each domain pairs a `FiniteFp` (or its real value) with a
shadow + a concretization γ; ops are sound transformers. Two **pillars**:

**Precise pillar** (exact, on the integer shadow `ExactInt.n : ℤ`) — discrete/structural domains,
brittle to error:
- `ExactInt` (n) → `ExactIntB` (n + magnitude bound) → value-fidelity.
- **Ring-hom-image family** `IsImage (S)` [`ExactIntModP.lean`]: `IsResidue` (S=ZMod p), CRT
  `IsResiduePair` (S=ZMod p×ZMod q), `IsExactly` (S=ℤ, the top), functorial `.map`. mod-p etc.
- **`HasSign`** [`ExactIntSign.lean`]: multiplicative monoid-with-zero hom; `×` closes, `+` doesn't.
- **`HasSignMag`** [`ExactIntSignMag.lean`]: REDUCED PRODUCT sign×magnitude-interval; `+` now closes
  (even across opposite signs, given separation). First reduced product.

**Approximate pillar** (inexact, real value, carries `err`) — metric/continuous domains, robust:
- `ScaledExact` (m·2^s exact) → `ScaledInt` (m·2^s + err, forward-error composition).
- **`AffineForm`** [`AffineForm.lean`]: ideal `a·x+b`, the first continuous *structural* domain;
  `+` closes (`add`), `×` leaks the quadratic into err (`mul`, needs input bound X — reduced
  product with an interval, the metric mirror of HasSignMag).
- **`AffineFormVec`** [`AffineFormVec.lean`]: multi-input `c0+∑cᵢxᵢ` (affine arithmetic, a layer's
  shadow); `add`/`scaleConst`/`neg`/`ofConst`/`addConst`, bilinear-leak bound `mul_nonlinearity_bound`.
  **Grounded in a real layer** [`AffineLayer.lean`]: `ofDotProductBound` reads the existing
  `FpDotProductBound` (a real FP `∑wᵢxᵢ`) off AS an affine form; `neuron` adds bias; multi-input
  `reluActive` + `neuron_relu_value` = a real `⟨w,x⟩+b` layer + ReLU, on its region, IS the affine
  map of the inputs. Also unifies the affine domain with the error-analysis library.

**Bridges / interfaces:**
- **Snapping** [`ScaledIntSnap.lean`]: approximate → precise for discrete domains, gated `err < ½`
  (the "discretization α"). Recovers the exact integer → its residue/image.
- **ReLU regions** [`AffineRelu.lean`, `AffineNet.lean`]: the discrete×continuous interface — the
  *sign* picks the activation region, within which the unit (and a whole net) is *exactly affine*.
  Capstone: a 2-layer net in one region IS a single affine map `A·x+b` (+ matching err bound).
  Robust region certificate keyed on the ideal clearing the err margin, not the raw bit.
- **Tags unification** [`Tags/Bridges/ExactIntDomains.lean`]: the exact-int domains REFINE the
  pre-existing Tags domains (`HasSign→IsNonneg`, `HasSignMag→HasAbsBound`) — AI is the explicit
  spine joining this lattice to the 47k-line error-analysis library.

**The two recurring lessons:** (1) one *shape-agnostic* sound transformer serves many shadows
(`fpAddFinite_inexact_general` etc. — ScaledInt/AffineForm/AffineFormVec all reuse it); (2) closing
the "hard" operation forces a **reduced product with a magnitude/interval domain** — sign needs
magnitude to close `+`, affine needs an input bound to close `×`. Dual faces of one principle, and
the concrete reason a uniform `AbstractFp` transformer typeclass is the wrong abstraction.

Region-over-an-input-box DONE [`AffineRegion.lean`]: the classical ReLU **linear region as an input
set** — `relu_affine_on_box` (`max 0 g = g` over a box where the affine ideal is uniformly
positive ⇒ the neuron IS its affine map there) + FP-robust `fp_s_false_of_box` (box margin > radius
bound + err). The affine ⋈ interval reduced product, realized.

Taylor-degree-2 DONE [`QuadForm.lean`]: the **model-order tower**. `QuadForm` (ideal `a·x²+b·x+c`);
headline `ofAffineMul` catches the affine product EXACTLY (no `x²` leak, no `X` — degree-2 catches
what degree-1 dumped); `quad_mul_leak`+`QuadForm.mul` show the tower continues (degree-2 leaks
degree 3–4). The continuous regime is now a tower indexed by model order, each rung catching the
previous rung's nonlinearity leak — *curved* regions, not just linear.

Generic degree-`d` tower DONE [`PolyForm.lean`]: `PolyForm R d` (ideal `∑_{i≤d}cᵢxⁱ`) writes the
degree-generic add/scaleConst/neg/value/γ ONCE for all d; `value_one`/`value_two` recover
AffineForm/QuadForm as d=1,2; generic leak `truncateOne` (d+1→d, via `Fin.sum_univ_castSucc`).
**Meta-finding (mirrors IsImage):** the degree-fixed *structural skeleton factors uniformly*; the
real content is the *degree-changing* cross-ops — mul (raises degree exactly) + truncate (lowers,
leaks). Both done: `truncateOne` (lowers, leaks) AND `PolyForm.mul` (Cauchy product, raises degree d×e→d+e
EXACTLY, no leak — subsumes `QuadForm.ofAffineMul` and every rung). The tower is now **fully
generic**: mul up + truncate down, with AffineForm.mul/QuadForm.mul recovered as compositions. The
degree-coupling op (IsImage's `.map` on the continuous side) is built — both halves of the program
now exhibit "structure factors; the cross-level coupling carries the content."

Multi-input/general DONE [`MvForm.lean`]: the GENERAL multivariate Taylor model `MvForm R n` (ideal
= `MvPolynomial (Fin n) R`, value = `eval x P`). Since `eval` is a RING HOM, **add AND mul are both
EXACT** (no leak, no X) — polynomials closed under +,×. **Punchline: the leak was never intrinsic to
`×`, only to fixing the degree.** All the fixed-degree forms = `MvForm` restricted to bounded total
degree; their leak = the cost of truncating `MvForm.mul`'s exact result back down. The continuous
hierarchy is now topped out: MvForm (general) ⊃ PolyForm d ⊃ AffineForm/QuadForm; AffineFormVec.

LOOP CLOSED [`PolyForm.mul_truncateOne_value` + `mulCoeff_last_two`]: truncating the EXACT degree-2
product of two degree-1 forms back to degree 1 drops *exactly* `(slope·slope)·x²` = exactly the
affine `mul` leak — proved as an **equality** (`rw` to rfl), not a bound-by-analogy. So "the leak =
degree-truncation; `×` only leaks because the degree is fixed" is now a theorem, not a thesis. The
continuous hierarchy is complete *and* closed: general (`MvForm`, exact) → fixed-degree
(`PolyForm`/`Affine`/`Quad`) is literally the truncation, and the leak is its residue.

Core program complete (discrete `IsImage` + continuous `MvForm`-tower, both "structure factors;
cross-level coupling carries content"). **NEW THREAD (2026-06-15): probabilistic / RG physics** —
the chosen dramatic-enhancement vector. The reframing: this whole stack is *certified abstract
interpretation of FP*, and the loop-closing exposed **renormalization-group structure** (MvForm=UV-
complete; fixed-degree=effective theory; truncate=integrate out; leak=irrelevant operators ~`X^k`;
IsImage residues=conserved charges; err/η=cutoff; snapping=gap). The probabilistic layer is where
`err` becomes a *fluctuation scale* (variance/temperature) rather than a hard bound. First brick
shipped: `Flean/Operations/ProbError.lean` — the **√n law** (`variance_sum_le` quadrature +
`concentration` Chebyshev: typical rounding error `~√n·σ`, a `√n` win over worst-case `n·σ`; rounding
is noise and noise cancels). This is the statistical-mechanics version of error accumulation, on
Mathlib probability.

Open frontier (probabilistic/RG): connect σ↔η (bounded mean-zero ⇒ Var≤(η·scale)²); martingale/Azuma
for round-to-nearest; output-distribution (≈Gaussian) shadows; formalize (α,γ) Galois connection +
tower-as-RG-flow (running couplings, universality = "different nets, same effective theory",
relevant-vs-irrelevant = interpretability). Also open: n-ary `dotN`; grounded numeric examples.

**UPDATE 2026-06-15 (session 2) — σ↔η bridge + Gaussian fluctuations DONE.** `ProbError.lean` grew:
(a) **σ↔η bridge** `variance_le_sq_of_abs_le` (bounded mean-zero ⇒ Var ≤ b², via Mathlib Popoviciu
`variance_le_sq_of_bounded`; mean-zero not even needed for the *variance* bound) — ties the abstract
`σ` to the FP rounding unit `η·scale`, so the √n law is now literally about floating point.
(b) refactor: `concentration_of_variance_le` engine (any `Var≤V` ⇒ Chebyshev), with `concentration`
(√n) as a corollary. (c) FP statements: `concentration_fp` (uniform scale, `1/k²` tail) +
`concentration_fp_vec` (per-term, aggregate = **ℓ² norm** `√(∑scaleᵢ²)`, not ℓ¹ — the quadrature
made explicit). (d) **Gaussian fluctuations** (most of brick #3): `concentration_fp_subgaussian`
(one-sided) + `_abs` (two-sided) — bounded mean-zero rounding errors are **sub-Gaussian** (Mathlib
Hoeffding `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` + `measure_sum_ge_le_of_iIndepFun`), so
the accumulated error has an **exponential** tail `exp(-k²/2)` (vs Chebyshev's polynomial `1/k²`).
This is the rigorous form of "rounding ≈ Gaussian noise": the fluctuations concentrate like a Gaussian
at scale `η·√n·scale`. Independence required (iIndepFun); round-to-nearest's dependence (martingale
Azuma, `measure_sum_ge_le_of_HasCondSubgaussianMGF`) is the remaining brick #2.

**VERDICT on the meta-question** ("is rounding-error analysis = statistical mechanics/RG of FP a
*proved* principle or a productive analogy?"): **partly proved, partly program — and the proved part
is the statistical-mechanics core.** Proved as theorems: `err` *is* a fluctuation scale (σ↔η);
fluctuations *cancel* (√n quadrature, the law of large numbers for the reduction); fluctuations are
*Gaussian* (sub-Gaussian exponential concentration — the CLT/temperature picture). So "rounding =
noise, error analysis = its statistical mechanics" is now **proved**, not analogy. The *RG-flow* half
(running couplings = truncated-coefficient flow in `X`; universality = different microscopic FP
computations → same effective shadow; relevant/irrelevant = `X^k` suppression ↔ interpretability)
remains a structural dictionary, not yet theorems — that is the honest boundary. Statistical mechanics
of FP: proved. Renormalization *group* (the flow/β-function): still program. Settled exactly as
`AbstractFp` was settled by building `IsImage`: the part that factored into theorems, did.

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

**BUILT 2026-06-15** (`Flean/Operations/ScaledIntSnap.lean`): the snapping bridge is concrete.
`round_eq_of_abs_sub_lt_half` (`|v−n|<½ ⇒ round v = n`) + `ScaledInt.round_eq_of_value_int`
(ideal value = integer `N` ∧ `err < ½` ⇒ `round fp = N`) reduce an *inexact* `ScaledInt` to a
precise integer; `snap_image`/`snap_residue` then recover every structural shadow (any CommRing
`S`, mod-`p`) below the `½` gate. The α here is literally `½` (scale-0 / unit lattice); the
general "`err < ½ ulp at scale s`" form is `round_eq_of_value_int` with the ideal an integer at
that scale. This is the inexact pillar → discrete-shadow link, so a real FP modular net routes:
accumulate `err` on `ScaledInt` → check `err < ½` → snap → `IsResidue`.

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

---

## Verdict on the framework question (2026-06-15, after building mod-p)

Shipped `Flean/Operations/ExactIntModP.lean`: `IsResidue p r a := (a.n : ZMod p) = r`, total-op
propagation (`isResidue_zero/one`, `IsResidue.neg`), partial-op propagation
(`IsResidue.add/sub/mul`), the abstract headline `IsResidue.dot2`, and the fully-concrete
`dot2_residue_mod7` (`3·4+2·5 ≡ 1 mod 7`, inputs' integers + bit patterns left abstract). Every
propagation proof is **one `rw` chain**: `add_n`/`mul_n`/`neg_n` (definitional) + `Int.cast_{add,
mul,neg}`. ~5 lines each.

**The decisive finding: mod-p is a *pure post-composition* domain — it has no transformer of its
own.** It does NOT define its own `add`/`mul`; it *reuses `ExactInt`'s* verbatim (calls
`a.add b hbound h_exp` etc.) and only maps the shadow through the ring hom `Int.cast : ℤ → ZMod p`.
Consequently:

- **It adds zero new preconditions.** The residue is defined unconditionally on `.n`; mod-p
  inherits ExactInt's `hbound`/`h_exp` wholesale (same side conditions, same args, threaded
  unchanged). So mod-p does *not* stress "preconditions don't factor" (Decision 2) — it sidesteps
  the problem by not having a transformer to give a precondition.
- **What it shares with `ExactInt` is exactly the `.n` ring hom — nothing else.** The entire
  domain = "post-compose `.n` with a ring hom out of `ℤ`."

So the explicit `AbstractFp` (γ + per-domain sound transformer) is **still not worth building** —
mod-p didn't exercise the transformer/precondition machinery at all. But mod-p *did* reveal the
right light abstraction for **structural domains derived from the precise pillar**: not a
Galois-connection typeclass, but a **"ring-hom image of the exact shadow" helper** —
`IsImage (φ : ℤ →+* S) (s : S) (a : ExactInt R) := φ a.n = s`, with generic add/mul/neg/zero/one
propagation proved *once* (φ is a ring hom ⇒ commutes with everything). That single helper would
subsume mod-p, parity/sign-mod-2, mod-q, CRT products `ℤ → ZMod p × ZMod q`, any quotient or
image of the integer shadow. mod-p as written is the concrete instance `φ = Int.cast`.

**Recommendation:** documented pattern + the light `IsImage`/ring-hom-out-of-`.n` helper is the
right call. Note the scope limit: this helper covers domains that are **homomorphic images of the
exact integer shadow**. Structural domains that are *not* ℤ-ring-hom images (order-theoretic:
exact sign as a 3-valued lattice, monotonicity, periodicity-of-a-sequence) won't factor through
it and remain genuinely separate — so even the light helper is a *family* abstraction, not a
universal one, which reconfirms rejecting the heavy `AbstractFp`.

**Scope limit now DEMONSTRATED, not just asserted (2026-06-15, `ExactIntSign.lean`).** Built the
exact-sign domain `HasSign s a := SignType.sign a.n = s` — the first non-ring-hom shadow. Findings
sharpen the framework picture concretely: the sign carrier `{−1,0,+1}` is a *multiplicative*
monoid-with-zero (`signHom : ℤ →*₀ SignType`), not a ring. So **the split runs through a single
shadow, not just between shadows**: `×` factors like a hom (`HasSign.mul`, unconditional in the
signs — exact analogue of `IsImage.mul`), while `+` does *not* (only the diagonal `add_same`, or
`add_dominant` which needs magnitude `|b.n|<|a.n|`). Sign closes under `+` only as a **reduced
product with the magnitude domain** — the abstract-interpretation concept (reduced product) the
framework question kept circling. This is the deepest reason a uniform `AbstractFp` with one
`add_sound`/`mul_sound` pair is wrong: even *within* one domain, the two operations want different
machinery and different preconditions. The multiplicative half hints at a *parallel* light helper
`IsMulImage (φ : ℤ →*₀ M)` (factoring zero/one/mul/neg) — deferred until a 2nd multiplicative
instance, mirroring the `IsImage` discipline.

## Strategic read (2026-06-15): the missing quadrant

After the discrete corner (mod-p, sign, sign×mag reduced product, snapping), a top-down look:

**1. Everything so far is synthetic.** Every headline (`dot2_residue_mod7`, `dot2_pos`,
`add_stays_pos`) is on *abstractly-specified integer inputs*. The reduction stack is a fully-built
language that has **never been pointed at a real computation.** We built the grammar; we haven't
spoken a sentence about anything that exists.

**2. The corner is narrow vs the vision.** The exact-integer shadow is exact integer arithmetic
inside FP — a narrow phenomenon. Real ML is continuous and approximate. The design's *other*
family — metric/continuous **structural** domains (near-affine, near-shape: "this region ≈ a known
function") — is where the reductionist payoff lives, and we've built **zero** of it. We have lots
of approximate-pillar *value-fidelity* (`ScaledInt`+`err`) but no approximate-pillar *structure*.
That empty quadrant is the important one.

**3. Abstract interpretation is already the implicit spine — built twice.** The Tags framework
(`HasAbsBound`=magnitude/interval, `IsBoundedRange`, `IsNonneg`, with propagation theorems) *is*
abstract interpretation on real-valued FP, and it's what the big analyses (softmax, MLP layer)
actually run on. `IsNonneg` is literally the positive cone of the new sign domain, one pillar
over; `HasAbsBound` is `HasSignMag`'s magnitude factor on the real side. So AI isn't a new toy —
it's the spine of the whole library, instantiated in two disconnected places (Tags = metric on
real FP; exact-int = discrete on integer FP), with the discrete one the small validated copy.

**4. The sign domain is secretly about ReLU regions.** A ReLU net is piecewise linear; *which*
piece is the sign pattern of pre-activations. `HasSign` + `HasSign.pos` + the existing bit-level
`relu` work are the pieces of a linear-region extractor — a real ML primitive that lives at the
*intersection* of the two domain systems (signs pick the region; the region is an affine map you'd
bound with Tags). It's the natural forcing function for the unification.

**The three directions (fundamental → consolidation):**
- **(A) Build the missing quadrant** — a continuous near-affine domain on the approximate pillar,
  `|f − (A·x+b)| ≤ ε`, sound + composable, with `err` *composition* (not snapping) as the
  mechanism. The actual "extract the idea" engine; the real test of the framework jumping from
  discrete-exact to continuous-approximate. **← chosen.**
- **(B) Anchor to a real primitive** — ReLU linear-region extraction (sign pattern ⇒ provable
  local affine map). The first true sentence; drags (A) and the Tags-unification in behind it.
- **(C) Make the spine explicit** — bridge `HasSign↔IsNonneg`, `HasSignMag↔HasAbsBound`; state
  once that Tags + exact-int are one AI framework. Reframes 47k lines; organizing, not new math.

**Decision: build (A).** The first inhabitant is an **affine form** (affine-arithmetic / degree-1
Taylor model): a value whose ideal is `a·x + b` (vs `ScaledInt`'s constant `m·2^s` ideal), with
`|fp.toVal − (a·x+b)| ≤ err`. The err-composition transformer is **shape-agnostic** — the same
forward-error triangle `ScaledInt` uses works for any ideal real value (the `m·2^s` was
incidental), so the affine domain *reuses the transformer, changes the shadow*: exactly this
note's thesis (shared sound transformer, many γ). The conceptual payoff that makes it more than
"ScaledInt with extra fields" is the **dual of the discrete story**: affine closes under `+`
(coefficients add) but **not under `×`** — the product's quadratic term leaks into `err`, bounded
only with a *magnitude bound on the input* `|x| ≤ X` (a reduced product with an interval on x,
mirroring `HasSignMag`). "+ closes, × leaks" is the metric mirror of sign's "× closes, + leaks."

---

**Reduced product BUILT (2026-06-15, `ExactIntSignMag.lean`).** The `add`-doesn't-close seam the
sign domain exposed is discharged by the predicted construction: `HasSignMag s lo hi a` = sign ∧
magnitude interval `[lo,hi]`, the **meet** of the two factor domains (projects to each). On it
`add` is *total* — `add_dominant` certifies the sign of a sum even across opposite signs given
magnitude separation `hi_b < lo_a`, the closure neither factor has alone. This is the first
reduced product in the stack and the concrete confirmation of the abstract-interpretation read:
**domains compose by meet / reduced product, not by a uniform `AbstractFp` transformer.** The
operad of this area is now: ring-hom-image structural domains (`IsImage` family), the
multiplicative monoid-hom domain (`HasSign`), the magnitude domain (`ExactIntB`), and their
reduced products (`HasSignMag`) — each a point/meet in the abstract-interpretation lattice over
`ExactInt`, with the snapping bridge linking in the approximate pillar.

### `IsImage` BUILT (2026-06-15, same session — the second case validated it)

Rather than defer, built the helper immediately with a genuinely-different second instance to
poke it. `IsImage (s : S) (a : ExactInt R) := (a.n : S) = s`, generic over any `[CommRing S]`.

The clinching simplification: **ℤ is initial in `CommRing`, so the ring hom out of ℤ is *unique*
(= `Int.cast`) and a domain in this family is determined entirely by the target ring `S`.** No
`φ` parameter needed — index by `S` alone. Generic propagation (`isImage_zero/one`,
`IsImage.neg/add/sub/mul/dot2`) proved once via `Int.cast_*` + the `.n` ring-hom lemmas.

Instances, each needing **zero propagation proofs of its own** (pure delegation — the
abstraction's keep, earned):
- `IsResidue p r a := IsImage r a` at `S = ZMod p` — mod-p, recovered as a special case; all its
  lemmas are one-line `:= IsImage.foo …` delegations.
- `IsResiduePair p q r a := IsImage r a` at `S = ZMod p × ZMod q` — CRT / simultaneous residues,
  the second structurally-different target.

The payoff mod-p alone couldn't show: **functoriality** `IsImage.map (g : S →+* T) : IsImage s a
→ IsImage (g s) a` (proof = `g` commutes with `Int.cast`, one `rw [map_intCast]`). It makes the
family a *category*: the single CRT pair-shadow projects to mod-p and mod-q via `RingHom.fst`/
`snd` — `dot2_residue_crt_3_5` derives `≡1 mod 3` ∧ `≡1 mod 5` from one `IsResiduePair.dot2`
result by two `.map`s. **Verdict confirmed by construction:** the light `IsImage` helper is the
right abstraction; `AbstractFp` (transformer + per-domain precondition) was never needed — all
these domains *share ExactInt's transformer and preconditions verbatim* and differ only in the
post-composed ring hom.
