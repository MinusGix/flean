# Exact-Integer Reduction (Flean reductionist thread)

## Active concrete target (2026-07-21)

The reduction stack now has a selected first literal network: a two-input, two-hidden-unit ReLU
network computing XOR,

```text
h₁ = ReLU(x + y)
h₂ = ReLU(x + y - 1)
out = h₁ - 2 h₂.
```

For exactly encoded Boolean inputs, the intended headline is that the actual FP operation trace
reduces through bounded integer arithmetic and sign-bit ReLU to Boolean XOR. This is deliberately a
concrete calibration theorem, not a new generic network API. It uses existing length-two/exact-int
machinery and avoids making `dotN` a prerequisite. The follow-up target is a fixed binary-weight
neuron/network reduced to XNOR + popcount + threshold.

Full design and completion criteria: `docs/range_conditioned_circuit_reduction.md`.

**LANDED 2026-07-21.** `Flean/Operations/RangeReduction/XorNet.lean` carries the literal FP trace
through bounded exact integers and sign-bit ReLU, with `eval_n_eq_xor` as the generic headline.
`XorNetBinary32.lean` discharges the format contract and proves `Binary32.fpEval_eq_fpBit`: the
actual Binary32/RNE program returns the canonical encoded XOR bit. The concrete proof extracted
only `ExactIntB.withBound` and `ExactIntB.relu`; it did not require `dotN` or a generic net API.
Next research target: a fixed binary-weight neuron reduced to XNOR + popcount + threshold.

The first **range-conditioned reduction** piece (see `research-vision.md` — Flean's
"floats as integer/circuit substrate" soul). Goal arc: handcraft concrete exact-integer
reductions → generalize "what range behaves simply" → eventually extract "this float net
is really doing integer/modular arithmetic" (the **modular-arithmetic-network** target).

## Shipped (2026-06-14/15)

Pre-existing base (someone earlier): `Flean/Operations/ExactInt.lean` — per-op exactness
`fpAddFinite_int_exact` / `fpSubFinite_int_exact` / `fpMulFinite_int_exact`: integer-valued
floats with result a *nonzero* integer in `(-2^prec, 2^prec)` ⇒ op is exact. Each returns
`∃ f, op = f ∧ f.toVal = n`.

`Flean/Operations/ExactIntCompose.lean` was a transient "friction exhibit" (handcrafted
chained reductions); **deleted** once the algebra subsumed it.

New this session:
0. `Flean/Operations/ExactIntZero.lean` — **zero-admitting** per-op exactness
   (`fpAddFinite_int_exact0` / `fpMulFinite_int_exact0` / `fpSubFinite_int_exact0`): drops
   the `≠ 0` result hypothesis. Zero result lands on a finite signed zero (add: via
   `fpAddFinite_exact_cancel_sign` after deriving `addAlignedSumInt = 0` from
   `fpAddFinite_exact_sum`; mul: `roundIntSigM _ 0 _ = Fp.finite (signed 0)` after
   `a.m*b.m = 0`; sub: reduces to add-of-neg). Nonzero case delegates to the base lemmas.
2. `Flean/Operations/ExactIntBound.lean` — `ExactIntB R` (extends `ExactInt R` with a
   running magnitude bound; see Deferred §2 below for details). The interval layer.
1. `Flean/Operations/ExactIntAlgebra.lean` — `ExactInt R` structure carries
   the float as **honest data** (`fp : FiniteFp`, `n : ℤ`, `agree : fp.toVal = n`), no `∃`.
   - `Fp.toFiniteOr0` — total `Fp → FiniteFp` extraction (default 0) so op outputs (type
     `Fp`) are carried as literal `FiniteFp`.
   - Total instances `Zero`/`One`/`Neg` (negation never overflows).
   - Partial `def`s `mul`/`add`/`sub` (take just `< 2^prec` bound + `h_exp`; **no `≠ 0`** —
     route through the `_int_exact0` lemmas, so zero results are welcome). No total
     `Mul`/`Add` instance — overflow forbids it; `ExactInt` models `ℤ ∩ (-2^prec,2^prec)`.
   - **Homomorphism = the reduction**: `.n` commutes with every op (`mul_n`/`add_n`/`sub_n`/
     `zero_n`/`one_n`/`neg_n`, all `rfl`). "Float computation = integer computation" as one
     law.
   - **Provenance bridges**: `mul_fp`/`add_fp` — `(a.mul b _).fp = fpMulFinite a.fp b.fp`
     (the carried float is exactly what the op computes; nothing invented).
   - Payoff: `dot2` is one composed term; `dot2_n` (= integer dot product) is `rfl`.

All sorry-free; wired into `Flean/Operations.lean`; full build green.

## Deferred — next sub-pieces (in order)

1. ~~**Zero-admission**~~ — DONE 2026-06-15 (`ExactIntZero.lean`; algebra side-condition-free
   on zero). ("zero-tolerance" was the working name; "zero-admitting" is the honester one —
   we *welcome* zero, not tolerate it.)
2. ~~**Running magnitude bound**~~ — DONE 2026-06-15 (`ExactIntBound.lean`). `ExactIntB R`
   `extends ExactInt R` + `bound : ℕ` + `hbound : |n| ≤ bound`. Bound propagates: mul →
   `bₐ·b_b`, add/sub → `bₐ+b_b`, neg → `bₐ`; each op *derives* its `< 2^prec`
   representability from the propagated bound (via `Int.natAbs_mul`/`Int.natAbs_add_le`/
   `Int.natAbs_sub_le`). Total `Zero`/`One`/`Neg`. Payoff: `ExactIntB.dot2` takes a
   **single** representability hypothesis `bₐ₁·b_b₁ + bₐ₂·b_b₂ < 2^prec` (implies each
   product fits AND the sum fits, summands nonneg). `dot2_n`/`dot2_bound` by `rfl`.
3. **n-ary sum / `dotN`** (available follow-up, no longer a prerequisite for the concrete target).
   `List (ExactIntB R)` fold with a single
   running-bound hypothesis; the bound bookkeeping is now a fold over `bound`. Natural
   bridge to matvec.
4. **Concrete net — ACTIVE**. Implement the XOR network above, propagate its exact ranges via
   `ExactIntB`, and extract its Boolean behavior from the literal FP trace.

## Fixed-point / correction layer (the inexact frontier — started 2026-06-15)

Crossing from exact to "simpler form + bounded correction" (the reductionist payoff:
"multistep float ops → integer fn + minor correcting factor"). Staged as exact-first.

SHIPPED — `Flean/Operations/ScaledExact.lean` (the exact on-ramp): widens `ExactInt` from
integers to **fixed-point** `m · 2^s` (common scale `s`; `ExactInt` = `s=0`). Leans on
`exists_finiteFp_of_int_mul_zpow` (ToVal.lean) for scaled representability. Pieces:
`scaled_round_exact` (scaled `int_round_exact`), `fpAddFinite_scaled_exact` (same-scale
add), `fpMulFinite_scaled_exact` (scales add: `s_a + s_b`), `structure ScaledExact`
(fp, m, s, agree: `fp.toVal = m·2^s`), `value`/`value_eq_toVal`. Sorry-free, in aggregator.

SHIPPED — `Flean/Operations/ScaledCorrection.lean` (the C-teeth): `fpAddFinite_scaled_correction`
/ `fpMulFinite_scaled_correction`. Float op on exact common-scale inputs `= (integer op on
significands)·2^scale + correction`, `|correction| ≤ η·|value| + 2^(min_exp-prec)`. Exact
when the result fits (correction 0, via the `ScaledExact` lemmas); bounded otherwise.

CORRECTION TO EARLIER FINDING: a **generic** round-error bound DID already exist — I'd
grepped the wrong file. `round_preserves_abs_error_unified` (`Rounding/RoundPreserves.lean`)
is generic over **any nearest mode** `[RModeNearest R]` (both RNE and RNA provide it), needs
**no** `isNormalRange` (subnormals → the `2^(min_exp-prec)` tail), and gives `|f.toVal - x| ≤
η·|x| + 2^(min_exp-prec)`. So the correction op was just *applying* it — not policy-locked,
not normal-range-gated. (The mode-specific `roundNearestTiesToEven_abs_error_le_ulp_half` in
`RelativeErrorBounds.lean` gives the cleaner `≤ ½ ulp` form if a tighter/ulp-shaped bound is
wanted later.)

SHIPPED — `Flean/Operations/ScaledInt.lean` (the composing inexact layer): `ScaledInt R` =
`fp : FiniteFp` + ideal `(m, s)` + `err : R` + `herr : |fp.toVal - m·2^s| ≤ err`. `ofExact`
(err=0 base), `value`. Building-block theorem `fpAddFinite_scaled_inexact` (forward-error
triangle: new error = input errors + this op's rounding correction, bounded against the
ideal magnitude). `ScaledInt.add` (same-scale, takes finite-result `g` + nonzero-sum
witness) grows err by `(1+η)(err_a+err_b) + η|value| + 2^(min_exp-prec)`. `add_m/s/fp` simp.
This is forward error in fixed-point coordinates — the reduction extended from one op to a
chain.

UPDATE 2026-06-15: `ScaledInt.mul` SHIPPED (`fpMulFinite_scaled_inexact` — product-error
propagation `|ideal_a|·err_b + err_a·|ideal_b| + err_a·err_b` + the op's rounding; scales
add). Smarter `add`/`mul` SHIPPED: result float computed via `Fp.toFiniteOr0` (helper
`Fp.eq_finite_toFiniteOr0 : x.isFinite → x = Fp.finite x.toFiniteOr0` added in
`ExactIntAlgebra.lean`), caller supplies only an `isFinite` Prop + nonzero — no explicit
result-float witness.

UPDATE 2026-06-15: finiteness-from-bound SHIPPED. `round_isFinite_of_abs_le_largest`
(generic, `RModeMono` + `RModeIdem`: `|x| ≤ largestFiniteFloat ⇒ (○x).isFinite`; signed
analogue of Softmax's nonneg `round_exists_finite_of_*` — could be promoted to `Rounding/`).
`ScaledInt.addOfBound` / `mulOfBound`: take a no-overflow magnitude bound on the float
sum/product instead of an `isFinite` Prop, deriving finiteness internally. Gotcha logged:
the FiniteFp-add vs Fp-add coercion forms differ syntactically — `rw [fpAddFinite_correct]`
on the goal LHS fails; instead `rwa [← fpAddFinite_correct ...] at h` (match the unambiguous
`○ sum` RHS in a hypothesis).

UPDATE 2026-06-15: (a) `round_isFinite_of_abs_le_largest` PROMOTED to
`Rounding/RoundPreserves.lean` (generic, was in ScaledInt). (b) `add_err`/`mul_err` simp
accessors added. (c) **chain demo SHIPPED**: `ScaledInt.chain_two_adds_err` — two chained
adds on exact (`err=0`) inputs gives `η(1+η)·|first sum| + η·|total| + (2+η)·2^(min_exp-prec)`
by `simp + ring`, making the accumulation visible (two rounding contributions, first
amplified by `(1+η)`).

NEXT (this layer): (1) zero-sum handling. (2) n-ary `dotN`/list-fold (the bound bookkeeping
is now ready). (3) `ScaledExact` `sub`/`neg`. (4) the concrete modular-arith net (the
aspirational target — now has the full exact+inexact+bound stack under it).

UPDATE 2026-06-15 (mod-p — first STRUCTURAL domain): `Flean/Operations/ExactIntModP.lean`
shipped. `IsResidue p r a := (a.n : ZMod p) = r` on the precise pillar. Total-op props
(`isResidue_zero/one`, `IsResidue.neg`), partial-op props (`IsResidue.add/sub/mul`, reusing
ExactInt's `add/mul/sub` verbatim + their `hbound`/`h_exp`), abstract headline
`IsResidue.dot2`, concrete `dot2_residue_mod7` (`3·4+2·5 ≡ 1 mod 7` from input residues alone,
integers + bit patterns abstract). Every prop = one `rw` chain over `*_n` (definitional) +
`Int.cast_{add,mul,neg}` — mod-p is the ring hom `ℤ → ZMod p` post-composed onto the existing
`.n` ring hom, so it propagates for free. **Framework verdict recorded in
`exact-int-design.md`:** mod-p is a *pure post-composition* domain (no transformer of its own,
zero new preconditions) ⇒ explicit `AbstractFp` still not worth it; the right light
abstraction is a generic `IsImage` helper over `.n` (subsumes mod-p, parity, mod-q, CRT).
Order-theoretic structural domains (exact sign lattice, periodicity) won't factor through it.

UPDATE 2026-06-15 (same session — `IsImage` BUILT + CRT 2nd instance validates it): instead of
deferring, generalized immediately. Key simplification: **ℤ initial in CommRing ⇒ the hom out of
ℤ is unique (`Int.cast`), so index the family by the target ring `S` alone** — no `φ` parameter.
`IsImage (s : S) (a : ExactInt R) := (a.n : S) = s` over any `[CommRing S]`; generic
`isImage_zero/one`, `IsImage.neg/add/sub/mul/dot2` proved once. `IsResidue` (S=ZMod p) and
`IsResiduePair` (S=ZMod p × ZMod q, CRT) are instances with **zero propagation proofs of their
own** (one-line `:= IsImage.foo` delegations). Functoriality `IsImage.map (g : S →+* T)` (proof =
`map_intCast`, one rw) makes it a category: `dot2_residue_crt_3_5` derives `≡1 mod 3` ∧ `≡1 mod 5`
from one `IsResiduePair.dot2` via two `.map`s through `RingHom.fst`/`snd`. Verdict confirmed by
construction. All in `Flean/Operations/ExactIntModP.lean`, sorry-free.

UPDATE 2026-06-15 (S=ℤ terminal point + SNAPPING BRIDGE — the inexact pillar now reaches the
discrete shadows). (a) **S=ℤ instance** in ExactIntModP.lean: `IsExactly n a := IsImage n a` at
`S=ℤ` (identity hom) = `ExactInt`'s own integer = lattice top. `isExactly_iff` (↔ `a.n = n`),
`isExactly_self`, and the universal factoring `IsExactly.toImage : IsExactly n a → IsImage (n:S)
a` (every coarser shadow specializes it) + `IsExactly.toResidue`. Makes "domains form a lattice,
ExactInt on top" literal. (b) **Snapping bridge** = new file `Flean/Operations/ScaledIntSnap.lean`
(imports ScaledInt + ExactIntModP + Mathlib round). Pure recovery `round_eq_of_abs_sub_lt_half`
(`|v-n|<½ ⇒ round v = n`, via `round_eq`+`Int.floor_eq_iff`). `ScaledInt.round_eq_of_value_int`
(ideal value = integer N ∧ `err<½` ⇒ `round a.fp.toVal = N`) + `_of_scale_zero`. Generic
`snap_image` (snapped integer's image in ANY CommRing S = N's — mirrors IsImage genericity) +
mod-p headline `snap_residue` (`(round a.fp.toVal : ZMod p) = (N : ZMod p)`). The `½` = the design
note's "discretization α": below it the discrete structure survives FP noise, above it it's lost.
This closes the approximate→precise pillar gap for discrete domains. All sorry-free.

UPDATE 2026-06-15 (exact-SIGN — first NON-ring-hom structural domain; tests the framework
boundary): `Flean/Operations/ExactIntSign.lean`. `HasSign (s : SignType) a := SignType.sign a.n =
s`. Sign carrier `{−1,0,+1}` is NOT a ring (not closed under `+`), so sign can't be an `IsImage`
instance — it's a *multiplicative* monoid-with-zero hom (`signHom : ℤ →*₀ SignType`). The split
this exhibits = the framework lesson: **`mul` factors like a hom** (`HasSign.mul` via `sign_mul`,
no side conditions on signs — exact analogue of `IsImage.mul`; plus total `zero/one/neg`), but
**`add` does NOT factor** — only the diagonal `HasSign.add_same` (equal signs preserved,
conditional on signs *agreeing*, via pure helper `sign_add_of_sign_eq`) and the off-diagonal
`HasSign.add_dominant` which needs a *magnitude* hyp `|b.n|<|a.n|` (`sign_add_of_abs_lt`). So sign
closes under `+` only as a **reduced product with the magnitude domain (`ExactIntB`)** — even
within ONE shadow, `+` and `×` want different machinery (this is *why* uniform `AbstractFp` was
wrong). Bridges: `HasSign.pos` (HasSign 1 ⇒ `0 < fp.toVal`, genuine float fact). Headline
`dot2_pos`: all-positive integer dot product is provably positive (sign from sign alone —
ReLU/loss-positivity flavour). **Framework note**: the multiplicative half suggests a parallel
light helper `IsMulImage (φ : ℤ →*₀ M)` (would factor zero/one/mul/neg), but the additive half
escapes it — NOT building it yet (1 instance; mirror how `IsImage` waited for mod-p's 2nd case).
Scope-limit claim from design.md now demonstrated, not just asserted. All sorry-free.

UPDATE 2026-06-15 (sign × magnitude REDUCED PRODUCT — first reduced product in the stack;
discharges the `add` seam exposed by exact-sign): `Flean/Operations/ExactIntSignMag.lean`.
`HasSignMag s lo hi a := SignType.sign a.n = s ∧ 0 ≤ lo ∧ lo ≤ |a.n| ∧ |a.n| ≤ hi` — the **meet**
of the sign shadow and a magnitude interval (projects via `toSign` to `HasSign`, via `le_hi` to
the ExactIntB-style upper bound). The point: `add` is now **total** (no same-sign precondition),
because the magnitude data decides the off-diagonal. Ops: `HasSignMag.mul` (sign mults, interval
`[lo_a·lo_b, hi_a·hi_b]`, uncond), `.add_same` (equal signs, `[lo_a+lo_b, hi_a+hi_b]`, magnitudes
add exactly via pure helper `abs_add_of_sign_eq`), **`.add_dominant`** (the payoff: signs may
OPPOSE; `hi_b < lo_a` ⇒ result takes dominant's sign, interval `[lo_a−hi_b, hi_a+hi_b]`; uses
`sign_add_of_abs_lt` + `abs_sub_abs_le_abs_sub` for the lower bound). Total `zero/one/neg`.
Headline `add_stays_pos`: dominant positive + ANY value (any sign) of magnitude ceiling < the
positive's floor stays positive — opposite-sign addition certified, which neither factor domain
can do alone. This realizes the "reduced product" the exact-sign session flagged: confirms the
abstract-interpretation read (domains compose by meet/reduced-product, not by a uniform typeclass)
concretely. All sorry-free.

UPDATE 2026-06-15 (MISSING QUADRANT planted — first CONTINUOUS STRUCTURAL domain on the
approximate pillar): `Flean/Operations/AffineForm.lean`. See the strategic read added to
`exact-int-design.md` (everything prior was synthetic / discrete-exact; the vision's payoff is
continuous-approximate *structure*, which was empty; AI is already the implicit spine, built twice
— Tags for metric, exact-int for discrete; sign domain is secretly ReLU regions). `AffineForm R` =
float `fp` + affine ideal `a·x+b` (slope/intercept/input) + `err`, invariant `|fp.toVal−(a·x+b)| ≤
err` — `ScaledInt` with the constant ideal `m·2^s` replaced by an AFFINE ideal (degree-1 Taylor /
affine-arithmetic form). Two payoffs delivered: (1) **shape-agnostic transformer** —
`fpAddFinite_inexact_general` generalises `fpAddFinite_scaled_inexact` to ANY ideal real values
`i_a,i_b` (the `m·2^s` was incidental; ScaledInt is the `i:=m·2^s` instance), so the err-composition
machinery is REUSED, only the shadow changes — design-note thesis (one transformer, many γ) made
literal. (2) **"+ closes, × leaks" — metric dual of sign's "× closes, + leaks"**: `AffineForm.add`
(same x) adds coefficients `(a₁+a₂)x+(b₁+b₂)`, err via the generic transformer, `add_value` =
sum of ideals (`+` exact on the shadow); pure headline `affine_mul_nonlinearity` shows
`(a₁x+b₁)(a₂x+b₂)` = linear part + quadratic residual `a₁a₂x²`, bounded `≤|a₁a₂|·X²` given `|x|≤X`
— `×` leaves the affine domain, closing it needs a REDUCED PRODUCT with an interval on the input
(mirrors HasSignMag). ReLU-region motivation noted (fixed activation region ⇒ layer exactly affine
⇒ AffineForm with FP-only err is the verified-local-linear-region carrier). All sorry-free.

UPDATE 2026-06-15 (`AffineForm.mul` — `×` CLOSED via reduced product): `fpMulFinite_inexact_general`
(shape-agnostic multiplicative transformer, generalises `fpMulFinite_scaled_inexact` to arbitrary
ideals i_a,i_b — bounds float product vs EXACT product of ideals; ScaledInt/AffineForm both
instantiate). `AffineForm.mul p q (hx: p.x=q.x) (X) (hX:|p.x|≤X) hprod_ne hfin`: result ideal =
the **linearization** `(p.a·q.b+q.a·p.b)·x + p.b·q.b` of the product (NOT p.value·q.value); err =
[FP mul propagation via the generic transformer] + the quadratic leak `|p.a·q.a|·X²`. So `×`
closes ONLY by importing the input-magnitude bound X (reduced product with an interval on the
input — the metric mirror of HasSignMag importing magnitude to close `+`). Accessors `mul_a/b/x/
fp/value` + `mul_value_sub_prod` (|linearization − true product| ≤ |p.a·q.a|·X², making explicit
the affine ideal is the linearization off the true product by the bounded nonlinearity). Affine
domain now has both ops: `+` exact-on-shadow, `×` linearize-and-absorb. All sorry-free.

UPDATE 2026-06-15 (ReLU LINEAR REGIONS — direction B, FIRST real ML primitive the apparatus
touches): `Flean/Operations/AffineRelu.lean`. Composes `AffineForm` (continuous affine shadow) with
the sign of the pre-activation (the existing `Fp.fpRelu`, `fpRelu_finite_eq` from
IntegerEquivalence/ReluBits) to recover "a ReLU net is piecewise affine" FROM the FP operator, not
assumed. Per-region (sign bit `z.fp.s` picks the region): **active** (`z.fp.s=false`, pre-act ≥0):
ReLU = identity (`fpRelu_active`), output tracks the SAME affine ideal `a·x+b` within `z.err`
(`relu_active_tracks`); `reluActive` packages the output back as an `AffineForm` (same a/b/x/err,
fp = actual ReLU output) so a network reasons in the affine domain ACROSS the ReLU as long as the
region holds (`reluActive_value` = z.value). **inactive** (`z.fp.s=true`, pre-act <0): ReLU = exactly
0 (`fpRelu_inactive`, `relu_inactive_zero`). The KINK (region boundary, `z.fp.s` flips) is exactly
where the affine description breaks = the nonlinearity, the ReLU analogue of mul's quadratic leak.
Faithful: within a region affine, at the boundary structure-change. This is the discrete×continuous
interface concrete (sign picks region → affine map within). All sorry-free.

UPDATE 2026-06-15 (TAGS UNIFICATION — direction C, the two abstract-domain systems are ONE
lattice): `Flean/Tags/Bridges/ExactIntDomains.lean` (in `namespace ExactInt`, `open Flean.Tags`;
added to `Flean/Tags.lean` aggregator). Flean had AI built TWICE independently — **Tags**
(`IsNonneg`, `HasAbsBound`, `IsBoundedRange`; on the real value `FiniteFp.toVal`; metric face, used
by softmax/MLP) and **exact-int** (`HasSign`/`HasSignMag`; on integer shadow `ExactInt.n`;
structural face). Bridges make the connection load-bearing: the exact-int domains **refine** the
Tags ones, projecting along the γ-collapse `n → fp.toVal`. `HasSign.isNonneg` (`HasSign s a` +
`0≤s` ⇒ `IsNonneg a.fp`, via `sign_nonneg_iff`); `HasSignMag.hasAbsBound` (`le_hi` ⇒ `HasAbsBound
(hi:R) a.fp`, via `Int.cast_abs`/exact_mod_cast); `HasSignMag.isNonneg` (`0≤s`, via `.toSign`). So
`HasSign`'s 3-valued sign carries strictly more than `IsNonneg`'s one-sided bound, and
`HasSignMag`'s interval more than `HasAbsBound` — the discrete/structural domains sit ABOVE the
metric Tags domains under refinement; Tags = the real-valued residue. AI is now the explicit spine
joining the new lattice to the existing 47k-line error-analysis library. (Bridges go exact-int →
Tags only; the reverse can't recover the integer shadow.) Note: Tags structs live in
`namespace Flean.Tags`; `IsNonneg` sig = `[FloatFormat]{R}[Field][LinearOrder]FiniteFp→Prop` (no
StrictOrdered/FloorRing in binders despite being in the defining variable block). All sorry-free.

UPDATE 2026-06-15 (AFFINE NETWORK CAPSTONE — "a net-in-a-region IS a single affine map"):
`Flean/Operations/AffineNet.lean` (+ `AffineForm.abs_toVal_sub_value_le` in AffineForm.lean = the
γ: `|fp.toVal − value| ≤ err`). Affine-map toolkit on AffineForm: `ofConst` (constant/weight/bias
as degree-0 form), `scaleConst` (×constant float `w`; NO input bound X needed since constant ⇒ zero
quadratic leak; ideal `↦ w·(a·x+b)`, proved direct via `fpMulFinite_inexact_general` with err_b=0),
`addConst` (+constant float, via `add` against `ofConst`), `affineMap p w c` = `y↦w·y+c` (one
neuron's pre-act map, ideal `↦ w·value+c`). Composition: `affineMap_reluActive_value` (2nd affine
layer after ReLU in active region ⇒ ideal `= z₁.value·w₂+b₂`, ReLU=identity there). **Capstone
`two_layer_affine_in_region`**: 2-layer scalar ReLU net restricted to one activation region has
`value = input.value·(w₁·w₂) + (b₁·w₂+b₂)` — a SINGLE affine map in the input, recovered end-to-end
from FP ops; ideal exact-on-shadow, all FP cost in `err`. **`two_layer_error_bound`**: actual FP
output within the form's `err` of that affine map ⇒ complete verified-local-linear-region
certificate (ideal IS affine A·x+b ∧ FP output within err). All sorry-free.

UPDATE 2026-06-15 (ROBUST region certificate — region in terms of the IDEAL not the bit pattern):
in `AffineRelu.lean`. `fp_s_false_of_err_lt_value` (z.err < z.value ⇒ z.fp.s = false, via
`abs_le`+`FiniteFp.toVal_pos_iff`), `reluActiveOfValue z (h: z.err < z.value)` = certified active
region keyed on the ideal clearing the error margin (robust to FP noise; below the margin = the
kink, ambiguous). `two_layer_affine_certified` in AffineNet = the capstone with the interpretable
margin hypothesis instead of a raw sign bit — the form a real "certified linear region" theorem
should take. All sorry-free.

UPDATE 2026-06-15 (MULTI-INPUT affine forms — real affine arithmetic, toward a linear LAYER):
`Flean/Operations/AffineFormVec.lean`. `AffineFormVec R n` = fp + coeffs `c : Fin n → R` + const
`c0` + inputs `x : Fin n → R` + err, invariant `|fp.toVal − (c0 + ∑ᵢ cᵢ·xᵢ)| ≤ err` — the standard
affine-arithmetic/zonotope form, shadow of a neuron's `⟨w,x⟩+b`. Same shape-agnostic transformers
(`fpAddFinite_inexact_general`/`fpMulFinite_inexact_general`), only the shadow becomes a
`Finset.sum`. `value`, `abs_toVal_sub_value_le` (γ), `ofExact`, `add` (coeff/const-wise, `+` stays
affine, `add_value`=sum of ideals; value identity via `Finset.sum_add_distrib`+`Pi.add_apply`),
`scaleConst` (×const, `scaleConst_value`=value·w, via `Finset.sum_mul`). Compiled first try.
Answers the "just scalar toy" critique — the domain vectorizes cleanly (design note: vectors
orthogonal to the domain question, confirmed). `mul_nonlinearity_bound` (pure, multi-input analogue of
`affine_mul_nonlinearity`): `|(∑pᵢxᵢ)(∑qⱼxⱼ)| ≤ X²·(∑|pᵢ|)(∑|qⱼ|)` over input box `|xᵢ|≤X` — the
bilinear leak, closing `×` again needs the input interval (reduced product). Next: full FP
multi-input `mul` op (combine this + FP mul err); FP dot-product CONSTRUCTOR (build an AffineFormVec
from a layer's `⟨w,x⟩+b` FP computation, via the existing FpDotProductBound). All sorry-free.

---

## Session summary (2026-06-15 autonomous run) — 6 new files, all sorry-free, full build green

Goal was "enhance / explore more of the regime." Built out the **approximate-pillar continuous
structural** quadrant end to end and unified the two domain systems:
- `AffineForm.mul` + `fpMulFinite_inexact_general` (× closes via reduced product w/ input bound).
- `AffineRelu.lean`: ReLU linear regions (active=identity tracks ideal, inactive=0; `reluActive`
  carries the form forward); **robust** region cert `reluActiveOfValue` (ideal clears err margin).
- `AffineNet.lean`: affine-map toolkit (`ofConst`/`scaleConst`/`addConst`/`affineMap`); **capstone**
  `two_layer_affine_in_region` (2-layer ReLU net in a region = single affine map) + `two_layer_error_bound`
  + `two_layer_affine_certified`.
- `AffineFormVec.lean`: multi-input affine arithmetic (`c0+∑cᵢxᵢ`) + add/scaleConst + `mul_nonlinearity_bound`.
- `Tags/Bridges/ExactIntDomains.lean`: exact-int domains REFINE Tags (`HasSign→IsNonneg`, `HasSignMag→HasAbsBound`).
- See the **Regime map** at the top of `exact-int-design.md` for the full lattice.
FP dot-product constructor DONE (see below); open frontier now: full multi-input `mul`;
region-over-an-input-box; Taylor-degree-2 domain (catch the affine quadratic leak — model-order tower).

UPDATE 2026-06-15 (FP DOT-PRODUCT CONSTRUCTOR — multi-input affine GROUNDED in a real layer):
`Flean/Operations/AffineLayer.lean` (+ `AffineFormVec.ofConst`/`addConst` added to AffineFormVec.lean).
The existing `FpDotProduct.FpDotProductBound w x R` already proves `|result − ∑ wᵢ·xᵢ| ≤ relErr·∑|wᵢxᵢ|`
— which IS the `AffineFormVec` invariant (weights = coefficients, inputs = noise symbols).
`AffineFormVec.ofDotProductBound w x db` reads it off as an affine form (ideal = true dot product
`∑ wᵢxᵢ`, c0=0, err = relErr·∑|wᵢxᵢ|); `neuron w x db b` adds the bias via `addConst` (ideal
`(∑wᵢxᵢ)+b` = the pre-activation, `neuron_value`). `AffineFormVec.reluActive` (multi-input ReLU,
sign-dispatch, identity in active region) + `neuron_relu_value`: **end to end** a real FP `⟨w,x⟩+b`
layer + ReLU, in its active region, has ideal `(∑wᵢxᵢ)+b` — the affine map of the inputs, recovered
from the ACTUAL computation (not synthetic). This also unifies the affine domain with the existing
error-analysis library (FpDotProductBound). `open FpDotProduct` to name the structure. All sorry-free.

UPDATE 2026-06-15 (MULTI-INPUT `mul` — `×` closes for AffineFormVec; affine op-set complete):
`AffineFormVec.mul` in AffineFormVec.lean. Pure helper `mul_decomp` (product of two multi-input
affine ideals = linearization + bilinear residual `(∑pcᵢxᵢ)(∑qcⱼxⱼ)`, via `Finset.mul_sum`+
`sum_add_distrib`). `mul p q hx X hX hX0 ...`: result ideal = LINEARIZATION `p.c0·q.c0 + ∑ᵢ
(p.c0·qᵢ+q.c0·pᵢ)·xᵢ`; err = FP-mul-propagation (`fpMulFinite_inexact_general`, i_a=p.value,
i_b=q.value) + bilinear leak `X²·(∑|pᵢ|)(∑|qᵢ|)` (`mul_nonlinearity_bound`). Proof: triangle
|f−L| ≤ |f−P·Q| + |P·Q−L|, with P·Q−L = residual (mul_decomp). Accessors `mul_c/c0/x/value`.
Closes the top frontier item — AffineFormVec now has the full op-set (`add`/`scaleConst`/`mul`/`neg`/
`ofConst`/`addConst`), same "+closes, ×leaks (needs input box)" duality as scalar AffineForm, and
grounded in real layers (AffineLayer). Remaining frontier: region-over-an-input-box (DONE below);
Taylor-degree-2 (catch the quadratic leak). All sorry-free.

UPDATE 2026-06-15 (LINEAR REGION AS AN INPUT SET — region-over-a-box; the affine ⋈ interval reduced
product): `Flean/Operations/AffineRegion.lean`. The classical ReLU *linear region* made rigorous —
an ideal-level property (separable from FP) proved by the standard affine-arithmetic range bound.
Over a box `|xᵢ−centerᵢ|≤radᵢ`: `affine_box_bound` (affine fn deviates from center value by ≤
`∑|cᵢ|·radᵢ`, via `Finset.sum_sub_distrib`+`abs_sum_le_sum_abs`), `affine_box_pos` (center value >
radius bound ⇒ uniformly positive over the WHOLE box), **headline `relu_affine_on_box`** (`max 0 g =
g` for every input in the box ⇒ the neuron IS its affine map `g(x)=c0+∑cᵢxᵢ` throughout the
certified region). FP-form bridges (namespace AffineFormVec): `value_pos_of_box`, `value_ge_of_box`
(value ≥ center−radius), `fp_s_false_of_err_lt_value` (positive value ⇒ sign clear, via
`FiniteFp.toVal_pos_iff`), **`fp_s_false_of_box`** = the FULLY certified region: box margin >
radius bound + err ⇒ FP pre-activation active (accounts for input box AND FP noise). Turns "this
point is in the linear region" into "this whole input region is the affine map A·x+b". All
sorry-free.

UPDATE 2026-06-15 (TAYLOR-DEGREE-2 DOMAIN — the model-order tower): `Flean/Operations/QuadForm.lean`.
`QuadForm R` = fp + quadratic ideal `a·x²+b·x+c` + err. The tower idea: degree-d catches polynomial
structure up to degree d and leaks degree d+1; AffineForm is d=1 (leaks degree 2), QuadForm is d=2.
`add` (coeff-wise, `+` stays degree 2, via `fpAddFinite_inexact_general`). **Headline `ofAffineMul`**:
the FP product of two AFFINE forms is caught EXACTLY as a QuadForm (ideal = `p.value·q.value` exactly,
coeffs `a=pa·qa, b=pa·qb+qa·pb, c=pb·qb`), err = FP rounding ONLY — NO x² leak, NO input bound X
needed (vs AffineForm.mul which had `+|pa·qa|·X²` and required X). The degree-2 rung catches what
degree-1 dumped. **Tower continues**: pure `quad_mul_leak` (degree-4 product − degree-2 truncation =
degree-3,4 terms ≤ `|a₁a₂|X⁴+|a₁b₂+b₁a₂|X³`), `QuadForm.mul` (quad×quad = degree-2 truncation, leaks
degree 3-4 into err — same pattern as AffineForm.mul one rung up). Same shape-agnostic transformers
reused. All sorry-free. The continuous regime is now a TOWER (degree 1 affine, degree 2 quad, …) each
rung catching the previous rung's nonlinearity leak — curved regions, not just linear.

UPDATE 2026-06-15 (GENERIC degree-d tower — the abstraction): `Flean/Operations/PolyForm.lean`.
`PolyForm R d` = fp + coeffs `c : Fin(d+1)→R` + x + err, ideal `∑_{i≤d} cᵢ·xⁱ`. The degree-generic
operations written ONCE for all d: `value`, γ `abs_toVal_sub_value_le`, `ofExact`, `add` (coeff-
wise, via `fpAddFinite_inexact_general`), `scaleConst`, `neg` (+ value lemmas; same Finset
techniques as AffineFormVec). `value_one`/`value_two` recover AffineForm (=PolyForm 1, ideal
`c₀+c₁x`) and QuadForm (=PolyForm 2, ideal `c₀+c₁x+c₂x²`) — the instances. **Generic leak step**
`truncateOne` (degree d+1→d: same float reinterpreted, top coeff dropped, leaked `c_{d+1}·x^{d+1}`
absorbed into err ≤`|c_{d+1}|·X^{d+1}`; via `Fin.sum_univ_castSucc`, NO FP op/typeclasses needed) +
`value_castSucc_split`/`truncateOne_value`. **Meta-finding** (mirrors IsImage): the degree-generic
ADDITIVE/scaling/structural skeleton FACTORS uniformly (one def, all d); the cross-degree content
is mul (raises degree d×e→d+e exactly) + truncate (lowers, leaks) — truncate generalized here. All
sorry-free.

UPDATE 2026-06-15 (GENERIC Cauchy-product `mul` — the degree-coupling op, tower COMPLETE):
`PolyForm.mul : PolyForm d → PolyForm e → PolyForm (d+e)`, EXACT (FP rounding only, no leak, no
input bound — the product of a degree-d and degree-e ideal is a genuine degree-(d+e) polynomial,
caught exactly). Coeffs = Cauchy product `mulCoeff c c' k = ∑_{i+j=k} cᵢc'ⱼ`. Key value identity
`mulCoeff_value` (`(∑cᵢxⁱ)(∑c'ⱼxʲ)=∑ₖ mulCoeff·xᵏ`) proved via `Fintype.sum_mul_sum` +
`Finset.sum_comm`(×2) + helper `inner_cauchy` (∑ₖ indicator picks the single k=i+j term, via
`Fin.sum_univ_eq_sum_range`+`Finset.sum_ite_eq`; `i+j≤d+e` by omega on i.isLt/j.isLt). `mul_value`
= p.value·q.value exactly; herr via `fpMulFinite_inexact_general`, NO leak term. Subsumes
`QuadForm.ofAffineMul` (d=1,e=1) and every rung at once. **Tower now fully generic**: `mul` raises
degree exactly, `truncateOne` lowers (leaks); AffineForm.mul & QuadForm.mul both = (mul up) then
(truncate down). The degree-coupling op that IsImage's `.map` was on the discrete side — both sides'
cross-level operation now built. Gotcha: `rw [hx]` over-rewrites ALL `p.x` (incl. inside p.value) —
align q's x via a separate `hq` (∑ q.c j p.x^j = q.value), don't rw [hx] on the whole goal. All
sorry-free.

UPDATE 2026-06-15 (GENERAL MULTIVARIATE Taylor model — top of the continuous hierarchy, the leak
EXPLAINED): `Flean/Operations/MvForm.lean`. `MvForm R n` = fp + `P : MvPolynomial (Fin n) R` ideal
+ x:Fin n→R + err, invariant `|fp.toVal − eval x P| ≤ err`. **Because `MvPolynomial.eval x` is a
RING HOM, add (P+Q) AND mul (P·Q) are BOTH EXACT** (FP rounding only, no leak, no input bound X) —
polynomials closed under +,× so an unbounded-degree model never truncates. `value`=`eval x P`, γ,
`ofExact`, `add`/`mul`/`neg` (all `noncomputable` — MvPolynomial ring is) + value lemmas (via
`simp [value, eval_add/eval_mul/map_neg, hx]`). **The punchline of the whole continuous thread**:
the leak was NEVER intrinsic to `×` — it's an artifact of FIXING the degree. AffineForm/QuadForm/
AffineFormVec/PolyForm = MvForm restricted to bounded total degree; their leak = the cost of
projecting `MvForm.mul`'s (exact) result back down to that degree. Carry the full polynomial ⇒ `×`
is as exact as `+`. Mathlib `MvPolynomial.eval` (RingHom) offloads ALL the multivariate algebra.
Continuous hierarchy now: MvForm (general, exact) ⊃ PolyForm d (1-input deg-d) ⊃ AffineForm/QuadForm;
AffineFormVec (n-input deg-1). All sorry-free.

UPDATE 2026-06-15 (LOOP CLOSED — the leak IS degree-truncation, as an EQUALITY): in PolyForm.lean.
`mul_truncateOne_value` (p q : PolyForm R 1): `((p.mul q).truncateOne X hX).value = p.value·q.value
− mulCoeff p.c q.c (Fin.last (1+1)) · x^(1+1)` — proved by `rw [truncateOne_value, mul_value, mul_c,
mul_x]` (just rfl after the value lemmas). I.e. truncating the EXACT degree-2 product back to degree
1 drops *exactly* the top Cauchy coeff × x². `mulCoeff_last_two` (pure): that top coeff = `c 1 · c'
1` = the slope product = exactly `AffineForm.affine_mul_nonlinearity`'s leaked `|a₁a₂|`. So the
fixed-degree affine leak is LITERALLY the projection of the exact product onto degree 1 — same term,
now an equality, not a bound-by-analogy. **The whole continuous thread's thesis ("× leaks only
because the degree is fixed; the leak = truncation") is now a proved equality, not a slogan.** Gotcha:
`Fin.last (d+1)` with d solved to 1 stays as `Fin.last (1+1)` (not auto-reduced to `Fin.last 2`); full
`simp` over-factors `A−Bx²=A−Cx²` into `B=C ∨ x=0` — use controlled `rw`, state the leak as the
Cauchy coeff (matches `truncateOne_value` verbatim). All sorry-free. **Continuous hierarchy COMPLETE
and closed: general (MvForm, exact) → fixed-degree (PolyForm/Affine/Quad) via truncation = the leak.**

UPDATE 2026-06-15 (PROBABILISTIC / RG PHYSICS — first brick: the √n law of rounding error):
`Flean/Operations/ProbError.lean` (`namespace Flean.ProbError`, on Mathlib probability). Chosen
direction after the strategic step-back (the higher-level reframing: the whole reduction stack is
**certified abstract interpretation of FP**, and the loop-closing revealed it has **renormalization-
group structure** — MvForm=UV-complete, fixed-degree forms=effective theories, truncate=integrating
out modes, leak=irrelevant operators suppressed by `X^k`, IsImage residues=conserved charges,
err/η=cutoff, snapping=gap. See design-note "Strategic read"/"Regime map"). First probabilistic brick:
the statistical mechanics of rounding — worst-case err accumulates LINEARLY (`n·η·scale`) but under
the **probabilistic rounding model** (independent mean-zero per-step errors, the Higham–Mary model,
exact for stochastic rounding) variances ADD, so typical error grows like **`√n·η·scale`**.
`variance_sum_le` (the quadrature law: `Var[∑eᵢ] ≤ ∑vᵢ`, via Mathlib `IndepFun.variance_sum`);
`concentration` (Chebyshev → `μ{|∑eᵢ| ≥ k·√n·σ} ≤ 1/k²`, the `√n` explicit). In the RG picture this
is where `err` becomes a *fluctuation scale* (variance/temperature) not a hard cutoff; concentration
= the law of large numbers for the reduction. Gotchas: `μ[∑ i, eᵢ]` needs `Finset.sum_apply` to
expose the integrand for `integral_finset_sum`; rw under set-builder binders fails → use
`measure_mono` + pointwise subset; `div_le_div_iff`→`div_le_div_iff₀`; `n>0` positivity needs an
explicit `(0:ℝ)<n` witness (positivity won't strict-ify a Nat cast alone). Next bricks: connect σ to
η (bounded mean-zero ⇒ `Var ≤ (η·scale)²`); martingale/Azuma for round-to-nearest (errors not
independent but mean-zero given the past); output-distribution shadows (≈Gaussian); formalize the
(α,γ) Galois connection + tower-as-RG-flow. All sorry-free.

**UPDATE 2026-06-15 (session 2) — σ↔η bridge + Gaussian fluctuations.** `ProbError.lean` extended:
- **σ↔η bridge** `variance_le_sq_of_abs_le` (bounded mean-zero ⇒ `Var ≤ b²`). Route: Mathlib
  Popoviciu `variance_le_sq_of_bounded` with `a=-b`, `b=b` ⇒ `((b-(-b))/2)² = b²` (`ring`). Cleaner
  than the planned `E[X²]` route; mean-zero isn't needed for the variance bound (only to *centre* the
  later concentration). Now the abstract `σ` *is* the FP rounding unit `η·scale`.
- Refactor: `concentration_of_variance_le` (engine: any `Var[∑e]≤V` ⇒ `μ{|∑e|≥k√V}≤1/k²`), with
  `concentration` (√n) a one-liner corollary. FP corollaries `concentration_fp` (uniform scale) +
  `concentration_fp_vec` (per-term; aggregate = **ℓ²** norm `√(∑scaleᵢ²)`, not ℓ¹ — quadrature explicit).
- **Gaussian fluctuations** (brick #3, mostly): `concentration_fp_subgaussian` (one-sided) + `_abs`
  (two-sided ≤ `2·exp(-k²/2)`). Bounded mean-zero ⇒ **sub-Gaussian** (Hoeffding lemma
  `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, param `(‖b-(-b)‖₊/2)²`), independent sub-Gaussians
  sum (`HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` → `exp(-ε²/(2∑cᵢ))`). Sub `ε=k√n·η·scale`,
  `∑cᵢ=n(η·scale)²` ⇒ exponent `-k²/2`. **Exponential** tail beats Chebyshev's polynomial `1/k²` —
  the rigorous "rounding ≈ Gaussian noise". Needs `iIndepFun` (round-to-nearest dependence = Azuma,
  brick #2, still open via `measure_sum_ge_le_of_HasCondSubgaussianMGF`).
- Gotchas (session 2): result measure is `μ.real` (real-valued) for the sub-Gaussian API, set is
  one-sided `{ε ≤ ∑}` (two-sided via `le_abs` split + `measureReal_union_le` + neg-family
  `iIndepFun.comp (fun _ => Neg.neg) (fun _ => measurable_neg)`, `Finset.sum_neg_distrib`); ℝ≥0→ℝ
  coercion of the sub-Gaussian param needs `push_cast [Real.norm_eq_abs]` then `abs_of_pos`; the sum of
  constants: `NNReal.coe_sum` *first* (coe pushes inside the sum during elaboration, so state it that
  way), then `Finset.sum_const`+`nsmul_eq_mul`; neg-family mean needs `simp only [Pi.neg_apply,
  integral_neg, hmean i, neg_zero]` (the family lambda must beta-reduce). All sorry-free, warning-clean.

## Design notes / gotchas

- `HMul`/`HAdd`/`HSub FiniteFp FiniteFp Fp` (result is `Fp`, coerced back). That `Fp`
  return is why we need `toFiniteOr0` to carry results as `FiniteFp` data.
- Provenance bridges: state RHS as `fpMulFinite a.fp b.fp` (not `a.fp * b.fp`). A `: Fp`
  ascription on the LHS biases `a.fp * b.fp` to *`Fp`-level* mul (`↑a.fp * ↑b.fp`),
  mismatching the `FiniteFp`-level `hf_eq`. Naming the function dodges it.
- `h_exp : prec - 1 ≤ max_exp` is a per-format triviality threaded everywhere; a future
  `[FloatFormat]`-derived instance/simp could remove it.
