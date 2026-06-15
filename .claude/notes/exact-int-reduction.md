# Exact-Integer Reduction (Flean reductionist thread)

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
3. **n-ary sum / `dotN`** (NEXT, now unblocked). `List (ExactIntB R)` fold with a single
   running-bound hypothesis; the bound bookkeeping is now a fold over `bound`. Natural
   bridge to matvec.
4. **Concrete net**. Interval-propagate a small concrete network (bounds flow via
   `ExactIntB`) and extract its integer/modular behavior. The aspirational target.

## Fixed-point / correction layer (the inexact frontier — started 2026-06-15)

Crossing from exact to "simpler form + bounded correction" (the reductionist payoff:
"multistep float ops → integer fn + minor correcting factor"). Staged as exact-first.

SHIPPED — `Flean/Operations/ScaledExact.lean` (the exact on-ramp): widens `ExactInt` from
integers to **fixed-point** `m · 2^s` (common scale `s`; `ExactInt` = `s=0`). Leans on
`exists_finiteFp_of_int_mul_zpow` (ToVal.lean) for scaled representability. Pieces:
`scaled_round_exact` (scaled `int_round_exact`), `fpAddFinite_scaled_exact` (same-scale
add), `fpMulFinite_scaled_exact` (scales add: `s_a + s_b`), `structure ScaledExact`
(fp, m, s, agree: `fp.toVal = m·2^s`), `value`/`value_eq_toVal`. Sorry-free, in aggregator.

KEY FINDING (correction op, the actual C-teeth): there is **no generic `○`-level error
bound** in Flean — only mode-specific ones (`roundNearestTiesToEven_abs_error_le_ulp_half`
in `Rounding/RelativeErrorBounds.lean`, which also need `isNormalRange x`). So the
correction op must (a) commit to a rounding policy — `[UseRoundingPolicy
RoundNearestEvenPolicy]`, (b) carry `isNormalRange`, (c) connect the generic `○`/fpAddFinite
to `roundNearestTiesToEven` under that policy, then bound the deviation by `ulp/2`. That is
the next focused piece — the rounding-policy plumbing IS its content. Result shape: a
float op on common-scale values `= (integer op on significands)·2^s + correction`, with
`|correction| ≤ ½ ulp`. Then the inexact `ScaledInt` (carry an `err` field) wraps it.

TODO on `ScaledExact` (mechanical, when needed): `sub`/`neg`, data-carrying
`addExact`/`mulExact` constructors + `.fp` provenance bridges (mirror `ExactIntAlgebra`).

## Design notes / gotchas

- `HMul`/`HAdd`/`HSub FiniteFp FiniteFp Fp` (result is `Fp`, coerced back). That `Fp`
  return is why we need `toFiniteOr0` to carry results as `FiniteFp` data.
- Provenance bridges: state RHS as `fpMulFinite a.fp b.fp` (not `a.fp * b.fp`). A `: Fp`
  ascription on the LHS biases `a.fp * b.fp` to *`Fp`-level* mul (`↑a.fp * ↑b.fp`),
  mismatching the `FiniteFp`-level `hf_eq`. Naming the function dodges it.
- `h_exp : prec - 1 ≤ max_exp` is a per-format triviality threaded everywhere; a future
  `[FloatFormat]`-derived instance/simp could remove it.
