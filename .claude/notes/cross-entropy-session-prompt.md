# Flean — Focused Session: Cross-Entropy Loss End-to-End

## What you're doing

Formalize the cross-entropy loss (the standard ML classification
objective) as an FP-level end-to-end error bound, composing the
already-landed log-sum-exp, softmax, and dot-product machinery.  This
is the **capstone of the ML-primitives arc**: softmax + LSE + CE is
the "can this library actually verify real ML?" demonstration.

Expected shape:

```
CE(y, x) = − Σ_i y_i · (x_i − LSE(x))
         = − Σ_i y_i · log_softmax(x)_i
```

where `x : Fin n → FiniteFp` are logits, `y : Fin n → FiniteFp` are
target probabilities (often one-hot).  The FP implementation:

1. Compute `lse = fpLogSumExp(x)` via the existing pipeline.
2. Shift: `r_i = fpSubFinite(x_i, lse)` — log-probabilities.
3. Dot product: `s = fpDotProduct(y, r)`.
4. Negate: `loss = fpNeg(s)`.

End-to-end bound relates `loss.toVal` to the real-valued `CE(y, x)`
in terms of the per-step errors composing cleanly.

## Context to absorb first

Read in order, each until you understand what the API looks like
(use `../lean-extract-bin` to survey signatures without pulling in
proof bodies):

1. **`.claude/notes/directions.md`** — the entry for
   "Cross-entropy loss" + surrounding ML-primitives arc + the just-
   resolved dot-product adapter status.
2. **`Flean/Operations/LogSumExp.lean`** — particularly
   `fpLogSumExp_end_to_end_error_bound` (§EndToEnd).  This is the
   canonical pattern CE will follow: raw inputs, exact-shift witness,
   abstract `h_log_close` witness, final-add step, sign-symmetric
   rounding via `[RModeConj ℝ]`.  Also skim the `Demo` section —
   `fpLogSumExp_kahanSum_error_bound` etc. are the concrete-summation
   adapters CE should mirror.
3. **`Flean/Operations/Softmax.lean`** — skim the bundle/Demo
   sections.  CE's bundle (`FpCrossEntropyResult`) should look
   structurally similar.
4. **`Flean/Operations/FpDotProduct.lean`** — the `FpDotProductBound`
   struct, `.ofDotProduct` / `.ofDotProductFMA` constructors, and
   the `FpDotProductBoundCompensated` path.  CE's dot-product step
   plugs in here.
5. **`Flean/Tags/LayerNorm.lean`** — Stage 7 demo
   (`fpLayerNorm_naiveSum_demo`) is the most recent example of a
   concrete end-to-end adapter; read it for patterns.

## Key design decisions

### 1. Abstract vs concrete log witness

LSE keeps the log step abstract (`fpLogFinite`/`LogApprox` doesn't
exist yet — see the `LogApprox / fpLogFinite` entry in
`directions.md`).  **CE should do the same** — take an abstract
`(logResult, η_log, logSubConst, h_log_close)` witness and let the
log step land when the `LogApprox` capstone does.  This keeps the
session self-contained without requiring the ~500–800-line log
machinery first.

### 2. Input shape

Match LSE's signature:

- `xs : Fin n → FiniteFp` — raw logits.
- `xs' : Fin n → FiniteFp` with exact-shift `(xs' j).toVal = (xs j).toVal − (fpMax xs hn).toVal`.
- `exps` witnessed by `fpExpFinite (xs' i) = Fp.finite (exps i)`.
- `FpSum.FpSumBound exps ℝ` — summation adapter for the LSE sum.
- `logResult, η_log, logSubConst, h_log_close` — abstract log step.
- `fpAddFinite (fpMax xs hn) logResult = Fp.finite lse` — assemble LSE.
- `ys : Fin n → FiniteFp` — target distribution (no nonneg or
  simplex assumption forced at first; the bound just carries
  `Σ|y_i|` naturally).
- `r : Fin n → FiniteFp` + `∀ i, fpSubFinite (xs i) lse = Fp.finite (r i)` — log-probs.
- `FpDotProductBound ys r ℝ` — dot-product witness for `Σ y_i · r_i`.
- `loss : FiniteFp` + `loss.toVal = −s.toVal` (or build this from
  sign flip + finite witness).

### 3. Error composition

Three error "streams" compose additively into the final bound:

- **LSE error**: `|lse.toVal − LSE_exact| ≤ Δ_LSE` where `Δ_LSE` is
  the quantity produced by `fpLogSumExp_end_to_end_error_bound` —
  carry through as an abstract bound.
- **Shift error per i**: `|r_i.toVal − (x_i.toVal − lse.toVal)| ≤ η·|x_i − lse|` (one rounding step, normal-range regime).
  Composes with `Δ_LSE` to get `|r_i.toVal − r_exact_i| ≤ δ_r_i`.
- **Dot product error**: `|s.toVal − Σ y_i · r_i.toVal| ≤ dp.relErr · Σ|y_i · r_i.toVal|`.

Final bound: `|loss.toVal − CE_exact| ≤ <composition>`.

The composition involves:
- `|Σ y_i · r_i.toVal − Σ y_i · r_exact_i| ≤ Σ |y_i| · δ_r_i`
- triangle with the dp bound on the LHS
- triangle with the LSE error distributed across indices weighted by `|y_i|`

### 4. Shape of the final bound

Target:
```
|loss.toVal − CE(y, x)| ≤
    dp.relErr · Σ |y_i · r_i.toVal|
  + (1 + dp.relErr) · Σ|y_i| · (η · |x_i − lse.toVal| + Δ_LSE)
  + subnormalConst
```

Exact constants TBD during derivation — mirror the shape from
`fpLogSumExp_end_to_end_error_bound`.

## What to deliver

### Required (session success criteria)

- **New file**: `Flean/Operations/CrossEntropy.lean`.  ~500 lines
  tops.  Sorry-free.  `lake build Flean` passes.
- **Pure-math**: `crossEntropy (y x : Fin n → ℝ) : ℝ` definition +
  basic lemmas (`crossEntropy_shift_eq`, non-negativity under
  nonneg y and bounded r, etc.).
- **End-to-end theorem**:
  `fpCrossEntropy_end_to_end_error_bound` — all the hypotheses
  listed in §2 above, concludes the final forward bound.
- **Bundle**: `FpCrossEntropyResult xs ys hn` + `.error_bound`
  method.  Mirror `FpLogSumExpResult`'s shape.
- **Concrete demo(s)**: at minimum one `_naiveSum_error_bound`
  demo (NaiveSum for the LSE-internal sum + `ofDotProductFMA` for
  the outer dot product), analogous to
  `fpLogSumExp_naiveSum_error_bound`.  Optionally Kahan/Neumaier
  variants if time permits.
- **Directions.md update**: move CE from pending to done.

### Optional (if budget allows)

- **One-hot specialization**: `fpCrossEntropy_onehot` — when `y_j = 1`
  for some `j` and `y_i = 0` elsewhere, `CE = −r_j = lse − x_j`.
  Very common in practice; might tighten the bound.
- **Tag framework plug-in**: `IsSimplex y` tag → `Σ|y_i| = 1` →
  the `Σ|y_i| · …` term collapses cleanly.  Lives in
  `Flean/Tags/CrossEntropy.lean` or stays inline.

## Hard constraints

- **Sorry-free**: 2800+ job library invariant.  If stuck, narrow
  scope (drop the optional extensions; narrow the final bound
  shape); do NOT commit a `sorry`.
- `set_option autoImplicit false` in the new file.
- Follow the Lean-level conventions from `CLAUDE.md`: local `prec`
  notation, explicit `R` over `ℝ`, etc.  Since CE is ℝ-specialised
  at the end (LSE is), you can mostly write `ℝ` directly — mirror
  LSE's style.
- No new dependencies beyond what LSE + FpDotProduct already pull in.
- Commit in logical chunks: (a) pure-math, (b) end-to-end theorem,
  (c) demos.  Each chunk builds.

## Known gotchas (from LSE/softmax sessions)

- `η` can't be used as a bound-variable name in theorem signatures
  (parser error).  Pick a different letter (`t`, `u`, `η_log`).
- `[RModeConj ℝ]` is required for sign-symmetric rounding (CE has a
  final negation; LSE's `h_final_ne` pattern carries over).
- `Fp.ulp_eq_neg` handles sign-flip interactions between rounding
  and `fpNeg`.
- `fpSubFinite` reduces to `fpAddFinite · (neg ·)` — the same
  pattern LayerNorm uses for shift.
- `subnormalConst` shows up in shift-step normal-range regime;
  carry it through like Softmax/LSE do.
- `FiniteFp.toVal_neg_eq_neg` needs `(R := ℝ)` explicit in `linarith`
  hint lists.
- Struct elaboration with many `FpSumBound`-valued fields can hit
  `whnf` heartbeat limits (LayerNorm session hit this).  If the
  bundle blows up, unbundle — take plain hypotheses instead.

## Reporting back

At session end, summarize:
- LOC of `CrossEntropy.lean` and any modified files.
- Whether the one-hot / tag extensions landed or were deferred.
- Any new infrastructure lemmas added (e.g. real-math CE identities
  that should live in Util.lean).
- Commit references.

Update `directions.md`: move CE to "done" under the ML primitives
arc, with a one-line summary of the shipped API.  Update
`memory/MEMORY.md` if useful new patterns emerged.
