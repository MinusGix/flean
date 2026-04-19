# Log-sum-exp session plan

## Goal

Add a verified end-to-end `logsumexp` error bound, mirroring the softmax
pipeline structure in `Flean/Operations/Softmax.lean`.

`logsumexp(xs) = log(Σ exp(xs_i))`, computed stably via the subtract-max
identity:

```
logsumexp(xs) = max(xs) + log(Σ exp(xs_i - max(xs)))
```

The subtract-max trick bounds each shifted input in `(-∞, 0]`, so each
`exp(shifted)` is in `(0, 1]` — no overflow. The post-shift sum `S' ≥ 1` (max
term is `exp(0) = 1`), so `log(S')` is well-defined and non-negative.

## FP pipeline

Given raw `xs : Fin n → FiniteFp`:

1. `c := fpMax xs hn`                          — reuse existing
2. `xs' i := fpSubFinite (xs i) c`             — reuse existing (assume exact)
3. `exps i := fpExpFinite (xs' i)`             — reuse existing
4. `sumResult := fpSum exps`                   — reuse `FpSumBound` adapter
5. `logResult := fpLog sumResult`              — **see blocker below**
6. `result := fpAddFinite c logResult`         — one final fpAdd

## Blocker and workaround

`fpLogFinite` / `LogApprox` does not exist. `Flean/Operations/LogComputable.lean`
has `logComputableRun` (arbitrary-precision rational log via Taylor series),
but nothing parallel to `ExpApprox` / `fpExpFinite` from
`Flean/Operations/Exp.lean`.

**Workaround:** take the log step as an abstract hypothesis, matching how
softmax takes `h_exp` as `fpExpFinite (xs i) = Fp.finite (exps i)`. Concretely:

```lean
(h_log_close : ∃ logResult : FiniteFp,
  |(logResult.toVal : ℝ) - Real.log ((sumResult.toVal : ℝ))| ≤
    η_log * |Real.log ((sumResult.toVal : ℝ))| + additiveConst)
```

or more directly take `logResult : FiniteFp` + the bound as a witness. This
makes the LSE theorem compose with any future concrete `fpLogFinite` — when
the `LogApprox` typeclass lands, a thin wrapper produces the required witness.

Do NOT build `LogApprox` as part of this session — that's a separate
~500-800 line project. Keep the log step abstract.

## Target theorem shape

```lean
theorem fpLogSumExp_end_to_end_error_bound
    {n : ℕ} (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ j,
      ((xs' j).toVal : ℝ) = ((xs j).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp) (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (hd_m : sum.result.m ≠ 0)  -- or equivalent positivity witness
    -- Abstract log witness:
    (logResult : FiniteFp)
    (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))|)
    -- Final add:
    (result : FiniteFp)
    (h_final_add : fpMax xs hn + logResult = Fp.finite result)
    (hnr_final : ...)
    -- Hypotheses to make denominator/log well-defined:
    (hsum_pos : (0 : ℝ) < sum.result.toVal)
    :
    |((result.toVal : ℝ)) -
      Real.log (∑ j, Real.exp ((xs j).toVal : ℝ))| ≤
      [bound involving η, relErr, η_log, shift-related terms]
```

## Error analysis (rough sketch)

Let `S := Σ exp(xs_j.toVal)` (true) and `S' := Σ exp(xs'_j.toVal) = exp(-c)·S`
(shifted true sum, using `softmax_shift_eq`-style). By the exact shift
assumption, `Σ exp((xs j).toVal - c) = S'`.

1. **Exp step:** `|exps_i - exp(xs'_i)| ≤ η · exp(xs'_i)` (multiplicative) for
   each `i`. Already established in softmax machinery (`exps_error_of_correct`).

2. **Sum step:** `|sumResult - Σ exps_i| ≤ sum.relErr · Σ|exps_i|`. Because
   `exps_i ≥ 0` (for shifted inputs that are nonpositive), `Σ|exps_i| = Σ exps_i`.

3. **Combined (exp + sum):** `|sumResult - S'| ≤ η'·S'` where `η' ≈ η +
   sum.relErr·(1+η)`. Same kind of combined-error step as in softmax.

4. **Log step:** `log(x·(1+δ)) - log(x) = log(1+δ)`. So `|log(sumResult) -
   log(S')| ≤ |log(1+δ)| ≤ |δ|/(1-|δ|) ≈ η'` for small `η'`. Combined with
   `h_log_close`'s rounding: `|logResult - log(S')| ≤ η_log · |log(sumResult)|
   + |δ|/(1-|δ|)`.

   **Key subtlety:** `log(S')` can be as large as `log(n)` (when all inputs
   are equal) or near `0` (when one term dominates). Need `S' ≥ 1` to know
   `log(S') ≥ 0`. This follows from `S' ≥ exp(0) = 1` when the max term is
   zero-shifted (which it is, by `fpMax_attained`).

5. **Final add:** `|result - (c + logResult)| ≤ η · |c + logResult|`. Then
   `c + logResult ≈ c + log(S') = c + log(exp(-c)·S) = log(S) = LSE(xs)`.

6. **Total:** `|result - LSE(xs)| ≤ (combined bound in terms of η, sum.relErr,
   η_log, |c|, |LSE(xs)|)`.

The bound shape is likely something like

```
|result - LSE(xs)| ≤ η_total · (|LSE(xs)| + |c|) + η'_total
```

where `η_total` combines the exp/sum/log/final-add relative errors. Additive
tails from subnormals may also appear (analogous to `subnormalConst` in
softmax).

## Deliverables (target ~400-600 lines)

1. **Mathematical setup in Softmax.lean or new file `LogSumExp.lean`:**
   - `logsumexp : (Fin n → ℝ) → ℝ := fun xs => Real.log (∑ j, Real.exp (xs j))`
   - `logsumexp_shift_eq`: `logsumexp(shift xs c) + c = logsumexp(xs)`
   - `logsumexp_ge_max`: `logsumexp(xs) ≥ max(xs)` (from `log(exp(max)) = max ≤ log(Σ exp)`)
   - Basic facts about `∑ exp` being positive when `n > 0`.

2. **Error bound theorem** (the big one):
   - `fpLogSumExp_end_to_end_error_bound` with the hypotheses above
   - Decompose into exp error, sum error, log error, final-add error
   - Use existing softmax lemmas where they apply (the first ~3 steps are
     literally the same as softmax's analysis)

3. **Bundle (optional):**
   - `FpLogSumExpResult` struct bundling all hypotheses, like `FpSoftmaxResult`
   - `.error_bound`, maybe `.lower_bound_by_max` (shows `result ≥ (fpMax xs).toVal`)

4. **Demo:**
   - `fpLogSumExp_with_naiveSum_error` — wires `FpSumBound.ofNaive` through the theorem
   - Parallels `fpSoftmax_naiveSum_error_bound`

## Suggested approach

1. **Start with the math:** prove the real-valued `logsumexp_shift_eq` and
   `logsumexp_ge_max` lemmas — quick, ~30 lines.

2. **Reuse softmax machinery:** steps 1-3 of the error analysis (exp + sum
   combined error) already exist in `Softmax.lean`. Lift the relevant
   intermediate results or re-prove them if they're too tightly coupled to
   the softmax structure.

3. **Build the log step separately:** prove
   `log_bound : |log(x·(1+δ)) - log(x)| ≤ |δ|/(1-|δ|)` for `x > 0`, `|δ| < 1`
   as a standalone helper.

4. **Compose in the main theorem:** triangle inequality threading through each
   step's error.

5. **Demo last:** wire a NaiveSum witness in to sanity-check the full pipeline.

## Potential gotchas

- `Real.log` is defined on all reals (negative → 0 in Mathlib's convention,
  or undefined — check). Need to carefully handle positivity of `sum.result`
  so the log step is meaningful.
- The additive-error bucket (analogous to `subnormalConst` in softmax) may
  need handling when `exps_i` can underflow to zero.
- `sum.result.m ≠ 0` vs `0 < sum.result.toVal` distinction — softmax uses the
  first as a strong condition; for LSE we really need the latter (log needs
  positive input).
- `log(S') ≥ 0` needs `S' ≥ 1` — this comes from `exp(0) = 1` being among the
  summands, which needs the argmax argument used in softmax's `S ≥ 1` derivation.

## Out of scope for this session

- Building `LogApprox` / `fpLogFinite` — separate big project.
- Temperature scaling `logsumexp(xs/T)`.
- Backward-error LSE (probably doesn't fit `BackwardError` cleanly anyway).
- `fpLogSumExp` as a computable function (we're stating bounds on hypothesis
  witnesses, not defining a concrete function).

## Reference points

- `Flean/Operations/Softmax.lean` — main pattern to mirror, section `EndToEnd`
  for the raw-input version. Reuse the shift machinery, argmax helper, etc.
- `Flean/Operations/Exp.lean` — `ExpApprox`/`fpExpFinite` pattern to mentally
  mirror for the future `fpLog`.
- `Flean/Operations/FpSum.lean` — `FpSumBound` adapter to thread the sum step.
- `Flean/Operations/LogComputable.lean` — if time permits, could be a starting
  point for a concrete `fpLog` wrapper. But keep out of scope unless tiny.
