# Flean — Next Directions

Tracked iteratively. Priorities ordered top-to-bottom within each tier.

## Completed
- [x] **Relative error bounds** — Machine epsilon bound (2^(1-prec)) for all rounding modes ✓
- [x] **Half machine epsilon for roundNearest** — Tighten roundNearest bound to 2^(-prec) ✓
- [x] **Rounding idempotence** — `round(f.toVal) = Fp.finite f` for all 5 rounding modes ✓
- [x] **Rounding correctness properties** — All done ✓
  - Idempotence for all modes
  - Monotonicity for all 5 modes (`roundDown_mono`, `roundUp_mono`, `roundTowardZero_mono`, `roundNearestTE_mono`, `roundNearestTA_mono`)
  - Negation symmetry (`roundDown_neg_eq_neg_roundUp`, `roundUp_neg_eq_neg_roundDown`)
  - Bracket property (`roundDown_le_roundUp`)
  - Sandwich (`roundDown ≤ rnTE/rnTA ≤ roundUp`)
  - `toVal_injective`, `toVal_abs_ge_smallest`, `toVal_abs_lt_overflow`
- [x] **fpAdd correctness** — `fpAddFinite_correct`, `fpAdd_comm` ✓
- [x] **fpMul** — `fpMulFinite_correct`, `fpMul_comm` ✓
- [x] **fpSub** — `fpSubFinite_correct` (reduces to fpAdd) ✓
- [x] **fpDiv** — `fpDivFinite_correct` (sticky-bit technique) ✓
- [x] **fpSqrt** — `fpSqrtFinite_correct` (integer sqrt + sticky bit) ✓
- [x] **fpFMA** — `fpFMAFinite_correct`, `fpFMA_comm_ab`, `fpFMA_neg_mul_neg`, reduction to Add/Mul ✓
- [x] **Generalize RoundNearest/roundIntSig_correct** — removed `hval_ge_ssps` precondition ✓
- [x] **Factor sticky-bit scaffolding** — `sticky_roundIntSig_eq_round` shared by Div/Sqrt ✓
- [x] **Veltkamp splitting** (issue #32) — `veltkampSplit_exact`: `a_hi.toVal + a_lo.toVal = a.toVal` via grid coefficient error bounds ✓

## Near-Term
- [x] **Close remaining sorries** — all removed ✓
  - ~~`Linearize/FinalTest.lean:78`~~ — deleted (test for old limitation)
  - ~~`AlternatingChooseSum.lean:73`~~ — deleted (unused `leading_pade_coeff_sum`)
  - ~~`Ulp.lean:21` — Harrison's ULP~~ ✓ defined + linked to standard ULP
- [x] **Encoding round-trip** — `toBits_ofBits` + `ofBits_toBits` both sorry-free ✓
- [x] **Common constants verification** — proved in BitSize.lean without native_decide ✓

## Encoding Cleanup — Done
- [x] **Remove `@[reducible]` from `FpExponent`/`FpSignificand`** ✓
- [x] **Add `significandBits_eq` simp lemma** ✓ — `@[simp] significandBits_eq` in BitSize.lean
- [x] **Extract standalone `finite_FpExponent` / `finite_FpSignificand`** ✓ — plus helpers
  `finite_exponent_zero_of_subnormal`, `finite_exponent_ne_zero_of_normal`, `append_one_toNat`
- [x] **Simplify `lift_repr_toBitsTriple_significand`** ✓ — 75→4 lines (exponent: 27→3 lines)
- [x] **Encoding ±0 documented** ✓ — expected IEEE 754 behavior, not a bug
- [x] **Clean up `toBits` NaN branch** ✓ — extracted `one_significandBits_ne_zero`
- [x] **Remove commented-out `#eval` block** ✓

## LogComputable — Done
- [x] **Full pipeline sorry-free**: LogTaylor, LogComputableDefs, LogComputableSound, LogTermination, LogComputable
- [x] **File structure** (5 files, parallel to exp):
  - `LogTaylor.lean`: alternating series bounds for `log(1+t)`
  - `LogComputableDefs.lean`: computation defs, `logTarget`, `logComputableRun`
  - `LogComputableSound.lean`: bracket correctness (`logBounds_lower_lt_log`, `logBounds_log_le_upper`)
  - `LogTermination.lean`: width bounds + MVT irrationality gap + fuel sufficiency
  - `LogComputable.lean`: final assembly + `OpRefExecSound logTarget` instance
- [x] **Fuel**: `600 * ab^4 * 2^ab` (exponential, not polynomial like exp). See docstring in LogComputableDefs.lean for paths to polynomial fuel via Padé for log(1+z).

## LogApprox / fpLogFinite — DONE (2026-04-22)
- [x] **`LogApprox` typeclass + `fpLogFinite` + soundness** — 3 files, ~830
  lines total, sorry-free.  Parallel to `ExpApprox`/`fpExpFinite` in `Exp.lean`:
  - `Flean/Operations/Log.lean` (~498 lines): `LogApproxData` inductive
    (`exact sign mag e_base` / `sticky sign q e_base` — sign bit tracks
    log's negativity for `0 < x < 1`), `LogApprox` / `LogApproxSound`
    typeclasses (preconditions `0 < a.toVal ∧ a.toVal ≠ 1`), `fpLogFinite`
    (top-level branches: `x ≤ 0` → NaN, `x = 1` → `+0`, else dispatch),
    `fpLog : Fp → Fp` (IEEE semantics: `log(-∞) = NaN`, `log(+∞) = +∞`),
    `fpLogFinite_correct` (under `0 < a.toVal`), noncomputable concrete
    instance `logApproxConcrete` (priority 100).
  - `Flean/Operations/LogAdapter.lean` (~188 lines): adapter from
    `OpRefExec logTarget` / `OpRefExecSound logTarget` (provided by
    `LogComputable.lean`) → `LogApprox` / `LogApproxSound` at priority
    1000 (shadows the noncomputable concrete when `LogComputable` is
    imported).  Sign decided by `a.toVal (R := ℚ) < 1`.
  - `Flean/Operations/LogClose.lean` (~146 lines): bridge lemma
    `fpLogFinite_close` (positive input + finite witness → LSE-shaped
    `|logResult - log x| ≤ η·|log x| + Softmax.subnormalConst` bound,
    sign-symmetric via `RModeConj ℝ`) + `fpLogSumExp_concrete_error_bound`
    demo eliminating the last abstract hypothesis in the LSE pipeline
    (`η_log = η`, `logSubConst = Softmax.subnormalConst`).
  - Key structural differences from exp: sign handling (log can be
    negative), domain partial (NaN for `x ≤ 0`), `log(1) = 0` exact case.
  - Five `LogApproxSound` fields: `exact_mag_ne_zero`, `exact_value`
    (sign-folded `intSigVal` identity), `sticky_q_lower`, `sticky_interval`
    (brackets `|log x|`), `sticky_sign` (sign flips `|log|` back to `log`).
  - `fpLogSumExp_concrete_error_bound` and
    `fpCrossEntropy_concrete_error_bound` demos both shipped
    (LogClose.lean, ~230 lines total).  Abstract log hypothesis is gone
    from both pipelines.

## Shared Infrastructure (exp + log)
- `StickyTermination.lean`: `stickyExtractLoop_sound`, `stickyExtractLoop_pos_of_success`, `uniform_gap_from_pointwise`
- `Util.lean`: `Rat.den_lt_num_of_one_lt`, `Real.log_abs_sub_ge_div_max`, `geom_decay_bound`, `cube_lt_two_pow`, `two_mul_sq_lt_two_pow`
- Both exp and log use `uniform_gap_from_pointwise` to lift pointwise irrationality gaps to uniform gaps over bounded shifts

## ExpComputable Cleanup
- [x] **File splitting** — Done. Split into 4 files:
  - `ExpTaylor.lean` (203 lines): Taylor series (taylorExpQ, taylorRemainder, bounds)
  - `ExpComputableDefs.lean` (1121 lines): computation defs + bracket correctness
  - `ExpTermination.lean`: width bounds + Padé gap + fuel sufficiency
  - `ExpComputable.lean` (148 lines): final assembly + ExpRefExecSound instance
- [x] **Unify expBounds sign cases** — Extracted `expLowerBound`/`expUpperBound` to ExpTaylor.lean ✓
- [x] **Factor `cast_eq` helper** — Extracted as `Rat.cast_eq_natAbs_div_den` in Util.lean ✓
- [x] **Make `expShift_bound` concrete** — Direct `≤ prec + 9 + |k|` bound ✓
- [x] **Move `padeConvergenceN₀_le` to PadeExp.lean** ✓
- [x] **Extract `exp_effective_gap`** — Packages `pade_effective_delta` + `pade_delta_log_bound` per shift, used by `uniform_gap_from_pointwise` ✓

## Exp Code Audit Findings
- [x] **Move general lemmas to Util.lean** ✓
- [x] **Extract duplicate `k.natAbs` bound** ✓
- [x] **Fix misleading comment** ✓
- [x] **Trim exploratory comments** ✓
- [ ] **Missing API lemmas in ExpTaylor** — `taylorExpQ_pos` (strict positivity for n ≥ 1, y ≥ 0), `taylorRemainder_pos` (strict, for y > 0). Low priority.
- [x] **Constants documentation + tightening** — See below.

## Exp Termination Constants

Chain: `N₀ ≤ 27·ab → D ≤ ab^(113·ab) → 2D ≤ 2^L, L ≤ 500·ab·log₂ab → fuel = 100·ab·log₂ab + 1000`

| Constant | Location | Derivation | Tight value | Slack |
|----------|----------|------------|-------------|-------|
| **9** | `prec+9+|k|` shift bound (ExpTermination) | Exact: `prec+4-(k-5)` | 9 | Tight |
| **27** | `N₀ ≤ 27·ab` (PadeExp) | `5·ab` (m bound) + `17·ab` (M bound) + `5·ab` (s) | ~22 | ~20% |
| **113** | `D ≤ ab^(113·ab)` (ExpTermination) | `56·ab` (N!) + `56·ab` ((4b)^N) + `ab` (exp\|x\|) | Depends on N₀ | Cascades from 27 |
| **500** | `L ≤ 500·ab·log₂ab` (ExpTermination) | `1 + 113·ab·log₂ab`; 114 suffices since `1 ≤ ab·log₂ab` | **114** | **4.4x — tightened** |
| **100** (fuel mult) | `expFuel` (ExpComputableDefs) | Needs `iter ≈ L/10 < fuel`; with L≤114, need ~12 | **15** | **~7x — tightened** |
| **1000** (fuel const) | `expFuel` (ExpComputableDefs) | Small-ab edge cases | **200** | **~5x — tightened** |
| **100** (ab slack) | `ab` definition (ExpComputableDefs) | Need `ab ≥ 28` for `28ab ≤ ab²` | ~30 | ~3x |
| **10** (terms/iter) | Taylor order growth | Affects computation speed, not just proof | 10 | Not worth changing |
| **50** (ln2 bits/iter) | ln2 precision growth | Affects computation speed | 50 | Not worth changing |
| **52** (base ln2) | Base ln2 bits | Initial precision | 52 | Minor |

**Theoretical optimum**: The asymptotic growth `L = O(ab · log ab)` is optimal. The leading
constant 114 could be ~55-60 using Stirling (`N! ≈ (N/e)^N`) instead of `N! ≤ N^N` in the
`hD_pow` block. This is the main source of the remaining 2x slack: `N^N` vs `(N/e)^N` doubles
the exponent (113 → ~56, then 114 → ~57). Mathlib has Stirling bounds but wiring them through
would be a moderate refactor of `pade_delta_log_bound`.

## Linearize Tactic
- [x] **ℕ exponent support** — `pow_le_pow_right₀`/`pow_lt_pow_right₀` for ℕ exponents ✓
- [x] **omega in side goals** — `trySideGoalTactics` tries assumption → omega → exact_mod_cast → norm_num → linarith ✓
- [x] **`asInt` fix** — Proper literal/variable handling for omega compatibility ✓
- [x] **Non-literal base syntax** (`linearize (base := expr)`) ✓
  - Works for variables, products, any expression via `isDefEq` matching
- [x] **Reciprocal recognition** ✓ — `c/base^m ≤ c/base^n` via `div_le_div_of_nonneg_left` with recursive side goal solving
- [x] **`unfold_let` preprocessing** ✓ — `unfoldLetFVars` + `instantiateMVars` sees through `set` aliases
- [x] **Side goal `norm_cast` pass** ✓ — Already resolved by exact_mod_cast + asInt fixes
- [x] **Multiplicative monotonicity** — `bound_calc` tactic ✓ (see below)

Known limitations documented in memory/linearize-issues.md. Tests in FinalTest.lean.

## bound_calc Tactic — DONE
- [x] **Phase 1**: gcongr + rich subgoal dispatch ✓
- [x] **Synthesized bounds** (R1+R2): auto-bound `f.m`, `precNat`, etc. from context ✓
- [x] **Partial dispatch** (P4): close subgoals that can be solved, leave rest ✓
- [x] **Hint syntax**: `bound_calc [expr₁, expr₂]` for manual witnesses ✓
- [x] **`@[bound_calc]` attribute**: extensible registered lemma dispatch ✓
- [x] **`assumption_mod_cast`** in dispatch chain ✓
- Deployed to ~144 sites across 26 files
- Design doc: `Flean/BoundCalc/Design.md`; tests: `Flean/BoundCalc/TestCases.lean`

## zpow_norm Tactic — DONE
- [x] **Core**: Normalize zpow products, collapse `2^a * 2^b → 2^(a+b)`, bridge ℕ↔ℤ casts ✓
- [x] **Division**: `2^a / 2^b → 2^(a-b)` ✓
- [x] **Exponent solving**: delegates to `ring`/`omega` ✓
- [x] **Hypothesis mode**: `zpow_norm at h` ✓
- Deployed to 46 sites across 16 files
- Design doc: `Flean/ZpowNorm/Design.md`; tests: `Flean/ZpowNorm/TestCases.lean`

## Remaining Tactic Ideas

### A. `cast_bound` — ℕ↔ℤ↔ℝ inequality bridge (~110 sites)
Auto-bridge cast gaps for inequalities: `(f.m : R) < (2:R)^prec.toNat` → `(2:R)^prec`.
Chains `exact_mod_cast`, `zify`, `zpow_natCast`, `omega`. Partially subsumed by `zpow_norm` + `bound_calc`.

### B. Rounding case splitter (~95 sites)
Domain-specific: unfold rounding function → simp reduceDIte → three-way case split
(subnormal/normal/overflow) → unfold appropriate subroutine. Very repetitive in
Rounding/ files but narrow applicability.

## StorageFormats Extensions
- [x] **Capstone theorem**: `fromFp.toVal = RMode.round(fp.toVal)` when no overflow. ✓
  Chain: `fromFp_val_eq_intSigVal` → `roundSigCore_eq_roundIntSigM` → `RoundIntSigMSound` → `RMode.round`.
  Need: show `roundSigCore` with `rneRoundUp` matches `roundIntSigM` with RNE `shouldRoundUp`.
  Typeclasses: `[RMode R] [RModeExec] [RoundIntSigMSound R]` + hypothesis that `shouldRoundUp = policyShouldRoundUp .nearestEven`.
- [x] **Overflow correctness**: `fromFp_overflow` + `fromFp_overflow_saturate`/`_inf`/`_nan` ✓
  When `roundSigCore` overflows, `fromFp` delegates to `applyOverflow`:
  `.saturate` → `signedMaxFinite`, `.overflow` + `hasInf` → `infEncoding`, `.overflow` + `¬hasInf` → `canonicalNaN`.
- [ ] **E8M0 round-trip**: BLOCKED — `FloatFormat` requires `prec ≥ 2`, but E8M0 has `prec = 1` (manBits = 0).
  Would need either relaxing `FloatFormat.valid_prec` or a separate conversion path.
- [x] **General round-trip**: `roundtrip_general` in Extensionality.lean — structural proof via bitvector extensionality ✓
- **Note**: `hsigned : f.hasSigned = true` required everywhere — E8M0 (unsigned) is excluded from all FromFpCorrect theorems

## Mid-Term — Algorithm Error Analysis
- [x] **Kahan compensated summation** — Full Higham Theorem 4.3: `|ŝₙ - Σxᵢ| ≤ (2η + nη²)·Σ|xᵢ|` ✓
  - **Approach A** (four-ρ): standard error model, ρ₂ cancellation, second-order bounds, concrete trace bound
  - **Approach B** (TwoSum-exact): `StepTwoSumExact` → `stepResidual = ρ₁` → `traceTwoSumBound`
  - Triangle split: `traceTwoSumBound ≤ η·Σ|xᵢ| + η·traceCompSum`
  - Compensation induction: `traceCompSum ≤ |c₀| + η·traceAddMag`, `final_comp_le_eta_mul`
  - **Capstone**: `kahan_higham_bound` — `(2η + nη²)·Σ|xᵢ|` (Higham eq. 4.9)
  - ~1085 lines, sorry-free. Both approaches share `kahan_error_bound` base.
  - **Extensions** (documented in KahanSum.lean module docstring):
    - [x] **A. Self-contained bound**: `kahan_higham_bound_auto` eliminates `hM` entirely via energy invariant ✓
      `|ŝₙ - Σxᵢ| ≤ (η·(1 + (1+η)^{2n}) + n·η²·(1+η)^{2n}) · Σ|xᵢ|`
    - [x] **B. Weak backward error**: `ŝₙ = Σ(1+μᵢ)xᵢ`, `|μᵢ| ≤ 2η + nη²` ✓
      `kahan_weak_backward_error` + `_auto` via `error_distributable` (proportional distribution).
      Strong per-element form (Higham eq. 4.8: `|μᵢ| ≤ 2η + O((n-i+1)η²)`) deferred.
    - [x] **C. Pairwise comparison**: `pairwise_error_bound` + `kahan_eps_lt_pairwise_eps` in PairwiseSum.lean.
    - [x] **D. Neumaier variant**: `neumaier_abstract_error_bound` in NeumaierSum.lean.
      State, step witness with `delta_exact`, trace, telescoping, abstract error bound `η·Σ|comp+delta|`.
    - [x] **E. Connect `twoSum_exact`**: `step_twosum_exact_of_dekker` — Dekker condition → Sterbenz → exact compensation ✓
      Also: `step_twosum_exact_of_sub_exact` for the general case (first subtraction exact → full TwoSum exact).
- [x] **Dot product error bound** — `dp_error_bound` + `dp_error_bound_gamma` in DotProduct.lean.
  `|sₙ - x·y| ≤ ((1+η)^n-1)·Σ|xᵢyᵢ| ≤ γ_n·Σ|xᵢyᵢ|`. Sorry-free.
- [x] **Horner's method** — `horner_error_bound` + `_gamma` in Horner.lean.
  `|fl(p(x)) - p(x)| ≤ ((1+η)^{2n}-1)·p̃(|x|) ≤ γ_{2n}·p̃(|x|)` (Higham Thm 5.1). Sorry-free.
- [x] **FMA Horner** — `fma_horner_error_bound` + `_gamma` in HornerFMA.lean.
  `|fl(p(x)) - p(x)| ≤ ((1+η)^n-1)·p̃(|x|) ≤ γ_n·p̃(|x|)`. Half the exponent of non-FMA. Sorry-free.
- [x] **Compensated Horner** — `comp_horner_exact_decomposition` in CompensatedHorner.lean.
  `sₙ + hornerPoly(errors, 0, x) = p(x)` exact decomposition via `hornerPoly_affine`. Sorry-free.
- [ ] **Reverse Horner** — standard Horner on `1/x` with reversed coefficients.
  Same `γ_{2n}·p̃(|x|)` absolute bound (no improvement), but better conditioning for |x|>1.
  Ref: Burrus et al. (Rice). Low priority — the advantage is conditioning, not the error bound.
- [x] **Compensated Horner bound** — `comp_horner_bound` in CompensatedHorner.lean.
  `|result - p(x)| ≤ η|sₙ+r̃ₙ| + γ_{2m}·hornerPoly(|ẽ|, 0, |x|)`. Sorry-free.
  With exact EFTs: `O(η + n²η²)·p̃(|x|)`.
- [x] **Clenshaw's algorithm** — `clenshaw_exact_decomposition` in Clenshaw.lean.
  2D affine structure: `clenshawExact_affine` + `clenshawProp` (linear propagation).
  Exact decomposition: computed + error propagation = exact. Sorry-free.
- [x] **Affine fold abstraction** — `AffineFold.lean`: generic `affineFold`/`affineProp` over
  `AddCommGroup S`. Core theorem `affineFold_affine` + `affineFold_exact_decomposition`.
  Unifies Horner (1D), Clenshaw (2D), Jet Horner (2D). Sorry-free.
  Scalar + gauge bounds, per-index bounds, Horner instantiation.
- [x] **geomBound** — `GeomBound.lean`: `geomBound α β n = α · Σ (1+β)^k`. 23-lemma API.
  `geomBound_uniform`: bridge to `(1+α)^n - 1`. `geomBound_add`: composition.
  Division-free core (`mul_geomBound`), monotonicity, positivity.
- [x] **Four-parameter accumulator model** — `GeneralAccum.lean`: two-term output with
  separate error rates `(α_acc, α_off)` and magnitude growth `(β_acc, β_off)`.
  `weightedErrorSum_le_of_general_step` + `_uniform_step` + `_max` wrapper.
  `weightedErrorSum_append` (structural split) + `weightedErrorSum_compose'` (composition).
  Design doc: `AccumulatorBounds.md`.
- [x] **DotProduct/DotProductFMA via framework** — `AffineFoldInstances.lean`: κ=1 instantiation.
  Tight `dp_error_bound_tight` via four-parameter model (exponent n vs 2n).
- [x] **Jet Horner** — `JetHorner.lean`: simultaneous value+derivative (S = R × R).
  `polyDeriv` + recurrence + chain rule term. Third AffineFold instance. Sorry-free.
- [x] **Newton + jet Horner** — `NewtonHorner.lean`: sorry-free, ~725 lines.
  JetHornerStep/Trace, exact decomposition, value error bound ((1+η)^{2n}-1),
  exact Newton quadratic convergence, perturbed Newton ball invariance,
  NewtonStep structure, perturbation bounds, quotient perturbation, full composition.
- [ ] **Newton-Horner concrete instantiation** — Compute explicit convergence radii for
  common formats (binary32, binary64, binary16). Given polynomial degree `n`, compute
  the concrete `ρ` and `δ` for `perturbed_newton_ball`: `ρ` from the polynomial's
  root separation and conditioning, `δ = O(η · |p(x)/p'(x)|)` from the perturbation bound.
  For binary64 (η ≈ 1.1e-16), a degree-10 polynomial with well-separated roots would
  converge to ~1e-15 in 4-5 steps. Would demonstrate the library's end-to-end capability.
- [x] **Jet Horner derivative error bound** — `jetHorner_deriv_error_bound` in NewtonHorner.lean.
  L1 gauge `ν(v,d)=|v|+|d|` with contraction `κ=|x|+1`. Per-index weighted sum form.
  Cross-coupling handled via gauge framework rather than tight closed-form.
- [ ] **Newton reciprocal** — `x_{n+1} = x_n(2 - ax_n)`, quadratic convergence in floats.
  Two FP multiplications per step. Used in hardware division (Goldschmidt). The perturbed
  Newton framework applies directly with `p(x) = 1/a - x` (trivial Horner, degree 1).
- [ ] **Newton sqrt** — `x_{n+1} = (x_n + a/x_n)/2` or reciprocal form `y_{n+1} = y_n(3 - ay_n²)/2`.
  Reciprocal form avoids division. Used in hardware sqrt implementations (e.g. x86 FSQRT
  initial approximation + Newton refinement). Similar to Newton reciprocal framework.
- [x] **Mathlib Polynomial connection** — `hornerPoly_eq_eval` in PolynomialConnection.lean ✓
  `hornerPoly cs 0 x = (hornerListPoly cs).eval x` + derivative eval.
  hornerPoly now only needs `CommRing R` (typeclass cleanup).
  Follow-up items:
  - [x] **polyDeriv ↔ Polynomial.derivative** — `polyDeriv_eq_derivative_eval` in PolynomialConnection.lean ✓
    `polyDeriv cs 0 x = (hornerListPoly cs).derivative.eval x`.
  - [ ] **Backward error in Polynomial form** — restate `horner_backward_error` as
    `fl(p(x)) = p̃(x)` where `p̃ : R[X]` is a Mathlib polynomial with perturbed coefficients.
  - [ ] **hornerListPoly properties** — `natDegree`, leading coefficient, cons/append recurrences.
  - [ ] **Estrin sub-polynomial splitting** — express `p(x) = p_lo(x) + x^m · p_hi(x)` via
    `hornerListPoly` and reason about the tree-structured evaluation in Mathlib terms.
- [ ] **Estrin's method** — parallel polynomial evaluation: group pairs of Horner steps,
  evaluate sub-polynomials independently, combine. Error bound `γ_{2⌈log₂n⌉}·p̃(|x|)`
  (better than Horner's `γ_{2n}` for large n). Tree-structured variant of AffineFold,
  or direct analysis. Practically important for SIMD/pipelining.
  Ref: Muller et al., Handbook of FP Arithmetic, §5.3.
- [x] **Compensated dot product** (Ogita-Rump-Oishi) — CompensatedDotProduct.lean. Sorry-free.
  - `cdp_exact_decomposition`: `sₙ + Σ(σᵢ+πᵢ) = Σxᵢyᵢ` (exact telescoping)
  - `c_lane_telescoping`: `cₙ + Σ(c-errors) = Σ(corrections)` (exact)
  - `cdp_error_bound`: `|result - Σxᵢyᵢ| ≤ η|sₙ+cₙ| + ((1+η)^{2n}-1)·Σ|σᵢ+πᵢ|`
  - `cdp_error_bound_gamma_sq`: `|result - Σxᵢyᵢ| ≤ η|sₙ+cₙ| + γ_{2n}²·Σ|xᵢyᵢ|`
  - `cdp_correction_bound`: each `|σᵢ+πᵢ| ≤ ((1+η)²-1)·(|sᵢ₋₁| + |xᵢyᵢ|)`
  - Structures: `CDPStep` (computation), `CDPStepExact` (EFT), `CDPStepNormalRange`, `CDPTrace`
  - **Extension: tight γ_n² form** — The current γ_{2n}² uses the framework's 2n exponent
    for bounding Σ|corrections|. To get the standard γ_n² (Ogita Thm 4.3), need to
    extract a `DPTrace` from the s-lane of `CDPTrace` and apply the manual
    `dp_error_bound` (which has exponent n via zero-init + separate mul/add tracking).
    The `cdp_error_bound_gamma_sq` theorem takes `hcorr_bound` as a hypothesis, so
    users who prove the tighter `Σ|corrections| ≤ ((1+η)^n-1)·Σ|xᵢyᵢ|` get γ_n²
    automatically. Requires: s-lane DPTrace extraction function + proof that the
    extracted trace matches the original s-lane operations + apply `dp_error_bound`.
  Ref: Ogita, Rump, Oishi, "Accurate Sum and Dot Product" (2005).
- [ ] **Running error bounds** — computable error estimates alongside computation:
  `r_i = (1+η)|x·r_{i-1}| + |v_i|·η` for Horner, etc. Prove `actual_error ≤ running_bound`
  at each step. Practically important: user can check at runtime if answer is good enough
  without knowing condition number a priori. Would be a verified implementation, not just
  a bound theorem.
- [x] **Compensated Newton** — `CompensatedNewton.lean`: compensated Horner *inside* Newton iteration ✓
  `CompNewtonStep` structure + `comp_newton_perturbation` bound.
  `newton_perturbation_from_eval_errors` in NewtonHorner.lean: generic composition
  of evaluation errors + rounding → Newton perturbation. ~140 lines, sorry-free.
  Near roots, perturbation is `O(η/|p'(x*)|)` instead of `O(nη/|p'(x*)|)`.

## Mid-Term — Backward Error & Conditioning
- [x] **Backward error framework** — `BackwardError.lean`: `PerturbationGauge`, `BackwardResult`,
  `MixedResult`, `error_distributable`, condition number bridge (`forward_le_cond_mul_backward`).
  Design doc: `Flean/Operations/BackwardErrorDesign.md`.
- [x] **Dot product backward error** — `dp_backward_error` + `_gamma`: `fl(x·y) = Σ(1+μᵢ)xᵢyᵢ`,
  `|μᵢ| ≤ (1+η)^n-1` or `γ_n`. Constructive perturbations via `error_distributable`.
- [x] **Scalar composition** — `backward_compose_one_round`: `(1+δ)·Σ(1+μᵢ)vᵢ = Σ(1+μ'ᵢ)vᵢ`
  with `|μ'ᵢ| ≤ ε₁+ε₂+ε₁ε₂`.
- [x] **Condition number (summation)** — `componentwiseCondNumber` + `forward_rel_le_cond_mul_backward`:
  `rel_fwd_error ≤ ε · Σ|xᵢ|/|Σxᵢ|`.
- [x] **Horner backward error** — `horner_backward_error` (existential) + `horner_backward_result`
  (structured `BackwardResult` with `componentwiseRelGauge`) ✓. `|μᵢ| ≤ (1+η)^{2n}-1`.
- [ ] **General condition numbers** — formalize `cond(f, x) = ‖J_f(x)‖·‖x‖/‖f(x)‖` and prove the
  fundamental relation `forward_error ≤ cond · backward_error · (1 + O(η))`.
  For polynomial evaluation: standard Wilkinson-type bounds.
- [x] **Full gauge-based composition** — `PerturbationLift`, `PerturbationMetric`, `BackwardResult.compose` ✓
  Two tracks: multiplicative (`compose_scalar_sum/weighted_sum` for `componentwiseRelGauge`)
  and additive (`BackwardResult.compose` with `PerturbationMetric` + `PerturbationLift`).
- [ ] **Concrete `PerturbationLift` instances** — needed to make `BackwardResult.compose` usable:
  - [x] Summation lift (`uniformGauge`→`scalarAbsGauge`): `Λ = 1`, distribute perturbation evenly ✓
  - [ ] Horner/weighted-sum lift: pull back output perturbation to coefficient perturbations.
    `Λ = condition number` (= `Σ|cᵢx^i|/|p(x)|`). Connects to `componentwiseCondNumber`.
  - [ ] Linear function lift (general): any `f(x) = Ax` with `Λ = ‖A⁻¹‖` or pseudo-inverse.
- [ ] **`MixedResult.compose_no_lift`** — fallback composition into `MixedResult` when no
  lift exists. Backward part from `brA`, forward residual bounded by Lipschitz constant
  of `g` times `brB.eps`. Needs Lipschitz-like hypothesis on `g`. Low priority.
- [x] **Composition example: Horner + rounding** — `horner_compose_round` in BackwardError.lean ✓
  Composes `horner_backward_result` with scalar rounding via `compose_scalar_weighted_sum`.
  `horner_compose_round_eps`: backward error = `(1+η)^{2n+1} - 1` on coefficients.
- [ ] **Wilkinson polynomial root conditioning** — root sensitivity bound:
  `|Δx_k| ≈ |Δaⱼ| · Πᵢ≠ₖ |x_k - x_i|⁻¹`. Connects to Newton-Horner convergence radius:
  ill-conditioned roots → smaller convergence basin → more Newton steps needed.
  Would need Mathlib Polynomial connection first.
- [ ] **Triangular solve / LU / Cholesky backward error** — classical Wilkinson chapter,
  big new chunk and the main remaining linear-algebra direction for the framework.
  Triangular solve is the right entry point: simpler than full LU, but exercises matrix
  algorithms end-to-end. Standard result (Higham Ch. 8): forward substitution computes
  `x̂` satisfying `(L + ΔL)x̂ = b` with `|ΔL| ≤ γₙ · |L|` (componentwise). Then LU/Cholesky
  build on top via composition. Multi-session arc:
  - [ ] **Forward substitution backward error** — sequential `xᵢ = (bᵢ - Σⱼ<ᵢ Lᵢⱼxⱼ)/Lᵢᵢ`.
    Per-row uses dot product + division + subtraction. Likely composes via existing
    `FpDotProductBound` + scalar perturbation. Result lives on the `L` matrix space.
  - [ ] **Back substitution** — symmetric to forward sub.
  - [ ] **LU decomposition backward error** — Doolittle/Crout, plus row pivoting.
    Combine with forward+back sub for full linear-system solve `(A+ΔA)x̂ = b`.
  - [ ] **Cholesky** — for SPD matrices, tighter bound `|ΔA| ≤ γₙ₊₁·|L||Lᵀ|`.
  - Would establish a `BackwardMatrixResult` analogue: perturbation gauge on matrix space.

## Mid-Term — ML Primitives
- [x] **Softmax numerical stability** — `Softmax.lean`: mathematical softmax, shift invariance,
  overflow analysis, FP-level no-overflow theorem. Sorry-free.
  - `softmax_shift_eq`: softmax invariant under uniform translation
  - `fpExpFinite_no_overflow`: exp on non-positive input doesn't overflow (via monotonicity + idempotence)
  - `round_le_largestFiniteFloat` / `round_ne_pos_inf_of_le_largest`: general rounding safety lemmas
  - Extensions:
    - [x] **FP softmax computation** — `fpSoftmaxOf` + generic `FpSumBound` framework. Sorry-free.
      - `FpSum.FpSumBound` structure — bundles sum result + relative error bound
      - `FpSumBound.ofPairwise` / `ofNaive` — constructors (NaiveSum via right-spine PairwiseSum.Trace)
      - `fpSoftmaxOf` (bare) + `fpSoftmaxFromSum` (wraps FpSumBound)
      - Safety: `fpExpFinite_exists_finite`, `fpSoftmaxOf_exists_finite` (finite-output guarantees)
      - Error bound: `fpSoftmaxOf_error_bound` — `|fpSoftmax_i - softmax_i| ≤ softmaxErrorCoeff εsum · softmax_i`
        where `softmaxErrorCoeff εsum = (η² + 2η + δ)/(1-δ)`, `δ = η + εsum·(1+η)` (Higham-style). For small η,εsum ≈ 3η + εsum.
      - Simpler bound: `softmaxErrorCoeff_le_linear` — `≤ 7η + 3εsum` under `η + 2εsum ≤ 1/2`
      - Convenience wrappers: `fpSoftmaxOf_error_bound_of_sumBound` (FpSumBound-taking), `fpSoftmax_shifted_error` (auto-extracts exps/result)
      - Companion theorems: `fpSoftmax_sum_close_to_one`, `fpSoftmax_preserves_argmax_pair`
      - Bundle: `FpSoftmaxResult` — packages the full pipeline; `.error_bound`, `.sum_close_to_one`, `.preserves_argmax_pair` methods
      - `FpSum.FpSumBound.weaken`/`reindex`/`congr`/`append` — compositional adapters
      - Pre-shift: `fpMax`, `fpSoftmaxShift` (subtracts c from each)
      - Subnormal-tolerant building blocks: `subnormalConst`, `ulp_half_le_unified`,
        `exps_unified_error_of_correct`, `sum_exps_unified_error`, `denom_unified_error`.
      - [x] **Subnormal-tolerant softmax** — factored around private Sb-parametric core
        `fpSoftmax_apply_core_bound`. Both main variants derive from core:
        - `fpSoftmaxOf_error_bound_subnormal` (factor-of-2): `m = (1-δ)S/2`, hypothesis
          `h_S_margin : (1-δ)S > 2·N·sc`. Bound: `2·softmaxErrorCoeff εsum · σ_i +
          subnormalSoftmaxAbs xs εsum · subnormalConst`.
        - `fpSoftmaxOf_error_bound_subnormal_tight` (no factor-of-2 loosening):
          `m = (1-δ)S - N·sc`, hypothesis `h_m_pos : 0 < subnormalSoftmaxDenomMargin xs εsum`.
          Coefficients `softmaxErrorCoeff_tight`/`subnormalSoftmaxAbs_tight` reduce to
          `softmaxErrorCoeff` / `1 + (1+η)/(1-δ)` as `N·sc → 0`.
        - `fpSoftmaxOf_error_bound_subnormal_shifted` (factor-of-2, S ≥ 1): xs-indep
          coefficients via `subnormalSoftmaxAbs_le_of_S_ge_one`.
        - Underflow-tolerant via `fpDivFinite_toVal_zero_of_num_m_zero` (private) +
          case split on `(exps i).m = 0` inside the core.
        - `_of_sumBound` wrappers for both variants (take `FpSum.FpSumBound` adapter).
        - Companions: `fpSoftmax_sum_close_to_one_subnormal{,_tight}`,
          `fpSoftmax_preserves_argmax_pair_subnormal{,_tight}`.
        - Bundles: `FpSoftmaxResultSubnormal{,Tight}` with `.error_bound`/
          `.sum_close_to_one`/`.preserves_argmax_pair` methods.
        - Helpers: `exps_nonneg_unified`, `exps_pos_of_m_ne_zero`,
          `softmaxErrorCoeff_tight_le_of_S_ge_one`, `subnormalSoftmaxAbs_tight_le_of_S_ge_one`.
      - Naive-sum step helpers: `fpAddFinite_exists_finite_of_nonneg_bounded`,
        `naiveSum_step_finite_of_nonneg_bounded` — automate per-step `Fp.finite`
        witness. Full automated NaiveSum-from-bounded-list builder deferred.
      - [x] **Shifted tight variant** — `fpSoftmaxOf_error_bound_subnormal_tight_shifted`
        in Softmax.lean (+ `FpSoftmaxResultSubnormalTight.shifted` bundle wrapper).
        Uses `softmaxErrorCoeff_tight_le_of_S_ge_one` + `subnormalSoftmaxAbs_tight_le_of_S_ge_one`
        to produce the xs-independent tight bound under S ≥ 1.
      - [x] **End-to-end pipeline theorem** — `fpSoftmax_end_to_end_error_bound`
        in Softmax.lean (section `EndToEnd`). Takes raw `xs`, an exact-shift
        witness `xs'` satisfying `(xs' j).toVal = (xs j).toVal - (fpMax xs hn).toVal`,
        plus the standard pipeline components; produces the xs-independent tight
        bound. S ≥ 1 is derived from the argmax via private `fpMax_attained`.
      - [ ] **Non-exact-shift regime** for the end-to-end softmax — track the
        `fpSubFinite (xs i) c` rounding error all the way through. Currently
        the pipeline theorem requires exactness via Sterbenz, which fails when
        `|xs i|` and `|c|` differ by more than a factor of 2. Plan: introduce
        `xs' i = xs i - c + δᵢ` with `|δᵢ| ≤ η·|xs i - c| + subnormalConst`,
        push through `exp` (where a relative perturbation becomes
        `exp(x'+δ)/exp(x') = exp(δ) ≈ 1 + δ`), then through the sum, and bound
        the difference `softmax(xs'.toVal) - softmax(xs.toVal - c)`. ~200-400
        lines. Tighter pipeline but narrower gain — defer unless a user hits
        the Sterbenz constraint in practice.
      - [x] **Concrete `FpSumBound` instances**:
        - `FpSumBound.ofNaive` (already existed — `(1+η)^(n-1) - 1` via right-spine PairwiseSum)
        - `FpSumBound.ofKahanTrace` in `FpSum.lean` (tight `2η + n·η²` via `kahan_higham_bound`)
        - Demos: `fpSoftmax_naiveSum_error_bound` (+ `_shifted`), `fpSoftmax_kahanSum_error_bound`
          in `Softmax.lean`, wiring each into `_tight_of_sumBound`.
        - [x] `FpSumBound.ofNeumaierTrace` in `FpSum.lean` — loose
          `n·η·((1+η)^{n+1}-1) + (1+η)·((1+η)^n-1)` bound via
          `neumaier_concrete_bound + comp_growth + triangle`. Drops the
          compensator, so bound is O((n+1)·η·S) leading — worse than
          `ofKahanTrace` and roughly matching `ofNaive`. Docstring flags this.
          Demo: `fpSoftmax_neumaierSum_error_bound` in `Softmax.lean`.
        - [x] **`FpSumBoundCompensated` struct** in `FpSum.lean` with
          `ofNeumaierTrace` (tight `O(n²η²)` via `neumaier_concrete_bound`)
          + `compensateAndRound` bridge to `FpSumBound` via one final
          `fpAdd(sum, comp)` (new `relErr = cb.relErr·(1+η) + η`). Demo
          `fpSoftmax_neumaierCompensated_error_bound` in `Softmax.lean`.
          Adapters: `weaken`, `weakenComp`, `reindex`, `congr`, `append`
          (compensated-preserving via separate sum/comp `fpAdd`s;
          `new_relErr = εM(1+η) + η(1+2cεM)`, `new_compErr = (1+η)cεM`),
          `appendCollapsed` (→ `FpSumBound`). Struct now carries `compErr`
          + `h_comp_bound` as a second bound on `|comp|` alone; helper
          lemmas `sigma_abs_le`, `sum_abs_le`.
    - [x] **Log-sum-exp** — `LogSumExp.lean` (~715 lines, sorry-free).
      - Real-valued: `logsumexp`, `logsumexp_shift_eq`, `logsumexp_ge`.
      - Helper: `log_rel_error_bound` — `|log y - log x| ≤ ε/(1-ε)` when `|y-x| ≤ ε·x`.
      - Main: `fpLogSumExp_end_to_end_error_bound` — raw `xs`, exact-shift witness,
        abstract `(logResult, η_log, logSubConst, h_log_close)` witness, `fpAddFinite`
        final step, `h_final_ne` (sign-symmetric via `[RModeConj ℝ]`). Effective sum
        error `ε_sum = (η + relErr(1+η)) + (1+relErr)·n·sc`, induced log error
        `D_log = ε_sum/(1-ε_sum)`. Bound:
        `η·|LSE| + (1+η)·(η_log·(LSE-c) + (1+η_log)·D_log + logSubConst) + subnormalConst`.
      - Bundle: `FpLogSumExpResult xs hn` with `.error_bound` method.
      - Demos: `fpLogSumExp_naiveSum_error_bound`, `_kahanSum_error_bound`,
        `_neumaierSum_error_bound` (loose), `_neumaierCompensated_error_bound` (tight).
      - Log step stays abstract (no `fpLogFinite`/`LogApprox` exists yet); when
        one lands, a thin wrapper supplies `h_log_close`.
    - [x] **Dot-product bound adapters** — `FpDotProductBound.ofDotProduct`
      + `.ofDotProductFMA` in `Flean/Operations/FpDotProduct.lean` (the
      work previously tracked as a to-do "FpSumBound.ofDotProduct" —
      that name was a misnomer, since `FpSumBound` bounds `Σ xs_i.toVal`
      while the dot product bound is against `Σ xs_i·ys_i`; the right
      output type is `FpDotProductBound`, which already exists).  Both
      adapters wrap `DPTrace` / `FMADPTrace` with `relErr = (1+η)^n − 1`.
      `ofDotProduct` needs `RModeIdem` for the zero-init exact-step trick;
      `ofDotProductFMA` doesn't.  Also already shipped:
      `FpDotProductBoundCompensated` + `.ofProducts` + `.compensateAndRound`.
    - [x] **Cross-entropy loss** — `CrossEntropy.lean` (~505 lines, sorry-free).
      - Real-valued: `crossEntropy`, `crossEntropy_shift_eq`,
        `crossEntropy_nonneg`.
      - Main: `fpCrossEntropy_end_to_end_error_bound` — composes full LSE
        pipeline + per-index shift-rounding witness
        (`h_shift_close`, abstract like LSE's `h_log_close`) +
        `FpDotProductBound ys r`.  Loss = `-dp.result`.  Bound shape:
        `dp.relErr · Σ|y_i · r_i| + Σ|y_i| · (η·|x_i - lse| + subnormalConst + Δ_LSE)`
        where `Δ_LSE` is the LSE end-to-end bound propagated uniformly
        through the shift (since `r_exact_i - (x_i - lse) = lse - LSE`
        is constant across `i`).
      - Bundle: `FpCrossEntropyResult xs ys hn` with `.loss` and
        `.error_bound`.
      - Demo: `fpCrossEntropy_naiveSum_error_bound` — NaiveSum for the
        LSE inner sum + `ofDotProductFMA` for the outer dot product
        (FMA adapter avoids needing `RModeIdem ℝ`).
      - Session prompt preserved at
        `.claude/notes/cross-entropy-session-prompt.md` for reference.
    - [ ] **Temperature scaling** — `softmax(xs/T)`, convergence to argmax as T→0.

## Mid-Term — Mixed-Precision & ML
- [ ] **Mixed-precision accumulation** — error of computing in FP16/BF16 and accumulating
  in FP32 (bridges StorageFormats + Operations). Key theorem: if `x_i : StorageFp E4M3`
  and accumulation is in `FloatFormat.Binary32`, bound the additional error from the
  format conversion at each step. Needs `fromFp_correct` composed with operation error bounds.
- [ ] **Quantization error bounds** — given `fromFp : Fp fmt₁ → StorageFp fmt₂`, bound
  `|fromFp(x).toVal - x.toVal|` in terms of the target format's machine epsilon.
  Machinery exists (fromFp_correct + relative error bounds), needs composition theorem.
  Concrete instances: Binary32→E4M3, Binary16→E5M2, Binary32→BF16.
- [ ] **Stochastic rounding** — probabilistic rounding mode used in ML training where
  `E[round(x)] = x` (unbiased). Would need: new rounding mode definition, proof of
  unbiasedness, probabilistic error analysis (`E[|error|] ≤ η/2` vs worst-case `η`),
  and convergence-in-expectation for summation/SGD. Significant new direction.
- [ ] **Block floating point** — shared-exponent formats (e.g., Microsoft MSFP, used in
  ML accelerators). Group of values shares one exponent, each has reduced mantissa.
  Would need new `BlockFormat` structure + conversion correctness + error bounds.

## Mid-Term — Infrastructure & Automation
- [ ] **Constraint-tagged values framework** — generalize the "normalness
  certificate" idea to a full framework of structural `P : FiniteFp → Prop`
  tags (`IsNonneg`, `IsSimplex_ε`, `IsProb`, `IsUnit_ε`, `HasRangeBound`,
  `IsPostReLU`, etc.) propagated through ops via a `Preserves` typeclass,
  with *tag-specialized error bounds* that tighten when a caller has extra
  structural info. Detailed plan: [tag-framework-plan.md](tag-framework-plan.md).
  Phased rollout:
  - [x] **Phase 0 (pilots)** — four plain-theorem pilots, all sorry-free
    and wired into `Flean/Tags.lean` aggregator:
    - `Flean/Tags/Simplex.lean` (~185 lines): `IsSimplex` + permutation
      preservation + `FpDotProductBound.simplex_bound` (bound in `max|xᵢ|`).
    - `Flean/Tags/Normal.lean` (~128 lines): `IsNormal` + `add_nonneg`
      preservation + `ulp_half_le_of_normal` (drops `+ subnormalConst` tail).
    - `Flean/Tags/Sterbenz.lean` (~145 lines): `IsSterbenz` + negation
      preservation + `fpSubFinite_exact_of_sterbenz` (error = 0 exactly).
    - `Flean/Tags/Nonneg.lean` (~175 lines): `IsNonneg` + `fpMul`/`fpAdd`
      preservations + composition demo `fpMulAdd_isNonneg` threading the
      tag through two different ops.
    - `Flean/Tags/SoftmaxBounded.lean` (~153 lines): first contact with
      a real downstream consumer. `IsBoundedRange lo hi xs` input tag
      + bridge `→ ∀ i, isNormalRange (exp xs_i)` (real-analysis step via
      `exp_int_mul_log2`) + `fpSoftmax_bound_of_bounded` wrapper that
      consumes the tag and delegates to `fpSoftmaxOf_error_bound` (the
      existing clean variant). Validates that natural input tags feed
      downstream hypotheses via a single bridge theorem.
    Pilots span four flavors of tag-specialized bound + two threading tests:
    - **Structural isolation** (`IsSimplex`): bound's RHS shape changes
      but magnitude doesn't shrink. Win is fewer joint dependencies.
    - **Additive-tail elimination** (`IsNormal`): drop a `+ c` term
      (`subnormalConst`). Strict tightening.
    - **Multiplicative-tail elimination** (`IsSterbenz`): drop a `· ε`
      factor — full rounding error collapses to 0. Strongest tightening.
    - **Cross-op composition** (`IsNonneg`): tag propagates through mul
      then add. Two preservation applications compose cleanly.
    - **Input-tag → existing-theorem bridge** (`IsBoundedRange`): a
      natural input constraint tag generates the `isNormalRange (exp ·)`
      hypothesis that the clean softmax bound already requires. First
      validation that tags survive contact with a pre-existing proof.
    Key cross-pilot findings (full assessments at the top of each file):
    - Plan's "tag-specialized bounds are tighter" framing is misleading
      as a blanket statement. Some tags isolate structure, others tighten
      magnitude, others force exactness. Phase 1 language should be
      careful to distinguish.
    - Nonempty-domain preconditions can be absorbed into tags
      (`IsSimplex.pos`). Pattern: structural tags should eat degeneracy
      preconditions they already imply.
    - Tag-as-structure vs. tag-as-wrapper is fine either way; four
      pilots used structures with 1, 2, and 5 fields.
    - **Preservation lemmas are boilerplate** — each fp-op preservation
      for `IsNonneg` is "round preserves nonneg via monotonicity +
      zero." A meta-lemma (`round_preserves_nonneg : RModeMono +
      RModeZero → IsNonneg x → fp_op x = Fp.finite f → IsNonneg f`) could
      discharge the family once. Phase 1 typeclass work should factor
      this.
    - **Finiteness is orthogonal to the tag**. Tags track semantic
      structure; finiteness tracks numerical well-definedness. The
      preservation lemmas all take finiteness as a separate hypothesis.
      Framework should not bundle these.
    - **Zero-case handling is ad-hoc per op**. `fpAddFinite` has
      `fpAddFinite_zero_left_val`; `fpMulFinite` needed inline unfolding.
      A uniform `fp_op_finite_toVal` covering both zero and nonzero
      cases would simplify all future tag-preservation work.
    - **Bridge theorems to existing codebase are natural**. The
      `IsBoundedRange → isNormalRange(exp ·)` bridge in
      `SoftmaxBounded.lean` is one real-analysis lemma (~15 lines) that
      discharges a real Softmax precondition automatically. The
      framework just needs a clean "tag-to-hypothesis" surface — no
      extra machinery required.
    - **Not all preconditions factor cleanly**. Softmax's `h_quot_nr`
      (quotient in normal range) depends on `denom`, a computed
      quantity — not derivable from input tags alone. Phase 1 design
      should acknowledge that some hypotheses remain manual and not
      force everything through the tag surface.
  - **Phase 0.5 — items queued before Phase 1 framework commitment**:
    - [x] **Phase 1 design doc** (top priority). Synthesize the 5 pilots
      into a concrete framework proposal covering: tag representation
      (struct vs class), preservation-lemma factoring, bridge library
      structure, parametric-tag composition, zero-case handler,
      finiteness separation, and explicit non-goals. Drafted at
      `.claude/notes/tag-framework-phase1-design.md`. Later updates
      folded in review decisions (§§1.8, 1.9) and the `h_quot_nr` /
      `IsBoundedRange.fpAdd` canonical signatures (locked in §§3.3,
      3.4 as code blocks — library stays sorry-free).
    - [~] **Close the `h_quot_nr` gap**. Signature **locked** in the
      design doc §3.3 (Phase 1 architecture deliverable). Proof
      deferred to a focused FP-error-analysis session; not added to
      library as a `sorry` stub (preserves sorry-free invariant).
    - [~] **Parametric tag propagation through ops**. Signatures for
      `IsBoundedRange.fpAdd` / `.fpMul` **locked** in design doc §3.4
      (as ∃-form to avoid pinning output-interval formulas prematurely).
      Proofs deferred to a focused session. Not added as `sorry` stubs.
    - [x] **Promote `round_nonneg_of_nonneg` into `Rounding/`**. Done
      as `Flean/Rounding/RoundPreserves.lean::round_preserves_nonneg`.
      `Nonneg.lean` updated to import + use the kernel.
  - [x] **Phase 1 (framework)** — SHIPPED (2026-04-20). Note: the original
    plan of introducing a `Preserves` typeclass was **deliberately rejected**
    in the Phase 1 design doc §1.1 (plain structures + meta-lemmas instead,
    for typeclass-inference perf reasons flagged in the plan). What
    actually landed: `round_preserves_nonneg` meta-lemma kernel,
    unified `fp{Add,Mul,FMA}Finite_round_witness` helpers,
    `Flean/Tags/Bridges/` structure, `exp_isNormalRange` +
    `quot_isNormalRange` bridges, six `IsBoundedRange` propagation
    theorems, `FpInterval` interval algebra.  See `.claude/notes/
    tag-framework-phase1-design.md` for the record-of-decisions.
  - [x] **Phase 2 (specialized bounds)** — PARTIAL.  The two named items:
    - *Drop `subnormalConst` from Softmax under `IsNormal`-style spread*:
      delivered via `fpSoftmax_bound_of_separated` (`Flean/Tags/
      SoftmaxBounded.lean`).  The analogous LSE/CE wrappers that would
      drop the tail under the same regime are not yet shipped.
    - *Drop `fpSubFinite` rounding under `IsSterbenz`*: delivered as
      the `fpSubFinite_exact_of_sterbenz` + `sterbenzShift_of`
      extraction in `Flean/Tags/Sterbenz.lean` + `Flean/Tags/
      SterbenzShift.lean`, plus `fpLogSumExp_sterbenzShift_error_bound` /
      `fpCrossEntropy_sterbenzShift_error_bound` wrappers that
      discharge `h_shift_exact` from the vector-level tag.  Softmax
      analog queued.
    - LayerNorm received full Phase 2 treatment (see Phase 2 design
      doc).  Its cascaded + fully-tagged bounds serve as the template
      for how far any given primitive can be pushed.
- [ ] **Normalness certificate** — a predicate on `Fin n → FiniteFp` (and single
  `FiniteFp` values) asserting all values stay in a bounded-exponent range
  (no subnormals, no near-overflow), with propagation lemmas through the basic
  ops (add/mul/FMA/div/sqrt) and through the algorithm-level structures
  (`FpSumBound`, `FpDotProductBound`, `FpMatVecBound`, etc.). Consumers of
  current bounds carry a `subnormalConst` additive tail (e.g. Softmax,
  LogSumExp); a normalness witness would let them drop it, making the bound
  purely multiplicative `|result − exact| ≤ relErr · |exact|`. High leverage:
  (a) makes "if inputs are normal, accuracy is obscenely better" a provable
  statement suitable for a suggestion tool, (b) tightens all downstream ML
  bounds, (c) the right primitive for real-vs-FP divergence quantification.
  Complements the "Overflow condition formalization" entry below (normalness
  implies no overflow at the format's edges, so sharing the same API makes
  sense). Natural first tag in the tag-framework plan above.
- [ ] **Straight-line program verifier** — given a sequence of FP ops as a `List FpOp`
  (where `FpOp = add | mul | fma | ...`), auto-derive the error bound by chaining
  per-op lemmas. Could be a tactic (`fp_bound`) or a verified interpreter. We have all
  the per-op error lemmas; the gap is chaining them. Would subsume manual error proofs
  for simple programs.
- [ ] **Overflow condition formalization** — formalize sufficient no-overflow conditions.
  E.g., "if all inputs ≤ B and polynomial degree ≤ n, then Horner doesn't overflow in
  binary64". Currently we assume `hno_ov` everywhere; could derive it from input bounds
  and format parameters. Would make end-to-end theorems more self-contained.
- [ ] **Faithful rounding** — result within 1 ulp of exact (weaker than correct rounding).
  Some hardware ops and libm functions only guarantee this. Formalize as
  `|round(x) - x| ≤ ulp(round(x))` and adapt error bounds. The relative error becomes
  `2η` instead of `η`, so all our bounds would have "faithful" variants with doubled constants.

## Mid-Term — Mathlib Connections
- [ ] **Power series connection** — our exp/log Taylor bounds are about truncated power series.
  Connect to Mathlib's `PowerSeries` or `HasSum` for formal manipulation. Would let us
  state remainder bounds in terms of Mathlib's analytic function theory.
- [ ] **Gauge → Seminorm** — our `Gauge` is an `AddGroupSeminorm` minus the `neg'` axiom
  (no negation symmetry requirement), with generic codomain `R` instead of `ℝ`.
  Our L1 gauge does satisfy `neg'` and homogeneity, so it *is* a seminorm.
  Could add `neg'` to `Gauge` (all instances satisfy it) and provide a coercion
  `Gauge → AddGroupSeminorm` for access to Mathlib's functional analysis lemmas.
  Low priority — current framework is self-contained and sufficient.

## Long-Term
- [ ] Error-minimizing tactic (reorder FP computations to minimize error bound)
- [ ] Verified computation examples (e.g. count of floats between 0 and 1)
- [ ] Gradient descent error analysis — bound `|x_{k+1} - x*|` under FP arithmetic for
  common loss functions. Connects mixed-precision + Newton-like convergence analysis.
- [ ] Higher-order jets (k-jets for k-th derivative, `S = Fin (k+1) → R` or `R^{k+1}`)
  — generalizes jet Horner to compute `p(x), p'(x), ..., p^{(k)}(x)` simultaneously.
  The linear map becomes a `(k+1)×(k+1)` lower-triangular Toeplitz matrix.
  AffineFold framework applies directly with appropriate gauge.
- [ ] Prove approximation bounds on specific papers (e.g. arxiv 2410.00907)
- [ ] **Interval arithmetic** — connection between our error bounds and interval methods.
  Formalize `[a, b]` arithmetic and prove that our rounding model produces valid intervals.
  Would enable verified numerical integration, ODE solvers, etc.
- [ ] **Automatic differentiation error** — FP error in forward-mode AD. The jet Horner
  framework is essentially forward-mode AD for polynomials; generalize to arbitrary
  composition of elementary ops. Each op introduces rounding in both value and derivative
  channels (cross-coupling, as in jet Horner).
