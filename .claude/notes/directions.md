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

## Near-Term
- [ ] **Close remaining sorries** (1 remaining, pre-existing/unrelated)
  - `Linearize/FinalTest.lean:78` — multiplicative linearize test case
  - ~~`Ulp.lean:21` — Harrison's ULP~~ ✓ defined + linked to standard ULP
- [x] **Encoding round-trip** — `toBits_ofBits` + `ofBits_toBits` both sorry-free ✓
- [ ] **Common constants verification** — prove binary32/64 constants match claimed values

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

## Long-Term
- [ ] Error-minimizing tactic (reorder FP computations)
- [ ] Verified computation examples (e.g. count of floats between 0 and 1)
- [ ] Gradient descent error analysis for common functions
- [ ] Prove approximation bounds on specific papers (e.g. arxiv 2410.00907)
