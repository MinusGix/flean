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
- [ ] **Encoding round-trip** — prove finite floats fit in bit repr, bit-level equality equivalence
- [ ] **Common constants verification** — prove binary32/64 constants match claimed values

## ExpComputable Cleanup
- [x] **File splitting** — Done. Split into 4 files:
  - `ExpTaylor.lean` (203 lines): Taylor series (taylorExpQ, taylorRemainder, bounds)
  - `ExpComputableDefs.lean` (1121 lines): computation defs + bracket correctness
  - `ExpTermination.lean` (1559 lines): width bounds + Padé gap + fuel sufficiency
  - `ExpComputable.lean` (148 lines): final assembly + ExpRefExecSound instance
- [x] **Unify expBounds sign cases** — Extracted `expLowerBound`/`expUpperBound` to ExpTaylor.lean ✓
- [x] **Factor `cast_eq` helper** — Extracted as `Rat.cast_eq_natAbs_div_den` in Util.lean ✓
- [x] **Make `expShift_bound` concrete** — Direct `≤ prec + 9 + |k|` bound ✓
- [x] **Move `padeConvergenceN₀_le` to PadeExp.lean** ✓

## Exp Code Audit Findings
- [x] **Move general lemmas to Util.lean** — 9+ lemmas in ExpComputableDefs/ExpTermination already marked `omit [FloatFormat]`:
  - `nat_floor_div_mul_le` (ExpComputableDefs:311) — generic floor division bound
  - `real_lt_nat_floor_div_succ_mul` (ExpComputableDefs:318) — generic floor upper bound
  - `two_mul_zpow_neg_succ` (ExpComputableDefs:330) — zpow simplification
  - `exp_int_mul_log2` (ExpComputableDefs:378) — `exp(k * log 2) = 2^k`
  - `exp_arg_red` (ExpComputableDefs:385) — `exp(x) = 2^k * exp(x - k*log 2)`
  - `log2_gt_half` (ExpComputableDefs:475), `log2_lt_one` (483), `log2_lt_seven_eighths` (491)
  - `rat_abs_le_natAbs` (ExpComputableDefs:498)
  - `exp_sub_le_mul_exp` (ExpTermination:262) — general MVT-type bound
- [x] **Extract duplicate `k.natAbs` bound** — `k.natAbs ≤ 2 * x.num.natAbs + 1` proved twice in ExpTermination (~lines 1052-1081 and 1192-1201, ~30 lines each). Should be a shared lemma.
- [x] **Fix misleading comment** — ExpTermination:1300 says "sorry-ed helper bounds" but there are no sorries. Quick fix.
- [x] **Trim exploratory comments** — `expBounds_lower_lt_exp` (ExpComputableDefs:869-954) has ~25 lines of exploration comments that could be condensed.
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

## Long-Term
- [ ] Error-minimizing tactic (reorder FP computations)
- [ ] Linearize tactic improvements (multiplicative cases, edge cases)
- [ ] Verified computation examples (e.g. count of floats between 0 and 1)
- [ ] Gradient descent error analysis for common functions
- [ ] Prove approximation bounds on specific papers (e.g. arxiv 2410.00907)
