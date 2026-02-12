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

## Long-Term
- [ ] Error-minimizing tactic (reorder FP computations)
- [ ] Linearize tactic improvements (multiplicative cases, edge cases)
- [ ] Verified computation examples (e.g. count of floats between 0 and 1)
- [ ] Gradient descent error analysis for common functions
- [ ] Prove approximation bounds on specific papers (e.g. arxiv 2410.00907)
