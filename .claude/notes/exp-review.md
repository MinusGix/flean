# Exp Implementation Review — Action Items

Tracked list from code review of the 8 exp-related files.
Status: [ ] = todo, [x] = done, [-] = skipped/deferred

## 1. Extract `expComputableRun_loop_sound`
- **File:** `Flean/Operations/ExpComputable.lean`
- **Fix:** Extracted `expComputableRun_loop_sound` combining both sticky proofs' preambles
- **Status:** [x]

## 2. Move `pow_div_factorial_geometric_bound` to Util
- **File:** `Flean/NumberTheory/PadeExp.lean` → `Flean/Util.lean`
- **Fix:** Moved both `pow_div_factorial_geometric_bound` and `pow_div_factorial_effective`
- **Status:** [x]

## 3. Move `padeP_abs_le` to PadeExpDefs.lean
- **File:** `Flean/Operations/ExpTermination.lean` → `Flean/NumberTheory/PadeExpDefs.lean`
- **Fix:** Moved with docstring, near other padeP properties
- **Status:** [x]

## 4. Factor common pattern in `expBounds_r_width_le`
- **File:** `Flean/Operations/ExpTermination.lean`
- **Issue:** ~150 lines with 4 sign cases sharing some structure
- **Assessment:** Less duplicated than initially thought. `recip_bound` already extracted. Realistic savings ~20 lines.
- **Status:** [-] deferred (marginal improvement)

## 5. Address `choose_pade_recurrence_nat` heartbeats
- **File:** `Flean/NumberTheory/PadeExp.lean`
- **Fix:** Replaced ~100-line proof with ~30-line version. Key: `zify` early, split k=0 case, single `nlinarith [h1, h2]`. No `maxHeartbeats` needed.
- **Status:** [x]

## 6. Split PadeExp.lean
- **Split:** `PadeExpDefs.lean` (719 lines) + `PadeExp.lean` (949 lines)
- **PadeExpDefs:** defs, clearing denoms, Padé condition, remainder bound, positivity, `padeP_abs_le`, non-vanishing
- **PadeExp:** effective bounds, cross product recurrence, convergence threshold, effective delta
- **Status:** [x]

## 7. Extract `abs_ge_of_int_gap` / `floor_eq_of_close`
- **File:** `Flean/NumberTheory/ExpEffectiveBound.lean`
- **Assessment:** Neither lemma is actually used outside this file currently (only a comment reference). Low priority.
- **Status:** [-] deferred (unused outside defining file)

## Lower priority / future

### Extract cast bridge
- `toVal_rat_cast_eq_real` lemma for `(a.toVal (R := ℚ) : ℝ) = a.toVal (R := ℝ)`

### Factor sticky cell extraction into generic pattern
- The bracket-check-refine loop could be parameterized over an abstract bracket oracle

### Split ExpComputableDefs.lean (~940 lines)
- Thread 1 bracket correctness proofs could be their own file

### Document `expFuel` +200 constant
- Add concrete worst-case example
