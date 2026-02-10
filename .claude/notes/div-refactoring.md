# Div.lean / OddInterval.lean Refactoring Notes

## Completed
- `round_eq_on_odd_interval` — all sorry spots eliminated
- `overflow_threshold_outside_odd_interval` in OddInterval.lean — compiles clean
- `overflowThreshold` abbrev — project-wide rename done
- `noRepresentableIn` abbrev — done
- Extract m=0 midpoint parity as `midpoint_zero_pred_outside_odd_interval` in OddInterval.lean (-55 lines)
- Extract `finite_toVal_lt_overflowThreshold` and `le_toVal_of_roundUp_finite` helpers (-32 lines)
- Unify `rnTE_no_crossing` / `rnTA_no_crossing` into parametric `roundNearest_no_crossing` (-112 lines)

## Remaining Refactors

### 5. Clean up stale comments
Minor cleanup of abandoned reasoning comments in the proof bodies.

## Naming Improvements

### NOT recommended: bundling interval bounds
Keep `hv_lo` and `hv_hi` as separate hypotheses — `linarith` eats them directly.
Bundling into `inOddInterval` conjunction would require constant `.1`/`.2`.
