# Div.lean / OddInterval.lean Refactoring Notes

## Completed
- `round_eq_on_odd_interval` — all sorry spots eliminated
- `overflow_threshold_outside_odd_interval` in OddInterval.lean — compiles clean

## Potential Refactors (ordered by impact)

### 1. Unify `rnTE_no_crossing` and `rnTA_no_crossing` (~220 lines saved)
These two theorems are ~240 lines each and ~95% identical. Differences:
- `rnEven_ge_inf` vs `rnAway_ge_inf`
- `rnEven_pos_succ_overflow` vs `rnAway_pos_succ_overflow`
- `rnEven_above_mid_roundUp` (strict `>`) vs `rnAway_ge_mid_roundUp` (weak `≥`)
- `rnEven_below_mid_roundDown` vs `rnAway_lt_mid_roundDown`

Approach: parameterize over `roundNear : R → Fp` and 4 callback lemmas.
The strict/weak midpoint difference is harmless — we always have strict from interval bounds.
Difficulty: medium (mechanical, ~1-2 hours).

### 2. Extract m=0 midpoint parity as standalone lemma (~100 lines saved)
Lines 753-867 (rnTE) / 993-1088 (rnTA) are identical self-contained parity arguments.
Does NOT depend on which rounding mode — purely about `succ_fp.toVal / 2` being
outside the odd interval when `pred_fp.m = 0`.
Could be: `theorem midpoint_zero_pred_outside_odd_interval ...`

### 3. Extract adjacency proof `hadj` as standalone lemma
Lines 696-713 — proves no representable float strictly between pred and succ
using `roundDown_mono`, `roundUp_mono`, and `hno_rep`. Purely about representable
floats in the interval, independent of rounding mode. Used in both theorems.

### 4. Extract `roundUp_finite_implies_le` helper
The proof that `roundUp w = Fp.finite succ_fp → w ≤ succ_fp.toVal` appears 4 times
(lines 723-735 / 844-854 / 968-979 / 1065-1075). Each time it goes through
`findSuccessorPos` case analysis. Should be a one-liner helper.
Note: `val_lt_thresh_of_roundUp_finite` in RoundNearest.lean (line 687) does
something related but for the threshold, not for `w ≤ succ_fp.toVal`.

### 5. Clean up stale comments
Lines 676-689 have abandoned reasoning about the m=0 case that meanders through
several false starts before the actual approach.

## Naming Improvements

### `overflowThreshold` abbrev (project-wide, 53 occurrences across 6 files)
The expression `(2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp`
should become an `abbrev` in FloatFormat.lean. Use `abbrev` not `def` to keep
transparency for `linarith`/`rw`. Files affected:
- FloatFormat.lean (define it + update 3 support lemmas)
- RoundNearest.lean (18 occurrences)
- Div.lean (13 occurrences)
- RelativeErrorBounds.lean (11 occurrences)
- OddInterval.lean (3 occurrences)
- RoundIntSig.lean (3 occurrences)
- Idempotence.lean (2 occurrences)

### `noRepresentableInInterval lo hi` abbrev
The quantifier `∀ f : FiniteFp, f.s = false → 0 < f.m → ¬(lo < f.toVal ∧ f.toVal < hi)`
appears in both no_crossing theorems, `round_eq_on_odd_interval`,
`roundDown_eq_of_no_representable`, etc.

### NOT recommended: bundling interval bounds
Keep `hv_lo` and `hv_hi` as separate hypotheses — `linarith` eats them directly.
Bundling into `inOddInterval` conjunction would require constant `.1`/`.2`.
