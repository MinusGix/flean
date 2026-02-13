# Fast2Sum: `add_error_representable` Proof Plan

## File: `Flean/Operations/Fast2Sum.lean`, line 181

## What needs proving

```lean
theorem add_error_representable (mode : RoundingMode) (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (hmode : mode = .NearestTiesToEven ∨ mode = .NearestTiesAwayFromZero)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s_fp : FiniteFp) (hs : fpAddFinite mode a b = Fp.finite s_fp) :
    ∃ t_fp : FiniteFp,
      (t_fp.s = false ∨ 0 < t_fp.m) ∧
        (t_fp.toVal : R) = (a.toVal : R) + b.toVal - s_fp.toVal
```

## Proof Strategy

### Step 1: Handle error = 0
If `(a+b) - s_fp.toVal = 0`, return zero float `⟨false, min_exp, 0, ...⟩`.

### Step 2: New helper lemma — nearest-mode bound

**Key lemma to add (doesn't exist in codebase):**
```
For nearest modes with positive x in normal range and finite result f:
  f.toVal ≤ 2 * x - (findPredecessorPos x hxpos).toVal
```

This says `roundUp_error ≤ roundDown_distance`. Proof follows EXACT same structure as
`roundNearestTiesToEven_is_roundDown_or_roundUp` (RelativeErrorBounds.lean:189):
- Unfold roundNearestTiesToEven, dismiss x=0/small/overflow cases
- `split_ifs at hf with h1 h2 h3`
- Pred cases (h1, h3): `f.toVal = pred.toVal ≤ x`, so `f.toVal ≤ 2x - pred.toVal` by `linarith`
- Succ case (h2): `x > midpoint = (pred+succ)/2`, so `succ < 2x - pred` by `linarith`
- Tie case (¬h1,¬h2): `x = midpoint`, so `succ = 2x - pred` by `linarith`

Write for both TE and TA, combine with `cases hmode`.

### Step 3: Derive `|error| ≤ b.toVal`

Chain:
1. `roundDown(a+b) ≥ a.toVal` — from `roundDown_ge_of_fp_le` (Idempotence.lean:871)
2. Helper gives `s_fp.toVal ≤ 2*(a+b) - roundDown(a+b).toVal ≤ 2*(a+b) - a.toVal = a + 2b`
3. Combined with `a ≤ s_fp.toVal` (already proved as `round_sum_ge_left`):
   `0 ≤ s_fp.toVal - a.toVal ≤ 2b`, so `error = (a+b) - s ∈ [-b, b]`

**isNormalRange(a+b)** needed for the helper. Proof:
- Lower: When error ≠ 0, `a` must be normal (subnormal sums are exact), so `a+b ≥ 2^min_exp`
- Upper: From finite result + nearest mode overflow check: `a+b < overflowThreshold < 2^(max_exp+1)`
  - Use `toVal_abs_lt_overflow` (Idempotence.lean:515) pattern

### Step 4: Express error as integer × 2^e₀

- `e₀ = min(a.e, b.e) - prec + 1`
- `a+b = isum * 2^e₀` (from `fpAddFinite_exact_sum`)
- `s_fp.toVal = s_fp.m * 2^(s_fp.e - prec + 1)` (from `FiniteFp.toVal_pos_eq`, s_fp.s = false)
- `s_fp.e ≥ min(a.e, b.e)` (from `s_fp.toVal ≥ a.toVal` + `toVal_lt_zpow_succ`)
- Factor: `s_fp.toVal = (s_fp.m * 2^k) * 2^e₀` where `k = s_fp.e - min(a.e,b.e)`
- So `error = (isum - s_fp.m * 2^k) * 2^e₀ = r * 2^e₀`

### Step 5: Bound `|r| < 2^prec`

From `|error| ≤ b.toVal = b.m * 2^(b.e - prec + 1)`:
- `|r| ≤ b.m * 2^(b.e - min(a.e,b.e))`
- If min = b.e: `|r| ≤ b.m < 2^prec` ✓
- If min = a.e: `|r| ≤ b.m * 2^(b.e - a.e) ≤ a.m < 2^prec` (from `b.toVal ≤ a.toVal`) ✓

### Step 6: Construct float

- If `r > 0`: `exists_finiteFp_of_nat_mul_zpow` (ToVal.lean:385) with `mag = r`, `e_base = e₀`
- If `r < 0`: Same with `mag = |r|`, then negate the result
- Exponent bounds: `e₀ ≥ min_exp - prec + 1` ✓, `e₀ + prec - 1 = min(a.e,b.e) ≤ max_exp` ✓

## Key Existing Lemmas

| Lemma | Location | Purpose |
|-------|----------|---------|
| `roundDown_ge_of_fp_le` | Idempotence.lean:871 | roundDown(y) ≥ f when f.toVal ≤ y |
| `findPredecessorPos_le` | Neighbor.lean:74 | roundDown(x) ≤ x |
| `roundUp_ge` | RoundUp.lean:83 | x ≤ roundUp(x) |
| `rnTE_is_roundDown_or_roundUp` | RelativeErrorBounds.lean:189 | Dispatch lemma (template for helper) |
| `rnTA_is_roundDown_or_roundUp` | RelativeErrorBounds.lean:244 | TA version |
| `fpAddFinite_exact_sum` | Add.lean:163 | a+b = isum * 2^e₀ |
| `FiniteFp.toVal_pos_eq` | ToVal.lean:330 | toVal = m * 2^(e-p+1) |
| `FiniteFp.toVal_lt_zpow_succ` | ToVal.lean:339 | toVal < 2^(e+1) |
| `exists_finiteFp_of_nat_mul_zpow` | ToVal.lean:385 | Construct float from mag*2^e |
| `FiniteFp.toVal_neg_eq_neg` | ToVal.lean:80 | (-f).toVal = -f.toVal |
| `round_sum_ge_left` | Fast2Sum.lean:40 | a.toVal ≤ s_fp.toVal |
| `toVal_abs_lt_overflow` | (search in Idempotence.lean) | f.toVal < overflowThreshold |
| `overflowThreshold` | FloatFormat.lean:555 | (2 - 2^(1-p)/2) * 2^max_exp |

## Also TODO
- Add `import Flean.Operations.Fast2Sum` to `Flean/Operations.lean`
- Run `lake build` to verify
