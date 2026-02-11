# Unwieldy Goal Audit

This document tracks theorem/lemma statements whose goal/type signatures are hard to read, especially where the goal includes `let`, `match`, or very long arithmetic expressions.

## Scope and Method

- Focused on declaration headers (`theorem`/`lemma ... : ... :=`) rather than proof bodies.
- Prioritized:
  - Goal statements containing `let` / `match` / nested `if`.
  - Very long multi-line theorem statements that are hard to scan.

## Group A: Explicit `let`/`match` In Goal Type

These are the strongest readability candidates.

| File | Declaration | Why it is unwieldy | Suggested direction |
|---|---|---|---|
| `Flean/Rounding/RoundNearest.lean:410` | `rnEven_pos_unfold` | Previously used inline `let midpoint := ...` + nested `if` chain. | Completed: statement now targets `rnEvenPosCore` (`Flean/Rounding/RoundNearest.lean:373`). |
| `Flean/Rounding/RoundNearest.lean:441` | `rnAway_pos_unfold` | Previously used inline midpoint/tie `if` chain. | Completed: statement now targets `rnAwayPosCore` (`Flean/Rounding/RoundNearest.lean:382`). |
| `Flean/Operations/Div.lean:89` | `fpDivFinite_exact_quotient` | Previously used local `let q`, `let r` in theorem goal. | Completed: theorem now uses `divQ`/`divR` aliases (`Flean/Operations/Div.lean:40`, `Flean/Operations/Div.lean:43`). |
| `Flean/Operations/Sterbenz.lean:67` | `sterbenz_aligned_diff_bound` | Previously used local `let e_min`, `let isum` in theorem goal. | Completed: theorem now targets `sterbenzAlignedDiffInt` (`Flean/Operations/Sterbenz.lean:60`) with `sterbenzEMin` (`Flean/Operations/Sterbenz.lean:57`). |
| `Flean/Rounding/RoundNormal.lean:74` | `floor_isNormal_of_bounds` | Previously bound `e`/`m`/`hb` via theorem-goal `let`s. | Completed: theorem goal is now direct (`isNormal (floorScaledNormal x).natAbs`) using `floorScaledNormal` (`Flean/Rounding/RoundNormal.lean:70`). |
| `Flean/Order.lean:945` | `lt_def` | Previously had raw `match (x, y)` case tree in theorem statement. | Completed: statement now reads `x < y ↔ is_total_lt x y`. |
| `Flean/Order.lean:947` | `le_def` | Previously expanded the `match` tree inline in theorem statement. | Completed: statement now reads `x ≤ y ↔ (is_total_lt x y ∨ x = y)`. |

## Group B: Long Multi-Line Goal Types (No `let` Required)

These are still difficult to read because the theorem header is overloaded.

| File | Declaration | Why it is unwieldy | Suggested direction |
|---|---|---|---|
| `Flean/Rounding/RoundDown.lean:305` | `roundDown_nat_mul_zpow` | Very long hypothesis list and large constructed `Fp.finite` target. | Completed: statement now targets `Fp.finite (mkRoundDownNatMulZpowTarget ...)`, with validity packaged in `isValid_roundDownNatMulZpowTarget` (`Flean/Rounding/RoundDown.lean:221`). |
| `Flean/Rounding/RoundUp.lean:238` | `roundUp_nat_mul_zpow` | Same pattern as above in ceil direction. | Completed: statement now targets `Fp.finite (mkRoundUpNatMulZpowTarget ...)`, with validity packaged in `isValid_roundUpNatMulZpowTarget` (`Flean/Rounding/RoundUp.lean:158`). |
| `Flean/Rounding/RoundUp.lean:391` | `roundUp_nat_mul_zpow_carry` | Carry-specialized variant with similarly heavy signature. | Completed: statement now targets `Fp.finite (mkRoundUpNatMulZpowCarryTarget ...)`, with validity packaged in `isValid_roundUpNatMulZpowCarryTarget` (`Flean/Rounding/RoundUp.lean:363`). |
| `Flean/Rounding/RoundNearest.lean:410` | `rnEven_pos_of_roundDown_roundUp` | Many continuation hypotheses (`hmid_*`) and large assumptions block. | Completed: midpoint cases are bundled in `rnEvenMidpointCases` (`Flean/Rounding/RoundNearest.lean:401`) with shared term `rnMidpoint` (`Flean/Rounding/RoundNearest.lean:379`), and theorem now targets `rnEvenPosCore` directly. |
| `Flean/Rounding/OddInterval.lean:1114` | `round_eq_on_odd_interval` | Many interval assumptions and mode dispatch in one theorem. | Completed: interval endpoints/membership are now named (`oddIntervalLo`, `oddIntervalHi`, `inOddInterval` at `Flean/Rounding/OddInterval.lean:788`), and theorem takes membership hypotheses instead of 4 raw bounds. |
| `Flean/Operations/FMA.lean:142` | `fpFMAFinite_exact_sum` | Dense arithmetic with duplicated aligned-integer expression. | Completed: aligned product/addend/sum terms are now named (`fmaAlignedProdInt`, `fmaAlignedAddInt`, `fmaAlignedSumInt`) with shared exponent helpers (`fmaProdE`, `fmaEMin`) at `Flean/Operations/FMA.lean:92`. |
| `Flean/Operations/Add.lean:156` | `fpAddFinite_exact_sum` | Similar dense aligned-sum expression. | Completed: addition now uses named aligned helpers (`finiteSignedInt`, `alignedSignedInt`, `addAlignedSumInt`) at `Flean/Operations/Add.lean:104`, and theorem goal is flattened through those names. |
| `Flean/Operations/RoundIntSig.lean:1500` | `sticky_roundIntSig_eq_round` | Long assumptions and mode/sign dependent statement. | Completed: sticky interval membership is now packaged as `inStickyInterval` (`Flean/Operations/RoundIntSig.lean:1384`), with sign split into `sticky_roundIntSig_eq_round_pos` + sign-transport helper before the final dispatcher theorem. |

## Proposed Refactor Queue (Iteration Plan)

1. `RoundNearest` unfold lemmas (`rnEven_pos_unfold`, `rnAway_pos_unfold`) - completed via `rnEvenPosCore`/`rnAwayPosCore`.
2. `Order` `lt_def`/`le_def` match-based theorem statements - completed.
3. `Div` + `Sterbenz` local-`let` theorem goals - completed.
4. `RoundNormal` `floor_isNormal_of_bounds` - completed via `floorScaledNormal`.
5. Large rounding bridge theorems (`roundDown_nat_mul_zpow`, `roundUp_nat_mul_zpow`, `...carry`) - completed with `mk...Target` constructors and dedicated validity lemmas to keep theorem goals flat.
6. `RoundNearest` midpoint wrapper theorem (`rnEven_pos_of_roundDown_roundUp`) - completed via `rnMidpoint` + `rnEvenMidpointCases` decomposition.
7. `OddInterval` mode-constancy theorem (`round_eq_on_odd_interval`) - completed via interval endpoint/membership aliases and compact theorem inputs.
8. `FMA` exact-sum theorem (`fpFMAFinite_exact_sum`) - completed via named aligned-term helpers and a flattened theorem goal.
9. `Add` exact-sum theorem (`fpAddFinite_exact_sum`) - completed via shared aligned-significand helper names and simplified theorem/proof surface.
10. `RoundIntSig` sticky wrapper (`sticky_roundIntSig_eq_round`) - completed via `inStickyInterval` and a positive-core + sign-transport decomposition.

Rationale:
- Start where abstraction risk is low and readability gain is immediate.
- Reuse those abstractions in larger theorem families after patterns stabilize.

## Candidate Abstractions to Discuss

- `def`/`abbrev` for repeated arithmetic kernels:
  - aligned signed integer terms,
  - quotient/remainder aliases for division,
  - midpoint decision core for nearest rounding.
- Small context structures bundling repeated hypotheses:
  - normal/subnormal range constraints,
  - non-overflow/inexact side conditions,
  - odd-interval assumptions.
- Statement-shaping style:
  - prefer `theorem foo (ctx : Ctx ...) : P ctx := ...` over 15+ raw arguments.
  - keep theorem goal proposition “flat” and push computational scaffolding into named defs.

## Decisions (Current)

- Extra top-level `def`/`abbrev` names are acceptable when they are natural terms and improve readability.
- `def` vs `abbrev` remains situational:
  - prefer `def` when the name represents a conceptual object we expect to reason about repeatedly;
  - prefer `abbrev` for lighter-weight readability aliases with minimal conceptual weight.
- Defer context-record refactors for now; revisit after the first “normal pass” using helper defs/abbrevs.
- Completed readability pass:
  - Added `condNeg` in `Flean/Defs.lean` and switched repeated signed-int conditionals to it in `Add`, `FMA`, and `Sterbenz`.
  - Added local notations `prec`/`precNat` in those files to reduce repeated `FloatFormat.prec` verbosity in theorem statements/proofs.

## Open Questions

1. Any additional constraint for choosing `def` vs `abbrev` beyond the current guideline above?
2. After first pass, do we want context records per subsystem (`Round*`, `Operations/*`) or a shared style?

## Working Notes

- This list is intentionally focused on readability pain points, not proof difficulty.
- We can trim or expand the candidate set as we refactor and see which abstractions pay off.
