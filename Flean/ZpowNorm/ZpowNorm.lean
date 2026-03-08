/-
Copyright (c) 2026. All rights reserved.
-/
import Flean.Util
import Flean.FloatFormat
import Lean.Elab.Tactic.Basic

/-!
# ZpowNorm Tactic

Normalizes equalities involving `(2 : R) ^ e` expressions over ordered fields.

## What it handles

- **Product collapse:** `2^a * 2^b = 2^(a+b)`
- **Division:** `2^a / 2^b = 2^(a-b)`
- **ℕ→ℤ cast bridge:** `(2:R)^n.toNat = (2:R)^(n:ℤ)` (with FloatFormat precision lemmas)
- **Bare 2 recognition:** `2 * 2^a = 2^(a+1)`
- **Scalar passthrough:** `x * 2^a * 2^b = x * 2^(a+b)`

## Algorithm

1. Normalize both sides via `simp only` with curated zpow lemma set
2. Close the remaining goal via `rfl` / `congr 1; ring` / `congr 1; omega`

See `Flean/ZpowNorm/Design.md` for full design rationale.
-/

open Lean Elab Meta Tactic

/-- Try running a tactic syntax, return true if it closed all goals. -/
private def tryClose (stx : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic stx
    return true
  catch _ =>
    restoreState saved
    return false

elab "zpow_norm" : tactic => do
  -- Phase 1: Normalize zpow expressions
  --
  -- This simp set:
  -- (a) Converts npow to zpow: (2:R)^n → (2:R)^(↑n : ℤ)
  -- (b) Simplifies ℕ→ℤ casts in exponents: prec.toNat → prec, etc.
  -- (c) Collapses zpow products: 2^a * 2^b → 2^(a+b)
  -- (d) Handles division: 2^a / 2^b → 2^(a-b)
  -- (e) Handles bare 2 factors: 2 * 2^n → 2^(1+n)
  -- (f) Cleans up: 1 * x → x, 2^0 → 1, 2^1 → 2
  let simpStx ← `(tactic|
    simp only [
      -- (a) npow → zpow
      ← zpow_natCast,
      -- (b) ℕ→ℤ exponent cast simplification
      FloatFormat.prec_toNat_eq, FloatFormat.prec_sub_one_toNat_eq,
      Nat.cast_mul, Nat.cast_add, Nat.cast_sub, Nat.cast_ofNat,
      -- (c) zpow product collapse
      two_zpow_mul, mul_two_zpow_right,
      -- (d) zpow division
      two_zpow_div, mul_two_zpow_div_two_zpow, div_two_zpow_mul_two_zpow,
      -- (e) bare 2 as zpow
      two_mul_two_zpow, two_zpow_mul_two,
      -- (f) cleanup
      one_mul, mul_one, zpow_zero, zpow_one
    ])
  try
    evalTactic simpStx
    -- If simp closed all goals, we're done
    if (← getGoals).isEmpty then return
  catch _ => pure ()

  -- Phase 2: Try to close the goal
  -- After normalization, both sides should have the same structure up to
  -- exponent arithmetic. Try increasingly powerful closers.
  if ← tryClose (← `(tactic| rfl)) then return
  if ← tryClose (← `(tactic| (congr 1; ring))) then return
  if ← tryClose (← `(tactic| (congr 1; push_cast; ring))) then return
  if ← tryClose (← `(tactic| (congr 1; simp only [FloatFormat.prec_toNat_eq, FloatFormat.prec_sub_one_toNat_eq]; ring))) then return
  if ← tryClose (← `(tactic| (congr 1; omega))) then return
  if ← tryClose (← `(tactic| ring)) then return

  throwError "zpow_norm: could not close the goal"
