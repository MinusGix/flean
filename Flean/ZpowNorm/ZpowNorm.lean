/-
Copyright (c) 2026. All rights reserved.
-/
import Flean.Util
import Flean.FloatFormat

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

1. Normalize both sides: collect zpow factors, bridge ℕ→ℤ casts, collapse products
2. Match scalar prefixes
3. Solve exponent equality via `ring` / `omega` / `push_cast; ring`

See `Flean/ZpowNorm/Design.md` for full design rationale.
-/

-- TODO: Implement zpow_norm tactic
-- Placeholder so TestCases.lean can import this file

