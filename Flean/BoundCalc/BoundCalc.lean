/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Tactic.GCongr
import Flean.Linearize.Linearize

/-!
# BoundCalc tactic

`bound_calc` automates monotonicity reasoning for products, divisions, and powers.
It calls `gcongr` to decompose the goal structurally, then dispatches subgoals
with a chain of standard tactics.

## Usage

```lean
-- Instead of: mul_le_mul h1 h2 (by positivity) (by positivity)
-- Write:
by bound_calc
```

See `BoundCalc/Design.md` for the full design and `BoundCalc/TestCases.lean` for examples.
-/

open Lean Elab Tactic in
/-- `bound_calc` decomposes monotonicity goals via `gcongr`, then dispatches
subgoals with: `assumption | le_refl | positivity | omega | norm_num | linearize | linarith`. -/
elab "bound_calc" : tactic => do
  -- First try gcongr to decompose the goal
  -- Then dispatch each subgoal with a chain of tactics.
  -- We use `try linearize` because linearize may throw errors on non-power goals
  -- rather than failing gracefully.
  evalTactic (← `(tactic|
    gcongr <;> first
      | assumption
      | exact le_refl _
      | positivity
      | omega
      | (norm_num; done)
      | linarith
      | linearize
  ))
