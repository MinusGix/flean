/-
Copyright (c) 2026. All rights reserved.
-/
import Flean.BoundCalc.BoundCalc
import Flean.FloatFormat

/-!
# Registered `@[bound_calc]` lemmas

Domain-specific lemmas registered for automatic dispatch in `bound_calc`.
These are tried when standard tactics (positivity, omega, linarith, etc.)
fail to close a subgoal.

To register a new lemma, tag it with `@[bound_calc]`:
```
@[bound_calc] theorem my_useful_bound : ... := ...
```
or retroactively tag an existing lemma:
```
attribute [bound_calc] SomeModule.useful_lemma
```
-/

-- Ceiling: x ≤ ⌈x⌉
attribute [bound_calc] Int.le_ceil

-- FloatFormat: 4 ≤ 2^prec (ℕ version)
attribute [bound_calc] FloatFormat.nat_four_le_two_pow_prec

-- FloatFormat: (4 : R) ≤ (2 : R)^prec.toNat (generic version)
attribute [bound_calc] FloatFormat.prec_pow_le
