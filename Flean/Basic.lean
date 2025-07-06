import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Bits

import Flean.FloatFormat
import Flean.Util
import Flean.Defs
import Flean.ToVal

/-! Based off of 'Handbook of Floating Point Arithmetic' by Jean-Michel Muller et al. -/
-- Some designs of floating point arithmetic talk about floats as a subset of the reals/rationals with some extra properties
-- This is helpful for nicer integration and extreme generality, but I believe is overkill and obscures the core idea.
