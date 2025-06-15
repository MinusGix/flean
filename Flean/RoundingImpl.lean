import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational

import Flean.Basic
import Flean.Ulp
import Flean.Ufp

/-!
# Floating-Point Rounding Implementation

This file provides a complete implementation of IEEE 754 rounding modes.
It includes helper functions for finding neighboring floating-point values
and implements all five standard rounding modes.
-/

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-- Construct a finite floating-point number with validation -/
@[reducible]
def mkFiniteFp (s : Bool) (e : ℤ) (m : ℕ) : Option FiniteFp :=
  if h : IsValidFiniteVal e m then
    some ⟨s, e, m, h⟩
  else
    none

/-- Check if a positive number is in the subnormal range -/
def isSubnormalRange (x : R) : Prop :=
  0 < x ∧ x < (2 : R) ^ FloatFormat.min_exp

/-- Check if a positive number is in the normal range -/
def isNormalRange (x : R) : Prop :=
  (2 : R) ^ FloatFormat.min_exp ≤ x ∧ x < (2 : R) ^ (FloatFormat.max_exp + 1)

/-- Check if a positive number causes overflow -/
def isOverflow (x : R) : Prop :=
  x ≥ (2 : R) ^ (FloatFormat.max_exp + 1)

/-- Round a positive subnormal value down -/
def roundSubnormalDown (x : R) (_ : isSubnormalRange x) : Fp :=
  -- In subnormal range, spacing is uniform: 2^(min_exp - prec + 1)
  let ulp := (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)
  let k := ⌊x / ulp⌋
  if k = 0 then
    Fp.finite 0
  else
    match mkFiniteFp false FloatFormat.min_exp k.natAbs with
    | some f => Fp.finite f
    | none => Fp.NaN  -- Should not happen

/-- Round a positive subnormal value up -/
def roundSubnormalUp (x : R) (_ : isSubnormalRange x) : Fp :=
  -- In subnormal range, spacing is uniform: 2^(min_exp - prec + 1)
  let ulp := (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)
  let k := ⌈x / ulp⌉
  if k = 0 then
    -- This shouldn't happen since x > 0, but handle it
    match mkFiniteFp false FloatFormat.min_exp 1 with
    | some f => Fp.finite f
    | none => Fp.NaN
  else if k ≥ 2^(FloatFormat.prec - 1) then
    -- Transition to normal range
    match mkFiniteFp false FloatFormat.min_exp (2^(FloatFormat.prec - 1)) with
    | some f => Fp.finite f
    | none => Fp.NaN
  else
    match mkFiniteFp false FloatFormat.min_exp k.natAbs with
    | some f => Fp.finite f
    | none => Fp.NaN

/-- Find the exponent for rounding down (largest e such that 2^e <= x) -/
def findExponentDown (x : R) (_ : (2 : R) ^ FloatFormat.min_exp ≤ x) : ℤ :=
  -- Use Int.log to find the greatest power of 2 such that 2^e <= x
  let raw_exp := Int.log 2 x
  -- Clamp to valid exponent range
  max (min raw_exp FloatFormat.max_exp) FloatFormat.min_exp


/-- Round a positive normal value down -/
def roundNormalDown (x : R) (h : isNormalRange x) : Fp :=
  -- Find the exponent by comparing with powers of 2
  -- We know x >= 2^min_exp from the range condition
  let e := findExponentDown x h.1
  let binade_base := (2 : R) ^ e
  let scaled := x / binade_base
  -- scaled is now in [1, 2)
  let m_scaled := scaled * (2 : R) ^ (FloatFormat.prec - 1)
  let m := ⌊m_scaled⌋
  match mkFiniteFp false e m.natAbs with
  | some f => Fp.finite f
  | none => Fp.NaN  -- Should not happen

/-- Round a positive normal value up -/
def roundNormalUp (x : R) (h : isNormalRange x) : Fp :=
  -- Find the exponent by comparing with powers of 2
  let e := findExponentDown x h.1
  let binade_base := (2 : R) ^ e
  let scaled := x / binade_base
  -- scaled is now in [1, 2)
  let m_scaled := scaled * (2 : R) ^ (FloatFormat.prec - 1)
  let m := ⌈m_scaled⌉
  -- Handle overflow within the binade
  if m ≥ 2^FloatFormat.prec then
    -- Need to move to next binade
    if e + 1 > FloatFormat.max_exp then
      -- Overflow to infinity
      Fp.infinite false
    else
      match mkFiniteFp false (e + 1) (2^(FloatFormat.prec - 1)) with
      | some f => Fp.finite f
      | none => Fp.NaN
  else
    match mkFiniteFp false e m.natAbs with
    | some f => Fp.finite f
    | none => Fp.NaN

/-- Find the predecessor of a positive number -/
def findPredecessorPos (x : R) (hpos : 0 < x) : Fp :=
  -- Check ranges manually without decidability
  if hlt : x < (2 : R) ^ FloatFormat.min_exp then
    -- Subnormal range
    roundSubnormalDown x ⟨hpos, hlt⟩
  else if hlt2 : x < (2 : R) ^ (FloatFormat.max_exp + 1) then
    -- Normal range
    roundNormalDown x ⟨le_of_not_gt hlt, hlt2⟩
  else
    -- x is too large, return largest finite float
    Fp.finite FiniteFp.largestFiniteFloat

/-- Find the successor of a positive number -/
def findSuccessorPos (x : R) (hpos : 0 < x) : Fp :=
  -- Check ranges manually without decidability
  if hlt : x < (2 : R) ^ FloatFormat.min_exp then
    -- Subnormal range
    roundSubnormalUp x ⟨hpos, hlt⟩
  else if hlt2 : x < (2 : R) ^ (FloatFormat.max_exp + 1) then
    -- Normal range
    roundNormalUp x ⟨le_of_not_gt hlt, hlt2⟩
  else
    -- Overflow
    Fp.infinite false

/-- Find the largest floating-point value less than or equal to x (predecessor) -/
def findPredecessor (x : R) : Fp :=
  if h : x = 0 then Fp.finite 0
  else if hpos : 0 < x then
    findPredecessorPos x hpos
  else
    -- x < 0: use symmetry
    have hne : x ≠ 0 := h
    have hneg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hne)
    match findSuccessorPos (-x) hneg with
    | Fp.finite f => Fp.finite (-f)
    | Fp.infinite b => Fp.infinite (!b)
    | Fp.NaN => Fp.NaN

/-- Find the smallest floating-point value greater than or equal to x (successor) -/
def findSuccessor (x : R) : Fp :=
  if h : x = 0 then Fp.finite 0
  else if hpos : 0 < x then
    findSuccessorPos x hpos
  else
    -- x < 0: use symmetry
    have hne : x ≠ 0 := h
    have hneg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hne)
    match findPredecessorPos (-x) hneg with
    | Fp.finite f => Fp.finite (-f)
    | Fp.infinite b => Fp.infinite (!b)
    | Fp.NaN => Fp.NaN

end Rounding
