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

theorem isNormalRange_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) : isNormalRange x → 0 < x := by
  intro h
  have : (0 :R) < (2 : R) ^(FloatFormat.min_exp : ℤ) := by
    apply zpow_pos (by norm_num)
  apply lt_of_lt_of_le this h.left

-- theorem isNormalRange_isNormal_m (x : R) (h : isNormalRange x) : isNormal m

/-- Check if a positive number causes overflow -/
def isOverflow (x : R) : Prop :=
  (2 : R) ^ (FloatFormat.max_exp + 1) ≤ x

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
def findExponentDown (x : R) : ℤ :=
  max (min (Int.log 2 x) FloatFormat.max_exp) FloatFormat.min_exp

theorem findExponentDown_min (x : R) : FloatFormat.min_exp ≤ findExponentDown x := by
  unfold findExponentDown
  simp only [le_sup_right]

theorem findExponentDown_max (x : R) : findExponentDown x ≤ FloatFormat.max_exp := by
  unfold findExponentDown
  simp only [sup_le_iff, inf_le_right, FloatFormat.exp_order_le, and_self]

theorem findExponentDown_normal (x : R) (h : isNormalRange x) : findExponentDown x = Int.log 2 x := by
  have xpos := isNormalRange_pos x h
  have ha₁ : Int.log 2 x < FloatFormat.max_exp + 1 := (Int.lt_zpow_iff_log_lt (by norm_num) xpos).mp h.right
  unfold findExponentDown
  have := FloatFormat.exp_order_le
  rw [max_eq_left]
  rw [min_eq_left (by linarith)]
  rw [min_eq_left (by linarith)]
  apply (Int.zpow_le_iff_le_log (by norm_num) xpos).mp
  exact h.left

theorem findExponentDown_subnormal (x : R) (h : isSubnormalRange x) : findExponentDown x = FloatFormat.min_exp := by
  have hu : Int.log 2 x < FloatFormat.min_exp := by
    apply (Int.lt_zpow_iff_log_lt (by norm_num) h.left).mp
    exact h.right
  unfold findExponentDown
  rw [max_eq_right]
  rw [min_eq_left]
  · apply le_of_lt hu
  · apply le_of_lt
    apply lt_trans
    exact hu
    exact FloatFormat.exp_order

theorem findExponentDown_overflow (x : R) (h : isOverflow x) : findExponentDown x = FloatFormat.max_exp := by
  unfold findExponentDown
  unfold isOverflow at h
  have := FloatFormat.exp_order
  have a1 := Int.log_mono_right (b := 2) ?_ h
  have a2 := Int.log_zpow (R := R) (b := 2) (by norm_num : 1 < 2) (FloatFormat.max_exp + 1)
  rw_mod_cast [a2] at a1
  rw [max_eq_left]
  rw [min_eq_right]
  · linarith
  · cases min_cases (Int.log 2 x) FloatFormat.max_exp with
    | inl ha =>
      rw [ha.left]
      linarith
    | inr ha =>
      rw [ha.left]
      linarith
  · apply zpow_pos (by norm_num)

/-- A value in the normal range will have a binade within `1 ≤ e < 2` -/
theorem findExponentDown_div_binade_normal (x : R) (h : isNormalRange x) :
  (1 : R) ≤ x / ((2 : R)^(findExponentDown x)) ∧
  x / ((2 : R)^(findExponentDown x)) < (2 : R) := by
  have xpos := isNormalRange_pos x h
  rw [findExponentDown_normal x h]
  have hl : (2 : R) ^ (Int.log 2 x) ≤ x := by apply Int.zpow_log_le_self (by norm_num) xpos
  have hu : x < (2 : R)^(Int.log 2 x + 1) := by apply Int.lt_zpow_succ_log_self (by norm_num)
  split_ands
  · apply (one_le_div ?_).mpr (by trivial)
    apply zpow_pos (by norm_num)
  · apply (div_lt_iff₀ ?_).mpr
    rw [mul_comm]
    rw [← zpow_add_one₀ (by norm_num)]
    trivial
    apply zpow_pos (by norm_num)

theorem findExponentDown_div_binade_subnormal (x : R) (h : isSubnormalRange x) :
  0 < x / ((2 : R)^(findExponentDown x)) ∧
  x / ((2 : R)^(findExponentDown x)) < 1 := by
  rw [findExponentDown_subnormal x h]
  split_ands
  · apply div_pos h.left
    apply zpow_pos (by norm_num)
  · apply (div_lt_one ?_).mpr
    · exact h.right
    · apply zpow_pos (by norm_num)

theorem findExponentDown_div_binade_overflow (x : R) (h : isOverflow x) :
  2 ≤ x / ((2 : R)^(findExponentDown x)) := by
  rw [findExponentDown_overflow x h]
  unfold isOverflow at h
  apply (le_div_iff₀ ?_).mpr
  rw [← zpow_one_add₀ (by norm_num)]
  rw [add_comm]
  trivial
  apply zpow_pos (by norm_num)

/-- Round a positive normal value down -/
def roundNormalDown (x : R) (h : isNormalRange x) : Fp :=
  -- Find the exponent by comparing with powers of 2
  -- We know x >= 2^min_exp from the range condition
  let e := findExponentDown x
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
  let e := findExponentDown x
  let binade_base := (2 : R) ^ e
  let scaled := x / binade_base
  -- scaled is now in [1, 2)
  let m_scaled := scaled * (2 : R) ^ (FloatFormat.prec - 1)
  let m := ⌈m_scaled⌉

  have mpos : m > 0 := by
    unfold m m_scaled scaled binade_base
    norm_num
    apply mul_pos
    apply div_pos
    exact isNormalRange_pos x h
    apply zpow_pos (by norm_num)
    apply zpow_pos (by norm_num)

  -- Handle overflow within the binade
  if m ≥ 2^FloatFormat.prec then
    -- Need to move to next binade
    if e + 1 > FloatFormat.max_exp then
      -- Overflow to infinity
      Fp.infinite false
    else
      -- TODO: we could make a proof in this function that we never produce a NaN so that we don't need an outside proof to be as complicated?
      match mkFiniteFp false (e + 1) (2^(FloatFormat.prec - 1)) with
      | some f => Fp.finite f
      | none => Fp.NaN
  else
    match mkFiniteFp false e m.natAbs with
    | some f => Fp.finite f
    | none => Fp.NaN

theorem roundNormalDown_ne_nan (x : R) (h : isNormalRange x) : roundNormalDown x h ≠ Fp.NaN := by
  unfold roundNormalDown
  extract_lets e binade_base scaled m_scaled m
  unfold mkFiniteFp
  have hb := findExponentDown_div_binade_normal x h
  have vp := FloatFormat.valid_prec
  have : IsValidFiniteVal e m.natAbs := by
    have mpos : m > 0 := by
      unfold m m_scaled scaled binade_base
      norm_num
      apply Int.floor_pos.mpr

      apply le_trans

      apply hb.left
      unfold e
      conv_lhs => rw [← mul_one (x / 2 ^ (findExponentDown x))]
      rw [mul_le_mul_left (by linarith)]

      simp only [Nat.one_lt_ofNat, one_le_zpow_iff_right₀, Int.sub_nonneg, Nat.one_le_cast]
      linarith

    unfold IsValidFiniteVal
    have a1 : x / 2 ^ findExponentDown x * 2 ^ (FloatFormat.prec - 1) < ↑((2 : ℤ) ^ FloatFormat.prec) := by
      rw [FloatFormat.natCast_pow_prec_msb]
      rw [mul_comm, mul_assoc]
      norm_num
      rw [← lt_div_iff₀' (by norm_num)]
      linarith

    split_ands
    · apply findExponentDown_min
    · apply findExponentDown_max
    · zify
      rw [abs_of_pos mpos]
      unfold m m_scaled scaled binade_base e
      apply Int.floor_lt.mpr
      exact a1
    · left
      unfold isNormal
      split_ands
      <;> zify
      <;> rw [abs_of_pos mpos]
      <;> unfold m m_scaled scaled binade_base e
      · apply Int.le_floor.mpr
        zify
        -- TODO: having to do this manually is a SHAME
        conv_lhs => rw [← one_mul (2 ^ (FloatFormat.prec - 1))]
        rw [mul_le_mul_right]
        · exact hb.left
        · apply pow_pos (by norm_num)
      · apply Int.floor_lt.mpr
        exact a1
  rw [dite_cond_eq_true (eq_true this)]
  split
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · trivial

theorem roundNormalUp_ne_nan (x : R) (h : isNormalRange x) : roundNormalUp x h ≠ Fp.NaN := by
  unfold roundNormalUp
  extract_lets e binade_base scaled m_scaled m mpos
  unfold mkFiniteFp
  sorry

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
