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
import Flean.Gsplit.Gsplit
import Flean.Util
import Flean.Rounding.Defs
import Flean.Rounding.RoundSubnormal
import Flean.Rounding.RoundNormal

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

section findPredecessorPos

/-- Find the predecessor of a positive number -/
def findPredecessorPos (x : R) (hpos : 0 < x) : FiniteFp :=
  -- Check ranges manually without decidability
  if hlt : x < (2 : R) ^ FloatFormat.min_exp then
    -- Subnormal range
    roundSubnormalDown x ⟨hpos, hlt⟩
  else if hlt2 : x < (2 : R) ^ (FloatFormat.max_exp + 1) then
    -- Normal range
    roundNormalDown x ⟨le_of_not_gt hlt, hlt2⟩
  else
    -- x is too large, return largest finite float
    FiniteFp.largestFiniteFloat


theorem findPredecessorPos_pos {x : R} {hpos : 0 < x} (hx : FiniteFp.smallestPosSubnormal.toVal ≤ x) : (0 : R) < (findPredecessorPos x hpos).toVal := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · apply roundSubnormalDown_pos hx
  · apply roundNormalDown_pos
  · apply FiniteFp.largestFiniteFloat_toVal_pos

/-- If the output is positive, then the input is at least the smallest positive subnormal (and thus wasn't rounded down to zero) -/
theorem findPredecessorPos_pos_iff {x : R} {hpos : 0 < x} : FiniteFp.smallestPosSubnormal.toVal ≤ x ↔ (0 : R) < (findPredecessorPos x hpos).toVal := by
  constructor
  · exact findPredecessorPos_pos
  · intro hf
    unfold findPredecessorPos at hf
    split_ifs at hf with h1 h2
    · apply roundSubnormalDown_pos_iff.mpr hf
    · norm_num at h1
      rw [FiniteFp.smallestPosSubnormal_toVal]
      apply le_trans' h1
      gcongr; norm_num
      fomega
    · norm_num at h1 h2
      rw [FiniteFp.smallestPosSubnormal_toVal]
      apply le_trans' h1
      gcongr; norm_num
      fomega

theorem findPredecessorPos_nonneg {x : R} {hpos : 0 < x} : (0 : R) ≤ (findPredecessorPos x hpos).toVal := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · apply roundSubnormalDown_nonneg
  · apply roundNormalDown_nonneg
  · apply le_of_lt FiniteFp.largestFiniteFloat_toVal_pos

-- findPredecessorPos preserves the floor property
lemma findPredecessorPos_le (x : R) (hpos : 0 < x) : (findPredecessorPos x hpos).toVal ≤ x := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · apply roundSubnormalDown_le
  · apply roundNormalDown_le
  · linarith [FiniteFp.largestFiniteFloat_lt_maxExp_succ (R := R)]

end findPredecessorPos





section findSuccessorPos

/-- Find the successor of a positive number -/
def findSuccessorPos (x : R) (hpos : 0 < x) : Fp :=
  -- Check ranges manually without decidability
  if hlt : x < (2 : R) ^ FloatFormat.min_exp then
    -- Subnormal range
    Fp.finite (roundSubnormalUp x ⟨hpos, hlt⟩)
  else if hlt2 : x < (2 : R) ^ (FloatFormat.max_exp + 1) then
    -- Normal range
    roundNormalUp x ⟨le_of_not_gt hlt, hlt2⟩
  else
    -- Overflow
    Fp.infinite false

@[simp]
theorem findSuccessorPos_ne_nan (x : R) (hpos : 0 < x) : findSuccessorPos x hpos ≠ Fp.NaN := by
  unfold findSuccessorPos
  split_ifs
  <;> simp

@[simp]
theorem findSuccessorPos_ne_neg_inf (x : R) (hpos : 0 < x) : findSuccessorPos x hpos ≠ Fp.infinite true := by
  unfold findSuccessorPos
  split_ifs
  <;> simp

-- findSuccessorPos preserves the ceiling property
lemma findSuccessorPos_ge (x : R) (hpos : 0 < x) (f : FiniteFp)
  (h : findSuccessorPos x hpos = Fp.finite f) : x ≤ f.toVal := by
  unfold findSuccessorPos at h
  split_ifs at h with h_sub h_normal
  · -- Subnormal case
    rw [Fp.finite.injEq] at h
    exact roundSubnormalUp_ge x ⟨hpos, h_sub⟩ f h
  · -- Normal case
    exact roundNormalUp_ge x ⟨le_of_not_gt h_sub, h_normal⟩ f h
  -- Overflow case handled automatically

theorem findSuccessorPos_pos {x : R} {hpos : 0 < x} {f : FiniteFp} (hf : findSuccessorPos x hpos = Fp.finite f): (0 : R) < f.toVal := by
  unfold findSuccessorPos at hf
  split_ifs at hf with h1 h2
  · rw [Fp.finite.injEq] at hf
    rw [← hf]
    apply roundSubnormalUp_pos
  · exact roundNormalUp_pos hf

end findSuccessorPos




section findPredecessor

/-- Find the largest floating-point value less than or equal to x (predecessor) -/
def findPredecessor (x : R) : Fp :=
  if h : x = 0 then Fp.finite 0
  else if hpos : 0 < x then
    Fp.finite (findPredecessorPos x hpos)
  else
    -(findSuccessorPos (-x) (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) h)))

@[simp]
theorem findPredecessor_zero : findPredecessor (0 : R) = Fp.finite 0 := by simp [findPredecessor]

@[simp]
theorem findPredecessor_pos_eq (x : R) (hpos : 0 < x) : findPredecessor x = Fp.finite (findPredecessorPos x hpos) := by
  unfold findPredecessor findPredecessorPos
  simp_all only [↓reduceDIte, dite_eq_ite, ite_eq_right_iff]
  intro hx
  linarith

@[simp]
theorem findPredecessor_neg_eq (x : R) (hneg : x < 0) :
  findPredecessor x = -(findSuccessorPos (-x) (neg_pos.mpr hneg)) := by
  have hnz : x ≠ 0 := by linarith
  have hnpos : ¬0 < x := by linarith
  simp [findPredecessor, hneg, hnz, hnpos]

end findPredecessor




section findSuccessor

/-- Find the smallest floating-point value greater than or equal to x (successor) -/
def findSuccessor (x : R) : Fp :=
  if h : x = 0 then Fp.finite 0
  else if hpos : 0 < x then
    findSuccessorPos x hpos
  else
    -- x < 0: use symmetry
    have hne : x ≠ 0 := h
    have hneg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hne)
    let v := findPredecessorPos (-x) hneg
    Fp.finite (-v)

theorem findSuccessor_symm (x : R) (h : x < 0) : findSuccessor x = -findPredecessor (-x) := by
  unfold findSuccessor findPredecessor
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · extract_lets hne hneg v
    unfold v
    rw [Fp.neg_finite]
  · linarith

@[simp]
theorem findSuccessor_zero : findSuccessor (0 : R) = Fp.finite 0 := by simp [findSuccessor]

@[simp]
theorem findSuccessor_pos_eq (x : R) (hpos : 0 < x) : findSuccessor x = findSuccessorPos x hpos := by
  unfold findSuccessor findSuccessorPos
  simp_all only [↓reduceDIte, dite_eq_ite, ite_eq_right_iff]
  intro a
  subst a
  split
  next h =>
    simp_all only [Fp.finite.injEq]
    linarith
  next h => simp_all only [lt_self_iff_false]

@[simp]
theorem findSuccessor_neg_eq (x : R) (hneg : x < 0) :
  findSuccessor x = Fp.finite (-findPredecessorPos (-x) (neg_pos.mpr hneg)) := by
  have hnz : x ≠ 0 := by linarith
  have hnpos : ¬0 < x := by linarith
  simp [findSuccessor, hneg, hnz, hnpos]

end findSuccessor


section Misc

/-- Check if a value is exactly at the midpoint between two consecutive floating-point values -/
def isMidpoint [FloatFormat] (x : R) : Prop :=
  let pred := findPredecessor x
  let succ := findSuccessor x
  match pred, succ with
  | Fp.finite p, Fp.finite s => x = (p.toVal + s.toVal) / 2
  | _, _ => False

end Misc


end Rounding
