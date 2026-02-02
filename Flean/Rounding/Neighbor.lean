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

/-- findPredecessorPos always returns a non-negative float (sign = false) -/
theorem findPredecessorPos_sign_false (x : R) (hpos : 0 < x) :
    (findPredecessorPos x hpos).s = false := by
  unfold findPredecessorPos
  split_ifs with h1 h2
  · -- Subnormal case: roundSubnormalDown
    simp only [roundSubnormalDown]
    split_ifs <;> rfl
  · -- Normal case: roundNormalDown
    simp only [roundNormalDown]
  · -- Overflow case: largestFiniteFloat
    simp only [FiniteFp.largestFiniteFloat]

/-- The toVal of findPredecessorPos is monotone: if x ≤ y then the results are ordered.
    This is the key lemma - it says the floor operation on floats is monotone. -/
theorem findPredecessorPos_toVal_mono {x y : R} (hx : 0 < x) (hy : 0 < y) (h : x ≤ y) :
    (findPredecessorPos x hx).toVal (R := R) ≤ (findPredecessorPos y hy).toVal (R := R) := by
  unfold findPredecessorPos
  -- Split on ranges for x and y
  by_cases hx_sub : x < (2 : R) ^ FloatFormat.min_exp
  · -- x is in subnormal range
    simp only [hx_sub, ↓reduceDIte]
    by_cases hy_sub : y < (2 : R) ^ FloatFormat.min_exp
    · -- y also in subnormal range
      simp only [hy_sub, ↓reduceDIte]
      apply roundSubnormalDown_toVal_mono ⟨hx, hx_sub⟩ ⟨hy, hy_sub⟩ h
    · -- y in normal or overflow range
      simp only [hy_sub, ↓reduceDIte]
      by_cases hy_nor : y < (2 : R) ^ (FloatFormat.max_exp + 1)
      · -- y in normal range: roundSubnormalDown x ≤ roundNormalDown y
        simp only [hy_nor, ↓reduceDIte]
        -- roundSubnormalDown x ≤ x < 2^min_exp ≤ roundNormalDown y
        have hstep : (roundSubnormalDown x ⟨hx, hx_sub⟩).toVal (R := R) < (2 : R) ^ FloatFormat.min_exp := by
          calc (roundSubnormalDown x ⟨hx, hx_sub⟩).toVal (R := R)
              ≤ x := roundSubnormalDown_le x ⟨hx, hx_sub⟩
            _ < (2 : R) ^ FloatFormat.min_exp := hx_sub
        apply le_of_lt
        calc (roundSubnormalDown x ⟨hx, hx_sub⟩).toVal (R := R)
            < (2 : R) ^ FloatFormat.min_exp := hstep
          _ ≤ (roundNormalDown y ⟨not_lt.mp hy_sub, hy_nor⟩).toVal := roundNormalDown_ge_zpow_min_exp y ⟨not_lt.mp hy_sub, hy_nor⟩
      · -- y in overflow range
        simp only [hy_nor, ↓reduceDIte]
        -- roundSubnormalDown x is a finite float, so it's ≤ largestFiniteFloat
        exact FiniteFp.finite_le_largestFiniteFloat _
  · -- x is in normal or overflow range
    simp only [hx_sub, ↓reduceDIte]
    by_cases hx_nor : x < (2 : R) ^ (FloatFormat.max_exp + 1)
    · -- x in normal range
      simp only [hx_nor, ↓reduceDIte]
      -- y must also be in normal or overflow range (since x ≤ y and x ≥ 2^min_exp)
      have hy_not_sub : ¬(y < (2 : R) ^ FloatFormat.min_exp) := by
        intro hy_sub
        have : y < x := lt_of_lt_of_le hy_sub (not_lt.mp hx_sub)
        linarith
      simp only [hy_not_sub, ↓reduceDIte]
      by_cases hy_nor : y < (2 : R) ^ (FloatFormat.max_exp + 1)
      · -- Both in normal range
        simp only [hy_nor, ↓reduceDIte]
        exact roundNormalDown_toVal_mono ⟨not_lt.mp hx_sub, hx_nor⟩ ⟨not_lt.mp hy_not_sub, hy_nor⟩ h
      · -- y in overflow range
        simp only [hy_nor, ↓reduceDIte]
        -- roundNormalDown x is a finite float, so it's ≤ largestFiniteFloat
        exact FiniteFp.finite_le_largestFiniteFloat _
    · -- x in overflow range
      -- y must also be in overflow range
      have hy_not_sub : ¬(y < (2 : R) ^ FloatFormat.min_exp) := by
        intro hy_sub
        have hx_sub' : x < (2 : R) ^ FloatFormat.min_exp := by
          apply lt_of_le_of_lt h hy_sub
        exact hx_sub hx_sub'
      have hy_not_nor : ¬(y < (2 : R) ^ (FloatFormat.max_exp + 1)) := by
        intro hy_nor
        have hx_nor' : x < (2 : R) ^ (FloatFormat.max_exp + 1) := by
          apply lt_of_le_of_lt h hy_nor
        exact hx_nor hx_nor'
      simp only [hx_nor, hy_not_sub, hy_not_nor, ↓reduceDIte]
      -- Both return largestFiniteFloat, goal is ≤ by reflexivity
      exact le_refl _

/-- findPredecessorPos is monotone in the FiniteFp ordering -/
theorem findPredecessorPos_mono {x y : R} (hx : 0 < x) (hy : 0 < y) (h : x ≤ y) :
    findPredecessorPos x hx ≤ findPredecessorPos y hy := by
  -- Use toVal_le_handle: for non-negative floats, ordering matches toVal ordering
  apply FiniteFp.toVal_le_handle R
  · exact findPredecessorPos_toVal_mono hx hy h
  · intro hz
    -- Both have sign = false (non-negative), so if both are zero, they're both = 0
    have hsx := findPredecessorPos_sign_false x hx
    have hsy := findPredecessorPos_sign_false y hy
    rw [FiniteFp.isZero_iff, FiniteFp.isZero_iff] at hz
    rcases hz with ⟨h1 | h2, h3 | h4⟩
    · rw [h1, h3]
    · -- h4 says findPredecessorPos y hy = -0, but sign is false, contradiction
      exfalso
      have hsign : (findPredecessorPos y hy).s = (-0 : FiniteFp).s := by rw [h4]
      rw [hsy, FiniteFp.neg_def, FiniteFp.zero_def] at hsign
      simp at hsign
    · -- h2 says findPredecessorPos x hx = -0, but sign is false, contradiction
      exfalso
      have hsign : (findPredecessorPos x hx).s = (-0 : FiniteFp).s := by rw [h2]
      rw [hsx, FiniteFp.neg_def, FiniteFp.zero_def] at hsign
      simp at hsign
    · -- Both are -0, same contradiction
      exfalso
      have hsign : (findPredecessorPos x hx).s = (-0 : FiniteFp).s := by rw [h2]
      rw [hsx, FiniteFp.neg_def, FiniteFp.zero_def] at hsign
      simp at hsign

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

/-- findSuccessor is monotone on negative values.
    For x ≤ y < 0, findSuccessor x ≤ findSuccessor y.
    This follows from findPredecessorPos_mono by symmetry. -/
theorem findSuccessor_mono_neg {x y : R} (hx : x < 0) (hy : y < 0) (h : x ≤ y) :
    findSuccessor x ≤ findSuccessor y := by
  -- Use the formula: findSuccessor x = -findPredecessorPos (-x)
  rw [findSuccessor_neg_eq x hx, findSuccessor_neg_eq y hy]
  -- Now show Fp.finite (-f_x) ≤ Fp.finite (-f_y)
  -- where f_x = findPredecessorPos (-x) and f_y = findPredecessorPos (-y)
  -- From x ≤ y < 0, we get 0 < -y ≤ -x
  have hny : 0 < -y := neg_pos.mpr hy
  have hnx : 0 < -x := neg_pos.mpr hx
  have hyx : -y ≤ -x := neg_le_neg h
  -- By findPredecessorPos_toVal_mono: f_y.toVal ≤ f_x.toVal
  have hmono := findPredecessorPos_toVal_mono hny hnx hyx
  -- Use FiniteFp.toVal_le_handle to convert from toVal ordering
  have htoVal : (-findPredecessorPos (-x) hnx).toVal (R := R) ≤ (-findPredecessorPos (-y) hny).toVal (R := R) := by
    rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
    linarith
  -- Get -f_x ≤ -f_y in FiniteFp ordering
  have hle : -findPredecessorPos (-x) hnx ≤ -findPredecessorPos (-y) hny := by
    apply FiniteFp.toVal_le_handle R htoVal
    intro hz
    -- Both are zero case: -f_x and -f_y both zero means f_x and f_y both zero
    -- f_x has sign false, so isZero means f_x = 0 (not -0)
    -- -f_x = -0 has sign true
    -- So if -f_x.isZero and -f_y.isZero, they're both -0 or 0
    have hsx := findPredecessorPos_sign_false (-x) hnx
    have hsy := findPredecessorPos_sign_false (-y) hny
    rw [FiniteFp.isZero_iff, FiniteFp.isZero_iff] at hz
    rcases hz with ⟨h1 | h2, h3 | h4⟩
    · -- Both are 0: -f_x = 0 and -f_y = 0 means f_x = 0 and f_y = 0
      -- But -0 = ⟨true, 0, 0⟩ ≠ ⟨false, 0, 0⟩ = 0
      exfalso
      rw [FiniteFp.neg_def, FiniteFp.eq_def] at h1
      simp only [FiniteFp.zero_def, Bool.not_false] at h1
      have := h1.left
      rw [hsx] at this
      simp at this
    · -- -f_x = 0, -f_y = -0: contradiction since -f_x has sign = !f_x.s = !false = true ≠ false
      exfalso
      rw [FiniteFp.neg_def, FiniteFp.eq_def] at h1
      simp only [FiniteFp.zero_def, Bool.not_false] at h1
      rw [hsx] at h1
      simp at h1
    · -- -f_x = -0, -f_y = 0: same contradiction for -f_y
      exfalso
      rw [FiniteFp.neg_def, FiniteFp.eq_def] at h3
      simp only [FiniteFp.zero_def, Bool.not_false] at h3
      rw [hsy] at h3
      simp at h3
    · -- Both are -0: -f_x = -0 and -f_y = -0, so they're equal
      rw [h2, h4]
  -- Convert FiniteFp.le to Fp.le
  rw [Fp.le_def]
  rw [FiniteFp.le_def] at hle
  cases hle with
  | inl hlt => left; exact hlt
  | inr heq => right; rw [heq]

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
