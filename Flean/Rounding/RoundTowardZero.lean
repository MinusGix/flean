import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Polyrith

import Flean.Util
import Flean.Basic
import Flean.Ulp
import Flean.Ufp
import Flean.Linearize.Linearize
import Flean.Rounding.Neighbor
import Flean.Rounding.RoundDown
import Flean.Rounding.RoundUp

section Rounding
section RoundTowardZero

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]


/-- Round toward zero -/
def roundTowardZero [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if x > 0 then
    -- For positive x, round down (toward zero)
    roundDown x
  else
    -- For negative x, round up (toward zero)
    roundUp x

/-- roundTowardZero returns 0 when input is 0 -/
theorem roundTowardZero_zero [FloatFormat] : roundTowardZero (0 : R) = Fp.finite 0 := by
  unfold roundTowardZero
  simp

theorem roundTowardZero_pos_eq [FloatFormat] (x : R) (hpos : 0 < x) : roundTowardZero x = roundDown x := by
  simp [roundTowardZero, hpos]
  intro hz
  linarith

theorem roundTowardZero_neg_eq [FloatFormat] (x : R) (hneg : x < 0) : roundTowardZero x = roundUp x := by
  have xnz : x ≠ 0 := by linarith
  have xngt : ¬0 < x := by linarith
  simp only [roundTowardZero, xnz, ↓reduceIte, gt_iff_lt, xngt]

-- Helper: roundTowardZero always returns a finite value
theorem roundTowardZero_isFinite [FloatFormat] (x : R) : ∃ f : FiniteFp, roundTowardZero x = Fp.finite f := by
  unfold roundTowardZero
  split_ifs with h1 h2
  · exact ⟨0, rfl⟩
  · -- x > 0: roundDown x = findPredecessor x
    unfold roundDown findPredecessor
    simp only [h1, ↓reduceDIte, h2]
    exact ⟨findPredecessorPos x h2, rfl⟩
  · -- x < 0: roundUp x = findSuccessor x
    have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt h2) h1
    unfold roundUp findSuccessor
    simp only [h1, ↓reduceDIte, h2, not_lt.mpr (le_of_lt hneg)]
    exact ⟨-findPredecessorPos (-x) (neg_pos.mpr hneg), rfl⟩

-- Helper: for positive x, roundTowardZero result has toVal in [0, x]
theorem roundTowardZero_pos_bounds [FloatFormat] (x : R) (hpos : 0 < x) (f : FiniteFp)
  (hf : roundTowardZero x = Fp.finite f) : (0 : R) ≤ f.toVal ∧ f.toVal ≤ x := by
  rw [roundTowardZero_pos_eq x hpos] at hf
  unfold roundDown findPredecessor at hf
  simp only [ne_of_gt hpos, ↓reduceDIte, hpos, Fp.finite.injEq] at hf
  rw [← hf]
  exact ⟨findPredecessorPos_nonneg, findPredecessorPos_le x hpos⟩

-- Helper: for negative x, roundTowardZero result has toVal in [x, 0]
theorem roundTowardZero_neg_bounds [FloatFormat] (x : R) (hneg : x < 0) (f : FiniteFp)
  (hf : roundTowardZero x = Fp.finite f) : x ≤ f.toVal ∧ f.toVal ≤ (0 : R) := by
  rw [roundTowardZero_neg_eq x hneg] at hf
  unfold roundUp findSuccessor at hf
  have hne : x ≠ 0 := ne_of_lt hneg
  have hnpos : ¬0 < x := not_lt.mpr (le_of_lt hneg)
  simp only [hne, ↓reduceDIte, hnpos, Fp.finite.injEq] at hf
  rw [← hf, FiniteFp.toVal_neg_eq_neg]
  constructor
  · have := findPredecessorPos_le (-x) (neg_pos.mpr hneg)
    linarith
  · have := findPredecessorPos_nonneg (x := -x) (hpos := neg_pos.mpr hneg)
    linarith

/-- For negative x, roundTowardZero x ≤ 0 in the Fp ordering -/
theorem roundTowardZero_neg_le_zero [FloatFormat] (x : R) (hneg : x < 0) :
    roundTowardZero x ≤ Fp.finite 0 := by
  rw [roundTowardZero_neg_eq x hneg]
  unfold roundUp
  rw [findSuccessor_neg_eq x hneg]
  -- Goal: Fp.finite (-findPredecessorPos (-x)) ≤ Fp.finite 0
  -- f = findPredecessorPos (-x) has sign = false (non-negative)
  -- -f has sign = true, so -f < 0
  have hf := findPredecessorPos_sign_false (-x) (neg_pos.mpr hneg)
  have hnf_sign : (-findPredecessorPos (-x) (neg_pos.mpr hneg)).s = true := by
    rw [FiniteFp.neg_def]; simp only [hf, Bool.not_false]
  -- Use Fp.lt_imp_le: show -f < 0 first
  apply Fp.lt_imp_le
  rw [Fp.lt_def]
  simp only
  rw [FiniteFp.lt_def]
  left
  -- Need to show (-f).s ∧ !(0 : FiniteFp).s
  simp only [FiniteFp.zero_def, Bool.not_false, and_true]
  exact hnf_sign

/-- For positive y, 0 ≤ roundTowardZero y in the Fp ordering -/
theorem roundTowardZero_zero_le_pos [FloatFormat] (y : R) (hpos : 0 < y) :
    Fp.finite 0 ≤ roundTowardZero y := by
  rw [roundTowardZero_pos_eq y hpos]
  unfold roundDown findPredecessor
  simp only [ne_of_gt hpos, ↓reduceDIte, hpos]
  -- f = findPredecessorPos y hpos has sign = false
  have hf := findPredecessorPos_sign_false y hpos
  by_cases hz : findPredecessorPos y hpos = 0
  · -- f = 0, so 0 ≤ 0
    rw [Fp.le_def]
    right; simp only [hz]
  · -- f ≠ 0, so 0 < f
    apply Fp.lt_imp_le
    rw [Fp.lt_def]
    simp only
    rw [FiniteFp.lt_def]
    right; left
    -- Need !(0).s ∧ !f.s ∧ 0.is_mag_lt f
    simp only [FiniteFp.zero_def, Bool.not_false, hf, true_and]
    -- 0 is_mag_lt f because f.m > 0
    unfold FiniteFp.is_mag_lt
    have hfm : (findPredecessorPos y hpos).m ≠ 0 := by
      intro hm0
      apply hz
      -- From validity and m = 0, we get e = min_exp
      have vf := (findPredecessorPos y hpos).valid
      unfold IsValidFiniteVal at vf
      rw [hm0] at vf
      -- vf says isNormal 0 ∨ isSubnormal e 0, but isNormal 0 is false
      have hn : ¬isNormal 0 := by simp [isNormal]
      have hsub : isSubnormal (findPredecessorPos y hpos).e 0 := by
        cases' vf.right.right.right with h h
        · exact (hn h).elim
        · exact h
      have he : (findPredecessorPos y hpos).e = FloatFormat.min_exp := isSubnormal.zero_iff.mp hsub
      rw [FiniteFp.eq_def]
      exact ⟨hf, he, hm0⟩
    -- Now prove 0.is_mag_lt f using hfm
    have hfm_pos : 0 < (findPredecessorPos y hpos).m := Nat.pos_of_ne_zero hfm
    split_ifs with he hgt
    · -- 0.e = f.e: need 0 < f.m
      exact hfm_pos
    · -- 0.e > f.e: impossible since 0.e = min_exp is minimum
      exfalso
      have he_ge := (findPredecessorPos y hpos).valid_min_exp
      simp only [FiniteFp.zero_def] at hgt
      omega
    · -- 0.e < f.e: need 0 < f.m * 2^(...)
      apply Nat.mul_pos hfm_pos
      apply Nat.pow_pos
      norm_num

/-- Monotonicity of roundTowardZero: if x ≤ y then roundTowardZero x ≤ roundTowardZero y.
    Uses:
    - findPredecessorPos_mono for both positive case
    - findSuccessor_mono_neg for both negative case
    - roundTowardZero_neg_le_zero and roundTowardZero_zero_le_pos for crossing zero -/
theorem roundTowardZero_mono [FloatFormat] {x y : R} (h : x ≤ y) : roundTowardZero x ≤ roundTowardZero y := by
  -- Case split on signs of x and y
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0
    rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · -- Both negative: use findSuccessor_mono_neg
      rw [roundTowardZero_neg_eq x hx_neg, roundTowardZero_neg_eq y hy_neg]
      exact findSuccessor_mono_neg hx_neg hy_neg h
    · -- x < 0, y = 0
      rw [hy_zero, roundTowardZero_zero]
      exact roundTowardZero_neg_le_zero x hx_neg
    · -- x < 0 < y: roundTowardZero x ≤ 0 ≤ roundTowardZero y
      -- Extract finite values from roundTowardZero results
      obtain ⟨fx, hfx⟩ := roundTowardZero_isFinite x
      obtain ⟨fy, hfy⟩ := roundTowardZero_isFinite y
      rw [hfx, hfy]
      -- Use transitivity: fx ≤ 0 ≤ fy
      have h1 : roundTowardZero x ≤ Fp.finite 0 := roundTowardZero_neg_le_zero x hx_neg
      have h2 : Fp.finite 0 ≤ roundTowardZero y := roundTowardZero_zero_le_pos y hy_pos
      rw [hfx] at h1; rw [hfy] at h2
      exact Fp.finite_le_trans h1 h2
  · -- x = 0
    rw [hx_zero, roundTowardZero_zero]
    rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · -- y < 0 contradicts 0 ≤ y
      linarith
    · -- y = 0
      rw [hy_zero, roundTowardZero_zero]
      rw [Fp.le_def]; right; rfl
    · -- y > 0
      exact roundTowardZero_zero_le_pos y hy_pos
  · -- x > 0
    have hy_pos : 0 < y := lt_of_lt_of_le hx_pos h
    rw [roundTowardZero_pos_eq x hx_pos, roundTowardZero_pos_eq y hy_pos]
    unfold roundDown findPredecessor
    simp only [ne_of_gt hx_pos, ↓reduceDIte, hx_pos, ne_of_gt hy_pos, hy_pos]
    rw [Fp.finite_le_finite_iff]
    exact findPredecessorPos_mono hx_pos hy_pos h

/-- roundTowardZero never increases magnitude -/
theorem roundTowardZero_magnitude_le [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → |f.toVal| ≤ |x| := by
  intro h
  cases' lt_trichotomy x 0 with h1 h2
  · rw [roundTowardZero_neg_eq x h1] at h
    unfold roundUp at h
    rw [findSuccessor_neg_eq x h1, Fp.finite.injEq] at h
    have ha := findPredecessorPos_le (-x) (neg_pos.mpr h1)
    rw [neg_eq_iff_eq_neg] at h
    rw [h, FiniteFp.toVal_neg_eq_neg] at ha
    norm_num at ha
    apply abs_le_abs_of_nonpos
    · have := findPredecessorPos_nonneg (x := -x) (hpos := neg_pos.mpr h1)
      rw [h, FiniteFp.toVal_neg_eq_neg] at this
      linarith
    · trivial
  · cases' h2 with h2 h3
    · rw [h2, abs_zero]
      rw [h2, roundTowardZero_zero, Fp.finite.injEq] at h
      rw [← h, FiniteFp.toVal_zero, abs_zero]
    · rw [roundTowardZero_pos_eq x h3] at h
      unfold roundDown at h
      rw [findPredecessor_pos_eq x h3, Fp.finite.injEq] at h
      have ha := findPredecessorPos_le x h3
      rw [← h]
      apply abs_le_abs_of_nonneg
      apply findPredecessorPos_nonneg
      trivial

theorem roundTowardZero_le_pos [FloatFormat] (x : R) (f : FiniteFp) (hpos : 0 < x) :
  roundTowardZero x = Fp.finite f → f.toVal ≤ x := by
  intro hf
  apply le_of_abs_le
  rw [← abs_of_pos hpos]
  apply roundTowardZero_magnitude_le x f hf

/-- roundTowardZero preserves sign for non-zero finite results -/
theorem roundTowardZero_pos [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → f.toVal ≠ (0 : R) → (0 < x ↔ (0 : R) < f.toVal) := by
  intro hf fnz
  constructor
  · intro xpos
    rw [roundTowardZero_pos_eq x xpos] at hf
    unfold roundDown at hf
    rw [findPredecessor_pos_eq x xpos, Fp.finite.injEq] at hf
    rw [← hf]
    apply findPredecessorPos_pos
    have := findPredecessorPos_nonneg (x := x) (hpos := xpos)
    rw [← hf] at fnz
    have : (0 : R) < (findPredecessorPos x xpos).toVal := lt_of_le_of_ne this fnz.symm
    apply findPredecessorPos_pos_iff.mpr this
  · intro fpos
    unfold roundTowardZero at hf
    split_ifs at hf with h1 h2
    · rw [Fp.finite.injEq] at hf
      rw [← hf, FiniteFp.toVal_zero] at fnz
      contradiction
    · trivial
    · norm_num at h2
      have h2 : x < 0 := h2.lt_of_ne h1
      unfold roundUp at hf
      rw [findSuccessor_neg_eq x h2, Fp.finite.injEq] at hf
      rw [neg_eq_iff_eq_neg] at hf
      have ha := findPredecessorPos_le (-x) (neg_pos.mpr h2)
      rw [hf, FiniteFp.toVal_neg_eq_neg] at ha
      have ha' := findPredecessorPos_nonneg (x := -x) (hpos := neg_pos.mpr h2)
      rw [hf, FiniteFp.toVal_neg_eq_neg] at ha'
      norm_num at ha'
      linarith


end RoundTowardZero

end Rounding
