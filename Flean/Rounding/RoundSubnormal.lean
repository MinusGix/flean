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
import Flean.CommonConstants

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-- Round a positive subnormal value down -/
def roundSubnormalDown (x : R) (h : isSubnormalRange x) : FiniteFp :=
  -- In subnormal range, spacing is uniform: 2^(min_exp - prec + 1)
  let ulp := (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)
  let k := ⌊x / ulp⌋
  if knz : k = 0 then
    0
  else
    have vf : IsValidFiniteVal FloatFormat.min_exp k.natAbs := by
      unfold isSubnormalRange at h
      have kpos : 0 < k := by
        apply lt_of_le_of_ne
        apply Int.floor_nonneg.mpr
        apply div_nonneg
        linarith
        unfold ulp; linearize
        omega

      apply IsValidFiniteVal_subnormal
      zify
      rw [abs_of_pos kpos]
      apply Int.floor_le_iff.mpr
      norm_num
      exact isSubnormalRange_div_binade_upper h
    FiniteFp.mk false FloatFormat.min_exp k.natAbs vf

/-- Round a positive subnormal value up -/
def roundSubnormalUp (x : R) (h : isSubnormalRange x) : FiniteFp :=
  -- In subnormal range, spacing is uniform: 2^(min_exp - prec + 1)
  let k := ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉
  if hk : k ≥ 2^(FloatFormat.prec - 1) then
    -- Transition to normal range
    FiniteFp.smallestPosNormal
  else
    have vf : IsValidFiniteVal FloatFormat.min_exp k.natAbs := by
      norm_num at hk
      have hu := isSubnormalRange_div_binade_upper h
      unfold isSubnormalRange at h
      have kpos : k > 0 := by
        apply Int.ceil_pos.mpr
        apply div_pos h.left
        linearize
      apply IsValidFiniteVal_subnormal
      zify
      rw [abs_of_pos kpos]
      apply Int.ceil_le.mpr
      have hk' := Int.ceil_lt_iff.mp hk
      norm_num at ⊢ hk'
      exact hk'

    FiniteFp.mk false FloatFormat.min_exp k.natAbs vf

theorem roundSubnormalDown_eq_zero_iff {x : R} {h : isSubnormalRange x} : roundSubnormalDown x h = 0 ↔ x < FiniteFp.smallestPosSubnormal.toVal := by
  unfold roundSubnormalDown
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  rw [FiniteFp.smallestPosSubnormal_toVal]
  have hz := FloatFormat.zpow_min_exp_prec_plus_one_le_zpow_min_exp (R := R)
  split_ifs with h1
  · have h1 := Int.floor_eq_zero_iff.mp h1
    obtain ⟨h1, h2⟩ := Set.mem_Ico.mp h1
    rw [div_lt_iff₀, one_mul] at h2
    constructor
    <;> intro h
    · trivial
    · trivial
    · linearize
  · constructor
    rw [FiniteFp.zero_def]
    norm_num
    · intro h h2
      rw [div_lt_iff₀, one_mul] at h2
      trivial
      linearize
    · intro h2
      rw [FiniteFp.zero_def]
      norm_num
      constructor
      · apply div_nonneg h.left.le (by linearize)
      · rw [div_lt_one_iff]
        left
        constructor
        · linearize
        · trivial

-- Fundamental ceiling property for subnormal range
lemma roundSubnormalUp_ge (x : R) (hsr : isSubnormalRange x) (f : FiniteFp)
  (h : roundSubnormalUp x hsr = f) : x ≤ f.toVal := by
  unfold roundSubnormalUp at h
  let k := ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉
  by_cases hk : k ≥ 2^(FloatFormat.prec - 1)
  · -- Case: k ≥ 2^(prec-1), transition to normal range
    unfold k at hk
    simp only [ge_iff_le, hk, ↓reduceDIte, Fp.finite.injEq] at h
    -- h now shows: f = FiniteFp.smallestPosNormal
    rw [← h, FiniteFp.smallestPosNormal_toVal]
    exact le_of_lt (hsr.right)
  · -- Case: k < 2^(prec-1), stays in subnormal range
    unfold k at hk
    simp only [ge_iff_le, hk, ↓reduceDIte, Fp.finite.injEq] at h
    rw [← h]
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Int.cast_ofNat, ge_iff_le]
    -- Goal: x ≤ k.natAbs * 2^(min_exp - prec + 1)
    -- We know k = ⌈x / 2^(min_exp - prec + 1)⌉ and k > 0 in subnormal range
    -- So k.natAbs = k and k ≥ x / 2^(min_exp - prec + 1)
    -- Therefore k * 2^(min_exp - prec + 1) ≥ x
    have k_pos : 0 < k := Int.ceil_div_pos hsr.left (by linearize)
    rw [Int.cast_natAbs_pos k_pos]
    have h_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by linearize
    -- x / 2^(min_exp - prec + 1) ≤ k
    -- So x ≤ k * 2^(min_exp - prec + 1)
    calc x = x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) *
              (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by {
        rw [div_mul_cancel₀ _ (ne_of_gt h_pos)]
      }
      _ ≤ (k : R) * (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
        apply mul_le_mul_of_nonneg_right
        · exact Int.le_ceil _
        · linearize

theorem roundSubnormalUp_pos {x : R} {hsr : isSubnormalRange x} : (0 : R) < (roundSubnormalUp x hsr).toVal := by
  unfold roundSubnormalUp
  extract_lets k
  split_ifs with h1
  · apply FiniteFp.smallestPosNormal_toVal_pos
  · norm_num
    apply FiniteFp.toVal_pos
    norm_num
    norm_num
    apply Int.ceil_ne_zero_pos
    apply div_pos
    · exact hsr.left
    · linearize

theorem roundSubnormalUp_nonneg {x : R} {hsr : isSubnormalRange x} : (0 : R) ≤ (roundSubnormalUp x hsr).toVal := le_of_lt roundSubnormalUp_pos

theorem roundSubnormalDown_eq_zero_iff' {x : R} {h : isSubnormalRange x} : roundSubnormalDown x h = 0 ↔ x < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
  rw [← FiniteFp.smallestPosSubnormal_toVal]
  exact roundSubnormalDown_eq_zero_iff

/-- A rounded down x bounds the resulting finite float from above -/
theorem roundSubnormalDown_le (x : R) (h : isSubnormalRange x) : (roundSubnormalDown x h).toVal ≤ x := by
  unfold roundSubnormalDown
  simp
  unfold isSubnormalRange at h
  split
  · rw [FiniteFp.toVal_zero]
    linarith
  · rename_i h'
    rw [not_and_or] at h'
    norm_num at h'
    unfold FiniteFp.toVal FiniteFp.sign'
    norm_num
    have : ¬(x / 2 ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1) < 0) := by
      norm_num
      apply div_nonneg
      linarith
      linearize
    simp only [this, false_or] at h'

    rw [Int.cast_natAbs_pos (Int.floor_pos.mpr (by trivial))]

    rw[FloatFormat.radix_val_eq_two]
    apply mul_le_of_le_div₀
    · linarith
    · linearize
    · rw [Int.cast_two]
      apply Int.floor_le

theorem roundSubnormalDown_nonneg {x : R} {h : isSubnormalRange x} : (0 : R) ≤ (roundSubnormalDown x h).toVal := by
  unfold roundSubnormalDown
  simp
  unfold isSubnormalRange at h
  split_ifs
  · rw [FiniteFp.toVal_zero]
  · unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    norm_num
    apply mul_nonneg
    apply Nat.cast_nonneg
    linearize

theorem roundSubnormalDown_pos {x : R} {h : isSubnormalRange x} (hx : FiniteFp.smallestPosSubnormal.toVal ≤ x) : (0 : R) < (roundSubnormalDown x h).toVal := by
  unfold roundSubnormalDown
  extract_lets ulp k
  have : k ≠ 0 := by
    apply Int.floor_ne_zero_ge_one
    unfold ulp
    apply (one_le_div₀ ?_).mpr
    rw [FiniteFp.smallestPosSubnormal_toVal] at hx
    exact hx
    linearize
  simp only [this, ↓reduceDIte, gt_iff_lt]
  apply FiniteFp.toVal_pos
  · norm_num
  · norm_num
    exact this

/-- If the output is positive, then the input is at least the smallest positive subnormal (and thus wasn't rounded down to zero) -/
theorem roundSubnormalDown_pos_iff {x : R} {h : isSubnormalRange x} : FiniteFp.smallestPosSubnormal.toVal ≤ x ↔ (0 : R) < (roundSubnormalDown x h).toVal := by
  constructor
  · exact roundSubnormalDown_pos
  · intro hf
    unfold roundSubnormalDown at hf
    extract_lets ulp k at hf
    split_ifs at hf with h1
    · rw [FiniteFp.toVal_zero] at hf
      linarith
    · norm_num at hf
      obtain ⟨h2, h3⟩ := FiniteFp.toVal_pos_iff.mpr hf
      norm_num at h2 h3
      unfold k ulp at h3
      cases' (Int.floor_ne_zero_iff).mp h3 with h4 h5
      · rw [FiniteFp.smallestPosSubnormal_toVal]
        rw [one_le_div₀] at h4
        trivial
        linearize
      · rw [FiniteFp.smallestPosSubnormal_toVal]
        rw [div_lt_iff₀, zero_mul] at h5
        have xpos := h.left
        linarith
        linearize

end Rounding
