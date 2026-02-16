import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational

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
      rw [FloatFormat.pow_toNat_sub_one_eq_zpow_sub_one]
      exact isSubnormalRange_div_binade_upper h
    FiniteFp.mk false FloatFormat.min_exp k.natAbs vf

/-- Round a positive subnormal value up -/
def roundSubnormalUp (x : R) (h : isSubnormalRange x) : FiniteFp :=
  -- In subnormal range, spacing is uniform: 2^(min_exp - prec + 1)
  let k := ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉
  if hk : k ≥ (2 : ℤ)^(FloatFormat.prec - 1).toNat then
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
  simp only []
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
  by_cases hk : k ≥ (2 : ℤ)^(FloatFormat.prec - 1).toNat
  · -- Case: k ≥ 2^(prec-1), transition to normal range
    unfold k at hk
    simp only [ge_iff_le, hk, ↓reduceDIte] at h
    -- h now shows: f = FiniteFp.smallestPosNormal
    rw [← h, FiniteFp.smallestPosNormal_toVal]
    exact le_of_lt (hsr.right)
  · -- Case: k < 2^(prec-1), stays in subnormal range
    unfold k at hk
    simp only [ge_iff_le, hk, ↓reduceDIte] at h
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
    have hdiv_nonneg : ¬(x / 2 ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1) < 0) := by
      norm_num
      apply div_nonneg
      linarith
      linearize
    simp only [hdiv_nonneg, false_or] at h'
    have hfloor_pos : 0 < ⌊x / 2 ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)⌋ := Int.floor_pos.mpr (by trivial)
    rw [abs_of_pos (Int.cast_pos.mpr hfloor_pos)]
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
    · exact abs_nonneg _
    · linearize

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

/-- Monotonicity of roundSubnormalDown on toVal: if x ≤ y in the subnormal range, then
    (roundSubnormalDown x).toVal ≤ (roundSubnormalDown y).toVal -/
theorem roundSubnormalDown_toVal_mono {x y : R} (hx : isSubnormalRange x) (hy : isSubnormalRange y) (h : x ≤ y) :
    (roundSubnormalDown x hx).toVal (R := R) ≤ (roundSubnormalDown y hy).toVal (R := R) := by
  -- Use floor monotonicity: if x ≤ y then ⌊x/ulp⌋ ≤ ⌊y/ulp⌋
  have hulp_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by linearize
  have hkx_le_ky : ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ ≤
                   ⌊y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ := by
    apply Int.floor_le_floor
    apply div_le_div_of_nonneg_right h (le_of_lt hulp_pos)
  -- Case split on whether each rounds to zero
  by_cases hkx_zero : ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ = 0
  · -- x rounds to zero
    have hrx : roundSubnormalDown x hx = 0 := by
      unfold roundSubnormalDown
      simp only [hkx_zero, ↓reduceDIte]
    rw [hrx, FiniteFp.toVal_zero]
    apply roundSubnormalDown_nonneg
  · -- x doesn't round to zero
    by_cases hky_zero : ⌊y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ = 0
    · -- y rounds to zero but x doesn't - contradiction
      exfalso
      have hkx_nonneg : 0 ≤ ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ :=
        Int.floor_nonneg.mpr (div_nonneg (le_of_lt hx.left) (le_of_lt hulp_pos))
      have hkx_le_zero : ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ ≤ 0 := by
        calc _ ≤ ⌊y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ := hkx_le_ky
          _ = 0 := hky_zero
      have := le_antisymm hkx_le_zero hkx_nonneg
      exact hkx_zero this
    · -- Neither rounds to zero
      unfold roundSubnormalDown
      simp only [hkx_zero, ↓reduceDIte, hky_zero]
      unfold FiniteFp.toVal FiniteFp.sign'
      rw [FloatFormat.radix_val_eq_two]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, ge_iff_le]
      -- Goal: |↑(floor x).natAbs| * 2^exp ≤ |↑(floor y).natAbs| * 2^exp
      gcongr
      -- Goal: (floor x).natAbs ≤ (floor y).natAbs as Nats
      -- Since floor results are non-negative, natAbs preserves the order
      have hkx_nonneg : 0 ≤ ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ :=
        Int.floor_nonneg.mpr (div_nonneg (le_of_lt hx.left) (le_of_lt hulp_pos))
      have hky_nonneg : 0 ≤ ⌊y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ :=
        Int.floor_nonneg.mpr (div_nonneg (le_of_lt hy.left) (le_of_lt hulp_pos))
      omega

/-- Monotonicity of roundSubnormalUp on toVal: if x ≤ y in the subnormal range, then
    (roundSubnormalUp x).toVal ≤ (roundSubnormalUp y).toVal -/
theorem roundSubnormalUp_toVal_mono {x y : R} (hx : isSubnormalRange x) (hy : isSubnormalRange y) (h : x ≤ y) :
    (roundSubnormalUp x hx).toVal (R := R) ≤ (roundSubnormalUp y hy).toVal (R := R) := by
  have hulp_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by linearize
  -- Ceiling monotonicity: ⌈x/ulp⌉ ≤ ⌈y/ulp⌉
  have hcx_le_cy : ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ ≤
                   ⌈y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ := by
    apply Int.ceil_le_ceil
    apply div_le_div_of_nonneg_right h (le_of_lt hulp_pos)
  have hkx_pos : 0 < ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ :=
    Int.ceil_div_pos hx.left hulp_pos
  have hky_pos : 0 < ⌈y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ :=
    Int.ceil_div_pos hy.left hulp_pos
  -- Case split on whether each hits the transition to normal
  by_cases hkx_ge : ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ ≥
      (2 : ℤ) ^ (FloatFormat.prec - 1).toNat
  · -- x transitions to normal: result is smallestPosNormal
    by_cases hky_ge : ⌈y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ ≥
        (2 : ℤ) ^ (FloatFormat.prec - 1).toNat
    · -- Both transition: both return smallestPosNormal, equal
      have hrx : roundSubnormalUp x hx = FiniteFp.smallestPosNormal := by
        unfold roundSubnormalUp; simp only [ge_iff_le, hkx_ge, ↓reduceDIte]
      have hry : roundSubnormalUp y hy = FiniteFp.smallestPosNormal := by
        unfold roundSubnormalUp; simp only [ge_iff_le, hky_ge, ↓reduceDIte]
      rw [hrx, hry]
    · -- kx ≥ 2^(prec-1) but ky < 2^(prec-1): contradiction since kx ≤ ky
      exfalso; push_neg at hky_ge; omega
  · -- x stays subnormal
    push_neg at hkx_ge
    by_cases hky_ge : ⌈y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ ≥
        (2 : ℤ) ^ (FloatFormat.prec - 1).toNat
    · -- x subnormal, y transitions to normal: roundSubnormalUp x ≤ smallestPosNormal
      have hry : roundSubnormalUp y hy = FiniteFp.smallestPosNormal := by
        unfold roundSubnormalUp; simp only [ge_iff_le, hky_ge, ↓reduceDIte]
      rw [hry]
      -- Direct unfold of roundSubnormalUp x in the non-transition case
      show (roundSubnormalUp x hx).toVal (R := R) ≤ FiniteFp.smallestPosNormal.toVal
      -- The transition case toVal is kx * ulp where kx < 2^(prec-1)
      -- smallestPosNormal.toVal = 2^min_exp = 2^(prec-1) * ulp
      -- So kx * ulp ≤ (2^(prec-1)-1) * ulp < 2^(prec-1) * ulp ✓
      have hnatabs_bound : (⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉).natAbs <
          2 ^ (FloatFormat.prec - 1).toNat := by
        zify [Nat.one_le_two_pow]; rw [abs_of_nonneg (le_of_lt hkx_pos)]; omega
      -- The toVal of the non-transition subnormal up = kx.natAbs * 2^(min_exp - prec + 1)
      -- Since kx.natAbs < 2^(prec-1), toVal < 2^(prec-1) * 2^(min_exp-prec+1) = 2^min_exp
      -- And 2^min_exp = smallestPosNormal.toVal
      apply le_of_lt
      -- toVal < smallestPosNormal.toVal = 2^min_exp
      rw [FiniteFp.smallestPosNormal_toVal]
      -- Now show toVal(roundSubnormalUp x) < 2^min_exp
      -- Step 1: Get the toVal value by going through FiniteFp.toVal_pos and bounding
      -- The toVal = sign * m * 2^(e - prec + 1), with sign=1, e=min_exp
      -- = kx.natAbs * 2^(min_exp - prec + 1)
      -- We know kx > 0, so kx.natAbs = kx, and kx < 2^(prec-1)
      have hval_eq : (roundSubnormalUp x hx).toVal (R := R) =
          (⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉).natAbs *
          (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1) := by
        unfold roundSubnormalUp
        simp only [ge_iff_le, not_le.mpr hkx_ge, ↓reduceDIte]
        unfold FiniteFp.toVal FiniteFp.sign'
        simp [FloatFormat.radix_val_eq_two]
      rw [hval_eq]
      have h_cast_bound : ((⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉).natAbs : R) <
          (2 ^ (FloatFormat.prec - 1).toNat : R) := by exact_mod_cast hnatabs_bound
      calc ((⌈x / (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)⌉).natAbs : R) *
              (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)
          < (2 ^ (FloatFormat.prec - 1).toNat : R) * (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1) := by
            apply mul_lt_mul_of_pos_right h_cast_bound (by linearize)
        _ = (2 : R) ^ FloatFormat.min_exp := by
            rw [← zpow_natCast (2 : R), FloatFormat.prec_sub_one_toNat_eq,
              two_zpow_mul]; congr 1; ring
    · -- Both stay subnormal
      push_neg at hky_ge
      -- Both return ⟨false, min_exp, k.natAbs, _⟩: reduce to natAbs monotonicity
      show (roundSubnormalUp x hx).toVal (R := R) ≤ (roundSubnormalUp y hy).toVal (R := R)
      -- Unfold to get at the FiniteFp.mk structure
      have hrx_sign : (roundSubnormalUp x hx).s = false := by
        unfold roundSubnormalUp; simp only [ge_iff_le, not_le.mpr hkx_ge, ↓reduceDIte]
      have hry_sign : (roundSubnormalUp y hy).s = false := by
        unfold roundSubnormalUp; simp only [ge_iff_le, not_le.mpr hky_ge, ↓reduceDIte]
      have hrx_exp : (roundSubnormalUp x hx).e = FloatFormat.min_exp := by
        unfold roundSubnormalUp; simp only [ge_iff_le, not_le.mpr hkx_ge, ↓reduceDIte]
      have hry_exp : (roundSubnormalUp y hy).e = FloatFormat.min_exp := by
        unfold roundSubnormalUp; simp only [ge_iff_le, not_le.mpr hky_ge, ↓reduceDIte]
      have hrx_m : (roundSubnormalUp x hx).m =
          (⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉).natAbs := by
        unfold roundSubnormalUp; simp only [ge_iff_le, not_le.mpr hkx_ge, ↓reduceDIte]
      have hry_m : (roundSubnormalUp y hy).m =
          (⌈y / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉).natAbs := by
        unfold roundSubnormalUp; simp only [ge_iff_le, not_le.mpr hky_ge, ↓reduceDIte]
      unfold FiniteFp.toVal FiniteFp.sign'
      rw [hrx_sign, hry_sign, hrx_exp, hry_exp, FloatFormat.radix_val_eq_two]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [hrx_m, hry_m]
      gcongr
      -- natAbs preserves order for positive integers
      omega

end Rounding
