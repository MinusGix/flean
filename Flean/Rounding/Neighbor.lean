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

/-- Helper: any Fp.finite value ≤ Fp.infinite false (positive infinity) -/
private theorem Fp.finite_le_pos_inf (f : FiniteFp) : Fp.finite f ≤ Fp.infinite false := by
  rw [Fp.le_def]; left; simp

/-- Helper: roundSubnormalUp result toVal ≤ 2^min_exp -/
private theorem roundSubnormalUp_toVal_le_min_exp (x : R) (hx : isSubnormalRange x) :
    (roundSubnormalUp x hx).toVal (R := R) ≤ (2 : R) ^ FloatFormat.min_exp := by
  have hulp_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by linearize
  have hk_pos : 0 < ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ :=
    Int.ceil_div_pos hx.left hulp_pos
  by_cases hk_ge : (2 : ℤ) ^ (FloatFormat.prec - 1).toNat ≤
      ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉
  · -- Transition case: result is smallestPosNormal, toVal = 2^min_exp
    have hrx : roundSubnormalUp x hx = FiniteFp.smallestPosNormal := by
      unfold roundSubnormalUp; simp only [ge_iff_le, hk_ge, ↓reduceDIte]
    rw [hrx, FiniteFp.smallestPosNormal_toVal]
  · -- Stays subnormal: result = ⟨false, min_exp, k.natAbs, _⟩
    push_neg at hk_ge
    have hnatabs_bound : (⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉).natAbs <
        2 ^ (FloatFormat.prec - 1).toNat := by
      zify [Nat.one_le_two_pow]; rw [abs_of_nonneg (le_of_lt hk_pos)]; omega
    have hval_eq : (roundSubnormalUp x hx).toVal (R := R) =
        (⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉).natAbs *
        (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1) := by
      unfold roundSubnormalUp
      simp only [ge_iff_le, not_le.mpr hk_ge, ↓reduceDIte]
      unfold FiniteFp.toVal FiniteFp.sign'
      simp [FloatFormat.radix_val_eq_two]
    rw [hval_eq]
    apply le_of_lt
    calc ((⌈x / (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)⌉).natAbs : R) *
            (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1)
        < (2 ^ (FloatFormat.prec - 1).toNat : R) * (2 : R) ^ (FloatFormat.min_exp - ↑FloatFormat.prec + 1) := by
          apply mul_lt_mul_of_pos_right (by exact_mod_cast hnatabs_bound) hulp_pos
      _ = (2 : R) ^ FloatFormat.min_exp := by
          rw [← zpow_natCast (2 : R), FloatFormat.prec_sub_one_toNat_eq, two_zpow_mul]; congr 1; ring

/-- Helper: if roundNormalUp x = +∞ for normal x, then x > largestFiniteFloat.toVal -/
private theorem roundNormalUp_inf_imp_gt_lff (x : R) (hx : isNormalRange x) (b : Bool)
    (h : roundNormalUp x hx = Fp.infinite b) : x > FiniteFp.largestFiniteFloat.toVal := by
  by_contra h_le
  push_neg at h_le
  unfold roundNormalUp at h
  extract_lets e binade_base scaled m_scaled m mpos at h
  norm_num at h
  split_ifs at h with hm he
  · -- hm : 2^prec ≤ m, he : e + 1 > max_exp
    -- e = findExponentDown x = max_exp
    have he_eq : e = FloatFormat.max_exp := by
      have hfed := findExponentDown_normal x hx
      have hlog_lt : Int.log 2 x < FloatFormat.max_exp + 1 :=
        (Int.lt_zpow_iff_log_lt (by norm_num : 1 < 2) (isNormalRange_pos x hx)).mp hx.right
      show findExponentDown x = FloatFormat.max_exp
      rw [hfed]; omega
    -- m = ⌈m_scaled⌉ ≥ 2^prec means m_scaled > 2^prec - 1
    have hms_gt := Int.lt_ceil.mp (show (2 : ℤ) ^ FloatFormat.prec.toNat - 1 < m from by omega)
    -- hms_gt : ↑(2^prec - 1) < m_scaled
    unfold m_scaled scaled binade_base at hms_gt
    rw [he_eq] at hms_gt
    -- hms_gt : ↑(2^prec - 1) < x / 2^max_exp * 2^(prec-1)
    -- Multiply both sides by 2^max_exp to get ↑(2^prec-1) * 2^max_exp < x * 2^(prec-1)
    have hbb_pos : (0 : R) < (2 : R) ^ FloatFormat.max_exp := by linearize
    have hms_rearr : (((2 : ℤ) ^ FloatFormat.prec.toNat - 1 : ℤ) : R) * (2 : R) ^ FloatFormat.max_exp <
        x * (2 : R) ^ (FloatFormat.prec - 1) := by
      have h1 := mul_lt_mul_of_pos_right hms_gt hbb_pos
      rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hbb_pos)] at h1
    -- hms_gt : ↑(2^prec - 1) * 2^max_exp < x * 2^(prec-1)
    -- Rewrite lff.toVal as (2^prec - 1) * 2^(max_exp - prec + 1) and show contradiction
    rw [FiniteFp.largestFiniteFloat_toVal] at h_le
    have hlff_eq : (2 : R) ^ FloatFormat.max_exp * (2 - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1)) =
        (((2 : ℤ) ^ FloatFormat.prec.toNat - 1 : ℤ) : R) * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
      -- LHS = 2^(max_exp+1) - 2^(max_exp - prec + 1)
      -- RHS = (2^prec - 1) * 2^(max_exp - prec + 1) = 2^prec * 2^(max_exp-prec+1) - 2^(max_exp-prec+1)
      --     = 2^(max_exp+1) - 2^(max_exp-prec+1)
      rw [mul_sub, show (2 : R) ^ FloatFormat.max_exp * 2 = (2 : R) ^ (FloatFormat.max_exp + 1) from by
        rw [← zpow_add_one₀ (show (2:R) ≠ 0 by norm_num)],
        show (2 : R) ^ FloatFormat.max_exp * (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) =
             (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) from by
        rw [two_zpow_mul]; congr 1; ring]
      push_cast [sub_mul]
      rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq, two_zpow_mul]
      simp only [one_mul]
      congr 1; ring
    -- h_le : x ≤ ↑(2^prec - 1) * 2^(max_exp - prec + 1)
    -- So x * 2^(prec-1) ≤ ↑(2^prec - 1) * 2^(max_exp - prec + 1) * 2^(prec-1) = ↑(2^prec - 1) * 2^max_exp
    have hprec_pos : (0 : R) < (2 : R) ^ (FloatFormat.prec - 1) := by linearize
    have hle2 : x * (2 : R) ^ (FloatFormat.prec - 1) ≤
        (((2 : ℤ) ^ FloatFormat.prec.toNat - 1 : ℤ) : R) * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) *
        (2 : R) ^ (FloatFormat.prec - 1) := by
      apply mul_le_mul_of_nonneg_right (by linarith [hlff_eq]) (le_of_lt hprec_pos)
    have hcollapse : (((2 : ℤ) ^ FloatFormat.prec.toNat - 1 : ℤ) : R) * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) *
        (2 : R) ^ (FloatFormat.prec - 1) =
        (((2 : ℤ) ^ FloatFormat.prec.toNat - 1 : ℤ) : R) * (2 : R) ^ FloatFormat.max_exp := by
      rw [mul_assoc, two_zpow_mul]; congr 1; ring
    linarith [hcollapse, hms_rearr]
  -- All other branches return Fp.finite, contradicting h : ... = Fp.infinite b
  all_goals (first | exact absurd h (by simp) | cases h)

/-- findSuccessorPos is monotone: if 0 < x ≤ y then findSuccessorPos x ≤ findSuccessorPos y.
    The ceiling analogue of findPredecessorPos_toVal_mono / findPredecessorPos_mono. -/
theorem findSuccessorPos_mono {x y : R} (hx : 0 < x) (hy : 0 < y) (h : x ≤ y) :
    findSuccessorPos x hx ≤ findSuccessorPos y hy := by
  unfold findSuccessorPos
  -- Helper to dispatch isZero contradictions for roundSubnormalUp
  have hzero_absurd : ∀ (hsr : isSubnormalRange x), ¬(roundSubnormalUp x hsr).isZero := by
    intro hsr hz
    have hpos := roundSubnormalUp_pos (hsr := hsr)
    rw [FiniteFp.isZero_iff] at hz
    rcases hz with h1 | h2
    · rw [h1, FiniteFp.toVal_zero] at hpos; linarith
    · rw [h2, FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_zero] at hpos; linarith
  by_cases hx_sub : x < (2 : R) ^ FloatFormat.min_exp
  · -- x is in subnormal range
    simp only [hx_sub, ↓reduceDIte]
    by_cases hy_sub : y < (2 : R) ^ FloatFormat.min_exp
    · -- Both subnormal
      simp only [hy_sub, ↓reduceDIte]
      rw [Fp.finite_le_finite_iff]
      exact FiniteFp.toVal_le_handle R (roundSubnormalUp_toVal_mono ⟨hx, hx_sub⟩ ⟨hy, hy_sub⟩ h)
        (fun ⟨hz, _⟩ => absurd hz (hzero_absurd ⟨hx, hx_sub⟩))
    · -- x subnormal, y not subnormal
      simp only [hy_sub, ↓reduceDIte]
      by_cases hy_nor : y < (2 : R) ^ (FloatFormat.max_exp + 1)
      · -- x subnormal, y normal
        simp only [hy_nor, ↓reduceDIte]
        have hynr : isNormalRange y := ⟨le_of_not_gt hy_sub, hy_nor⟩
        match hrU : roundNormalUp y hynr with
        | Fp.finite g =>
          rw [Fp.finite_le_finite_iff]
          exact FiniteFp.toVal_le_handle R
            (calc (roundSubnormalUp x ⟨hx, hx_sub⟩).toVal (R := R)
                  ≤ (2 : R) ^ FloatFormat.min_exp := roundSubnormalUp_toVal_le_min_exp x ⟨hx, hx_sub⟩
                _ ≤ y := le_of_not_gt hy_sub
                _ ≤ g.toVal := roundNormalUp_ge y hynr g hrU)
            (fun ⟨hz, _⟩ => absurd hz (hzero_absurd ⟨hx, hx_sub⟩))
        | Fp.infinite b =>
          have := roundNormalUp_ne_neg_infinite y hynr; rw [hrU] at this; simp at this; subst this
          exact Fp.finite_le_pos_inf _
        | Fp.NaN => exact absurd hrU (roundNormalUp_ne_nan y _)
      · -- x subnormal, y overflow
        simp only [hy_nor, ↓reduceDIte]
        exact Fp.finite_le_pos_inf _
  · -- x normal or overflow
    push_neg at hx_sub
    simp only [not_lt.mpr hx_sub, ↓reduceDIte]
    have hy_not_sub : ¬(y < (2 : R) ^ FloatFormat.min_exp) := not_lt.mpr (le_trans hx_sub h)
    simp only [hy_not_sub, ↓reduceDIte]
    by_cases hx_nor : x < (2 : R) ^ (FloatFormat.max_exp + 1)
    · simp only [hx_nor, ↓reduceDIte]
      by_cases hy_nor : y < (2 : R) ^ (FloatFormat.max_exp + 1)
      · -- Both normal
        simp only [hy_nor, ↓reduceDIte]
        have hxnr : isNormalRange x := ⟨hx_sub, hx_nor⟩
        have hynr : isNormalRange y := ⟨le_of_not_gt hy_not_sub, hy_nor⟩
        match hrUx : roundNormalUp x hxnr with
        | Fp.finite gx =>
          match hrUy : roundNormalUp y hynr with
          | Fp.finite gy =>
            rw [Fp.finite_le_finite_iff]
            apply FiniteFp.toVal_le_handle R
            · exact roundNormalUp_toVal_mono hxnr hynr hrUx hrUy h
            · intro ⟨hzx, _⟩
              exfalso
              have := roundNormalUp_pos hrUx
              rw [FiniteFp.isZero_iff] at hzx
              rcases hzx with h1 | h2
              · rw [h1, FiniteFp.toVal_zero] at this; linarith
              · rw [h2, FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_zero] at this; linarith
          | Fp.infinite b =>
            have := roundNormalUp_ne_neg_infinite y hynr; rw [hrUy] at this; simp at this; subst this
            exact Fp.finite_le_pos_inf _
          | Fp.NaN => exact absurd hrUy (roundNormalUp_ne_nan y _)
        | Fp.infinite bx =>
          have := roundNormalUp_ne_neg_infinite x hxnr; rw [hrUx] at this; simp at this; subst this
          have hx_gt := roundNormalUp_inf_imp_gt_lff x hxnr false hrUx
          have hy_gt : y > FiniteFp.largestFiniteFloat.toVal := lt_of_lt_of_le hx_gt h
          match hrUy : roundNormalUp y hynr with
          | Fp.finite gy =>
            exfalso
            linarith [FiniteFp.finite_le_largestFiniteFloat (R := R) gy,
                       roundNormalUp_ge y hynr gy hrUy]
          | Fp.infinite by_ =>
            have := roundNormalUp_ne_neg_infinite y hynr; rw [hrUy] at this; simp at this; subst this
            exact Fp.le_refl _
          | Fp.NaN => exact absurd hrUy (roundNormalUp_ne_nan y _)
        | Fp.NaN => exact absurd hrUx (roundNormalUp_ne_nan x _)
      · -- x normal, y overflow
        simp only [hy_nor, ↓reduceDIte]
        match hrU : roundNormalUp x ⟨hx_sub, hx_nor⟩ with
        | Fp.finite g => exact Fp.finite_le_pos_inf _
        | Fp.infinite b =>
          have := roundNormalUp_ne_neg_infinite x ⟨hx_sub, hx_nor⟩; rw [hrU] at this; simp at this; subst this
          exact Fp.le_refl _
        | Fp.NaN => exact absurd hrU (roundNormalUp_ne_nan x _)
    · -- x overflow
      simp only [hx_nor, ↓reduceDIte]
      have hy_not_nor : ¬(y < (2 : R) ^ (FloatFormat.max_exp + 1)) := not_lt.mpr (le_trans (not_lt.mp hx_nor) h)
      simp only [hy_not_nor, ↓reduceDIte]
      exact Fp.le_refl _

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

/-- findPredecessor is monotone on negative values.
    For x ≤ y < 0, findPredecessor x ≤ findPredecessor y.
    This follows from findSuccessorPos_mono by symmetry. -/
theorem findPredecessor_mono_neg {x y : R} (hx : x < 0) (hy : y < 0) (h : x ≤ y) :
    findPredecessor x ≤ findPredecessor y := by
  rw [findPredecessor_neg_eq x hx, findPredecessor_neg_eq y hy]
  -- Goal: -(findSuccessorPos(-x)) ≤ -(findSuccessorPos(-y))
  -- From x ≤ y < 0, we get 0 < -y ≤ -x
  have hny : 0 < -y := neg_pos.mpr hy
  have hnx : 0 < -x := neg_pos.mpr hx
  have hyx : -y ≤ -x := neg_le_neg h
  -- findSuccessorPos(-y) ≤ findSuccessorPos(-x) (larger input → larger output)
  have hmono := findSuccessorPos_mono hny hnx hyx
  -- Match on both to handle Fp negation
  match hfx : findSuccessorPos (-x) hnx, hfy : findSuccessorPos (-y) hny with
  | Fp.finite fx, Fp.finite fy =>
    rw [hfx, hfy] at hmono
    simp only [Fp.neg_finite, Fp.finite_le_finite_iff] at hmono ⊢
    apply FiniteFp.toVal_le_handle R
    · rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
      linarith [FiniteFp.le_toVal_le (R := R) hmono]
    · intro ⟨hxz, _⟩
      -- -fx is zero means fx.toVal = 0, contradicts findSuccessorPos_pos
      exfalso
      have := findSuccessorPos_pos hfx
      linarith [FiniteFp.toVal_isZero (R := R) hxz, FiniteFp.toVal_neg_eq_neg (R := R) (x := fx)]
  | Fp.finite _, Fp.infinite b =>
    rw [hfx, hfy] at hmono
    -- Fp.infinite b ≤ Fp.finite _, forces b = true (-∞)
    -- but findSuccessorPos ≠ -∞
    exfalso
    rw [Fp.le_def] at hmono
    cases hmono with
    | inl hlt =>
      change (b = true) at hlt
      rw [hlt] at hfy
      exact findSuccessorPos_ne_neg_inf (-y) hny hfy
    | inr heq => simp at heq
  | Fp.infinite false, Fp.finite fy =>
    -- findSuccessorPos(-x) = +∞, so -(+∞) = -∞ ≤ anything
    simp only [Fp.neg_finite, Fp.le_def, Fp.lt_def]
    left; rfl
  | Fp.infinite false, Fp.infinite false =>
    -- Both +∞, both negate to -∞
    exact Fp.le_refl _
  | Fp.infinite false, Fp.infinite true =>
    exfalso; exact findSuccessorPos_ne_neg_inf (-y) hny hfy
  | Fp.infinite true, _ =>
    exfalso; exact findSuccessorPos_ne_neg_inf (-x) hnx hfx
  | Fp.NaN, _ => exact absurd hfx (findSuccessorPos_ne_nan (-x) hnx)
  | _, Fp.NaN => exact absurd hfy (findSuccessorPos_ne_nan (-y) hny)

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
