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
import Flean.RoundingImpl

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]

/-- Helper function to determine if a real value is exactly representable as a floating-point number -/
def isExactlyRepresentable [FloatFormat] (x : R) : Prop :=
  ∃ (f : FiniteFp), f.toVal = x

/-- Check if a value is exactly at the midpoint between two consecutive floating-point values -/
def isMidpoint [FloatFormat] (x : R) : Prop :=
  let pred := findPredecessor x
  let succ := findSuccessor x
  match pred, succ with
  | Fp.finite p, Fp.finite s => x = (p.toVal + s.toVal) / 2
  | _, _ => False

/-- Extract the significand's least significant bit to check evenness for tie-breaking -/
def isEvenSignificand [FloatFormat] (f : FiniteFp) : Bool :=
  f.m % 2 = 0

-- Basic properties of rounding with zero
section ZeroProperties

/-- findPredecessor returns 0 when input is 0 -/
theorem findPredecessor_zero [FloatFormat] : findPredecessor (0 : R) = Fp.finite 0 := by
  -- By definition, findPredecessor checks if x = 0 first
  unfold findPredecessor
  -- The condition (0 : R) = 0 is true, so we take the first branch
  simp

/-- findSuccessor returns 0 when input is 0 -/
theorem findSuccessor_zero [FloatFormat] : findSuccessor (0 : R) = Fp.finite 0 := by
  -- By definition, findSuccessor also checks if x = 0 first
  unfold findSuccessor
  -- The condition (0 : R) = 0 is true, so we take the first branch
  simp

end ZeroProperties

-- Round toward negative infinity (floor)
section RoundDown

/-- Round toward negative infinity -/
def roundDown [FloatFormat] (x : R) : Fp :=
  findPredecessor x

/-- roundDown returns 0 when input is 0 -/
theorem roundDown_zero [FloatFormat] : roundDown (0 : R) = Fp.finite 0 := by
  unfold roundDown
  exact findPredecessor_zero

/-- roundDown never produces positive infinity -/
theorem roundDown_ne_pos_inf [FloatFormat] (x : R) : roundDown x ≠ Fp.infinite false := by
  unfold roundDown findPredecessor
  intro a
  split at a
  · -- Case: x = 0, returns Fp.finite 0 ≠ Fp.infinite false
    simp_all
  · split at a
    · -- Case: x ≠ 0 and x > 0, uses findPredecessorPos which never returns positive infinity
      have : findPredecessorPos x (by assumption) ≠ Fp.infinite false := findPredecessorPos_ne_inf x (by assumption) false
      contradiction
    · -- Case: x ≠ 0 and x ≤ 0, so x < 0 by trichotomy
      -- The result is match findSuccessorPos (-x) with | Fp.infinite b => Fp.infinite (!b) | ..
      -- For result to be Fp.infinite false, we need findSuccessorPos (-x) = Fp.infinite true
      -- But findSuccessorPos never returns Fp.infinite true
      have h_lt : x < 0 := by
        -- We have ¬x = 0 and ¬0 < x, so by trichotomy x < 0
        cases' lt_trichotomy x 0 with h h
        · exact h
        · cases' h with h h
          · simp_all
          · simp_all
      have h_neg_pos : 0 < -x := neg_pos.mpr h_lt
      have : findSuccessorPos (-x) h_neg_pos ≠ Fp.infinite true := findSuccessorPos_ne_neg_inf (-x) h_neg_pos
      -- Now split on the match expression
      generalize heq : findSuccessorPos (-x) h_neg_pos = result
      simp only [heq] at a
      cases result with
      | finite f => simp_all
      | infinite b =>
        simp_all only [Bool.not_eq_false]
        rw [← heq] at this
        simp_all
      | NaN => simp_all

theorem roundDown_lt_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundDown x = Fp.finite 0 := by
  unfold roundDown findPredecessor
  simp [ne_of_gt hn, hn]
  unfold findPredecessorPos
  -- Since x < smallestPosSubnormal, x is in subnormal range
  have h_sub : x < (2 : R) ^ FloatFormat.min_exp := by
    -- smallestPosSubnormal = 2^(min_exp - prec + 1) < 2^min_exp
    have : FiniteFp.smallestPosSubnormal.toVal < (2 : R) ^ FloatFormat.min_exp := by
      rw [FiniteFp.smallestPosSubnormal_toVal]
      apply zpow_lt_zpow_right₀ (by norm_num : (1 : R) < 2)
      have := FloatFormat.valid_prec
      omega
    exact lt_trans hs this
  simp [h_sub]
  unfold roundSubnormalDown
  -- The ULP in subnormal range is 2^(min_exp - prec + 1) = smallestPosSubnormal
  -- So ⌊x / smallestPosSubnormal⌋ = 0 since x < smallestPosSubnormal
  have h_floor : ⌊x / FiniteFp.smallestPosSubnormal.toVal⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor
    · apply div_nonneg (le_of_lt hn)
      rw [FiniteFp.smallestPosSubnormal_toVal]
      exact le_of_lt (zpow_pos (by norm_num) _)
    · rw [div_lt_one_iff]
      left
      constructor
      · linarith
      · trivial
  rw [FiniteFp.smallestPosSubnormal_toVal] at h_floor
  simp [h_floor]

theorem roundDown_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x ≥ (2 : R) ^ (FloatFormat.max_exp + 1)):
  roundDown x = Fp.finite FiniteFp.largestFiniteFloat := by
  unfold roundDown findPredecessor
  simp [ne_of_gt hn, hn]
  unfold findPredecessorPos
  -- Since x ≥ 2^(max_exp + 1), we're beyond the normal range
  have h_sub : ¬(x < (2 : R) ^ FloatFormat.min_exp) := by
    have h1 : (0 : R) < (2 : R) ^ FloatFormat.min_exp := zpow_pos (by norm_num) _
    have h2 : (2 : R) ^ FloatFormat.min_exp ≤ (2 : R) ^ (FloatFormat.max_exp + 1) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2)
      have := FloatFormat.exp_order_le
      have := FloatFormat.max_exp_pos
      have := FloatFormat.min_exp_nonpos
      omega
    linarith
  simp [h_sub]
  -- The second condition is also false since x ≥ 2^(max_exp + 1)
  have h_overflow : ¬(x < (2 : R) ^ (FloatFormat.max_exp + 1)) := by
    exact not_lt.mpr hs
  simp [h_overflow]

end RoundDown

-- Round toward positive infinity (ceiling)
section RoundUp

/-- Round toward positive infinity -/
def roundUp [FloatFormat] (x : R) : Fp :=
  findSuccessor x

/-- roundUp returns 0 when input is 0 -/
theorem roundUp_zero [FloatFormat] : roundUp (0 : R) = Fp.finite 0 := by
  unfold roundUp
  exact findSuccessor_zero

/-- roundUp never produces negative infinity -/
theorem roundUp_ne_neg_inf [FloatFormat] (x : R) : roundUp x ≠ Fp.infinite true := by
  unfold roundUp findSuccessor
  intro a
  split at a
  · -- Case: x = 0, returns Fp.finite 0 ≠ Fp.infinite true
    simp_all
  · split at a
    · -- Case: x ≠ 0 and x > 0, uses findSuccessorPos which never returns negative infinity
      have : findSuccessorPos x (by assumption) ≠ Fp.infinite true := findSuccessorPos_ne_neg_inf x (by assumption)
      contradiction
    · -- Case: x ≠ 0 and x ≤ 0, so x < 0 by trichotomy
      -- The result is match findPredecessorPos (-x) with | Fp.infinite b => Fp.infinite (!b) | ..
      -- For result to be Fp.infinite true, we need findPredecessorPos (-x) = Fp.infinite false
      -- But findPredecessorPos never returns Fp.infinite false
      have h_lt : x < 0 := by
        -- We have ¬x = 0 and ¬0 < x, so by trichotomy x < 0
        cases' lt_trichotomy x 0 with h h
        · exact h
        · cases' h with h h
          · simp_all
          · simp_all
      have h_neg_pos : 0 < -x := neg_pos.mpr h_lt
      have : findPredecessorPos (-x) h_neg_pos ≠ Fp.infinite false := findPredecessorPos_ne_inf (-x) h_neg_pos false
      -- Now split on the match expression
      generalize heq : findPredecessorPos (-x) h_neg_pos = result
      simp only [heq] at a
      cases result with
      | finite f => simp_all
      | infinite b =>
        simp_all only [Bool.not_eq_true]
        rw [← heq] at this
        simp_all
      | NaN => simp_all

theorem roundUp_lt_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundUp x = Fp.finite FiniteFp.smallestPosSubnormal := by
  unfold roundUp findSuccessor
  simp [ne_of_gt hn, hn]
  unfold findSuccessorPos
  -- We need to show x < 2^min_exp to enter the subnormal case
  -- smallestPosSubnormal = 2^(min_exp - prec + 1) < 2^min_exp
  have h_sub : x < (2 : R) ^ FloatFormat.min_exp := by
    exact lt_trans hs FiniteFp.smallestPosSubnormal_lt_minExp
  simp [h_sub]
  unfold roundSubnormalUp
  -- The ULP in subnormal range is 2^(min_exp - prec + 1) = smallestPosSubnormal
  -- So ⌈x / smallestPosSubnormal⌉ = 1 since 0 < x < smallestPosSubnormal
  have h_ceil : ⌈x / FiniteFp.smallestPosSubnormal.toVal⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · norm_num
      rw [div_pos_iff]
      left
      constructor
      · exact hn
      · rw [FiniteFp.smallestPosSubnormal_toVal]
        exact zpow_pos (by norm_num) _
    · norm_cast
      exact div_le_one_of_le₀ (le_of_lt hs) (by
        rw [FiniteFp.smallestPosSubnormal_toVal]
        exact le_of_lt (zpow_pos (by norm_num) _))
  rw [FiniteFp.smallestPosSubnormal_toVal] at h_ceil
  simp [h_ceil]
  -- Show k = 1 and 1 < 2^(prec-1), so go to else branch
  have h_k_lt : 1 < (2 : ℤ)^(FloatFormat.prec - 1) := by
    have := FloatFormat.prec_pred_pow_le
    linarith
  simp only [h_k_lt.not_ge] -- for some reason need the opposite to recognize it
  rw [dite_false, FiniteFp.smallestPosSubnormal]


-- Helper lemmas for roundUp_ge proof

-- Fundamental ceiling property for subnormal range
lemma roundSubnormalUp_ge [FloatFormat] (x : R) (hsr : isSubnormalRange x) (f : FiniteFp)
  (h : roundSubnormalUp x hsr = Fp.finite f) : x ≤ f.toVal := by
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
    simp
    -- Goal: x ≤ k.natAbs * 2^(min_exp - prec + 1)
    -- We know k = ⌈x / 2^(min_exp - prec + 1)⌉ and k > 0 in subnormal range
    -- So k.natAbs = k and k ≥ x / 2^(min_exp - prec + 1)
    -- Therefore k * 2^(min_exp - prec + 1) ≥ x
    have k_pos : 0 < k := by
      unfold k
      apply Int.ceil_pos.mpr
      apply div_pos hsr.left
      apply zpow_pos (by norm_num)
    have h_natAbs : (k.natAbs : R) = (k : R) := by
      have : |k| = k := abs_of_pos k_pos
      convert this.symm
      constructor
      · intro h1
        rw [abs_of_pos k_pos]
      · intro h1
        rw [Int.cast_natAbs]
        rw [abs_of_pos k_pos]
    rw [h_natAbs]
    have h_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
      apply zpow_pos (by norm_num)
    -- x / 2^(min_exp - prec + 1) ≤ k
    -- So x ≤ k * 2^(min_exp - prec + 1)
    calc x = x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) *
              (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by {
        rw [div_mul_cancel₀ _ (ne_of_gt h_pos)]
      }
      _ ≤ (k : R) * (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
        apply mul_le_mul_of_nonneg_right
        · unfold k
          exact Int.le_ceil _
        · exact le_of_lt h_pos

/-- rounding a normal up is bounded above by the float's representation -/
lemma roundNormalUp_ge [FloatFormat] (x : R) (hnr : isNormalRange x) (f : FiniteFp)
  (h : roundNormalUp x hnr = Fp.finite f) : x ≤ f.toVal := by
  unfold roundNormalUp at h
  let e := findExponentDown x
  let binade_base := (2 : R) ^ e
  let scaled := x / binade_base
  let m_scaled := scaled * (2 : R) ^ (FloatFormat.prec - 1)
  let m := ⌈m_scaled⌉

  have m_pos : 0 < m := by
    apply Int.ceil_pos.mpr
    apply mul_pos
    apply div_pos (isNormalRange_pos x hnr)
    apply zpow_pos (by norm_num)
    apply pow_pos (by norm_num : (0 : R) < 2)

  by_cases hm : 2^FloatFormat.prec ≤ m
  · -- Case: overflow within binade
    unfold m m_scaled scaled binade_base e at hm
    by_cases he : e + 1 > FloatFormat.max_exp
    · -- Overflow to infinity case - contradiction since h says result is finite
      unfold e at he
      simp only [ge_iff_le, hm, he, ↓reduceDIte] at h
      -- This returns Fp.infinite false, but h says result is Fp.finite f
      exfalso
      cases h
    · -- Move to next exponent case
      unfold e at he
      simp only [ge_iff_le, hm, he, ↓reduceDIte, Fp.finite.injEq] at h
      rw [← h]
      unfold FiniteFp.toVal FiniteFp.sign'
      rw [FloatFormat.radix_val_eq_two]
      simp
      -- Goal: x ≤ 2^(prec-1) * 2^(e + 1 - prec + 1) = 2^(e + 1)
      rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
      ring_nf
      -- Goal is x ≤ 2 ^ (e + 1)
      -- Use that findExponentDown gives us e such that 2^e ≤ x < 2^(e+1) in normal range
      have hbound := findExponentDown_div_binade_normal hnr
      have : x < binade_base * 2 := by
        unfold binade_base
        have : binade_base * 2 = (2 : R) ^ (e + 1) := by
          rw [← zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]
        rw [this]
        -- hbound says x / 2^e < 2, so x < 2^(e+1)
        have h1 : x / (2 : R) ^ e < 2 := hbound.right
        rw [zpow_add_one₀, mul_comm]
        exact (div_lt_iff₀ (zpow_pos (by norm_num : (0 : R) < 2) e)).mp h1
        norm_num
      unfold binade_base e at this
      rw [zpow_one_add₀, mul_comm]
      linarith
      norm_num
  · -- Case: no overflow, m < 2^prec
    unfold m m_scaled scaled binade_base e at hm
    simp only [ge_iff_le, hm, ↓reduceDIte, Fp.finite.injEq] at h
    rw [← h]
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two]
    simp only [Bool.false_eq_true, ↓reduceIte, FloatFormat.pow_prec_sub_one_nat_int, one_mul,
      Int.cast_ofNat, ge_iff_le]
    -- Goal: x ≤ m.natAbs * 2^(e - prec + 1)
    -- First we need to show m > 0 and m.natAbs = m
    have h_natAbs := natAbs_cast_of_pos (R := R) m_pos
    unfold m m_scaled scaled binade_base e at h_natAbs m_pos
    have m_pos' : 0 < x / (2 : R) ^ findExponentDown x * (2 : R) ^ (FloatFormat.prec - 1) := by
      apply Int.ceil_pos.mp
      trivial
    simp_all only [FloatFormat.pow_prec_sub_one_nat_int, Int.ceil_pos, ge_iff_le]

    -- Now x ≤ m * 2^(e - prec + 1)
    have h_pos : (0 : R) < (2 : R) ^ ((e : ℤ) - (FloatFormat.prec : ℤ) + 1) := by
      apply zpow_pos (by norm_num)
    -- Show x ≤ m * 2^(e - prec + 1)
    calc x = x / (2 : R) ^ e * (2 : R) ^ (FloatFormat.prec - 1) / (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e := by {
        rw [FloatFormat.pow_prec_sub_one_nat_int]
        rw [mul_div_cancel_right₀, div_mul_cancel₀]
        apply zpow_ne_zero _ (by norm_num)
        apply zpow_ne_zero _ (by norm_num)
      }
      _ ≤ (m : R) / (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e := by
        apply mul_le_mul_of_nonneg_right
        apply div_le_div_of_nonneg_right
        · unfold m
          exact Int.le_ceil _
        · apply pow_nonneg (by norm_num)
        · apply zpow_nonneg (by norm_num)
      _ = (m : R) * (2 : R) ^ (e - (FloatFormat.prec : ℤ) + 1) := by
        rw [div_mul_eq_mul_div]
        rw [mul_div_assoc]
        rw [FloatFormat.pow_prec_sub_one_nat_int]
        rw [← zpow_sub₀ (by norm_num)]
        ring_nf
    unfold m m_scaled scaled binade_base e
    simp only [FloatFormat.pow_prec_sub_one_nat_int, le_refl]

-- findSuccessorPos preserves the ceiling property
lemma findSuccessorPos_ge [FloatFormat] (x : R) (hpos : 0 < x) (f : FiniteFp)
  (h : findSuccessorPos x hpos = Fp.finite f) : x ≤ f.toVal := by
  unfold findSuccessorPos at h
  split_ifs at h with h_sub h_normal
  · -- Subnormal case
    exact roundSubnormalUp_ge x ⟨hpos, h_sub⟩ f h
  · -- Normal case
    exact roundNormalUp_ge x ⟨le_of_not_gt h_sub, h_normal⟩ f h
  -- Overflow case handled automatically

-- findPredecessorPos preserves the floor property
lemma findPredecessorPos_le [FloatFormat] (x : R) (hpos : 0 < x) (f : FiniteFp)
  (h : findPredecessorPos x hpos = Fp.finite f) : f.toVal ≤ x := by
  sorry -- Floor property for predecessor - to be completed

-- Main theorem: roundUp returns a value ≥ input (fundamental property of rounding up)
theorem roundUp_ge [FloatFormat] (x : R) (f : FiniteFp)
  (h : roundUp x = Fp.finite f) : x ≤ f.toVal := by
  unfold roundUp findSuccessor at h
  split_ifs at h with h_zero h_pos
  · -- Case: x = 0
    simp at h
    rw [h.symm, h_zero, FiniteFp.toVal_zero]
  · -- Case: x > 0
    exact findSuccessorPos_ge x h_pos f h
  · -- Case: x < 0
    -- Use symmetry: findSuccessor x = -findPredecessor (-x)
    have h_neg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h_pos) h_zero)
    unfold findPredecessorPos at h
    norm_num at h
    split at h
    <;> rename_i heq
    <;> split at heq
    · rename_i f' h1
      have hf : f = -f' := by simp_all only [Left.neg_pos_iff, Fp.finite.injEq]
      have hf' : f' = -f := by simp [hf]
      rw [hf'] at heq
      have a := roundSubnormalDown_le (-x) (by trivial) (-f) heq
      rw [FiniteFp.toVal_neg_eq_neg] at a
      linarith
    · split at heq
      · injection h with h1
        rw [neg_eq_iff_eq_neg.mp h1] at heq
        sorry
      · injection heq with h₁
        injection h with h₂
        rw [neg_eq_iff_eq_neg.mp h₂] at h₁
        rw [← neg_eq_iff_eq_neg.mpr h₁]
        rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.largestFiniteFloat_toVal]
        simp_all only [not_lt, Left.neg_pos_iff, ge_iff_le]
        have ha : x ≤ -2^(FloatFormat.max_exp + 1) := by linarith
        apply le_trans
        exact ha
        norm_num
        rw [zpow_add_one₀ (by norm_num)]
        rw [zpow_add_one₀ (by norm_num)]
        -- apply (mul_le_mul_iff_left ?_).mp
        apply mul_le_mul_of_nonneg_left
        simp only [zpow_neg, zpow_natCast, tsub_le_iff_right, le_add_iff_nonneg_right, inv_pos,
          Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_left, Nat.ofNat_nonneg]
        apply zpow_nonneg (by norm_num)
    · rename_i b h1
      have := roundSubnormalDown_ne_infinite (-x) (by trivial) b
      contradiction
    · trivial
    · trivial
    · trivial

-- roundUp doesn't return NaN for positive finite inputs
theorem roundUp_pos_not_nan [FloatFormat] (x : R) (xpos : 0 < x) :
  roundUp x ≠ Fp.NaN := by
  unfold roundUp findSuccessor
  intro a
  simp [ne_of_gt xpos] at a
  unfold findSuccessorPos at a
  split_ifs at a with h1 h2
  · -- Subnormal case: roundSubnormalUp
    have h : isSubnormalRange x := ⟨xpos, h1⟩
    have := roundSubnormalUp_ne_nan x h
    contradiction
  · -- Normal case: roundNormalUp
    norm_num at h1
    have h : isNormalRange x := ⟨h1, h2⟩
    have := roundNormalUp_ne_nan x h
    contradiction
  --· Overflow case: discharged automatically

theorem roundUp_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x > FiniteFp.largestFiniteFloat.toVal):
  roundUp x = Fp.infinite false := by
  -- Proof by contradiction: assume roundUp returns something other than positive infinity
  match h : roundUp x with
  | Fp.finite f =>
    -- If it returns a finite float f, then f.toVal ≥ x (property of rounding up)
    -- But f.toVal ≤ largestFiniteFloat (all finite floats are bounded)
    -- This gives largestFiniteFloat < x ≤ f.toVal ≤ largestFiniteFloat, contradiction!
    have h1 : (f.toVal : R) ≤ (FiniteFp.largestFiniteFloat.toVal : R) := FiniteFp.finite_le_largestFiniteFloat f
    have h2 : x ≤ (f.toVal : R) := roundUp_ge x f h
    have : (FiniteFp.largestFiniteFloat.toVal : R) < (FiniteFp.largestFiniteFloat.toVal : R) := by
      calc (FiniteFp.largestFiniteFloat.toVal : R) < x := hs
           _ ≤ (f.toVal : R) := h2
           _ ≤ (FiniteFp.largestFiniteFloat.toVal : R) := h1
    exact absurd this (lt_irrefl _)
  | Fp.infinite b =>
    -- Need to show b = false (positive infinity)
    by_cases hb : b
    · -- If b = true (negative infinity), contradiction since x > 0
      have : roundUp x ≠ Fp.infinite true := roundUp_ne_neg_inf x
      rw [h] at this
      simp [hb] at this
    · -- If b = false, we're done
      simp [hb]
  | Fp.NaN =>
    -- roundUp of valid positive input should not return NaN
    have : roundUp x ≠ Fp.NaN := roundUp_pos_not_nan x hn
    exact absurd h this

end RoundUp

-- Round toward zero (truncation)
section RoundTowardZero

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

/-- roundTowardZero never increases magnitude -/
theorem roundTowardZero_magnitude_le [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → |f.toVal| ≤ |x| := by
  intro h
  unfold roundTowardZero at h
  split_ifs at h with h_zero h_pos
  · -- Case: x = 0
    simp at h
    rw [← h]
    simp [h_zero, FiniteFp.toVal_zero]
  · -- Case: x > 0, use roundDown
    have h_eq : roundDown x = Fp.finite f := h
    -- roundDown gives us the largest float ≤ x, so f.toVal ≤ x
    -- Since x > 0 and f.toVal ≤ x, we have |f.toVal| ≤ |x|
    sorry -- Need roundDown_le property
  · -- Case: x < 0, use roundUp
    have h_eq : roundUp x = Fp.finite f := h
    -- roundUp gives us the smallest float ≥ x, so x ≤ f.toVal
    -- Since x < 0 and x ≤ f.toVal, we need to show |f.toVal| ≤ |x|
    -- This requires analyzing if f.toVal is negative or positive
    sorry -- Need roundUp_ge and analysis of sign

/-- roundTowardZero preserves sign for non-zero finite results -/
theorem roundTowardZero_sign_preservation [FloatFormat] (x : R) (f : FiniteFp) :
  roundTowardZero x = Fp.finite f → f.toVal ≠ (0 : R) → (x > 0 ↔ f.toVal > (0 : R)) := by
  sorry

end RoundTowardZero

-- Round to nearest, ties to even (default IEEE 754 rounding)
section RoundNearestTiesToEven

/-- Round to nearest, ties to even -/
def roundNearestTiesToEven [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then Fp.finite 0
  else if |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp then Fp.infinite (x < 0)
  else
    let pred := findPredecessor x
    let succ := findSuccessor x
    match pred, succ with
    | Fp.finite p, Fp.finite s =>
      let midpoint := (p.toVal + s.toVal) / 2
      if x < midpoint then pred
      else if x > midpoint then succ
      else  -- x is exactly at midpoint, round to even
        if isEvenSignificand p then pred else succ
    | _, _ => Fp.NaN  -- Should not happen in normal range

/-- roundNearestTiesToEven returns 0 when input is 0 -/
theorem roundNearestTiesToEven_zero [FloatFormat] : roundNearestTiesToEven (0 : R) = Fp.finite 0 := by
  unfold roundNearestTiesToEven
  simp

theorem rnEven_le_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesToEven x = Fp.finite 0 := by
  unfold roundNearestTiesToEven
  -- Check the conditions
  simp [ne_of_gt hn]
  -- Need to show |x| < smallestPosSubnormal / 2
  have h_abs : |x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hn]
    exact hs
  simp [h_abs]

-- TODO: negative values?
-- TODO: better name.
-- Closely related to largest positive normal number.
theorem rnEven_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesToEven x = Fp.infinite false := by
  sorry

end RoundNearestTiesToEven

-- Round to nearest, ties away from zero
section RoundNearestTiesAwayFromZero

/-- Round to nearest, ties away from zero -/
def roundNearestTiesAwayFromZero [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then Fp.finite 0
  else if |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp then Fp.infinite (x < 0)
  else
    let pred := findPredecessor x
    let succ := findSuccessor x
    match pred, succ with
    | Fp.finite p, Fp.finite s =>
      let midpoint := (p.toVal + s.toVal) / 2
      if x < midpoint then pred
      else if x > midpoint then succ
      else  -- x is exactly at midpoint, round away from zero
        if x > 0 then succ else pred
    | _, _ => Fp.NaN  -- Should not happen in normal range

/-- roundNearestTiesAwayFromZero returns 0 when input is 0 -/
theorem roundNearestTiesAwayFromZero_zero [FloatFormat] : roundNearestTiesAwayFromZero (0 : R) = Fp.finite 0 := by
  unfold roundNearestTiesAwayFromZero
  simp

theorem rnAway_lt_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesAwayFromZero x = Fp.finite 0 := by
  unfold roundNearestTiesAwayFromZero
  -- Check the conditions - same logic as rnEven
  simp [ne_of_gt hn]
  have h_abs : |x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hn]
    exact hs
  simp [h_abs]

theorem rnAway_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesAwayFromZero x = Fp.infinite false := by
  sorry

end RoundNearestTiesAwayFromZero


-- Rounding mode enumeration and general interface
section RoundingModes

inductive RoundingMode
  | Down
  | Up
  | TowardZero
  | NearestTiesToEven
  | NearestTiesAwayFromZero

def RoundingMode.toRoundingFunction [FloatFormat] (mode : RoundingMode) : R → Fp :=
  match mode with
  | .Down => roundDown
  | .Up => roundUp
  | .TowardZero => roundTowardZero
  | .NearestTiesToEven => roundNearestTiesToEven
  | .NearestTiesAwayFromZero => roundNearestTiesAwayFromZero

def RoundingMode.round [FloatFormat] (mode : RoundingMode) (x : R) : Fp :=
  mode.toRoundingFunction x

/-- General property: all rounding modes preserve exact zero -/
theorem all_rounding_modes_preserve_zero [FloatFormat] (mode : RoundingMode) :
  mode.round (0 : R) = Fp.finite 0 := by
  cases mode with
  | Down => exact roundDown_zero
  | Up => exact roundUp_zero
  | TowardZero => exact roundTowardZero_zero
  | NearestTiesToEven => exact roundNearestTiesToEven_zero
  | NearestTiesAwayFromZero => exact roundNearestTiesAwayFromZero_zero

/-- All rounding functions are well-defined (always return a valid Fp) -/
theorem rounding_mode_total [FloatFormat] (mode : RoundingMode) (x : R) :
  ∃ y : Fp, mode.round x = y := ⟨mode.round x, rfl⟩

-- TODO: Add monotonicity properties once we define an ordering on Fp
-- This would be useful for proving that rounding preserves order relations

end RoundingModes

end Rounding
