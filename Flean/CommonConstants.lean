import Flean.Defs
import Flean.ToVal

namespace FiniteFp

variable [FloatFormat]

def smallestPosSubnormal : FiniteFp := ⟨
  false,
  FloatFormat.min_exp,
  1,
  IsValidFiniteVal.smallestPosSubnormal
⟩

theorem smallestPosSubnormal_toVal {R : Type*} [Field R] : smallestPosSubnormal.toVal = (2 : R)^(FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
  unfold smallestPosSubnormal toVal sign'
  rw [FloatFormat.radix_val_eq_two]
  norm_num

theorem smallestPosSubnormal_isSubnormal : smallestPosSubnormal.isSubnormal := by
  have := FloatFormat.prec_pred_pow_le (R := ℕ)
  apply And.intro
  · rfl
  · unfold smallestPosSubnormal
    norm_num
    omega

theorem smallestPosSubnormal_lt_minExp {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
  smallestPosSubnormal.toVal < (2 : R) ^ FloatFormat.min_exp := by
  rw [smallestPosSubnormal_toVal]
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : R) < 2)
  have := FloatFormat.valid_prec
  omega

theorem smallestPosSubnormal_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : (0 : R) < smallestPosSubnormal.toVal := by
  rw [smallestPosSubnormal_toVal]
  linearize

def smallestPosNormal : FiniteFp := ⟨
  false,
  FloatFormat.min_exp,
  2^(FloatFormat.prec - 1),
  IsValidFiniteVal.smallestPosNormal
 ⟩

theorem smallestPosNormal_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : smallestPosNormal.toVal = (2 : R)^(FloatFormat.min_exp) := by
  unfold smallestPosNormal FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  norm_num
  rw [← zpow_add₀]
  simp only [sub_add_add_cancel, add_sub_cancel]
  norm_num

theorem smallestPosNormal_isNormal : smallestPosNormal.isNormal := by
  have := FloatFormat.valid_prec
  apply And.intro
  · apply pow_le_pow_right₀ (by norm_num) (by omega)
  · apply pow_lt_pow_right₀ (by norm_num) (by omega)

theorem smallestPosNormal_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : (0 : R) < smallestPosNormal.toVal := by
  rw [smallestPosNormal_toVal]
  linearize

def largestFiniteFloat : FiniteFp := ⟨
  false,
  FloatFormat.max_exp,
  2^(FloatFormat.prec) - 1,
  IsValidFiniteVal.largestFiniteFloat
⟩

theorem largestFiniteFloat_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : largestFiniteFloat.toVal = (2 : R)^(FloatFormat.max_exp) * ((2 : R) - (2 : R)^(-(FloatFormat.prec : ℤ) + 1)) := by
  unfold largestFiniteFloat FiniteFp.toVal FiniteFp.sign'
  have := FloatFormat.valid_prec
  rw [FloatFormat.radix_val_eq_two]
  norm_num
  rw [mul_comm, mul_sub, mul_one]
  rw [FloatFormat.pow_prec_nat_int]
  rw [sub_add, zpow_sub₀, zpow_sub₀]

  ring_nf
  rw [mul_comm _ 2, mul_assoc]
  rw [mul_inv_cancel₀, mul_one]
  have : (2 : R) ^ FloatFormat.max_exp * (2 ^ (FloatFormat.prec : ℤ))⁻¹ = 2 ^ FloatFormat.max_exp / (2 ^ (FloatFormat.prec : ℤ)) := by
    field_simp
  rw [this]
  rw [mul_comm _ 2, ← mul_sub]
  have : (2 : R) ^ FloatFormat.max_exp - (2 : R) ^ FloatFormat.max_exp / (2 : R) ^ (FloatFormat.prec : ℤ) = 2 ^ FloatFormat.max_exp * (1 - (2 ^ (FloatFormat.prec : ℤ))⁻¹) := by
    rw [division_def]
    have : ∀ (x y : R), x - x * y = x * (1 - y) := by
      intro x y
      ring_nf
    rw [this]
  rw [this]
  rw [← inv_zpow, inv_zpow']
  rw [← mul_assoc]
  rw [mul_comm 2 _, mul_assoc, mul_sub, mul_one]
  rw [show (2 : R) * (2 : R) ^ (-(FloatFormat.prec : ℤ)) = (2 : R)^(1 : ℤ) * (2 : R) ^ (-(FloatFormat.prec : ℤ)) by ring]
  rw [← zpow_add₀, ← sub_eq_add_neg]
  rw [← mul_sub]
  all_goals norm_num

theorem largestFiniteFloat_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : largestFiniteFloat.toVal > (0 : R) := by
  rw [largestFiniteFloat_toVal]
  have a1 := FloatFormat.max_exp_pos
  have a2 := FloatFormat.valid_prec
  have a3 := FloatFormat.prec_pred_pow_le (R := ℕ)
  have a4 := FloatFormat.exp_order_le
  have a5 := FloatFormat.min_exp_nonpos
  apply mul_pos
  · apply zpow_pos (by norm_num)
  · norm_num
    apply lt_trans
    apply zpow_lt_one_of_neg₀ (by norm_num) (by linarith)
    norm_num

theorem largestFiniteFloat_lt_maxExp_succ {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
  largestFiniteFloat.toVal < (2 : R) ^ (FloatFormat.max_exp + 1) := by
  rw [largestFiniteFloat_toVal]
  -- largestFiniteFloat = 2^max_exp * (2 - 2^(-prec+1))
  -- We need to show: 2^max_exp * (2 - 2^(-prec+1)) < 2^(max_exp + 1) = 2 * 2^max_exp
  -- This simplifies to: 2 - 2^(-prec+1) < 2
  -- Which is equivalent to: 0 < 2^(-prec+1)
  have h_pos : (0 : R) < (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := by
    apply zpow_pos (by norm_num)
  have h_lt : (2 : R) - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) < 2 := by
    linarith
  calc (2 : R) ^ FloatFormat.max_exp * ((2 : R) - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1))
    < (2 : R) ^ FloatFormat.max_exp * 2 := by {
      apply mul_lt_mul_of_pos_left h_lt
      apply zpow_pos (by norm_num) }
  _ = 2 * (2 : R) ^ FloatFormat.max_exp := by ring
  _ = (2 : R) ^ (FloatFormat.max_exp + 1) := by {
      rw [← zpow_one_add₀ (by norm_num : (2 : R) ≠ 0)]
      ring_nf }


-- TODO: prove that the smallest positive normal, smallest positive subnormal, and largest finite float are all truely their namesakes

-- Helper lemmas for the main theorem

theorem finite_neg_le_largest {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (f : FiniteFp) (h : f.s = true) : (f.toVal : R) ≤ (largestFiniteFloat.toVal : R) := by
  -- Negative float ≤ 0 ≤ positive largestFiniteFloat
  have h_neg : (f.toVal : R) ≤ 0 := by
    unfold toVal sign'
    simp [h, FloatFormat.radix_val_eq_two]
    apply mul_nonneg
    · apply Nat.cast_nonneg
    · apply zpow_nonneg (by norm_num : (0 : R) ≤ 2)
  exact le_trans h_neg (le_of_lt largestFiniteFloat_toVal_pos)

theorem finite_pos_le_largest {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (f : FiniteFp) (h_pos : f.s = false) :
  (f.toVal : R) ≤ (largestFiniteFloat.toVal : R) := by
  unfold toVal sign' largestFiniteFloat
  simp [h_pos]
  rw [FloatFormat.radix_val_eq_two]
  -- Goal: f.m * 2^(f.e - prec + 1) ≤ (2^prec - 1) * 2^(max_exp - prec + 1)

  have h_valid := f.valid
  unfold IsValidFiniteVal at h_valid
  have h_e_bound : f.e ≤ FloatFormat.max_exp := h_valid.2.1
  have h_m_bound : f.m < 2^FloatFormat.prec := h_valid.2.2.1

  by_cases h_e : f.e = FloatFormat.max_exp
  · -- Case: f.e = max_exp, need f.m ≤ 2^prec - 1
    rw [h_e]
    apply mul_le_mul_of_nonneg_right
    · -- f.m ≤ 2^prec - 1
      rw [FloatFormat.natCast_pow_prec_pred]
      norm_cast
      omega
    · exact zpow_nonneg (by norm_num) _
  · -- Case: f.e < max_exp
    have h_lt : f.e < FloatFormat.max_exp := lt_of_le_of_ne h_e_bound h_e
    have h_pow_le : ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R) ≤
                     ((2 : R) ^ (FloatFormat.max_exp - (FloatFormat.prec : ℤ) + 1) : R) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2)
      omega
    have h_m_le : (f.m : R) ≤ (2 : R) ^ FloatFormat.prec - 1 := by
      rw [FloatFormat.natCast_pow_prec_pred]
      norm_cast
      omega

    rw [Int.cast_two]
    calc (f.m : R) * ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R)
       ≤ ((2 : R) ^ FloatFormat.prec - 1) * ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R) := by {
         apply mul_le_mul_of_nonneg_right h_m_le
         exact zpow_nonneg (by norm_num) _ }
     _ ≤ ((2 : R) ^ FloatFormat.prec - 1) * ((2 : R) ^ (FloatFormat.max_exp - (FloatFormat.prec : ℤ) + 1) : R) := by {
         apply mul_le_mul_of_nonneg_left h_pow_le
         simp only [sub_nonneg]
         apply le_trans (by norm_num : (1 : R) ≤ 4)
         exact FloatFormat.prec_pow_le }

-- Main theorem: largestFiniteFloat is indeed the largest
theorem finite_le_largestFiniteFloat {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (f : FiniteFp) : (f.toVal : R) ≤ (largestFiniteFloat.toVal : R) := by
  by_cases h : f.s
  · -- Negative case
    exact finite_neg_le_largest f h
  · -- Positive case (works for both normal and subnormal)
    have h_pos : f.s = false := by simp at h; exact h
    exact finite_pos_le_largest f h_pos

section Finiteness

def normalFiniteEm : List (ℤ × ℕ) :=
  let e := List.range ((FloatFormat.max_exp - FloatFormat.min_exp + 1).natAbs) |> List.map (· + FloatFormat.min_exp)
  let m := List.range (2^FloatFormat.prec - 2^(FloatFormat.prec-1)) |> List.map (· + 2^(FloatFormat.prec-1))
  e ×ˢ m

theorem normalFiniteEm_isNormal : ∀ e m, (e, m) ∈ normalFiniteEm → _root_.isNormal m := by
  intro _ m hin
  unfold _root_.isNormal
  unfold normalFiniteEm at hin
  extract_lets le lm at hin
  rw [List.mem_product] at hin
  have hin := hin.right
  unfold lm at hin
  rw [List.mem_map] at hin
  rcases hin with ⟨a, har, hmeq⟩
  rw [List.mem_range] at har
  have har' : a + 2 ^ (FloatFormat.prec - 1) < 2 ^ FloatFormat.prec := by
    rw [← add_lt_add_iff_right (a := 2 ^ (FloatFormat.prec - 1))] at har
    rw [Nat.sub_add_cancel] at har
    trivial
    gcongr
    norm_num
    fomega
  rw [← hmeq]
  split_ands
  · linarith
  · trivial

theorem normalFiniteEm_isValidFiniteVal : ∀ e m, (e, m) ∈ normalFiniteEm → IsValidFiniteVal e m := by
  intro e m hin
  unfold IsValidFiniteVal
  have normal := normalFiniteEm_isNormal e m hin
  unfold normalFiniteEm at hin
  extract_lets le lm at hin
  rw [List.mem_product] at hin
  have hin := hin.right
  unfold lm at hin
  rw [List.mem_map] at hin
  rcases hin with ⟨a, har, hmeq⟩
  rw [List.mem_range] at har

  have hein := hin.left
  unfold le at hein
  rw [List.mem_map] at hein
  rcases hein with ⟨b, her, heqe⟩
  norm_num at her
  rcases her with ⟨c, hcr, heqc⟩
  split_ands
  · linarith
  · zify at hcr
    rw [abs_of_pos] at hcr
    linarith
    flinarith
  · simp_all
  · left
    trivial

def normalFiniteEmv : List { (e, m) : ℤ × ℕ | IsValidFiniteVal e m } :=
  normalFiniteEm.attachWith (λ em => IsValidFiniteVal em.1 em.2) (λ em => normalFiniteEm_isValidFiniteVal em.1 em.2)

def subnormalFiniteEm : List (ℤ × ℕ) :=
  List.range (2^(FloatFormat.prec-1)) |> List.map (FloatFormat.min_exp, ·)

theorem subnormalFiniteEm_isSubnormal : ∀ e m, (e, m) ∈ subnormalFiniteEm → _root_.isSubnormal e m := by
  intro e m hin
  unfold _root_.isSubnormal
  unfold subnormalFiniteEm at hin
  rw [List.mem_map] at hin
  rcases hin with ⟨a, har, hmeq⟩
  rw [List.mem_range] at har
  split_ands
  · grind
  · grind

theorem subnormalFiniteEm_isValidFiniteVal : ∀ e m, (e, m) ∈ subnormalFiniteEm → IsValidFiniteVal e m := by
  intro e m hin
  unfold IsValidFiniteVal
  have subnormal := subnormalFiniteEm_isSubnormal e m hin
  unfold subnormalFiniteEm at hin
  rw [List.mem_map] at hin
  rcases hin with ⟨a, har, hmeq⟩
  rw [List.mem_range] at har
  split_ands
  · grind
  · fomega
  · fomega
  · right
    trivial

def subnormalFiniteEmv : List { (e, m) : ℤ × ℕ | IsValidFiniteVal e m } :=
  subnormalFiniteEm.attachWith (λ em => IsValidFiniteVal em.1 em.2) (λ em => subnormalFiniteEm_isValidFiniteVal em.1 em.2)

def allFiniteEm : List (ℤ × ℕ) := normalFiniteEm ++ subnormalFiniteEm

theorem allFiniteEm_isValidFiniteVal : ∀ e m, (e, m) ∈ allFiniteEm → IsValidFiniteVal e m := by
  intro e m
  unfold allFiniteEm
  rw [List.mem_append]
  have := normalFiniteEm_isValidFiniteVal e m
  have := subnormalFiniteEm_isValidFiniteVal e m
  grind

def allFiniteEmv : List { (e, m) : ℤ × ℕ | IsValidFiniteVal e m } :=
  allFiniteEm.attachWith (λ em => IsValidFiniteVal em.1 em.2) (λ em => allFiniteEm_isValidFiniteVal em.1 em.2)

def allFiniteFps : List FiniteFp :=
  [true, false] ×ˢ allFiniteEmv |> List.map (fun (s, v) => ⟨s, v.val.1, v.val.2, v.property⟩)

theorem in_allFiniteFps (f : FiniteFp) : f ∈ allFiniteFps := by
  unfold allFiniteFps
  rw [List.mem_map]
  rcases f with ⟨s, e, m, vf⟩
  use (s, ⟨(e, m), vf⟩)
  simp
  have : ⟨(e, m), vf⟩ ∈ allFiniteEmv  := by
    unfold IsValidFiniteVal at *
    unfold allFiniteEmv allFiniteEm --normalFiniteEm subnormalFiniteEm
    rw [List.mem_attachWith, List.mem_append]
    have hvs := vf.right.right.right
    cases' hvs with h1 h1
    · left -- Normal
      unfold normalFiniteEm
      extract_lets el ml
      unfold el ml
      rw [List.mem_product, List.mem_map, List.mem_map]
      split_ands
      · use e - FloatFormat.min_exp
        norm_num
        use (e - FloatFormat.min_exp).natAbs
        split_ands
        · zify
          rw [abs_of_nonneg, abs_of_nonneg]
          <;> omega
        · zify
          rw [abs_of_nonneg]
          omega
      · use m - 2^(FloatFormat.prec - 1)
        norm_num
        omega
    · right -- Subnormal
      unfold subnormalFiniteEm
      rw [List.mem_map]
      norm_num
      unfold _root_.isSubnormal at h1
      split_ands
      · fomega
      · omega
  if s = false then
    grind
  else
    grind


instance : Fintype FiniteFp := {
  elems := allFiniteFps.toFinset
  complete := by
    intro f
    apply List.mem_toFinset.mpr
    apply in_allFiniteFps
}
instance : Finite (FiniteFp) := inferInstance


end Finiteness

end FiniteFp
