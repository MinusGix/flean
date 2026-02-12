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
  unfold smallestPosSubnormal
  exact isSubnormal.min_exp_one

theorem smallestPosSubnormal_lt_minExp {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
  smallestPosSubnormal.toVal < (2 : R) ^ FloatFormat.min_exp := by
  rw [smallestPosSubnormal_toVal]
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : R) < 2)
  have := FloatFormat.valid_prec
  omega

theorem smallestPosSubnormal_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : (0 : R) < smallestPosSubnormal.toVal := by
  rw [smallestPosSubnormal_toVal]
  linearize

/-- Half of smallestPosSubnormal is strictly less than 2^min_exp.
    This is useful for showing underflow threshold < overflow threshold. -/
theorem smallestPosSubnormal_half_lt_zpow_min_exp {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    (smallestPosSubnormal.toVal : R) / 2 < (2 : R) ^ FloatFormat.min_exp := by
  rw [smallestPosSubnormal_toVal]
  have hpos : (0 : R) < 2 ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by positivity
  have hexp_le : FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1 ≤ FloatFormat.min_exp := by
    have := FloatFormat.valid_prec; omega
  have hstep1 : (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) / 2 < 2 ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by
    linarith
  have hstep2 : (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) ≤ 2 ^ FloatFormat.min_exp :=
    two_zpow_mono hexp_le
  linarith

def smallestPosNormal : FiniteFp := ⟨
  false,
  FloatFormat.min_exp,
  2^(FloatFormat.prec - 1).toNat,
  IsValidFiniteVal.smallestPosNormal
 ⟩

theorem smallestPosNormal_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : smallestPosNormal.toVal = (2 : R)^(FloatFormat.min_exp) := by
  unfold smallestPosNormal FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  norm_num
  -- Convert nat pow to zpow
  rw [← zpow_natCast (G := R) 2 (FloatFormat.prec.toNat - 1)]
  rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
  congr 1
  have := FloatFormat.valid_prec
  omega

theorem smallestPosNormal_isNormal : smallestPosNormal.isNormal :=
  isNormal.sig_msb

theorem smallestPosNormal_toVal_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : (0 : R) < smallestPosNormal.toVal := by
  rw [smallestPosNormal_toVal]
  linearize

def largestFiniteFloat : FiniteFp := ⟨
  false,
  FloatFormat.max_exp,
  2^FloatFormat.prec.toNat - 1,
  IsValidFiniteVal.largestFiniteFloat
⟩

theorem largestFiniteFloat_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : largestFiniteFloat.toVal = (2 : R)^(FloatFormat.max_exp) * ((2 : R) - (2 : R)^(-(FloatFormat.prec : ℤ) + 1)) := by
  unfold largestFiniteFloat FiniteFp.toVal FiniteFp.sign'
  have := FloatFormat.valid_prec
  have h2ne : (2 : R) ≠ 0 := by norm_num
  rw [FloatFormat.radix_val_eq_two]
  norm_num
  rw [mul_comm, mul_sub, mul_one]
  -- Convert nat pow to zpow
  rw [← zpow_natCast (G := R) 2 FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]
  rw [sub_add, zpow_sub₀ h2ne, zpow_sub₀ h2ne]

  ring_nf
  rw [mul_comm _ 2, mul_assoc]
  rw [mul_inv_cancel₀ (zpow_ne_zero _ h2ne), mul_one]
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
  rw [← zpow_add₀ h2ne, ← sub_eq_add_neg]
  rw [← mul_sub]

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
  have h_m_bound : f.m < 2^FloatFormat.prec.toNat := h_valid.2.2.1

  by_cases h_e : f.e = FloatFormat.max_exp
  · -- Case: f.e = max_exp, need f.m ≤ 2^prec - 1
    rw [h_e]
    apply mul_le_mul_of_nonneg_right
    · -- f.m ≤ 2^prec - 1, we have f.m < 2^prec.toNat
      have h_nat_le : f.m ≤ 2^FloatFormat.prec.toNat - 1 := Nat.le_sub_one_of_lt h_m_bound
      -- Goal: ↑f.m ≤ (2 : R) ^ prec.toNat - 1 (already has toNat from the definition)
      have h4 := FloatFormat.nat_four_le_two_pow_prec
      have h_sub : (2 : R) ^ FloatFormat.prec.toNat - 1 = ((2 ^ FloatFormat.prec.toNat - 1 : ℕ) : R) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ FloatFormat.prec.toNat)]
        simp
      rw [h_sub]
      exact_mod_cast h_nat_le
    · exact zpow_nonneg (by norm_num) _
  · -- Case: f.e < max_exp
    have h_lt : f.e < FloatFormat.max_exp := lt_of_le_of_ne h_e_bound h_e
    have h_pow_le : ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R) ≤
                     ((2 : R) ^ (FloatFormat.max_exp - (FloatFormat.prec : ℤ) + 1) : R) := by
      apply two_zpow_mono
      omega
    have h_m_le : (f.m : R) ≤ (2 : R) ^ FloatFormat.prec - 1 := by
      have h_nat_le : f.m ≤ 2^FloatFormat.prec.toNat - 1 := Nat.le_sub_one_of_lt h_m_bound
      have h_pow_eq : (2 : R) ^ FloatFormat.prec = (2 : R) ^ FloatFormat.prec.toNat := by
        rw [← zpow_natCast]; congr 1; exact FloatFormat.prec_toNat_eq.symm
      rw [h_pow_eq]
      have h4 := FloatFormat.nat_four_le_two_pow_prec
      have h_sub : (2 : R) ^ FloatFormat.prec.toNat - 1 = ((2 ^ FloatFormat.prec.toNat - 1 : ℕ) : R) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ FloatFormat.prec.toNat)]
        simp
      rw [h_sub]
      exact_mod_cast h_nat_le

    rw [Int.cast_two]
    -- Connect 2^prec (zpow) to 2^prec.toNat (pow)
    have h_prec_eq : (2 : R) ^ FloatFormat.prec = (2 : R) ^ FloatFormat.prec.toNat := by
      rw [← zpow_natCast]; congr 1; exact FloatFormat.prec_toNat_eq.symm
    calc (f.m : R) * ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R)
       ≤ ((2 : R) ^ FloatFormat.prec - 1) * ((2 : R) ^ (f.e - (FloatFormat.prec : ℤ) + 1) : R) := by {
         apply mul_le_mul_of_nonneg_right h_m_le
         exact zpow_nonneg (by norm_num) _ }
     _ ≤ ((2 : R) ^ FloatFormat.prec - 1) * ((2 : R) ^ (FloatFormat.max_exp - (FloatFormat.prec : ℤ) + 1) : R) := by {
         apply mul_le_mul_of_nonneg_left h_pow_le
         simp only [sub_nonneg]
         apply le_trans (by norm_num : (1 : R) ≤ 4)
         have h_prec_zpow : (2 : R) ^ FloatFormat.prec = (2 : R) ^ FloatFormat.prec.toNat := by
           rw [← zpow_natCast]; congr 1; exact FloatFormat.prec_toNat_eq.symm
         rw [h_prec_zpow]
         exact FloatFormat.prec_pow_le (R := R) }
     _ = ((2 : R) ^ FloatFormat.prec.toNat - 1) * ((2 : R) ^ (FloatFormat.max_exp - (FloatFormat.prec : ℤ) + 1) : R) := by {
         rw [h_prec_eq] }

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
  let m := List.range (2^FloatFormat.prec.toNat - 2^(FloatFormat.prec-1).toNat) |> List.map (· + 2^(FloatFormat.prec-1).toNat)
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
  have har' : a + 2 ^ (FloatFormat.prec - 1).toNat < 2 ^ FloatFormat.prec.toNat := by
    rw [← add_lt_add_iff_right (a := 2 ^ (FloatFormat.prec - 1).toNat)] at har
    rw [Nat.sub_add_cancel] at har
    trivial
    have := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
    omega
  rw [← hmeq]
  split_ands
  · have := FloatFormat.one_le_prec_sub_one_toNat; omega
  · exact har'

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
    have := FloatFormat.exp_order
    omega
  · simp_all
  · left
    trivial

def normalFiniteEmv : List { (e, m) : ℤ × ℕ | IsValidFiniteVal e m } :=
  normalFiniteEm.attachWith (λ em => IsValidFiniteVal em.1 em.2) (λ em => normalFiniteEm_isValidFiniteVal em.1 em.2)

def subnormalFiniteEm : List (ℤ × ℕ) :=
  List.range (2^(FloatFormat.prec-1).toNat) |> List.map (FloatFormat.min_exp, ·)

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
  · have := FloatFormat.exp_order; omega
  · have := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec; omega
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
      · -- Normalize (prec - 1).toNat to prec.toNat - 1 throughout
        have hpow_eq : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
          rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
        -- h1 : isNormal m means 2^(prec-1).toNat ≤ m < 2^prec.toNat
        unfold _root_.isNormal at h1
        rw [hpow_eq] at h1
        use m - 2^(FloatFormat.prec.toNat - 1)
        norm_num
        have hpow_lt := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
        have hpow_ge := FloatFormat.nat_two_le_two_pow_prec_sub_one
        -- Help omega understand 2^prec = 2 * 2^(prec-1)
        have hpow_double : (2 : ℕ) ^ FloatFormat.prec.toNat = 2 * 2 ^ (FloatFormat.prec.toNat - 1) := by
          have hp := FloatFormat.prec_toNat_pos
          conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
        obtain ⟨h1_lb, h1_ub⟩ := h1
        omega
    · right -- Subnormal
      unfold subnormalFiniteEm
      rw [List.mem_map]
      norm_num
      -- Normalize (prec - 1).toNat to prec.toNat - 1
      have hpow_eq : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
        rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
      unfold _root_.isSubnormal at h1
      rw [hpow_eq] at h1
      -- Help omega with power bound
      have hpow_ge := FloatFormat.nat_two_le_two_pow_prec_sub_one
      simp only [FloatFormat.prec_sub_one_toNat_eq_toNat_sub] at hpow_ge
      split_ands
      · have := FloatFormat.exp_order; omega
      · omega
  if s = false then
    grind
  else
    grind

theorem allFiniteFps_no_dup : List.Nodup allFiniteFps := by
  unfold allFiniteFps
  rw [List.nodup_map_iff]
  · apply List.nodup_product
    trivial
    unfold allFiniteEmv
    rw [List.nodup_attachWith]
    unfold allFiniteEm
    rw [List.nodup_append]
    split_ands
    · unfold normalFiniteEm
      extract_lets el ml
      apply List.nodup_product
      · unfold el
        rw [List.nodup_map_iff]
        · norm_num
          rw [List.nodup_flatMap]
          split_ands
          · simp
          · unfold List.Disjoint Function.onFun
            norm_num
            apply List.pairwise_disjoint_range
        · intro a b h
          grind
      · unfold ml
        rw [List.nodup_map_iff]
        · apply List.nodup_range
        · intro a b h
          grind
    · unfold subnormalFiniteEm
      rw [List.nodup_map_iff]
      · apply List.nodup_range
      · intro a b h
        grind
    · unfold normalFiniteEm subnormalFiniteEm
      intro ⟨e1, m1⟩ hnorm ⟨e2, m2⟩ hsub hne
      simp only [List.mem_product, List.mem_map, List.mem_range] at hnorm hsub
      obtain ⟨_, ⟨k, hk, hm⟩⟩ := hnorm
      obtain ⟨a, ha, heq⟩ := hsub
      simp only [Prod.mk.injEq] at hne heq
      obtain ⟨_, rfl⟩ := heq
      omega
  · intro a b h
    grind


instance : Fintype FiniteFp := {
  elems := allFiniteFps.toFinset
  complete := by
    intro f
    apply List.mem_toFinset.mpr
    apply in_allFiniteFps
}
instance : Finite (FiniteFp) := inferInstance

theorem univ_def : Finset.univ = allFiniteFps.toFinset := by rfl

-- TODO: Define individual sizes for normal/subnormal
theorem card_def : Fintype.card FiniteFp = 2 * ((FloatFormat.max_exp - FloatFormat.min_exp + 1).toNat * (2^(FloatFormat.prec - 1).toNat) + 2^(FloatFormat.prec - 1).toNat) := by
  unfold Fintype.card
  rw [univ_def]
  rw [List.toFinset_card_of_nodup allFiniteFps_no_dup]
  unfold allFiniteFps
  rw [List.length_map, List.length_product, List.length_cons, List.length_cons, List.length_nil]
  unfold allFiniteEmv allFiniteEm normalFiniteEm subnormalFiniteEm
  rw [List.length_attachWith, List.length_append]
  extract_lets el ml
  rw [List.length_product, List.length_map]
  norm_num
  unfold ml
  rw [List.length_map, List.length_range]
  -- natAbs = toNat for nonnegative integers
  have hnatabs_eq : (FloatFormat.max_exp - FloatFormat.min_exp + 1).natAbs =
      (FloatFormat.max_exp - FloatFormat.min_exp + 1).toNat := by
    have hn : 0 ≤ FloatFormat.max_exp - FloatFormat.min_exp + 1 := by
      have := FloatFormat.exp_order; omega
    apply Int.ofNat_injective
    calc (↑(FloatFormat.max_exp - FloatFormat.min_exp + 1).natAbs : ℤ)
        = FloatFormat.max_exp - FloatFormat.min_exp + 1 := (Int.eq_natAbs_of_nonneg hn).symm
      _ = ↑(FloatFormat.max_exp - FloatFormat.min_exp + 1).toNat := (Int.toNat_of_nonneg hn).symm
  -- Normalize (prec - 1).toNat to prec.toNat - 1
  have hpow_eq : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
  rw [hnatabs_eq, hpow_eq]
  -- Goal is now in ℕ: n * (2^p - 2^(p-1)) = n * 2^(p-1)
  -- Key: 2^p - 2^(p-1) = 2^(p-1) when p ≥ 1
  have hpow_sub : (2 : ℕ) ^ FloatFormat.prec.toNat - 2 ^ (FloatFormat.prec.toNat - 1) =
      2 ^ (FloatFormat.prec.toNat - 1) := by
    have hp := FloatFormat.prec_toNat_pos
    have : (2 : ℕ) ^ FloatFormat.prec.toNat = 2 * 2 ^ (FloatFormat.prec.toNat - 1) := by
      conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    omega
  rw [hpow_sub]


end Finiteness

end FiniteFp
