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

section Rounding
section RoundDown

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]


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
  · split_ifs at a with h2
    -- Case: x ≠ 0 and x ≤ 0, so x < 0 by trichotomy
    -- The result is match findSuccessorPos (-x) with | Fp.infinite b => Fp.infinite (!b) | ..
    -- For result to be Fp.infinite false, we need findSuccessorPos (-x) = Fp.infinite true
    -- But findSuccessorPos never returns Fp.infinite true
    have h_lt : x < 0 := by
      rename_i h1 h3
      apply lt_of_le_of_ne (not_lt.mp h2) h3
    have h_neg_pos : 0 < -x := neg_pos.mpr h_lt
    have : findSuccessorPos (-x) h_neg_pos ≠ Fp.infinite true := findSuccessorPos_ne_neg_inf (-x) h_neg_pos
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
  simp only [ne_of_gt hn, ↓reduceDIte, hn]
  unfold findPredecessorPos
  -- Since x < smallestPosSubnormal, x is in subnormal range
  have h_sub : x < (2 : R) ^ FloatFormat.min_exp := by
    -- smallestPosSubnormal = 2^(min_exp - prec + 1) < 2^min_exp
    have : FiniteFp.smallestPosSubnormal.toVal < (2 : R) ^ FloatFormat.min_exp := by
      rw [FiniteFp.smallestPosSubnormal_toVal]
      flinearize!
    exact lt_trans hs this
  simp only [h_sub, ↓reduceDIte]
  rw [Fp.finite.injEq]
  apply roundSubnormalDown_eq_zero_iff.mpr
  trivial

theorem roundDown_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x ≥ (2 : R) ^ (FloatFormat.max_exp + 1)):
  roundDown x = Fp.finite FiniteFp.largestFiniteFloat := by
  unfold roundDown findPredecessor
  simp [ne_of_gt hn, hn]
  unfold findPredecessorPos
  -- Since x ≥ 2^(max_exp + 1), we're beyond the normal range
  have h_sub : ¬(x < (2 : R) ^ FloatFormat.min_exp) := by
    have h2 : (2 : R) ^ FloatFormat.min_exp ≤ (2 : R) ^ (FloatFormat.max_exp + 1) := by flinearize!
    linarith
  simp [h_sub]
  -- The second condition is also false since x ≥ 2^(max_exp + 1)
  have h_overflow : ¬(x < (2 : R) ^ (FloatFormat.max_exp + 1)) := by
    exact not_lt.mpr hs
  simp [h_overflow]

/-- Strengthened version: roundDown returns largestFiniteFloat for any x > largestFiniteFloat.toVal.
    This covers both x ≥ 2^(max_exp+1) (overflow range) and largestFiniteFloat.toVal < x < 2^(max_exp+1)
    (last binade where the floor gives the maximum significand). -/
theorem roundDown_gt_lff [FloatFormat] (x : R) (hn : 0 < x)
    (hgt : x > (FiniteFp.largestFiniteFloat.toVal : R)) :
    roundDown x = Fp.finite FiniteFp.largestFiniteFloat := by
  by_cases hge : x ≥ (2 : R) ^ (FloatFormat.max_exp + 1)
  · exact roundDown_gt_largestFiniteFloat x hn hge
  · -- x is in the last binade: largestFiniteFloat.toVal < x < 2^(max_exp+1)
    push_neg at hge
    -- Helper: 2^max_exp ≤ largestFiniteFloat.toVal
    have hlff_ge : (2 : R) ^ FloatFormat.max_exp ≤ FiniteFp.largestFiniteFloat.toVal := by
      rw [FiniteFp.largestFiniteFloat_toVal]
      calc (2 : R) ^ FloatFormat.max_exp
          = (2 : R) ^ FloatFormat.max_exp * 1 := by ring
        _ ≤ (2 : R) ^ FloatFormat.max_exp * ((2 : R) - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt (zpow_pos (by norm_num) _))
            have h1 : (0 : R) < (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := zpow_pos (by norm_num) _
            have h2 : (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) ≤ 1 := by
              calc (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) ≤ (2 : R) ^ (0 : ℤ) :=
                    two_zpow_mono (by linarith [FloatFormat.valid_prec])
                _ = 1 := zpow_zero _
            linarith
    have hnr : isNormalRange x := ⟨le_trans (le_trans (two_zpow_mono
      (by linarith [FloatFormat.exp_order])) hlff_ge) (le_of_lt hgt), hge⟩
    unfold roundDown findPredecessor
    simp [ne_of_gt hn, hn]
    unfold findPredecessorPos
    simp [not_lt.mpr hnr.1, hge]
    -- Now show roundNormalDown x = largestFiniteFloat
    have hlog : Int.log 2 x = FloatFormat.max_exp := by
      have h_lb := (Int.zpow_le_iff_le_log (by norm_num : 1 < 2) hn).mp
        (le_trans hlff_ge (le_of_lt hgt))
      have h_ub := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < 2) hn).mp hge
      omega
    have hefd : findExponentDown x = FloatFormat.max_exp := by
      rw [findExponentDown_normal x hnr, hlog]
    -- x > lff.toVal = (2^prec - 1) * 2^(max_exp - prec + 1)
    -- So x / 2^(max_exp - prec + 1) > 2^prec - 1
    -- And x / 2^(max_exp - prec + 1) < 2^prec (from x < 2^(max_exp+1))
    -- Therefore floor(x / ulp) = 2^prec - 1
    have hstep_pos : (0 : R) < (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) :=
      zpow_pos (by norm_num) _
    have hlff_eq : (FiniteFp.largestFiniteFloat.toVal : R) =
        ((2 : R) ^ FloatFormat.prec - 1) * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
      -- Both sides equal 2^(max_exp+1) - 2^(max_exp - prec + 1)
      rw [FiniteFp.largestFiniteFloat_toVal, sub_mul]
      -- LHS: 2^max_exp * (2 - 2^(-prec+1)) = 2^max_exp * 2 - 2^max_exp * 2^(-prec+1)
      rw [mul_sub]
      -- Need: 2^max_exp * 2 = 2^prec * 2^(max_exp - prec + 1)
      -- and: 2^max_exp * 2^(-prec+1) = 1 * 2^(max_exp - prec + 1)
      have h1 : (2 : R) ^ FloatFormat.max_exp * 2 = (2 : R) ^ FloatFormat.prec * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
        rw [mul_comm, show (2 : R) * (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ (FloatFormat.max_exp + 1) from by
          rw [show FloatFormat.max_exp + 1 = 1 + FloatFormat.max_exp from by ring, ← two_zpow_mul, zpow_one]]
        rw [two_zpow_mul]; congr 1; ring
      have h2 : (2 : R) ^ FloatFormat.max_exp * (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) =
          1 * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
        rw [one_mul, two_zpow_mul]; congr 1; ring
      rw [h1, h2]
    have hdiv_lb : (2 : R) ^ FloatFormat.prec - 1 < x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
      rw [lt_div_iff₀ hstep_pos]; linarith [hlff_eq]
    have hdiv_ub : x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) < (2 : R) ^ FloatFormat.prec := by
      rw [div_lt_iff₀ hstep_pos, two_zpow_mul]
      rw [show (FloatFormat.prec : ℤ) + (FloatFormat.max_exp - FloatFormat.prec + 1) = FloatFormat.max_exp + 1 from by ring]
      exact hge
    have hfloor_eq : ⌊x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1)⌋ =
        (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
      apply le_antisymm
      · have hlt : ⌊x / (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1)⌋ <
            (2 : ℤ) ^ FloatFormat.prec.toNat := by
          rw [Int.floor_lt]; push_cast
          rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]
          exact hdiv_ub
        omega
      · rw [Int.le_floor]; push_cast
        rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]
        linarith
    unfold roundNormalDown
    simp only
    rw [FiniteFp.eq_def]
    simp only [FiniteFp.largestFiniteFloat]
    rw [hefd, floor_scaled_eq_floor_div_ulp_step, hfloor_eq]
    have h4 := FloatFormat.nat_four_le_two_pow_prec
    refine ⟨trivial, rfl, ?_⟩
    -- natAbs of (2^prec.toNat - 1) = 2^prec.toNat - 1 (as ℕ)
    -- Lift to ℤ
    suffices h : ((2 : ℤ) ^ FloatFormat.prec.toNat - 1).natAbs = (2 ^ FloatFormat.prec.toNat - 1 : ℕ) from h
    zify [Nat.one_le_two_pow]
    have : (4 : ℤ) ≤ (2 : ℤ) ^ FloatFormat.prec.toNat := by exact_mod_cast h4
    rw [abs_of_nonneg (by omega)]

theorem roundDown_nonneg_imp_nonneg [FloatFormat] (x : R) (hs : 0 ≤ x) (f : FiniteFp) (h' : roundDown x = Fp.finite f) : (0 : R) ≤ f.toVal := by
  unfold roundDown findPredecessor at h'
  split_ifs at h'
  · rw [Fp.finite.injEq] at h'
    simp [← h']
  · rw [Fp.finite.injEq] at h'
    rw [← h']
    apply findPredecessorPos_nonneg
  · norm_num at h'
    rename_i h1 h2
    norm_num at h1 h2
    have := (hs.ge_iff_eq.mp h2).symm
    contradiction

theorem roundDown_pos_imp_pos [FloatFormat] (x : R) (hs : FiniteFp.smallestPosSubnormal.toVal ≤ x) (f : FiniteFp) (h' : roundDown x = Fp.finite f) : (0 : R) < f.toVal := by
  unfold roundDown findPredecessor at h'
  have hpos : 0 < x := by linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  split_ifs at h'
  · simp_all only [lt_self_iff_false]
  · rw [Fp.finite.injEq] at h'
    rw [← h']
    apply findPredecessorPos_pos hs

/-- Key bridge lemma: `roundDown` of a positive value `mag * 2^e_base` produces a float with
significand `⌊val / 2^e_ulp⌋` and stored exponent `e_ulp + prec - 1`, where `e_ulp` is the
ULP exponent computed by `roundIntSig`. This bridges `roundIntSig`'s Nat division with
`roundDown`'s floor computation.

The hypotheses mirror the non-overflow, inexact case of `roundIntSig`:
- `hmag`: mag ≠ 0
- `hval_pos`: val > 0
- `hval_lt`: val < 2^(max_exp + 1) (non-overflow)
- `hfloor`: the floor of val / 2^e_ulp equals q
- `hint_log`: Int.log 2 val = Nat.log2 mag + e_base
- `he_ulp_ge_sub`: e_ulp ≥ min_exp - prec + 1
- `he_stored_le`: e_ulp + prec - 1 ≤ max_exp
- `hr_pos`: the remainder is positive (inexact)
-/
private lemma isValid_roundDownNatMulZpowTarget [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hfloor : ⌊(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌋ = (q : ℤ))
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq_bound : q < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq_normal_or_sub : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    IsValidFiniteVal (e_ulp + FloatFormat.prec - 1) q := by
  refine ⟨by omega, by omega, hq_bound, ?_⟩
  by_cases hn : 2 ^ (FloatFormat.prec - 1).toNat ≤ q
  · left; exact ⟨hn, hq_bound⟩
  · right
    push_neg at hn
    constructor
    · by_contra h_ne
      have h_gt : e_ulp + FloatFormat.prec - 1 > FloatFormat.min_exp := by omega
      have h_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
        rw [h_e_ulp_eq_normal_or_sub]; apply max_eq_left; omega
      have he_eq : e_ulp = (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 := by
        push_cast at h_normal ⊢; omega
      have hval_ge_binade : (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) ≤
          (mag : R) * (2 : R) ^ e_base := by
        rw [← two_zpow_mul, zpow_natCast]
        apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num) _)
        rw [← Nat.cast_ofNat, ← Nat.cast_pow]
        exact_mod_cast Nat.log2_self_le hmag
      have hq_ge_prec : (2 : R) ^ (FloatFormat.prec - 1) ≤
          (mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp := by
        rw [le_div_iff₀ (zpow_pos (by norm_num) _)]
        calc (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e_ulp
            = (2 : R) ^ ((FloatFormat.prec - 1) + e_ulp) := by rw [two_zpow_mul]
          _ = (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) := by
              congr 1; rw [he_eq]; ring
          _ ≤ (mag : R) * (2 : R) ^ e_base := hval_ge_binade
      have : (q : ℤ) ≥ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
        rw [← hfloor]
        exact Int.le_floor.mpr (by
          push_cast
          rw [← zpow_natCast (2 : R) (FloatFormat.prec - 1).toNat,
            FloatFormat.prec_sub_one_toNat_eq]
          exact hq_ge_prec)
      have hq_ge_nat : 2 ^ (FloatFormat.prec - 1).toNat ≤ q := by
        zify at hn ⊢; exact this
      omega
    · omega

private def mkRoundDownNatMulZpowTarget [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hfloor : ⌊(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌋ = (q : ℤ))
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq_bound : q < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq_normal_or_sub : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    FiniteFp :=
  ⟨false, e_ulp + FloatFormat.prec - 1, q,
    isValid_roundDownNatMulZpowTarget
      (R := R) mag e_base e_ulp q
      hmag hval_pos hfloor hint_log he_ulp_ge_sub he_stored_le hq_bound h_e_ulp_eq_normal_or_sub⟩

private abbrev roundDownNatMulZpowTarget [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hfloor : ⌊(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌋ = (q : ℤ))
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq_bound : q < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq_normal_or_sub : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    Fp :=
  Fp.finite <|
    mkRoundDownNatMulZpowTarget
      (R := R) mag e_base e_ulp q
      hmag hval_pos hfloor hint_log he_ulp_ge_sub he_stored_le hq_bound h_e_ulp_eq_normal_or_sub

theorem roundDown_nat_mul_zpow [FloatFormat]
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hval_lt : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1))
    (hfloor : ⌊(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌋ = (q : ℤ))
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq_bound : q < 2 ^ FloatFormat.prec.toNat)
    (hq_pos_or_zero : True) -- placeholder, q can be 0
    (h_e_ulp_eq_normal_or_sub : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    roundDown ((mag : R) * (2 : R) ^ e_base) =
      Fp.finite (mkRoundDownNatMulZpowTarget
        (R := R) mag e_base e_ulp q
        hmag hval_pos hfloor hint_log he_ulp_ge_sub he_stored_le hq_bound h_e_ulp_eq_normal_or_sub) := by
  unfold mkRoundDownNatMulZpowTarget
  unfold roundDown findPredecessor
  simp [ne_of_gt hval_pos, hval_pos]
  unfold findPredecessorPos
  -- Case split on subnormal vs normal vs overflow
  by_cases h_sub : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ FloatFormat.min_exp
  · -- SUBNORMAL CASE
    simp [h_sub]
    -- roundSubnormalDown computes ⌊val / 2^(min_exp - prec + 1)⌋
    -- and e_ulp = min_exp - prec + 1 (subnormal dominates)
    unfold roundSubnormalDown
    -- Need: e_ulp = min_exp - prec + 1 in subnormal case
    -- Since val < 2^min_exp, Int.log 2 val < min_exp
    -- So e_base + bits - prec < min_exp - prec + 1, meaning subnormal dominates
    have he_ulp_sub : e_ulp = FloatFormat.min_exp - FloatFormat.prec + 1 := by
      rw [h_e_ulp_eq_normal_or_sub]
      apply max_eq_right
      -- Need: e_base + bits - prec ≤ min_exp - prec + 1
      -- i.e., e_base + bits ≤ min_exp + 1
      -- From hint_log: Int.log 2 val = Nat.log2 mag + e_base
      -- From val < 2^min_exp: Int.log 2 val < min_exp
      have h_log_lt : (Nat.log2 mag : ℤ) + e_base < FloatFormat.min_exp := by
        rw [← hint_log]
        exact (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2:ℕ)) hval_pos).mp
          (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
      omega
    -- The floor computation: ⌊val / 2^(min_exp - prec + 1)⌋ = q
    have hfloor_sub : ⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋ = (q : ℤ) := by
      rw [← he_ulp_sub]; exact hfloor
    -- Need to match FiniteFp.mk equality
    -- roundSubnormalDown returns ⟨false, min_exp, k.natAbs⟩ where k = ⌊val / ulp⌋
    -- We need to show this equals ⟨false, e_ulp + prec - 1, q⟩
    -- Since e_ulp + prec - 1 = (min_exp - prec + 1) + prec - 1 = min_exp ✓
    -- And k.natAbs = q ✓ (from hfloor_sub: k = (q : ℤ), so k.natAbs = q)
    -- Establish key facts
    have hk_eq : ⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋ = (q : ℤ) := hfloor_sub
    have he_stored : e_ulp + FloatFormat.prec - 1 = FloatFormat.min_exp := by rw [he_ulp_sub]; ring
    have hnatabs : (⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋).natAbs = q := by
      rw [hk_eq]; exact Int.natAbs_natCast q
    -- The roundSubnormalDown unfolds to: if k = 0 then 0 else ⟨false, min_exp, k.natAbs, _⟩
    -- We need to show this = ⟨false, e_ulp + prec - 1, q, _⟩
    -- Both k=0 and k≠0 cases yield the same result once we rewrite
    -- Use congr to handle validity proof differences
    by_cases hk0 : ⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋ = 0
    · -- k = 0 means q = 0
      have hq0 : q = 0 := by exact_mod_cast (show (q : ℤ) = 0 from by rw [← hfloor_sub, hk0])
      simp only [hk0, ↓reduceDIte]
      -- Now goal: Fp.finite 0 = Fp.finite ⟨false, e_ulp + prec - 1, q, _⟩
      -- Goal: Fp.finite 0 = Fp.finite ⟨false, e_ulp + prec - 1, q, _⟩
      -- Both are Fp.finite of the zero FiniteFp
      congr 1
      rw [FiniteFp.eq_def, FiniteFp.zero_def]
      exact ⟨rfl, he_stored.symm, hq0.symm⟩
    · -- k ≠ 0
      simp only [hk0, ↓reduceDIte]
      -- Goal: Fp.finite ⟨false, min_exp, k.natAbs, _⟩ = Fp.finite ⟨false, e_ulp+prec-1, q, _⟩
      -- congr 1 decomposes through Fp.finite and FiniteFp into field goals
      congr 1; exact he_stored.symm
  · -- NOT SUBNORMAL: normal or overflow
    push_neg at h_sub
    by_cases h_normal : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1)
    · -- NORMAL CASE
      simp [not_lt.mpr h_sub, h_normal]
      -- roundNormalDown computes ⌊val / 2^e * 2^(prec-1)⌋ = ⌊val / 2^(e-prec+1)⌋
      -- where e = findExponentDown val
      unfold roundNormalDown
      simp only
      -- findExponentDown val = Int.log 2 val (in normal range, since val ∈ [2^min_exp, 2^(max_exp+1)))
      -- From hint_log: Int.log 2 val = Nat.log2 mag + e_base
      have h_nr : isNormalRange ((mag : R) * (2 : R) ^ e_base) := ⟨h_sub, h_normal⟩
      have h_fed : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
          (Nat.log2 mag : ℤ) + e_base := by
        rw [findExponentDown_normal _ h_nr, hint_log]
      -- e_ulp = e_base + bits - prec (normal dominates since val ≥ 2^min_exp)
      have he_ulp_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
        rw [h_e_ulp_eq_normal_or_sub]
        apply max_eq_left
        -- Need: min_exp - prec + 1 ≤ e_base + bits - prec
        -- i.e., min_exp + 1 ≤ e_base + bits
        -- From val ≥ 2^min_exp: Int.log 2 val ≥ min_exp
        have h_log_ge : FloatFormat.min_exp ≤ (Nat.log2 mag : ℤ) + e_base := by
          rw [← hint_log]
          exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2:ℕ)) hval_pos).mp
            (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
        omega
      -- findExponentDown val - prec + 1 = e_ulp
      have h_fed_ulp : findExponentDown ((mag : R) * (2 : R) ^ e_base) -
          FloatFormat.prec + 1 = e_ulp := by
        rw [h_fed, he_ulp_normal]; push_cast; ring
      -- The floor via floor_scaled_eq_floor_div_ulp_step
      have hfloor_normal : ⌊(mag : R) * (2 : R) ^ e_base /
          (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1)⌋ = (q : ℤ) := by
        have : (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 = e_ulp := by
          rw [he_ulp_normal]; push_cast; ring
        rw [this]; exact hfloor
      congr 1
      · -- e: findExponentDown val = e_ulp + prec - 1
        rw [h_fed, he_ulp_normal]; push_cast; ring
      · -- m: floor_scaled.natAbs = q
        rw [h_fed, floor_scaled_eq_floor_div_ulp_step, hfloor_normal]
        exact Int.natAbs_natCast q
    · -- OVERFLOW: contradiction with hval_lt
      exfalso; linarith

/-- roundDown of a positive value is ≥ Fp.finite 0 -/
theorem roundDown_zero_le_pos [FloatFormat] (x : R) (hx : 0 < x) :
    Fp.finite 0 ≤ roundDown x := by
  unfold roundDown
  rw [findPredecessor_pos_eq x hx, Fp.finite_le_finite_iff]
  apply FiniteFp.toVal_le_handle R
  · rw [FiniteFp.toVal_zero]; exact findPredecessorPos_nonneg
  · intro ⟨_, hy⟩
    unfold FiniteFp.isZero at hy
    unfold findPredecessorPos at hy ⊢
    split_ifs at hy ⊢ with h1 h2
    · simp only [roundSubnormalDown] at hy ⊢
      split_ifs at hy ⊢ with h3 <;> simp_all
    · exfalso
      have hnr : isNormalRange x := ⟨le_of_not_gt h1, h2⟩
      have hrnpos := roundNormalDown_pos x hnr
      have hzval := FiniteFp.toVal_isZero (R := R) hy
      linarith
    · exfalso; simp [FiniteFp.largestFiniteFloat] at hy
      have := FloatFormat.nat_four_le_two_pow_prec; omega

/-- roundDown of a negative value is ≤ Fp.finite 0 -/
theorem roundDown_neg_le_zero [FloatFormat] (x : R) (hx : x < 0) :
    roundDown x ≤ Fp.finite 0 := by
  unfold roundDown
  rw [findPredecessor_neg_eq x hx]
  have hneg_pos : 0 < -x := neg_pos.mpr hx
  match hfsp : findSuccessorPos (-x) hneg_pos with
  | Fp.finite f =>
    rw [Fp.neg_finite, Fp.finite_le_finite_iff]
    apply FiniteFp.toVal_le_handle R
    · rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_zero]
      linarith [findSuccessorPos_pos hfsp]
    · intro ⟨hx_zero, _⟩
      exfalso
      unfold FiniteFp.isZero at hx_zero
      simp [FiniteFp.neg_def] at hx_zero
      have hpos := findSuccessorPos_pos hfsp
      have hzero : f.toVal (R := R) = 0 := FiniteFp.toVal_isZero hx_zero
      linarith
  | Fp.infinite b =>
    have hne := findSuccessorPos_ne_neg_inf (-x) hneg_pos
    rw [hfsp] at hne; simp at hne
    cases b <;> simp_all [Fp.neg_def, Fp.le_def]
  | Fp.NaN =>
    exfalso
    exact findSuccessorPos_ne_nan (-x) hneg_pos (by rw [hfsp])

/-- roundDown is monotone: x ≤ y → roundDown x ≤ roundDown y -/
theorem roundDown_mono [FloatFormat] {x y : R} (h : x ≤ y) : roundDown x ≤ roundDown y := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0
    rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · -- Both negative: use findPredecessor_mono_neg
      unfold roundDown
      exact findPredecessor_mono_neg hx_neg hy_neg h
    · -- x < 0, y = 0
      rw [hy_zero, roundDown_zero]
      exact roundDown_neg_le_zero x hx_neg
    · -- x < 0 < y: roundDown x ≤ 0 ≤ roundDown y
      have h1 := roundDown_neg_le_zero x hx_neg
      have h2 := roundDown_zero_le_pos y hy_pos
      unfold roundDown at h1 h2 ⊢
      rw [findPredecessor_neg_eq x hx_neg] at h1 ⊢
      rw [findPredecessor_pos_eq y hy_pos] at h2 ⊢
      have hnx : 0 < -x := neg_pos.mpr hx_neg
      match hfsx : findSuccessorPos (-x) hnx with
      | Fp.finite fx =>
        rw [hfsx] at h1
        simp only [Fp.neg_finite] at h1 ⊢
        exact Fp.finite_le_trans h1 h2
      | Fp.infinite false =>
        -- -(+∞) = -∞ ≤ anything
        show Fp.infinite true ≤ _; rw [Fp.le_def]; left; simp [Fp.lt_def]
      | Fp.infinite true =>
        exfalso; exact findSuccessorPos_ne_neg_inf (-x) hnx hfsx
      | Fp.NaN => exact absurd hfsx (findSuccessorPos_ne_nan (-x) hnx)
  · -- x = 0
    rw [hx_zero, roundDown_zero]
    rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · linarith
    · rw [hy_zero, roundDown_zero]; exact Fp.le_refl _
    · exact roundDown_zero_le_pos y hy_pos
  · -- Both positive
    have hy_pos : 0 < y := lt_of_lt_of_le hx_pos h
    unfold roundDown
    rw [findPredecessor_pos_eq x hx_pos, findPredecessor_pos_eq y hy_pos]
    exact (Fp.finite_le_finite_iff _ _).mpr (findPredecessorPos_mono hx_pos hy_pos h)

end RoundDown

end Rounding
