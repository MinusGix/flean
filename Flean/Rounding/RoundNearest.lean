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

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]

/-- Extract the significand's least significant bit to check evenness for tie-breaking -/
def isEvenSignificand [FloatFormat] (f : FiniteFp) : Bool :=
  f.m % 2 = 0

section OppositeParityLemma

/-- For non-negative a with ⌊a⌋ ≠ ⌈a⌉, their natAbs values have opposite parity -/
private lemma floor_ceil_natAbs_opposite_parity {a : R} (ha : 0 ≤ a)
    (hne : ⌊a⌋ ≠ ⌈a⌉) : ⌊a⌋.natAbs % 2 ≠ ⌈a⌉.natAbs % 2 := by
  have hf_nn := Int.floor_nonneg.mpr ha
  have hle := Int.floor_le_ceil a
  have hceil_eq : ⌈a⌉ = ⌊a⌋ + 1 := le_antisymm (Int.ceil_le_floor_add_one a) (by omega)
  omega

/-- 2^n % 2 = 0 for n ≥ 1 -/
private lemma nat_two_pow_mod_two {n : ℕ} (hn : 1 ≤ n) : 2 ^ n % 2 = 0 :=
  Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : n ≠ 0))

/-- (2^n - 1) % 2 = 1 for n ≥ 1 -/
private lemma nat_two_pow_sub_one_mod_two {n : ℕ} (hn : 1 ≤ n) : (2 ^ n - 1) % 2 = 1 := by
  have h1 := nat_two_pow_mod_two hn
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

@[simp] private lemma FiniteFp.zero_m [FloatFormat] : (0 : FiniteFp).m = 0 := rfl
@[simp] private lemma FiniteFp.mk_m [FloatFormat] {s : Bool} {e : ℤ} {m : ℕ}
    {vf : IsValidFiniteVal e m} : (FiniteFp.mk s e m vf).m = m := rfl
@[simp] private lemma FiniteFp.smallestPosNormal_m [FloatFormat] :
    FiniteFp.smallestPosNormal.m = 2 ^ (FloatFormat.prec - 1).toNat := rfl

/-- When roundDown and roundUp give different results for a positive value,
    their significands have opposite parity. This is the key property that makes
    round-to-nearest-ties-to-even well-defined under negation. -/
theorem roundDown_roundUp_opposite_parity [FloatFormat]
    (x : R) (pred_fp succ_fp : FiniteFp)
    (hx_pos : 0 < x)
    (hrD : roundDown x = Fp.finite pred_fp)
    (hrU : roundUp x = Fp.finite succ_fp)
    (hne : pred_fp ≠ succ_fp) :
    isEvenSignificand pred_fp ≠ isEvenSignificand succ_fp := by
  -- Reduce to m parity
  suffices hm : pred_fp.m % 2 ≠ succ_fp.m % 2 by
    simp only [isEvenSignificand, ne_eq]
    intro heq; apply hm
    by_cases hp : pred_fp.m % 2 = 0 <;> by_cases hs : succ_fp.m % 2 = 0 <;> simp_all
  -- Unfold roundDown/roundUp to findPredecessorPos/findSuccessorPos
  rw [roundDown, findPredecessor_pos_eq x hx_pos, Fp.finite.injEq] at hrD
  rw [roundUp, findSuccessor_pos_eq x hx_pos] at hrU
  subst hrD
  unfold findPredecessorPos at hne ⊢
  unfold findSuccessorPos at hrU
  split_ifs at hne hrU ⊢ with h_sub h_norm
  · -- Case 1: subnormal (x < 2^min_exp)
    rw [Fp.finite.injEq] at hrU; subst hrU
    have hulp_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) := by
      linearize
    have ha_nonneg : 0 ≤ x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) :=
      div_nonneg (le_of_lt hx_pos) (le_of_lt hulp_pos)
    -- pred.m = ⌊x/ulp⌋.natAbs
    have hpred_m : (roundSubnormalDown x ⟨hx_pos, h_sub⟩).m =
        ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋.natAbs := by
      unfold roundSubnormalDown; dsimp only []
      split_ifs with h1
      · rw [show (0 : FiniteFp).m = 0 from rfl, h1]; rfl
      · rfl
    -- succ.m = ⌈x/ulp⌉.natAbs
    have hsucc_m : (roundSubnormalUp x ⟨hx_pos, h_sub⟩).m =
        ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉.natAbs := by
      unfold roundSubnormalUp; dsimp only []
      split_ifs with h1
      · -- Transition: ⌈x/ulp⌉ = 2^(prec-1) exactly
        have ha_lt : x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) <
            (2 : R) ^ (FloatFormat.prec - 1) := by
          rw [div_lt_iff₀ hulp_pos, ← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
          convert h_sub using 2; ring
        have hceil_le : ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ ≤
            (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
          have hfloor_lt : ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ <
              (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
            rw [Int.floor_lt]
            have : (↑((2 : ℤ) ^ (FloatFormat.prec - 1).toNat) : R) =
                (2 : R) ^ (FloatFormat.prec - 1) := by
              rw [Int.cast_pow, Int.cast_ofNat, ← zpow_natCast,
                FloatFormat.prec_sub_one_toNat_eq]
            linarith
          linarith [Int.ceil_le_floor_add_one
            (x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1))]
        have hceil_eq := le_antisymm hceil_le h1
        simp only [FiniteFp.smallestPosNormal_m]
        rw [hceil_eq]; rfl
      · rfl
    -- ⌊x/ulp⌋ ≠ ⌈x/ulp⌉ from hne
    have hfc_ne : ⌊x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌋ ≠
        ⌈x / (2 : R) ^ (FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1)⌉ := by
      intro heq; apply hne; rw [FiniteFp.eq_def]
      constructor
      · -- .s equal: both are determined by roundSubnormalDown/Up
        unfold roundSubnormalDown roundSubnormalUp; dsimp only []
        split_ifs <;> rfl
      constructor
      · -- .e equal: both are min_exp (or 0 maps to min_exp too)
        unfold roundSubnormalDown roundSubnormalUp; dsimp only []
        split_ifs <;> rfl
      · -- .m equal
        rw [hpred_m, hsucc_m, heq]
    rw [hpred_m, hsucc_m]
    exact floor_ceil_natAbs_opposite_parity ha_nonneg hfc_ne
  · -- Case 2: normal (2^min_exp ≤ x < 2^(max_exp+1))
    -- pred_fp.m = ⌊scaled⌋.natAbs where scaled = x / 2^e * 2^(prec-1)
    have hpred_m : (roundNormalDown x ⟨le_of_not_gt h_sub, h_norm⟩).m =
        ⌊x / (2 : R) ^ findExponentDown x *
          (2 : R) ^ (FloatFormat.prec - 1)⌋.natAbs := by
      unfold roundNormalDown; rfl
    -- Scaled value is non-negative
    have hscaled_nn : 0 ≤ x / (2 : R) ^ findExponentDown x *
        (2 : R) ^ (FloatFormat.prec - 1) := by
      apply mul_nonneg
      · exact div_nonneg (le_of_lt hx_pos) (zpow_nonneg (by norm_num) _)
      · exact zpow_nonneg (by norm_num) _
    have hfloor_pos := floor_scaled_normal_pos x ⟨le_of_not_gt h_sub, h_norm⟩
    -- Unfold roundNormalUp and split on carry (overflow auto-resolved)
    unfold roundNormalUp at hrU; dsimp only [] at hrU
    split_ifs at hrU with h_carry h_overflow
    · -- Carry + no overflow: succ.m = 2^(prec-1).toNat
      rw [Fp.finite.injEq] at hrU; subst hrU
      rw [hpred_m]
      -- ⌊scaled⌋ < 2^prec (from floor_isNormal_of_bounds, converted from Nat)
      have hfloor_ub_nat := (floor_isNormal_of_bounds x ⟨le_of_not_gt h_sub, h_norm⟩).right
      have hfloor_ub : ⌊x / (2 : R) ^ findExponentDown x *
          (2 : R) ^ (FloatFormat.prec - 1)⌋ < (2 : ℤ) ^ FloatFormat.prec.toNat := by
        have := Int.natAbs_of_nonneg (le_of_lt hfloor_pos)
        simp only [Int.two_pow_eq_nat_cast] at hfloor_ub_nat ⊢; omega
      -- ⌈scaled⌉ = 2^prec (from carry + upper bound)
      have hceil_eq_pow : ⌈x / (2 : R) ^ findExponentDown x *
          (2 : R) ^ (FloatFormat.prec - 1)⌉ = (2 : ℤ) ^ FloatFormat.prec.toNat := by
        apply le_antisymm
        · linarith [Int.ceil_le_floor_add_one (x / (2 : R) ^ findExponentDown x *
            (2 : R) ^ (FloatFormat.prec - 1))]
        · exact h_carry
      -- ⌊scaled⌋ = 2^prec - 1
      have hfloor_eq : ⌊x / (2 : R) ^ findExponentDown x *
          (2 : R) ^ (FloatFormat.prec - 1)⌋ = (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
        have := Int.ceil_le_floor_add_one (x / (2 : R) ^ findExponentDown x *
            (2 : R) ^ (FloatFormat.prec - 1))
        omega
      -- pred.m = 2^prec.toNat - 1
      have hpred_natAbs : (⌊x / (2 : R) ^ findExponentDown x *
          (2 : R) ^ (FloatFormat.prec - 1)⌋).natAbs = 2 ^ FloatFormat.prec.toNat - 1 := by
        have h_nn := le_of_lt hfloor_pos
        have h_cast : (⌊x / (2 : R) ^ findExponentDown x *
            (2 : R) ^ (FloatFormat.prec - 1)⌋.natAbs : ℤ) = ⌊x / (2 : R) ^ findExponentDown x *
            (2 : R) ^ (FloatFormat.prec - 1)⌋ := Int.natAbs_of_nonneg h_nn
        have h_cast2 : ((2 ^ FloatFormat.prec.toNat - 1 : ℕ) : ℤ) =
            (2 : ℤ) ^ FloatFormat.prec.toNat - 1 := by
          rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
        omega
      rw [hpred_natAbs]; dsimp only []
      -- Now goal: (2^prec.toNat - 1) % 2 ≠ 2^(prec-1).toNat % 2
      have h_even := nat_two_pow_mod_two (FloatFormat.one_le_prec_sub_one_toNat)
      have h_odd := nat_two_pow_sub_one_mod_two
        (show 1 ≤ FloatFormat.prec.toNat from by have := FloatFormat.two_le_prec_toNat; omega)
      omega
    · -- No carry: succ.m = ⌈scaled⌉.natAbs
      rw [Fp.finite.injEq] at hrU; subst hrU
      rw [hpred_m]
      -- hne gives ⌊scaled⌋ ≠ ⌈scaled⌉
      have hfc_ne : ⌊x / (2 : R) ^ findExponentDown x *
          (2 : R) ^ (FloatFormat.prec - 1)⌋ ≠
          ⌈x / (2 : R) ^ findExponentDown x *
          (2 : R) ^ (FloatFormat.prec - 1)⌉ := by
        intro heq; apply hne; rw [FiniteFp.eq_def]
        exact ⟨rfl, rfl, by rw [hpred_m, heq]⟩
      exact floor_ceil_natAbs_opposite_parity hscaled_nn hfc_ne
  -- Case 3 (overflow) auto-resolved by split_ifs

end OppositeParityLemma

-- Round to nearest, ties to even (default IEEE 754 rounding)
section RoundNearestTiesToEven

/-- Round to nearest, ties to even -/
def roundNearestTiesToEven [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then
    if x < 0 then Fp.finite (-0) else Fp.finite 0
  else if |x| ≥ FloatFormat.overflowThreshold R then Fp.infinite (x < 0)
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
    | Fp.finite _, _ => pred
    | _, Fp.finite _ => succ
    | _, _ => Fp.NaN

/-- roundNearestTiesToEven returns 0 when input is 0 -/
theorem roundNearestTiesToEven_zero [FloatFormat] : roundNearestTiesToEven (0 : R) = Fp.finite 0 := by
  unfold roundNearestTiesToEven
  simp

theorem rnEven_le_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesToEven x = Fp.finite 0 := by
  unfold roundNearestTiesToEven
  -- Need to show |x| < smallestPosSubnormal / 2
  have h_abs : |x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hn]
    exact hs
  have h_not_neg : ¬x < 0 := not_lt.mpr (le_of_lt hn)
  simp [ne_of_gt hn, h_abs, h_not_neg]

-- TODO: negative values?
-- TODO: better name.
-- Closely related to largest positive normal number.
theorem rnEven_ge_inf [FloatFormat] (x : R) (hx : x ≥ FloatFormat.overflowThreshold R) :
  roundNearestTiesToEven x = Fp.infinite false := by
  unfold roundNearestTiesToEven
  -- Use helper lemmas from FloatFormat
  have hthresh_pos := FloatFormat.overflow_threshold_pos (R := R)
  -- x is positive since threshold is positive
  have hx_pos : 0 < x := lt_of_lt_of_le hthresh_pos hx
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  -- smallestPosSubnormal / 2 < threshold (chain through 2^min_exp and 2^max_exp)
  have hsmall_lt : (FiniteFp.smallestPosSubnormal.toVal : R) / 2 < FloatFormat.overflowThreshold R :=
    calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp := zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ FloatFormat.overflowThreshold R := FloatFormat.zpow_max_exp_le_overflow_threshold
  have h_not_small : ¬|x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hx_pos]
    linarith
  have h_overflow : |x| ≥ FloatFormat.overflowThreshold R := by
    rw [abs_of_pos hx_pos]
    exact hx
  have h_not_neg : ¬x < 0 := not_lt.mpr (le_of_lt hx_pos)
  simp [hx_ne, h_not_small, h_overflow, h_not_neg]

end RoundNearestTiesToEven

-- Round to nearest, ties away from zero
section RoundNearestTiesAwayFromZero

/-- Round to nearest, ties away from zero -/
def roundNearestTiesAwayFromZero [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then
    if x < 0 then Fp.finite (-0) else Fp.finite 0
  else if |x| ≥ FloatFormat.overflowThreshold R then Fp.infinite (x < 0)
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
    | Fp.finite _, _ => pred
    | _, Fp.finite _ => succ
    | _, _ => Fp.NaN

/-- roundNearestTiesAwayFromZero returns 0 when input is 0 -/
theorem roundNearestTiesAwayFromZero_zero [FloatFormat] : roundNearestTiesAwayFromZero (0 : R) = Fp.finite 0 := by
  unfold roundNearestTiesAwayFromZero
  simp

theorem rnAway_lt_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesAwayFromZero x = Fp.finite 0 := by
  unfold roundNearestTiesAwayFromZero
  have h_abs : |x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hn]
    exact hs
  have h_not_neg : ¬x < 0 := not_lt.mpr (le_of_lt hn)
  simp [ne_of_gt hn, h_abs, h_not_neg]

theorem rnAway_ge_inf [FloatFormat] (x : R) (hx : x ≥ FloatFormat.overflowThreshold R) :
  roundNearestTiesAwayFromZero x = Fp.infinite false := by
  unfold roundNearestTiesAwayFromZero
  have hthresh_pos := FloatFormat.overflow_threshold_pos (R := R)
  have hx_pos : 0 < x := lt_of_lt_of_le hthresh_pos hx
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hsmall_lt : (FiniteFp.smallestPosSubnormal.toVal : R) / 2 < FloatFormat.overflowThreshold R :=
    calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp := zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ FloatFormat.overflowThreshold R := FloatFormat.zpow_max_exp_le_overflow_threshold
  have h_not_small : ¬|x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hx_pos]
    linarith
  have h_overflow : |x| ≥ FloatFormat.overflowThreshold R := by
    rw [abs_of_pos hx_pos]
    exact hx
  have h_not_neg : ¬x < 0 := not_lt.mpr (le_of_lt hx_pos)
  simp [hx_ne, h_not_small, h_overflow, h_not_neg]

end RoundNearestTiesAwayFromZero

/-! ### Negative overflow lemmas for nearest modes -/

/-- roundNearestTiesToEven of a sufficiently negative value gives negative infinity. -/
theorem rnEven_neg_overflow [FloatFormat] (y : R) (hy_pos : 0 < y)
    (hy_ge : y ≥ FloatFormat.overflowThreshold R) :
    roundNearestTiesToEven (-y) = Fp.infinite true := by
  unfold roundNearestTiesToEven
  have hne : (-y : R) ≠ 0 := by linarith
  have habs_eq : |-y| = y := by rw [abs_neg, abs_of_pos hy_pos]
  have hsmall : ¬(|-y| < (FiniteFp.smallestPosSubnormal.toVal : R) / 2) := by
    rw [habs_eq]
    linarith [calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp :=
          zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ _ := FloatFormat.zpow_max_exp_le_overflow_threshold]
  have hge : |-y| ≥ FloatFormat.overflowThreshold R := by
    rw [habs_eq]; exact hy_ge
  simp only [hne, hsmall, hge, ↓reduceIte, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  congr 1; exact decide_eq_true (by linarith : -y < 0)

/-- roundNearestTiesAwayFromZero of a sufficiently negative value gives negative infinity. -/
theorem rnAway_neg_overflow [FloatFormat] (y : R) (hy_pos : 0 < y)
    (hy_ge : y ≥ FloatFormat.overflowThreshold R) :
    roundNearestTiesAwayFromZero (-y) = Fp.infinite true := by
  unfold roundNearestTiesAwayFromZero
  have hne : (-y : R) ≠ 0 := by linarith
  have habs_eq : |-y| = y := by rw [abs_neg, abs_of_pos hy_pos]
  have hsmall : ¬(|-y| < (FiniteFp.smallestPosSubnormal.toVal : R) / 2) := by
    rw [habs_eq]
    linarith [calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp :=
          zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ _ := FloatFormat.zpow_max_exp_le_overflow_threshold]
  have hge : |-y| ≥ FloatFormat.overflowThreshold R := by
    rw [habs_eq]; exact hy_ge
  simp only [hne, hsmall, hge, ↓reduceIte, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  congr 1; exact decide_eq_true (by linarith : -y < 0)

/-! ### Nearest mode unfolding lemmas

These lemmas connect the integer-level midpoint comparison (`r` vs `2^(shift-1)`) with
the real-level nearest rounding functions. -/

/-- For positive `val` in the representable range, if `val < midpoint(pred, succ)` then
`roundNearestTiesToEven(val) = roundDown(val)`, and if `val > midpoint` then
`roundNearestTiesToEven(val) = roundUp(val)`. For the tie case, even parity decides. -/
theorem rnEven_pos_of_roundDown_roundUp [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt_thresh : val < FloatFormat.overflowThreshold R)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp)
    (hmid_lt : val < (pred_fp.toVal + succ_fp.toVal) / 2 →
      roundNearestTiesToEven val = roundDown val)
    (hmid_gt : val > (pred_fp.toVal + succ_fp.toVal) / 2 →
      roundNearestTiesToEven val = roundUp val)
    (hmid_even : val = (pred_fp.toVal + succ_fp.toVal) / 2 → isEvenSignificand pred_fp →
      roundNearestTiesToEven val = roundDown val)
    (hmid_odd : val = (pred_fp.toVal + succ_fp.toVal) / 2 → ¬isEvenSignificand pred_fp →
      roundNearestTiesToEven val = roundUp val) :
    True := trivial  -- This is just documentation; the actual proofs use the cases directly

-- The actual workhorse: unfold roundNearestTiesToEven for positive val in range
theorem rnEven_pos_unfold [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt_thresh : val < FloatFormat.overflowThreshold R)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesToEven val =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val < midpoint then Fp.finite pred_fp
      else if val > midpoint then Fp.finite succ_fp
      else if isEvenSignificand pred_fp then Fp.finite pred_fp
      else Fp.finite succ_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_ge_ssps
  have h_not_overflow : ¬(|val| ≥ FloatFormat.overflowThreshold R) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  -- Now in the let/match branch
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  -- roundDown = findPredecessor, roundUp = findSuccessor for positive val
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := by
    exact Fp.finite.inj hpred_eq
  -- findSuccessorPos returns Fp, not FiniteFp. We need to case-match.
  rw [hsucc_eq_fp]
  dsimp only
  rw [hpred_fp_eq]

/-- Similar unfolding for roundNearestTiesAwayFromZero on positive values. -/
theorem rnAway_pos_unfold [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt_thresh : val < FloatFormat.overflowThreshold R)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesAwayFromZero val =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val < midpoint then Fp.finite pred_fp
      else if val > midpoint then Fp.finite succ_fp
      else if val > 0 then Fp.finite succ_fp
      else Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_ge_ssps
  have h_not_overflow : ¬(|val| ≥ FloatFormat.overflowThreshold R) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := by
    exact Fp.finite.inj hpred_eq
  rw [hsucc_eq_fp]
  dsimp only
  rw [hpred_fp_eq]

/-! ### Midpoint decision lemmas for positive values

These lemmas directly give the rounding result based on the value's position relative to
the midpoint between adjacent floats. They are key building blocks for proving that
`roundIntSig` matches `mode.round`. -/

/-- TiesToEven: value above midpoint → rounds up -/
theorem rnEven_above_mid_eq_roundUp [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val > ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesToEven val = roundUp val := by
  rw [rnEven_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrU]
  dsimp only
  rw [if_neg (not_lt.mpr (le_of_lt hmid)), if_pos hmid]

/-- TiesToEven: value below midpoint → rounds down -/
theorem rnEven_below_mid_eq_roundDown [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val < ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesToEven val = roundDown val := by
  rw [rnEven_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only; rw [if_pos hmid]

/-- TiesToEven: at midpoint with odd predecessor → rounds up -/
theorem rnEven_at_mid_odd_eq_roundUp [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val = ((pred_fp.toVal : R) + succ_fp.toVal) / 2)
    (hodd : isEvenSignificand pred_fp = false) :
    roundNearestTiesToEven val = roundUp val := by
  rw [rnEven_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrU]
  dsimp only
  rw [if_neg (not_lt.mpr hmid.ge), if_neg (not_lt.mpr hmid.le), hodd]; simp

/-- TiesToEven: at midpoint with even predecessor → rounds down -/
theorem rnEven_at_mid_even_eq_roundDown [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val = ((pred_fp.toVal : R) + succ_fp.toVal) / 2)
    (heven : isEvenSignificand pred_fp = true) :
    roundNearestTiesToEven val = roundDown val := by
  rw [rnEven_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only
  rw [if_neg (not_lt.mpr hmid.ge), if_neg (not_lt.mpr hmid.le), heven]; simp

/-- TiesAway: value at or above midpoint → rounds up -/
theorem rnAway_ge_mid_eq_roundUp [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val ≥ ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesAwayFromZero val = roundUp val := by
  rw [rnAway_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrU]
  dsimp only
  by_cases hgt : val > ((pred_fp.toVal : R) + succ_fp.toVal) / 2
  · rw [if_neg (not_lt.mpr (le_of_lt hgt)), if_pos hgt]
  · rw [if_neg (not_lt.mpr hmid), if_neg hgt, if_pos hval_pos]

/-- TiesAway: value below midpoint → rounds down -/
theorem rnAway_lt_mid_eq_roundDown [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal / 2)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val < ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesAwayFromZero val = roundDown val := by
  rw [rnAway_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only; rw [if_pos hmid]

/-- When val ≥ midpoint(pred, succ) and both roundDown/roundUp are finite, val ≥ ssps/2.

This is used to eliminate the `hval_ge` precondition from the midpoint wrapper lemmas:
when val ≥ midpoint, the tiny-value branch is vacuously impossible because the midpoint
between 0 and ssps is exactly ssps/2. -/
private lemma val_ge_ssps_half_of_mid_ge [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_ge : val ≥ ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    val ≥ FiniteFp.smallestPosSubnormal.toVal / 2 := by
  by_contra hlt
  push_neg at hlt
  have hval_lt_ssps : val < FiniteFp.smallestPosSubnormal.toVal := by
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have hpred_zero : pred_fp = 0 :=
    Fp.finite.inj (by rw [← hrD]; exact roundDown_lt_smallestPosSubnormal val hval_pos hval_lt_ssps)
  have hsucc_ssps : succ_fp = FiniteFp.smallestPosSubnormal :=
    Fp.finite.inj (by rw [← hrU]; exact roundUp_lt_smallestPosSubnormal val hval_pos hval_lt_ssps)
  rw [hpred_zero, hsucc_ssps, FiniteFp.toVal_zero, zero_add] at hmid_ge
  linarith

/-! ### Midpoint lemma wrappers with explicit mid_val parameter

These variants take `mid_val` and a proof `hmid_eq : (pred + succ) / 2 = mid_val`
as separate arguments, so callers can provide the midpoint bridge and the comparison
as independent terms without inline tactic blocks. -/

/-- rnEven above midpoint → roundUp (with explicit mid_val) -/
theorem rnEven_above_mid_roundUp [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val > mid_val) :
    roundNearestTiesToEven val = roundUp val :=
  rnEven_above_mid_eq_roundUp val pred_fp succ_fp hval_pos
    (val_ge_ssps_half_of_mid_ge val pred_fp succ_fp hval_pos hrD hrU
      (le_of_lt (by rw [hmid_eq]; exact hmid)))
    hval_lt hrD hrU (by rw [hmid_eq]; exact hmid)

/-- rnEven below midpoint → roundDown (with explicit mid_val) -/
theorem rnEven_below_mid_roundDown [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val < mid_val) :
    roundNearestTiesToEven val = roundDown val := by
  by_cases hsmall : |val| < FiniteFp.smallestPosSubnormal.toVal / 2
  · -- Tiny value: both sides equal Fp.finite 0
    have hval_lt_ssps : val < FiniteFp.smallestPosSubnormal.toVal := by
      linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R),
        show val < _ from by rwa [abs_of_pos hval_pos] at hsmall]
    have hLHS : roundNearestTiesToEven val = Fp.finite 0 := by
      unfold roundNearestTiesToEven
      rw [if_neg (ne_of_gt hval_pos), if_pos hsmall, if_neg (not_lt.mpr (le_of_lt hval_pos))]
    rw [hLHS, roundDown_lt_smallestPosSubnormal val hval_pos hval_lt_ssps]
  · exact rnEven_below_mid_eq_roundDown val pred_fp succ_fp hval_pos
      (by have := not_lt.mp hsmall; rwa [abs_of_pos hval_pos] at this)
      hval_lt hrD hrU (by rw [hmid_eq]; exact hmid)

/-- rnEven at midpoint, odd predecessor → roundUp (with explicit mid_val) -/
theorem rnEven_at_mid_odd_roundUp [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val = mid_val)
    (hodd : isEvenSignificand pred_fp = false) :
    roundNearestTiesToEven val = roundUp val :=
  rnEven_at_mid_odd_eq_roundUp val pred_fp succ_fp hval_pos
    (val_ge_ssps_half_of_mid_ge val pred_fp succ_fp hval_pos hrD hrU
      (by rw [hmid_eq]; exact hmid.ge))
    hval_lt hrD hrU (by rw [hmid_eq]; exact hmid) hodd

/-- rnEven at midpoint, even predecessor → roundDown (with explicit mid_val) -/
theorem rnEven_at_mid_even_roundDown [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val = mid_val)
    (heven : isEvenSignificand pred_fp = true) :
    roundNearestTiesToEven val = roundDown val :=
  rnEven_at_mid_even_eq_roundDown val pred_fp succ_fp hval_pos
    (val_ge_ssps_half_of_mid_ge val pred_fp succ_fp hval_pos hrD hrU
      (by rw [hmid_eq]; exact hmid.ge))
    hval_lt hrD hrU (by rw [hmid_eq]; exact hmid) heven

/-- rnAway at or above midpoint → roundUp (with explicit mid_val) -/
theorem rnAway_ge_mid_roundUp [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val ≥ mid_val) :
    roundNearestTiesAwayFromZero val = roundUp val :=
  rnAway_ge_mid_eq_roundUp val pred_fp succ_fp hval_pos
    (val_ge_ssps_half_of_mid_ge val pred_fp succ_fp hval_pos hrD hrU
      (by rw [hmid_eq]; exact hmid))
    hval_lt hrD hrU (by rw [hmid_eq]; exact hmid)

/-- rnAway below midpoint → roundDown (with explicit mid_val) -/
theorem rnAway_lt_mid_roundDown [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt : val < FloatFormat.overflowThreshold R)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val < mid_val) :
    roundNearestTiesAwayFromZero val = roundDown val := by
  by_cases hsmall : |val| < FiniteFp.smallestPosSubnormal.toVal / 2
  · -- Tiny value: both sides equal Fp.finite 0
    have hval_lt_ssps : val < FiniteFp.smallestPosSubnormal.toVal := by
      linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R),
        show val < _ from by rwa [abs_of_pos hval_pos] at hsmall]
    have hLHS : roundNearestTiesAwayFromZero val = Fp.finite 0 := by
      unfold roundNearestTiesAwayFromZero
      rw [if_neg (ne_of_gt hval_pos), if_pos hsmall, if_neg (not_lt.mpr (le_of_lt hval_pos))]
    rw [hLHS, roundDown_lt_smallestPosSubnormal val hval_pos hval_lt_ssps]
  · exact rnAway_lt_mid_eq_roundDown val pred_fp succ_fp hval_pos
      (by have := not_lt.mp hsmall; rwa [abs_of_pos hval_pos] at this)
      hval_lt hrD hrU (by rw [hmid_eq]; exact hmid)

theorem largestFiniteFloat_lt_overflow_threshold [FloatFormat] :
    FiniteFp.largestFiniteFloat.toVal <
    FloatFormat.overflowThreshold R := by
  unfold FloatFormat.overflowThreshold
  rw [FiniteFp.largestFiniteFloat_toVal,
    show -(FloatFormat.prec : ℤ) + 1 = 1 - (FloatFormat.prec : ℤ) from by ring,
    mul_comm ((2:R) - _) _]
  exact mul_lt_mul_of_pos_left
    (by linarith [zpow_pos (by norm_num : (0:R) < 2) (1 - (FloatFormat.prec : ℤ))])
    (zpow_pos (by norm_num : (0:R) < 2) _)

theorem val_lt_thresh_of_roundUp_finite [FloatFormat]
    (val : R) (f : FiniteFp) (hval_pos : 0 < val)
    (hroundUp : roundUp val = Fp.finite f) :
    val < FloatFormat.overflowThreshold R := by
  have hfsp : findSuccessorPos val hval_pos = Fp.finite f := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  calc val ≤ f.toVal := findSuccessorPos_ge val hval_pos f hfsp
    _ ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
    _ < _ := largestFiniteFloat_lt_overflow_threshold

/-- When roundUp overflows and val < threshold, roundNearestTiesToEven returns roundDown. -/
theorem rnEven_pos_succ_overflow [FloatFormat]
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt_thresh : val < FloatFormat.overflowThreshold R)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesToEven val = Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    intro habs
    have hval_lt_ssps : val < FiniteFp.smallestPosSubnormal.toVal := by
      linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R),
        show val < _ from by rwa [abs_of_pos hval_pos] at habs]
    have h := roundUp_lt_smallestPosSubnormal val hval_pos hval_lt_ssps
    rw [hroundUp_inf] at h; exact absurd h (by simp)
  have h_not_overflow : ¬(|val| ≥ FloatFormat.overflowThreshold R) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf]; dsimp only; rw [hpred_fp_eq]

/-- When roundUp overflows and val < threshold, roundNearestTiesAwayFromZero returns roundDown. -/
theorem rnAway_pos_succ_overflow [FloatFormat]
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_lt_thresh : val < FloatFormat.overflowThreshold R)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesAwayFromZero val = Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    intro habs
    have hval_lt_ssps : val < FiniteFp.smallestPosSubnormal.toVal := by
      linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R),
        show val < _ from by rwa [abs_of_pos hval_pos] at habs]
    have h := roundUp_lt_smallestPosSubnormal val hval_pos hval_lt_ssps
    rw [hroundUp_inf] at h; exact absurd h (by simp)
  have h_not_overflow : ¬(|val| ≥ FloatFormat.overflowThreshold R) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf]; dsimp only; rw [hpred_fp_eq]

section NegationSymmetry

/-- roundNearestTiesAwayFromZero(-x) = -(roundNearestTiesAwayFromZero x) for positive x -/
private theorem rnAway_neg_eq_neg_pos [FloatFormat] (x : R) (hx : 0 < x) :
    roundNearestTiesAwayFromZero (-x) = -(roundNearestTiesAwayFromZero x) := by
  have hne : x ≠ 0 := ne_of_gt hx
  have hneg_ne : -x ≠ 0 := neg_ne_zero.mpr hne
  have hneg_lt : -x < 0 := neg_lt_zero.mpr hx
  unfold roundNearestTiesAwayFromZero
  -- Eliminate x = 0 / -x = 0 branches
  rw [if_neg hneg_ne, if_neg hne, abs_neg]
  -- Split on small range (use simp only for if-branches to rewrite both LHS and RHS)
  by_cases hsmall : |x| < FiniteFp.smallestPosSubnormal.toVal / 2
  · simp only [if_pos hsmall, hneg_lt, ↓reduceIte, not_lt.mpr (le_of_lt hx), Fp.neg_finite]
  · by_cases hoverflow : |x| ≥
        FloatFormat.overflowThreshold R
    · simp only [if_neg hsmall, if_pos hoverflow, hneg_lt, ↓reduceIte, not_lt.mpr (le_of_lt hx)]
      simp [Fp.neg_def]
    · simp only [if_neg hsmall, if_neg hoverflow]
      -- Normal range: rewrite findPredecessor/findSuccessor for -x
      simp only [findPredecessor_neg_eq (-x) hneg_lt, findSuccessor_neg_eq (-x) hneg_lt, neg_neg,
        findPredecessor_pos_eq x hx, findSuccessor_pos_eq x hx]
      -- Case split on whether findSuccessorPos is finite or infinite
      rcases hfsp : findSuccessorPos x hx with f | b | _
      · -- findSuccessorPos = Fp.finite f: split all if-conditions
        dsimp only
        simp only [FiniteFp.toVal_neg_eq_neg]
        split_ifs <;> simp_all [Fp.neg_finite] <;> linarith
      · -- findSuccessorPos = Fp.infinite b
        dsimp only
        rfl
      · -- findSuccessorPos = Fp.NaN: impossible
        exact absurd hfsp (findSuccessorPos_ne_nan x hx)

/-- roundNearestTiesAwayFromZero commutes with negation -/
theorem rnAway_neg_eq_neg [FloatFormat] (x : R) (hx : x ≠ 0) :
    roundNearestTiesAwayFromZero (-x) = -(roundNearestTiesAwayFromZero x) := by
  by_cases hpos : 0 < x
  · exact rnAway_neg_eq_neg_pos x hpos
  · -- x < 0: apply the positive case to -x
    have hxlt : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
    have hpos_neg : 0 < -x := neg_pos.mpr hxlt
    have h := rnAway_neg_eq_neg_pos (-x) hpos_neg
    rw [neg_neg] at h
    -- h : rnAway(x) = -(rnAway(-x))
    rw [h, neg_neg]

/-- roundNearestTiesToEven(-x) = -(roundNearestTiesToEven x) for positive x -/
private theorem rnEven_neg_eq_neg_pos [FloatFormat] (x : R) (hx : 0 < x) :
    roundNearestTiesToEven (-x) = -(roundNearestTiesToEven x) := by
  have hne : x ≠ 0 := ne_of_gt hx
  have hneg_ne : -x ≠ 0 := neg_ne_zero.mpr hne
  have hneg_lt : -x < 0 := neg_lt_zero.mpr hx
  unfold roundNearestTiesToEven
  rw [if_neg hneg_ne, if_neg hne, abs_neg]
  by_cases hsmall : |x| < FiniteFp.smallestPosSubnormal.toVal / 2
  · simp only [if_pos hsmall, hneg_lt, ↓reduceIte, not_lt.mpr (le_of_lt hx), Fp.neg_finite]
  · by_cases hoverflow : |x| ≥
        FloatFormat.overflowThreshold R
    · simp only [if_neg hsmall, if_pos hoverflow, hneg_lt, ↓reduceIte, not_lt.mpr (le_of_lt hx)]
      simp [Fp.neg_def]
    · simp only [if_neg hsmall, if_neg hoverflow]
      simp only [findPredecessor_neg_eq (-x) hneg_lt, findSuccessor_neg_eq (-x) hneg_lt, neg_neg,
        findPredecessor_pos_eq x hx, findSuccessor_pos_eq x hx]
      rcases hfsp : findSuccessorPos x hx with f | b | _
      · -- findSuccessorPos = Fp.finite f
        dsimp only
        simp only [FiniteFp.toVal_neg_eq_neg]
        have heven_neg : isEvenSignificand (-f) = isEvenSignificand f := by
          simp [isEvenSignificand, FiniteFp.neg_def]
        have hrD : roundDown x = Fp.finite (findPredecessorPos x hx) := by
          rw [roundDown, findPredecessor_pos_eq x hx]
        have hrU : roundUp x = Fp.finite f := by
          rw [roundUp, findSuccessor_pos_eq x hx, hfsp]
        by_cases hpred_eq : findPredecessorPos x hx = f
        · -- pred = succ: x is exactly a float, both sides trivially equal
          subst hpred_eq; simp only [heven_neg]
          split_ifs <;> simp_all [Fp.neg_finite] <;> linarith
        · -- pred ≠ succ: use opposite parity
          have hparity := roundDown_roundUp_opposite_parity x _ _ hx hrD hrU hpred_eq
          simp only [heven_neg]
          split_ifs <;> simp_all [Fp.neg_finite] <;> linarith
      · -- findSuccessorPos = Fp.infinite b
        dsimp only
        rfl
      · -- findSuccessorPos = Fp.NaN: impossible
        exact absurd hfsp (findSuccessorPos_ne_nan x hx)

/-- roundNearestTiesToEven commutes with negation -/
theorem rnEven_neg_eq_neg [FloatFormat] (x : R) (hx : x ≠ 0) :
    roundNearestTiesToEven (-x) = -(roundNearestTiesToEven x) := by
  by_cases hpos : 0 < x
  · exact rnEven_neg_eq_neg_pos x hpos
  · have hxlt : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
    have hpos_neg : 0 < -x := neg_pos.mpr hxlt
    have h := rnEven_neg_eq_neg_pos (-x) hpos_neg
    rw [neg_neg] at h
    rw [h, neg_neg]

end NegationSymmetry

end Rounding
