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

-- Round to nearest, ties to even (default IEEE 754 rounding)
section RoundNearestTiesToEven

/-- Round to nearest, ties to even -/
def roundNearestTiesToEven [FloatFormat] (x : R) : Fp :=
  if x = 0 then Fp.finite 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then
    if x < 0 then Fp.finite (-0) else Fp.finite 0
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
theorem rnEven_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesToEven x = Fp.infinite false := by
  unfold roundNearestTiesToEven
  -- Use helper lemmas from FloatFormat
  have hthresh_pos := FloatFormat.overflow_threshold_pos (R := R)
  -- x is positive since threshold is positive
  have hx_pos : 0 < x := lt_of_lt_of_le hthresh_pos hx
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  -- smallestPosSubnormal / 2 < threshold (chain through 2^min_exp and 2^max_exp)
  have hsmall_lt : (FiniteFp.smallestPosSubnormal.toVal : R) / 2 < (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp :=
    calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp := zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp := FloatFormat.zpow_max_exp_le_overflow_threshold
  have h_not_small : ¬|x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hx_pos]
    linarith
  have h_overflow : |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp := by
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

theorem rnAway_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesAwayFromZero x = Fp.infinite false := by
  unfold roundNearestTiesAwayFromZero
  have hthresh_pos := FloatFormat.overflow_threshold_pos (R := R)
  have hx_pos : 0 < x := lt_of_lt_of_le hthresh_pos hx
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hsmall_lt : (FiniteFp.smallestPosSubnormal.toVal : R) / 2 < (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp :=
    calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp := zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp := FloatFormat.zpow_max_exp_le_overflow_threshold
  have h_not_small : ¬|x| < FiniteFp.smallestPosSubnormal.toVal / 2 := by
    rw [abs_of_pos hx_pos]
    linarith
  have h_overflow : |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp := by
    rw [abs_of_pos hx_pos]
    exact hx
  have h_not_neg : ¬x < 0 := not_lt.mpr (le_of_lt hx_pos)
  simp [hx_ne, h_not_small, h_overflow, h_not_neg]

end RoundNearestTiesAwayFromZero

/-! ### Negative overflow lemmas for nearest modes -/

/-- roundNearestTiesToEven of a sufficiently negative value gives negative infinity. -/
theorem rnEven_neg_overflow [FloatFormat] (y : R) (hy_pos : 0 < y)
    (hy_ge : y ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp) :
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
  have hge : |-y| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp := by
    rw [habs_eq]; exact hy_ge
  simp only [hne, hsmall, hge, ↓reduceIte, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  congr 1; exact decide_eq_true (by linarith : -y < 0)

/-- roundNearestTiesAwayFromZero of a sufficiently negative value gives negative infinity. -/
theorem rnAway_neg_overflow [FloatFormat] (y : R) (hy_pos : 0 < y)
    (hy_ge : y ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp) :
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
  have hge : |-y| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp := by
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
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
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
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
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
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
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
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
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
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
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
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
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
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val < ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesToEven val = roundDown val := by
  rw [rnEven_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only; rw [if_pos hmid]

/-- TiesToEven: at midpoint with odd predecessor → rounds up -/
theorem rnEven_at_mid_odd_eq_roundUp [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
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
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
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
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
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
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val < ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesAwayFromZero val = roundDown val := by
  rw [rnAway_pos_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only; rw [if_pos hmid]

/-- Similar unfolding for roundNearestTiesToEven on negative values (-val where val > 0). -/
theorem rnEven_neg_unfold [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesToEven (-val) =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val > midpoint then -(Fp.finite succ_fp)
      else if val < midpoint then -(Fp.finite pred_fp)
      else if isEvenSignificand succ_fp then -(Fp.finite succ_fp)
      else -(Fp.finite pred_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  -- For negative -val: findPredecessor(-val) = -(findSuccessorPos val)
  --                    findSuccessor(-val) = Fp.finite (-(findPredecessorPos val))
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  -- Now findSuccessorPos val and findPredecessorPos val appear
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := Fp.finite.inj hpred_eq
  rw [hsucc_eq_fp, hpred_fp_eq]
  -- Need to reduce -Fp.finite succ_fp to Fp.finite (-succ_fp) for match
  simp only [Fp.neg_finite, FiniteFp.toVal_neg_eq_neg]
  -- Goal now has if-then-else with -val comparisons on LHS, val comparisons on RHS
  -- isEvenSignificand(-succ_fp) = isEvenSignificand(succ_fp)
  have heven_neg : isEvenSignificand (-succ_fp) = isEvenSignificand succ_fp := by
    simp [isEvenSignificand, FiniteFp.neg_def]
  rw [heven_neg]
  -- Split on all conditions and close with linarith
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all <;> linarith

/-- Similar unfolding for roundNearestTiesAwayFromZero on negative values. -/
theorem rnAway_neg_unfold [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesAwayFromZero (-val) =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val > midpoint then -(Fp.finite succ_fp)
      else if val < midpoint then -(Fp.finite pred_fp)
      else -(Fp.finite succ_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := Fp.finite.inj hpred_eq
  rw [hsucc_eq_fp, hpred_fp_eq]
  dsimp only
  simp only [Fp.neg_finite, FiniteFp.toVal_neg_eq_neg]
  congr 1
  · ext; constructor
    · intro h; linarith
    · intro h; linarith
  congr 1
  · ext; constructor
    · intro h; linarith
    · intro h; linarith
  -- tie: -val > 0 is false since hval_pos : 0 < val → -val < 0
  have h_neg_not_pos : ¬(-val > 0) := by linarith
  simp [h_neg_not_pos]

/-! ### Midpoint decision lemmas for negative values (-val where val > 0) -/

/-- TiesToEven neg: value above midpoint → result is -(roundUp val) -/
theorem rnEven_neg_above_mid [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val > ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesToEven (-val) = -(roundUp val) := by
  rw [rnEven_neg_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrU]
  dsimp only; rw [if_pos hmid]

/-- TiesToEven neg: value below midpoint → result is -(roundDown val) -/
theorem rnEven_neg_below_mid [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val < ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesToEven (-val) = -(roundDown val) := by
  rw [rnEven_neg_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only
  rw [if_neg (not_lt.mpr (le_of_lt hmid)), if_pos hmid]

/-- TiesToEven neg: at midpoint with even successor → result is -(roundUp val) -/
theorem rnEven_neg_at_mid_even_succ [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val = ((pred_fp.toVal : R) + succ_fp.toVal) / 2)
    (heven : isEvenSignificand succ_fp = true) :
    roundNearestTiesToEven (-val) = -(roundUp val) := by
  rw [rnEven_neg_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrU]
  dsimp only
  rw [if_neg (not_lt.mpr hmid.le), if_neg (not_lt.mpr hmid.ge), heven]; simp

/-- TiesToEven neg: at midpoint with odd successor → result is -(roundDown val) -/
theorem rnEven_neg_at_mid_odd_succ [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val = ((pred_fp.toVal : R) + succ_fp.toVal) / 2)
    (hodd : isEvenSignificand succ_fp = false) :
    roundNearestTiesToEven (-val) = -(roundDown val) := by
  rw [rnEven_neg_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only
  rw [if_neg (not_lt.mpr hmid.le), if_neg (not_lt.mpr hmid.ge), hodd]; simp

/-- TiesAway neg: value at or above midpoint → result is -(roundUp val) -/
theorem rnAway_neg_ge_mid [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val ≥ ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesAwayFromZero (-val) = -(roundUp val) := by
  rw [rnAway_neg_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrU]
  dsimp only
  by_cases hgt : val > ((pred_fp.toVal : R) + succ_fp.toVal) / 2
  · rw [if_pos hgt]
  · rw [if_neg hgt, if_neg (not_lt.mpr hmid)]

/-- TiesAway neg: value below midpoint → result is -(roundDown val) -/
theorem rnAway_neg_lt_mid [FloatFormat]
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid : val < ((pred_fp.toVal : R) + succ_fp.toVal) / 2) :
    roundNearestTiesAwayFromZero (-val) = -(roundDown val) := by
  rw [rnAway_neg_unfold val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU, hrD]
  dsimp only
  rw [if_neg (not_lt.mpr (le_of_lt hmid)), if_pos hmid]

/-! ### Midpoint lemma wrappers with explicit mid_val parameter

These variants take `mid_val` and a proof `hmid_eq : (pred + succ) / 2 = mid_val`
as separate arguments, so callers can provide the midpoint bridge and the comparison
as independent terms without inline tactic blocks. -/

/-- rnEven above midpoint → roundUp (with explicit mid_val) -/
theorem rnEven_above_mid_roundUp [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val > mid_val) :
    roundNearestTiesToEven val = roundUp val :=
  rnEven_above_mid_eq_roundUp val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

/-- rnEven below midpoint → roundDown (with explicit mid_val) -/
theorem rnEven_below_mid_roundDown [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val < mid_val) :
    roundNearestTiesToEven val = roundDown val :=
  rnEven_below_mid_eq_roundDown val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

/-- rnEven at midpoint, odd predecessor → roundUp (with explicit mid_val) -/
theorem rnEven_at_mid_odd_roundUp [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val = mid_val)
    (hodd : isEvenSignificand pred_fp = false) :
    roundNearestTiesToEven val = roundUp val :=
  rnEven_at_mid_odd_eq_roundUp val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid) hodd

/-- rnEven at midpoint, even predecessor → roundDown (with explicit mid_val) -/
theorem rnEven_at_mid_even_roundDown [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val = mid_val)
    (heven : isEvenSignificand pred_fp = true) :
    roundNearestTiesToEven val = roundDown val :=
  rnEven_at_mid_even_eq_roundDown val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid) heven

/-- rnAway at or above midpoint → roundUp (with explicit mid_val) -/
theorem rnAway_ge_mid_roundUp [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val ≥ mid_val) :
    roundNearestTiesAwayFromZero val = roundUp val :=
  rnAway_ge_mid_eq_roundUp val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

/-- rnAway below midpoint → roundDown (with explicit mid_val) -/
theorem rnAway_lt_mid_roundDown [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val < mid_val) :
    roundNearestTiesAwayFromZero val = roundDown val :=
  rnAway_lt_mid_eq_roundDown val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

/-- rnEven neg above midpoint (with explicit mid_val) -/
theorem rnEven_neg_above_mid' [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val > mid_val) :
    roundNearestTiesToEven (-val) = -(roundUp val) :=
  rnEven_neg_above_mid val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

/-- rnEven neg below midpoint (with explicit mid_val) -/
theorem rnEven_neg_below_mid' [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val < mid_val) :
    roundNearestTiesToEven (-val) = -(roundDown val) :=
  rnEven_neg_below_mid val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

/-- rnEven neg at midpoint, even successor (with explicit mid_val) -/
theorem rnEven_neg_at_mid_even_succ' [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val = mid_val)
    (heven : isEvenSignificand succ_fp = true) :
    roundNearestTiesToEven (-val) = -(roundUp val) :=
  rnEven_neg_at_mid_even_succ val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid) heven

/-- rnEven neg at midpoint, odd successor (with explicit mid_val) -/
theorem rnEven_neg_at_mid_odd_succ' [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val = mid_val)
    (hodd : isEvenSignificand succ_fp = false) :
    roundNearestTiesToEven (-val) = -(roundDown val) :=
  rnEven_neg_at_mid_odd_succ val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid) hodd

/-- rnAway neg at or above midpoint (with explicit mid_val) -/
theorem rnAway_neg_ge_mid' [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val ≥ mid_val) :
    roundNearestTiesAwayFromZero (-val) = -(roundUp val) :=
  rnAway_neg_ge_mid val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

/-- rnAway neg below midpoint (with explicit mid_val) -/
theorem rnAway_neg_lt_mid' [FloatFormat]
    (val mid_val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt : val < (2 - 2^(1-(FloatFormat.prec:ℤ))/2) * 2^FloatFormat.max_exp)
    (hrD : roundDown val = Fp.finite pred_fp) (hrU : roundUp val = Fp.finite succ_fp)
    (hmid_eq : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 = mid_val)
    (hmid : val < mid_val) :
    roundNearestTiesAwayFromZero (-val) = -(roundDown val) :=
  rnAway_neg_lt_mid val pred_fp succ_fp hval_pos hval_ge hval_lt hrD hrU
    (by rw [hmid_eq]; exact hmid)

theorem largestFiniteFloat_lt_overflow_threshold [FloatFormat] :
    FiniteFp.largestFiniteFloat.toVal <
    (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp := by
  rw [FiniteFp.largestFiniteFloat_toVal,
    show -(FloatFormat.prec : ℤ) + 1 = 1 - (FloatFormat.prec : ℤ) from by ring,
    mul_comm ((2:R) - _) _]
  exact mul_lt_mul_of_pos_left
    (by linarith [zpow_pos (by norm_num : (0:R) < 2) (1 - (FloatFormat.prec : ℤ))])
    (zpow_pos (by norm_num : (0:R) < 2) _)

theorem val_lt_thresh_of_roundUp_finite [FloatFormat]
    (val : R) (f : FiniteFp) (hval_pos : 0 < val)
    (hroundUp : roundUp val = Fp.finite f) :
    val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp := by
  have hfsp : findSuccessorPos val hval_pos = Fp.finite f := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  calc val ≤ f.toVal := findSuccessorPos_ge val hval_pos f hfsp
    _ ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
    _ < _ := largestFiniteFloat_lt_overflow_threshold

/-- When roundUp overflows and val < threshold, roundNearestTiesToEven returns roundDown. -/
theorem rnEven_pos_succ_overflow [FloatFormat]
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesToEven val = Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
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
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesAwayFromZero val = Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
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

/-- When roundUp overflows for val > 0 and val < threshold,
    roundNearestTiesToEven(-val) returns Fp.finite (-pred_fp). -/
theorem rnEven_neg_succ_overflow [FloatFormat]
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesToEven (-val) = Fp.finite (-pred_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf, hpred_fp_eq]

/-- When roundUp overflows for val > 0 and val < threshold,
    roundNearestTiesAwayFromZero(-val) returns Fp.finite (-pred_fp). -/
theorem rnAway_neg_succ_overflow [FloatFormat]
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesAwayFromZero (-val) = Fp.finite (-pred_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf, hpred_fp_eq]

end Rounding
