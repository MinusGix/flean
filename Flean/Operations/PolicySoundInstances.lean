import Flean.Operations.RoundIntSig
import Flean.Operations.RoundIntSigPolicySound
import Flean.Rounding.PolicyInstances
import Mathlib.Tactic.Linarith

/-!
Policy-driven soundness instances that live at the operations layer.

This file currently provides `RModeSticky` instances for all concrete
rounding-policy markers.
-/

section PolicySoundInstances

variable [FloatFormat]

private theorem odd_index_large_of_q_lower (q : ℕ)
    (hq_lower : 2 ^ (FloatFormat.prec.toNat + 2) ≤ q) :
    2 ^ (FloatFormat.prec.toNat + 3) < 2 * q + 1 := by
  have hmul : 2 * 2 ^ (FloatFormat.prec.toNat + 2) ≤ 2 * q :=
    Nat.mul_le_mul_left 2 hq_lower
  have hpow : 2 ^ (FloatFormat.prec.toNat + 3) = 2 * 2 ^ (FloatFormat.prec.toNat + 2) := by
    rw [show FloatFormat.prec.toNat + 3 = (FloatFormat.prec.toNat + 2) + 1 by omega,
      Nat.pow_succ, Nat.mul_comm]
  have hle : 2 ^ (FloatFormat.prec.toNat + 3) ≤ 2 * q := by
    simpa [hpow] using hmul
  omega

private theorem sticky_interval_to_odd {R : Type*} [Field R] [LinearOrder R]
    {q : ℕ} {e_base : ℤ} {x : R}
    (hx : inStickyInterval (R := R) q e_base x) :
    inOddInterval (R := R) (2 * q + 1) e_base x := by
  rcases hx with ⟨hx_lo, hx_hi⟩
  constructor
  · calc
      oddIntervalLo (R := R) (2 * q + 1) e_base
          = (2 * (q : R)) * (2 : R) ^ e_base := by
              unfold oddIntervalLo
              push_cast
              ring
      _ < x := hx_lo
  · calc
      x < (2 * ((q : R) + 1)) * (2 : R) ^ e_base := hx_hi
      _ = oddIntervalHi (R := R) (2 * q + 1) e_base := by
            unfold oddIntervalHi
            push_cast
            ring

private theorem stickyAbs_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (q : ℕ) (e_base : ℤ) :
    0 < stickyAbs (R := R) q e_base := by
  unfold stickyAbs stickyMag
  have hE_pos : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0 : R) < 2) _
  have hcoeff_pos : (0 : R) < ((2 * q + 1 : ℕ) : R) := by
    exact_mod_cast (Nat.succ_pos (2 * q))
  exact mul_pos hcoeff_pos hE_pos

private theorem abs_exact_pos_of_inSticky {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {q : ℕ} {e_base : ℤ} {abs_exact : R}
    (h_exact_in : inStickyInterval (R := R) q e_base abs_exact) :
    0 < abs_exact := by
  rcases h_exact_in with ⟨hlo, _⟩
  have hE_pos : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0 : R) < 2) _
  have hcoeff_nonneg : (0 : R) ≤ (2 * (q : R)) := by positivity
  have hlo_nonneg : (0 : R) ≤ (2 * (q : R)) * (2 : R) ^ e_base :=
    mul_nonneg hcoeff_nonneg hE_pos.le
  linarith

private theorem sticky_mid_in_odd {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (q : ℕ) (e_base : ℤ) :
    inOddInterval (R := R) (2 * q + 1) e_base (stickyAbs (R := R) q e_base) := by
  have hE_pos : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0 : R) < 2) _
  have h_mid_sticky : inStickyInterval (R := R) q e_base (stickyAbs (R := R) q e_base) := by
    unfold inStickyInterval stickyAbs stickyMag
    constructor
    · have hcoeff : (2 * (q : R)) < ((2 * q + 1 : ℕ) : R) := by
        exact_mod_cast (Nat.lt_succ_self (2 * q))
      exact mul_lt_mul_of_pos_right hcoeff hE_pos
    · have hcoeff : (((2 * q + 1 : ℕ) : R)) < 2 * ((q : R) + 1) := by
        have hcoeff_nat : 2 * q + 1 < 2 * (q + 1) := by omega
        have hcoeff' : (((2 * q + 1 : ℕ) : R)) < ((2 * (q + 1) : ℕ) : R) := by
          exact_mod_cast hcoeff_nat
        simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hcoeff'
      exact mul_lt_mul_of_pos_right hcoeff hE_pos
  exact sticky_interval_to_odd (R := R) h_mid_sticky

section StickyInstances

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModeSticky R where
  round_eq_on_sticky_interval := by
    letI : RMode R := inferInstance
    intro sign q e_base hq_lower abs_exact h_exact_in
    let n : ℕ := 2 * q + 1
    have hn_odd : n % 2 = 1 := by
      unfold n
      omega
    have hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n := by
      unfold n
      exact odd_index_large_of_q_lower q hq_lower
    have h_mid_in : inOddInterval (R := R) n e_base (stickyAbs (R := R) q e_base) := by
      simpa [n] using sticky_mid_in_odd (R := R) q e_base
    have h_exact_in_odd : inOddInterval (R := R) n e_base abs_exact := by
      simpa [n] using sticky_interval_to_odd (R := R) h_exact_in
    cases sign with
    | false =>
      simpa [RMode.round] using
        (roundDown_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd)
    | true =>
      have hmid_pos : 0 < stickyAbs (R := R) q e_base := stickyAbs_pos (R := R) q e_base
      have habs_pos : 0 < abs_exact := abs_exact_pos_of_inSticky (R := R) h_exact_in
      have hmid_ne : stickyAbs (R := R) q e_base ≠ 0 := ne_of_gt hmid_pos
      have habs_ne : abs_exact ≠ 0 := ne_of_gt habs_pos
      have h_up_eq : roundUp (stickyAbs (R := R) q e_base) = roundUp abs_exact := by
        exact roundUp_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd
      have hneg :
          roundDown (-(stickyAbs (R := R) q e_base)) = roundDown (-abs_exact) := by
        calc
          roundDown (-(stickyAbs (R := R) q e_base)) = -roundUp (stickyAbs (R := R) q e_base) := by
            simpa using (roundDown_neg_eq_neg_roundUp (R := R) (stickyAbs (R := R) q e_base) hmid_ne)
          _ = -roundUp abs_exact := by rw [h_up_eq]
          _ = roundDown (-abs_exact) := by
            symm
            simpa using (roundDown_neg_eq_neg_roundUp (R := R) abs_exact habs_ne)
      simpa [RMode.round] using hneg

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModeSticky R where
  round_eq_on_sticky_interval := by
    letI : RMode R := inferInstance
    intro sign q e_base hq_lower abs_exact h_exact_in
    let n : ℕ := 2 * q + 1
    have hn_odd : n % 2 = 1 := by
      unfold n
      omega
    have hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n := by
      unfold n
      exact odd_index_large_of_q_lower q hq_lower
    have h_mid_in : inOddInterval (R := R) n e_base (stickyAbs (R := R) q e_base) := by
      simpa [n] using sticky_mid_in_odd (R := R) q e_base
    have h_exact_in_odd : inOddInterval (R := R) n e_base abs_exact := by
      simpa [n] using sticky_interval_to_odd (R := R) h_exact_in
    cases sign with
    | false =>
      simpa [RMode.round] using
        (roundUp_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd)
    | true =>
      have hmid_pos : 0 < stickyAbs (R := R) q e_base := stickyAbs_pos (R := R) q e_base
      have habs_pos : 0 < abs_exact := abs_exact_pos_of_inSticky (R := R) h_exact_in
      have hmid_ne : stickyAbs (R := R) q e_base ≠ 0 := ne_of_gt hmid_pos
      have habs_ne : abs_exact ≠ 0 := ne_of_gt habs_pos
      have h_down_eq : roundDown (stickyAbs (R := R) q e_base) = roundDown abs_exact := by
        exact roundDown_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd
      have hneg :
          roundUp (-(stickyAbs (R := R) q e_base)) = roundUp (-abs_exact) := by
        calc
          roundUp (-(stickyAbs (R := R) q e_base)) = -roundDown (stickyAbs (R := R) q e_base) := by
            simpa using (roundUp_neg_eq_neg_roundDown (R := R) (stickyAbs (R := R) q e_base) hmid_ne)
          _ = -roundDown abs_exact := by rw [h_down_eq]
          _ = roundUp (-abs_exact) := by
            symm
            simpa using (roundUp_neg_eq_neg_roundDown (R := R) abs_exact habs_ne)
      simpa [RMode.round] using hneg

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModeSticky R where
  round_eq_on_sticky_interval := by
    letI : RMode R := inferInstance
    intro sign q e_base hq_lower abs_exact h_exact_in
    let n : ℕ := 2 * q + 1
    have hn_odd : n % 2 = 1 := by
      unfold n
      omega
    have hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n := by
      unfold n
      exact odd_index_large_of_q_lower q hq_lower
    have h_mid_in : inOddInterval (R := R) n e_base (stickyAbs (R := R) q e_base) := by
      simpa [n] using sticky_mid_in_odd (R := R) q e_base
    have h_exact_in_odd : inOddInterval (R := R) n e_base abs_exact := by
      simpa [n] using sticky_interval_to_odd (R := R) h_exact_in
    cases sign with
    | false =>
      simpa [RMode.round] using
        (roundTowardZero_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd)
    | true =>
      have hmid_pos : 0 < stickyAbs (R := R) q e_base := stickyAbs_pos (R := R) q e_base
      have habs_pos : 0 < abs_exact := abs_exact_pos_of_inSticky (R := R) h_exact_in
      have hmid_ne : stickyAbs (R := R) q e_base ≠ 0 := ne_of_gt hmid_pos
      have habs_ne : abs_exact ≠ 0 := ne_of_gt habs_pos
      have h_tz_eq : roundTowardZero (stickyAbs (R := R) q e_base) = roundTowardZero abs_exact := by
        exact roundTowardZero_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd
      have hneg :
          roundTowardZero (-(stickyAbs (R := R) q e_base)) = roundTowardZero (-abs_exact) := by
        calc
          roundTowardZero (-(stickyAbs (R := R) q e_base)) = -roundTowardZero (stickyAbs (R := R) q e_base) := by
            simpa using (roundTowardZero_neg_eq_neg (R := R) (stickyAbs (R := R) q e_base) hmid_ne)
          _ = -roundTowardZero abs_exact := by rw [h_tz_eq]
          _ = roundTowardZero (-abs_exact) := by
            symm
            simpa using (roundTowardZero_neg_eq_neg (R := R) abs_exact habs_ne)
      simpa [RMode.round] using hneg

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeSticky R where
  round_eq_on_sticky_interval := by
    letI : RMode R := inferInstance
    intro sign q e_base hq_lower abs_exact h_exact_in
    let n : ℕ := 2 * q + 1
    have hn_odd : n % 2 = 1 := by
      unfold n
      omega
    have hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n := by
      unfold n
      exact odd_index_large_of_q_lower q hq_lower
    have h_mid_in : inOddInterval (R := R) n e_base (stickyAbs (R := R) q e_base) := by
      simpa [n] using sticky_mid_in_odd (R := R) q e_base
    have h_exact_in_odd : inOddInterval (R := R) n e_base abs_exact := by
      simpa [n] using sticky_interval_to_odd (R := R) h_exact_in
    cases sign with
    | false =>
      simpa [RMode.round] using
        (rnEven_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd)
    | true =>
      have hmid_pos : 0 < stickyAbs (R := R) q e_base := stickyAbs_pos (R := R) q e_base
      have habs_pos : 0 < abs_exact := abs_exact_pos_of_inSticky (R := R) h_exact_in
      have hmid_ne : stickyAbs (R := R) q e_base ≠ 0 := ne_of_gt hmid_pos
      have habs_ne : abs_exact ≠ 0 := ne_of_gt habs_pos
      have h_nearest_eq :
          roundNearestTiesToEven (stickyAbs (R := R) q e_base) = roundNearestTiesToEven abs_exact := by
        exact rnEven_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd
      have hneg :
          roundNearestTiesToEven (-(stickyAbs (R := R) q e_base)) =
            roundNearestTiesToEven (-abs_exact) := by
        calc
          roundNearestTiesToEven (-(stickyAbs (R := R) q e_base)) =
              -roundNearestTiesToEven (stickyAbs (R := R) q e_base) := by
                simpa using (rnEven_neg_eq_neg (R := R) (stickyAbs (R := R) q e_base) hmid_ne)
          _ = -roundNearestTiesToEven abs_exact := by rw [h_nearest_eq]
          _ = roundNearestTiesToEven (-abs_exact) := by
                symm
                simpa using (rnEven_neg_eq_neg (R := R) abs_exact habs_ne)
      simpa [RMode.round] using hneg

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeSticky R where
  round_eq_on_sticky_interval := by
    letI : RMode R := inferInstance
    intro sign q e_base hq_lower abs_exact h_exact_in
    let n : ℕ := 2 * q + 1
    have hn_odd : n % 2 = 1 := by
      unfold n
      omega
    have hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n := by
      unfold n
      exact odd_index_large_of_q_lower q hq_lower
    have h_mid_in : inOddInterval (R := R) n e_base (stickyAbs (R := R) q e_base) := by
      simpa [n] using sticky_mid_in_odd (R := R) q e_base
    have h_exact_in_odd : inOddInterval (R := R) n e_base abs_exact := by
      simpa [n] using sticky_interval_to_odd (R := R) h_exact_in
    cases sign with
    | false =>
      simpa [RMode.round] using
        (rnAway_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd)
    | true =>
      have hmid_pos : 0 < stickyAbs (R := R) q e_base := stickyAbs_pos (R := R) q e_base
      have habs_pos : 0 < abs_exact := abs_exact_pos_of_inSticky (R := R) h_exact_in
      have hmid_ne : stickyAbs (R := R) q e_base ≠ 0 := ne_of_gt hmid_pos
      have habs_ne : abs_exact ≠ 0 := ne_of_gt habs_pos
      have h_nearest_eq :
          roundNearestTiesAwayFromZero (stickyAbs (R := R) q e_base) = roundNearestTiesAwayFromZero abs_exact := by
        exact rnAway_eq_on_odd_interval (R := R) hn_odd hn_large h_mid_in h_exact_in_odd
      have hneg :
          roundNearestTiesAwayFromZero (-(stickyAbs (R := R) q e_base)) =
            roundNearestTiesAwayFromZero (-abs_exact) := by
        calc
          roundNearestTiesAwayFromZero (-(stickyAbs (R := R) q e_base)) =
              -roundNearestTiesAwayFromZero (stickyAbs (R := R) q e_base) := by
                simpa using (rnAway_neg_eq_neg (R := R) (stickyAbs (R := R) q e_base) hmid_ne)
          _ = -roundNearestTiesAwayFromZero abs_exact := by rw [h_nearest_eq]
          _ = roundNearestTiesAwayFromZero (-abs_exact) := by
                symm
                simpa using (rnAway_neg_eq_neg (R := R) abs_exact habs_ne)
      simpa [RMode.round] using hneg

end StickyInstances

end PolicySoundInstances
