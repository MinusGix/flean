import Flean.Rounding.ModeClass
import Mathlib.Tactic.Linarith

/-!
Concrete policy-driven instances for `RMode`/`RModeExec` and their observable laws.

Policy selection is marker-type driven via `[UseRoundingPolicy P]`.
-/

section PolicyInstances

variable [FloatFormat]

instance (priority := 100) instRModeCOfComponents (R : Type*)
    [Field R] [Preorder R] [RMode R]
    [RModeZero R] [RModeMono R] [RModeIdem R] : RModeC R :=
  {}

private def shouldRoundTowardNeg (sign : Bool) (_q r _shift : ℕ) : Bool :=
  if r = 0 then false else sign

private def shouldRoundTowardPos (sign : Bool) (_q r _shift : ℕ) : Bool :=
  if r = 0 then false else !sign

private def shouldRoundTowardZero (_sign : Bool) (_q _r _shift : ℕ) : Bool :=
  false

private def shouldRoundNearestEven (_sign : Bool) (q r shift : ℕ) : Bool :=
  if r = 0 then false
  else
    let half := 2 ^ (shift - 1)
    if r > half then true
    else if r < half then false
    else q % 2 ≠ 0

private def shouldRoundNearestAway (_sign : Bool) (_q r shift : ℕ) : Bool :=
  if r = 0 then false
  else
    let half := 2 ^ (shift - 1)
    r ≥ half

section ExecInstances

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModeExec where
  shouldRoundUp := shouldRoundTowardNeg
  handleOverflow := fun sign => if sign then Fp.infinite true else Fp.finite FiniteFp.largestFiniteFloat
  cancelSignOnExactZero := true

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModeExec where
  shouldRoundUp := shouldRoundTowardPos
  handleOverflow := fun sign => if sign then Fp.finite (-FiniteFp.largestFiniteFloat) else Fp.infinite false

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModeExec where
  shouldRoundUp := shouldRoundTowardZero
  handleOverflow := fun sign =>
    if sign then Fp.finite (-FiniteFp.largestFiniteFloat) else Fp.finite FiniteFp.largestFiniteFloat

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeExec where
  shouldRoundUp := shouldRoundNearestEven
  handleOverflow := fun sign => Fp.infinite sign

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeExec where
  shouldRoundUp := shouldRoundNearestAway
  handleOverflow := fun sign => Fp.infinite sign

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeTieEven where
  tie_round_up_iff_odd := by
    intro sign q shift hshift
    cases shift with
    | zero =>
      cases (Nat.not_lt_zero 0 hshift)
    | succ k =>
      simp [RModeExec.shouldRoundUp, shouldRoundNearestEven]

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeTieAway where
  tie_round_up := by
    intro sign q shift hshift
    cases shift with
    | zero =>
      cases (Nat.not_lt_zero 0 hshift)
    | succ k =>
      simp [RModeExec.shouldRoundUp, shouldRoundNearestAway]

end ExecInstances

private theorem rnEven_le_two_x_sub_pred {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (x : R) (hxpos : 0 < x) (hx : isNormalRange x)
    (f : FiniteFp) (hf : roundNearestTiesToEven x = Fp.finite f) :
    (f.toVal : R) ≤ 2 * x - (findPredecessorPos x hxpos).toVal := by
  have hrd : roundDown x = Fp.finite (findPredecessorPos x hxpos) := by
    simpa [roundDown] using (findPredecessor_pos_eq x hxpos)
  rcases roundNearestTiesToEven_is_roundDown_or_roundUp x hx f hf with hdown | hup
  · have hpred_eq : findPredecessorPos x hxpos = f := by
      apply Fp.finite.inj
      calc
        Fp.finite (findPredecessorPos x hxpos) = roundDown x := hrd.symm
        _ = Fp.finite f := hdown
    have hpred_le : ((findPredecessorPos x hxpos).toVal : R) ≤ x :=
      findPredecessorPos_le x hxpos
    have hf_le : (f.toVal : R) ≤ x := by
      simpa [hpred_eq] using hpred_le
    linarith
  · by_cases hpred_eq : findPredecessorPos x hxpos = f
    · have hpred_le : ((findPredecessorPos x hxpos).toVal : R) ≤ x :=
        findPredecessorPos_le x hxpos
      have hf_le : (f.toVal : R) ≤ x := by
        simpa [hpred_eq] using hpred_le
      linarith
    · have hx_lt_thresh : x < FloatFormat.overflowThreshold R :=
        val_lt_thresh_of_roundUp_finite x f hxpos hup
      let mid : R := (((findPredecessorPos x hxpos).toVal : R) + f.toVal) / 2
      have h_not_lt_mid : ¬x < mid := by
        intro hlt
        have hnear_down : roundNearestTiesToEven x = roundDown x :=
          rnEven_below_mid_roundDown x mid (findPredecessorPos x hxpos) f
            hxpos hx_lt_thresh hrd hup (by simp [mid]) hlt
        have hrd_eq_hup : roundDown x = roundUp x := by
          calc
            roundDown x = roundNearestTiesToEven x := hnear_down.symm
            _ = Fp.finite f := hf
            _ = roundUp x := hup.symm
        have hpred_eq' : findPredecessorPos x hxpos = f :=
          Fp.finite.inj (by simpa [hrd, hup] using hrd_eq_hup)
        exact hpred_eq hpred_eq'
      have hmid_le : (((findPredecessorPos x hxpos).toVal : R) + f.toVal) / 2 ≤ x := by
        simpa [mid] using (not_lt.mp h_not_lt_mid)
      linarith

private theorem rnAway_le_two_x_sub_pred {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (x : R) (hxpos : 0 < x) (hx : isNormalRange x)
    (f : FiniteFp) (hf : roundNearestTiesAwayFromZero x = Fp.finite f) :
    (f.toVal : R) ≤ 2 * x - (findPredecessorPos x hxpos).toVal := by
  have hrd : roundDown x = Fp.finite (findPredecessorPos x hxpos) := by
    simpa [roundDown] using (findPredecessor_pos_eq x hxpos)
  rcases roundNearestTiesAwayFromZero_is_roundDown_or_roundUp x hx f hf with hdown | hup
  · have hpred_eq : findPredecessorPos x hxpos = f := by
      apply Fp.finite.inj
      calc
        Fp.finite (findPredecessorPos x hxpos) = roundDown x := hrd.symm
        _ = Fp.finite f := hdown
    have hpred_le : ((findPredecessorPos x hxpos).toVal : R) ≤ x :=
      findPredecessorPos_le x hxpos
    have hf_le : (f.toVal : R) ≤ x := by
      simpa [hpred_eq] using hpred_le
    linarith
  · by_cases hpred_eq : findPredecessorPos x hxpos = f
    · have hpred_le : ((findPredecessorPos x hxpos).toVal : R) ≤ x :=
        findPredecessorPos_le x hxpos
      have hf_le : (f.toVal : R) ≤ x := by
        simpa [hpred_eq] using hpred_le
      linarith
    · have hx_lt_thresh : x < FloatFormat.overflowThreshold R :=
        val_lt_thresh_of_roundUp_finite x f hxpos hup
      let mid : R := (((findPredecessorPos x hxpos).toVal : R) + f.toVal) / 2
      have h_not_lt_mid : ¬x < mid := by
        intro hlt
        have hnear_down : roundNearestTiesAwayFromZero x = roundDown x :=
          rnAway_lt_mid_roundDown x mid (findPredecessorPos x hxpos) f
            hxpos hx_lt_thresh hrd hup (by simp [mid]) hlt
        have hrd_eq_hup : roundDown x = roundUp x := by
          calc
            roundDown x = roundNearestTiesAwayFromZero x := hnear_down.symm
            _ = Fp.finite f := hf
            _ = roundUp x := hup.symm
        have hpred_eq' : findPredecessorPos x hxpos = f :=
          Fp.finite.inj (by simpa [hrd, hup] using hrd_eq_hup)
        exact hpred_eq hpred_eq'
      have hmid_le : (((findPredecessorPos x hxpos).toVal : R) + f.toVal) / 2 ≤ x := by
        simpa [mid] using (not_lt.mp h_not_lt_mid)
      linarith

section TowardNeg

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
instance [UseRoundingPolicy RoundTowardNegPolicy] : RMode R where
  round := roundDown

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModeZero R where
  round_zero := by
    simpa [RMode.round] using (roundDown_zero (R := R))

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModeMono R where
  round_mono := by
    intro x y hxy
    simpa [RMode.round] using (roundDown_mono (R := R) hxy)

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModeIdem R where
  round_idempotent := by
    intro f hf
    simpa [RMode.round] using (roundDown_idempotent (R := R) f hf)

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModeExecSound R where
  chooseUp_exact := by
    intro sign q shift
    simp [RModeExec.shouldRoundUp, shouldRoundTowardNeg]
  overflow_round_characterization := by
    intro sign x hx
    have hx_pos : (0 : R) < x := lt_of_lt_of_le FloatFormat.overflow_threshold_pos hx
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hx_gt_lff : (FiniteFp.largestFiniteFloat.toVal : R) < x :=
      lt_of_lt_of_le largestFiniteFloat_lt_overflow_threshold hx
    cases sign with
    | false =>
      have hrd : roundDown x = Fp.finite FiniteFp.largestFiniteFloat :=
        roundDown_gt_lff x hx_pos hx_gt_lff
      simpa [RModeExec.handleOverflow, RMode.round] using hrd.symm
    | true =>
      have hru : roundUp x = Fp.infinite false :=
        roundUp_gt_largestFiniteFloat x hx_pos hx_gt_lff
      have hrd_neg : roundDown (-x) = -(roundUp x) :=
        roundDown_neg_eq_neg_roundUp x hx_ne
      simp [RModeExec.handleOverflow, RMode.round, hru, hrd_neg, Fp.neg_def]

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModePolicyTag R where
  kind := .towardNeg

instance [UseRoundingPolicy RoundTowardNegPolicy] : RModePolicySpec R where
  kind := .towardNeg
  round_eq_policy := by
    intro x
    rfl
  shouldRoundUp_eq_policy := by
    intro sign q r shift
    rfl
  handleOverflow_eq_policy := by
    intro sign
    rfl
  cancelSignOnExactZero_eq_policy := by
    rfl

end TowardNeg

section TowardPos

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
instance [UseRoundingPolicy RoundTowardPosPolicy] : RMode R where
  round := roundUp

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModeZero R where
  round_zero := by
    simpa [RMode.round] using (roundUp_zero (R := R))

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModeMono R where
  round_mono := by
    intro x y hxy
    simpa [RMode.round] using (roundUp_mono (R := R) hxy)

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModeIdem R where
  round_idempotent := by
    intro f hf
    simpa [RMode.round] using (roundUp_idempotent (R := R) f hf)

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModeExecSound R where
  chooseUp_exact := by
    intro sign q shift
    simp [RModeExec.shouldRoundUp, shouldRoundTowardPos]
  overflow_round_characterization := by
    intro sign x hx
    have hx_pos : (0 : R) < x := lt_of_lt_of_le FloatFormat.overflow_threshold_pos hx
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hx_gt_lff : (FiniteFp.largestFiniteFloat.toVal : R) < x :=
      lt_of_lt_of_le largestFiniteFloat_lt_overflow_threshold hx
    have hrd : roundDown x = Fp.finite FiniteFp.largestFiniteFloat :=
      roundDown_gt_lff x hx_pos hx_gt_lff
    cases sign with
    | false =>
      have hru : roundUp x = Fp.infinite false :=
        roundUp_gt_largestFiniteFloat x hx_pos hx_gt_lff
      simpa [RModeExec.handleOverflow, RMode.round] using hru.symm
    | true =>
      have hru_neg : roundUp (-x) = Fp.finite (-FiniteFp.largestFiniteFloat) := by
        have hsym : roundUp (-x) = -(roundDown x) :=
          roundUp_neg_eq_neg_roundDown x hx_ne
        simp [hsym, hrd, Fp.neg_def]
      simpa [RModeExec.handleOverflow, RMode.round] using hru_neg.symm

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModePolicyTag R where
  kind := .towardPos

instance [UseRoundingPolicy RoundTowardPosPolicy] : RModePolicySpec R where
  kind := .towardPos
  round_eq_policy := by
    intro x
    rfl
  shouldRoundUp_eq_policy := by
    intro sign q r shift
    rfl
  handleOverflow_eq_policy := by
    intro sign
    rfl
  cancelSignOnExactZero_eq_policy := by
    rfl

end TowardPos

section TowardZero

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
instance [UseRoundingPolicy RoundTowardZeroPolicy] : RMode R where
  round := roundTowardZero

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModeZero R where
  round_zero := by
    simpa [RMode.round] using (roundTowardZero_zero (R := R))

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModeMono R where
  round_mono := by
    intro x y hxy
    simpa [RMode.round] using (roundTowardZero_mono (R := R) hxy)

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModeIdem R where
  round_idempotent := by
    intro f hf
    simpa [RMode.round] using (roundTowardZero_idempotent (R := R) f hf)

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModeConj R where
  round_neg := by
    intro x hx
    simpa [RMode.round] using (roundTowardZero_neg_eq_neg (R := R) x hx)

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModeExecSound R where
  chooseUp_exact := by
    intro sign q shift
    simp [RModeExec.shouldRoundUp, shouldRoundTowardZero]
  overflow_round_characterization := by
    intro sign x hx
    have hx_pos : (0 : R) < x := lt_of_lt_of_le FloatFormat.overflow_threshold_pos hx
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hx_gt_lff : (FiniteFp.largestFiniteFloat.toVal : R) < x :=
      lt_of_lt_of_le largestFiniteFloat_lt_overflow_threshold hx
    have hrd : roundDown x = Fp.finite FiniteFp.largestFiniteFloat :=
      roundDown_gt_lff x hx_pos hx_gt_lff
    cases sign with
    | false =>
      have htz : roundTowardZero x = roundDown x := roundTowardZero_pos_eq x hx_pos
      simpa [RModeExec.handleOverflow, RMode.round, htz] using hrd.symm
    | true =>
      have htz : roundTowardZero (-x) = roundUp (-x) :=
        roundTowardZero_neg_eq (-x) (neg_lt_zero.mpr hx_pos)
      have hru_neg : roundUp (-x) = Fp.finite (-FiniteFp.largestFiniteFloat) := by
        have hsym : roundUp (-x) = -(roundDown x) :=
          roundUp_neg_eq_neg_roundDown x hx_ne
        simp [hsym, hrd, Fp.neg_def]
      simpa [RModeExec.handleOverflow, RMode.round, htz] using hru_neg.symm

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModePolicyTag R where
  kind := .towardZero

instance [UseRoundingPolicy RoundTowardZeroPolicy] : RModePolicySpec R where
  kind := .towardZero
  round_eq_policy := by
    intro x
    rfl
  shouldRoundUp_eq_policy := by
    intro sign q r shift
    rfl
  handleOverflow_eq_policy := by
    intro sign
    rfl
  cancelSignOnExactZero_eq_policy := by
    rfl

end TowardZero

section NearestEven

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
instance [UseRoundingPolicy RoundNearestEvenPolicy] : RMode R where
  round := roundNearestTiesToEven

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeZero R where
  round_zero := by
    simpa [RMode.round] using (roundNearestTiesToEven_zero (R := R))

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeMono R where
  round_mono := by
    intro x y hxy
    simpa [RMode.round] using (roundNearestTE_mono (R := R) hxy)

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeIdem R where
  round_idempotent := by
    intro f hf
    simpa [RMode.round] using (roundNearestTiesToEven_idempotent (R := R) f hf)

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeConj R where
  round_neg := by
    intro x hx
    simpa [RMode.round] using (rnEven_neg_eq_neg (R := R) x hx)

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeNearest R where
  toRModeC := inferInstance
  round_eq_roundDown_or_roundUp := by
    intro x
    simpa [RMode.round] using (rnTE_eq_roundDown_or_roundUp' (R := R) x)
  roundDown_le_round := by
    intro x
    simpa [RMode.round] using (roundDown_le_roundNearestTE (R := R) x)
  round_le_roundUp := by
    intro x
    simpa [RMode.round] using (roundNearestTE_le_roundUp (R := R) x)
  overflow_pos_inf := by
    intro x hx
    simpa [RMode.round] using (rnEven_ge_inf (R := R) x hx)
  round_le_two_x_sub_pred := by
    intro x hxpos hx f hf
    have hf' : roundNearestTiesToEven x = Fp.finite f := by
      simpa [RMode.round] using hf
    simpa [RMode.round] using (rnEven_le_two_x_sub_pred (R := R) x hxpos hx f hf')

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModeExecSound R where
  chooseUp_exact := by
    intro sign q shift
    cases shift with
    | zero =>
      simp [RModeExec.shouldRoundUp, shouldRoundNearestEven]
    | succ k =>
      simp [RModeExec.shouldRoundUp, shouldRoundNearestEven]
  overflow_round_characterization := by
    intro sign x hx
    have hx_pos : (0 : R) < x := lt_of_lt_of_le FloatFormat.overflow_threshold_pos hx
    cases sign with
    | false =>
      simpa [RModeExec.handleOverflow, RMode.round] using (rnEven_ge_inf (R := R) x hx).symm
    | true =>
      simpa [RModeExec.handleOverflow, RMode.round] using
        (rnEven_neg_overflow (R := R) x hx_pos hx).symm

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModePolicyTag R where
  kind := .nearestEven

instance [UseRoundingPolicy RoundNearestEvenPolicy] : RModePolicySpec R where
  kind := .nearestEven
  round_eq_policy := by
    intro x
    rfl
  shouldRoundUp_eq_policy := by
    intro sign q r shift
    rfl
  handleOverflow_eq_policy := by
    intro sign
    rfl
  cancelSignOnExactZero_eq_policy := by
    rfl

end NearestEven

section NearestAway

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
instance [UseRoundingPolicy RoundNearestAwayPolicy] : RMode R where
  round := roundNearestTiesAwayFromZero

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeZero R where
  round_zero := by
    simpa [RMode.round] using (roundNearestTiesAwayFromZero_zero (R := R))

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeMono R where
  round_mono := by
    intro x y hxy
    simpa [RMode.round] using (roundNearestTA_mono (R := R) hxy)

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeIdem R where
  round_idempotent := by
    intro f hf
    simpa [RMode.round] using (roundNearestTiesAwayFromZero_idempotent (R := R) f hf)

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeConj R where
  round_neg := by
    intro x hx
    simpa [RMode.round] using (rnAway_neg_eq_neg (R := R) x hx)

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeNearest R where
  toRModeC := inferInstance
  round_eq_roundDown_or_roundUp := by
    intro x
    simpa [RMode.round] using (rnTA_eq_roundDown_or_roundUp' (R := R) x)
  roundDown_le_round := by
    intro x
    simpa [RMode.round] using (roundDown_le_roundNearestTA (R := R) x)
  round_le_roundUp := by
    intro x
    simpa [RMode.round] using (roundNearestTA_le_roundUp (R := R) x)
  overflow_pos_inf := by
    intro x hx
    simpa [RMode.round] using (rnAway_ge_inf (R := R) x hx)
  round_le_two_x_sub_pred := by
    intro x hxpos hx f hf
    have hf' : roundNearestTiesAwayFromZero x = Fp.finite f := by
      simpa [RMode.round] using hf
    simpa [RMode.round] using (rnAway_le_two_x_sub_pred (R := R) x hxpos hx f hf')

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModeExecSound R where
  chooseUp_exact := by
    intro sign q shift
    cases shift with
    | zero =>
      simp [RModeExec.shouldRoundUp, shouldRoundNearestAway]
    | succ k =>
      simp [RModeExec.shouldRoundUp, shouldRoundNearestAway]
  overflow_round_characterization := by
    intro sign x hx
    have hx_pos : (0 : R) < x := lt_of_lt_of_le FloatFormat.overflow_threshold_pos hx
    cases sign with
    | false =>
      simpa [RModeExec.handleOverflow, RMode.round] using (rnAway_ge_inf (R := R) x hx).symm
    | true =>
      simpa [RModeExec.handleOverflow, RMode.round] using
        (rnAway_neg_overflow (R := R) x hx_pos hx).symm

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModePolicyTag R where
  kind := .nearestAway

instance [UseRoundingPolicy RoundNearestAwayPolicy] : RModePolicySpec R where
  kind := .nearestAway
  round_eq_policy := by
    intro x
    rfl
  shouldRoundUp_eq_policy := by
    intro sign q r shift
    rfl
  handleOverflow_eq_policy := by
    intro sign
    rfl
  cancelSignOnExactZero_eq_policy := by
    rfl

end NearestAway

end PolicyInstances
