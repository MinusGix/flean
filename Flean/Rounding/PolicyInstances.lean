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

private theorem rnEven_ge_two_x_sub_succ {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (x : R) (hxpos : 0 < x) (hx : isNormalRange x)
    (f : FiniteFp) (hf : roundNearestTiesToEven x = Fp.finite f)
    (succ : FiniteFp) (hsucc : findSuccessorPos x hxpos = Fp.finite succ) :
    (2 * x - succ.toVal : R) ≤ f.toVal := by
  have hru : roundUp x = Fp.finite succ := by
    rw [roundUp, findSuccessor_pos_eq x hxpos]; exact hsucc
  rcases roundNearestTiesToEven_is_roundDown_or_roundUp x hx f hf with hdown | hup
  · by_cases hsucc_eq : succ = f
    · have hsucc_ge : x ≤ (succ.toVal : R) :=
        findSuccessorPos_ge x hxpos succ hsucc
      have hf_ge : x ≤ (f.toVal : R) := by
        simpa [hsucc_eq] using hsucc_ge
      linarith
    · have hx_lt_thresh : x < FloatFormat.overflowThreshold R :=
        val_lt_thresh_of_roundUp_finite x succ hxpos hru
      let mid : R := ((f.toVal : R) + succ.toVal) / 2
      have h_not_gt_mid : ¬mid < x := by
        intro hgt
        have hrd : roundDown x = Fp.finite f := hdown
        have hnear_up : roundNearestTiesToEven x = roundUp x :=
          rnEven_above_mid_roundUp x mid f succ
            hxpos hx_lt_thresh hrd hru (by simp [mid]) hgt
        have hup_eq_hdown : roundUp x = roundDown x := by
          calc
            roundUp x = roundNearestTiesToEven x := hnear_up.symm
            _ = Fp.finite f := hf
            _ = roundDown x := hdown.symm
        have hsucc_eq' : succ = f :=
          Fp.finite.inj (by simpa [hru, hdown] using hup_eq_hdown)
        exact hsucc_eq hsucc_eq'
      have hmid_ge : x ≤ ((f.toVal : R) + succ.toVal) / 2 := by
        simpa [mid] using (not_lt.mp h_not_gt_mid)
      linarith
  · have hsucc_eq : succ = f := by
      apply Fp.finite.inj
      calc
        Fp.finite succ = roundUp x := hru.symm
        _ = Fp.finite f := hup
    have hsucc_ge : x ≤ (succ.toVal : R) :=
      findSuccessorPos_ge x hxpos succ hsucc
    have hf_ge : x ≤ (f.toVal : R) := by
      simpa [hsucc_eq] using hsucc_ge
    linarith

private theorem rnAway_ge_two_x_sub_succ {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (x : R) (hxpos : 0 < x) (hx : isNormalRange x)
    (f : FiniteFp) (hf : roundNearestTiesAwayFromZero x = Fp.finite f)
    (succ : FiniteFp) (hsucc : findSuccessorPos x hxpos = Fp.finite succ) :
    (2 * x - succ.toVal : R) ≤ f.toVal := by
  have hru : roundUp x = Fp.finite succ := by
    rw [roundUp, findSuccessor_pos_eq x hxpos]; exact hsucc
  rcases roundNearestTiesAwayFromZero_is_roundDown_or_roundUp x hx f hf with hdown | hup
  · by_cases hsucc_eq : succ = f
    · have hsucc_ge : x ≤ (succ.toVal : R) :=
        findSuccessorPos_ge x hxpos succ hsucc
      have hf_ge : x ≤ (f.toVal : R) := by
        simpa [hsucc_eq] using hsucc_ge
      linarith
    · have hx_lt_thresh : x < FloatFormat.overflowThreshold R :=
        val_lt_thresh_of_roundUp_finite x succ hxpos hru
      let mid : R := ((f.toVal : R) + succ.toVal) / 2
      have h_not_gt_mid : ¬mid < x := by
        intro hgt
        have hrd : roundDown x = Fp.finite f := hdown
        have hnear_up : roundNearestTiesAwayFromZero x = roundUp x :=
          rnAway_ge_mid_roundUp x mid f succ
            hxpos hx_lt_thresh hrd hru (by simp [mid]) hgt.le
        have hup_eq_hdown : roundUp x = roundDown x := by
          calc
            roundUp x = roundNearestTiesAwayFromZero x := hnear_up.symm
            _ = Fp.finite f := hf
            _ = roundDown x := hdown.symm
        have hsucc_eq' : succ = f :=
          Fp.finite.inj (by simpa [hru, hdown] using hup_eq_hdown)
        exact hsucc_eq hsucc_eq'
      have hmid_ge : x ≤ ((f.toVal : R) + succ.toVal) / 2 := by
        simpa [mid] using (not_lt.mp h_not_gt_mid)
      linarith
  · have hsucc_eq : succ = f := by
      apply Fp.finite.inj
      calc
        Fp.finite succ = roundUp x := hru.symm
        _ = Fp.finite f := hup
    have hsucc_ge : x ≤ (succ.toVal : R) :=
      findSuccessorPos_ge x hxpos succ hsucc
    have hf_ge : x ≤ (f.toVal : R) := by
      simpa [hsucc_eq] using hsucc_ge
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
  round_ge_two_x_sub_succ := by
    intro x hxpos hx f succ hf hsucc
    have hf' : roundNearestTiesToEven x = Fp.finite f := by
      simpa [RMode.round] using hf
    exact rnEven_ge_two_x_sub_succ (R := R) x hxpos hx f hf' succ hsucc

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
  round_ge_two_x_sub_succ := by
    intro x hxpos hx f succ hf hsucc
    have hf' : roundNearestTiesAwayFromZero x = Fp.finite f := by
      simpa [RMode.round] using hf
    exact rnAway_ge_two_x_sub_succ (R := R) x hxpos hx f hf' succ hsucc

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

/-! ## Generic nearest-mode relative error bound -/

/-! ## Generic nearest-mode half-epsilon relative error bound -/

/-- **Half-ULP Absolute Error for any Nearest Rounding Mode**: For positive x in the normal range,
the absolute error of any nearest rounding mode is at most `ulp(x) / 2`.

This follows from the `RModeNearest` axioms `round_le_two_x_sub_pred` and
`round_ge_two_x_sub_succ` (finite successor case) plus overflow-edge arithmetic
(infinite successor case). -/
theorem RModeNearest_abs_error_le_ulp_half {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeNearest R]
    (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : ○x = Fp.finite f) :
    |x - (f.toVal : R)| ≤ Fp.ulp x / 2 := by
  have hxpos := isNormalRange_pos x hx
  -- Establish roundDown / roundUp connections
  have hrd : roundDown x = Fp.finite (findPredecessorPos x hxpos) := by
    unfold roundDown; rw [findPredecessor_pos_eq]
  have hru : roundUp x = findSuccessorPos x hxpos := by
    unfold roundUp; rw [findSuccessor_pos_eq]
  -- Bracket: pred.toVal ≤ x
  have hpred_le : ((findPredecessorPos x hxpos).toVal : R) ≤ x :=
    findPredecessorPos_le x hxpos
  -- From round_le_two_x_sub_pred: f.toVal ≤ 2*x - pred.toVal, i.e. f.toVal - x ≤ x - pred.toVal
  have hA := RModeNearest.round_le_two_x_sub_pred x hxpos hx f hf
  -- Case split on findSuccessorPos
  match hsucc_eq : findSuccessorPos x hxpos with
  | .finite s =>
    -- Finite successor case
    -- Bracket: x ≤ s.toVal
    have hsucc_ge : x ≤ (s.toVal : R) := findSuccessorPos_ge x hxpos s hsucc_eq
    -- From round_ge_two_x_sub_succ: x - f.toVal ≤ s.toVal - x
    have hB := RModeNearest.round_ge_two_x_sub_succ x hxpos hx f s hf hsucc_eq
    -- Gap bound: s.toVal - pred.toVal ≤ ulp(x)
    have hgap : (s.toVal : R) - (findPredecessorPos x hxpos).toVal ≤ Fp.ulp x := by
      apply findSuccessor_sub_findPredecessor_le_ulp_of_normal x hx s (findPredecessorPos x hxpos)
      · rw [findSuccessor_pos_eq]; exact hsucc_eq
      · exact findPredecessor_pos_eq x hxpos
    -- Bracket ordering: pred.toVal ≤ f.toVal (from roundDown_le_round)
    have hpred_le_f : ((findPredecessorPos x hxpos).toVal : R) ≤ (f.toVal : R) := by
      have hle : roundDown x ≤ ○x := RModeNearest.roundDown_le_round x
      rw [hrd, hf] at hle
      exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff _ _).mp hle)
    -- Bracket ordering: f.toVal ≤ s.toVal (from round_le_roundUp)
    have hf_le_s : (f.toVal : R) ≤ (s.toVal : R) := by
      have hle : ○x ≤ roundUp x := RModeNearest.round_le_roundUp x
      rw [hf, hru, hsucc_eq] at hle
      exact FiniteFp.le_toVal_le R ((Fp.finite_le_finite_iff _ _).mp hle)
    -- Conclude: |x - f.toVal| ≤ ulp(x) / 2
    rw [abs_le]
    constructor <;> linarith
  | .infinite false =>
    -- Overflow edge case: findSuccessorPos returned +∞
    -- Step 1: x > lff.toVal (contrapositive of roundUp_le_of_fp_ge)
    have hgt_lff : (FiniteFp.largestFiniteFloat.toVal : R) < x := by
      by_contra h
      push_neg at h
      have hle : roundUp x ≤ Fp.finite FiniteFp.largestFiniteFloat :=
        roundUp_le_of_fp_ge x FiniteFp.largestFiniteFloat (Or.inl rfl) h
      rw [hru, hsucc_eq] at hle
      exact absurd ((Fp.pos_inf_le_iff _).mp hle) (by simp)
    -- Step 2: ○x = roundDown x (since roundUp is infinite)
    have hround_down : ○x = roundDown x := by
      rcases RModeNearest.round_eq_roundDown_or_roundUp x with h | h
      · exact h
      · rw [h, hru, hsucc_eq] at hf; cases hf
    -- Step 3: f = lff (from roundDown_gt_lff)
    have hf_eq_lff : Fp.finite f = Fp.finite FiniteFp.largestFiniteFloat := by
      rw [← hf, hround_down]
      exact roundDown_gt_lff x hxpos hgt_lff
    have hf_lff : f = FiniteFp.largestFiniteFloat := Fp.finite.inj hf_eq_lff
    -- Step 4: x < overflowThreshold (otherwise round would give +∞)
    have hlt_ot : x < FloatFormat.overflowThreshold R := by
      by_contra h
      push_neg at h
      have := RModeNearest.overflow_pos_inf x h
      rw [this] at hf; cases hf
    -- Step 5: Compute ulp(x) at the top binade
    have hlog : Int.log 2 x = FloatFormat.max_exp := by
      apply le_antisymm
      · -- upper: x < 2^(max_exp+1) → Int.log 2 x < max_exp + 1
        have hlt_zpow : x < (2 : R) ^ (FloatFormat.max_exp + 1) :=
          lt_trans hlt_ot FloatFormat.overflowThreshold_lt_zpow_max_exp_succ
        have := (Int.lt_zpow_iff_log_lt (by norm_num : (1 : ℕ) < 2) hxpos).mp hlt_zpow
        omega
      · -- lower: 2^max_exp ≤ x → max_exp ≤ Int.log 2 x
        exact (Int.zpow_le_iff_le_log (by norm_num : (1 : ℕ) < 2) hxpos).mp
          (le_trans FiniteFp.zpow_max_exp_le_largestFiniteFloat_toVal (le_of_lt hgt_lff))
    have hulp : Fp.ulp x = (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
      simp only [Fp.ulp, abs_of_pos hxpos, hlog, max_eq_left FloatFormat.exp_order_le]
    -- Step 6: overflowThreshold - lff.toVal = ulp(x) / 2
    have hhalf :
        FloatFormat.overflowThreshold R - (FiniteFp.largestFiniteFloat.toVal : R)
          = Fp.ulp x / 2 := by
      rw [FiniteFp.largestFiniteFloat_toVal, hulp]
      have hexp_eq : (-(FloatFormat.prec : ℤ) + 1) = 1 - (FloatFormat.prec : ℤ) := by ring
      rw [hexp_eq]
      unfold FloatFormat.overflowThreshold
      set p := (2 : R) ^ (1 - (FloatFormat.prec : ℤ))
      set M := (2 : R) ^ FloatFormat.max_exp
      have hMp : M * p = (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
        simp only [M, p, ← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
        congr 1; ring
      rw [← hMp]
      have hp_pos : (0 : R) < p := by positivity
      have hM_pos : (0 : R) < M := by positivity
      nlinarith
    -- Step 7: Conclude
    rw [hf_lff]
    have : x - (FiniteFp.largestFiniteFloat.toVal : R) ≥ 0 := by linarith
    rw [abs_of_nonneg this]
    linarith

  | .infinite true =>
    -- findSuccessorPos for positive x can't return -∞
    exfalso
    have := findSuccessorPos_ne_neg_inf x hxpos
    rw [hsucc_eq] at this
    exact this rfl
  | .NaN =>
    exfalso
    have := findSuccessorPos_ne_nan x hxpos
    rw [hsucc_eq] at this
    exact this rfl

/-- **Half Machine Epsilon for any Nearest Rounding Mode**: For positive x in the normal range,
the relative error of any nearest rounding mode is at most `2^(-prec)` (half machine epsilon). -/
theorem RModeNearest_relativeError_le_half {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeNearest R]
    (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : ○x = Fp.finite f) :
    Fp.relativeError x f ≤ 2 ^ (-(FloatFormat.prec : ℤ)) := by
  have hxpos := isNormalRange_pos x hx
  have h_abs_err := RModeNearest_abs_error_le_ulp_half x hx f hf
  have h_abs_ge : (2 : R) ^ FloatFormat.min_exp ≤ |x| := by
    rw [abs_of_pos hxpos]; exact hx.left
  have h_le : |x - f.toVal| ≤ (1/2) * Fp.ulp x := by linarith
  have h := Fp.relativeError_ulp_upper_bound_le x f (1/2) (by norm_num) h_abs_ge h_le
  calc Fp.relativeError x f
      ≤ 1 / 2 * 2 ^ (1 - (FloatFormat.prec : ℤ)) := h
    _ = 2 ^ (-(FloatFormat.prec : ℤ)) := by
        rw [show (1 : R) / 2 = (2 : R) ^ (-1 : ℤ) from by norm_num, two_zpow_mul]
        congr 1; ring

end PolicyInstances
