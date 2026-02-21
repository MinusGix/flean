import Flean.Rounding.Neighbor.Basic

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

section Gap

/-- Finite-output witness for `nextUp`. -/
abbrev IsNextUp (f u : FiniteFp) : Prop := nextUp (Fp.finite f) = Fp.finite u

/-- Finite-output witness for `nextDown`. -/
abbrev IsNextDown (f d : FiniteFp) : Prop := nextDown (Fp.finite f) = Fp.finite d

/-- One-sided ULP bound for `nextUp` from a finite value, routed through the normal-range
successor/predecessor gap theorem at the perturbed input point. -/
theorem nextUp_sub_self_le_ulp_of_normal_step
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] ≤ Fp.ulp (stepUpVal f) := by
  have hs : findSuccessor (stepUpVal f) = Fp.finite u := by
    simpa [IsNextUp, nextUp_finite] using hup
  exact findSuccessor_sub_findPredecessor_le_ulp_of_normal
    (stepUpVal f) hN u f hs hpred

/-- Exact one-ULP gap for `nextUp` from a finite value under normal-step hypotheses. -/
theorem nextUp_sub_self_eq_ulp_of_normal_step
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] = Fp.ulp (stepUpVal f) := by
  have hs : findSuccessor (stepUpVal f) = Fp.finite u := by
    simpa [IsNextUp, nextUp_finite] using hup
  have hpred_lt : (⌞f⌟[ℚ] : ℚ) < stepUpVal f := by
    unfold stepUpVal neighborStep
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  exact findSuccessor_sub_findPredecessor_eq_ulp_of_normal_of_pred_lt
    (stepUpVal f) hN u f hs hpred hpred_lt

/-- One-sided ULP bound for `nextDown` from a finite value, routed through the normal-range
successor/predecessor gap theorem at the perturbed input point. -/
theorem self_sub_nextDown_le_ulp_of_normal_step
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] ≤ Fp.ulp (stepDownVal f) := by
  have hp : findPredecessor (stepDownVal f) = Fp.finite d := by
    simpa [IsNextDown, nextDown_finite] using hdown
  exact findSuccessor_sub_findPredecessor_le_ulp_of_normal
    (stepDownVal f) hN f d hsucc hp

/-- Exact one-ULP gap for `nextDown` from a finite value under normal-step hypotheses.

The additional strictness hypothesis excludes the representable-input degenerate case
(`pred = x`), ensuring true adjacency around the perturbed point. -/
theorem self_sub_nextDown_eq_ulp_of_normal_step
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] = Fp.ulp (stepDownVal f) := by
  have hp : findPredecessor (stepDownVal f) = Fp.finite d := by
    simpa [IsNextDown, nextDown_finite] using hdown
  have hsucc_gt : (stepDownVal f : ℚ) < ⌞f⌟[ℚ] := by
    unfold stepDownVal neighborStep
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  exact findSuccessor_sub_findPredecessor_eq_ulp_of_normal_of_succ_gt
    (stepDownVal f) hN f d hsucc hp hsucc_gt

/-- `nextUp` one-sided ULP bound specialized back to `ulp(f.toVal)` when the perturbation
stays in the same log binade. -/
theorem nextUp_sub_self_le_ulp_of_log_step_eq
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hup : IsNextUp f u)
    (hlog : Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) := by
  have hstep : Fp.ulp (stepUpVal f) = Fp.ulp (⌞f⌟[ℚ]) :=
    Fp.ulp_step_log (stepUpVal f) (⌞f⌟[ℚ]) hlog
  have hbase := nextUp_sub_self_le_ulp_of_normal_step f u hN hpred hup
  simpa [hstep] using hbase

/-- Exact `nextUp` gap specialized back to `ulp(f.toVal)` when the perturbation stays in the
same log binade. -/
theorem nextUp_sub_self_eq_ulp_of_log_step_eq
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hup : IsNextUp f u)
    (hlog : Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) := by
  have hstep : Fp.ulp (stepUpVal f) = Fp.ulp (⌞f⌟[ℚ]) :=
    Fp.ulp_step_log (stepUpVal f) (⌞f⌟[ℚ]) hlog
  have hbase := nextUp_sub_self_eq_ulp_of_normal_step f u hN hpred hup
  simpa [hstep] using hbase

/-- `nextDown` one-sided ULP bound specialized back to `ulp(f.toVal)` when the perturbation
stays in the same log binade. -/
theorem self_sub_nextDown_le_ulp_of_log_step_eq
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hdown : IsNextDown f d)
    (hlog : Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) := by
  have hstep : Fp.ulp (stepDownVal f) = Fp.ulp (⌞f⌟[ℚ]) :=
    Fp.ulp_step_log (stepDownVal f) (⌞f⌟[ℚ]) hlog
  have hbase := self_sub_nextDown_le_ulp_of_normal_step f d hN hsucc hdown
  simpa [hstep] using hbase

/-- Exact `nextDown` gap specialized back to `ulp(f.toVal)` when the perturbation stays in the
same log binade. -/
theorem self_sub_nextDown_eq_ulp_of_log_step_eq
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hdown : IsNextDown f d)
    (hlog : Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) := by
  have hstep : Fp.ulp (stepDownVal f) = Fp.ulp (⌞f⌟[ℚ]) :=
    Fp.ulp_step_log (stepDownVal f) (⌞f⌟[ℚ]) hlog
  have hbase := self_sub_nextDown_eq_ulp_of_normal_step f d hN hsucc hdown
  simpa [hstep] using hbase

/-- Bundled interior hypothesis for proving one-sided `nextUp` ULP bounds from a finite value. -/
abbrev NextUpInterior (f : FiniteFp) : Prop :=
  isNormalRange (stepUpVal f) ∧
    findPredecessor (stepUpVal f) = Fp.finite f

/-- Bundled interior hypothesis for proving one-sided `nextDown` ULP bounds from a finite value. -/
abbrev NextDownInterior (f : FiniteFp) : Prop :=
  isNormalRange (stepDownVal f) ∧
    findSuccessor (stepDownVal f) = Fp.finite f

/-- `nextUp` one-sided ULP bound from the bundled interior hypothesis. -/
theorem nextUp_sub_self_le_ulp_of_interior
    (f u : FiniteFp) (hI : NextUpInterior f)
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] ≤ Fp.ulp (stepUpVal f) := by
  exact nextUp_sub_self_le_ulp_of_normal_step f u hI.1 hI.2 hup

/-- `nextDown` one-sided ULP bound from the bundled interior hypothesis. -/
theorem self_sub_nextDown_le_ulp_of_interior
    (f d : FiniteFp) (hI : NextDownInterior f)
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] ≤ Fp.ulp (stepDownVal f) := by
  exact self_sub_nextDown_le_ulp_of_normal_step f d hI.1 hI.2 hdown

/-- Bundled interior hypothesis with same-log condition for specializing to `ulp(f.toVal)`. -/
abbrev NextUpInteriorSameLog (f : FiniteFp) : Prop :=
  NextUpInterior f ∧
    Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)

/-- Bundled interior hypothesis with same-log condition for specializing to `ulp(f.toVal)`. -/
abbrev NextDownInteriorSameLog (f : FiniteFp) : Prop :=
  NextDownInterior f ∧
    Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)

/-- Constructor for `NextUpInterior`. -/
theorem nextUpInterior_intro (f : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f) :
    NextUpInterior f := ⟨hN, hpred⟩

/-- Constructor for `NextDownInterior`. -/
theorem nextDownInterior_intro (f : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f) :
    NextDownInterior f := ⟨hN, hsucc⟩

/-- Constructor for `NextUpInteriorSameLog`. -/
theorem nextUpInteriorSameLog_intro (f : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)) :
    NextUpInteriorSameLog f := ⟨⟨hN, hpred⟩, hlog⟩

/-- Constructor for `NextDownInteriorSameLog`. -/
theorem nextDownInteriorSameLog_intro (f : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)) :
    NextDownInteriorSameLog f := ⟨⟨hN, hsucc⟩, hlog⟩

/-- Clean public `nextUp` bound to `ulp(f.toVal)` under bundled interior/same-log hypotheses. -/
theorem nextUp_sub_self_le_ulp_of_interior_sameLog
    (f u : FiniteFp) (hI : NextUpInteriorSameLog f)
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) := by
  exact nextUp_sub_self_le_ulp_of_log_step_eq f u
    hI.1.1 hI.1.2 hup hI.2

/-- Clean public `nextDown` bound to `ulp(f.toVal)` under bundled interior/same-log hypotheses. -/
theorem self_sub_nextDown_le_ulp_of_interior_sameLog
    (f d : FiniteFp) (hI : NextDownInteriorSameLog f)
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) := by
  exact self_sub_nextDown_le_ulp_of_log_step_eq f d
    hI.1.1 hI.1.2 hdown hI.2

/-- Public `nextUp` gap theorem with explicit assumptions and no manual bundle construction. -/
theorem nextUp_gap_le_ulp_of
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|))
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) := by
  exact nextUp_sub_self_le_ulp_of_interior_sameLog f u
    (nextUpInteriorSameLog_intro f hN hpred hlog) hup

/-- Public `nextDown` gap theorem with explicit assumptions and no manual bundle construction. -/
theorem nextDown_gap_le_ulp_of
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|))
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) := by
  exact self_sub_nextDown_le_ulp_of_interior_sameLog f d
    (nextDownInteriorSameLog_intro f hN hsucc hlog) hdown

/-- Short alias for `nextUp_sub_self_le_ulp_of_normal_step`. -/
theorem nextUp_gap_le_ulp_step
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] ≤ Fp.ulp (stepUpVal f) :=
  nextUp_sub_self_le_ulp_of_normal_step f u hN hpred hup

/-- Short alias for `self_sub_nextDown_le_ulp_of_normal_step`. -/
theorem nextDown_gap_le_ulp_step
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] ≤ Fp.ulp (stepDownVal f) :=
  self_sub_nextDown_le_ulp_of_normal_step f d hN hsucc hdown

/-- Short alias for `nextUp_sub_self_le_ulp_of_interior_sameLog`. -/
theorem nextUp_gap_le_ulp
    (f u : FiniteFp) (hI : NextUpInteriorSameLog f) (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) :=
  nextUp_sub_self_le_ulp_of_interior_sameLog f u hI hup

/-- Short alias for `self_sub_nextDown_le_ulp_of_interior_sameLog`. -/
theorem nextDown_gap_le_ulp
    (f d : FiniteFp) (hI : NextDownInteriorSameLog f) (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] ≤ Fp.ulp (⌞f⌟[ℚ]) :=
  self_sub_nextDown_le_ulp_of_interior_sameLog f d hI hdown

/-- Public `nextUp` exact-gap theorem with explicit assumptions and no manual bundle construction. -/
theorem nextUp_gap_eq_ulp_of
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|))
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) := by
  exact nextUp_sub_self_eq_ulp_of_log_step_eq f u hN hpred hup hlog

/-- Public `nextDown` exact-gap theorem with explicit assumptions and no manual bundle construction. -/
theorem nextDown_gap_eq_ulp_of
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|))
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) := by
  exact self_sub_nextDown_eq_ulp_of_log_step_eq f d hN hsucc hdown hlog

/-- Short alias for `nextUp_sub_self_eq_ulp_of_normal_step`. -/
theorem nextUp_gap_eq_ulp_step
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] = Fp.ulp (stepUpVal f) :=
  nextUp_sub_self_eq_ulp_of_normal_step f u hN hpred hup

/-- Short alias for `self_sub_nextDown_eq_ulp_of_normal_step`. -/
theorem nextDown_gap_eq_ulp_step
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hdown : IsNextDown f d) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] = Fp.ulp (stepDownVal f) :=
  self_sub_nextDown_eq_ulp_of_normal_step f d hN hsucc hdown

/-- Short alias for `nextUp_sub_self_eq_ulp_of_log_step_eq`. -/
theorem nextUp_gap_eq_ulp
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|))
    (hup : IsNextUp f u) :
    ⌞u⌟[ℚ] - ⌞f⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) :=
  nextUp_sub_self_eq_ulp_of_log_step_eq f u hN hpred hup hlog

/-- Short alias for `self_sub_nextDown_eq_ulp_of_log_step_eq`. -/
theorem nextDown_gap_eq_ulp
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hdown : IsNextDown f d)
    (hlog : Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|)) :
    ⌞f⌟[ℚ] - ⌞d⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) :=
  self_sub_nextDown_eq_ulp_of_log_step_eq f d hN hsucc hdown hlog

end Gap

end Rounding
