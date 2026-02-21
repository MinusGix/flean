import Flean.Rounding.Neighbor.Basic

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

section Boundary

private theorem neighborStep_pos : (0 : ℚ) < neighborStep := by
  unfold neighborStep
  linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]

private theorem neighborStep_lt_smallestPosSubnormal :
    neighborStep < (FiniteFp.smallestPosSubnormal.toVal : ℚ) := by
  unfold neighborStep
  linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]

private theorem findSuccessor_rat_of_pos_lt_smallestPosSubnormal
    (x : ℚ) (hpos : 0 < x) (hsmall : x < FiniteFp.smallestPosSubnormal.toVal) :
    findSuccessor x = Fp.finite FiniteFp.smallestPosSubnormal := by
  rw [findSuccessor_pos_eq (R := ℚ) x hpos]
  unfold findSuccessorPos
  have h_sub : x < (2 : ℚ) ^ FloatFormat.min_exp := by
    exact lt_trans hsmall FiniteFp.smallestPosSubnormal_lt_minExp
  simp only [h_sub, ↓reduceDIte]
  unfold roundSubnormalUp
  rw [FiniteFp.smallestPosSubnormal_toVal] at hsmall
  have h_ceil : ⌈x / FiniteFp.smallestPosSubnormal.toVal⌉ = 1 := by
    rw [Int.ceil_eq_iff, FiniteFp.smallestPosSubnormal_toVal]
    norm_num
    constructor
    · exact div_pos hpos (by linearize)
    · exact div_le_one_of_le₀ (le_of_lt hsmall) (by linearize)
  rw [FiniteFp.smallestPosSubnormal_toVal] at h_ceil
  simp [h_ceil]
  have h_k_lt : (2 : ℤ) ^ ((FloatFormat.prec - 1).toNat) > 1 := by
    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
    have h2 : 2 ≤ FloatFormat.prec.toNat := FloatFormat.two_le_prec_toNat
    have hne : FloatFormat.prec.toNat - 1 ≠ 0 := by omega
    have hnat : 1 < (2 : ℕ) ^ (FloatFormat.prec.toNat - 1) := Nat.one_lt_pow hne (by norm_num : 1 < 2)
    calc (2 : ℤ) ^ (FloatFormat.prec.toNat - 1)
        = ((2 : ℕ) ^ (FloatFormat.prec.toNat - 1) : ℤ) := by simp only [Nat.cast_ofNat]
      _ > 1 := by omega
  have h_not_ge : ¬((2 : ℤ) ^ ((FloatFormat.prec - 1).toNat) ≤ 1) := not_le.mpr h_k_lt
  split_ifs with hk
  · exfalso
    exact h_not_ge (by simpa [ge_iff_le] using hk)
  · rfl

private theorem findPredecessor_rat_of_pos_lt_smallestPosSubnormal
    (x : ℚ) (hpos : 0 < x) (hsmall : x < FiniteFp.smallestPosSubnormal.toVal) :
    findPredecessor x = Fp.finite 0 := by
  rw [findPredecessor_pos_eq (R := ℚ) x hpos]
  unfold findPredecessorPos
  have h_sub : x < (2 : ℚ) ^ FloatFormat.min_exp := by
    exact lt_trans hsmall FiniteFp.smallestPosSubnormal_lt_minExp
  have hzero : roundSubnormalDown x ⟨hpos, h_sub⟩ = 0 :=
    (roundSubnormalDown_eq_zero_iff (x := x) (h := ⟨hpos, h_sub⟩)).2 hsmall
  simp only [h_sub, ↓reduceDIte, hzero]

private theorem findSuccessor_rat_gt_largestFiniteFloat
    (x : ℚ) (hgt : (FiniteFp.largestFiniteFloat.toVal : ℚ) < x) :
    findSuccessor x = Fp.infinite false := by
  have hpos : (0 : ℚ) < x := lt_trans (FiniteFp.largestFiniteFloat_toVal_pos (R := ℚ)) hgt
  rw [findSuccessor_pos_eq (R := ℚ) x hpos]
  match hfs : findSuccessorPos x hpos with
  | Fp.finite f =>
    exfalso
    have hge : (x : ℚ) ≤ f.toVal := findSuccessorPos_ge x hpos f hfs
    have hle : (f.toVal : ℚ) ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
    linarith
  | Fp.infinite false =>
    rfl
  | Fp.infinite true =>
    exfalso
    exact findSuccessorPos_ne_neg_inf x hpos hfs
  | Fp.NaN =>
    exfalso
    exact findSuccessorPos_ne_nan x hpos hfs

private theorem findPredecessor_rat_lt_neg_largestFiniteFloat
    (x : ℚ) (hlt : x < -(FiniteFp.largestFiniteFloat.toVal : ℚ)) :
    findPredecessor x = Fp.infinite true := by
  have hneg : x < 0 := by
    linarith [FiniteFp.largestFiniteFloat_toVal_pos (R := ℚ)]
  rw [findPredecessor_neg_eq (R := ℚ) x hneg]
  have hpos : (0 : ℚ) < -x := neg_pos.mpr hneg
  have hgt : (FiniteFp.largestFiniteFloat.toVal : ℚ) < -x := by linarith
  have hsucc : findSuccessor (-x) = Fp.infinite false :=
    findSuccessor_rat_gt_largestFiniteFloat (-x) hgt
  have hsuccPos : findSuccessorPos (-x) hpos = Fp.infinite false := by
    simpa [findSuccessor_pos_eq (R := ℚ) (-x) hpos] using hsucc
  rw [hsuccPos]
  simp

/-- `nextUp` of zero is the smallest positive subnormal finite float. -/
@[simp] theorem nextUp_zero :
    nextUp (0 : Fp) = Fp.finite FiniteFp.smallestPosSubnormal := by
  have hsucc : findSuccessor neighborStep = Fp.finite FiniteFp.smallestPosSubnormal :=
    findSuccessor_rat_of_pos_lt_smallestPosSubnormal neighborStep neighborStep_pos
      (neighborStep_lt_smallestPosSubnormal)
  simpa [nextUp, stepUpVal, neighborStep, FiniteFp.toVal_zero] using hsucc

/-- `nextDown` of zero is the negative smallest positive subnormal finite float. -/
@[simp] theorem nextDown_zero :
    nextDown (0 : Fp) = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
  have hsucc : findSuccessor neighborStep = Fp.finite FiniteFp.smallestPosSubnormal :=
    findSuccessor_rat_of_pos_lt_smallestPosSubnormal neighborStep neighborStep_pos
      (neighborStep_lt_smallestPosSubnormal)
  have hsuccPos : findSuccessorPos neighborStep neighborStep_pos = Fp.finite FiniteFp.smallestPosSubnormal := by
    simpa [findSuccessor_pos_eq (R := ℚ) neighborStep neighborStep_pos] using hsucc
  have hneg : -(neighborStep : ℚ) < 0 := by linarith [neighborStep_pos]
  calc
    nextDown (0 : Fp)
        = findPredecessor (-(neighborStep : ℚ)) := by
            simp [nextDown, stepDownVal, neighborStep, FiniteFp.toVal_zero]
    _ = -(findSuccessorPos neighborStep neighborStep_pos) := by
          simpa using (findPredecessor_neg_eq (R := ℚ) (-(neighborStep : ℚ)) hneg)
    _ = -(Fp.finite FiniteFp.smallestPosSubnormal) := by rw [hsuccPos]
    _ = Fp.finite (-FiniteFp.smallestPosSubnormal) := by simp

/-- Signed-zero behavior: `nextUp(-0) = smallestPosSubnormal`. -/
@[simp] theorem nextUp_neg_zero :
    nextUp (Fp.finite (-0 : FiniteFp)) = Fp.finite FiniteFp.smallestPosSubnormal := by
  have hsucc : findSuccessor neighborStep = Fp.finite FiniteFp.smallestPosSubnormal :=
    findSuccessor_rat_of_pos_lt_smallestPosSubnormal neighborStep neighborStep_pos
      (neighborStep_lt_smallestPosSubnormal)
  simpa [nextUp_finite, stepUpVal, neighborStep] using hsucc

/-- Signed-zero behavior: `nextDown(-0) = -smallestPosSubnormal`. -/
@[simp] theorem nextDown_neg_zero :
    nextDown (Fp.finite (-0 : FiniteFp)) = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
  calc
    nextDown (Fp.finite (-0 : FiniteFp))
        = nextDown (Fp.finite (0 : FiniteFp)) := by
          simp [nextDown_finite, stepDownVal, neighborStep]
    _ = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
          exact nextDown_zero

/-- `nextUp` of the largest finite float overflows to `+∞`. -/
@[simp] theorem nextUp_largestFiniteFloat :
    nextUp (Fp.finite FiniteFp.largestFiniteFloat) = Fp.infinite false := by
  have hgt : (FiniteFp.largestFiniteFloat.toVal : ℚ) < stepUpVal FiniteFp.largestFiniteFloat := by
    unfold stepUpVal neighborStep
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hsucc : findSuccessor (stepUpVal FiniteFp.largestFiniteFloat) = Fp.infinite false :=
    findSuccessor_rat_gt_largestFiniteFloat (stepUpVal FiniteFp.largestFiniteFloat) hgt
  simpa [nextUp_finite] using hsucc

/-- `nextDown` of the most-negative finite float underflows to `-∞`. -/
@[simp] theorem nextDown_neg_largestFiniteFloat :
    nextDown (Fp.finite (-FiniteFp.largestFiniteFloat)) = Fp.infinite true := by
  have hlt : stepDownVal (-FiniteFp.largestFiniteFloat) <
      -(FiniteFp.largestFiniteFloat.toVal : ℚ) := by
    unfold stepDownVal neighborStep
    rw [FiniteFp.toVal_neg_eq_neg]
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := ℚ)]
  have hpred : findPredecessor (stepDownVal (-FiniteFp.largestFiniteFloat)) = Fp.infinite true :=
    findPredecessor_rat_lt_neg_largestFiniteFloat (stepDownVal (-FiniteFp.largestFiniteFloat)) hlt
  simpa [nextDown_finite] using hpred

/-- `nextDown` of the smallest positive subnormal is `+0`. -/
@[simp] theorem nextDown_smallestPosSubnormal :
    nextDown (Fp.finite FiniteFp.smallestPosSubnormal) = Fp.finite 0 := by
  have hstep : stepDownVal FiniteFp.smallestPosSubnormal = neighborStep := by
    unfold stepDownVal neighborStep
    ring
  have hpred : findPredecessor neighborStep = Fp.finite 0 :=
    findPredecessor_rat_of_pos_lt_smallestPosSubnormal neighborStep neighborStep_pos
      (neighborStep_lt_smallestPosSubnormal)
  calc
    nextDown (Fp.finite FiniteFp.smallestPosSubnormal)
        = findPredecessor (stepDownVal FiniteFp.smallestPosSubnormal) := by
            simp
    _ = findPredecessor neighborStep := by rw [hstep]
    _ = Fp.finite 0 := hpred

/-- `nextUp` of the negative smallest positive subnormal is `-0`. -/
@[simp] theorem nextUp_neg_smallestPosSubnormal :
    nextUp (Fp.finite (-FiniteFp.smallestPosSubnormal)) = Fp.finite (-0) := by
  have hstep : stepUpVal (-FiniteFp.smallestPosSubnormal) = -(neighborStep : ℚ) := by
    unfold stepUpVal neighborStep
    rw [FiniteFp.toVal_neg_eq_neg]
    ring
  have hneg : -(neighborStep : ℚ) < 0 := by linarith [neighborStep_pos]
  have hpred : findPredecessor neighborStep = Fp.finite 0 :=
    findPredecessor_rat_of_pos_lt_smallestPosSubnormal neighborStep neighborStep_pos
      (neighborStep_lt_smallestPosSubnormal)
  calc
    nextUp (Fp.finite (-FiniteFp.smallestPosSubnormal))
        = findSuccessor (stepUpVal (-FiniteFp.smallestPosSubnormal)) := by
            simp
    _ = findSuccessor (-(neighborStep : ℚ)) := by rw [hstep]
    _ = -findPredecessor neighborStep := by
          simpa using (findSuccessor_symm (R := ℚ) (-(neighborStep : ℚ)) hneg)
    _ = -(Fp.finite 0) := by rw [hpred]
    _ = Fp.finite (-0) := by simp

/-- Zero-domain inverse behavior: `nextDown (nextUp (+0)) = +0`. -/
@[simp] theorem nextDown_nextUp_pos_zero :
    nextDown (nextUp (Fp.finite (0 : FiniteFp))) = Fp.finite 0 := by
  have h0 : nextUp (Fp.finite (0 : FiniteFp)) = Fp.finite FiniteFp.smallestPosSubnormal := by
    exact nextUp_zero
  rw [h0]
  exact nextDown_smallestPosSubnormal

/-- Zero-domain inverse behavior: `nextUp (nextDown (+0)) = -0`. -/
@[simp] theorem nextUp_nextDown_pos_zero :
    nextUp (nextDown (Fp.finite (0 : FiniteFp))) = Fp.finite (-0) := by
  have h0 : nextDown (Fp.finite (0 : FiniteFp)) = Fp.finite (-FiniteFp.smallestPosSubnormal) := by
    exact nextDown_zero
  rw [h0]
  exact nextUp_neg_smallestPosSubnormal

end Boundary

end Rounding
