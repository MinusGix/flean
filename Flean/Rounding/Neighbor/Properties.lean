import Flean.Rounding.Neighbor.Boundary
import Flean.Rounding.RoundUp

/-! # Predecessor/successor distance properties

Key properties of `nextUp` and `nextDown`:
1. `finite_lt_nextUp` / `finite_le_nextUp`: strict/non-strict ordering with nextUp
2. `nextDown_lt_finite` / `nextDown_le_finite`: symmetric for nextDown
3. `nextUp_no_float_between` / `nextDown_no_float_between`: adjacency (no intermediate float)
-/

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

/-! ## General ceiling/floor properties for findSuccessor/findPredecessor -/

/-- `findSuccessor x` returns a value `≥ x` when it returns a finite float. -/
theorem findSuccessor_ge (x : ℚ) (f : FiniteFp)
    (h : findSuccessor x = Fp.finite f) : x ≤ (f.toVal : ℚ) := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · rw [findSuccessor_neg_eq (R := ℚ) x hx_neg] at h
    rw [Fp.finite.injEq] at h; rw [← h, FiniteFp.toVal_neg_eq_neg]
    linarith [findPredecessorPos_le (R := ℚ) (-x) (neg_pos.mpr hx_neg)]
  · subst hx_zero; rw [findSuccessor_zero (R := ℚ)] at h
    rw [Fp.finite.injEq] at h; rw [← h, FiniteFp.toVal_zero]
  · rw [findSuccessor_pos_eq (R := ℚ) x hx_pos] at h
    exact findSuccessorPos_ge (R := ℚ) x hx_pos f h

/-- `findPredecessor x` returns a value `≤ x` when it returns a finite float. -/
theorem findPredecessor_le_val (x : ℚ) (f : FiniteFp)
    (h : findPredecessor x = Fp.finite f) : (f.toVal : ℚ) ≤ x := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · rw [findPredecessor_neg_eq (R := ℚ) x hx_neg] at h
    have hnx_pos : (0 : ℚ) < -x := neg_pos.mpr hx_neg
    match hfsp : findSuccessorPos (-x) hnx_pos with
    | Fp.finite g =>
      rw [hfsp, Fp.neg_finite, Fp.finite.injEq] at h
      rw [← h, FiniteFp.toVal_neg_eq_neg]
      linarith [findSuccessorPos_ge (R := ℚ) (-x) hnx_pos g hfsp]
    | Fp.infinite b => rw [hfsp] at h; cases b <;> simp at h
    | Fp.NaN => exact absurd hfsp (findSuccessorPos_ne_nan (R := ℚ) (-x) hnx_pos)
  · subst hx_zero; rw [findPredecessor_zero (R := ℚ)] at h
    rw [Fp.finite.injEq] at h; rw [← h, FiniteFp.toVal_zero]
  · rw [findPredecessor_pos_eq (R := ℚ) x hx_pos] at h
    rw [Fp.finite.injEq] at h; rw [← h]
    exact findPredecessorPos_le (R := ℚ) x hx_pos

/-- `findSuccessor` never returns `NaN`. -/
private theorem findSuccessor_ne_nan (x : ℚ) : findSuccessor x ≠ Fp.NaN := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [findSuccessor_neg_eq (R := ℚ) x hx]; simp
  · rw [findSuccessor_zero (R := ℚ)]; simp
  · rw [findSuccessor_pos_eq (R := ℚ) x hx]; exact findSuccessorPos_ne_nan (R := ℚ) x hx

/-- `findSuccessor` never returns `-∞`. -/
private theorem findSuccessor_ne_neg_inf (x : ℚ) : findSuccessor x ≠ Fp.infinite true := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [findSuccessor_neg_eq (R := ℚ) x hx]; simp
  · rw [findSuccessor_zero (R := ℚ)]; simp
  · rw [findSuccessor_pos_eq (R := ℚ) x hx]; exact findSuccessorPos_ne_neg_inf (R := ℚ) x hx

/-- `findPredecessor` never returns `NaN`. -/
private theorem findPredecessor_ne_nan (x : ℚ) : findPredecessor x ≠ Fp.NaN := by
  intro h
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [findPredecessor_neg_eq (R := ℚ) x hx] at h
    have hnx_pos : (0 : ℚ) < -x := neg_pos.mpr hx
    match hfsp : findSuccessorPos (-x) hnx_pos with
    | Fp.finite g => rw [hfsp] at h; simp at h
    | Fp.infinite false => rw [hfsp] at h; simp at h
    | Fp.infinite true => exact findSuccessorPos_ne_neg_inf (R := ℚ) (-x) hnx_pos hfsp
    | Fp.NaN => exact findSuccessorPos_ne_nan (R := ℚ) (-x) hnx_pos hfsp
  · rw [findPredecessor_zero (R := ℚ)] at h; simp at h
  · rw [findPredecessor_pos_eq (R := ℚ) x hx] at h; simp at h

/-- `findPredecessor` never returns `+∞`. -/
private theorem findPredecessor_ne_pos_inf (x : ℚ) : findPredecessor x ≠ Fp.infinite false := by
  intro h
  have : findPredecessor x ≤ Fp.finite FiniteFp.largestFiniteFloat :=
    findPredecessor_le_largestFiniteFloat (R := ℚ) x
  rw [h] at this; exact absurd this (by simp [Fp.le_def])

/-! ## Grid alignment: all representable values are multiples of sps -/

/-- Every representable value is an integer multiple of `2^(min_exp - prec + 1)`. -/
private theorem toVal_int_mul_sps (f : FiniteFp) :
    ∃ n : ℤ, (f.toVal : ℚ) = (n : ℚ) * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by
  by_cases hm : f.m = 0
  · exact ⟨0, by rw [FiniteFp.toVal_isZero hm]; simp⟩
  · by_cases hs : f.s = false
    · exact FiniteFp.toVal_int_mul_zpow (R := ℚ) f hs _ (by have := f.valid.1; omega)
    · -- s = true: f.toVal = -(-f).toVal, and -f has s = false
      have hns : (-f).s = false := by simp [FiniteFp.neg_def, hs]
      have hne : (-f).e = f.e := by simp [FiniteFp.neg_def]
      obtain ⟨n, hn⟩ := FiniteFp.toVal_int_mul_zpow (R := ℚ) (-f) hns
        (FloatFormat.min_exp - FloatFormat.prec + 1) (by rw [hne]; have := f.valid.1; omega)
      refine ⟨-n, ?_⟩
      rw [FiniteFp.toVal_neg_eq_neg] at hn
      push_cast; linarith

/-- Distinct representable values differ by at least `sps.toVal`. -/
private theorem distinct_toVal_gap (f g : FiniteFp) (h : (f.toVal : ℚ) < g.toVal) :
    (FiniteFp.smallestPosSubnormal.toVal : ℚ) ≤ (g.toVal : ℚ) - f.toVal := by
  obtain ⟨a, ha⟩ := toVal_int_mul_sps f
  obtain ⟨b, hb⟩ := toVal_int_mul_sps g
  rw [FiniteFp.smallestPosSubnormal_toVal]
  have he_pos : (0 : ℚ) < (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by positivity
  have hab : a < b := by
    by_contra h_le; push_neg at h_le
    have : (b : ℚ) * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) ≤
           (a : ℚ) * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) :=
      mul_le_mul_of_nonneg_right (Int.cast_le.mpr h_le) (le_of_lt he_pos)
    linarith [ha, hb]
  have hab1 : 1 ≤ b - a := by omega
  have hgap : (g.toVal : ℚ) - f.toVal = (b - a : ℤ) * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by
    rw [ha, hb]; push_cast; ring
  rw [hgap]
  calc (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
      = 1 * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by ring
    _ ≤ (b - a : ℤ) * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hab1) (le_of_lt he_pos)

/-- Distinct representable values differ by more than `neighborStep`. -/
private theorem distinct_toVal_gt_neighborStep (f g : FiniteFp) (h : (f.toVal : ℚ) < g.toVal) :
    neighborStep < (g.toVal : ℚ) - f.toVal := by
  calc neighborStep
      < (FiniteFp.smallestPosSubnormal.toVal : ℚ) := neighborStep_lt_smallestPosSubnormal
    _ ≤ (g.toVal : ℚ) - f.toVal := distinct_toVal_gap f g h

/-- If `f.toVal < g.toVal` for representable f, g, then `stepUpVal f ≤ g.toVal`. -/
private theorem stepUpVal_le_of_toVal_lt (f g : FiniteFp) (h : (f.toVal : ℚ) < g.toVal) :
    stepUpVal f ≤ (g.toVal : ℚ) := by
  unfold stepUpVal
  linarith [distinct_toVal_gt_neighborStep f g h]

/-! ## Property 1 & 2: nextUp/nextDown ordering -/

/-- `Fp.finite f < nextUp (Fp.finite f)` when `nextUp` returns a finite float. -/
theorem finite_lt_nextUp (f u : FiniteFp)
    (hu : nextUp (Fp.finite f) = Fp.finite u) :
    Fp.finite f < Fp.finite u := by
  simp only [nextUp_finite] at hu
  have hge := findSuccessor_ge (stepUpVal f) u hu
  have hlt : (f.toVal : ℚ) < (u.toVal : ℚ) :=
    lt_of_lt_of_le (by unfold stepUpVal; linarith [neighborStep_pos]) hge
  exact (Fp.finite_le_finite_iff _ _).mpr (le_of_lt (FiniteFp.toVal_lt ℚ hlt))
    |>.lt_of_ne (by intro heq; rw [Fp.finite.injEq] at heq; subst heq; linarith)

/-- `Fp.finite f ≤ nextUp (Fp.finite f)` for all finite `f`. -/
theorem finite_le_nextUp (f : FiniteFp) :
    Fp.finite f ≤ nextUp (Fp.finite f) := by
  simp only [nextUp_finite]
  match hres : findSuccessor (stepUpVal f) with
  | Fp.finite u =>
    exact le_of_lt (finite_lt_nextUp f u (by simp [nextUp_finite, hres]))
  | Fp.infinite false => exact Fp.le_pos_inf _
  | Fp.infinite true => exact absurd hres (findSuccessor_ne_neg_inf (stepUpVal f))
  | Fp.NaN => exact absurd hres (findSuccessor_ne_nan (stepUpVal f))

/-- `nextDown (Fp.finite f) < Fp.finite f` when `nextDown` returns a finite float. -/
theorem nextDown_lt_finite (f d : FiniteFp)
    (hd : nextDown (Fp.finite f) = Fp.finite d) :
    Fp.finite d < Fp.finite f := by
  simp only [nextDown_finite] at hd
  have hle := findPredecessor_le_val (stepDownVal f) d hd
  have hlt : (d.toVal : ℚ) < (f.toVal : ℚ) :=
    lt_of_le_of_lt hle (by unfold stepDownVal; linarith [neighborStep_pos])
  exact (Fp.finite_le_finite_iff _ _).mpr (le_of_lt (FiniteFp.toVal_lt ℚ hlt))
    |>.lt_of_ne (by intro heq; rw [Fp.finite.injEq] at heq; subst heq; linarith)

/-- `nextDown (Fp.finite f) ≤ Fp.finite f` for all finite `f`. -/
theorem nextDown_le_finite (f : FiniteFp) :
    nextDown (Fp.finite f) ≤ Fp.finite f := by
  simp only [nextDown_finite]
  match hres : findPredecessor (stepDownVal f) with
  | Fp.finite d =>
    exact le_of_lt (nextDown_lt_finite f d (by simp [nextDown_finite, hres]))
  | Fp.infinite true => exact Fp.neg_inf_le_of_not_nan _ (by simp)
  | Fp.infinite false => exact absurd hres (findPredecessor_ne_pos_inf (stepDownVal f))
  | Fp.NaN => exact absurd hres (findPredecessor_ne_nan (stepDownVal f))

/-! ## Property 3: No float between f and nextUp f / nextDown f and f -/

/-- `findSuccessor` applied to a representable non-neg-zero value returns that value. -/
private theorem findSuccessor_idempotent (g : FiniteFp) (hg : g.notNegZero) :
    findSuccessor (g.toVal : ℚ) = Fp.finite g :=
  roundUp_idempotent (R := ℚ) g hg

/-- No representable float has a value strictly between `f.toVal` and `(nextUp f).toVal`.
Stated at the `toVal` level to avoid signed-zero ordering subtleties. -/
theorem nextUp_no_float_between (f u : FiniteFp)
    (hu : nextUp (Fp.finite f) = Fp.finite u) (g : FiniteFp)
    (hg_lower : (f.toVal : ℚ) < g.toVal)
    (hg_upper : (g.toVal : ℚ) < u.toVal) : False := by
  simp only [nextUp_finite] at hu
  -- Key: f.toVal < g.toVal implies stepUpVal f ≤ g.toVal (grid alignment)
  have hge := stepUpVal_le_of_toVal_lt f g hg_lower
  -- Since g.toVal > 0 or we handle neg-zero
  by_cases hgnz : g.notNegZero
  · -- g is not neg-zero: findSuccessor(g.toVal) = Fp.finite g
    have hfix := findSuccessor_idempotent g hgnz
    -- By monotonicity: findSuccessor(stepUpVal f) ≤ findSuccessor(g.toVal)
    have hmono : findSuccessor (stepUpVal f) ≤ findSuccessor (g.toVal : ℚ) :=
      findSuccessor_mono (R := ℚ) hge
    rw [hu, hfix] at hmono
    -- u ≤ g in Fp ordering
    have hle := FiniteFp.le_toVal_le ℚ ((Fp.finite_le_finite_iff _ _).mp hmono)
    linarith
  · -- g is neg-zero: g.toVal = 0
    simp only [FiniteFp.notNegZero] at hgnz; push_neg at hgnz
    have hg_zero : g.isZero := by unfold FiniteFp.isZero; omega
    have hg_val : (g.toVal : ℚ) = 0 := FiniteFp.toVal_isZero hg_zero
    -- stepUpVal f ≤ 0 and findSuccessor(stepUpVal f) ≤ findSuccessor(0) = Fp.finite 0
    have h0 : stepUpVal f ≤ (0 : ℚ) := by linarith [hg_val]
    have hmono : findSuccessor (stepUpVal f) ≤ findSuccessor (0 : ℚ) :=
      findSuccessor_mono (R := ℚ) h0
    rw [findSuccessor_zero (R := ℚ), hu] at hmono
    have hule := FiniteFp.le_toVal_le ℚ ((Fp.finite_le_finite_iff _ _).mp hmono)
    rw [FiniteFp.toVal_zero (R := ℚ)] at hule
    linarith [hg_val]

/-- No representable float has a value strictly between `(nextDown f).toVal` and `f.toVal`. -/
theorem nextDown_no_float_between (f d : FiniteFp)
    (hd : nextDown (Fp.finite f) = Fp.finite d) (g : FiniteFp)
    (hg_lower : (d.toVal : ℚ) < g.toVal)
    (hg_upper : (g.toVal : ℚ) < f.toVal) : False := by
  simp only [nextDown_finite] at hd
  -- f.toVal > g.toVal implies stepDownVal f ≥ g.toVal (grid alignment: f-g ≥ sps > neighborStep)
  have hge : (g.toVal : ℚ) ≤ stepDownVal f := by
    unfold stepDownVal
    linarith [distinct_toVal_gt_neighborStep g f hg_upper]
  by_cases hgnz : g.notNegZero
  · -- g is not neg-zero: roundDown_idempotent gives findPredecessor(g.toVal) = g
    have hfix : findPredecessor (g.toVal : ℚ) = Fp.finite g := by
      simpa [roundDown] using (roundDown_idempotent (R := ℚ) g hgnz)
    have hmono : findPredecessor (g.toVal : ℚ) ≤ findPredecessor (stepDownVal f) :=
      findPredecessor_mono (R := ℚ) hge
    rw [hfix, hd] at hmono
    have hle := FiniteFp.le_toVal_le ℚ ((Fp.finite_le_finite_iff _ _).mp hmono)
    linarith
  · -- g is neg-zero: g.toVal = 0
    simp only [FiniteFp.notNegZero] at hgnz; push_neg at hgnz
    have hg_zero : g.isZero := by unfold FiniteFp.isZero; omega
    have hg_val : (g.toVal : ℚ) = 0 := FiniteFp.toVal_isZero hg_zero
    -- stepDownVal f ≥ 0 and findPredecessor(stepDownVal f) ≥ findPredecessor(0) = Fp.finite 0
    have h0 : (0 : ℚ) ≤ stepDownVal f := by linarith [hg_val]
    have hmono : findPredecessor (0 : ℚ) ≤ findPredecessor (stepDownVal f) :=
      findPredecessor_mono (R := ℚ) h0
    rw [findPredecessor_zero (R := ℚ), hd] at hmono
    have hdle := FiniteFp.le_toVal_le ℚ ((Fp.finite_le_finite_iff _ _).mp hmono)
    rw [FiniteFp.toVal_zero (R := ℚ)] at hdle
    linarith [hg_val]

end Rounding
