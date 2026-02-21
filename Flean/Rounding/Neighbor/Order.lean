import Flean.Rounding.Neighbor.Gap
import Flean.Rounding.RoundUp

section Rounding

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [OfNat R n]
variable [FloatFormat]

section OrderLaws

/-- Monotonicity of `nextUp` on finite inputs via monotonicity of `findSuccessor`. -/
theorem nextUp_mono_finite {f g : FiniteFp}
    (hfg : (⌞f⌟[ℚ] : ℚ) ≤ ⌞g⌟[ℚ]) :
    nextUp (Fp.finite f) ≤ nextUp (Fp.finite g) := by
  have hstep : stepUpVal f ≤ stepUpVal g := by
    unfold stepUpVal
    linarith
  simpa [nextUp_finite] using (findSuccessor_mono (R := ℚ) hstep)

/-- Monotonicity of `nextDown` on finite inputs via monotonicity of `findPredecessor`. -/
theorem nextDown_mono_finite {f g : FiniteFp}
    (hfg : (⌞f⌟[ℚ] : ℚ) ≤ ⌞g⌟[ℚ]) :
    nextDown (Fp.finite f) ≤ nextDown (Fp.finite g) := by
  have hstep : stepDownVal f ≤ stepDownVal g := by
    unfold stepDownVal
    linarith
  simpa [nextDown_finite] using (findPredecessor_mono (R := ℚ) hstep)

/-- Monotonicity of `nextUp` on non-NaN inputs. -/
theorem nextUp_mono_nonNaN {x y : Fp}
    (hx : x ≠ Fp.NaN) (hy : y ≠ Fp.NaN) (hxy : x ≤ y) :
    nextUp x ≤ nextUp y := by
  cases x with
  | NaN => contradiction
  | infinite bx =>
    cases bx
    · -- x = +∞
      cases y with
      | NaN => contradiction
      | infinite b =>
        cases b <;> simp [nextUp, Fp.le_def] at hxy ⊢
      | finite g =>
        have : Fp.finite g = Fp.infinite false := (Fp.pos_inf_le_iff _).1 hxy
        simp at this
    · -- x = -∞
      cases y with
      | NaN => contradiction
      | infinite b =>
        cases b <;> simp [nextUp, Fp.le_def]
      | finite g =>
        simpa [nextUp_finite] using
          (neg_largestFiniteFloat_le_findSuccessor (R := ℚ) (stepUpVal g))
  | finite f =>
    cases y with
    | NaN => contradiction
    | infinite b =>
      cases b with
      | false =>
        exact findSuccessor_le_pos_inf (R := ℚ) (stepUpVal f)
      | true =>
        have : Fp.finite f = Fp.NaN ∨ Fp.finite f = Fp.infinite true := (Fp.le_neg_inf_iff _).1 hxy
        simp at this
    | finite g =>
      have hfg : (⌞f⌟[ℚ] : ℚ) ≤ ⌞g⌟[ℚ] := by
        exact FiniteFp.le_toVal_le ℚ ((Fp.finite_le_finite_iff _ _).mp hxy)
      exact nextUp_mono_finite hfg

/-- Monotonicity of `nextDown` on non-NaN inputs. -/
theorem nextDown_mono_nonNaN {x y : Fp}
    (hx : x ≠ Fp.NaN) (hy : y ≠ Fp.NaN) (hxy : x ≤ y) :
    nextDown x ≤ nextDown y := by
  cases x with
  | NaN => contradiction
  | infinite bx =>
    cases bx
    · -- x = +∞
      cases y with
      | NaN => contradiction
      | infinite b =>
        cases b <;> simp [nextDown, Fp.le_def] at hxy ⊢
      | finite g =>
        have : Fp.finite g = Fp.infinite false := (Fp.pos_inf_le_iff _).1 hxy
        simp at this
    · -- x = -∞
      cases y with
      | NaN => contradiction
      | infinite b =>
        cases b <;> simp [nextDown, Fp.le_def]
      | finite g =>
        simpa [nextDown_finite] using
          (neg_inf_le_findPredecessor (R := ℚ) (stepDownVal g))
  | finite f =>
    cases y with
    | NaN => contradiction
    | infinite b =>
      cases b with
      | false =>
        simpa [nextDown_finite] using
          (findPredecessor_le_largestFiniteFloat (R := ℚ) (stepDownVal f))
      | true =>
        have : Fp.finite f = Fp.NaN ∨ Fp.finite f = Fp.infinite true := (Fp.le_neg_inf_iff _).1 hxy
        simp at this
    | finite g =>
      have hfg : (⌞f⌟[ℚ] : ℚ) ≤ ⌞g⌟[ℚ] := by
        exact FiniteFp.le_toVal_le ℚ ((Fp.finite_le_finite_iff _ _).mp hxy)
      exact nextDown_mono_finite hfg

/-- Monotonicity of `nextUp` on all `Fp` values (including NaN). -/
theorem nextUp_mono {x y : Fp} (hxy : x ≤ y) :
    nextUp x ≤ nextUp y := by
  by_cases hx : x = Fp.NaN
  · subst hx
    rw [nextUp_nan]
    exact Fp.nan_le _
  · by_cases hy : y = Fp.NaN
    · subst hy
      have : x = Fp.NaN := (Fp.le_nan_iff x).1 hxy
      exact (hx this).elim
    · exact nextUp_mono_nonNaN hx hy hxy

/-- Monotonicity of `nextDown` on all `Fp` values (including NaN). -/
theorem nextDown_mono {x y : Fp} (hxy : x ≤ y) :
    nextDown x ≤ nextDown y := by
  by_cases hx : x = Fp.NaN
  · subst hx
    rw [nextDown_nan]
    exact Fp.nan_le _
  · by_cases hy : y = Fp.NaN
    · subst hy
      have : x = Fp.NaN := (Fp.le_nan_iff x).1 hxy
      exact (hx this).elim
    · exact nextDown_mono_nonNaN hx hy hxy

/-- Regression check: NaN-left boundary is monotone for `nextUp`. -/
theorem nextUp_nan_le_nextUp (x : Fp) :
    nextUp Fp.NaN ≤ nextUp x := by
  exact nextUp_mono (Fp.nan_le x)

/-- Regression check: NaN-left boundary is monotone for `nextDown`. -/
theorem nextDown_nan_le_nextDown (x : Fp) :
    nextDown Fp.NaN ≤ nextDown x := by
  exact nextDown_mono (Fp.nan_le x)

/-- Regression check: if `x ≤ NaN`, monotonicity pushes through `nextUp`. -/
theorem nextUp_mono_to_nan {x : Fp} (h : x ≤ Fp.NaN) :
    nextUp x ≤ nextUp Fp.NaN := by
  simpa using nextUp_mono h

/-- Regression check: if `x ≤ NaN`, monotonicity pushes through `nextDown`. -/
theorem nextDown_mono_to_nan {x : Fp} (h : x ≤ Fp.NaN) :
    nextDown x ≤ nextDown Fp.NaN := by
  simpa using nextDown_mono h

/-- Characterization (finite upper witnesses):
if a finite `g` is a valid finite value and has value at least `stepUpVal f`,
then it is above `nextUp(f)`. -/
theorem nextUp_finite_le_of_stepUpVal_le
    (f g : FiniteFp)
    (hg : g.notNegZero)
    (h : stepUpVal f ≤ (g.toVal : ℚ)) :
    nextUp (Fp.finite f) ≤ Fp.finite g := by
  have hfix : findSuccessor (g.toVal : ℚ) = Fp.finite g := by
    simpa [roundUp] using (roundUp_idempotent (R := ℚ) g hg)
  have hmono : findSuccessor (stepUpVal f) ≤ findSuccessor (g.toVal : ℚ) :=
    findSuccessor_mono h
  simpa [nextUp_finite, hfix] using hmono

/-- Characterization (finite lower witnesses):
if a finite `g` is a valid finite value and has value at most `stepDownVal f`,
then it is below `nextDown(f)`. -/
theorem finite_le_nextDown_of_toVal_le_stepDownVal
    (f g : FiniteFp)
    (hg : g.notNegZero)
    (h : (g.toVal : ℚ) ≤ stepDownVal f) :
    Fp.finite g ≤ nextDown (Fp.finite f) := by
  have hfix : findPredecessor (g.toVal : ℚ) = Fp.finite g := by
    simpa [roundDown] using (roundDown_idempotent (R := ℚ) g hg)
  have hmono : findPredecessor (g.toVal : ℚ) ≤ findPredecessor (stepDownVal f) :=
    findPredecessor_mono h
  simpa [nextDown_finite, hfix] using hmono

/-- `nextUp` on finite values is the least finite bound above `stepUpVal`. -/
theorem nextUp_finite_isLeastFiniteAbove_stepUpVal
    (f : FiniteFp) :
    ∀ g : FiniteFp, g.notNegZero →
      stepUpVal f ≤ (g.toVal : ℚ) →
      nextUp (Fp.finite f) ≤ Fp.finite g := by
  intro g hg h
  exact nextUp_finite_le_of_stepUpVal_le f g hg h

/-- `nextDown` on finite values is the greatest finite bound below `stepDownVal`. -/
theorem nextDown_finite_isGreatestFiniteBelow_stepDownVal
    (f : FiniteFp) :
    ∀ g : FiniteFp, g.notNegZero →
      (g.toVal : ℚ) ≤ stepDownVal f →
      Fp.finite g ≤ nextDown (Fp.finite f) := by
  intro g hg h
  exact finite_le_nextDown_of_toVal_le_stepDownVal f g hg h

/-- Strict ordering law for finite `nextUp`: under the exact-gap hypotheses, output is
strictly greater than input. -/
theorem nextUp_strict_of
    (f u : FiniteFp)
    (hN : isNormalRange (stepUpVal f))
    (hpred : findPredecessor (stepUpVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepUpVal f|) = Int.log 2 (|⌞f⌟[ℚ]|))
    (hup : IsNextUp f u) :
    f < u := by
  have hgap : ⌞u⌟[ℚ] - ⌞f⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) :=
    nextUp_gap_eq_ulp_of f u hN hpred hlog hup
  have hulp : (0 : ℚ) < Fp.ulp (⌞f⌟[ℚ]) := Fp.ulp_pos (⌞f⌟[ℚ])
  have hval : (⌞f⌟[ℚ] : ℚ) < ⌞u⌟[ℚ] := by
    linarith
  exact FiniteFp.toVal_lt ℚ hval

/-- Strict ordering law for finite `nextDown`: under the exact-gap hypotheses, output is
strictly less than input. -/
theorem nextDown_strict_of
    (f d : FiniteFp)
    (hN : isNormalRange (stepDownVal f))
    (hsucc : findSuccessor (stepDownVal f) = Fp.finite f)
    (hlog : Int.log 2 (|stepDownVal f|) = Int.log 2 (|⌞f⌟[ℚ]|))
    (hdown : IsNextDown f d) :
    d < f := by
  have hgap : ⌞f⌟[ℚ] - ⌞d⌟[ℚ] = Fp.ulp (⌞f⌟[ℚ]) :=
    nextDown_gap_eq_ulp_of f d hN hsucc hlog hdown
  have hulp : (0 : ℚ) < Fp.ulp (⌞f⌟[ℚ]) := Fp.ulp_pos (⌞f⌟[ℚ])
  have hval : (⌞d⌟[ℚ] : ℚ) < ⌞f⌟[ℚ] := by
    linarith
  exact FiniteFp.toVal_lt ℚ hval

/-- Inverse-style round-trip law: if `u` is witnessed as `nextUp(f)` and `f` is witnessed as
`nextDown(u)`, then composing the operations returns `f`. -/
theorem nextDown_nextUp_eq_self_of_witness
    (f u : FiniteFp)
    (hup : IsNextUp f u)
    (hdown : IsNextDown u f) :
    nextDown (nextUp (Fp.finite f)) = Fp.finite f := by
  calc
    nextDown (nextUp (Fp.finite f))
        = nextDown (Fp.finite u) := by
            simpa [IsNextUp] using congrArg nextDown hup
    _ = Fp.finite f := by
          simpa [IsNextDown] using hdown

/-- Inverse-style round-trip law: if `d` is witnessed as `nextDown(f)` and `f` is witnessed as
`nextUp(d)`, then composing the operations returns `f`. -/
theorem nextUp_nextDown_eq_self_of_witness
    (f d : FiniteFp)
    (hdown : IsNextDown f d)
    (hup : IsNextUp d f) :
    nextUp (nextDown (Fp.finite f)) = Fp.finite f := by
  calc
    nextUp (nextDown (Fp.finite f))
        = nextUp (Fp.finite d) := by
            simpa [IsNextDown] using congrArg nextUp hdown
    _ = Fp.finite f := by
          simpa [IsNextUp] using hup

/-- Witness-free inverse wrapper for `nextDown ∘ nextUp` on finite values:
if some finite witness round-trips, the composition returns the original input. -/
theorem nextDown_nextUp_eq_self_of_exists
    (f : FiniteFp)
    (h : ∃ u : FiniteFp, IsNextUp f u ∧ IsNextDown u f) :
    nextDown (nextUp (Fp.finite f)) = Fp.finite f := by
  rcases h with ⟨u, hup, hdown⟩
  exact nextDown_nextUp_eq_self_of_witness f u hup hdown

/-- Witness-free inverse wrapper for `nextUp ∘ nextDown` on finite values:
if some finite witness round-trips, the composition returns the original input. -/
theorem nextUp_nextDown_eq_self_of_exists
    (f : FiniteFp)
    (h : ∃ d : FiniteFp, IsNextDown f d ∧ IsNextUp d f) :
    nextUp (nextDown (Fp.finite f)) = Fp.finite f := by
  rcases h with ⟨d, hdown, hup⟩
  exact nextUp_nextDown_eq_self_of_witness f d hdown hup

end OrderLaws

end Rounding
