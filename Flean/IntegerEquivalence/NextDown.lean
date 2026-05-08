import Flean.IntegerEquivalence.BitNextUp

/-! # FP ↔ Integer equivalence: `nextDown` via symmetry

Phase 1.6 of the FP ↔ Integer equivalence area.

`nextDown` and `nextUp` are sign-symmetric: `nextDown(x) = -nextUp(-x)` for
non-NaN `x`. This file ships the value-level primitive
`nextDown_finite_eq_neg_nextUp_neg` for finite inputs and uses it to derive
the structural-predecessor bridges by negation, mirroring the `nextUp`
bridges shipped in `Successor.lean` and `BitNextUp.lean`.

The bit-level symmetry is `bitNextDown b = signFlip (bitNextUp (signFlip b))`
modulo NaN handling — at the bit level, sign-flip + bit-pattern increment
equals "decrement magnitude" (toward zero on the original sign). -/

namespace Fp

/-- **Symmetry primitive (finite).** `nextDown (Fp.finite f) = -(nextUp (Fp.finite (-f)))`.
Always true — the underlying `findPredecessor`/`findSuccessor` symmetry
applies cleanly because `stepDownVal f` is never 0 for representable `f`
(the gap between any `f.toVal` and `neighborStep` is strictly positive). -/
theorem nextDown_finite_eq_neg_nextUp_neg [FloatFormat] (f : FiniteFp) :
    nextDown (Fp.finite f) = -(nextUp (Fp.finite (-f))) := by
  show findPredecessor (stepDownVal f) = -findSuccessor (stepUpVal (-f))
  have h_step : stepUpVal (-f) = -stepDownVal f := by
    unfold stepUpVal stepDownVal
    rw [FiniteFp.toVal_neg_eq_neg]; ring
  rw [h_step]
  -- Goal: findPredecessor x = -findSuccessor (-x) where x = stepDownVal f.
  set x : ℚ := stepDownVal f
  rcases lt_trichotomy x 0 with h_lt | h_eq | h_gt
  · -- x < 0
    -- findSuccessor_symm: findSuccessor x = -findPredecessor (-x). Rearranges.
    -- We want: findPredecessor x = -findSuccessor (-x).
    -- Apply findSuccessor_symm at -x (where -x > 0). Hmm doesn't apply.
    -- Direct: findPredecessor x = -findSuccessorPos (-x) (findPredecessor_neg_eq).
    --        findSuccessor (-x) = findSuccessorPos (-x) (since -x > 0).
    -- So findPredecessor x = -findSuccessor (-x).
    have h_negx_pos : 0 < -x := by linarith
    rw [findPredecessor_neg_eq _ h_lt, findSuccessor_pos_eq _ h_negx_pos]
  · -- x = 0: this case can't occur because stepDownVal f ≠ 0 for any representable f.
    -- We argue: if stepDownVal f = 0, then f.toVal = neighborStep = smallestPosSub/2.
    -- But smallestPosSub is the smallest positive representable, so f.toVal can't equal
    -- a value strictly less than it (other than 0, but f.toVal = 0 ⇒ stepDownVal = -neighborStep ≠ 0).
    exfalso
    -- Show f.toVal would equal neighborStep, contradicting representability.
    have h_f_eq : (f.toVal : ℚ) = neighborStep := by
      show f.toVal (R := ℚ) = neighborStep
      have : f.toVal (R := ℚ) - neighborStep = 0 := h_eq
      linarith
    -- For any representable f, |f.toVal| is either 0 or ≥ smallestPosSubnormal.toVal.
    -- f.toVal = neighborStep = smallestPosSub.toVal/2, which is between 0 and smallestPosSub,
    -- so f cannot be representable here.
    have hns_lt_sps : neighborStep < (FiniteFp.smallestPosSubnormal.toVal : ℚ) :=
      neighborStep_lt_smallestPosSubnormal
    have hns_pos : (0 : ℚ) < neighborStep := neighborStep_pos
    -- f.toVal > 0 (from h_f_eq + hns_pos). Hence f.s = false ∧ f.m > 0 (toVal_pos_iff).
    have hf_pos : (0 : ℚ) < f.toVal (R := ℚ) := by rw [h_f_eq]; exact hns_pos
    obtain ⟨hf_s, hf_m_pos⟩ := (FiniteFp.toVal_pos_iff (R := ℚ)).mpr hf_pos
    -- f is positive, so f.toVal ≥ smallestPosSubnormal.toVal (smallest positive value).
    -- Use `toVal_nonneg`-style + minimum-magnitude lemma. We can show
    -- |f.toVal| ≥ smallestPosSub.toVal contradicts f.toVal = neighborStep.
    -- The relevant fact: for f representable nonzero, |f.toVal| ≥ 2^(min_exp - prec + 1).
    -- This is essentially the existence of minimum spacing.
    have hf_lb : (FiniteFp.smallestPosSubnormal.toVal : ℚ) ≤ f.toVal (R := ℚ) := by
      -- f.s = false ∧ f.m ≥ 1 ⇒ f.toVal ≥ 2^(min_exp - prec + 1) = smallestPosSub.toVal.
      rw [FiniteFp.toVal_pos_eq f hf_s, FiniteFp.smallestPosSubnormal_toVal]
      have h_e_ge : FloatFormat.min_exp ≤ f.e := f.valid.1
      have h_zpow_le : (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) ≤
          (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)
      have h_m_ge : (1 : ℚ) ≤ (f.m : ℚ) := by exact_mod_cast hf_m_pos
      have h_zpow_pos : (0 : ℚ) < (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by positivity
      calc (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
          ≤ (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := h_zpow_le
        _ = 1 * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by ring
        _ ≤ (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
            mul_le_mul_of_nonneg_right h_m_ge (le_of_lt h_zpow_pos)
    linarith
  · -- x > 0
    have h_negx_neg : -x < 0 := by linarith
    -- Use findSuccessor_symm: findSuccessor (-x) = -findPredecessor x (since -x < 0).
    rw [findSuccessor_symm _ h_negx_neg]
    -- Goal: findPredecessor x = -(-findPredecessor (-(-x)))
    -- = findPredecessor (-(-x)) = findPredecessor x (using neg_neg).
    rw [neg_neg, neg_neg]

/-! ## Predecessor structures via symmetry

Define `predecessorPos f` (for positive `f`, the structural predecessor) as
`-(successorNeg (-f))`. This corresponds to "reflect, take successorNeg
(which moves toward zero on the negative side), reflect back" — exactly the
predecessor on the positive side. -/

namespace FiniteFp

variable [FloatFormat]

/-- **Structural predecessor for positive `f`.** Always finite (the smallest
positive representable's predecessor is `+0`). -/
def predecessorPos (f : FiniteFp) : Fp :=
  -(FiniteFp.successorNeg (-f))

/-- **Structural predecessor for negative `f`.** Goes more negative; can
saturate to `-∞`. -/
def predecessorNeg (f : FiniteFp) : Fp :=
  -(FiniteFp.successorPos (-f))

end FiniteFp

/-- **Bridge to `nextDown` (positive case).** For positive `f`,
`nextDown (Fp.finite f) = predecessorPos f`. Derived from the `nextUp`
symmetric bridge via the symmetry primitive. -/
theorem nextDown_finite_eq_predecessorPos [FloatFormat]
    (f : FiniteFp) (hs : f.s = false) :
    nextDown (Fp.finite f) = FiniteFp.predecessorPos f := by
  -- nextDown(.finite f) = -nextUp(.finite (-f)).
  rw [nextDown_finite_eq_neg_nextUp_neg]
  -- For -f genuinely negative (s = true; if f.m = 0 too, then -f = -0 ⇒ successorNeg gives smallestPosSub).
  have h_neg_f_s : (-f).s = true := by rw [FiniteFp.neg_def]; simp [hs]
  rw [FiniteFp.nextUp_finite_eq_successorNeg _ h_neg_f_s]
  rfl

/-- **Bridge to `nextDown` (negative case).** For negative `f`,
`nextDown (Fp.finite f) = predecessorNeg f`. -/
theorem nextDown_finite_eq_predecessorNeg [FloatFormat]
    (f : FiniteFp) (hs : f.s = true) :
    nextDown (Fp.finite f) = FiniteFp.predecessorNeg f := by
  rw [nextDown_finite_eq_neg_nextUp_neg]
  have h_neg_f_s : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
  rw [FiniteFp.nextUp_finite_eq_successorPos _ h_neg_f_s]
  rfl

end Fp
