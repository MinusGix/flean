import Flean.Operations.Log
import Flean.Operations.LogComputable

/-! # Adapter: `OpRefExec logTarget` → `LogApprox`

Lifts the computable log kernel (provided by `LogComputable.lean`) into
the `LogApprox` / `LogApproxSound` typeclasses used by the operation
layer.  The kernel returns brackets on `logTarget a = |Real.log a.toVal|`;
the adapter attaches a `sign` bit (`a.toVal (R := ℚ) < 1`) and lifts
the bracket to a signed `intSigVal` identity.

This file is a thin bridge — all mathematics is in `Log.lean` and
`LogComputable.lean`.  Importing it overrides the noncomputable concrete
instance from `Log.lean` with a computable path via the sticky kernel.
-/

section LogAdapter

variable [FloatFormat]

/-- Helper: `a.toVal (R := ℚ) < 1 ↔ a.toVal (R := ℝ) < 1`. -/
private theorem toVal_lt_one_iff (a : FiniteFp) :
    a.toVal (R := ℚ) < 1 ↔ (a.toVal : ℝ) < 1 := by
  rw [← FiniteFp.toVal_ratCast a]
  exact_mod_cast Iff.rfl

/-- Helper: for `a` non-degenerate in ℝ, the ℚ branching on `< 1` agrees with
`decide ((a.toVal : ℝ) < 1)` at the `Bool` level. -/
private theorem decide_toVal_lt_one_Q_eq_R (a : FiniteFp) :
    (decide (a.toVal (R := ℚ) < 1) : Bool) = decide ((a.toVal : ℝ) < 1) := by
  by_cases h : a.toVal (R := ℚ) < 1
  · have hR : (a.toVal : ℝ) < 1 := (toVal_lt_one_iff a).mp h
    simp [h, hR]
  · have hR : ¬ ((a.toVal : ℝ) < 1) := fun hR => h ((toVal_lt_one_iff a).mpr hR)
    simp [h, hR]

/-- Adapter: turn an `OpRefOut` from the log kernel into `LogApproxData`,
attaching the sign bit `a.toVal (R := ℚ) < 1`. -/
def OpRefOut.toLogApproxData (a : FiniteFp) (o : OpRefOut) : LogApproxData :=
  let sign : Bool := decide (a.toVal (R := ℚ) < 1)
  if o.isExact then .exact sign (2 * o.q) o.e_base
  else .sticky sign o.q o.e_base

instance (priority := 1000) [OpRefExec logTarget] : LogApprox where
  approx a := OpRefOut.toLogApproxData a (OpRefExec.run (target := logTarget) a)

/-- When `toLogApproxData a o = .exact sign mag e_base`, we get
`o.isExact = true`, parameter equalities, and the sign agrees with the
ℚ-level comparison. -/
private theorem toLogApproxData_exact
    {a : FiniteFp} {o : OpRefOut} {sign : Bool} {mag : ℕ} {e_base : ℤ}
    (h : OpRefOut.toLogApproxData a o = .exact sign mag e_base) :
    o.isExact = true ∧ sign = decide (a.toVal (R := ℚ) < 1) ∧
      mag = 2 * o.q ∧ e_base = o.e_base := by
  simp only [OpRefOut.toLogApproxData] at h
  split at h
  · -- o.isExact = true branch
    rename_i hExact
    refine ⟨hExact, ?_, ?_, ?_⟩
    · injection h with hsig _ _; exact hsig.symm
    · injection h with _ hmag _; exact hmag.symm
    · injection h with _ _ he; exact he.symm
  · -- o.isExact = false branch — can't produce .exact
    cases h

/-- When `toLogApproxData a o = .sticky sign q e_base`, we get
`o.isExact = false`, parameter equalities, and the sign. -/
private theorem toLogApproxData_sticky
    {a : FiniteFp} {o : OpRefOut} {sign : Bool} {q : ℕ} {e_base : ℤ}
    (h : OpRefOut.toLogApproxData a o = .sticky sign q e_base) :
    o.isExact = false ∧ sign = decide (a.toVal (R := ℚ) < 1) ∧
      q = o.q ∧ e_base = o.e_base := by
  simp only [OpRefOut.toLogApproxData] at h
  split at h
  · cases h
  · rename_i hFalse
    refine ⟨?_, ?_, ?_, ?_⟩
    · match hi : o.isExact with
      | true => exact absurd hi hFalse
      | false => rfl
    · injection h with hsig _ _; exact hsig.symm
    · injection h with _ hq _; exact hq.symm
    · injection h with _ _ he; exact he.symm

/-- For a non-degenerate input `a`, `logTarget a = |Real.log a.toVal|`. -/
private theorem logTarget_eq_abs_log
    (a : FiniteFp) (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    logTarget a = |Real.log (a.toVal : ℝ)| := by
  unfold logTarget
  have h_pos_Q : (0 : ℚ) < a.toVal (R := ℚ) := by
    have hcast := FiniteFp.toVal_ratCast a
    have : (0 : ℝ) < ((a.toVal (R := ℚ) : ℝ)) := hcast ▸ h_pos
    exact_mod_cast this
  have h_ne_Q : a.toVal (R := ℚ) ≠ 1 := by
    have hcast := FiniteFp.toVal_ratCast a
    intro hQ; apply h_ne
    rw [← hcast]; exact_mod_cast hQ
  have h_not : ¬ (a.toVal (R := ℚ) ≤ 0 ∨ a.toVal (R := ℚ) = 1) := by
    push_neg; exact ⟨h_pos_Q, h_ne_Q⟩
  simp only [h_not, ↓reduceIte]

/-- Sign-correctness: flipping `|log x|` by `decide (x < 1)` yields `log x`. -/
private theorem sign_flip_abs_log
    (a : FiniteFp) (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    (if decide (a.toVal (R := ℚ) < 1) then -|Real.log (a.toVal : ℝ)|
     else |Real.log (a.toVal : ℝ)|) = Real.log (a.toVal : ℝ) := by
  rw [decide_toVal_lt_one_Q_eq_R]
  by_cases h : (a.toVal : ℝ) < 1
  · have hlog_neg : Real.log (a.toVal : ℝ) < 0 := Real.log_neg h_pos h
    simp only [h, decide_true, ↓reduceIte, abs_of_neg hlog_neg, neg_neg]
  · have h_gt : 1 < (a.toVal : ℝ) :=
      lt_of_le_of_ne (not_lt.mp h) (Ne.symm h_ne)
    have hlog_pos : 0 < Real.log (a.toVal : ℝ) := Real.log_pos h_gt
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte,
      abs_of_pos hlog_pos]

/-- Lifted `intSigVal` identity: `intSigVal sign (2q) e_base = Real.log x`,
given that the kernel's exact identity holds and the sign is the ℚ-level
decision. -/
private theorem intSigVal_signed_eq_log
    (a : FiniteFp) (o : OpRefOut)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1)
    (hkernel : intSigVal (R := ℝ) false (2 * o.q) o.e_base = logTarget a) :
    intSigVal (R := ℝ) (decide (a.toVal (R := ℚ) < 1)) (2 * o.q) o.e_base =
      Real.log (a.toVal : ℝ) := by
  have h_target := logTarget_eq_abs_log a h_pos h_ne
  have h_intSigVal_abs :
      ((2 * o.q : ℕ) : ℝ) * (2 : ℝ) ^ o.e_base = |Real.log (a.toVal : ℝ)| := by
    have := hkernel
    unfold intSigVal at this
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, h_target]
  have h_flip := sign_flip_abs_log a h_pos h_ne
  unfold intSigVal
  match hS : decide (a.toVal (R := ℚ) < 1) with
  | true =>
      simp only [hS, ↓reduceIte] at h_flip ⊢
      linarith [h_intSigVal_abs, h_flip]
  | false =>
      simp only [hS, Bool.false_eq_true, ↓reduceIte] at h_flip ⊢
      linarith [h_intSigVal_abs, h_flip]

instance (priority := 1000) [OpRefExec logTarget] [OpRefExecSound logTarget] :
    LogApproxSound where
  exact_mag_ne_zero := by
    intro a sign mag e_base h_pos h_ne h
    change OpRefOut.toLogApproxData a (OpRefExec.run (target := logTarget) a) =
      .exact sign mag e_base at h
    obtain ⟨hExact, hsig, hmag, he⟩ := toLogApproxData_exact h
    subst hmag
    have := OpRefExecSound.exact_mag_ne_zero (target := logTarget) a _ rfl hExact
    exact this
  exact_value := by
    intro a sign mag e_base h_pos h_ne h
    change OpRefOut.toLogApproxData a (OpRefExec.run (target := logTarget) a) =
      .exact sign mag e_base at h
    obtain ⟨hExact, hsig, hmag, he⟩ := toLogApproxData_exact h
    subst hsig; subst hmag; subst he
    have hkernel :=
      OpRefExecSound.exact_value (target := logTarget) a _ rfl hExact
    exact intSigVal_signed_eq_log a _ h_pos h_ne hkernel
  sticky_q_lower := by
    intro a sign q e_base h_pos h_ne h
    change OpRefOut.toLogApproxData a (OpRefExec.run (target := logTarget) a) =
      .sticky sign q e_base at h
    obtain ⟨hFalse, hsig, hq, he⟩ := toLogApproxData_sticky h
    subst hq
    exact OpRefExecSound.sticky_q_lower (target := logTarget) a _ rfl hFalse
  sticky_interval := by
    intro a sign q e_base h_pos h_ne h
    change OpRefOut.toLogApproxData a (OpRefExec.run (target := logTarget) a) =
      .sticky sign q e_base at h
    obtain ⟨hFalse, hsig, hq, he⟩ := toLogApproxData_sticky h
    subst hq; subst he
    have hkernel :=
      OpRefExecSound.sticky_interval (target := logTarget) a _ rfl hFalse
    have h_target := logTarget_eq_abs_log a h_pos h_ne
    rw [h_target] at hkernel
    exact hkernel
  sticky_sign := by
    intro a sign q e_base h_pos h_ne h
    change OpRefOut.toLogApproxData a (OpRefExec.run (target := logTarget) a) =
      .sticky sign q e_base at h
    obtain ⟨hFalse, hsig, hq, he⟩ := toLogApproxData_sticky h
    subst hsig
    exact sign_flip_abs_log a h_pos h_ne

end LogAdapter
