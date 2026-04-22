import Flean.Operations.StickyExtract
import Flean.Rounding.PolicyInstances
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Floating-Point Logarithm (Operation Layer)

Parallel to `Flean/Operations/Exp.lean`, provides an operation-layer
wrapper for the natural logarithm on floating-point arguments.

Key structural differences from `exp`:

* `log` is defined only on positive reals (`x ≤ 0` → NaN).
* `log` can produce negative values (for `0 < x < 1`), so the typeclass
  tracks the sign explicitly; the `sticky`/`exact` witnesses specify
  `|log(x)|` together with a `sign : Bool` flag.
* `log(1) = 0` is representable exactly; handled at the operation level.

The computable kernel lives in `Flean/Operations/LogComputable.lean`, which
provides an `OpRefExecSound logTarget` instance.  The adapter at the bottom
of this file lifts that instance to `LogApprox`/`LogApproxSound`.
-/

section Log

variable [FloatFormat]

/-! ## Log approximation data -/

/-- Output shape of the finite log approximation stage.

- `exact sign mag e_base` means
  `Real.log(a.toVal) = (if sign then - else +)(mag · 2^e_base)` exactly.
- `sticky sign q e_base` means `|Real.log(a.toVal)|` lies in the open
  sticky interval `(2q·2^e_base, 2(q+1)·2^e_base)`, and `sign` tracks the
  sign of `Real.log(a.toVal)` (i.e. `sign = true` iff `a.toVal < 1`).
-/
inductive LogApproxData where
  | exact (sign : Bool) (mag : ℕ) (e_base : ℤ)
  | sticky (sign : Bool) (q : ℕ) (e_base : ℤ)
deriving Repr

/-- Execution hook for finite `log` approximation.

The hook is only required to be correct on the non-degenerate domain
`0 < a.toVal ∧ a.toVal ≠ 1`.  Degenerate inputs (`a.toVal ≤ 0` and
`a.toVal = 1`) are handled at the `fpLogFinite` level, so the hook may
return an arbitrary value on them.
-/
class LogApprox where
  approx : FiniteFp → LogApproxData

/-- Semantic contract for `LogApprox` against the real `log` function.

All fields are conditional on `0 < a.toVal ∧ a.toVal ≠ 1`; the hook's
behavior on degenerate inputs is unconstrained.
-/
class LogApproxSound [LogApprox] : Prop where
  exact_mag_ne_zero :
    ∀ (a : FiniteFp) (sign : Bool) (mag : ℕ) (e_base : ℤ),
      (0 : ℝ) < (a.toVal : ℝ) → (a.toVal : ℝ) ≠ 1 →
      LogApprox.approx a = .exact sign mag e_base →
      mag ≠ 0
  /-- Sign-and-magnitude identity: the signed `intSigVal` equals `log`. -/
  exact_value :
    ∀ (a : FiniteFp) (sign : Bool) (mag : ℕ) (e_base : ℤ),
      (0 : ℝ) < (a.toVal : ℝ) → (a.toVal : ℝ) ≠ 1 →
      LogApprox.approx a = .exact sign mag e_base →
      intSigVal (R := ℝ) sign mag e_base = Real.log (a.toVal : ℝ)
  sticky_q_lower :
    ∀ (a : FiniteFp) (sign : Bool) (q : ℕ) (e_base : ℤ),
      (0 : ℝ) < (a.toVal : ℝ) → (a.toVal : ℝ) ≠ 1 →
      LogApprox.approx a = .sticky sign q e_base →
      2 ^ (FloatFormat.prec.toNat + 2) ≤ q
  /-- The sticky cell brackets `|Real.log(a.toVal)|`. -/
  sticky_interval :
    ∀ (a : FiniteFp) (sign : Bool) (q : ℕ) (e_base : ℤ),
      (0 : ℝ) < (a.toVal : ℝ) → (a.toVal : ℝ) ≠ 1 →
      LogApprox.approx a = .sticky sign q e_base →
      inStickyInterval (R := ℝ) q e_base |Real.log (a.toVal : ℝ)|
  /-- `sign` correctly tracks the sign of `Real.log(a.toVal)`: if we flip
  `|log|` according to `sign` we recover `log`. -/
  sticky_sign :
    ∀ (a : FiniteFp) (sign : Bool) (q : ℕ) (e_base : ℤ),
      (0 : ℝ) < (a.toVal : ℝ) → (a.toVal : ℝ) ≠ 1 →
      LogApprox.approx a = .sticky sign q e_base →
      (if sign then -|Real.log (a.toVal : ℝ)| else |Real.log (a.toVal : ℝ)|) =
        Real.log (a.toVal : ℝ)

/-! ## Finite-input log -/

/-- Finite-input logarithm.

Three branches:
- `a.toVal ≤ 0` — domain violation → `NaN`.
- `a.toVal = 1` — `log(1) = 0` exactly → `+0`.
- Otherwise — dispatch to `LogApprox` and round via `roundIntSigM`.

The branching is performed on the ℚ-valued `a.toVal` (which is decidable). -/
def fpLogFinite [RModeExec] [LogApprox] (a : FiniteFp) : Fp :=
  let x : ℚ := a.toVal
  if x ≤ 0 then .NaN
  else if x = 1 then .finite 0
  else
    match LogApprox.approx a with
    | .exact sign mag e_base =>
        roundIntSigM sign mag e_base
    | .sticky sign q e_base =>
        roundIntSigM sign (2 * q + 1) e_base

/-- IEEE-style `log` at the `Fp` level.

Special cases follow IEEE 754 §9.2:
- `NaN → NaN`
- `+∞ → +∞`
- `-∞ → NaN`
- finite → `fpLogFinite`
-/
def fpLog [RModeExec] [LogApprox] (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .infinite false
  | .infinite true => .NaN
  | .finite a => fpLogFinite a

@[simp] theorem fpLog_finite [RModeExec] [LogApprox] (a : FiniteFp) :
    fpLog (Fp.finite a) = fpLogFinite a := rfl

@[simp] theorem fpLog_nan [RModeExec] [LogApprox] :
    fpLog Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpLog_pos_inf [RModeExec] [LogApprox] :
    fpLog (Fp.infinite false) = Fp.infinite false := rfl

@[simp] theorem fpLog_neg_inf [RModeExec] [LogApprox] :
    fpLog (Fp.infinite true) = Fp.NaN := rfl

/-! ## Finite-case correctness -/

/-- **Correctness of `fpLogFinite` on positive inputs**.

For `0 < a.toVal`, `fpLogFinite a` equals the rounded real `log(a.toVal)`.
The proof dispatches on the three branches; `x = 1` uses `RModeZero`. -/
theorem fpLogFinite_correct
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ] [RModeZero ℝ]
    [LogApprox] [LogApproxSound]
    (a : FiniteFp) (h_pos : 0 < (a.toVal : ℝ)) :
    fpLogFinite a = ○(Real.log (a.toVal : ℝ)) := by
  unfold fpLogFinite
  -- Move positivity into ℚ for the branching.
  have h_pos_Q : (0 : ℚ) < (a.toVal : ℚ) := by
    have hcast := FiniteFp.toVal_ratCast a
    have : (0 : ℝ) < ((a.toVal (R := ℚ) : ℝ)) := hcast ▸ h_pos
    exact_mod_cast this
  have h_not_nneg : ¬ (a.toVal (R := ℚ) ≤ 0) := not_le.mpr h_pos_Q
  simp only [h_not_nneg, ↓reduceIte]
  by_cases h_one_Q : a.toVal (R := ℚ) = 1
  · -- x = 1: result is Fp.finite 0, Real.log 1 = 0.
    simp only [h_one_Q, ↓reduceIte]
    have h_one_R : (a.toVal : ℝ) = 1 := by
      have hcast := FiniteFp.toVal_ratCast a
      rw [← hcast]
      exact_mod_cast h_one_Q
    rw [h_one_R, Real.log_one]
    exact (RModeZero.round_zero (R := ℝ)).symm
  · -- Non-degenerate: dispatch to LogApprox.
    simp only [h_one_Q, ↓reduceIte]
    have h_ne_R : (a.toVal : ℝ) ≠ 1 := by
      have hcast := FiniteFp.toVal_ratCast a
      rw [← hcast]
      intro hR
      apply h_one_Q
      exact_mod_cast hR
    cases happrox : LogApprox.approx a with
    | exact sign mag e_base =>
        simp
        have hmag_ne :=
          LogApproxSound.exact_mag_ne_zero a sign mag e_base h_pos h_ne_R happrox
        have hexact :=
          LogApproxSound.exact_value a sign mag e_base h_pos h_ne_R happrox
        rw [roundIntSigM_correct_tc (R := ℝ) sign mag e_base hmag_ne, hexact]
    | sticky sign q e_base =>
        simp
        have hq_lower :=
          LogApproxSound.sticky_q_lower a sign q e_base h_pos h_ne_R happrox
        have h_exact_in :=
          LogApproxSound.sticky_interval a sign q e_base h_pos h_ne_R happrox
        have h_sign :=
          LogApproxSound.sticky_sign a sign q e_base h_pos h_ne_R happrox
        rw [sticky_roundIntSig_eq_round_tc (R := ℝ) (sign := sign)
          (q := q) (e_base := e_base) (hq_lower := hq_lower)
          (abs_exact := |Real.log (a.toVal : ℝ)|) (h_exact_in := h_exact_in)]
        rw [h_sign]

/-! ## Concrete (noncomputable) `LogApprox` instance using `Real.log`.

Mirrors `expApproxConcrete` in `Exp.lean`.  Provides a verifier-style
witness: for non-degenerate inputs, scale `|log x|` by a sufficiently
large power of two so the scaled value exceeds the sticky lower bound,
floor it, and decide between `exact` and `sticky` branches.

On degenerate inputs (`a.toVal ≤ 0` or `a.toVal = 1`) any value is
acceptable — we return a dummy `.exact false 0 0`.
-/

private abbrev logStickyLowerNat : ℕ :=
  2 ^ (FloatFormat.prec.toNat + 2)

private noncomputable def logL (a : FiniteFp) : ℝ :=
  |Real.log (a.toVal : ℝ)|

private noncomputable def logN (a : FiniteFp) : ℕ :=
  Nat.find (exists_nat_gt ((logStickyLowerNat : ℝ) / logL a))

private noncomputable def logEBase (a : FiniteFp) : ℤ :=
  -((logN a : ℤ)) - 1

private noncomputable def logScaled (a : FiniteFp) : ℝ :=
  logL a / (2 : ℝ) ^ (logEBase a + 1)

private noncomputable def logQ (a : FiniteFp) : ℕ :=
  Nat.floor (logScaled a)

private noncomputable def logSign (a : FiniteFp) : Bool :=
  decide ((a.toVal : ℝ) < 1)

private theorem logEBase_add_one (a : FiniteFp) :
    logEBase a + 1 = -((logN a : ℤ)) := by
  unfold logEBase; omega

private theorem logScaled_eq_mul_pow (a : FiniteFp) :
    logScaled a = logL a * (2 : ℝ) ^ (logN a : ℤ) := by
  unfold logScaled
  rw [logEBase_add_one, zpow_neg, div_eq_mul_inv, inv_inv]

/-- When `a` is non-degenerate (`0 < a.toVal ∧ a.toVal ≠ 1`),
`|log(a.toVal)| > 0`. -/
private theorem logL_pos (a : FiniteFp)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    0 < logL a := by
  unfold logL
  have h_log_ne : Real.log (a.toVal : ℝ) ≠ 0 := by
    intro hz
    have h_exp_eq : Real.exp (Real.log (a.toVal : ℝ)) = Real.exp 0 := by rw [hz]
    rw [Real.exp_log h_pos, Real.exp_zero] at h_exp_eq
    exact h_ne h_exp_eq
  exact abs_pos.mpr h_log_ne

private theorem logScaled_nonneg (a : FiniteFp) : 0 ≤ logScaled a := by
  unfold logScaled
  have h1 : 0 ≤ logL a := abs_nonneg _
  have h2 : 0 < (2 : ℝ) ^ (logEBase a + 1) := by positivity
  exact div_nonneg h1 (le_of_lt h2)

private theorem logScaled_pos_of_ne_one (a : FiniteFp)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    0 < logScaled a := by
  unfold logScaled
  have h2 : 0 < (2 : ℝ) ^ (logEBase a + 1) := by positivity
  exact div_pos (logL_pos a h_pos h_ne) h2

private theorem logScaled_gt_stickyLower (a : FiniteFp)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    (logStickyLowerNat : ℝ) < logScaled a := by
  have hL_pos : 0 < logL a := logL_pos a h_pos h_ne
  have hfind :
      ((logStickyLowerNat : ℝ) / logL a) < (logN a : ℝ) :=
    Nat.find_spec (exists_nat_gt ((logStickyLowerNat : ℝ) / logL a))
  have hpow : (logN a : ℝ) < (2 : ℝ) ^ (logN a : ℕ) := by
    exact_mod_cast (Nat.lt_two_pow_self : logN a < 2 ^ logN a)
  have hdiv :
      ((logStickyLowerNat : ℝ) / logL a) < (2 : ℝ) ^ (logN a : ℕ) :=
    lt_trans hfind hpow
  have hmul' : (logStickyLowerNat : ℝ) < (2 : ℝ) ^ (logN a : ℕ) * logL a :=
    (div_lt_iff₀ hL_pos).mp hdiv
  have hmul : (logStickyLowerNat : ℝ) < logL a * (2 : ℝ) ^ (logN a : ℕ) := by
    simpa [mul_comm] using hmul'
  have hzpow : (logStickyLowerNat : ℝ) < logL a * (2 : ℝ) ^ (logN a : ℤ) := by
    simpa [zpow_natCast] using hmul
  simpa [logScaled_eq_mul_pow] using hzpow

private theorem logQ_lower (a : FiniteFp)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    logStickyLowerNat ≤ logQ a := by
  unfold logQ
  refine (Nat.le_floor_iff (logScaled_nonneg a)).2 ?_
  exact le_of_lt (logScaled_gt_stickyLower a h_pos h_ne)

private theorem logQ_le_scaled (a : FiniteFp) :
    (logQ a : ℝ) ≤ logScaled a := by
  unfold logQ
  exact Nat.floor_le (logScaled_nonneg a)

private theorem logScaled_lt_q_add_one (a : FiniteFp) :
    logScaled a < (logQ a : ℝ) + 1 := by
  unfold logQ
  simpa using Nat.lt_floor_add_one (logScaled a)

omit [FloatFormat] in
private theorem log_sticky_lo_rewrite (q : ℕ) (e : ℤ) :
    (2 * (q : ℝ)) * (2 : ℝ) ^ e = (q : ℝ) * (2 : ℝ) ^ (e + 1) := by
  rw [show e + 1 = e + (1 : ℤ) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

omit [FloatFormat] in
private theorem log_sticky_hi_rewrite (q : ℕ) (e : ℤ) :
    (2 * ((q : ℝ) + 1)) * (2 : ℝ) ^ e = ((q : ℝ) + 1) * (2 : ℝ) ^ (e + 1) := by
  rw [show e + 1 = e + (1 : ℤ) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

omit [FloatFormat] in
private theorem log_even_mag_rewrite (q : ℕ) (e : ℤ) :
    (((2 * q : ℕ) : ℝ) * (2 : ℝ) ^ e) = (q : ℝ) * (2 : ℝ) ^ (e + 1) := by
  have hcast : (((2 * q : ℕ) : ℝ)) = 2 * (q : ℝ) := by norm_num
  rw [hcast, log_sticky_lo_rewrite]

/-- Absolute-value identity: for non-degenerate `a`, flipping `|log|` by
the sign bit yields `log`. -/
private theorem logSign_flip_abs (a : FiniteFp)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    (if logSign a then -|Real.log (a.toVal : ℝ)| else |Real.log (a.toVal : ℝ)|) =
      Real.log (a.toVal : ℝ) := by
  unfold logSign
  by_cases h : (a.toVal : ℝ) < 1
  · -- log negative branch
    have hlog_neg : Real.log (a.toVal : ℝ) < 0 := Real.log_neg h_pos h
    simp only [h, decide_true, ↓reduceIte]
    rw [abs_of_neg hlog_neg, neg_neg]
  · -- log positive branch
    have h_gt : 1 < (a.toVal : ℝ) :=
      lt_of_le_of_ne (not_lt.mp h) (Ne.symm h_ne)
    have hlog_pos : 0 < Real.log (a.toVal : ℝ) := Real.log_pos h_gt
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact abs_of_pos hlog_pos

/-- Non-degenerate case: `intSigVal sign (2q) e = log(x)` when
`logScaled = q`. -/
private theorem logExact_value_case (a : FiniteFp)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1)
    (hExact : logScaled a = (logQ a : ℝ)) :
    intSigVal (R := ℝ) (logSign a) (2 * logQ a) (logEBase a) =
      Real.log (a.toVal : ℝ) := by
  have hpow_ne : (2 : ℝ) ^ (logEBase a + 1) ≠ 0 := by positivity
  have hL_eq : logL a = (logQ a : ℝ) * (2 : ℝ) ^ (logEBase a + 1) := by
    unfold logScaled at hExact
    exact (div_eq_iff hpow_ne).mp hExact
  -- `intSigVal sign mag e = (if sign then -mag else mag) * 2^e`.
  unfold intSigVal
  have h_absL : |Real.log (a.toVal : ℝ)| = logL a := rfl
  by_cases h_sign : logSign a = true
  · -- sign = true, log negative, x < 1
    rw [h_sign]
    simp only [↓reduceIte]
    have h_x_lt : (a.toVal : ℝ) < 1 := by
      unfold logSign at h_sign
      exact of_decide_eq_true h_sign
    have h_log_neg : Real.log (a.toVal : ℝ) < 0 := Real.log_neg h_pos h_x_lt
    have h_L_eq_neg : logL a = -Real.log (a.toVal : ℝ) := by
      unfold logL; exact abs_of_neg h_log_neg
    calc (-((2 * logQ a : ℕ) : ℝ)) * (2 : ℝ) ^ logEBase a
        = -(((2 * logQ a : ℕ) : ℝ) * (2 : ℝ) ^ logEBase a) := by ring
      _ = -((logQ a : ℝ) * (2 : ℝ) ^ (logEBase a + 1)) := by
          rw [log_even_mag_rewrite]
      _ = -logL a := by rw [← hL_eq]
      _ = Real.log (a.toVal : ℝ) := by rw [h_L_eq_neg]; ring
  · have h_sign_false : logSign a = false := by
      cases hS : logSign a with
      | true => exact absurd hS h_sign
      | false => rfl
    rw [h_sign_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h_x_ge : 1 ≤ (a.toVal : ℝ) := by
      have h_not_lt : ¬ ((a.toVal : ℝ) < 1) := by
        unfold logSign at h_sign_false
        exact of_decide_eq_false h_sign_false
      linarith
    have h_x_gt : 1 < (a.toVal : ℝ) := lt_of_le_of_ne h_x_ge (Ne.symm h_ne)
    have h_log_pos : 0 < Real.log (a.toVal : ℝ) := Real.log_pos h_x_gt
    have h_L_eq_pos : logL a = Real.log (a.toVal : ℝ) := by
      unfold logL; exact abs_of_pos h_log_pos
    calc (((2 * logQ a : ℕ) : ℝ)) * (2 : ℝ) ^ logEBase a
        = (logQ a : ℝ) * (2 : ℝ) ^ (logEBase a + 1) := log_even_mag_rewrite _ _
      _ = logL a := hL_eq.symm
      _ = Real.log (a.toVal : ℝ) := h_L_eq_pos

/-- Non-degenerate case: when `logScaled ≠ q`, `|log(x)|` lies strictly
inside the sticky cell `(logQ, logEBase)`. -/
private theorem logSticky_interval_case (a : FiniteFp)
    (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1)
    (hExact : logScaled a ≠ (logQ a : ℝ)) :
    inStickyInterval (R := ℝ) (logQ a) (logEBase a) |Real.log (a.toVal : ℝ)| := by
  have hq_le : (logQ a : ℝ) ≤ logScaled a := logQ_le_scaled a
  have hq_lt : (logQ a : ℝ) < logScaled a :=
    lt_of_le_of_ne hq_le (fun h => hExact h.symm)
  have hq_hi : logScaled a < (logQ a : ℝ) + 1 := logScaled_lt_q_add_one a
  have hpow_pos : 0 < (2 : ℝ) ^ (logEBase a + 1) := by positivity
  have h_absL : |Real.log (a.toVal : ℝ)| = logL a := rfl
  have hlo_mul : (logQ a : ℝ) * (2 : ℝ) ^ (logEBase a + 1) < logL a := by
    have hdiv : (logQ a : ℝ) < logL a / (2 : ℝ) ^ (logEBase a + 1) := by
      simpa [logScaled] using hq_lt
    exact (lt_div_iff₀ hpow_pos).mp hdiv
  have hhi_mul : logL a < ((logQ a : ℝ) + 1) * (2 : ℝ) ^ (logEBase a + 1) := by
    have hdiv : logL a / (2 : ℝ) ^ (logEBase a + 1) < (logQ a : ℝ) + 1 := by
      simpa [logScaled] using hq_hi
    exact (div_lt_iff₀ hpow_pos).mp hdiv
  have hlo : (2 * (logQ a : ℝ)) * (2 : ℝ) ^ logEBase a < logL a := by
    rw [log_sticky_lo_rewrite]; exact hlo_mul
  have hhi : logL a < (2 * ((logQ a : ℝ) + 1)) * (2 : ℝ) ^ logEBase a := by
    calc logL a
        < ((logQ a : ℝ) + 1) * (2 : ℝ) ^ (logEBase a + 1) := hhi_mul
      _ = (2 * ((logQ a : ℝ) + 1)) * (2 : ℝ) ^ logEBase a := by
          rw [log_sticky_hi_rewrite]
  refine ⟨?_, ?_⟩
  · rw [h_absL]; exact hlo
  · rw [h_absL]; exact hhi

/-- Degenerate inputs: `a.toVal ≤ 0` or `a.toVal = 1`.  Decided
classically (noncomputable). -/
private def logDegenerate (a : FiniteFp) : Prop :=
  ¬ (0 < (a.toVal : ℝ)) ∨ (a.toVal : ℝ) = 1

open Classical in
private noncomputable instance (a : FiniteFp) : Decidable (logDegenerate a) :=
  propDecidable _

/-- Concrete approximation hook.  Noncomputable because it inspects
`Real.log`. -/
private noncomputable def logApproxConcrete (a : FiniteFp) : LogApproxData :=
  if logDegenerate a then
    .exact false 0 0  -- dummy for degenerate inputs
  else if logScaled a = (logQ a : ℝ) then
    .exact (logSign a) (2 * logQ a) (logEBase a)
  else
    .sticky (logSign a) (logQ a) (logEBase a)

private theorem not_logDegenerate_of
    {a : FiniteFp} (h_pos : 0 < (a.toVal : ℝ)) (h_ne : (a.toVal : ℝ) ≠ 1) :
    ¬ logDegenerate a := by
  unfold logDegenerate
  push_neg; exact ⟨h_pos, h_ne⟩

noncomputable instance (priority := 100) : LogApprox where
  approx := logApproxConcrete

noncomputable instance (priority := 100) : LogApproxSound where
  exact_mag_ne_zero := by
    intro a sign mag e_base h_pos h_ne h
    change logApproxConcrete a = .exact sign mag e_base at h
    unfold logApproxConcrete at h
    rw [if_neg (not_logDegenerate_of h_pos h_ne)] at h
    split_ifs at h with hExact
    · injection h with hsig hmag he
      subst hmag
      have hQpos : 0 < logStickyLowerNat := by
        unfold logStickyLowerNat
        exact Nat.two_pow_pos _
      have hqpos : 0 < logQ a :=
        lt_of_lt_of_le hQpos (logQ_lower a h_pos h_ne)
      omega
  exact_value := by
    intro a sign mag e_base h_pos h_ne h
    change logApproxConcrete a = .exact sign mag e_base at h
    unfold logApproxConcrete at h
    rw [if_neg (not_logDegenerate_of h_pos h_ne)] at h
    split_ifs at h with hExact
    · injection h with hsig hmag he
      subst hsig; subst hmag; subst he
      exact logExact_value_case a h_pos h_ne hExact
  sticky_q_lower := by
    intro a sign q e_base h_pos h_ne h
    change logApproxConcrete a = .sticky sign q e_base at h
    unfold logApproxConcrete at h
    rw [if_neg (not_logDegenerate_of h_pos h_ne)] at h
    split_ifs at h with hExact
    · injection h with hsig hq he
      subst hq
      exact logQ_lower a h_pos h_ne
  sticky_interval := by
    intro a sign q e_base h_pos h_ne h
    change logApproxConcrete a = .sticky sign q e_base at h
    unfold logApproxConcrete at h
    rw [if_neg (not_logDegenerate_of h_pos h_ne)] at h
    split_ifs at h with hExact
    · injection h with hsig hq he
      subst hq; subst he
      exact logSticky_interval_case a h_pos h_ne hExact
  sticky_sign := by
    intro a sign q e_base h_pos h_ne h
    change logApproxConcrete a = .sticky sign q e_base at h
    unfold logApproxConcrete at h
    rw [if_neg (not_logDegenerate_of h_pos h_ne)] at h
    split_ifs at h with hExact
    · injection h with hsig hq he
      subst hsig
      exact logSign_flip_abs a h_pos h_ne

end Log
