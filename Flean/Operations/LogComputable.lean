import Flean.Operations.LogComputableSound
import Flean.Operations.LogTermination

/-! # Computable `OpRefExec` and `OpRefExecSound` Instances for log

Provides a fully verified computable `log` for floating-point arithmetic. The computation
returns either an exact representation or a "sticky cell" bracketing `|log(x)|`, and the
proof establishes that the result is always correct.

## Algorithm

1. **Degenerate case**: `x ≤ 0` or `x = 1` → return exact dummy.
2. **Domain reduction**: for `0 < x < 1`, work with `y = 1/x ≥ 1` so `log(y) > 0`.
3. **Argument reduction** (`logArgRedK`): compute `k = ⌊log₂ y⌋` so that
   `log(y) = k · log(2) + log(1+t)` with `t = y/2^k - 1 ∈ [0, 1)`.
4. **Iterative refinement** (`stickyExtractLoop (logBounds y k)`): at increasing precision
   levels, compute rational brackets around `log(y)`, then check floor agreement.

## Proof structure

Two independent threads meet at `logLoop_sound`:

### Thread 1 — Bracket correctness (LogComputableSound.lean)
- `logBounds_lower_lt_log`: strict lower bound via irrationality of log
- `logBounds_log_le_upper`: upper bound via Taylor + ln2 series
- `logBounds_lower_pos`: positivity of lower bound

### Thread 2 — Termination (LogTermination.lean)
- `stickyTryOne_logBounds_terminates`: the loop succeeds within `logFuel y` steps
-/

section LogComputable

variable [FloatFormat]

/-! ## Exact case helpers -/

/-- When `x ≤ 0 ∨ x = 1`, `logComputableRun` returns the exact dummy. -/
private theorem logComputableRun_degenerate (a : FiniteFp)
    (hx : a.toVal (R := ℚ) ≤ 0 ∨ a.toVal (R := ℚ) = 1) :
    logComputableRun a = { q := 1, e_base := -1, isExact := true } := by
  simp [logComputableRun, hx]

/-- The exact case only fires for degenerate inputs. -/
private theorem logComputableRun_exact_is_degenerate (a : FiniteFp)
    (hExact : (logComputableRun a).isExact = true) :
    a.toVal (R := ℚ) ≤ 0 ∨ a.toVal (R := ℚ) = 1 := by
  simp only [logComputableRun] at hExact
  split_ifs at hExact with h1 h2
  · exact h1
  · simp [StickyOut.toOpRefOut_isExact] at hExact
  · simp [StickyOut.toOpRefOut_isExact] at hExact

theorem logComputableRun_exact_mag_ne_zero (a : FiniteFp) (o : OpRefOut)
    (hr : logComputableRun a = o) (hExact : o.isExact = true) : o.q ≠ 0 := by
  have hx := logComputableRun_exact_is_degenerate a (hr ▸ hExact)
  rw [logComputableRun_degenerate a hx] at hr
  subst hr
  norm_num

theorem logComputableRun_exact_value (a : FiniteFp) (o : OpRefOut)
    (hr : logComputableRun a = o) (hExact : o.isExact = true) :
    intSigVal (R := ℝ) false (2 * o.q) o.e_base = logTarget a := by
  have hx := logComputableRun_exact_is_degenerate a (hr ▸ hExact)
  rw [logComputableRun_degenerate a hx] at hr
  subst hr
  simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
  simp only [logTarget, hx, ↓reduceIte]
  norm_num

/-! ## Sticky case: logTarget = log(y) -/

/-- In the non-exact branch, we have `0 < x` and `x ≠ 1`. -/
private theorem logComputableRun_nonexact_pos (a : FiniteFp)
    (hFalse : (logComputableRun a).isExact = false) :
    (0 : ℚ) < a.toVal (R := ℚ) ∧ a.toVal (R := ℚ) ≠ 1 := by
  by_contra h
  push_neg at h
  have : a.toVal (R := ℚ) ≤ 0 ∨ a.toVal (R := ℚ) = 1 := by
    by_cases hle : a.toVal (R := ℚ) ≤ 0
    · exact Or.inl hle
    · push_neg at hle; exact Or.inr (h hle)
  rw [logComputableRun_degenerate a this] at hFalse
  exact absurd hFalse (by decide)

/-- `logTarget a = log(y)` where `y = max(x, 1/x) ≥ 1`, for positive `x ≠ 1`. -/
private theorem logTarget_eq_log_y (a : FiniteFp)
    (hx_pos : (0 : ℚ) < a.toVal (R := ℚ)) (hx_ne : a.toVal (R := ℚ) ≠ 1) :
    let x : ℚ := a.toVal
    let y := if 1 < x then x else 1 / x
    logTarget a = Real.log (y : ℝ) := by
  simp only [logTarget, show ¬(a.toVal (R := ℚ) ≤ 0 ∨ a.toVal (R := ℚ) = 1) from by
    push_neg; exact ⟨hx_pos, hx_ne⟩, ↓reduceIte]
  rw [← FiniteFp.toVal_ratCast a]
  set x : ℚ := a.toVal
  by_cases h1 : 1 < x
  · simp only [h1, ↓reduceIte]
    exact abs_of_pos (Real.log_pos (by exact_mod_cast h1))
  · have hx_lt : x < 1 := lt_of_le_of_ne (not_lt.mp h1) hx_ne
    simp only [show ¬(1 < x) from h1, ↓reduceIte]; push_cast
    rw [one_div, Real.log_inv,
        abs_of_neg (Real.log_neg (by exact_mod_cast hx_pos) (by exact_mod_cast hx_lt))]

/-! ## Meeting point -/

/-- **Meeting point of correctness and termination.**

For `y > 1` (the binding condition is `hy1`; `hy` is the weak form needed by some sub-lemmas),
the loop output brackets `log(y)` in a valid sticky cell with `q ≥ 2^(prec+2)`. -/
private theorem logLoop_sound (y : ℚ) (hy : 1 ≤ y) (hy1 : 1 < y) :
    let s := stickyExtractLoop (logBounds y (logArgRedK y)) 0 (logFuel y)
    2 ^ (FloatFormat.prec.toNat + 2) ≤ s.q ∧
    inStickyInterval (R := ℝ) s.q s.e_base (Real.log (y : ℝ)) := by
  have hpos : ∀ i, 0 < (logBounds y (logArgRedK y) i).1 := by
    intro i
    have := logBounds_lower_pos y hy hy1 i
    exact_mod_cast this
  set s := stickyExtractLoop (logBounds y (logArgRedK y)) 0 (logFuel y) with hs
  suffices hq_pos : 0 < s.q by
    exact ⟨stickyExtractLoop_q_ge _ 0 (logFuel y) hpos hq_pos,
           stickyExtractLoop_sound _ 0 (logFuel y) (Real.log (y : ℝ)) hpos
              (fun i => logBounds_lower_lt_log y hy hy1 i)
              (fun i => logBounds_log_le_upper y hy i) hq_pos⟩
  rw [hs]
  exact stickyExtractLoop_pos_of_success _ 0 (logFuel y) hpos
    (stickyTryOne_logBounds_terminates y hy hy1)

/-! ## Main soundness theorems -/

/-- For positive non-one input, `logComputableRun` reduces to the sticky extraction loop. -/
private theorem logComputableRun_loop_sound (a : FiniteFp) (o : OpRefOut)
    (hr : logComputableRun a = o) (hFalse : o.isExact = false) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q ∧
    inStickyInterval (R := ℝ) o.q o.e_base (logTarget a) := by
  have ⟨hx_pos, hx_ne⟩ := logComputableRun_nonexact_pos a (hr ▸ hFalse)
  set x : ℚ := a.toVal with hx_def
  set y := if 1 < x then x else 1 / x with hy_def
  have hy_ge : 1 ≤ y := by
    simp only [hy_def]
    split_ifs with h
    · exact le_of_lt h
    · push_neg at h; rw [le_div_iff₀ hx_pos]; linarith
  have hy_gt : 1 < y := by
    simp only [hy_def]
    split_ifs with h
    · exact h
    · push_neg at h; rw [lt_div_iff₀ hx_pos]
      linarith [lt_of_le_of_ne h hx_ne]
  have hval : logComputableRun a =
      (stickyExtractLoop (logBounds y (logArgRedK y)) 0 (logFuel y)).toOpRefOut := by
    simp only [logComputableRun, ← hx_def, ← hy_def]
    simp only [show ¬(x ≤ 0 ∨ x = 1) from by push_neg; exact ⟨hx_pos, hx_ne⟩, ↓reduceIte]
  rw [hval] at hr; rw [← hr]
  simp only [StickyOut.toOpRefOut_q, StickyOut.toOpRefOut_e_base]
  have hsound := logLoop_sound y hy_ge hy_gt
  have htarget := logTarget_eq_log_y a hx_pos hx_ne
  rw [htarget]
  exact hsound

/-! ## OpRefExecSound logTarget instance -/

instance (priority := 500) : OpRefExecSound logTarget where
  exact_mag_ne_zero := fun a o hr hExact => by
    have := logComputableRun_exact_mag_ne_zero a o hr hExact; omega
  exact_value := fun a o hr hExact =>
    logComputableRun_exact_value a o hr hExact
  sticky_q_lower := fun a o hr hFalse =>
    (logComputableRun_loop_sound a o hr hFalse).1
  sticky_interval := fun a o hr hFalse =>
    (logComputableRun_loop_sound a o hr hFalse).2

end LogComputable
