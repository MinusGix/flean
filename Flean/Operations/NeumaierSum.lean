import Flean.Operations.KahanSum

/-!
# Neumaier Summation

Extension D: Neumaier's improved compensated summation, which handles the case where
`|xᵢ| > |sumᵢ|` by conditionally swapping in the compensation step.

## Algorithm

```
sum = x[0], comp = 0
for i = 1..n-1:
  t = fl(sum + x[i])
  if |sum| >= |x[i]|:
    comp += (sum - t) + x[i]   -- Fast2Sum: sum is larger
  else:
    comp += (x[i] - t) + sum   -- Fast2Sum: x[i] is larger
  sum = t
return sum + comp
```

The key insight: in both branches, the compensation `delta` captures the rounding error
`sum + x - t` exactly (via Fast2Sum / Sterbenz + representability). This eliminates the
Dekker condition `|y| ≤ |sum|` required by standard Kahan summation.

## Error Analysis

The corrected sum `σ = sum + comp` satisfies:
  `σₙ = Σxᵢ + Σεᵢ`
where `εᵢ` is the rounding error from accumulating `comp ← fl(comp + delta)`.
Each `|εᵢ| ≤ η|compᵢ + deltaᵢ|`, giving the abstract bound
  `|σₙ - Σxᵢ| ≤ η · Σ|compᵢ + deltaᵢ|`

The step witness carries `delta_exact` as a field (like `CompensatedSum.CSStep.twosum_exact`),
abstracting away the branch choice.
-/

namespace NeumaierSum

variable [FloatFormat]

/-- State of a Neumaier summation: running sum and accumulated compensation. -/
structure NState where
  sum : FiniteFp
  comp : FiniteFp

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Corrected sum: the mathematically meaningful accumulated value. -/
def NState.sigma (st : NState) : R :=
  (st.sum.toVal : R) + st.comp.toVal

/-- One step of Neumaier summation.

    Computes `t = fl(sum + x)`, then a compensation `delta` that exactly captures
    the rounding error `sum + x - t`, and accumulates it: `comp' = fl(comp + delta)`. -/
structure NStepWitness [RModeExec] (st : NState) (x : FiniteFp) where
  /-- `t = fl(sum + x)` -/
  t : FiniteFp
  ht : st.sum + x = Fp.finite t
  /-- Compensation delta, computed via one of two branches -/
  delta : FiniteFp
  /-- The key property: delta captures the rounding error exactly -/
  delta_exact : (delta.toVal : R) = (st.sum.toVal : R) + x.toVal - t.toVal
  /-- Updated compensation: `comp' = fl(comp + delta)` -/
  comp' : FiniteFp
  hcomp : st.comp + delta = Fp.finite comp'

/-- Next state after one Neumaier step. -/
def NStepWitness.nextState [RModeExec] {st : NState} {x : FiniteFp}
    (step : NStepWitness (R := R) st x) : NState :=
  ⟨step.t, step.comp'⟩

/-! ## Step Identity -/

/-- The per-step rounding error: the gap between `comp'` and the exact `comp + delta`. -/
def stepRho [RModeExec] (st : NState) (x : FiniteFp)
    (step : NStepWitness (R := R) st x) : R :=
  (step.comp'.toVal : R) - (st.comp.toVal + step.delta.toVal)

/-- **Corrected sum identity**: `σ' = σ + x + ρ` where `ρ` is the comp rounding error. -/
theorem neumaier_step_sigma_eq [RModeExec] (st : NState) (x : FiniteFp)
    (step : NStepWitness (R := R) st x) :
    (step.nextState (R := R)).sigma (R := R) =
      st.sigma (R := R) + x.toVal + stepRho (R := R) st x step := by
  unfold NStepWitness.nextState NState.sigma stepRho
  rw [step.delta_exact]; ring

/-! ## Normal Range and Rounding Bounds -/

/-- Normal range hypothesis for a Neumaier step. -/
structure NStepNormalRange [RModeExec] (st : NState) (x : FiniteFp)
    (step : NStepWitness (R := R) st x) where
  t_normal : isNormalRange ((st.sum.toVal : R) + x.toVal) ∨
             (st.sum.toVal : R) + x.toVal = 0
  comp_normal : isNormalRange ((st.comp.toVal : R) + step.delta.toVal) ∨
                (st.comp.toVal : R) + step.delta.toVal = 0

/-- Rounding bound on the step error ρ. -/
theorem stepRho_abs_le [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x)
    (hnr : NStepNormalRange (R := R) st x step) :
    |stepRho (R := R) st x step| ≤
      η * |(st.comp.toVal : R) + step.delta.toVal| := by
  unfold stepRho
  exact KahanSum.fpAdd_error_or_zero (R := R) st.comp step.delta step.comp'
    step.hcomp hnr.comp_normal

/-- The delta rounding error bound: `|delta| ≤ η|sum + x|`. -/
theorem delta_abs_le [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x)
    (hnr : NStepNormalRange (R := R) st x step) :
    |step.delta.toVal (R := R)| ≤ η * |(st.sum.toVal : R) + x.toVal| := by
  rw [step.delta_exact]
  have : (st.sum.toVal : R) + x.toVal - step.t.toVal =
      -((step.t.toVal : R) - (st.sum.toVal + x.toVal)) := by ring
  rw [this, abs_neg]
  exact KahanSum.fpAdd_error_or_zero (R := R) st.sum x step.t step.ht hnr.t_normal

/-! ## Trace -/

/-- A trace of Neumaier summation steps over a list. -/
inductive NTrace [RModeExec] : List FiniteFp → NState → NState → Type where
  | nil (st : NState) : NTrace [] st st
  | cons {st : NState} {x : FiniteFp} {xs : List FiniteFp} {final : NState}
      (step : NStepWitness (R := R) st x)
      (rest : NTrace xs (step.nextState (R := R)) final) :
      NTrace (x :: xs) st final

/-- Sum of per-step residuals. -/
def traceResidual [RModeExec] :
    {xs : List FiniteFp} → {init final : NState} →
    NTrace (R := R) xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons step rest =>
    stepRho (R := R) _ _ step + traceResidual rest

/-- **Telescoping identity**: corrected sum = initial + Σxᵢ + Σρᵢ. -/
theorem neumaier_trace_sigma_eq [RModeExec]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final) :
    final.sigma (R := R) =
      init.sigma (R := R) +
      (xs.map (fun x => x.toVal (R := R))).sum +
      traceResidual (R := R) trace := by
  induction trace with
  | nil => simp [traceResidual, NState.sigma]
  | cons step rest ih =>
    simp only [List.map_cons, List.sum_cons, traceResidual]
    rw [ih, neumaier_step_sigma_eq]; ring

/-! ## Abstract Error Bound -/

/-- Sum of `|comp + delta|` at each step. -/
def traceCompDeltaSum [RModeExec] :
    {xs : List FiniteFp} → {init final : NState} →
    NTrace (R := R) xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons (st := st) step rest =>
    |(st.comp.toVal : R) + step.delta.toVal| + traceCompDeltaSum rest

private theorem traceResidual_abs_le_eta_compDelta [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final)
    (hnr : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      NStepNormalRange (R := R) st x step) :
    |traceResidual (R := R) trace| ≤ η * traceCompDeltaSum (R := R) trace := by
  induction trace with
  | nil => simp [traceResidual, traceCompDeltaSum]
  | cons step rest ih =>
    simp only [traceResidual, traceCompDeltaSum]
    have hstep := stepRho_abs_le _ _ step (hnr _ _ step)
    have hη : (0 : R) ≤ η := by positivity
    -- ih : |traceResidual rest| ≤ η * traceCompDeltaSum rest
    have habs := abs_add_le (stepRho (R := R) _ _ step) (traceResidual (R := R) rest)
    nlinarith [abs_nonneg (stepRho (R := R) _ _ step)]

/-- **Abstract Neumaier error bound**: `|σₙ - Σxᵢ| ≤ η · Σ|compᵢ + deltaᵢ|`. -/
theorem neumaier_abstract_error_bound [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hnr : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      NStepNormalRange (R := R) st x step) :
    |final.sigma (R := R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      η * traceCompDeltaSum (R := R) trace := by
  have hsigma := neumaier_trace_sigma_eq trace
  have hinit : init.sigma (R := R) = 0 := by unfold NState.sigma; rw [hinit_sum, hinit_comp]; ring
  rw [hsigma, hinit, zero_add, show (xs.map (fun x => x.toVal (R := R))).sum +
      traceResidual (R := R) trace -
      (xs.map (fun x => x.toVal (R := R))).sum =
      traceResidual (R := R) trace from by ring]
  exact traceResidual_abs_le_eta_compDelta trace hnr

/-! ## Concrete Bound -/

/-- Each `|comp + delta|` is bounded by `|comp| + η|sum + x|`. -/
theorem compDelta_le_comp_eta_add [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x)
    (hnr : NStepNormalRange (R := R) st x step) :
    |(st.comp.toVal : R) + step.delta.toVal| ≤
      |st.comp.toVal (R := R)| + η * |(st.sum.toVal : R) + x.toVal| := by
  have := delta_abs_le st x step hnr
  linarith [abs_add_le (st.comp.toVal (R := R)) (step.delta.toVal (R := R))]

/-- Sum of `|sum + x|` at each step. -/
def traceAddMag [RModeExec] :
    {xs : List FiniteFp} → {init final : NState} →
    NTrace (R := R) xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons (st := st) (x := x) _ rest =>
    |(st.sum.toVal : R) + x.toVal| + traceAddMag rest

/-- Bound `traceAddMag` via an external magnitude hypothesis `M`. -/
theorem traceAddMag_le_mul_length [RModeExec]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final)
    (M : R)
    (hM : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      |(st.sum.toVal : R) + x.toVal| ≤ M) :
    traceAddMag (R := R) trace ≤ M * (xs.length : R) := by
  induction trace with
  | nil => simp [traceAddMag]
  | cons step rest ih =>
    rename_i _ _ xs_tail _
    have h := hM _ _ step
    show traceAddMag (NTrace.cons step rest) ≤ _
    unfold traceAddMag
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    have hmul : M * ((xs_tail.length : R) + 1) = M * ↑xs_tail.length + M := by ring
    linarith [add_le_add h ih]

end NeumaierSum
