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

/-! ## Branch Construction

These lemmas prove `delta_exact` for each branch of the Neumaier algorithm.
The key chain: Sterbenz → reversed subtraction exact → representability → idempotence. -/

/-- **Reversed subtraction is exact**: if `fl(t - a) = t - a` exactly, then
    `fl(a - t) = a - t` exactly. -/
theorem reversed_sub_exact
    [RModeExec] [RMode R] [RoundIntSigMSound R] [RModeIdem R]
    (a t w : FiniteFp)
    (hw : a - t = Fp.finite w)
    (z : FiniteFp) (hz_val : (z.toVal : R) = t.toVal - a.toVal) :
    (w.toVal : R) = a.toVal - t.toVal := by
  by_cases hat : (a.toVal : R) - t.toVal = 0
  · exact (KahanSum.fpSub_exact_zero (R := R) a t w hw hat).symm ▸ hat.symm
  · -- a - t ≠ 0, so z ≠ 0 and -z is representable
    have hz_ne : (z.toVal : R) ≠ 0 := by rw [hz_val]; intro h; exact hat (by linarith)
    have hm_pos : 0 < z.m := by
      by_contra h; push_neg at h
      exact hz_ne (FiniteFp.toVal_isZero (show z.isZero from by unfold FiniteFp.isZero; omega))
    have hneg_nnz : (-z).notNegZero := Or.inr (by simp [hm_pos])
    -- w.toVal = a.toVal - t.toVal = -(t.toVal - a.toVal) = (-z).toVal
    have hval : (a.toVal : R) - t.toVal = (-z).toVal := by
      rw [FiniteFp.toVal_neg_eq_neg, hz_val]; ring
    -- fl(a - t) = round(a.toVal - t.toVal) = round((-z).toVal) = -z (idempotence)
    have hsub := fpSubFinite_correct (R := R) a t hat
    simp only [sub_eq_fpSub, fpSub_coe_coe] at hsub hw
    rw [hsub, hval, RModeIdem.round_idempotent (R := R) (-z) hneg_nnz] at hw
    rw [show w = -z from Fp.finite.inj hw.symm, FiniteFp.toVal_neg_eq_neg, hz_val]; ring

/-- **Addition of representable error is exact**: if `w.toVal + x.toVal` equals a
    representable value, then `fl(w + x)` computes it exactly. -/
private theorem add_of_representable_exact
    [RModeExec] [RMode R] [RoundIntSigMSound R] [RModeIdem R]
    (w x delta : FiniteFp) (hdelta : w + x = Fp.finite delta)
    (err : FiniteFp) (herr_nnz : err.notNegZero)
    (herr_val : (err.toVal : R) = w.toVal + x.toVal) :
    (delta.toVal : R) = w.toVal + x.toVal := by
  by_cases hwx : (w.toVal : R) + x.toVal = 0
  · exact (KahanSum.fpAdd_exact_zero (R := R) w x delta hdelta hwx).symm ▸ hwx.symm
  · have hadd := fpAddFinite_correct (R := R) w x hwx
    simp only [add_eq_fpAdd, fpAdd_coe_coe] at hadd hdelta
    rw [hadd, ← herr_val, RModeIdem.round_idempotent (R := R) err herr_nnz] at hdelta
    rw [show delta = err from Fp.finite.inj hdelta.symm, herr_val]

/-- **Branch A construction**: when `|sum| ≥ |x|` (same sign, both nonzero),
    the compensation `delta = fl(fl(sum - t) + x)` captures the rounding error exactly.

    Requires intermediate fp witnesses: `w = fl(sum - t)` and `delta = fl(w + x)`. -/
theorem delta_exact_branch_A
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    [RModeConj R] [RModeIdem R] [RModeMono R]
    (sum x t : FiniteFp)
    (ht : sum + x = Fp.finite t)
    (hsame : sum.s = x.s) (hsum_nz : 0 < sum.m) (hx_nz : 0 < x.m)
    (hge : FiniteFp.toVal_mag x (R := R) ≤ FiniteFp.toVal_mag sum)
    (hne : (sum.toVal : R) + x.toVal ≠ 0)
    (w : FiniteFp) (hw : sum - t = Fp.finite w)
    (delta : FiniteFp) (hdelta : w + x = Fp.finite delta) :
    (delta.toVal : R) = sum.toVal + x.toVal - t.toVal := by
  -- Step 1: fl(t - sum) is exact by Sterbenz (via sterbenz_sub_sa_same_sign)
  obtain ⟨z_fp, _hz_sub, hz_val⟩ :=
    sterbenz_sub_sa_same_sign (R := R) sum x hsame hsum_nz hge hne t ht
  -- Step 2: fl(sum - t) is exact (reversed)
  have hw_exact : (w.toVal : R) = sum.toVal - t.toVal :=
    reversed_sub_exact (R := R) sum t w hw z_fp hz_val
  -- Step 3: sum + x - t is representable
  obtain ⟨err_fp, herr_nnz, herr_val⟩ :=
    add_error_representable_general_left_nz (R := R) sum x hsum_nz hne t ht
  -- Step 4: w + x is representable (= -err_fp or similar)
  have hwx_repr : (err_fp.toVal : R) = sum.toVal + x.toVal - t.toVal := herr_val
  -- Need: err.toVal = w.toVal + x.toVal
  have herr_eq : (err_fp.toVal : R) = w.toVal + x.toVal := by
    rw [herr_val, hw_exact]; ring
  -- Step 5: fl(w + x) = w + x
  have := add_of_representable_exact (R := R) w x delta hdelta err_fp herr_nnz herr_eq
  rw [this, hw_exact]; ring

/-- **Branch B construction**: when `|x| > |sum|` (same sign, both nonzero),
    the compensation `delta = fl(fl(x - t) + sum)` captures the rounding error exactly.

    Requires intermediate fp witnesses: `w = fl(x - t)` and `delta = fl(w + sum)`. -/
theorem delta_exact_branch_B
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    [RModeConj R] [RModeIdem R] [RModeMono R]
    (sum x t : FiniteFp)
    (ht : sum + x = Fp.finite t)
    (hsame : sum.s = x.s) (hsum_nz : 0 < sum.m) (hx_nz : 0 < x.m)
    (hgt : FiniteFp.toVal_mag sum (R := R) ≤ FiniteFp.toVal_mag x)
    (hne : (sum.toVal : R) + x.toVal ≠ 0)
    (w : FiniteFp) (hw : x - t = Fp.finite w)
    (delta : FiniteFp) (hdelta : w + sum = Fp.finite delta) :
    (delta.toVal : R) = sum.toVal + x.toVal - t.toVal := by
  -- Use commutativity: sum + x = x + sum
  have ht' : x + sum = Fp.finite t := by
    rw [show (x : Fp) + sum = sum + x from fpAdd_comm x sum]; exact ht
  -- Step 1: fl(t - x) is exact by Sterbenz (x is the larger operand)
  have hsame' : x.s = sum.s := hsame.symm
  obtain ⟨z_fp, _hz_sub, hz_val⟩ :=
    sterbenz_sub_sa_same_sign (R := R) x sum hsame' hx_nz hgt
      (show (x.toVal : R) + sum.toVal ≠ 0 by rwa [add_comm]) t ht'
  -- Step 2: fl(x - t) is exact (reversed)
  have hw_exact : (w.toVal : R) = x.toVal - t.toVal :=
    reversed_sub_exact (R := R) x t w hw z_fp hz_val
  -- Step 3: x + sum - t is representable
  obtain ⟨err_fp, herr_nnz, herr_val⟩ :=
    add_error_representable_general_left_nz (R := R) x sum hx_nz
      (show (x.toVal : R) + sum.toVal ≠ 0 by rwa [add_comm]) t ht'
  -- err.toVal = x + sum - t = w + sum
  have herr_eq : (err_fp.toVal : R) = w.toVal + sum.toVal := by
    rw [herr_val, hw_exact]; ring
  -- Step 4: fl(w + sum) = w + sum
  have := add_of_representable_exact (R := R) w sum delta hdelta err_fp herr_nnz herr_eq
  rw [this, hw_exact]; ring

/-! ## Compensation Growth -/

/-- **Compensation growth bound**: `|comp_n| ≤ (1+η)^n · |comp_0| + (1+η)((1+η)^n - 1)·S`.

    This captures how the compensation magnitude grows over n steps. When `comp_0 = 0`,
    the bound simplifies to `(1+η)((1+η)^n - 1)·S`. -/
theorem comp_growth [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final)
    (hnr : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      NStepNormalRange (R := R) st x step)
    (S : R) (hS : 0 ≤ S)
    (hM : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      |(st.sum.toVal : R) + x.toVal| ≤ S) :
    |final.comp.toVal (R := R)| ≤
      (1 + η) ^ xs.length * |init.comp.toVal (R := R)| +
      (1 + η) * ((1 + η) ^ xs.length - 1) * S := by
  induction trace with
  | nil => simp
  | cons step rest ih =>
    rename_i st₀ xi xs_tail fin₁
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    have hcd := compDelta_le_comp_eta_add st₀ _ step (hnr st₀ _ step)
    have hρ := stepRho_abs_le st₀ _ step (hnr st₀ _ step)
    have hM_step := hM st₀ _ step
    have hdelta := delta_abs_le st₀ _ step (hnr st₀ _ step)
    -- Bound |step.comp'| ≤ (1+η)(|comp₀| + ηS)
    have hcomp' : |step.comp'.toVal (R := R)| ≤
        (1 + η) * |st₀.comp.toVal (R := R)| + (1 + η) * η * S := by
      have heq : step.comp'.toVal (R := R) =
          (st₀.comp.toVal + step.delta.toVal) + stepRho (R := R) st₀ _ step := by
        unfold stepRho; ring
      rw [heq]
      have h1 := abs_add_le (st₀.comp.toVal (R := R) + step.delta.toVal)
        (stepRho (R := R) st₀ _ step)
      have hcd_nn := abs_nonneg (st₀.comp.toVal (R := R) + step.delta.toVal)
      have hrho_nn := abs_nonneg (stepRho (R := R) st₀ _ step)
      -- |comp + delta + ρ| ≤ (1+η)|comp + delta| ≤ (1+η)(|comp₀| + ηS)
      have hcd_bound : |(st₀.comp.toVal (R := R) + step.delta.toVal)| ≤
          |st₀.comp.toVal (R := R)| + η * S := by
        nlinarith [abs_nonneg (st₀.sum.toVal (R := R) + xi.toVal)]
      nlinarith [mul_nonneg (show (0:R) ≤ 1 + η by linarith) hcd_nn,
                 mul_le_mul_of_nonneg_left hcd_bound (show (0:R) ≤ 1 + η by linarith),
                 mul_nonneg hη (abs_nonneg (st₀.comp.toVal (R := R)))]
    -- IH for rest
    simp only [List.length_cons]
    have hpow : (1 + η : R) ^ (xs_tail.length + 1) = (1 + η) * (1 + η) ^ xs_tail.length := by
      rw [pow_succ]; ring
    -- ih rewrites: step.nextState.comp = step.comp'
    -- ih has step.nextState.comp; definitionally this equals step.comp'
    -- We rewrite ih to get the bound in terms of step.comp'
    have ih' : |fin₁.comp.toVal (R := R)| ≤
        (1 + η) ^ xs_tail.length * |step.comp'.toVal (R := R)| +
        (1 + η) * ((1 + η) ^ xs_tail.length - 1) * S := by
      have hns : (step.nextState (R := R)).comp.toVal (R := R) = step.comp'.toVal (R := R) := rfl
      rw [hns] at ih; exact ih
    rw [hpow]
    have hpow_nn := pow_nonneg (show (0 : R) ≤ 1 + η by linarith) xs_tail.length
    nlinarith [abs_nonneg (st₀.comp.toVal (R := R)),
               abs_nonneg (step.comp'.toVal (R := R)),
               mul_nonneg hpow_nn (abs_nonneg (step.comp'.toVal (R := R))),
               mul_nonneg hpow_nn (abs_nonneg (st₀.comp.toVal (R := R))),
               mul_nonneg (mul_nonneg (show (0:R) ≤ 1+η by linarith) hpow_nn)
                          (abs_nonneg (st₀.comp.toVal (R := R)))]

/-! ## Capstone -/

/-- Generalized comp-delta sum bound: allows nonzero initial compensation.
    `traceCompDeltaSum ≤ n·(1+η)^n·|init.comp| + n·(1+η)·((1+η)^n - 1)·S`. -/
private theorem traceCompDeltaSum_bound_gen [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final)
    (hnr : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      NStepNormalRange (R := R) st x step)
    (S : R) (hS : 0 ≤ S)
    (hM : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      |(st.sum.toVal : R) + x.toVal| ≤ S) :
    traceCompDeltaSum (R := R) trace ≤
      (xs.length : R) * (1 + η) ^ xs.length * |init.comp.toVal (R := R)| +
      (xs.length : R) * (1 + η) * ((1 + η) ^ xs.length - 1) * S := by
  induction trace with
  | nil => simp [traceCompDeltaSum]
  | cons step rest ih =>
    rename_i st₀ xi xs_tail fin₁
    simp only [traceCompDeltaSum, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    have hpow_nn := pow_nonneg (show (0 : R) ≤ 1 + η by linarith) xs_tail.length
    have hS_nn := hS
    -- Bound |comp₀ + delta₀|
    have hcd := compDelta_le_comp_eta_add st₀ xi step (hnr st₀ xi step)
    -- Bound |step.comp'| via comp_growth on a single step
    have hcomp'_bound : |step.comp'.toVal (R := R)| ≤
        (1 + η) * |st₀.comp.toVal (R := R)| + (1 + η) * η * S := by
      have hM_step := hM st₀ xi step
      have hdelta := delta_abs_le st₀ xi step (hnr st₀ xi step)
      have hρ := stepRho_abs_le st₀ xi step (hnr st₀ xi step)
      have hcd' := compDelta_le_comp_eta_add st₀ xi step (hnr st₀ xi step)
      have heq : step.comp'.toVal (R := R) =
          (st₀.comp.toVal + step.delta.toVal) + stepRho (R := R) st₀ xi step := by
        unfold stepRho; ring
      rw [heq]
      have h1 := abs_add_le (st₀.comp.toVal (R := R) + step.delta.toVal)
        (stepRho (R := R) st₀ xi step)
      have hcd_bound : |(st₀.comp.toVal (R := R) + step.delta.toVal)| ≤
          |st₀.comp.toVal (R := R)| + η * S := by
        nlinarith [abs_nonneg (st₀.sum.toVal (R := R) + xi.toVal)]
      nlinarith [abs_nonneg (st₀.comp.toVal (R := R) + step.delta.toVal),
                 abs_nonneg (stepRho (R := R) st₀ xi step),
                 mul_nonneg hη (abs_nonneg (st₀.comp.toVal (R := R) + step.delta.toVal)),
                 mul_le_mul_of_nonneg_left hcd_bound (show (0:R) ≤ 1 + η by linarith)]
    -- IH: rewrites step.nextState.comp = step.comp'
    have ih' : traceCompDeltaSum (R := R) rest ≤
        (xs_tail.length : R) * (1 + η) ^ xs_tail.length * |step.comp'.toVal (R := R)| +
        (xs_tail.length : R) * (1 + η) * ((1 + η) ^ xs_tail.length - 1) * S := by
      have hns : (step.nextState (R := R)).comp.toVal (R := R) = step.comp'.toVal (R := R) := rfl
      rw [hns] at ih; exact ih
    have hpow_succ : (1 + η : R) ^ (xs_tail.length + 1) =
        (1 + η) * (1 + η) ^ xs_tail.length := by rw [pow_succ]; ring
    have hM_step := hM st₀ xi step
    -- Combine: |cd| + sum_rest ≤ target
    -- |cd| ≤ |st₀.comp| + η·S
    -- sum_rest ≤ n·(1+η)^n·|comp'| + n·(1+η)·((1+η)^n-1)·S
    --         ≤ n·(1+η)^n·((1+η)|comp₀| + (1+η)ηS) + n·(1+η)·((1+η)^n-1)·S
    have hcomp₀_nn := abs_nonneg (st₀.comp.toVal (R := R))
    have hcomp'_nn := abs_nonneg (step.comp'.toVal (R := R))
    have hn_nn : (0 : R) ≤ xs_tail.length := Nat.cast_nonneg' (n := xs_tail.length)
    have h1η_pos : (0 : R) ≤ 1 + η := by linarith
    -- rest ≤ n·(1+η)^{n+1}·|c₀| + n·(1+η)^{n+1}·η·S + n·(1+η)·((1+η)^n-1)·S
    have hrest_bound : traceCompDeltaSum (R := R) rest ≤
        (xs_tail.length : R) * (1 + η) ^ xs_tail.length *
          ((1 + η) * |st₀.comp.toVal (R := R)| + (1 + η) * η * S) +
        (xs_tail.length : R) * (1 + η) * ((1 + η) ^ xs_tail.length - 1) * S := by
      calc traceCompDeltaSum (R := R) rest
          ≤ (xs_tail.length : R) * (1 + η) ^ xs_tail.length * |step.comp'.toVal (R := R)| +
            (xs_tail.length : R) * (1 + η) * ((1 + η) ^ xs_tail.length - 1) * S := ih'
        _ ≤ (xs_tail.length : R) * (1 + η) ^ xs_tail.length *
              ((1 + η) * |st₀.comp.toVal (R := R)| + (1 + η) * η * S) +
            (xs_tail.length : R) * (1 + η) * ((1 + η) ^ xs_tail.length - 1) * S := by
            have := mul_le_mul_of_nonneg_left hcomp'_bound (mul_nonneg hn_nn hpow_nn)
            linarith
    -- Now combine: |cd| + rest ≤ target = (n+1)·(1+η)^{n+1}·|c₀| + (n+1)·(1+η)·((1+η)^{n+1}-1)·S
    -- Expand hrest_bound: rest ≤ n·(1+η)^{n+1}·|c₀| + n·(1+η)^{n+1}·η·S + n·(1+η)^{n+1}·S - n·(1+η)·S
    -- Total: |c₀| + η·S + n·(1+η)^{n+1}·|c₀| + n·(1+η)^{n+1}·η·S + n·(1+η)^{n+1}·S - n·(1+η)·S
    -- Target: (n+1)·(1+η)^{n+1}·|c₀| + (n+1)·(1+η)·((1+η)^{n+1}-1)·S
    -- Let P = (1+η)^{n+1}. Suffice: |c₀| ≤ n·(P-1)·|c₀| + extra... actually need:
    -- (n+1)·P·|c₀| ≥ |c₀| + n·(1+η)·P·|c₀| = |c₀|(1 + n·P·(1+η)/...) hmm
    -- Break into |c₀| part and S part separately
    have hP := hpow_succ  -- (1+η)^{n+1} = (1+η) * (1+η)^n
    have hpow1 : (1 : R) ≤ (1 + η) ^ xs_tail.length :=
      one_le_pow₀ h1η
    -- For |c₀| part: (1 + n*(1+η)^{n+1}) ≤ (n+1)*(1+η)^{n+1}
    -- iff 1 ≤ (1+η)^{n+1}, which holds
    have hcomp₀_part : |st₀.comp.toVal (R := R)| +
        (xs_tail.length : R) * (1 + η) ^ xs_tail.length * ((1 + η) * |st₀.comp.toVal (R := R)|) ≤
        ((xs_tail.length : R) + 1) * (1 + η) ^ (xs_tail.length + 1) * |st₀.comp.toVal (R := R)| := by
      rw [hP]; nlinarith [mul_nonneg hpow_nn hcomp₀_nn, mul_nonneg hn_nn hpow_nn,
                           mul_nonneg (mul_nonneg hn_nn hpow_nn) hcomp₀_nn]
    -- For S part: η·S + n·(1+η)^{n+1}·η·S + n·(1+η)^{n+1}·S - n·(1+η)·S
    --           ≤ (n+1)·(1+η)·((1+η)^{n+1}-1)·S
    -- = (n+1)·(1+η)^{n+2}·S - (n+1)·(1+η)·S
    -- LHS = η·S + n·Q·η·S + n·Q·S - n·(1+η)·S where Q = (1+η)^{n+1}
    --     = η·S(1 + n·Q) + n·Q·S - n·(1+η)·S
    -- Need: η·S(1 + n·Q) + n·Q·S - n·(1+η)·S ≤ (n+1)·(1+η)·Q·S - (n+1)·(1+η)·S
    -- i.e., η·(1 + n·Q) + n·Q - n·(1+η) ≤ (n+1)·(1+η)·Q - (n+1)·(1+η)
    -- = (n+1)·Q·(1+η) - (n+1)·(1+η) - n·Q + n·(1+η) - η·(1+n·Q)
    -- = Q·((n+1)·(1+η) - n) - (1+η) - η - η·n·Q
    -- = Q·(n·η + 1) - (1 + 2η) - η·n·Q
    -- = Q·(n·η + 1 - η·n) - (1+2η) = Q - (1+2η) ≥ 0 when Q ≥ 1+2η
    -- Actually Q = (1+η)^{n+1} ≥ 1 + (n+1)η ≥ 1 + η ≥ 1+2η for n ≥ 1... not always
    -- Key inequality: (1+η)*(1+η)*(1+η)^n ≥ 1+2η
    -- From: (1+η)*(1+η) = 1+2η+η² ≥ 1+2η, and (1+η)^n ≥ 1
    -- Break hS_part into linear steps using the identity:
    -- RHS - LHS = S * ((1+η)*(1+η)*(1+η)^n - 1 - 2η)
    -- Need: (1+η)*(1+η)*(1+η)^n ≥ 1 + 2η
    -- Step 1: set a := (1+η)*(1+η)*(1+η)^n and b := (1+η)^n*(1+2η)
    have heta_sq : (0 : R) ≤ (η : R) * η := mul_self_nonneg (η : R)
    -- (1+η)*P ≥ P ≥ 1 where P = (1+η)^n
    have hP1 := hpow1  -- 1 ≤ P
    -- (1+η)*(1+η)*P - (1+2η) = (η*η)*P + (1+2η)*(P-1) + (1+2η) - (1+2η)
    --                         = η²*P + (1+2η)*(P-1) ≥ 0
    have h12eta : (0 : R) ≤ 1 + 2 * η := by linarith
    -- (1+2η)*(P-1) ≥ 0 since P ≥ 1 and 1+2η ≥ 0
    have h12eta_P1 : (0 : R) ≤ (1 + 2 * η) * ((1 + η) ^ xs_tail.length - 1) :=
      mul_nonneg h12eta (by linarith)
    -- (η*η)*P ≥ 0
    have heta_sq_P : (0 : R) ≤ (η * η) * (1 + η) ^ xs_tail.length :=
      mul_nonneg (mul_self_nonneg (η:R)) hpow_nn
    -- Therefore (1+η)*(1+η)*(1+η)^n ≥ 1+2η:
    have hpow2_ge : (1 + η : R) * (1 + η) * (1 + η) ^ xs_tail.length ≥ 1 + 2 * η := by
      have : (1 + η : R) * (1 + η) * (1 + η) ^ xs_tail.length =
          (1 + 2 * η) * (1 + η) ^ xs_tail.length + η * η * (1 + η) ^ xs_tail.length := by ring
      linarith [mul_nonneg h12eta hpow_nn, le_mul_of_one_le_right h12eta hpow1]
    -- hS_key: (1+η)*(1+η)*(1+η)^n - (1+2η) ≥ 0, so the S gap is ≥ 0
    have hS_key_nn : (0 : R) ≤ (1 + η) * (1 + η) * (1 + η) ^ xs_tail.length - (1 + 2 * η) := by
      linarith
    -- Prove hS_part via explicit linear decomposition
    -- Set Q := (1+η)^n for brevity
    set Q := (1 + η : R) ^ xs_tail.length with hQ_def
    -- We need:
    -- η*S + n*Q*(1+η)*η*S + n*(1+η)*(Q-1)*S ≤ (n+1)*(1+η)*((1+η)^{n+1}-1)*S
    -- = (n+1)*(1+η)*((1+η)*Q-1)*S  [after hpow_succ]
    -- Let's compute RHS - LHS directly:
    -- RHS - LHS = ((1+η)*(1+η)*Q - (1+2η)) * S  [ring identity]
    -- And ((1+η)*(1+η)*Q - (1+2η)) = (1+2η)*(Q-1) + η*η*Q ≥ 0
    have hS_part : η * S + (xs_tail.length : R) * Q * ((1 + η) * η * S) +
        (xs_tail.length : R) * (1 + η) * (Q - 1) * S ≤
        ((xs_tail.length : R) + 1) * (1 + η) * ((1 + η) ^ (xs_tail.length + 1) - 1) * S := by
      rw [hpow_succ]
      -- Introduce the gap term explicitly
      have hgap_eq : ((xs_tail.length : R) + 1) * (1 + η) * ((1 + η) * Q - 1) * S -
          (η * S + (xs_tail.length : R) * Q * ((1 + η) * η * S) +
           (xs_tail.length : R) * (1 + η) * (Q - 1) * S) =
          ((1 + η) * (1 + η) * Q - (1 + 2 * η)) * S := by ring
      linarith [mul_nonneg hS_key_nn hS]
    -- Simplify hcd: |comp₀+delta₀| ≤ |c₀| + η*S (using hM_step)
    have hcd' : |(st₀.comp.toVal : R) + step.delta.toVal| ≤
        |st₀.comp.toVal (R := R)| + η * S := by
      have := mul_le_mul_of_nonneg_left hM_step hη
      linarith
    -- Combine: |cd| + rest ≤ target
    -- |cd| ≤ |c₀| + η*S
    -- hrest_bound: rest ≤ n*Q*[(1+η)*|c₀| + (1+η)*η*S] + n*(1+η)*(Q-1)*S
    -- hcomp₀_part: |c₀| + n*Q*(1+η)*|c₀| ≤ (n+1)*(1+η)^{n+1}*|c₀|
    -- hS_part: η*S + n*Q*(1+η)*η*S + n*(1+η)*(Q-1)*S ≤ (n+1)*(1+η)*((1+η)^{n+1}-1)*S
    -- Total: (|c₀| + n*Q*(1+η)*|c₀|) + (η*S + n*Q*(1+η)*η*S + n*(1+η)*(Q-1)*S) ≤ target
    -- Need to use hrest_bound by separating the |c₀| and S parts
    -- The final combination step
    -- hcd': |cd| ≤ |c₀| + η*S
    -- hcomp₀_part: |c₀| + n*Q*(1+η)*|c₀| ≤ (n+1)*(1+η)^{n+1}*|c₀|
    -- hS_part: η*S + n*Q*(1+η)*η*S + n*(1+η)*(Q-1)*S ≤ (n+1)*(1+η)*((1+η)^{n+1}-1)*S
    -- hrest_bound: rest ≤ n*Q*(1+η)*|c₀| + n*Q*(1+η)*η*S + n*(1+η)*(Q-1)*S
    --   (by expanding n*Q*(stuff) + n*(1+η)*(Q-1)*S from hrest_bound)
    have h1eta_pos2 : (0 : R) ≤ (1+η)*η := mul_nonneg h1η_pos hη
    have heta_S_nn : (0 : R) ≤ (1+η) * η * S := mul_nonneg h1eta_pos2 hS
    have hrest_expand : traceCompDeltaSum (R := R) rest ≤
        (xs_tail.length : R) * Q * ((1+η) * |st₀.comp.toVal (R := R)|) +
        (xs_tail.length : R) * Q * ((1+η) * η * S) +
        (xs_tail.length : R) * (1+η) * (Q - 1) * S := by
      linarith [mul_nonneg (mul_nonneg hn_nn hpow_nn) heta_S_nn]
    linarith

/-- Bound `traceCompDeltaSum` using `comp_growth` to bound each step uniformly. -/
private theorem traceCompDeltaSum_bound [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final)
    (hnr : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      NStepNormalRange (R := R) st x step)
    (S : R) (hS : 0 ≤ S)
    (hM : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      |(st.sum.toVal : R) + x.toVal| ≤ S)
    (hinit_comp : init.comp.toVal (R := R) = 0) :
    traceCompDeltaSum (R := R) trace ≤
      (xs.length : R) * ((1 + η) ^ (xs.length + 1) - 1) * S := by
  have hgen := traceCompDeltaSum_bound_gen trace hnr S hS hM
  rw [hinit_comp, abs_zero, mul_zero, zero_add] at hgen
  have hη : (0 : R) ≤ η := by positivity
  have hpow_nn := pow_nonneg (show (0 : R) ≤ 1 + η by linarith) xs.length
  have hpow_succ : (1 + η : R) ^ (xs.length + 1) = (1 + η) * (1 + η) ^ xs.length := by
    rw [pow_succ]; ring
  have hn_nn : (0 : R) ≤ xs.length := Nat.cast_nonneg' (n := xs.length)
  have h1η : (1 : R) ≤ 1 + η := by linarith
  -- Need: n*(1+η)*((1+η)^n - 1)*S ≤ n*((1+η)^{n+1} - 1)*S
  -- Equivalently: n*(1+η)*S ≥ n*S since n*η*S ≥ 0
  -- After rw [hpow_succ]: n*((1+η)*(1+η)^n - 1)*S = n*(1+η)^n*(1+η)*S - n*S
  -- LHS: n*(1+η)*((1+η)^n-1)*S = n*(1+η)^n*(1+η)*S - n*(1+η)*S
  -- Diff: n*(1+η)*S - n*S = n*η*S ≥ 0
  rw [hpow_succ]
  nlinarith [mul_nonneg hn_nn hS, mul_nonneg hn_nn hpow_nn,
             mul_nonneg (mul_nonneg hn_nn hpow_nn) hS,
             mul_nonneg (mul_nonneg hn_nn hη) hS]

/-- **Neumaier concrete error bound**.

    `|σₙ - Σxᵢ| ≤ n · η · ((1+η)^{n+1} - 1) · S`

    where `S = Σ|xᵢ|` and `n = xs.length`. The bound is `O(n²η²S)` for small `nη`. -/
theorem neumaier_concrete_bound [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : NState}
    (trace : NTrace (R := R) xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hnr : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      NStepNormalRange (R := R) st x step)
    (S : R) (hS : 0 ≤ S)
    (hM : ∀ (st : NState) (x : FiniteFp) (step : NStepWitness (R := R) st x),
      |(st.sum.toVal : R) + x.toVal| ≤ S) :
    |final.sigma (R := R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      (xs.length : R) * η * ((1 + η) ^ (xs.length + 1) - 1) * S := by
  have habstract := neumaier_abstract_error_bound trace hinit_sum hinit_comp hnr
  have hbound := traceCompDeltaSum_bound trace hnr S hS hM hinit_comp
  have hη : (0 : R) ≤ η := by positivity
  nlinarith

end NeumaierSum
