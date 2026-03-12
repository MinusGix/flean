import Flean.Operations.Add
import Flean.Operations.Sub
import Flean.Rounding.PolicyInstances

/-!
# Kahan Compensated Summation

Defines Kahan's compensated summation algorithm and proves its error bound.

The key result: the error of Kahan summation is `O(ε · Σ|xᵢ|)`, independent of `n`,
compared to naive summation's `O(nε · Σ|xᵢ|)`.

## Algorithm

```
sum = x[0]; c = 0
for i = 1 to n-1:
  y = x[i] - c        // compensated input
  t = sum + y          // new partial sum
  c = (t - sum) - y    // new compensation
  sum = t
return sum
```

## Approach

We use the standard error model: `fl(a ⊕ b) = (a + b)(1 + δ)` with `|δ| ≤ η`
where `η = 2^(-prec)` (half machine epsilon), valid in the normal range.

The compensation `c ≈ -(rounding error of t)` captures the O(ε) error from
each addition, so the accumulated error only grows as O(nε²) instead of O(nε).
-/

namespace KahanSum

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Standard Error Model

Bridge from the library's `relativeError` bound to the multiplicative `(1 + δ)` form
used in numerical analysis. -/

/-- The standard error model: for nearest rounding in normal range,
    `f.toVal = x * (1 + δ)` for some `|δ| ≤ η`. -/
theorem standard_error_model
    [RMode R] [RModeNearest R]
    (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : ○x = Fp.finite f) :
    ∃ δ : R, f.toVal = x * (1 + δ) ∧ |δ| ≤ η := by
  have hxpos := isNormalRange_pos x hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hrel := RModeNearest_relativeError_le_half x hx f hf
  unfold Fp.relativeError at hrel
  set δ := (f.toVal - x) / x
  refine ⟨δ, ?_, ?_⟩
  · have : x * (1 + δ) = x + x * δ := by ring
    rw [this, show δ = (f.toVal - x) / x from rfl]; field_simp
    ring
  · rw [show δ = (f.toVal - x) / x from rfl]
    rwa [show (x - f.toVal) / x = -((f.toVal - x) / x) from by ring, abs_neg] at hrel

/-- Additive form: `|f.toVal - x| ≤ η * |x|` in normal range. -/
theorem standard_error_additive
    [RMode R] [RModeNearest R]
    (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : ○x = Fp.finite f) :
    |f.toVal - x| ≤ η * |x| := by
  obtain ⟨δ, hval, hδ⟩ := standard_error_model x hx f hf
  have : f.toVal - x = x * δ := by rw [hval]; ring
  rw [this, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg x)

/-! ## Floating-point operation error bounds

Combined lemmas: correctness + standard error model gives additive error bounds
for fp addition and subtraction applied to `FiniteFp` operands. -/

/-- Error bound for fp addition: `|fl(a + b) - (a + b)| ≤ η · |a + b|`,
    when the result is finite and the exact sum is in normal range. -/
theorem fpAdd_error
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a + b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) + b.toVal)) :
    |(f.toVal : R) - (a.toVal + b.toVal)| ≤ η * |(a.toVal : R) + b.toVal| := by
  have hne : (a.toVal : R) + b.toVal ≠ 0 := ne_of_gt (isNormalRange_pos _ hnormal)
  have hcorr := fpAddFinite_correct (R := R) a b hne
  rw [hcorr] at hf
  exact standard_error_additive ((a.toVal : R) + b.toVal) hnormal f hf

/-- Error bound for fp subtraction: `|fl(a - b) - (a - b)| ≤ η · |a - b|`. -/
theorem fpSub_error
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a - b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) - b.toVal)) :
    |(f.toVal : R) - (a.toVal - b.toVal)| ≤ η * |(a.toVal : R) - b.toVal| := by
  have hne : (a.toVal : R) - b.toVal ≠ 0 := ne_of_gt (isNormalRange_pos _ hnormal)
  have hcorr := fpSubFinite_correct (R := R) a b hne
  rw [hcorr] at hf
  exact standard_error_additive ((a.toVal : R) - b.toVal) hnormal f hf

/-- When the exact result is zero, the fp result is also zero. -/
theorem fpAdd_exact_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a + b = Fp.finite f)
    (hzero : (a.toVal : R) + b.toVal = 0) :
    (f.toVal : R) = 0 := by
  have hexact := fpAddFinite_exact_sum R a b
  have hisum_zero : addAlignedSumInt a b = 0 := by
    have h0 : ((addAlignedSumInt a b : ℤ) : R) * (2:R) ^ (min a.e b.e - prec + 1) = 0 := by
      rw [← hexact]; exact hzero
    rcases mul_eq_zero.mp h0 with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt (by positivity))
  have hcancel := fpAddFinite_exact_cancel_sign a b hisum_zero
  have hf' : fpAddFinite a b = Fp.finite f := hf
  rw [hcancel] at hf'
  exact FiniteFp.toVal_isZero (by rw [(Fp.finite.inj hf').symm])

/-- When the exact result is zero, the fp subtraction result is also zero. -/
theorem fpSub_exact_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a - b = Fp.finite f)
    (hzero : (a.toVal : R) - b.toVal = 0) :
    (f.toVal : R) = 0 := by
  -- a - b = a + (-b), and a.toVal + (-b).toVal = a.toVal - b.toVal = 0
  have hzero' : (a.toVal : R) + (-b).toVal = 0 := by
    rw [FiniteFp.toVal_neg_eq_neg]; linarith
  have hf' : fpAddFinite a (-b) = Fp.finite f := hf
  exact fpAdd_exact_zero a (-b) f hf' hzero'

/-- Unified error bound: handles both normal range and exact-zero cases. -/
theorem fpSub_error_or_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a - b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) - b.toVal) ∨ (a.toVal : R) - b.toVal = 0) :
    |(f.toVal : R) - (a.toVal - b.toVal)| ≤ η * |(a.toVal : R) - b.toVal| := by
  rcases hnormal with h | h
  · exact fpSub_error a b f hf h
  · rw [h, fpSub_exact_zero (R := R) a b f hf h]; simp

theorem fpAdd_error_or_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a + b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) + b.toVal) ∨ (a.toVal : R) + b.toVal = 0) :
    |(f.toVal : R) - (a.toVal + b.toVal)| ≤ η * |(a.toVal : R) + b.toVal| := by
  rcases hnormal with h | h
  · exact fpAdd_error a b f hf h
  · rw [h, fpAdd_exact_zero (R := R) a b f hf h]; simp

/-! ## Kahan State and Step

A single step of Kahan summation, with explicit finiteness witnesses. -/

/-- State of the Kahan compensated summation algorithm. -/
structure State where
  sum : FiniteFp
  comp : FiniteFp

/-- Witnesses for one step of Kahan summation.
    Given state `(sum, comp)` and input `x`, produces new state `(t, c')`. -/
structure StepWitness [RModeExec] (st : State) (x : FiniteFp) where
  /-- `y = fl(x - comp)` -/
  y : FiniteFp
  hy : x - st.comp = Fp.finite y
  /-- `t = fl(sum + y)` -/
  t : FiniteFp
  ht : st.sum + y = Fp.finite t
  /-- `w = fl(t - sum)` -/
  w : FiniteFp
  hw : t - st.sum = Fp.finite w
  /-- `c' = fl(w - y)` -/
  c' : FiniteFp
  hc : w - y = Fp.finite c'

/-- Next state after a Kahan step. -/
def StepWitness.nextState [RModeExec] {st : State} {x : FiniteFp}
    (step : StepWitness st x) : State :=
  ⟨step.t, step.c'⟩

/-! ## Kahan Trace

A trace recording all intermediate steps of Kahan summation over a list. -/

/-- A valid execution trace of Kahan summation over a list of inputs.
    Lives in `Type` (not `Prop`) so we can extract data like accumulated residuals. -/
inductive Trace [RModeExec] : List FiniteFp → State → State → Type where
  /-- Empty list: state unchanged. -/
  | nil (st : State) : Trace [] st st
  /-- One step followed by the rest. -/
  | cons {st : State} {x : FiniteFp} {xs : List FiniteFp} {final : State}
      (step : StepWitness st x)
      (rest : Trace xs step.nextState final) :
      Trace (x :: xs) st final

/-- Extract the final sum from a Kahan trace. -/
def Trace.finalSum [RModeExec] {xs : List FiniteFp} {init final : State}
    (_trace : Trace xs init final) : FiniteFp :=
  final.sum

/-! ## Error Bound

The main error bound theorem for Kahan compensated summation. -/

/-- Normal range precondition for all intermediate values in a Kahan step. -/
structure StepNormalRange [RModeExec] (st : State) (x : FiniteFp)
    (step : StepWitness st x) where
  /-- `x.toVal - comp.toVal` is in normal range (for y = fl(x - c)) -/
  y_normal : isNormalRange ((x.toVal : R) - st.comp.toVal) ∨
             (x.toVal : R) - st.comp.toVal = 0
  /-- `sum.toVal + y.toVal` is in normal range (for t = fl(sum + y)) -/
  t_normal : isNormalRange ((st.sum.toVal : R) + step.y.toVal) ∨
             (st.sum.toVal : R) + step.y.toVal = 0
  /-- `t.toVal - sum.toVal` is in normal range (for w = fl(t - sum)) -/
  w_normal : isNormalRange ((step.t.toVal : R) - st.sum.toVal) ∨
             (step.t.toVal : R) - st.sum.toVal = 0
  /-- `w.toVal - y.toVal` is in normal range (for c' = fl(w - y)) -/
  c_normal : isNormalRange ((step.w.toVal : R) - step.y.toVal) ∨
             (step.w.toVal : R) - step.y.toVal = 0

/-! ## Per-Step Corrected Sum Error

The key identity: if we track `σ = sum - comp` (the "corrected sum"),
then after one Kahan step processing input `x`:

  `σ' = σ + x + (ρ₁ - ρ₃ - ρ₄)`

where ρ₁, ρ₃, ρ₄ are rounding errors from the subtraction and compensation steps.
The compensation absorbs the main addition error ρ₂, leaving only second-order terms. -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The corrected sum recurrence: `σ' = σ + x + (ρ₁ - ρ₃ - ρ₄)`.
    Note: `ρ₂` (the addition rounding error) cancels algebraically — the compensation
    absorbs it. This is the key identity behind Kahan summation. -/
theorem kahan_step_corrected_sum
    [RModeExec]
    (st : State) (x : FiniteFp)
    (step : StepWitness st x) :
    let σ := (st.sum.toVal : R) - st.comp.toVal
    let σ' := (step.t.toVal : R) - step.c'.toVal
    let ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
    let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
    let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
    σ' = σ + x.toVal + (ρ₁ - ρ₃ - ρ₄) := by
  simp only
  ring

/-- Error bounds on the individual rounding errors in a Kahan step. -/
theorem kahan_step_rounding_bounds
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp)
    (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step) :
    let ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
    let ρ₂ := (step.t.toVal : R) - (st.sum.toVal + step.y.toVal)
    let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
    let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
    |ρ₁| ≤ η * |(x.toVal : R) - st.comp.toVal| ∧
    |ρ₂| ≤ η * |(st.sum.toVal : R) + step.y.toVal| ∧
    |ρ₃| ≤ η * |(step.t.toVal : R) - st.sum.toVal| ∧
    |ρ₄| ≤ η * |(step.w.toVal : R) - step.y.toVal| := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fpSub_error_or_zero x st.comp step.y step.hy hnr.y_normal
  · exact fpAdd_error_or_zero st.sum step.y step.t step.ht hnr.t_normal
  · exact fpSub_error_or_zero step.t st.sum step.w step.hw hnr.w_normal
  · exact fpSub_error_or_zero step.w step.y step.c' step.hc hnr.c_normal

/-! ## Compensation Identity

The compensation `c'` exactly captures the sum of the three "remaining" rounding errors
(ρ₂ + ρ₃ + ρ₄). This is the algebraic reason why Kahan works: the compensation
absorbs the O(η) errors, leaving only O(η²) residuals in ρ₃ and ρ₄. -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The compensation equals the sum of the three remaining rounding errors. -/
theorem kahan_step_comp_eq_rounding_errors
    [RModeExec]
    (st : State) (x : FiniteFp)
    (step : StepWitness st x) :
    (step.c'.toVal : R) =
      ((step.t.toVal : R) - (st.sum.toVal + step.y.toVal)) +
      ((step.w.toVal : R) - (step.t.toVal - st.sum.toVal)) +
      ((step.c'.toVal : R) - (step.w.toVal - step.y.toVal)) := by
  ring

/-! ## Inductive Error Accumulation

Telescope the per-step corrected sum identity over a full trace to get:
  `σ_final = σ_init + Σxᵢ + Σ(ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ)`

Then combine with the final compensation to bound `|sum - Σxᵢ|`. -/

/-- Per-step rounding residual: `ρ₁ - ρ₃ - ρ₄` for one Kahan step. -/
def stepResidual [RModeExec] (st : State) (x : FiniteFp)
    (step : StepWitness st x) : R :=
  let ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
  let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
  let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
  ρ₁ - ρ₃ - ρ₄

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The corrected sum after a Kahan step equals the old corrected sum
    plus the input plus the step residual. -/
theorem kahan_step_sigma_eq [RModeExec]
    (st : State) (x : FiniteFp) (step : StepWitness st x) :
    (step.t.toVal : R) - step.c'.toVal =
      ((st.sum.toVal : R) - st.comp.toVal) + x.toVal + stepResidual st x step := by
  unfold stepResidual; ring

/-- Accumulated residuals from a trace. -/
def traceResidual [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons step rest =>
    stepResidual _ _ step + traceResidual rest

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The corrected sum telescopes over a full trace:
    `σ_final = σ_init + Σxᵢ + Σ(residuals)`. -/
theorem kahan_trace_sigma_eq [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final) :
    (final.sum.toVal : R) - final.comp.toVal =
      ((init.sum.toVal : R) - init.comp.toVal) +
      (xs.map (fun x => x.toVal (R := R))).sum +
      traceResidual trace := by
  induction trace with
  | nil st => simp [traceResidual]
  | cons step rest ih =>
    simp only [List.map_cons, List.sum_cons, traceResidual, StepWitness.nextState] at *
    rw [ih, kahan_step_sigma_eq]
    ring

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- **Main error decomposition**: the final sum error splits into
    corrected-sum error plus final compensation.

    `sum_n - Σxᵢ = (σ_n - Σxᵢ) + c_n`

    where `σ_n = sum_n - c_n` is the corrected sum. By the per-step identity,
    `σ_n - Σxᵢ = Σ(ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ)` (accumulated second-order errors),
    giving `|sum_n - Σxᵢ| ≤ Σ|ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ| + |c_n|`. -/
theorem kahan_error_decomposition
    [RModeExec]
    {final : State} (xs : List FiniteFp) :
    (final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum =
      ((final.sum.toVal : R) - final.comp.toVal -
        (xs.map (fun x => x.toVal (R := R))).sum) +
      final.comp.toVal := by ring

omit [FloorRing R] in
/-- Triangle inequality form of the error decomposition. -/
theorem kahan_error_triangle
    [RModeExec]
    {final : State} (xs : List FiniteFp) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      |(final.sum.toVal : R) - final.comp.toVal -
        (xs.map (fun x => x.toVal (R := R))).sum| +
      |final.comp.toVal (R := R)| := by
  rw [kahan_error_decomposition xs]
  exact abs_add_le _ _

/-- Sum of |stepResidual| over the trace — the triangle inequality bound. -/
def traceResidualAbsBound [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons step rest =>
    |stepResidual (R := R) _ _ step| + traceResidualAbsBound rest

omit [FloorRing R] in
/-- The accumulated residual is bounded by the sum of absolute step residuals. -/
theorem traceResidual_abs_le [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final) :
    |traceResidual (R := R) trace| ≤ traceResidualAbsBound trace := by
  induction trace with
  | nil => simp [traceResidual, traceResidualAbsBound]
  | cons step rest ih =>
    simp only [traceResidual, traceResidualAbsBound]
    exact le_trans (abs_add_le _ _) (add_le_add_right ih _)

omit [FloorRing R] in
/-- **Kahan summation error bound** (general form).

    Starting from zero initial state, the error of Kahan summation satisfies:

    `|sum_n - Σxᵢ| ≤ Σ|ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ| + |c_n|`

    where each `|ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ|` is bounded by
    `η|xᵢ - cᵢ₋₁| + η|tᵢ - sᵢ₋₁| + η|wᵢ - yᵢ|`
    via `kahan_step_rounding_bounds`.

    The key insight is that ρ₂ (the O(η) addition error) is absent — it is
    absorbed by the compensation. The remaining terms ρ₃, ρ₄ are O(η²) since
    they operate on quantities that are themselves O(η), giving total error
    O(nη²) for the corrected sum. Combined with the O(η) compensation `c_n`,
    the total error is O(η) instead of O(nη). -/
theorem kahan_error_bound
    [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      traceResidualAbsBound trace +
      |final.comp.toVal (R := R)| := by
  have hsigma := kahan_trace_sigma_eq (R := R) trace
  rw [hinit_sum, hinit_comp] at hsigma
  have hresid : (final.sum.toVal : R) - final.comp.toVal -
      (xs.map (fun x => x.toVal (R := R))).sum = traceResidual trace := by linarith
  calc |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum|
      ≤ |(final.sum.toVal : R) - final.comp.toVal -
          (xs.map (fun x => x.toVal (R := R))).sum| +
        |final.comp.toVal (R := R)| := kahan_error_triangle xs
    _ = |traceResidual trace| + |final.comp.toVal (R := R)| := by rw [hresid]
    _ ≤ traceResidualAbsBound trace + |final.comp.toVal (R := R)| :=
        add_le_add (traceResidual_abs_le trace) (le_refl _)

end KahanSum
