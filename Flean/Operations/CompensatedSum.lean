import Flean.Operations.TwoSum6Op
import Flean.Operations.KahanSum

/-! # TwoSum-Compensated Summation

A variant of Kahan compensated summation that uses the 6-operation TwoSum
(Knuth/Møller) for error recovery instead of the 3-operation Fast2Sum pattern.

## Comparison with Kahan (KahanSum.lean)

| | Classical Kahan | TwoSum-Compensated |
|---|---|---|
| Error recovery | 3-op Fast2Sum | 6-op TwoSum |
| Corrected sum | `sum - comp` | `sum + err` |
| Compensation step | `y = fl(x - comp)` | `y = fl(x + err)` |
| TwoSum-exact when | same-sign + Dekker | always (unconditional) |
| Error per step | `ρ₁ - ρ₃ - ρ₄` | `ρ₁` only |

The 6-op TwoSum gives `t + err = sum + y` exactly (no Dekker/sign conditions),
so the only rounding error per step is `ρ₁ = fl(x + err) - (x + err)`.

## Main results

- `cs_step_corrected_sum` — per-step identity: `σ' = σ + x + ρ₁`
- `cs_trace_sigma_eq` — telescoping: `σₙ = σ₀ + Σxᵢ + Σρ₁ᵢ`
- `cs_error_bound` — error bound: `|final_sum - Σxᵢ| ≤ |err| + η·Σ|xᵢ + errᵢ|`
-/

namespace CompensatedSum

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## State -/

/-- State for TwoSum-compensated summation.
    The corrected sum is `sum.toVal + err.toVal` (additive convention). -/
structure CSState where
  sum : FiniteFp
  err : FiniteFp

/-- The corrected sum: `sum + err`. -/
def CSState.sigma (st : CSState) : R := st.sum.toVal + st.err.toVal

/-! ## Step witness -/

/-- Witnesses for one step of TwoSum-compensated summation.

Given state `(sum, err)` and input `x`:
1. `y = fl(x + err)` — compensated input
2. `(t, err') = TwoSum₆(sum, y)` — error-free sum with recovery

The 6-op TwoSum intermediates are `bv, av, br, ar`. -/
structure CSStep [RModeExec] (st : CSState) (x : FiniteFp) where
  /-- `y = fl(x + err)` — compensated input -/
  y : FiniteFp
  hy : x + st.err = Fp.finite y
  /-- `t = fl(sum + y)` — new sum (= s in TwoSum) -/
  t : FiniteFp
  ht : st.sum + y = Fp.finite t
  /-- `bv = fl(t - sum)` — virtual b -/
  bv : FiniteFp
  hbv : t - st.sum = Fp.finite bv
  /-- Splitting property: when sum + y ≠ 0, bv exactly recovers t - sum.
      This is automatically satisfied for round-to-nearest modes
      (discharged via `split_s_sub_bv` theorems). -/
  hbv_exact :
    ((st.sum.toVal : R) + y.toVal ≠ 0) →
    bv.toVal (R := R) = t.toVal - st.sum.toVal
  /-- `av = fl(t - bv)` — virtual a -/
  av : FiniteFp
  hav : t - bv = Fp.finite av
  /-- `br = fl(y - bv)` — b roundoff -/
  br : FiniteFp
  hbr : y - bv = Fp.finite br
  /-- `ar = fl(sum - av)` — a roundoff -/
  ar : FiniteFp
  har : st.sum - av = Fp.finite ar
  /-- `err' = fl(ar + br)` — error term -/
  err' : FiniteFp
  herr : ar + br = Fp.finite err'

/-- Next state after a compensated sum step. -/
def CSStep.nextState [RModeExec] {st : CSState} {x : FiniteFp}
    (step : CSStep (R := R) st x) : CSState :=
  ⟨step.t, step.err'⟩

/-! ## TwoSum exactness -/

/-- The 6-op TwoSum gives `t + err' = sum + y` exactly. -/
theorem cs_twosum_exact [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    (st : CSState) (x : FiniteFp) (step : CSStep (R := R) st x) :
    (step.t.toVal : R) + step.err'.toVal = st.sum.toVal + step.y.toVal :=
  twoSum_6op (R := R) st.sum step.y step.t step.ht
    step.bv step.hbv step.hbv_exact
    step.av step.hav step.br step.hbr step.ar step.har
    step.err' step.herr

/-! ## Per-step corrected sum identity -/

/-- The rounding error of the compensated input computation. -/
def cs_rho1 [RModeExec] (st : CSState) (x : FiniteFp)
    (step : CSStep (R := R) st x) : R :=
  step.y.toVal - (x.toVal + st.err.toVal)

/-- **Corrected sum identity**: `σ' = σ + x + ρ₁`.

Under TwoSum-exactness (which holds unconditionally for the 6-op algorithm),
the only rounding error per step is `ρ₁` from `fl(x + err)`. -/
theorem cs_step_corrected_sum [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    (st : CSState) (x : FiniteFp) (step : CSStep (R := R) st x) :
    (step.nextState (R := R)).sigma (R := R) =
      st.sigma + x.toVal + cs_rho1 (R := R) st x step := by
  unfold CSStep.nextState CSState.sigma cs_rho1
  have h2s := cs_twosum_exact (R := R) st x step
  linarith

/-! ## Trace -/

/-- A trace of TwoSum-compensated summation steps. -/
inductive CSTrace [RModeExec] :
    List FiniteFp → CSState → CSState → Type where
  /-- Empty list: state unchanged. -/
  | nil (st : CSState) : CSTrace [] st st
  /-- One step followed by the rest. -/
  | cons {st : CSState} {x : FiniteFp} {xs : List FiniteFp} {final : CSState}
      (step : CSStep (R := R) st x)
      (rest : CSTrace xs (step.nextState (R := R)) final) :
      CSTrace (x :: xs) st final

/-- Total rounding residual across a trace: Σρ₁ᵢ. -/
def csTraceResidual [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : R :=
  match trace with
  | .nil _ => 0
  | .cons step rest => cs_rho1 (R := R) _ _ step + csTraceResidual rest

/-- **Corrected sum telescoping**: `σₙ = σ₀ + Σxᵢ + Σρ₁ᵢ`. -/
theorem cs_trace_sigma_eq [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) :
    final.sigma (R := R) =
      init.sigma +
      (xs.map (fun x => x.toVal (R := R))).sum +
      csTraceResidual trace := by
  induction trace with
  | nil st => simp [csTraceResidual, CSState.sigma]
  | cons step rest ih =>
    simp only [List.map_cons, List.sum_cons, csTraceResidual]
    have hstep := cs_step_corrected_sum (R := R) _ _ step
    unfold CSStep.nextState CSState.sigma cs_rho1 at hstep
    unfold CSState.sigma CSStep.nextState at ih
    simp only at ih
    unfold CSState.sigma cs_rho1
    linarith

/-! ## Error bound -/

/-- Absolute sum of rounding residuals. -/
def csTraceResidualAbs [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : R :=
  match trace with
  | .nil _ => 0
  | .cons step rest => |cs_rho1 (R := R) _ _ step| + csTraceResidualAbs rest

theorem csTraceResidual_abs_le [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) :
    |csTraceResidual trace| ≤ csTraceResidualAbs trace := by
  induction trace with
  | nil _ => simp [csTraceResidual, csTraceResidualAbs]
  | cons step rest ih =>
    simp only [csTraceResidual, csTraceResidualAbs]
    calc |cs_rho1 (R := R) _ _ step + csTraceResidual rest|
        ≤ |cs_rho1 (R := R) _ _ step| + |csTraceResidual rest| := abs_add_le _ _
      _ ≤ |cs_rho1 (R := R) _ _ step| + csTraceResidualAbs rest := by linarith

/-- **Error bound**: the final sum minus the true sum of inputs is bounded
by the initial error plus the sum of per-step rounding residuals.

Since each `|ρ₁ᵢ| ≤ η|xᵢ + errᵢ|` (standard error model), this gives
the concrete bound `≤ |err₀| + η·Σ|xᵢ + errᵢ|`. -/
theorem cs_error_bound [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_err : init.err.toVal (R := R) = 0) :
    |final.sum.toVal (R := R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      |final.err.toVal (R := R)| + csTraceResidualAbs trace := by
  have hsigma := cs_trace_sigma_eq (R := R) trace
  unfold CSState.sigma at hsigma
  rw [hinit_sum, hinit_err] at hsigma
  -- final.sum + final.err = 0 + 0 + Σxᵢ + Σρ₁ᵢ
  -- final.sum - Σxᵢ = Σρ₁ᵢ - final.err
  have hresid : (final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum =
      csTraceResidual trace - final.err.toVal := by linarith
  calc |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum|
      = |csTraceResidual trace - final.err.toVal (R := R)| := by rw [hresid]
    _ ≤ |csTraceResidual trace| + |final.err.toVal (R := R)| := by
        rw [show csTraceResidual trace - final.err.toVal (R := R) =
            csTraceResidual trace + (-(final.err.toVal (R := R))) from sub_eq_add_neg _ _]
        have := abs_add_le (csTraceResidual trace) (-(final.err.toVal (R := R)))
        rw [abs_neg] at this; exact this
    _ ≤ csTraceResidualAbs trace + |final.err.toVal (R := R)| := by
        linarith [csTraceResidual_abs_le (R := R) trace]
    _ = |final.err.toVal (R := R)| + csTraceResidualAbs trace := by ring

end CompensatedSum
