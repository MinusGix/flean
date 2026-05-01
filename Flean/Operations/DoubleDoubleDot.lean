import Flean.Operations.DoubleDoubleFma

set_option linter.unusedSectionVars false

/-! # Double-Double Dot Product

Inductive trace of N-ary double-double dot product. Each step is one
`DDFmaStep` advancing the accumulator: `acc := dd_fma(x_i, y_i, acc) ≈ x_i·y_i + acc`.

```
inductive DDDotTrace : List (DoubleDouble × DoubleDouble) → DoubleDouble → DoubleDouble → Type
  | nil  acc : DDDotTrace [] acc acc
  | cons step rest_trace : DDDotTrace ((x, y) :: rest) acc final
```

Theorems shipped:
- `result_isNormalized` — propagates from initial `acc.IsNormalized`.
- `final_abs_le_uniform_step` — triangle bound `≤ n · stepErr` given a
  uniform per-step error bound.

Per-step error bounds compose with `DDFmaStep.error_bound_abstract` /
`error_bound_auto`. -/

variable [FloatFormat]

section DDDot

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Trace of an iterated double-double dot product. Each step is a DD-FMA. -/
inductive DDDotTrace : List (DoubleDouble × DoubleDouble) → DoubleDouble → DoubleDouble → Type
  | nil (acc : DoubleDouble) : DDDotTrace [] acc acc
  | cons {acc x y final : DoubleDouble} {rest : List (DoubleDouble × DoubleDouble)}
      (step : DDFmaStep (R := R) x y acc)
      (next : DDDotTrace rest step.result final) :
      DDDotTrace ((x, y) :: rest) acc final

namespace DDDotTrace

/-- **Normalization propagates** through the trace. -/
theorem result_isNormalized
    {pairs : List (DoubleDouble × DoubleDouble)} {acc final : DoubleDouble}
    (trace : DDDotTrace (R := R) pairs acc final)
    (hacc : acc.IsNormalized (R := R)) :
    final.IsNormalized (R := R) := by
  induction trace with
  | nil _ => exact hacc
  | cons step rest ih => exact ih step.result_isNormalized

/-- The "true dot product" of the input pairs. -/
def trueDot (pairs : List (DoubleDouble × DoubleDouble)) : R :=
  (pairs.map (fun p => (p.1.toVal : R) * p.2.toVal)).sum

@[simp] theorem trueDot_nil :
    trueDot (R := R) ([] : List (DoubleDouble × DoubleDouble)) = 0 := by
  simp [trueDot]

@[simp] theorem trueDot_cons (x y : DoubleDouble)
    (pairs : List (DoubleDouble × DoubleDouble)) :
    trueDot (R := R) ((x, y) :: pairs) = x.toVal * y.toVal + trueDot pairs := by
  simp [trueDot]

/-- **Triangle bound on the final deviation.**

Caller supplies a per-step error bound `stepErr` for `dd_fma`'s deviation
`|step.result.toVal − (x·y + acc.toVal)|`. The trace's deviation is at
most `n · stepErr` where `n = pairs.length`. -/
theorem final_abs_le_uniform_step
    {pairs : List (DoubleDouble × DoubleDouble)} {acc final : DoubleDouble}
    (trace : DDDotTrace (R := R) pairs acc final)
    (stepErr : R)
    (h_step :
      ∀ {a x y f : DoubleDouble} {rest : List (DoubleDouble × DoubleDouble)},
        DDDotTrace (R := R) ((x, y) :: rest) a f →
        ∀ s : DDFmaStep (R := R) x y a,
          |s.result.toVal (R := R) - (x.toVal * y.toVal + a.toVal)| ≤ stepErr) :
    |final.toVal (R := R) - (acc.toVal + trueDot pairs)| ≤
      pairs.length * stepErr := by
  induction trace with
  | nil acc =>
    simp [trueDot]
  | @cons acc x y final pairs step rest ih =>
    rw [trueDot_cons]
    have h_split :
        final.toVal (R := R) - (acc.toVal + (x.toVal * y.toVal + trueDot pairs)) =
        (final.toVal - (step.result.toVal + trueDot pairs))
        + (step.result.toVal - (x.toVal * y.toVal + acc.toVal)) := by ring
    rw [h_split]
    have h_rest := ih
    have h_curr := h_step (.cons step rest) step
    have h_len : (((x, y) :: pairs).length : R) = 1 + pairs.length := by
      simp [List.length_cons]; ring
    rw [h_len]
    calc |(final.toVal (R := R) - (step.result.toVal + trueDot pairs))
          + (step.result.toVal - (x.toVal * y.toVal + acc.toVal))|
        ≤ |final.toVal (R := R) - (step.result.toVal + trueDot pairs)| +
          |step.result.toVal - (x.toVal * y.toVal + acc.toVal)| := abs_add_le _ _
      _ ≤ pairs.length * stepErr + stepErr := by linarith
      _ = (1 + pairs.length) * stepErr := by ring

end DDDotTrace

end DDDot
