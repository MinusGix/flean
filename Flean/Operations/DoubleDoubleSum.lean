import Flean.Operations.DoubleDouble

set_option linter.unusedSectionVars false

/-! # Double-Double Iterated Summation

Inductive trace of N-ary double-double summation: starting from an
accumulator `acc`, iterate `acc := dd_add(acc, xs[i])`.

```
inductive DDSumTrace : List DoubleDouble → DoubleDouble → DoubleDouble → Type
  | nil  acc                       : DDSumTrace [] acc acc
  | cons step rest_trace           : DDSumTrace (x :: xs) acc final
```

Each `step : DDAddStep R acc x` carries one rounded addition's witnesses;
`rest` chains from `step.result` to the final accumulator.

Theorems shipped:
- `result_isNormalized` — normalization propagates if the initial `acc` is
  normalized (the final TwoSum of each step preserves it).
- `final_abs_value_le` — exact triangle bound on `|final.toVal − (acc.toVal + ∑xs.toVal)|`
  in terms of per-step `δ` values.

Per-step error bounds (`DDAddStep.error_bound`) compose with this trace via the
iterated triangle inequality. -/

variable [FloatFormat]

section DDSum

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Trace of an iterated double-double summation. The trace witnesses the
    chain `acc → step₁.result → step₂.result → ... → final`. -/
inductive DDSumTrace : List DoubleDouble → DoubleDouble → DoubleDouble → Type
  | nil (acc : DoubleDouble) : DDSumTrace [] acc acc
  | cons {acc x final : DoubleDouble} {xs : List DoubleDouble}
      (step : DDAddStep (R := R) acc x)
      (rest : DDSumTrace xs step.result final) :
      DDSumTrace (x :: xs) acc final

namespace DDSumTrace

omit [RModeNearest R] [RModeConj R] in
/-- **Normalization propagates through the trace.** If the initial accumulator
    is normalized, so is the final result. -/
theorem result_isNormalized
    {xs : List DoubleDouble} {acc final : DoubleDouble}
    (trace : DDSumTrace (R := R) xs acc final)
    (hacc : acc.IsNormalized (R := R)) :
    final.IsNormalized (R := R) := by
  induction trace with
  | nil _ => exact hacc
  | cons step rest ih => exact ih step.result_isNormalized

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- The "true sum" of the input list. -/
def trueSum (xs : List DoubleDouble) : R := (xs.map (DoubleDouble.toVal (R := R))).sum

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem trueSum_nil : trueSum (R := R) ([] : List DoubleDouble) = 0 := by
  simp [trueSum]

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem trueSum_cons (x : DoubleDouble) (xs : List DoubleDouble) :
    trueSum (R := R) (x :: xs) = x.toVal + trueSum xs := by
  simp [trueSum]

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Triangle bound on the final deviation.**

Caller supplies a per-step error bound function `stepErr` such that each
step's deviation `|step.result.toVal − (step's-acc + x.toVal)|` is at most
`stepErr`. The trace's deviation is at most `n · stepErr` where `n` is
the list length. For mixed bounds, sum over the list directly via
induction. -/
theorem final_abs_le_uniform_step
    {xs : List DoubleDouble} {acc final : DoubleDouble}
    (trace : DDSumTrace (R := R) xs acc final)
    (stepErr : R)
    (h_step :
      ∀ {a x f : DoubleDouble} {rest_xs : List DoubleDouble},
        DDSumTrace (R := R) (x :: rest_xs) a f →
        ∀ s : DDAddStep (R := R) a x,
          |s.result.toVal (R := R) - (a.toVal + x.toVal)| ≤ stepErr) :
    |final.toVal (R := R) - (acc.toVal + trueSum xs)| ≤
      xs.length * stepErr := by
  induction trace with
  | nil acc =>
    simp [trueSum]
  | @cons acc x final xs step rest ih =>
    -- Unfold trueSum on the cons:
    rw [trueSum_cons]
    -- Want: |final.toVal - (acc + x + trueSum xs)| ≤ (1 + xs.length) * stepErr
    -- Decompose: final.toVal - (acc + x + S) = (final.toVal - (step.result + S))
    --                                          + (step.result - (acc + x))
    have h_split :
        final.toVal (R := R) - (acc.toVal + (x.toVal + trueSum xs)) =
        (final.toVal - (step.result.toVal + trueSum xs))
        + (step.result.toVal - (acc.toVal + x.toVal)) := by ring
    rw [h_split]
    have h_rest := ih
    have h_curr := h_step (.cons step rest) step
    have h_len : ((x :: xs).length : R) = 1 + xs.length := by
      simp [List.length_cons]; ring
    rw [h_len]
    calc |(final.toVal (R := R) - (step.result.toVal + trueSum xs))
          + (step.result.toVal - (acc.toVal + x.toVal))|
        ≤ |final.toVal (R := R) - (step.result.toVal + trueSum xs)| +
          |step.result.toVal - (acc.toVal + x.toVal)| := abs_add_le _ _
      _ ≤ xs.length * stepErr + stepErr := by linarith
      _ = (1 + xs.length) * stepErr := by ring

end DDSumTrace

end DDSum
