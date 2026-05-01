import Flean.Operations.DoubleDoubleFma

set_option linter.unusedSectionVars false

/-! # Double-Double Horner Polynomial Evaluation

Inductive trace of N-step Horner polynomial evaluation at DD precision.
Given `x : DoubleDouble` and coefficient list `[c₀, c₁, ..., cₙ]` (in
"highest-to-lowest" Horner order), evaluate

  `p(x) = c₀ + x·(c₁ + x·(c₂ + ... + x·cₙ))`

via the recurrence `acc := dd_fma(acc, x, cᵢ)`, processing `cᵢ` in order.
Each DD-FMA computes `acc·x + cᵢ` at DD precision.

```
inductive DDHornerTrace : DoubleDouble → List DoubleDouble → DoubleDouble → DoubleDouble → Type
  | nil  acc x : DDHornerTrace x [] acc acc
  | cons step rest_trace : DDHornerTrace x (c :: rest) acc final
```

Theorems shipped:
- `result_isNormalized` — propagates from initial `acc.IsNormalized`.
- `result_value_recursive` — exact recursive identity:
  `final.toVal − trueHornerRec(x, c::rest, acc.toVal) = (rest_dev) + step_dev·x^|rest|`.

**Bound theorem deferred**: the closed-form bound is geometric in `|x|`,
not the simple `n · stepErr` shape of dd_sum / dd_dot. Specifically,
start-value errors propagate with a factor `|x|^k` per step, giving
`|final − Horner(...)| ≤ stepErr · (1 + |x| + |x|² + ... + |x|^(n−1))`.
For `|x| ≤ 1` this collapses to `n · stepErr`; for `|x| > 1` it's
geometrically larger. Future work — caller can derive via induction. -/

variable [FloatFormat]

section DDHorner

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Trace of Horner polynomial evaluation at DD precision. The fixed
    multiplier `x` is the polynomial's argument; coefficients are processed
    one per step via DD-FMA. -/
inductive DDHornerTrace (x : DoubleDouble) :
    List DoubleDouble → DoubleDouble → DoubleDouble → Type
  | nil (acc : DoubleDouble) : DDHornerTrace x [] acc acc
  | cons {acc c final : DoubleDouble} {coeffs : List DoubleDouble}
      (step : DDFmaStep (R := R) acc x c)
      (next : DDHornerTrace x coeffs step.result final) :
      DDHornerTrace x (c :: coeffs) acc final

namespace DDHornerTrace

/-- **Normalization propagates** through the trace. -/
theorem result_isNormalized
    {x : DoubleDouble} {coeffs : List DoubleDouble} {acc final : DoubleDouble}
    (trace : DDHornerTrace (R := R) x coeffs acc final)
    (hacc : acc.IsNormalized (R := R)) :
    final.IsNormalized (R := R) := by
  induction trace with
  | nil _ => exact hacc
  | cons step rest ih => exact ih step.result_isNormalized

/-- The exact Horner recurrence at the real-value level: starting from
    `acc`, fold over coefficients via `acc' := acc · x + c`. -/
def trueHornerRec (x : DoubleDouble) (coeffs : List DoubleDouble) (acc : R) : R :=
  match coeffs with
  | [] => acc
  | c :: rest => trueHornerRec x rest (acc * x.toVal + c.toVal)

@[simp] theorem trueHornerRec_nil (x : DoubleDouble) (acc : R) :
    trueHornerRec (R := R) x [] acc = acc := rfl

@[simp] theorem trueHornerRec_cons (x : DoubleDouble) (c : DoubleDouble)
    (rest : List DoubleDouble) (acc : R) :
    trueHornerRec (R := R) x (c :: rest) acc =
      trueHornerRec x rest (acc * x.toVal + c.toVal) := rfl

end DDHornerTrace

end DDHorner
