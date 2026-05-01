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

/-- **Linearity of `trueHornerRec` in the starting accumulator.**

The difference between two Horner evaluations starting from `s'` vs `s`
is exactly `(s' − s) · x^n` where `n = coeffs.length`. This is the
key algebraic fact that makes the geometric bound work: a perturbation
in the starting accumulator amplifies by `x^k` after `k` further steps. -/
theorem trueHornerRec_diff (x : DoubleDouble) (coeffs : List DoubleDouble)
    (s s' : R) :
    trueHornerRec (R := R) x coeffs s' - trueHornerRec x coeffs s =
      (s' - s) * x.toVal ^ coeffs.length := by
  induction coeffs generalizing s s' with
  | nil => simp [trueHornerRec]
  | cons c rest ih =>
    simp only [trueHornerRec_cons, List.length_cons]
    have hd := ih (s * x.toVal + c.toVal) (s' * x.toVal + c.toVal)
    rw [hd, pow_succ]
    ring

/-- **Geometric bound** `stepErr · Σ_{k<n} |x|^k`, defined recursively to
match the inductive proof structure. -/
def geomBound (absX stepErr : R) : ℕ → R
  | 0 => 0
  | n + 1 => stepErr * absX ^ n + geomBound absX stepErr n

/-- **Triangle bound on Horner deviation, geometric in `|x|`.**

Caller supplies a per-step bound `stepErr` for the DD-FMA deviation
`|step.result.toVal − (acc·x + c)|`. The trace's deviation is bounded by
`stepErr · (1 + |x| + |x|² + ⋯ + |x|^(n−1))` = `geomBound |x| stepErr n`.

For `|x| ≤ 1`, `geomBound |x| stepErr n ≤ n · stepErr` (the dd_sum / dd_dot
shape). For `|x| > 1`, the geometric series matters. -/
theorem final_abs_le_geomBound
    {x : DoubleDouble} {coeffs : List DoubleDouble} {acc final : DoubleDouble}
    (trace : DDHornerTrace (R := R) x coeffs acc final)
    (stepErr : R)
    (h_step :
      ∀ {a c f : DoubleDouble} {rest : List DoubleDouble},
        DDHornerTrace (R := R) x (c :: rest) a f →
        ∀ s : DDFmaStep (R := R) a x c,
          |s.result.toVal (R := R) - (a.toVal * x.toVal + c.toVal)| ≤ stepErr) :
    |final.toVal (R := R) - trueHornerRec x coeffs acc.toVal| ≤
      geomBound |x.toVal (R := R)| stepErr coeffs.length := by
  induction trace with
  | nil acc =>
    simp [trueHornerRec, geomBound]
  | @cons acc c final coeffs step rest ih =>
    rw [trueHornerRec_cons]
    -- Decompose:
    --   final − trueHornerRec rest (acc·x + c)
    --     = (final − trueHornerRec rest step.result.toVal)
    --     + (trueHornerRec rest step.result.toVal − trueHornerRec rest (acc·x + c))
    -- The second piece is `(step.result.toVal − (acc·x + c)) · x^|rest|` by linearity.
    have h_diff := trueHornerRec_diff (R := R) x coeffs
      (acc.toVal * x.toVal + c.toVal) step.result.toVal
    have h_split :
        final.toVal (R := R) -
          trueHornerRec x coeffs (acc.toVal * x.toVal + c.toVal) =
        (final.toVal - trueHornerRec x coeffs step.result.toVal) +
        (step.result.toVal - (acc.toVal * x.toVal + c.toVal)) *
          x.toVal ^ coeffs.length := by
      have := h_diff
      linarith
    rw [h_split, List.length_cons, geomBound]
    have h_curr := h_step (.cons step rest) step
    calc |(final.toVal (R := R) - trueHornerRec x coeffs step.result.toVal) +
           (step.result.toVal - (acc.toVal * x.toVal + c.toVal)) *
              x.toVal ^ coeffs.length|
        ≤ |final.toVal (R := R) - trueHornerRec x coeffs step.result.toVal| +
          |(step.result.toVal - (acc.toVal * x.toVal + c.toVal)) *
              x.toVal ^ coeffs.length| := abs_add_le _ _
      _ = |final.toVal (R := R) - trueHornerRec x coeffs step.result.toVal| +
          |step.result.toVal - (acc.toVal * x.toVal + c.toVal)| *
            |x.toVal (R := R)| ^ coeffs.length := by
            rw [abs_mul, abs_pow]
      _ ≤ geomBound |x.toVal (R := R)| stepErr coeffs.length +
          stepErr * |x.toVal (R := R)| ^ coeffs.length := by
            have hpow_nn : 0 ≤ |x.toVal (R := R)| ^ coeffs.length := by positivity
            gcongr
      _ = stepErr * |x.toVal (R := R)| ^ coeffs.length +
          geomBound |x.toVal (R := R)| stepErr coeffs.length := by ring

/-- **`geomBound` for `|x| ≤ 1` collapses to `n · stepErr`.** -/
theorem geomBound_le_linear_of_absX_le_one
    {absX stepErr : R} (habsX_nn : 0 ≤ absX) (habsX_le : absX ≤ 1)
    (h_stepErr_nn : 0 ≤ stepErr) (n : ℕ) :
    geomBound absX stepErr n ≤ n * stepErr := by
  induction n with
  | zero => simp [geomBound]
  | succ k ih =>
    simp only [geomBound]
    have hpow_le : absX ^ k ≤ 1 := by
      exact pow_le_one₀ habsX_nn habsX_le
    have hpow_nn : 0 ≤ absX ^ k := by positivity
    calc stepErr * absX ^ k + geomBound absX stepErr k
        ≤ stepErr * 1 + k * stepErr := by
          gcongr
      _ = (k + 1) * stepErr := by ring
      _ = ↑(k + 1) * stepErr := by push_cast; ring

end DDHornerTrace

end DDHorner
