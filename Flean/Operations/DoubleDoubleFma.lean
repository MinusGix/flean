import Flean.Operations.DoubleDouble

/-! # Double-Double Fused Multiply-Add

`fma(a, b, c) = a · b + c` at double-double precision, computed as the
composition `dd_add(dd_mul(a, b), c)`.

```
prod        := dd_mul(a, b)              -- DD product, normalized
result_step := dd_add(prod.result, c)    -- DD addition, normalized
return result_step.result
```

This is the natural way to do FMA at DD precision: hardware FMA gives a
single-rounding `a·b + c`, but for double-double (~106 bits) the precision
budget is far above what one hardware rounding can deliver, so we use full
DD multiplication followed by DD addition — same `O(η²)` accuracy as
either operation alone.

Value identity: `result.toVal − (a·b + c) = δ_mul + δ_add`, where:
- `δ_mul` is `DDMulStep.result_value`'s exact decomposition (the dd_mul
  3-term identity).
- `δ_add` is `DDAddStep.result_value`'s exact decomposition (the dd_add
  identity).

Composes cleanly: each piece is bounded by its own `error_bound` theorem.
Lives in a separate file to keep `DoubleDouble.lean`'s elaboration
context manageable. -/

variable [FloatFormat]

section DDFma

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Witnesses for one execution of double-double fused multiply-add.

Two-stage composition: a `DDMulStep` for `a·b`, then a `DDAddStep` for the
addition of the product with `c`. The structure is dependent — `add_step`'s
type references `prod.result`. -/
structure DDFmaStep (a b c : DoubleDouble) where
  /-- DD product `a · b`. -/
  prod : DDMulStep (R := R) a b
  /-- DD addition `prod.result + c`. -/
  add_step : DDAddStep (R := R) prod.result c

namespace DDFmaStep

variable {a b c : DoubleDouble} (step : DDFmaStep (R := R) a b c)

/-- The `DoubleDouble` produced by the FMA step. -/
def result : DoubleDouble := step.add_step.result

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_eq : step.result = step.add_step.result := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [RMode R]
    [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Exact value identity for `dd_fma`.**

The result deviates from `a·b + c` by exactly the sum of the dd_mul and
dd_add deviations. Composes the exact identities of both stages. -/
theorem result_value :
    step.result.toVal (R := R) - (a.toVal * b.toVal + c.toVal) =
      (step.prod.result.toVal - a.toVal * b.toVal)
      + (step.add_step.result.toVal -
          (step.prod.result.toVal + c.toVal)) := by
  show step.add_step.result.toVal (R := R) - (a.toVal * b.toVal + c.toVal) = _
  ring

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Normalization of the `dd_fma` result.**

Inherited from `DDAddStep.result_isNormalized` on the final stage. -/
theorem result_isNormalized :
    step.result.IsNormalized (R := R) :=
  step.add_step.result_isNormalized

omit [FloorRing R] [RMode R] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Abstract bound for `dd_fma`.**

Caller supplies magnitude bounds for the dd_mul and dd_add deviations;
the FMA bound is their sum. Compose with `DDMulStep.error_bound` and
`DDAddStep.error_bound` for closed-form bounds. -/
theorem error_bound_abstract
    (mulErr addErr : R)
    (hMul : |step.prod.result.toVal (R := R) - a.toVal * b.toVal| ≤ mulErr)
    (hAdd : |step.add_step.result.toVal (R := R) -
              (step.prod.result.toVal + c.toVal)| ≤ addErr) :
    |step.result.toVal (R := R) - (a.toVal * b.toVal + c.toVal)| ≤
      mulErr + addErr := by
  rw [step.result_value]
  calc |(step.prod.result.toVal (R := R) - a.toVal * b.toVal)
        + (step.add_step.result.toVal -
            (step.prod.result.toVal + c.toVal))|
      ≤ |step.prod.result.toVal (R := R) - a.toVal * b.toVal|
        + |step.add_step.result.toVal (R := R) -
            (step.prod.result.toVal + c.toVal)| := abs_add_le _ _
    _ ≤ mulErr + addErr := by gcongr

omit [RModeConj R] [RModeIdem R] in
/-- **Auto-quantitative bound for `dd_fma`.**

Discharges both pieces from `DDMulStep.error_bound` and
`DDAddStep.error_bound`. Caller supplies four normal-range / exact-zero
hypotheses (two for the dd_mul lo-channel FMAs, two for the dd_add
lo-channel adds). -/
theorem error_bound_auto
    (h_mul_1 : isNormalRange (a.hi.toVal * b.lo.toVal +
                              (step.prod.p_lo.toVal : R)) ∨
               a.hi.toVal * b.lo.toVal + (step.prod.p_lo.toVal : R) = 0)
    (h_mul_2 : isNormalRange (a.lo.toVal * b.hi.toVal +
                              (step.prod.t1.toVal : R)) ∨
               a.lo.toVal * b.hi.toVal + (step.prod.t1.toVal : R) = 0)
    (h_add_1 : isNormalRange ((step.add_step.e_hi.toVal : R) +
                              step.prod.result.lo.toVal) ∨
               (step.add_step.e_hi.toVal : R) + step.prod.result.lo.toVal = 0)
    (h_add_2 : isNormalRange ((step.add_step.e_lo_partial.toVal : R) +
                              c.lo.toVal) ∨
               (step.add_step.e_lo_partial.toVal : R) + c.lo.toVal = 0) :
    |step.result.toVal (R := R) - (a.toVal * b.toVal + c.toVal)| ≤
        η * (|a.hi.toVal * b.lo.toVal + (step.prod.p_lo.toVal : R)| +
             |a.lo.toVal * b.hi.toVal + (step.prod.t1.toVal : R)|)
      + |a.lo.toVal * b.lo.toVal (R := R)|
      + η * (|(step.add_step.e_hi.toVal : R) + step.prod.result.lo.toVal| +
             |(step.add_step.e_lo_partial.toVal : R) + c.lo.toVal|) := by
  have h_mulErr := step.prod.error_bound (R := R) h_mul_1 h_mul_2
  have h_addErr := step.add_step.error_bound (R := R) h_add_1 h_add_2
  have h := step.error_bound_abstract (R := R) _ _ h_mulErr h_addErr
  linarith

end DDFmaStep

/-! ### Constructors -/

namespace DDFmaStep

variable {a b c : DoubleDouble}

/-- Structural constructor for `DDFmaStep`. Just bundles the two stage
    structures. -/
@[inline]
def ofWitnesses
    (prod : DDMulStep (R := R) a b)
    (add_step : DDAddStep (R := R) prod.result c) :
    DDFmaStep (R := R) a b c :=
  { prod, add_step }

end DDFmaStep

end DDFma
