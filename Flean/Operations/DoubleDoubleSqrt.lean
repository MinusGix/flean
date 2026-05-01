import Flean.Operations.DoubleDouble

/-! # Double-Double Square Root — Newton Iteration

One Newton iteration for square root at DD precision. The structure
`DDSqrtNewtonStep` represents *one step* of Newton's method specialized to
`f(x) = x² − a`: given any starting estimate `x1`, compute the corresponding
correction and refined estimate. Convergence to `√a` is a separate fact —
provable when `x1² ≈ a.hi` (Stage 2, future).

```
x1               := round(sqrt(a.hi))                 -- initial estimate (single FP)
prod             := dd_mul(⟨x1, 0⟩, ⟨x1, 0⟩)         -- x1² as DD
residual         := dd_sub(a, prod.result)             -- a − x1² as DD
correction       := round(residual.hi / (2 · x1))      -- Newton correction
(hi_out, lo_out) := TwoSum(x1, correction)             -- exact final accumulate
return ⟨hi_out, lo_out⟩
```

Mathematical basis: Newton's iteration `x_{k+1} = (x_k + a/x_k)/2` rewrites to
`x_{k+1} = x_k + (a − x_k²)/(2·x_k)`. With one iteration the relative error
is squared: starting from `≈η` accuracy of the initial single-FP `sqrt`, one
DD iteration gives `≈η²` accuracy.

## Relation to `NewtonStep` in `Flean/Operations/NewtonHorner.lean`

That `NewtonStep` handles general polynomial root-finding: it evaluates a
polynomial and its derivative via JetHorner, then applies the Newton
correction. It operates at single-FP precision throughout.

`DDSqrtNewtonStep` is a sibling specialization: hard-coded for `f(x) = x² − a`
(no JetHorner — directly compute `x²` and `a − x²`), but uses *DD arithmetic*
for the precision-critical `(a − x²)` step. The single-FP division
`(a − x²)/(2x)` is sufficient for the quotient because the residual itself is
already small (`≈η²·a`).

The two are not subsumable in either direction: a degree-2 polynomial Newton
through JetHorner would lose DD precision; conversely DDSqrtNewtonStep can't
handle arbitrary polynomials.

## Why the structure lives in its own file

The structure declaration involves nested `DDMulStep` / `DDSubStep` fields
with deep typeclass cascades; at the accumulated elaboration context of
`DoubleDouble.lean` it times out the elaborator. A fresh file's smaller
context handles it cleanly.

## Why `x1` is unconstrained

A field of the form `hx1 : fpSqrtFinite a.hi = (x1 : Fp)` would force Lean
to unfold `fpSqrtFinite`'s `let`-laden body during structure elaboration —
even at 1.6M `maxHeartbeats` it doesn't terminate. The structure therefore
takes `x1` as a free runtime parameter; convergence to `√a` from the
specific `fpSqrtFinite a.hi` start is a separate fact, established by
hypothesis `x1² ≈ a.hi` in the (future) error-bound theorem. -/

variable [FloatFormat]

section DDSqrt

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Witnesses for one Newton iteration of double-double square root.

The starting estimate `x1` is provided by the caller; the structure does not
constrain *how* `x1` was obtained (typically via `fpSqrtFinite a.hi`, but
any reasonable estimate works). The Newton iteration's correctness depends
on `x1² ≈ a.hi`, which the caller supplies via the error-bound theorem's
hypotheses.

Genuinely *dependent* like `DDDivStep`: `prod` references `x1`, `residual`
references `prod.result`. The `two_x1` field is provided as an external
runtime witness with its exact value `2·x1.toVal`. -/
structure DDSqrtNewtonStep (a : DoubleDouble) where
  /-- Initial sqrt estimate (caller-supplied; typically `round(sqrt(a.hi))`). -/
  x1 : FiniteFp
  /-- DD square: `x1²` as a normalized double-double. -/
  prod : DDMulStep (R := R) (DoubleDouble.ofFiniteFp x1) (DoubleDouble.ofFiniteFp x1)
  /-- DD residual: `a − x1²` as a normalized double-double. -/
  residual : DDSubStep (R := R) a prod.result
  /-- `two_x1 = 2 · x1` (caller supplies; exact since `*2` is an exponent shift). -/
  two_x1 : FiniteFp
  htwo_x1_val : (two_x1.toVal : R) = 2 * x1.toVal
  /-- Newton correction: `correction = round(residual.hi / two_x1)`. -/
  correction : FiniteFp
  hcorrection : residual.result.hi / two_x1 = (correction : Fp)
  /-- Final TwoSum on `(x1, correction)`: rounded sum. -/
  hi_out : FiniteFp
  hhi_out : x1 + correction = (hi_out : Fp)
  /-- Final TwoSum: error (the new lo). -/
  lo_out : FiniteFp
  hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal = x1.toVal + correction.toVal

namespace DDSqrtNewtonStep

variable {a : DoubleDouble} (step : DDSqrtNewtonStep (R := R) a)

/-- The `DoubleDouble` produced by the sqrt step. -/
def result : DoubleDouble := ⟨step.hi_out, step.lo_out⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_hi : step.result.hi = step.hi_out := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_lo : step.result.lo = step.lo_out := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [RMode R]
    [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Exact value identity for `dd_sqrt`.**

The result equals `x1 + correction` exactly via the final TwoSum. The
relation to `√a` is captured by the squared form `|result² − a| ≤ ε` or
the ℝ-specialized `|result − √a| ≤ ε` corollary (future work). -/
theorem result_value :
    step.result.toVal (R := R) = step.x1.toVal + step.correction.toVal := by
  show (step.hi_out.toVal : R) + step.lo_out.toVal =
       step.x1.toVal + step.correction.toVal
  exact step.hlo_out_exact

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Normalization of the `dd_sqrt` result.**

The output `⟨hi_out, lo_out⟩` is normalized via the final TwoSum identity. -/
theorem result_isNormalized :
    step.result.IsNormalized (R := R) :=
  isNormalized_of_value_witness (R := R)
    step.x1 step.correction step.hi_out step.lo_out
    step.hhi_out step.hlo_out_exact

end DDSqrtNewtonStep

/-! ### Constructors -/

namespace DDSqrtNewtonStep

variable {a : DoubleDouble}

/-- Structural constructor for `DDSqrtNewtonStep`. The dependent fields make
    constructor calls naturally pipelined. -/
@[inline]
def ofWitnesses
    (x1 : FiniteFp)
    (prod : DDMulStep (R := R)
        (DoubleDouble.ofFiniteFp x1) (DoubleDouble.ofFiniteFp x1))
    (residual : DDSubStep (R := R) a prod.result)
    (two_x1 : FiniteFp)
    (htwo_x1_val : (two_x1.toVal : R) = 2 * x1.toVal)
    (correction : FiniteFp)
    (hcorrection : residual.result.hi / two_x1 = (correction : Fp))
    (hi_out : FiniteFp)
    (hhi_out : x1 + correction = (hi_out : Fp))
    (lo_out : FiniteFp)
    (hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal =
        x1.toVal + correction.toVal) :
    DDSqrtNewtonStep (R := R) a :=
  { x1, prod, residual, two_x1, htwo_x1_val,
    correction, hcorrection, hi_out, hhi_out, lo_out, hlo_out_exact }

omit [RModeIdem R] in
/-- Smart constructor: discharges the final TwoSum exactness via
    `twoSum_exact`. Returns existential because `lo_out` is the produced
    TwoSum witness. -/
theorem exists_via_finalTwoSum
    (x1 : FiniteFp)
    (prod : DDMulStep (R := R)
        (DoubleDouble.ofFiniteFp x1) (DoubleDouble.ofFiniteFp x1))
    (residual : DDSubStep (R := R) a prod.result)
    (two_x1 : FiniteFp) (htwo_x1_val : (two_x1.toVal : R) = 2 * x1.toVal)
    (correction : FiniteFp)
    (hcorrection : residual.result.hi / two_x1 = (correction : Fp))
    (hi_out : FiniteFp) (hhi_out : x1 + correction = (hi_out : Fp))
    (hx1_nz : 0 < x1.m) (hcorrection_nz : 0 < correction.m) :
    ∃ step : DDSqrtNewtonStep (R := R) a,
      step.x1 = x1 ∧ step.correction = correction ∧ step.hi_out = hi_out := by
  obtain ⟨lo_out, hlo_out_exact⟩ :=
    twoSum_exact (R := R) x1 correction hx1_nz hcorrection_nz hi_out hhi_out
  refine ⟨ofWitnesses (R := R) x1 prod residual two_x1 htwo_x1_val
            correction hcorrection hi_out hhi_out lo_out hlo_out_exact,
          ?_, ?_, ?_⟩ <;> rfl

end DDSqrtNewtonStep

end DDSqrt
