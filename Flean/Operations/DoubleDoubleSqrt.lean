import Flean.Operations.DoubleDouble

/-! # Double-Double Square Root

One-iteration Newton refinement for square root at DD precision. Lives in a
separate file from the rest of `DoubleDouble.lean` because the structure
declaration involves nested `DDMulStep` / `DDSubStep` fields with deep
typeclass cascades that would otherwise time out the elaborator at the file's
accumulated context size.

The starting estimate `x1` is provided by the caller (typically computed via
`fpSqrtFinite a.hi` from `Flean.Operations.Sqrt`); we don't include the
relation `fpSqrtFinite a.hi = (x1 : Fp)` as a structure field because Lean's
elaborator unfolds `fpSqrtFinite`'s `let`-laden body during structure
elaboration, blowing the heartbeat budget. The Newton iteration's
correctness depends on `x1² ≈ a.hi`, supplied as an error-bound hypothesis.

```
x1               := round(sqrt(a.hi))                 -- initial estimate (single FP)
prod             := dd_mul(⟨x1, 0⟩, ⟨x1, 0⟩)         -- x1² as DD
residual         := dd_sub(a, prod.result)             -- a − x1² as DD
correction       := round(residual.hi / (2 · x1))      -- Newton correction
(hi_out, lo_out) := TwoSum(x1, correction)             -- exact final accumulate
return ⟨hi_out, lo_out⟩
```

Mathematical correctness: Newton's iteration `x_{k+1} = (x_k + a/x_k)/2`
rewrites to `x_{k+1} = x_k + (a − x_k²)/(2·x_k)`. With one iteration the
relative error is squared: starting from `≈η` accuracy of the initial
single-FP `sqrt`, one DD iteration gives `≈η²` accuracy.

Stage 1 (this file): structure, value identity (`result.toVal = x1 + correction`
exact), normalization, constructors. Connection to `√a` is deferred — the
generic-`R` form would use the squared identity `|result² − a| ≤ ε`; the
ℝ-specialized form gives `|result − √a| ≤ ε` directly. Both are future
work. -/

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
structure DDSqrtStep (a : DoubleDouble) where
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

namespace DDSqrtStep

variable {a : DoubleDouble} (step : DDSqrtStep (R := R) a)

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

end DDSqrtStep

/-! ### Constructors -/

namespace DDSqrtStep

variable {a : DoubleDouble}

/-- Structural constructor for `DDSqrtStep`. The dependent fields make
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
    DDSqrtStep (R := R) a :=
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
    ∃ step : DDSqrtStep (R := R) a,
      step.x1 = x1 ∧ step.correction = correction ∧ step.hi_out = hi_out := by
  obtain ⟨lo_out, hlo_out_exact⟩ :=
    twoSum_exact (R := R) x1 correction hx1_nz hcorrection_nz hi_out hhi_out
  refine ⟨ofWitnesses (R := R) x1 prod residual two_x1 htwo_x1_val
            correction hcorrection hi_out hhi_out lo_out hlo_out_exact,
          ?_, ?_, ?_⟩ <;> rfl

end DDSqrtStep

end DDSqrt
