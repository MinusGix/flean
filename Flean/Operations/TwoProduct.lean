import Flean.Operations.MulErrorRepresentable

/-! # TwoProduct: Error-Free Transformation for Multiplication

TwoProduct recovers the exact rounding error of floating-point multiplication.
Given `p = fl(a × b)`, the FMA computes `e = fma(a, b, -p)` such that
`p + e = a × b` exactly. This is the multiplicative analogue of TwoSum and a
foundational building block for compensated dot products and double-double arithmetic.

The key condition `fmaProdE a b ≥ min_exp` prevents severe underflow: without it,
the product can lose more than prec bits during subnormal rounding, making the
error unrepresentable.
-/

section TwoProduct

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- **TwoProduct correctness**.

For any two nonzero finite floats whose product doesn't severely underflow
(`fmaProdE a b ≥ min_exp`), the FMA-based error recovery `e = fma(a, b, -p)`
satisfies `p + e = a × b` exactly. -/
theorem twoProduct_exact (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (p : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hp : a * b = p)
    (hno_underflow : fmaProdE a b ≥ FloatFormat.min_exp) :
    ∃ e : FiniteFp,
      (p.toVal : R) + e.toVal = a.toVal * b.toVal := by
  by_cases herr : (a.toVal : R) * b.toVal - p.toVal = 0
  · exact ⟨0, by rw [show (0 : FiniteFp).toVal (R := R) = 0 from FiniteFp.toVal_isZero rfl]; linarith⟩
  · obtain ⟨e, _, he_val⟩ :=
      mul_error_representable (R := R) a b ha_nz hb_nz p hp hno_underflow herr
    exact ⟨e, by rw [he_val]; ring⟩

end TwoProduct
