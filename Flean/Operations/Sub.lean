import Flean.Operations.Add

/-! # Floating-Point Subtraction

Subtraction is defined as `x - y = x + (-y)`, delegating to `fpAdd`. -/

section Sub

variable [FloatFormat]

def fpSubFinite [RModeExec] (a b : FiniteFp) : Fp :=
  a + (-b)

instance [RModeExec] : HSub FiniteFp FiniteFp Fp where
  hSub := fpSubFinite

@[simp] theorem sub_finite_eq_fpSubFinite [RModeExec] (x y : FiniteFp) : x - y = fpSubFinite x y := rfl

/-- IEEE 754 subtraction with contextual rounding policy. -/
def fpSub [RModeExec] (x y : Fp) : Fp :=
  x + (-y)

instance [RModeExec] : HSub Fp Fp Fp where
  hSub := fpSub

@[simp] theorem sub_eq_fpSub [RModeExec] (x y : Fp) : x - y = fpSub x y := rfl

/-! ## Correctness -/

/-- Class-driven correctness for nonzero finite differences. -/
theorem fpSubFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp)
    (hdiff : (a.toVal : R) - b.toVal ≠ 0) :
    a - b = RMode.round ((a.toVal : R) - b.toVal) := by
  have hdiff' : (a.toVal : R) + (-b).toVal ≠ 0 := by
    simpa [FiniteFp.toVal_neg_eq_neg, sub_eq_add_neg] using hdiff
  simpa [sub_finite_eq_fpSubFinite, fpSubFinite, FiniteFp.toVal_neg_eq_neg, sub_eq_add_neg] using
    (fpAddFinite_correct (R := R) a (-b) hdiff')

/-! ## Relationship to fpAdd -/

/-- `fpSub` is just `fpAdd` with negated second operand. -/
theorem fpSub_eq_fpAdd_neg [RModeExec] (x y : Fp) :
    x - y = x + (-y) := rfl

/-- `fpSubFinite` is just `fpAddFinite` with negated second operand. -/
theorem fpSubFinite_eq_fpAddFinite_neg [RModeExec] (a b : FiniteFp) :
    a - b = a + (-b) := rfl

end Sub
