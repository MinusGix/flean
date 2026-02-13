import Flean.Operations.Add

/-! # Floating-Point Subtraction

Subtraction is defined as `x - y = x + (-y)`, delegating to `fpAdd`. -/

section Sub

variable [FloatFormat]

/-- Subtract finite floats using contextual rounding policy. -/
def fpSubFinite [RModeExec] (a b : FiniteFp) : Fp :=
  fpAddFinite a (-b)

/-- IEEE 754 subtraction with contextual rounding policy. -/
def fpSub [RModeExec] (x y : Fp) : Fp :=
  fpAdd x (-y)

/-! ## Correctness -/

/-- Class-driven correctness for nonzero finite differences. -/
theorem fpSubFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp)
    (hdiff : (a.toVal : R) - b.toVal ≠ 0) :
    fpSubFinite a b = RMode.round ((a.toVal : R) - b.toVal) := by
  have hdiff' : (a.toVal : R) + (-b).toVal ≠ 0 := by
    simpa [FiniteFp.toVal_neg_eq_neg, sub_eq_add_neg] using hdiff
  simpa [fpSubFinite, FiniteFp.toVal_neg_eq_neg, sub_eq_add_neg] using
    (fpAddFinite_correct (R := R) a (-b) hdiff')

/-! ## Relationship to fpAdd -/

/-- `fpSub` is just `fpAdd` with negated second operand. -/
theorem fpSub_eq_fpAdd_neg [RModeExec] (x y : Fp) :
    fpSub x y = fpAdd x (-y) := rfl

/-- `fpSubFinite` is just `fpAddFinite` with negated second operand. -/
theorem fpSubFinite_eq_fpAddFinite_neg [RModeExec] (a b : FiniteFp) :
    fpSubFinite a b = fpAddFinite a (-b) := rfl

end Sub
