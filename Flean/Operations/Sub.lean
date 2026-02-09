import Flean.Operations.Add

/-! # Floating-Point Subtraction

Subtraction is defined as `x - y = x + (-y)`, delegating to `fpAdd`. -/

section Sub

variable [FloatFormat]

/-- Subtract two finite floating-point numbers: `a - b = fpAddFinite mode a (-b)`. -/
def fpSubFinite (mode : RoundingMode) (a b : FiniteFp) : Fp :=
  fpAddFinite mode a (-b)

/-- IEEE 754 floating-point subtraction: `x - y = fpAdd mode x (-y)`. -/
def fpSub (mode : RoundingMode) (x y : Fp) : Fp :=
  fpAdd mode x (-y)

/-! ## Correctness -/

/-- `fpSubFinite` correctly rounds the exact difference for nonzero results. -/
theorem fpSubFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp)
    (hdiff : (a.toVal : R) - b.toVal ≠ 0) :
    fpSubFinite mode a b = mode.round ((a.toVal : R) - b.toVal) := by
  unfold fpSubFinite
  rw [show (a.toVal : R) - b.toVal = a.toVal + (-b).toVal from by
    rw [FiniteFp.toVal_neg_eq_neg]; ring]  at hdiff ⊢
  exact fpAddFinite_correct mode a (-b) hdiff

/-! ## Relationship to fpAdd -/

/-- `fpSub` is just `fpAdd` with negated second operand. -/
theorem fpSub_eq_fpAdd_neg (mode : RoundingMode) (x y : Fp) :
    fpSub mode x y = fpAdd mode x (-y) := rfl

/-- `fpSubFinite` is just `fpAddFinite` with negated second operand. -/
theorem fpSubFinite_eq_fpAddFinite_neg (mode : RoundingMode) (a b : FiniteFp) :
    fpSubFinite mode a b = fpAddFinite mode a (-b) := rfl

end Sub
