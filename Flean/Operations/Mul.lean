import Flean.Operations.RoundIntSig

/-! # Floating-Point Multiplication

Softfloat-style floating-point multiplication using `roundIntSigM` as the rounding primitive.

The algorithm for multiplying two finite floats:
1. Compute the sign as XOR of operand signs
2. Compute the magnitude as the product of significands
3. Compute the exponent base from the sum of operand exponents
4. Delegate to `roundIntSigM` for rounding

The exact product `a.toVal * b.toVal` equals `±(a.m * b.m) * 2^(a.e + b.e - 2*prec + 2)`,
which directly feeds into `roundIntSigM`.
-/

section Mul

variable [FloatFormat]

/-- Multiply two finite floating-point numbers with contextual rounding policy.

The exact product `a.toVal * b.toVal` is represented as
`intSigVal (a.s ^^ b.s) (a.m * b.m) (a.e + b.e - 2*prec + 2)`, then rounded via
`roundIntSigM`. -/
def fpMulFinite [RModeExec] (a b : FiniteFp) : Fp :=
  let sign := a.s ^^ b.s
  let mag := a.m * b.m
  let e_base := a.e + b.e - 2 * FloatFormat.prec + 2
  roundIntSigM sign mag e_base

instance [RModeExec] : HMul FiniteFp FiniteFp Fp where
  hMul := fpMulFinite

@[simp] theorem mul_finite_eq_fpMulFinite [RModeExec] (x y : FiniteFp) : x * y = fpMulFinite x y := rfl

/-- IEEE 754 floating-point multiplication with full special-case handling.

Special cases:
- Any NaN operand produces NaN
- `∞ * ∞` = `∞` (with XOR sign)
- `∞ * 0` = NaN
- `∞ * finite_nonzero` = `∞` (with XOR sign)
- `finite * finite` delegates to `fpMulFinite` -/
def fpMul [RModeExec] (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | .infinite sx, .infinite sy => .infinite (sx ^^ sy)
  | .infinite s, .finite f =>
    if f.m = 0 then .NaN else .infinite (s ^^ f.s)
  | .finite f, .infinite s =>
    if f.m = 0 then .NaN else .infinite (f.s ^^ s)
  | .finite a, .finite b => a * b

instance [RModeExec] : HMul Fp Fp Fp where
  hMul := fpMul

@[simp] theorem mul_eq_fpMul [RModeExec] (x y : Fp) : x * y = fpMul x y := rfl

/-! ## Exact Product Representation -/

/-- The exact product of two finite floats equals `intSigVal (a.s ^^ b.s) (a.m * b.m) (a.e + b.e - 2*prec + 2)`.

This is the bridge between the real-valued product `a.toVal * b.toVal` and the
integer-significand representation that `roundIntSigM` expects. -/
theorem fpMulFinite_exact_product {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : FiniteFp) :
    (a.toVal : R) * b.toVal =
    intSigVal (R := R) (a.s ^^ b.s) (a.m * b.m) (a.e + b.e - 2 * FloatFormat.prec + 2) := by
  unfold FiniteFp.toVal FiniteFp.sign' intSigVal
  rw [FloatFormat.radix_val_eq_two, Nat.cast_mul]
  set ea := (2 : R) ^ (a.e - FloatFormat.prec + 1) with hea
  set eb := (2 : R) ^ (b.e - FloatFormat.prec + 1) with heb
  set eab := (2 : R) ^ (a.e + b.e - 2 * FloatFormat.prec + 2) with heab
  -- Key: ea * eb = eab
  have hexp : ea * eb = eab := by
    rw [hea, heb, heab, two_zpow_mul]; congr 1; omega
  -- All sign cases: product of (±m_a * ea) * (±m_b * eb) = ±(m_a * m_b) * eab
  cases a.s <;> cases b.s <;> simp <;> rw [← hexp] <;> ring

/-! ## fpMulFinite Correctness -/

/-- Class-driven correctness for nonzero finite products. -/
theorem fpMulFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp)
    (hprod : (a.toVal : R) * b.toVal ≠ 0) :
    a * b = ○((a.toVal : R) * b.toVal) := by
  have hexact := fpMulFinite_exact_product (R := R) a b
  have hmag_ne : a.m * b.m ≠ 0 := by
    intro hzero
    apply hprod
    rw [hexact]
    unfold intSigVal
    simp [hzero]
  simp only [mul_finite_eq_fpMulFinite, fpMulFinite]
  rw [roundIntSigM_correct_tc (R := R) _ _ _ hmag_ne]
  congr 1
  rw [hexact]

/-! ## Commutativity -/

/-- `fpMulFinite` is commutative. -/
theorem fpMulFinite_comm [RModeExec] (a b : FiniteFp) :
    fpMulFinite a b = fpMulFinite b a := by
  simp only [fpMulFinite, Bool.xor_comm a.s b.s, Nat.mul_comm a.m b.m, add_comm a.e b.e]

/-- `fpMul` is commutative. -/
theorem fpMul_comm [RModeExec] (x y : Fp) :
    x * y = y * x := by
  cases x with
  | NaN => cases y <;> simp [mul_eq_fpMul, fpMul]
  | infinite sx =>
    cases y with
    | NaN => simp [mul_eq_fpMul, fpMul]
    | infinite sy => simp [mul_eq_fpMul, fpMul, Bool.xor_comm]
    | finite b =>
      simp only [mul_eq_fpMul, fpMul]
      by_cases hm : b.m = 0
      · simp [hm]
      · simp [hm, Bool.xor_comm]
  | finite a =>
    cases y with
    | NaN => simp [mul_eq_fpMul, fpMul]
    | infinite sy =>
      simp only [mul_eq_fpMul, fpMul]
      by_cases hm : a.m = 0
      · simp [hm]
      · simp [hm, Bool.xor_comm]
    | finite b => simp [mul_eq_fpMul, fpMul, fpMulFinite_comm]

end Mul
