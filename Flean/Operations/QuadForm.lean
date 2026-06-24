import Flean.Operations.AffineForm

/-! # The degree-2 Taylor-model domain — the model-order tower

`AffineForm` (degree 1) closes under `+` but *leaks* under `×`: the product of two affine ideals is
quadratic, and the affine domain cannot hold the `x²` term, so it dumps it into `err` (bounded only
with an input bound `X`). The fix is the next rung of the **model-order tower**: a degree-2 form
that *catches* the quadratic term the affine form leaked.

A `QuadForm R` tracks a float against the quadratic ideal `a·x² + b·x + c`, with `|fp.toVal −
(a·x²+b·x+c)| ≤ err`. The tower structure:

* **`add`** — quadratic forms add coefficient-wise, stay degree 2. `+` closes.
* **`ofAffineMul`** (the headline) — the product of two *affine* forms is *exactly* a quadratic
  ideal `(pa·qa)·x² + (pa·qb+qa·pb)·x + pb·qb`, so the degree-2 form catches it with **only the FP
  rounding error — no `x²` leak, and crucially no input bound `X` needed.** This is the precise
  sense in which degree-2 catches what degree-1 leaked.
* (The tower continues: a degree-2 `×` degree-2 product is degree 4, leaking degree 3–4 — caught
  only by a degree-3 form, and so on. Each rung catches the previous rung's leak.)

So the domains form a *tower indexed by model order*: degree `d` catches polynomial structure up to
degree `d` and leaks degree `d+1`. `AffineForm` is `d = 1`; `QuadForm` is `d = 2`.
-/

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A float paired with the quadratic ideal `a·x² + b·x + c` it approximates, and a deviation bound
`err`. The degree-2 rung of the Taylor-model tower. -/
structure QuadForm (R : Type*) [FloatFormat] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  /-- The actual float value. -/
  fp : FiniteFp
  /-- The `x²` coefficient. -/
  a : R
  /-- The `x` coefficient. -/
  b : R
  /-- The constant term. -/
  c : R
  /-- The input point. -/
  x : R
  /-- Running error bound. -/
  err : R
  /-- The float is within `err` of the quadratic ideal `a·x² + b·x + c`. -/
  herr : |(fp.toVal : R) - (a * x ^ 2 + b * x + c)| ≤ err

namespace QuadForm

/-- The quadratic ideal `a·x² + b·x + c` this approximates. -/
def value (p : QuadForm R) : R := p.a * p.x ^ 2 + p.b * p.x + p.c

/-- The form tracks its ideal: the float is within `err` of the quadratic value (γ). -/
theorem abs_toVal_sub_value_le (p : QuadForm R) :
    |(p.fp.toVal : R) - p.value| ≤ p.err := p.herr

/-- The exact base case: a float realising a quadratic value exactly, with zero error. -/
def ofExact (f : FiniteFp) (a b c x : R) (h : (f.toVal : R) = a * x ^ 2 + b * x + c) :
    QuadForm R :=
  ⟨f, a, b, c, x, 0, by rw [h]; simp⟩

@[simp] theorem ofExact_err (f : FiniteFp) (a b c x : R)
    (h : (f.toVal : R) = a * x ^ 2 + b * x + c) : (ofExact f a b c x h).err = (0 : R) := rfl

omit [FloatFormat] in
/-- **The degree-2 leak.** The product of two quadratic ideals (degree 4) exceeds its degree-2
truncation by the degree-3 and degree-4 terms, bounded over an input box `|x| ≤ X` by
`|a₁a₂|·X⁴ + |a₁b₂+b₁a₂|·X³`. The tower continues: degree-2 catches up to degree 2 and leaks
degree 3–4 (mirroring degree-1's degree-2 leak). -/
theorem quad_mul_leak (a₁ b₁ c₁ a₂ b₂ c₂ x X : R) (hX : |x| ≤ X) :
    |(a₁ * x ^ 2 + b₁ * x + c₁) * (a₂ * x ^ 2 + b₂ * x + c₂)
        - ((a₁ * c₂ + b₁ * b₂ + c₁ * a₂) * x ^ 2 + (b₁ * c₂ + c₁ * b₂) * x + c₁ * c₂)|
      ≤ |a₁ * a₂| * X ^ 4 + |a₁ * b₂ + b₁ * a₂| * X ^ 3 := by
  rw [show (a₁ * x ^ 2 + b₁ * x + c₁) * (a₂ * x ^ 2 + b₂ * x + c₂)
        - ((a₁ * c₂ + b₁ * b₂ + c₁ * a₂) * x ^ 2 + (b₁ * c₂ + c₁ * b₂) * x + c₁ * c₂)
      = a₁ * a₂ * x ^ 4 + (a₁ * b₂ + b₁ * a₂) * x ^ 3 from by ring]
  have h4 : |a₁ * a₂ * x ^ 4| ≤ |a₁ * a₂| * X ^ 4 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hX 4) (abs_nonneg _)
  have h3 : |(a₁ * b₂ + b₁ * a₂) * x ^ 3| ≤ |a₁ * b₂ + b₁ * a₂| * X ^ 3 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hX 3) (abs_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add h4 h3)

section Compose
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Addition.** Quadratic forms over the same input add coefficient-wise; the error grows by the
shape-agnostic forward-error formula. `+` stays degree 2. -/
def add (p q : QuadForm R) (hx : p.x = q.x)
    (hsum_ne : (p.fp.toVal : R) + q.fp.toVal ≠ 0)
    (hfin : (p.fp + q.fp).isFinite) : QuadForm R where
  fp := (p.fp + q.fp).toFiniteOr0
  a := p.a + q.a
  b := p.b + q.b
  c := p.c + q.c
  x := p.x
  err := (1 + η) * (p.err + q.err) + η * |p.value + q.value|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hgen := fpAddFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hsum_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : (p.a + q.a) * p.x ^ 2 + (p.b + q.b) * p.x + (p.c + q.c) = p.value + q.value := by
      rw [show p.value = p.a * p.x ^ 2 + p.b * p.x + p.c from rfl,
        show q.value = q.a * q.x ^ 2 + q.b * q.x + q.c from rfl, ← hx]; ring
    rw [hval]; exact hgen

@[simp] theorem add_a (p q : QuadForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).a = p.a + q.a := rfl
@[simp] theorem add_b (p q : QuadForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).b = p.b + q.b := rfl
@[simp] theorem add_c (p q : QuadForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).c = p.c + q.c := rfl
@[simp] theorem add_x (p q : QuadForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).x = p.x := rfl

@[simp] theorem add_value (p q : QuadForm R) (hx : p.x = q.x) (hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).value = p.value + q.value := by
  simp only [value, add_a, add_b, add_c, add_x, ← hx]; ring

/-! ## The headline: degree-2 catches the affine product exactly

`AffineForm.mul` produced `err = FP_bound + |pa·qa|·X²` and needed an input bound `X` — it *leaked*
the quadratic. Here the same affine product is held *exactly* by a `QuadForm`: `err = FP_bound`, no
leak term, no `X`. The degree-2 rung catches what degree-1 dumped. -/

/-- **The affine product, caught exactly as a quadratic.** The FP product of two affine forms is a
`QuadForm` whose ideal is *exactly* the product `p.value · q.value` (a genuine quadratic), with only
the floating-point rounding error — no `x²` leak, no input bound. -/
def ofAffineMul (p q : AffineForm R) (hx : p.x = q.x)
    (hprod_ne : (p.fp.toVal : R) * q.fp.toVal ≠ 0)
    (hfin : (p.fp * q.fp).isFinite) : QuadForm R where
  fp := (p.fp * q.fp).toFiniteOr0
  a := p.a * q.a
  b := p.a * q.b + q.a * p.b
  c := p.b * q.b
  x := p.x
  err := η * |p.value * q.value|
          + (1 + η) * (|p.value| * q.err + p.err * |q.value| + p.err * q.err)
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb := fpMulFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : (p.a * q.a) * p.x ^ 2 + (p.a * q.b + q.a * p.b) * p.x + p.b * q.b
        = p.value * q.value := by
      rw [show p.value = p.a * p.x + p.b from rfl, show q.value = q.a * q.x + q.b from rfl,
        ← hx]; ring
    rw [hval]; exact hb

@[simp] theorem ofAffineMul_a (p q : AffineForm R) (hx hprod_ne hfin) :
    (ofAffineMul p q hx hprod_ne hfin).a = p.a * q.a := rfl
@[simp] theorem ofAffineMul_b (p q : AffineForm R) (hx hprod_ne hfin) :
    (ofAffineMul p q hx hprod_ne hfin).b = p.a * q.b + q.a * p.b := rfl
@[simp] theorem ofAffineMul_c (p q : AffineForm R) (hx hprod_ne hfin) :
    (ofAffineMul p q hx hprod_ne hfin).c = p.b * q.b := rfl
@[simp] theorem ofAffineMul_x (p q : AffineForm R) (hx hprod_ne hfin) :
    (ofAffineMul p q hx hprod_ne hfin).x = p.x := rfl

/-- The degree-2 form's ideal *is* the affine product `p.value · q.value`, caught exactly. -/
@[simp] theorem ofAffineMul_value (p q : AffineForm R) (hx : p.x = q.x) (hprod_ne hfin) :
    (ofAffineMul p q hx hprod_ne hfin).value = p.value * q.value := by
  rw [show (ofAffineMul p q hx hprod_ne hfin).value
        = (p.a * q.a) * p.x ^ 2 + (p.a * q.b + q.a * p.b) * p.x + p.b * q.b from rfl,
    show p.value = p.a * p.x + p.b from rfl, show q.value = q.a * q.x + q.b from rfl, ← hx]; ring

/-! ## The tower continues: degree-2 `×` degree-2 leaks degree 3–4 -/

/-- **Quadratic multiplication.** Over an input box `|x| ≤ X`, the product of two quadratic forms is
the degree-2 *truncation* of the (degree-4) product; the degree-3 and degree-4 terms leak into
`err`, bounded by `|a₁a₂|·X⁴ + |a₁b₂+b₁a₂|·X³` (`quad_mul_leak`). Exactly the affine `mul` pattern
one rung up. -/
def mul (p q : QuadForm R) (hx : p.x = q.x) (X : R) (hX : |p.x| ≤ X)
    (hprod_ne : (p.fp.toVal : R) * q.fp.toVal ≠ 0)
    (hfin : (p.fp * q.fp).isFinite) : QuadForm R where
  fp := (p.fp * q.fp).toFiniteOr0
  a := p.a * q.c + p.b * q.b + p.c * q.a
  b := p.b * q.c + p.c * q.b
  c := p.c * q.c
  x := p.x
  err := (η * |p.value * q.value|
            + (1 + η) * (|p.value| * q.err + p.err * |q.value| + p.err * q.err)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ))
          + (|p.a * q.a| * X ^ 4 + |p.a * q.b + p.b * q.a| * X ^ 3)
  herr := by
    have hb := fpMulFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hqv : q.value = q.a * p.x ^ 2 + q.b * p.x + q.c := by
      rw [show q.value = q.a * q.x ^ 2 + q.b * q.x + q.c from rfl, ← hx]
    have hpv : p.value = p.a * p.x ^ 2 + p.b * p.x + p.c := rfl
    have hleak := quad_mul_leak p.a p.b p.c q.a q.b q.c p.x X hX
    rw [← hpv, ← hqv] at hleak
    calc |((p.fp * q.fp).toFiniteOr0.toVal : R)
            - ((p.a * q.c + p.b * q.b + p.c * q.a) * p.x ^ 2 + (p.b * q.c + p.c * q.b) * p.x
                + p.c * q.c)|
        ≤ |((p.fp * q.fp).toFiniteOr0.toVal : R) - p.value * q.value|
            + |p.value * q.value
                - ((p.a * q.c + p.b * q.b + p.c * q.a) * p.x ^ 2 + (p.b * q.c + p.c * q.b) * p.x
                    + p.c * q.c)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hb hleak

@[simp] theorem mul_a (p q : QuadForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).a = p.a * q.c + p.b * q.b + p.c * q.a := rfl
@[simp] theorem mul_b (p q : QuadForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).b = p.b * q.c + p.c * q.b := rfl
@[simp] theorem mul_c (p q : QuadForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).c = p.c * q.c := rfl
@[simp] theorem mul_x (p q : QuadForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).x = p.x := rfl

/-- The product form's ideal is the degree-2 *truncation* of the (degree-4) product of ideals. -/
@[simp] theorem mul_value (p q : QuadForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).value
      = (p.a * q.c + p.b * q.b + p.c * q.a) * p.x ^ 2 + (p.b * q.c + p.c * q.b) * p.x
        + p.c * q.c := by
  simp only [value, mul_a, mul_b, mul_c, mul_x]

end Compose

end QuadForm
