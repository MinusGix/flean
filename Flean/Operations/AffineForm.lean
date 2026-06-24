import Flean.Operations.ScaledInt

/-! # The near-affine domain — the first *continuous structural* shadow (the missing quadrant)

Everything in the reduction stack so far is either **discrete structure on integer-valued FP**
(mod-p, sign, sign×magnitude — `ExactInt`) or **value-fidelity on the approximate pillar**
(`ScaledInt`: how far a float is from a fixed-point constant). What was missing is the quadrant
the reductionist vision actually targets: **continuous *structure*** — "this computation is
(approximately) a known *shape*", the metric analogue of "this is mod-p arithmetic."

This file plants the flag there with the simplest such shape: **affine**. An `AffineForm R`
carries a float `fp` together with the *affine ideal* `a · x + b` it is meant to realize (slope
`a`, intercept `b`, input point `x`) and a running error bound `err` with `|fp.toVal − (a·x+b)| ≤
err`. It is exactly `ScaledInt` with the constant ideal `m · 2^s` replaced by an **affine** ideal
`a · x + b` — a degree-1 Taylor model / affine-arithmetic form.

## Two payoffs

**The transformer is shape-agnostic.** `ScaledInt`'s forward-error triangle never used the
`m · 2^s` structure of its ideal beyond "it's some real number." So the *same* sound transformer
re-establishes the invariant for the affine ideal — we reuse the err-composition machinery and
only change the shadow (`fpAddFinite_inexact_general` below generalises
`fpAddFinite_scaled_inexact`; `ScaledInt` is the `i := m·2^s` special case). This is the design
note's thesis made literal: one sound transformer, many concretizations γ.

**+ closes, × leaks — the metric dual of the sign story.** Affine forms add coefficient-wise
(`AffineForm.add`: `(a₁+a₂)·x + (b₁+b₂)`, errors compose) — `+` stays in the domain. But the
product of two affine ideals is *quadratic*: `(a₁x+b₁)(a₂x+b₂) = a₁a₂·x² + …`. The affine domain
cannot hold the `x²` term; it **leaks into the error**, bounded only with a *magnitude bound on
the input* `|x| ≤ X` (`affine_mul_nonlinearity`: residual `≤ |a₁a₂|·X²`). This is the exact mirror
of the sign domain, where `×` closed but `+` leaked and needed a magnitude reduced product. There
as here, closing the hard operation forces a **reduced product with an interval domain on the
inputs**.

(Why this matters downstream: in a fixed ReLU activation region a layer is *exactly* affine in its
input, so `AffineForm` with `err` from FP-rounding only is the natural carrier for a verified
local linear region; crossing a region boundary is exactly where a `max`/`×` injects the
nonlinearity that leaks into `err`. See the strategic note in `exact-int-design.md`.)
-/

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A float paired with the affine ideal `a · x + b` it approximates, and a bound `err` on the
deviation. `err = 0` is the exact affine case. The metric/continuous analogue of `ScaledInt`. -/
structure AffineForm (R : Type*) [FloatFormat] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  /-- The actual float value. -/
  fp : FiniteFp
  /-- Slope: coefficient of the tracked input. -/
  a : R
  /-- Intercept. -/
  b : R
  /-- The tracked input point. -/
  x : R
  /-- Running error bound. -/
  err : R
  /-- The float is within `err` of the affine ideal `a · x + b`. -/
  herr : |(fp.toVal : R) - (a * x + b)| ≤ err

/-- The affine ideal `a · x + b` this approximates. -/
def AffineForm.value (p : AffineForm R) : R := p.a * p.x + p.b

/-- The form tracks its ideal: the actual float is within `err` of the affine value. This is
`herr` restated through `value` — the concretization γ of the affine domain. -/
theorem AffineForm.abs_toVal_sub_value_le (p : AffineForm R) :
    |(p.fp.toVal : R) - p.value| ≤ p.err := p.herr

/-- **Negation** — total and *exact* (FiniteFp negation flips the sign bit losslessly), so the
error is unchanged. Completes the additive structure; enables residuals (e.g. `y − (affine
approximation)`). Ideal `↦ −(a·x + b)`. -/
def AffineForm.neg (p : AffineForm R) : AffineForm R where
  fp := -p.fp
  a := -p.a
  b := -p.b
  x := p.x
  err := p.err
  herr := by
    rw [FiniteFp.toVal_neg_eq_neg,
      show -(p.fp.toVal : R) - (-p.a * p.x + -p.b) = -((p.fp.toVal : R) - (p.a * p.x + p.b)) by ring,
      abs_neg]
    exact p.herr

@[simp] theorem AffineForm.neg_a (p : AffineForm R) : p.neg.a = -p.a := rfl
@[simp] theorem AffineForm.neg_b (p : AffineForm R) : p.neg.b = -p.b := rfl
@[simp] theorem AffineForm.neg_x (p : AffineForm R) : p.neg.x = p.x := rfl
@[simp] theorem AffineForm.neg_err (p : AffineForm R) : p.neg.err = p.err := rfl

@[simp] theorem AffineForm.neg_value (p : AffineForm R) : p.neg.value = -p.value := by
  simp only [AffineForm.value, AffineForm.neg_a, AffineForm.neg_b, AffineForm.neg_x]; ring

/-- The exact base case: a float realising an affine value exactly, with zero error. -/
def AffineForm.ofExact (f : FiniteFp) (a b x : R) (h : (f.toVal : R) = a * x + b) :
    AffineForm R :=
  ⟨f, a, b, x, 0, by rw [h]; simp⟩

@[simp] theorem AffineForm.ofExact_err (f : FiniteFp) (a b x : R)
    (h : (f.toVal : R) = a * x + b) : (AffineForm.ofExact f a b x h).err = (0 : R) := rfl

/-! ## The nonlinearity headline (pure): × leaves the affine domain, bounded by `|x| ≤ X`

This needs no FP and no rounding typeclasses — it is the structural fact that multiplication of
affine ideals produces a quadratic residual, quantified against an input-magnitude bound. -/

omit [FloatFormat] in
/-- **× leaks a quadratic term.** The product of two affine ideals equals the *linear*
approximation `(a₁b₂+a₂b₁)·x + b₁b₂` plus a residual `a₁a₂·x²`, whose size is bounded by
`|a₁a₂|·X²` given `|x| ≤ X`. The seam where the affine domain must reduce-product with an interval
domain on the input to close `×`. -/
theorem affine_mul_nonlinearity (a₁ b₁ a₂ b₂ x X : R) (hX : |x| ≤ X) :
    |(a₁ * x + b₁) * (a₂ * x + b₂) - ((a₁ * b₂ + a₂ * b₁) * x + b₁ * b₂)| ≤ |a₁ * a₂| * X ^ 2 := by
  have hexpand : (a₁ * x + b₁) * (a₂ * x + b₂) - ((a₁ * b₂ + a₂ * b₁) * x + b₁ * b₂)
      = (a₁ * a₂) * x ^ 2 := by ring
  rw [hexpand, abs_mul]
  have hx2 : |x ^ 2| ≤ X ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg x) hX 2
  exact mul_le_mul_of_nonneg_left hx2 (abs_nonneg _)

/-! ## The shape-agnostic forward-error transformer

`fpAddFinite_scaled_inexact` (in `ScaledInt`) bounds the float sum against the ideal `m·2^s` sum.
Its proof only ever uses that the ideal is *some* real value; the fixed-point structure is
incidental. Here is the same bound for an **arbitrary** ideal decomposition `i_a`, `i_b`, of which
both `ScaledInt` (`i := m·2^s`) and `AffineForm` (`i := a·x+b`) are instances. -/

section Compose
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Generic composition building block.** Adding two inexact values with *any* ideal real
values `i_a`, `i_b`: the float result's deviation from `i_a + i_b` is the two input errors plus
this op's rounding correction (bounded against the ideal magnitude). Shape-agnostic — the
transformer does not see how the ideal is built. -/
theorem fpAddFinite_inexact_general (a b : FiniteFp) (i_a i_b err_a err_b : R) (f : FiniteFp)
    (ha : |(a.toVal : R) - i_a| ≤ err_a)
    (hb : |(b.toVal : R) - i_b| ≤ err_b)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hf : a + b = Fp.finite f) :
    |(f.toVal : R) - (i_a + i_b)|
      ≤ (1 + η) * (err_a + err_b) + η * |i_a + i_b|
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have hη_nn : (0 : R) ≤ η := by positivity
  have hround : (○((a.toVal : R) + b.toVal) : Fp) = Fp.finite f := by
    rw [← fpAddFinite_correct (R := R) a b hsum_ne]; exact hf
  have hrb := round_preserves_abs_error_unified (R := R) ((a.toVal : R) + b.toVal) hround
  have hinput : |((a.toVal : R) + b.toVal) - (i_a + i_b)| ≤ err_a + err_b := by
    have heq : ((a.toVal : R) + b.toVal) - (i_a + i_b)
        = ((a.toVal : R) - i_a) + ((b.toVal : R) - i_b) := by ring
    rw [heq]; exact (abs_add_le _ _).trans (add_le_add ha hb)
  have hmag : |(a.toVal : R) + b.toVal| ≤ |i_a + i_b| + (err_a + err_b) := by
    have h1 := abs_sub_abs_le_abs_sub ((a.toVal : R) + b.toVal) (i_a + i_b)
    linarith [hinput, h1]
  calc |(f.toVal : R) - (i_a + i_b)|
      ≤ |(f.toVal : R) - ((a.toVal : R) + b.toVal)|
          + |((a.toVal : R) + b.toVal) - (i_a + i_b)| := abs_sub_le _ _ _
    _ ≤ (η * |(a.toVal : R) + b.toVal|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)) + (err_a + err_b) :=
        add_le_add hrb hinput
    _ ≤ (η * (|i_a + i_b| + (err_a + err_b))
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)) + (err_a + err_b) := by
        gcongr
    _ = (1 + η) * (err_a + err_b) + η * |i_a + i_b|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by ring

/-! ## `add`: affine forms compose under addition (`+` closes) -/

/-- **Inexact affine addition.** Two affine forms over the same input `x` add coefficient-wise to
`(a₁+a₂)·x + (b₁+b₂)`; the error grows by the shape-agnostic forward-error formula. The result
float is computed automatically; the caller supplies finiteness + nonzero. -/
def AffineForm.add (p q : AffineForm R) (hx : p.x = q.x)
    (hsum_ne : (p.fp.toVal : R) + q.fp.toVal ≠ 0)
    (hfin : (p.fp + q.fp).isFinite) : AffineForm R where
  fp := (p.fp + q.fp).toFiniteOr0
  a := p.a + q.a
  b := p.b + q.b
  x := p.x
  err := (1 + η) * (p.err + q.err) + η * |(p.a + q.a) * p.x + (p.b + q.b)|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hq' : |(q.fp.toVal : R) - (q.a * p.x + q.b)| ≤ q.err := by rw [hx]; exact q.herr
    have hgen := fpAddFinite_inexact_general p.fp q.fp (p.a * p.x + p.b) (q.a * p.x + q.b)
      p.err q.err _ p.herr hq' hsum_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : (p.a * p.x + p.b) + (q.a * p.x + q.b) = (p.a + q.a) * p.x + (p.b + q.b) := by ring
    rw [hval] at hgen; exact hgen

@[simp] theorem AffineForm.add_a (p q : AffineForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).a = p.a + q.a := rfl
@[simp] theorem AffineForm.add_b (p q : AffineForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).b = p.b + q.b := rfl
@[simp] theorem AffineForm.add_x (p q : AffineForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).x = p.x := rfl
@[simp] theorem AffineForm.add_fp (p q : AffineForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).fp = (p.fp + q.fp).toFiniteOr0 := rfl
@[simp] theorem AffineForm.add_err (p q : AffineForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).err
      = (1 + η) * (p.err + q.err) + η * |(p.a + q.a) * p.x + (p.b + q.b)|
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := rfl

/-- The added form's ideal is the sum of ideals — `+` is exact on the *shadow* (only `err`
carries the FP cost). -/
@[simp] theorem AffineForm.add_value (p q : AffineForm R) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).value = p.value + q.value := by
  simp only [AffineForm.value, AffineForm.add_a, AffineForm.add_b, AffineForm.add_x, hx]; ring

/-! ## The generic multiplicative transformer + `mul`: `×` closes only via reduced product

`fpMulFinite_scaled_inexact` (in `ScaledInt`) is, like its additive sibling, shape-agnostic — it
bounds the float product against the *exact* product of the two ideals. Here it is for arbitrary
ideals. `AffineForm.mul` then composes this with `affine_mul_nonlinearity` (the quadratic leak,
needing `|x| ≤ X`): the result form's ideal is the **linearization** of the product, and the
quadratic part is absorbed into `err`. This is the reduced product — `×` closes only by importing
the input-magnitude bound `X` (the interval domain on the input). -/

/-- **Generic multiplicative building block.** The float product's deviation from the *exact*
product of ideals `i_a · i_b` is the propagated input error plus this op's rounding correction.
Shape-agnostic; `ScaledInt`'s and `AffineForm`'s mul both instantiate it. -/
theorem fpMulFinite_inexact_general (a b : FiniteFp) (i_a i_b err_a err_b : R) (f : FiniteFp)
    (ha : |(a.toVal : R) - i_a| ≤ err_a)
    (hb : |(b.toVal : R) - i_b| ≤ err_b)
    (hprod_ne : (a.toVal : R) * b.toVal ≠ 0)
    (hf : a * b = Fp.finite f) :
    |(f.toVal : R) - i_a * i_b|
      ≤ η * |i_a * i_b|
        + (1 + η) * (|i_a| * err_b + err_a * |i_b| + err_a * err_b)
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have hη_nn : (0 : R) ≤ η := by positivity
  have herr_a_nn : (0 : R) ≤ err_a := le_trans (abs_nonneg _) ha
  have hround : (○((a.toVal : R) * b.toVal) : Fp) = Fp.finite f := by
    rw [← fpMulFinite_correct (R := R) a b hprod_ne]; exact hf
  have hrb := round_preserves_abs_error_unified (R := R) ((a.toVal : R) * b.toVal) hround
  have hinput : |(a.toVal : R) * b.toVal - i_a * i_b|
      ≤ |i_a| * err_b + err_a * |i_b| + err_a * err_b := by
    have hexp : (a.toVal : R) * b.toVal - i_a * i_b
        = i_a * ((b.toVal : R) - i_b) + ((a.toVal : R) - i_a) * i_b
          + ((a.toVal : R) - i_a) * ((b.toVal : R) - i_b) := by ring
    rw [hexp]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) herr_a_nn
  have hmag : |(a.toVal : R) * b.toVal|
      ≤ |i_a * i_b| + (|i_a| * err_b + err_a * |i_b| + err_a * err_b) := by
    have h1 := abs_sub_abs_le_abs_sub ((a.toVal : R) * b.toVal) (i_a * i_b)
    linarith [hinput, h1]
  calc |(f.toVal : R) - i_a * i_b|
      ≤ |(f.toVal : R) - (a.toVal : R) * b.toVal|
          + |(a.toVal : R) * b.toVal - i_a * i_b| := abs_sub_le _ _ _
    _ ≤ (η * |(a.toVal : R) * b.toVal|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ))
        + (|i_a| * err_b + err_a * |i_b| + err_a * err_b) := add_le_add hrb hinput
    _ ≤ (η * (|i_a * i_b| + (|i_a| * err_b + err_a * |i_b| + err_a * err_b))
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ))
        + (|i_a| * err_b + err_a * |i_b| + err_a * err_b) := by gcongr
    _ = η * |i_a * i_b|
        + (1 + η) * (|i_a| * err_b + err_a * |i_b| + err_a * err_b)
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by ring

/-- **Inexact affine multiplication.** Over a common input `x` bounded by `|x| ≤ X`, the product
of two affine forms is itself an affine form whose ideal is the **linearization** `(a₁b₂+a₂b₁)·x +
b₁b₂` of the true product. The error absorbs three things: the propagated input error, this op's FP
rounding, and the *quadratic leak* `|a₁a₂|·X²`. `×` closes only by importing the input bound `X`. -/
def AffineForm.mul (p q : AffineForm R) (hx : p.x = q.x) (X : R) (hX : |p.x| ≤ X)
    (hprod_ne : (p.fp.toVal : R) * q.fp.toVal ≠ 0)
    (hfin : (p.fp * q.fp).isFinite) : AffineForm R where
  fp := (p.fp * q.fp).toFiniteOr0
  a := p.a * q.b + q.a * p.b
  b := p.b * q.b
  x := p.x
  err := (η * |(p.a * p.x + p.b) * (q.a * p.x + q.b)|
            + (1 + η) * (|p.a * p.x + p.b| * q.err + p.err * |q.a * p.x + q.b| + p.err * q.err)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ))
          + |p.a * q.a| * X ^ 2
  herr := by
    have hq' : |(q.fp.toVal : R) - (q.a * p.x + q.b)| ≤ q.err := by rw [hx]; exact q.herr
    have hmul := fpMulFinite_inexact_general p.fp q.fp (p.a * p.x + p.b) (q.a * p.x + q.b)
      p.err q.err _ p.herr hq' hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hnonlin := affine_mul_nonlinearity p.a p.b q.a q.b p.x X hX
    calc |((p.fp * q.fp).toFiniteOr0.toVal : R) - ((p.a * q.b + q.a * p.b) * p.x + p.b * q.b)|
        ≤ |((p.fp * q.fp).toFiniteOr0.toVal : R) - (p.a * p.x + p.b) * (q.a * p.x + q.b)|
            + |(p.a * p.x + p.b) * (q.a * p.x + q.b)
                - ((p.a * q.b + q.a * p.b) * p.x + p.b * q.b)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hmul hnonlin

@[simp] theorem AffineForm.mul_a (p q : AffineForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).a = p.a * q.b + q.a * p.b := rfl
@[simp] theorem AffineForm.mul_b (p q : AffineForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).b = p.b * q.b := rfl
@[simp] theorem AffineForm.mul_x (p q : AffineForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).x = p.x := rfl
@[simp] theorem AffineForm.mul_fp (p q : AffineForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).fp = (p.fp * q.fp).toFiniteOr0 := rfl

/-- The mul form's ideal is the **linearization** of the product — not `p.value · q.value`. The
gap between them is exactly the bounded quadratic leak (`mul_value_sub_prod`). -/
@[simp] theorem AffineForm.mul_value (p q : AffineForm R) (hx X hX hprod_ne hfin) :
    (p.mul q hx X hX hprod_ne hfin).value
      = (p.a * q.b + q.a * p.b) * p.x + p.b * q.b := by
  simp only [AffineForm.value, AffineForm.mul_a, AffineForm.mul_b, AffineForm.mul_x]

/-- The mul form's ideal (the linearization) is within the quadratic leak `|a₁a₂|·X²` of the true
product of ideals. Makes explicit that `×` stays affine only up to the bounded nonlinearity. -/
theorem AffineForm.mul_value_sub_prod (p q : AffineForm R) (hx : p.x = q.x) (X : R)
    (hX : |p.x| ≤ X) (hprod_ne hfin) :
    |(p.mul q hx X hX hprod_ne hfin).value - p.value * q.value| ≤ |p.a * q.a| * X ^ 2 := by
  have h := affine_mul_nonlinearity p.a p.b q.a q.b p.x X hX
  simp only [AffineForm.value, ← hx]
  rw [abs_sub_comm]; exact h

end Compose
