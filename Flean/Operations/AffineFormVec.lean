import Flean.Operations.AffineForm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Multi-input affine forms — affine arithmetic over a vector input (toward a real layer)

`AffineForm` tracks a float against an affine ideal of *one* input. A real linear layer is affine
in a *vector* of inputs. This file lifts the affine domain to many inputs: an `AffineFormVec R n`
carries a float `fp` against the ideal `c₀ + ∑ᵢ cᵢ · xᵢ` over `n` inputs `x : Fin n → R` — the
standard **affine-arithmetic / zonotope** form, the shadow of a neuron's pre-activation
`⟨w, x⟩ + b`.

The transformers are the shape-agnostic ones again (`fpAddFinite_inexact_general` etc.): only the
*shadow* changes (now a `Finset.sum`), the err-composition is identical. `+` adds the coefficient
vectors and constants and stays affine (`add`); scaling by a constant scales them (`scaleConst`).
Multiplication of two genuinely-multivariate forms would leak the bilinear cross terms into `err`
(the multi-input analogue of `AffineForm.mul`); that and the FP dot-product *constructor* (building
a form from a layer's `⟨w,x⟩+b` computation) are the natural next steps.
-/

open Finset

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A float paired with the affine ideal `c₀ + ∑ᵢ cᵢ · xᵢ` over `n` inputs it approximates, and a
deviation bound `err`. The multi-input (vector) analogue of `AffineForm`. -/
structure AffineFormVec (R : Type*) [FloatFormat] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (n : ℕ) where
  /-- The actual float value. -/
  fp : FiniteFp
  /-- Slope coefficients, one per input. -/
  c : Fin n → R
  /-- Constant term. -/
  c0 : R
  /-- The input values (noise-symbol values). -/
  x : Fin n → R
  /-- Running error bound. -/
  err : R
  /-- The float is within `err` of the affine ideal `c₀ + ∑ᵢ cᵢ · xᵢ`. -/
  herr : |(fp.toVal : R) - (c0 + ∑ i, c i * x i)| ≤ err

namespace AffineFormVec

variable {n : ℕ}

/-- The affine ideal `c₀ + ∑ᵢ cᵢ · xᵢ` this approximates. -/
def value (p : AffineFormVec R n) : R := p.c0 + ∑ i, p.c i * p.x i

/-- The form tracks its ideal: the float is within `err` of the affine value (γ of the domain). -/
theorem abs_toVal_sub_value_le (p : AffineFormVec R n) :
    |(p.fp.toVal : R) - p.value| ≤ p.err := p.herr

/-- The exact base case: a float realising an affine value exactly, with zero error. -/
def ofExact (f : FiniteFp) (c : Fin n → R) (c0 : R) (x : Fin n → R)
    (h : (f.toVal : R) = c0 + ∑ i, c i * x i) : AffineFormVec R n :=
  ⟨f, c, c0, x, 0, by rw [h]; simp⟩

/-- **Negation** — total and exact (FiniteFp negation is lossless), error unchanged. Ideal
`↦ −(c₀ + ∑ cᵢ·xᵢ)`. -/
def neg (p : AffineFormVec R n) : AffineFormVec R n where
  fp := -p.fp
  c := -p.c
  c0 := -p.c0
  x := p.x
  err := p.err
  herr := by
    have hsneg : (∑ i, (-p.c) i * p.x i) = -∑ i, p.c i * p.x i := by
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [FiniteFp.toVal_neg_eq_neg, hsneg,
      show -(p.fp.toVal : R) - (-p.c0 + -∑ i, p.c i * p.x i)
        = -((p.fp.toVal : R) - (p.c0 + ∑ i, p.c i * p.x i)) by ring, abs_neg]
    exact p.herr

@[simp] theorem neg_c (p : AffineFormVec R n) : p.neg.c = -p.c := rfl
@[simp] theorem neg_c0 (p : AffineFormVec R n) : p.neg.c0 = -p.c0 := rfl
@[simp] theorem neg_x (p : AffineFormVec R n) : p.neg.x = p.x := rfl
@[simp] theorem neg_err (p : AffineFormVec R n) : p.neg.err = p.err := rfl

@[simp] theorem neg_value (p : AffineFormVec R n) : p.neg.value = -p.value := by
  have hsneg : (∑ i, (-p.c) i * p.x i) = -∑ i, p.c i * p.x i := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  simp only [value, neg_c, neg_c0, neg_x, hsneg]; ring

@[simp] theorem ofExact_err (f : FiniteFp) (c : Fin n → R) (c0 : R) (x : Fin n → R)
    (h : (f.toVal : R) = c0 + ∑ i, c i * x i) : (ofExact f c c0 x h).err = (0 : R) := rfl

/-- A constant `b.toVal` as a degree-0 multi-input affine form (all coefficients `0`). Models a
bias entering a layer. -/
def ofConst (b : FiniteFp) (x : Fin n → R) : AffineFormVec R n :=
  ⟨b, fun _ => 0, (b.toVal : R), x, 0, by simp⟩

@[simp] theorem ofConst_fp (b : FiniteFp) (x : Fin n → R) : (ofConst b x).fp = b := rfl
@[simp] theorem ofConst_c (b : FiniteFp) (x : Fin n → R) : (ofConst b x).c = fun _ => (0 : R) := rfl
@[simp] theorem ofConst_c0 (b : FiniteFp) (x : Fin n → R) : (ofConst b x).c0 = (b.toVal : R) := rfl
@[simp] theorem ofConst_x (b : FiniteFp) (x : Fin n → R) : (ofConst b x).x = x := rfl
@[simp] theorem ofConst_value (b : FiniteFp) (x : Fin n → R) :
    (ofConst b x).value = (b.toVal : R) := by simp [value]

section Compose
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Multi-input affine addition.** Two forms over the same inputs `x` add coefficient-wise and
constant-wise; the error grows by the shape-agnostic forward-error formula. `+` stays affine. -/
def add (p q : AffineFormVec R n) (hx : p.x = q.x)
    (hsum_ne : (p.fp.toVal : R) + q.fp.toVal ≠ 0)
    (hfin : (p.fp + q.fp).isFinite) : AffineFormVec R n where
  fp := (p.fp + q.fp).toFiniteOr0
  c := p.c + q.c
  c0 := p.c0 + q.c0
  x := p.x
  err := (1 + η) * (p.err + q.err) + η * |p.value + q.value|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hgen := fpAddFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hsum_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : (p.c0 + q.c0) + ∑ i, (p.c + q.c) i * p.x i = p.value + q.value := by
      simp only [value, ← hx, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
    rw [hval]; exact hgen

@[simp] theorem add_c (p q : AffineFormVec R n) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).c = p.c + q.c := rfl
@[simp] theorem add_c0 (p q : AffineFormVec R n) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).c0 = p.c0 + q.c0 := rfl
@[simp] theorem add_x (p q : AffineFormVec R n) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).x = p.x := rfl
@[simp] theorem add_fp (p q : AffineFormVec R n) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).fp = (p.fp + q.fp).toFiniteOr0 := rfl

/-- `+` is exact on the shadow: the added form's ideal is the sum of ideals. -/
@[simp] theorem add_value (p q : AffineFormVec R n) (hx : p.x = q.x) (hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).value = p.value + q.value := by
  simp only [value, add_c, add_c0, add_x, ← hx, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring

/-- **Add a constant float `b`** (a bias), as `add` against a constant form. Ideal becomes
`(c₀ + ∑ cᵢxᵢ) + b`. -/
def addConst (p : AffineFormVec R n) (b : FiniteFp)
    (hsum_ne : (p.fp.toVal : R) + b.toVal ≠ 0)
    (hfin : (p.fp + b).isFinite) : AffineFormVec R n :=
  p.add (ofConst b p.x) rfl hsum_ne hfin

@[simp] theorem addConst_value (p : AffineFormVec R n) (b : FiniteFp)
    (hsum_ne : (p.fp.toVal : R) + b.toVal ≠ 0) (hfin : (p.fp + b).isFinite) :
    (p.addConst b hsum_ne hfin).value = p.value + (b.toVal : R) := by
  rw [addConst, add_value, ofConst_value]

/-- **Scale by a constant float `w`.** Scales every coefficient and the constant — affine, no leak
(the multi-input version of `AffineForm.scaleConst`). Ideal becomes `w · value`. -/
def scaleConst (p : AffineFormVec R n) (w : FiniteFp)
    (hprod_ne : (p.fp.toVal : R) * w.toVal ≠ 0)
    (hfin : (p.fp * w).isFinite) : AffineFormVec R n where
  fp := (p.fp * w).toFiniteOr0
  c := fun i => p.c i * (w.toVal : R)
  c0 := p.c0 * (w.toVal : R)
  x := p.x
  err := η * |p.value * (w.toVal : R)| + (1 + η) * (p.err * |(w.toVal : R)|)
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb0 : |(w.toVal : R) - (w.toVal : R)| ≤ 0 := by simp
    have hmul := fpMulFinite_inexact_general p.fp w p.value (w.toVal : R) p.err 0 _
      p.abs_toVal_sub_value_le hb0 hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : p.c0 * (w.toVal : R) + ∑ i, (p.c i * (w.toVal : R)) * p.x i
        = p.value * (w.toVal : R) := by
      simp only [value, add_mul, Finset.sum_mul]; ring
    rw [hval]
    calc |((p.fp * w).toFiniteOr0.toVal : R) - p.value * (w.toVal : R)|
        ≤ η * |p.value * (w.toVal : R)|
            + (1 + η) * (|p.value| * 0 + p.err * |(w.toVal : R)| + p.err * 0)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := hmul
      _ = η * |p.value * (w.toVal : R)| + (1 + η) * (p.err * |(w.toVal : R)|)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by ring

@[simp] theorem scaleConst_c (p : AffineFormVec R n) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).c = fun i => p.c i * (w.toVal : R) := rfl
@[simp] theorem scaleConst_c0 (p : AffineFormVec R n) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).c0 = p.c0 * (w.toVal : R) := rfl
@[simp] theorem scaleConst_x (p : AffineFormVec R n) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).x = p.x := rfl

/-- Scaling multiplies the ideal by the constant — affine, no leak. -/
@[simp] theorem scaleConst_value (p : AffineFormVec R n) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).value = p.value * (w.toVal : R) := by
  simp only [value, scaleConst_c, scaleConst_c0, scaleConst_x, add_mul, Finset.sum_mul]; ring

end Compose

/-! ## The multi-input nonlinearity bound: `×` leaks the bilinear cross terms

The vector analogue of `affine_mul_nonlinearity`. The product of two multi-input affine ideals is
the linear part plus the bilinear residual `(∑ pᵢxᵢ)(∑ qⱼxⱼ)`, which the affine domain cannot
hold; over an input box `|xᵢ| ≤ X` it is bounded by `X² · (∑|pᵢ|)·(∑|qⱼ|)`. As in the scalar case,
closing `×` needs a reduced product with an interval domain on the inputs. -/

omit [FloatFormat] in
/-- The bilinear leak of a multi-input affine product is bounded by the input box. -/
theorem mul_nonlinearity_bound (p q x : Fin n → R) (X : R)
    (hX : ∀ i, |x i| ≤ X) (hX0 : 0 ≤ X) :
    |(∑ i, p i * x i) * (∑ j, q j * x j)| ≤ X ^ 2 * ((∑ i, |p i|) * (∑ j, |q j|)) := by
  have hbound : ∀ (r : Fin n → R), |∑ i, r i * x i| ≤ (∑ i, |r i|) * X := by
    intro r
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hX i) (abs_nonneg _)
  have hp_nn : (0 : R) ≤ (∑ i, |p i|) * X :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hX0
  rw [abs_mul]
  calc |∑ i, p i * x i| * |∑ j, q j * x j|
      ≤ ((∑ i, |p i|) * X) * ((∑ j, |q j|) * X) :=
        mul_le_mul (hbound p) (hbound q) (abs_nonneg _) hp_nn
    _ = X ^ 2 * ((∑ i, |p i|) * (∑ j, |q j|)) := by ring

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The product of two multi-input affine ideals decomposes into its linearization plus the
bilinear residual `(∑ pcᵢxᵢ)(∑ qcⱼxⱼ)`. Pure algebra. -/
theorem mul_decomp (pc qc px : Fin n → R) (pc0 qc0 : R) :
    (pc0 + ∑ i, pc i * px i) * (qc0 + ∑ i, qc i * px i)
      = (pc0 * qc0 + ∑ i, (pc0 * qc i + qc0 * pc i) * px i)
        + (∑ i, pc i * px i) * (∑ i, qc i * px i) := by
  have hsum : (∑ i, (pc0 * qc i + qc0 * pc i) * px i)
      = pc0 * (∑ i, qc i * px i) + qc0 * (∑ i, pc i * px i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]; ring

/-! ## Multi-input multiplication: `×` linearizes and absorbs the bilinear leak

The vector analogue of `AffineForm.mul`. The result ideal is the *linearization* of the product;
the bilinear cross terms are absorbed into `err` (bounded via `mul_nonlinearity_bound` over the
input box `|xᵢ| ≤ X`). `×` closes only by importing the input bound — the reduced product. -/

section ComposeMul
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Multi-input affine multiplication.** Over inputs bounded by `|xᵢ| ≤ X`, the product of two
forms is the affine form whose ideal is the *linearization* `p.c0·q.c0 + ∑ᵢ (p.c0·qᵢ + q.c0·pᵢ)·xᵢ`
of the true product; `err` absorbs the FP rounding, the propagated input error, and the bilinear
leak `X²·(∑|pᵢ|)(∑|qᵢ|)`. -/
def mul (p q : AffineFormVec R n) (hx : p.x = q.x) (X : R)
    (hX : ∀ i, |p.x i| ≤ X) (hX0 : 0 ≤ X)
    (hprod_ne : (p.fp.toVal : R) * q.fp.toVal ≠ 0)
    (hfin : (p.fp * q.fp).isFinite) : AffineFormVec R n where
  fp := (p.fp * q.fp).toFiniteOr0
  c := fun i => p.c0 * q.c i + q.c0 * p.c i
  c0 := p.c0 * q.c0
  x := p.x
  err := (η * |p.value * q.value|
            + (1 + η) * (|p.value| * q.err + p.err * |q.value| + p.err * q.err)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ))
          + X ^ 2 * ((∑ i, |p.c i|) * (∑ i, |q.c i|))
  herr := by
    have hb := fpMulFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hqv : q.value = q.c0 + ∑ i, q.c i * p.x i := by simp only [value]; rw [← hx]
    have hPQ : p.value * q.value
        = (p.c0 * q.c0 + ∑ i, (p.c0 * q.c i + q.c0 * p.c i) * p.x i)
          + (∑ i, p.c i * p.x i) * (∑ i, q.c i * p.x i) := by
      rw [show p.value = p.c0 + ∑ i, p.c i * p.x i from rfl, hqv]
      exact mul_decomp p.c q.c p.x p.c0 q.c0
    have hnonlin : |p.value * q.value
          - (p.c0 * q.c0 + ∑ i, (p.c0 * q.c i + q.c0 * p.c i) * p.x i)|
        ≤ X ^ 2 * ((∑ i, |p.c i|) * (∑ i, |q.c i|)) := by
      rw [show p.value * q.value - (p.c0 * q.c0 + ∑ i, (p.c0 * q.c i + q.c0 * p.c i) * p.x i)
            = (∑ i, p.c i * p.x i) * (∑ i, q.c i * p.x i) from by rw [hPQ]; ring]
      exact mul_nonlinearity_bound p.c q.c p.x X hX hX0
    calc |((p.fp * q.fp).toFiniteOr0.toVal : R)
            - (p.c0 * q.c0 + ∑ i, (p.c0 * q.c i + q.c0 * p.c i) * p.x i)|
        ≤ |((p.fp * q.fp).toFiniteOr0.toVal : R) - p.value * q.value|
            + |p.value * q.value
                - (p.c0 * q.c0 + ∑ i, (p.c0 * q.c i + q.c0 * p.c i) * p.x i)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hb hnonlin

@[simp] theorem mul_c (p q : AffineFormVec R n) (hx X hX hX0 hprod_ne hfin) :
    (p.mul q hx X hX hX0 hprod_ne hfin).c = fun i => p.c0 * q.c i + q.c0 * p.c i := rfl
@[simp] theorem mul_c0 (p q : AffineFormVec R n) (hx X hX hX0 hprod_ne hfin) :
    (p.mul q hx X hX hX0 hprod_ne hfin).c0 = p.c0 * q.c0 := rfl
@[simp] theorem mul_x (p q : AffineFormVec R n) (hx X hX hX0 hprod_ne hfin) :
    (p.mul q hx X hX hX0 hprod_ne hfin).x = p.x := rfl

/-- The product form's ideal is the *linearization* `p.c0·q.c0 + ∑ᵢ (p.c0·qᵢ + q.c0·pᵢ)·xᵢ`. -/
@[simp] theorem mul_value (p q : AffineFormVec R n) (hx X hX hX0 hprod_ne hfin) :
    (p.mul q hx X hX hX0 hprod_ne hfin).value
      = p.c0 * q.c0 + ∑ i, (p.c0 * q.c i + q.c0 * p.c i) * p.x i := by
  simp only [value, mul_c, mul_c0, mul_x]

end ComposeMul

end AffineFormVec
