import Flean.Operations.AffineFormVec

/-! # The linear region as an input *set* — affine-arithmetic range bounds over a box

So far a "region" has meant a single input point (the activation determined by one float's sign).
The genuinely useful interpretability statement is over a *set* of inputs: **for this whole box of
inputs, the ReLU neuron is the affine map `g(x) = c₀ + ∑ cᵢxᵢ`.** That is the classical *linear
region* of a ReLU network, and it is fundamentally a property of the affine **ideal** — separable
from floating point — so it is proved cleanly here by the standard affine-arithmetic range bound.

Over a box `|xᵢ − centerᵢ| ≤ radᵢ`, the affine function deviates from its center value by at most
`∑ |cᵢ|·radᵢ` (`affine_box_bound`). So if the center value exceeds that radius, the function is
**uniformly positive** over the whole box (`affine_box_pos`), the ReLU is uniformly the identity,
and the neuron equals its affine map *everywhere on the box* (`relu_affine_on_box`). The box is the
certified linear region. `AffineFormVec.value_pos_of_box` connects this to a form whose carried
input lies in such a box.

This is the affine ⋈ interval reduced product: the affine domain (the coefficients) meets an
interval domain on the inputs (the box) to certify a region rather than a point.
-/

open Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

variable {n : ℕ}

/-- **Affine-arithmetic range bound.** Over a box `|xᵢ − centerᵢ| ≤ radᵢ`, an affine function
deviates from its center value by at most `∑ |cᵢ|·radᵢ`. -/
theorem affine_box_bound (c center rad x : Fin n → R) (c0 : R)
    (hx : ∀ i, |x i - center i| ≤ rad i) :
    |(c0 + ∑ i, c i * x i) - (c0 + ∑ i, c i * center i)| ≤ ∑ i, |c i| * rad i := by
  have hr : (c0 + ∑ i, c i * x i) - (c0 + ∑ i, c i * center i) = ∑ i, c i * (x i - center i) := by
    have hd : (∑ i, c i * (x i - center i)) = (∑ i, c i * x i) - ∑ i, c i * center i := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hd]; ring
  rw [hr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)

/-- **Uniform positivity over the box.** If the affine value at the box center exceeds the box
radius bound `∑|cᵢ|·radᵢ`, the function is positive at *every* point of the box. The certified
linear region as an input set. -/
theorem affine_box_pos (c center rad x : Fin n → R) (c0 : R)
    (hx : ∀ i, |x i - center i| ≤ rad i)
    (hcenter : (∑ i, |c i| * rad i) < c0 + ∑ i, c i * center i) :
    0 < c0 + ∑ i, c i * x i := by
  have hb := abs_le.mp (affine_box_bound c center rad x c0 hx)
  linarith [hb.1]

/-- **The ReLU is its affine map over the whole box.** Where the affine pre-activation is uniformly
positive, `max 0 g = g` for every input in the box — the neuron *is* the affine map `g(x) = c₀ +
∑ cᵢxᵢ` throughout the certified linear region. -/
theorem relu_affine_on_box (c center rad : Fin n → R) (c0 : R)
    (hcenter : (∑ i, |c i| * rad i) < c0 + ∑ i, c i * center i) (x : Fin n → R)
    (hx : ∀ i, |x i - center i| ≤ rad i) :
    max 0 (c0 + ∑ i, c i * x i) = c0 + ∑ i, c i * x i :=
  max_eq_right (affine_box_pos c center rad x c0 hx hcenter).le

namespace AffineFormVec

variable [FloatFormat]

/-- A form whose carried input lies in a box where its affine ideal is uniformly positive has
positive value — the bridge from the box region to the form. -/
theorem value_pos_of_box (p : AffineFormVec R n) (center rad : Fin n → R)
    (hx : ∀ i, |p.x i - center i| ≤ rad i)
    (hcenter : (∑ i, |p.c i| * rad i) < p.c0 + ∑ i, p.c i * center i) :
    0 < p.value :=
  affine_box_pos p.c center rad p.x p.c0 hx hcenter

/-- Lower bound on the form's value from the box: `value ≥ (center value) − (radius bound)`. -/
theorem value_ge_of_box (p : AffineFormVec R n) (center rad : Fin n → R)
    (hx : ∀ i, |p.x i - center i| ≤ rad i) :
    (p.c0 + ∑ i, p.c i * center i) - (∑ i, |p.c i| * rad i) ≤ p.value := by
  have hb := abs_le.mp (affine_box_bound p.c center rad p.x p.c0 hx)
  show (p.c0 + ∑ i, p.c i * center i) - (∑ i, |p.c i| * rad i) ≤ p.c0 + ∑ i, p.c i * p.x i
  linarith [hb.1]

/-- The positive-value certificate lifts to the float's sign bit (positive value ⇒ sign clear). -/
theorem fp_s_false_of_err_lt_value (p : AffineFormVec R n) (h : p.err < p.value) :
    p.fp.s = false := by
  have hpos : (0 : R) < p.fp.toVal := by
    have habs := abs_le.mp p.abs_toVal_sub_value_le
    linarith [habs.1]
  exact (FiniteFp.toVal_pos_iff.mpr hpos).1

/-- **Robust certified linear region (FP-aware).** If the affine ideal at the box center exceeds
the box radius bound by *more than the form's error*, the FP pre-activation's sign bit is clear over
the carried input — so ReLU is the identity and the neuron tracks its affine map, accounting for
both the input box and the floating-point noise. The fully certified linear region. -/
theorem fp_s_false_of_box (p : AffineFormVec R n) (center rad : Fin n → R)
    (hx : ∀ i, |p.x i - center i| ≤ rad i)
    (hmargin : p.err + (∑ i, |p.c i| * rad i) < p.c0 + ∑ i, p.c i * center i) :
    p.fp.s = false :=
  p.fp_s_false_of_err_lt_value (by linarith [p.value_ge_of_box center rad hx])

end AffineFormVec
