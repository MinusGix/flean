import Flean.Operations.AffineForm
import Flean.IntegerEquivalence.ReluBits

/-! # ReLU linear regions via the affine domain — pointing the machinery at a real ML primitive

Every headline so far has been on synthetic inputs (abstract integers, abstract affine forms). This
file is the first time the reduction apparatus says something true about a thing ML *actually
does*: the **linear regions of a ReLU**.

A ReLU network is piecewise linear; *which* linear piece you are in is fixed by the **sign of each
pre-activation**. That is exactly the discrete/continuous interface the strategic note flagged: the
sign picks the region, and within the region the unit is an honest affine map. We make it precise
by composing two domains we already built — `AffineForm` (the continuous affine shadow) and the
sign of the pre-activation:

* **Active region** (`z.fp.s = false`, pre-activation ≥ 0): ReLU is the **identity**, so the output
  tracks the *same* affine ideal `a·x + b` within the same `err` (`relu_active_tracks`). The unit is
  exactly affine here — and `reluActive` packages the output back as an `AffineForm`, so a downstream
  layer keeps reasoning in the affine domain *across the ReLU*, as long as the region holds.
* **Inactive region** (`z.fp.s = true`, pre-activation < 0): ReLU collapses to exactly `0`
  (`relu_inactive_zero`) — the "off" piece, the zero affine form.

The **kink** is the boundary between the two regions (`z.fp.s` flips). That is *precisely* where the
affine description breaks and the nonlinearity lives — the ReLU analogue of `AffineForm.mul`'s
quadratic leak. Within a region: affine. At the boundary: structure change. This is the faithful
statement of "a ReLU net is piecewise affine," recovered from the FP operator, not assumed.
-/

namespace AffineForm

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## The two regions, at the operator level -/

/-- Active region: a nonneg pre-activation passes through ReLU unchanged. -/
theorem fpRelu_active (z : AffineForm R) (hs : z.fp.s = false) :
    Fp.fpRelu (Fp.finite z.fp) = Fp.finite z.fp := by
  rw [Fp.fpRelu_finite_eq, hs]; simp

/-- Inactive region: a negative pre-activation is zeroed by ReLU. -/
theorem fpRelu_inactive (z : AffineForm R) (hs : z.fp.s = true) :
    Fp.fpRelu (Fp.finite z.fp) = Fp.finite (0 : FiniteFp) := by
  rw [Fp.fpRelu_finite_eq, hs]; simp

/-! ## Affine tracking within each region -/

/-- **Active-region tracking.** Where the pre-activation is nonneg, the ReLU output *is* the
pre-activation, so it tracks the same affine ideal `a·x + b` within `z.err` — the unit is exactly
affine on this linear piece. -/
theorem relu_active_tracks (z : AffineForm R) (hs : z.fp.s = false) :
    |((Fp.fpRelu (Fp.finite z.fp)).toFiniteOr0.toVal : R) - z.value| ≤ z.err := by
  rw [fpRelu_active z hs, Fp.toFiniteOr0_finite]
  exact z.herr

/-- **Inactive-region collapse.** Where the pre-activation is negative, the ReLU output is exactly
`0` — the "off" linear piece. -/
theorem relu_inactive_zero (z : AffineForm R) (hs : z.fp.s = true) :
    ((Fp.fpRelu (Fp.finite z.fp)).toFiniteOr0.toVal : R) = 0 := by
  rw [fpRelu_inactive z hs, Fp.toFiniteOr0_finite, FiniteFp.toVal_zero]

/-! ## Carrying the affine form through the ReLU (active region)

The point of an *abstract domain* is that it composes: the output of one op is an object of the same
kind, ready for the next op. `reluActive` packages the active-region ReLU output back as an
`AffineForm` over the same input `x` with the same ideal `a·x + b` — so a network can be reasoned
about, layer after layer, entirely in the affine domain *for as long as the activation region holds*.
-/

/-- The ReLU output in the active region, as an `AffineForm` for forward composition: it is `z`
unchanged (ReLU = identity here), now with `fp` the actual ReLU output. -/
def reluActive (z : AffineForm R) (hs : z.fp.s = false) : AffineForm R where
  fp := (Fp.fpRelu (Fp.finite z.fp)).toFiniteOr0
  a := z.a
  b := z.b
  x := z.x
  err := z.err
  herr := by rw [fpRelu_active z hs, Fp.toFiniteOr0_finite]; exact z.herr

@[simp] theorem reluActive_a (z : AffineForm R) (hs) : (z.reluActive hs).a = z.a := rfl
@[simp] theorem reluActive_b (z : AffineForm R) (hs) : (z.reluActive hs).b = z.b := rfl
@[simp] theorem reluActive_x (z : AffineForm R) (hs) : (z.reluActive hs).x = z.x := rfl
@[simp] theorem reluActive_err (z : AffineForm R) (hs) : (z.reluActive hs).err = z.err := rfl
@[simp] theorem reluActive_fp (z : AffineForm R) (hs) :
    (z.reluActive hs).fp = (Fp.fpRelu (Fp.finite z.fp)).toFiniteOr0 := rfl

/-- The carried form has the *same* affine ideal — ReLU is the identity on the shadow in the active
region. -/
@[simp] theorem reluActive_value (z : AffineForm R) (hs) : (z.reluActive hs).value = z.value := by
  simp only [AffineForm.value, reluActive_a, reluActive_b, reluActive_x]

/-! ## A *robust* region certificate: the region in terms of the ideal, not the bit pattern

`reluActive` keys on the raw sign bit `z.fp.s`. The honest notion of a *certified* linear region is
in terms of the **ideal**: the activation is determined whenever the affine value is bounded away
from the kink by more than the tracked error. Below that margin the bit pattern could go either way
(the kink); above it, the region is certified despite FP noise. -/

/-- If the affine value exceeds the error margin (`z.err < z.value`), the float pre-activation is
strictly positive, hence its sign bit is clear. The bridge from the ideal-level margin condition to
the bit-level region condition `reluActive` consumes. -/
theorem fp_s_false_of_err_lt_value (z : AffineForm R) (h : z.err < z.value) : z.fp.s = false := by
  have hpos : (0 : R) < z.fp.toVal := by
    have habs := abs_le.mp z.abs_toVal_sub_value_le
    linarith [habs.1]
  exact (FiniteFp.toVal_pos_iff.mpr hpos).1

/-- **Certified active region.** ReLU is provably the identity whenever the affine ideal clears the
error margin (`z.err < z.value`) — the activation region stated in terms of the ideal, robust to
floating-point noise. Returns the carried form (same ideal `a·x + b`). -/
def reluActiveOfValue (z : AffineForm R) (h : z.err < z.value) : AffineForm R :=
  z.reluActive (z.fp_s_false_of_err_lt_value h)

@[simp] theorem reluActiveOfValue_value (z : AffineForm R) (h : z.err < z.value) :
    (z.reluActiveOfValue h).value = z.value :=
  reluActive_value z _

@[simp] theorem reluActiveOfValue_fp (z : AffineForm R) (h : z.err < z.value) :
    (z.reluActiveOfValue h).fp = (Fp.fpRelu (Fp.finite z.fp)).toFiniteOr0 := rfl

end AffineForm
