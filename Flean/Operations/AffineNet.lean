import Flean.Operations.AffineRelu

/-! # Affine maps and multi-layer composition — a network-in-a-region *is* a single affine map

`AffineForm` + `AffineRelu` gave the pieces: an affine shadow, and ReLU as exactly-affine within a
fixed activation region. This file assembles them into the headline of the whole thread: **a
(scalar) ReLU network, restricted to one activation region, reduces to a single affine map of its
input**, with a tracked floating-point error — the literal "this region of the net is the affine
map `A·x + b`" statement the reductionist vision is after.

The building blocks are the affine-map primitives a linear layer is made of:
* `ofConst` — a constant (a weight/bias), as a degree-0 affine form;
* `scaleConst` — multiply a form by a constant float `w` (a weight). Affine stays affine with **no
  quadratic leak** (the other factor has slope 0), so — unlike `mul` — *no input bound `X` is
  needed*. Ideal `↦ w · (a·x+b)`;
* `addConst` — add a constant float `c` (a bias). Ideal `↦ (a·x+b) + c`;
* `affineMap p w c` — the composite `y ↦ w·y + c`, the scalar form of one neuron's pre-activation
  map. Ideal `↦ w·value + c`.

Composing `affineMap → reluActive → affineMap` and reading off `.value` gives a single affine map
in the input (`two_layer_affine_in_region`). The result is exact on the *shadow* (the ideal is a
genuine affine function of the input); all the floating-point cost lives in the tracked `err`.
-/

namespace AffineForm

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A constant `f.toVal` as a degree-0 affine form over input `x` (slope 0). Models a weight or
bias entering a layer. -/
def ofConst (f : FiniteFp) (x : R) : AffineForm R :=
  ⟨f, 0, (f.toVal : R), x, 0, by simp⟩

@[simp] theorem ofConst_fp (f : FiniteFp) (x : R) : (ofConst f x).fp = f := rfl
@[simp] theorem ofConst_a (f : FiniteFp) (x : R) : (ofConst f x).a = 0 := rfl
@[simp] theorem ofConst_b (f : FiniteFp) (x : R) : (ofConst f x).b = (f.toVal : R) := rfl
@[simp] theorem ofConst_x (f : FiniteFp) (x : R) : (ofConst f x).x = x := rfl
@[simp] theorem ofConst_value (f : FiniteFp) (x : R) : (ofConst f x).value = (f.toVal : R) := by
  simp [AffineForm.value]

section Compose
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Scale by a constant float `w`** (a weight). The product of an affine form with a constant is
affine with **no quadratic leak** — so this needs no input bound `X`, unlike `mul`. Ideal becomes
`w · (a·x + b)`; the error grows only by the FP multiplication. -/
def scaleConst (p : AffineForm R) (w : FiniteFp)
    (hprod_ne : (p.fp.toVal : R) * w.toVal ≠ 0)
    (hfin : (p.fp * w).isFinite) : AffineForm R where
  fp := (p.fp * w).toFiniteOr0
  a := p.a * (w.toVal : R)
  b := p.b * (w.toVal : R)
  x := p.x
  err := η * |p.value * (w.toVal : R)|
          + (1 + η) * (p.err * |(w.toVal : R)|)
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb0 : |(w.toVal : R) - (w.toVal : R)| ≤ 0 := by simp
    have hmul := fpMulFinite_inexact_general p.fp w (p.a * p.x + p.b) (w.toVal : R) p.err 0 _
      p.herr hb0 hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hideal : (p.a * (w.toVal : R)) * p.x + p.b * (w.toVal : R)
        = (p.a * p.x + p.b) * (w.toVal : R) := by ring
    calc |((p.fp * w).toFiniteOr0.toVal : R) - ((p.a * (w.toVal : R)) * p.x + p.b * (w.toVal : R))|
        = |((p.fp * w).toFiniteOr0.toVal : R) - (p.a * p.x + p.b) * (w.toVal : R)| := by rw [hideal]
      _ ≤ η * |(p.a * p.x + p.b) * (w.toVal : R)|
            + (1 + η) * (|p.a * p.x + p.b| * 0 + p.err * |(w.toVal : R)| + p.err * 0)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := hmul
      _ = η * |p.value * (w.toVal : R)| + (1 + η) * (p.err * |(w.toVal : R)|)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
          rw [show p.value = p.a * p.x + p.b from rfl]; ring

@[simp] theorem scaleConst_a (p : AffineForm R) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).a = p.a * (w.toVal : R) := rfl
@[simp] theorem scaleConst_b (p : AffineForm R) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).b = p.b * (w.toVal : R) := rfl
@[simp] theorem scaleConst_x (p : AffineForm R) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).x = p.x := rfl
@[simp] theorem scaleConst_fp (p : AffineForm R) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).fp = (p.fp * w).toFiniteOr0 := rfl

/-- Scaling multiplies the ideal by the constant — affine, no leak. -/
@[simp] theorem scaleConst_value (p : AffineForm R) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).value = p.value * (w.toVal : R) := by
  simp only [AffineForm.value, scaleConst_a, scaleConst_b, scaleConst_x]; ring

/-- **Add a constant float `c`** (a bias), as `add` against a constant form. Ideal becomes
`(a·x + b) + c`. -/
def addConst (p : AffineForm R) (c : FiniteFp)
    (hsum_ne : (p.fp.toVal : R) + c.toVal ≠ 0)
    (hfin : (p.fp + c).isFinite) : AffineForm R :=
  p.add (ofConst c p.x) rfl hsum_ne hfin

@[simp] theorem addConst_value (p : AffineForm R) (c : FiniteFp)
    (hsum_ne : (p.fp.toVal : R) + c.toVal ≠ 0) (hfin : (p.fp + c).isFinite) :
    (p.addConst c hsum_ne hfin).value = p.value + (c.toVal : R) := by
  rw [addConst, AffineForm.add_value, ofConst_value]

/-- **One neuron's pre-activation map** `y ↦ w·y + c`: scale by weight `w`, add bias `c`. The
scalar shape of a linear layer's contribution. Ideal becomes `w·value + c`. -/
def affineMap (p : AffineForm R) (w c : FiniteFp)
    (hprod_ne : (p.fp.toVal : R) * w.toVal ≠ 0)
    (hfin_mul : (p.fp * w).isFinite)
    (hsum_ne : ((p.scaleConst w hprod_ne hfin_mul).fp.toVal : R) + c.toVal ≠ 0)
    (hfin_add : ((p.scaleConst w hprod_ne hfin_mul).fp + c).isFinite) : AffineForm R :=
  (p.scaleConst w hprod_ne hfin_mul).addConst c hsum_ne hfin_add

@[simp] theorem affineMap_value (p : AffineForm R) (w c : FiniteFp)
    (hprod_ne hfin_mul hsum_ne hfin_add) :
    (p.affineMap w c hprod_ne hfin_mul hsum_ne hfin_add).value
      = p.value * (w.toVal : R) + (c.toVal : R) := by
  rw [affineMap, addConst_value, scaleConst_value]

/-! ## Multi-layer composition: a network-in-a-region is a single affine map

The composition law. Applying a second affine map *after* a ReLU, in the ReLU's active region,
yields a form whose ideal is `z₁.value · w₂ + b₂` — affine in the pre-activation `z₁`, because
ReLU is the identity there. Chaining this is what makes a multi-layer network collapse, region by
region, to one affine map. -/

/-- **The region composition law.** A second affine layer after a ReLU (active region) composes to
an affine map in the first layer's pre-activation value. -/
theorem affineMap_reluActive_value (z₁ : AffineForm R) (hactive : z₁.fp.s = false)
    (w₂ b₂ : FiniteFp) (h2pne h2mfin h2sne h2afin) :
    ((z₁.reluActive hactive).affineMap w₂ b₂ h2pne h2mfin h2sne h2afin).value
      = z₁.value * (w₂.toVal : R) + (b₂.toVal : R) := by
  rw [affineMap_value, reluActive_value]

/-- **Capstone: a two-layer scalar ReLU network, restricted to one activation region, *is* a
single affine map of its input** — `value = input.value · (w₁·w₂) + (b₁·w₂ + b₂)`. The ideal is a
genuine affine function of the input; the entire floating-point cost is carried in the form's
`err`. This is "this region of the net is the affine map `A·x + b`", recovered end to end from the
FP operations. -/
theorem two_layer_affine_in_region (input : AffineForm R) (w₁ b₁ w₂ b₂ : FiniteFp)
    (h1pne : (input.fp.toVal : R) * w₁.toVal ≠ 0)
    (h1mfin : (input.fp * w₁).isFinite)
    (h1sne : ((input.scaleConst w₁ h1pne h1mfin).fp.toVal : R) + b₁.toVal ≠ 0)
    (h1afin : ((input.scaleConst w₁ h1pne h1mfin).fp + b₁).isFinite)
    (hactive : (input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).fp.s = false)
    (h2pne h2mfin h2sne h2afin) :
    (((input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).reluActive hactive).affineMap
        w₂ b₂ h2pne h2mfin h2sne h2afin).value
      = input.value * (w₁.toVal : R) * (w₂.toVal : R)
        + ((b₁.toVal : R) * (w₂.toVal : R) + (b₂.toVal : R)) := by
  rw [affineMap_reluActive_value, affineMap_value]; ring

/-- **The verified local linear region, with error.** The actual floating-point output of the
two-layer network is within the form's `err` of the single affine map `A·x + b`
(`A = w₁·w₂`, `b = b₁·w₂ + b₂`). Together with `two_layer_affine_in_region` (which identifies the
ideal as that affine map) this is a complete certificate: in this activation region the net *is*
the affine map `A·x + b`, up to a tracked `err`. -/
theorem two_layer_error_bound (input : AffineForm R) (w₁ b₁ w₂ b₂ : FiniteFp)
    (h1pne : (input.fp.toVal : R) * w₁.toVal ≠ 0)
    (h1mfin : (input.fp * w₁).isFinite)
    (h1sne : ((input.scaleConst w₁ h1pne h1mfin).fp.toVal : R) + b₁.toVal ≠ 0)
    (h1afin : ((input.scaleConst w₁ h1pne h1mfin).fp + b₁).isFinite)
    (hactive : (input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).fp.s = false)
    (h2pne h2mfin h2sne h2afin) :
    |((((input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).reluActive hactive).affineMap
          w₂ b₂ h2pne h2mfin h2sne h2afin).fp.toVal : R)
        - (input.value * (w₁.toVal : R) * (w₂.toVal : R)
            + ((b₁.toVal : R) * (w₂.toVal : R) + (b₂.toVal : R)))|
      ≤ (((input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).reluActive hactive).affineMap
          w₂ b₂ h2pne h2mfin h2sne h2afin).err := by
  rw [← two_layer_affine_in_region]
  exact AffineForm.abs_toVal_sub_value_le _

/-- **The certified version of the capstone.** Same conclusion as `two_layer_affine_in_region`, but
the activation region is certified by the *interpretable, FP-noise-robust* condition "the layer-1
ideal clears its error margin" (`err < value`) rather than a raw sign bit. This is the form a real
"certified linear region of a ReLU net" theorem should take. -/
theorem two_layer_affine_certified (input : AffineForm R) (w₁ b₁ w₂ b₂ : FiniteFp)
    (h1pne : (input.fp.toVal : R) * w₁.toVal ≠ 0)
    (h1mfin : (input.fp * w₁).isFinite)
    (h1sne : ((input.scaleConst w₁ h1pne h1mfin).fp.toVal : R) + b₁.toVal ≠ 0)
    (h1afin : ((input.scaleConst w₁ h1pne h1mfin).fp + b₁).isFinite)
    (hmargin : (input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).err
               < (input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).value)
    (h2pne h2mfin h2sne h2afin) :
    (((input.affineMap w₁ b₁ h1pne h1mfin h1sne h1afin).reluActiveOfValue hmargin).affineMap
        w₂ b₂ h2pne h2mfin h2sne h2afin).value
      = input.value * (w₁.toVal : R) * (w₂.toVal : R)
        + ((b₁.toVal : R) * (w₂.toVal : R) + (b₂.toVal : R)) := by
  rw [affineMap_value, reluActiveOfValue_value, affineMap_value]; ring

end Compose

end AffineForm
