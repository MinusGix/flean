import Flean.Operations.AffineFormVec
import Flean.Operations.AffineNet
import Flean.Operations.FpDotProduct

/-! # Building an affine form from a real layer computation — grounding the multi-input domain

`AffineFormVec` is the affine shadow of `c₀ + ∑ cᵢ·xᵢ`. So far it has been *synthetic* — built by
`ofExact`/`add`/`scaleConst`. This file connects it to an **actual floating-point linear layer**:
the existing `FpDotProductBound` already proves a computed FP dot product `fl(⟨w, x⟩)` is within a
tracked error of the *true* real dot product `∑ wᵢ·xᵢ`. That bound *is* the `AffineFormVec`
invariant with the weights as coefficients and the inputs as the noise symbols.

So `ofDotProductBound` reads an `FpDotProductBound` off as an `AffineFormVec` (the linear part), and
`neuron` adds the bias (one FP add) to get a full pre-activation `⟨w, x⟩ + b` as an affine form
over the inputs. This is the multi-input affine domain *populated from a real computation* rather
than asserted — the entry point for analyzing an actual `Σ wᵢxᵢ + b` layer in the affine regime
(and then feeding it through `AffineRelu`/`AffineNet`).
-/

open FpDotProduct

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

namespace AffineFormVec

variable {n : ℕ}

section OfLayer
variable [FloorRing R]

/-- **Read a computed FP dot product as an affine form.** Weights `w` become the coefficients,
inputs `x` become the noise symbols, and the dot-product error becomes the form's `err`. The ideal
is the *true* real dot product `∑ wᵢ·xᵢ` (constant term `0` — the linear part). -/
def ofDotProductBound (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) : AffineFormVec R n where
  fp := db.result
  c := fun i => ((w i).toVal : R)
  c0 := 0
  x := fun i => ((x i).toVal : R)
  err := db.relErr * ∑ i, |((w i).toVal : R) * ((x i).toVal : R)|
  herr := by simpa using db.h_bound

@[simp] theorem ofDotProductBound_fp (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) :
    (ofDotProductBound w x db).fp = db.result := rfl
@[simp] theorem ofDotProductBound_c (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) :
    (ofDotProductBound w x db).c = fun i => ((w i).toVal : R) := rfl
@[simp] theorem ofDotProductBound_c0 (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) :
    (ofDotProductBound w x db).c0 = 0 := rfl
@[simp] theorem ofDotProductBound_x (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) :
    (ofDotProductBound w x db).x = fun i => ((x i).toVal : R) := rfl

/-- The constructed form's ideal is the *true* real dot product `∑ wᵢ·xᵢ`. -/
@[simp] theorem ofDotProductBound_value (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) :
    (ofDotProductBound w x db).value = ∑ i, ((w i).toVal : R) * ((x i).toVal : R) := by
  simp [AffineFormVec.value, ofDotProductBound]

end OfLayer

section Neuron
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **A full pre-activation `⟨w, x⟩ + b` as an affine form.** Reads the FP dot product as an affine
form (`ofDotProductBound`) and adds the bias by one FP add. The ideal is `(∑ wᵢxᵢ) + b` — a
neuron's pre-activation, affine in the inputs, built from the real layer computation. -/
def neuron (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) (b : FiniteFp)
    (hsum_ne : (db.result.toVal : R) + b.toVal ≠ 0)
    (hfin : (db.result + b).isFinite) : AffineFormVec R n :=
  (ofDotProductBound w x db).addConst b hsum_ne hfin

/-- The neuron's ideal is `(∑ wᵢxᵢ) + b` — affine in the inputs, the true pre-activation. -/
@[simp] theorem neuron_value (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) (b : FiniteFp)
    (hsum_ne : (db.result.toVal : R) + b.toVal ≠ 0) (hfin : (db.result + b).isFinite) :
    (neuron w x db b hsum_ne hfin).value
      = (∑ i, ((w i).toVal : R) * ((x i).toVal : R)) + (b.toVal : R) := by
  rw [neuron, AffineFormVec.addConst_value, ofDotProductBound_value]

end Neuron

/-! ## Multi-input ReLU: the layer-plus-activation stays affine in the inputs (within a region)

ReLU acts on the single output float of a form, independent of how many inputs it has. So the
scalar region story lifts verbatim: in the active region (output sign bit clear) ReLU is the
identity, and the neuron's output is still affine in the inputs. This is "a `⟨w,x⟩+b` layer
followed by ReLU is, on its activation region, the affine map `⟨w,·⟩+b` of the inputs." -/

/-- ReLU in the active region (output ≥ 0) preserves the multi-input affine form unchanged. -/
def reluActive (z : AffineFormVec R n) (hs : z.fp.s = false) : AffineFormVec R n where
  fp := (Fp.fpRelu (Fp.finite z.fp)).toFiniteOr0
  c := z.c
  c0 := z.c0
  x := z.x
  err := z.err
  herr := by
    have h : Fp.fpRelu (Fp.finite z.fp) = Fp.finite z.fp := by rw [Fp.fpRelu_finite_eq, hs]; simp
    rw [h, Fp.toFiniteOr0_finite]; exact z.herr

@[simp] theorem reluActive_c (z : AffineFormVec R n) (hs) : (z.reluActive hs).c = z.c := rfl
@[simp] theorem reluActive_c0 (z : AffineFormVec R n) (hs) : (z.reluActive hs).c0 = z.c0 := rfl
@[simp] theorem reluActive_x (z : AffineFormVec R n) (hs) : (z.reluActive hs).x = z.x := rfl
@[simp] theorem reluActive_err (z : AffineFormVec R n) (hs) : (z.reluActive hs).err = z.err := rfl

/-- ReLU is the identity on the shadow in the active region — the layer-plus-activation has the
same affine ideal in the inputs. -/
@[simp] theorem reluActive_value (z : AffineFormVec R n) (hs) :
    (z.reluActive hs).value = z.value := by
  simp only [AffineFormVec.value, reluActive_c, reluActive_c0, reluActive_x]

section NeuronRelu
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **The layer-plus-activation, end to end.** A `⟨w,x⟩+b` neuron built from the real FP dot
product, followed by ReLU in its active region, has ideal `(∑ wᵢxᵢ) + b` — the affine map of the
inputs, recovered from the actual computation. -/
theorem neuron_relu_value (w x : Fin n → FiniteFp) (db : FpDotProductBound w x R) (b : FiniteFp)
    (hsum_ne : (db.result.toVal : R) + b.toVal ≠ 0) (hfin : (db.result + b).isFinite)
    (hactive : (neuron w x db b hsum_ne hfin).fp.s = false) :
    ((neuron w x db b hsum_ne hfin).reluActive hactive).value
      = (∑ i, ((w i).toVal : R) * ((x i).toVal : R)) + (b.toVal : R) := by
  rw [reluActive_value, neuron_value]

end NeuronRelu

end AffineFormVec
