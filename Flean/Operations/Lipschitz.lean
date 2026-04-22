import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `LipschitzMax` Framework (M2)

A foundational notion of Lipschitz continuity tailored to forward-error
analyses on vector-valued functions.  Designed in conjunction with
the floating-point error analyses in `Flean/Operations/MLP.lean` and
companions, but self-contained: this file only depends on Mathlib
arithmetic, no `FloatFormat` or rounding-mode infrastructure.

## The notion

`LipschitzMax K f` for `f : (Fin m → R) → Fin n → R` asserts:

```
∀ δ x x', (∀ j, |x j − x' j| ≤ δ) → ∀ i, |f x i − f x' i| ≤ K · δ
```

i.e. *every output index* changes by at most `K · δ` when *every
input index* perturbs by at most `δ`.  The L∞→L∞ operator-norm
Lipschitz statement, but stated per-output-coordinate (which fits
forward-error analyses verbatim).

Strictly weaker than the sup-norm Lipschitz `max_i |f x i − f x' i|
≤ K · max_j |x j − x' j|`, but composes the same way.

## Why a custom shape over Mathlib's `LipschitzWith`?

Mathlib's `LipschitzWith K f` from `EMetric` is `∀ x y, edist (f x)
(f y) ≤ K * edist x y`, which would require `PiLp ⊤` instances on
`Fin n → R` and an `ℝ≥0∞`-valued constant.  Functional but heavy
for our use case.  See the spike findings in this file's git
history (`5836db0`).

A `LipschitzMax → LipschitzWith` bridge could be added later for
users who want Mathlib API; not load-bearing for our forward-error
analyses.

## Where Lipschitz fits, and where it doesn't

The framework is for **R-valued** functions (like `Layer.forward`).
The composition is for forward-error analyses where we propagate a
δ-perturbation on the input through layers of math.

What this is **not** for: per-FP-op "Lipschitz" statements about
rounding.  Rounding isn't continuous (discontinuities at midpoints),
so `fpAdd`, `fpMul` etc. aren't Lipschitz in the usual sense.  Their
behavior is captured by the existing `round_preserves_*` family
(absolute / relative error bounds).

## Scalar variant

`LipschitzScalar K f` for `f : R → R` is the per-element companion,
intended for scalar activations (M10).  Composition rules connect
the two: a scalar function applied component-wise to a vector
function preserves `LipschitzMax` with the product of constants.
-/

set_option autoImplicit false

namespace Flean.Lipschitz

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Vector → vector Lipschitz -/

/-- Per-output Lipschitz constant of a multivariate vector function. -/
def LipschitzMax {m n : ℕ} (K : R) (f : (Fin m → R) → Fin n → R) : Prop :=
  ∀ {δ : R} (x x' : Fin m → R), (∀ j, |x j - x' j| ≤ δ) →
    ∀ i, |f x i - f x' i| ≤ K * δ

/-- Identity vector function is `1`-Lipschitz. -/
theorem LipschitzMax.id_id {n : ℕ} : LipschitzMax (R := R) 1 (fun (x : Fin n → R) => x) := by
  intro δ x x' h_dx i
  simp
  linarith [h_dx i]

/-- A constant function (output is the same vector regardless of input)
is `0`-Lipschitz. -/
theorem LipschitzMax.const {m n : ℕ} (c : Fin n → R) :
    LipschitzMax (R := R) 0 (fun (_ : Fin m → R) => c) := by
  intro δ x x' h_dx i
  simp

/-- Relaxing the constant preserves the Lipschitz property, when the
input vector is nonempty (so `0 ≤ δ` is forced by the hypothesis). -/
theorem LipschitzMax.weaken {m n : ℕ} {K K' : R}
    {f : (Fin m → R) → Fin n → R}
    (hf : LipschitzMax (R := R) K f) (hKK : K ≤ K') (hm : 0 < m) :
    LipschitzMax (R := R) K' f := by
  intro δ x x' h_dx i
  have h_orig := hf x x' h_dx i
  have hδ_nn : 0 ≤ δ := le_trans (abs_nonneg _) (h_dx ⟨0, hm⟩)
  have : K * δ ≤ K' * δ := mul_le_mul_of_nonneg_right hKK hδ_nn
  linarith

/-- Composition: `g ∘ f` is `(K_g · K_f)`-Lipschitz. -/
theorem LipschitzMax.comp {m k n : ℕ} {K_f K_g : R}
    {f : (Fin m → R) → Fin k → R} {g : (Fin k → R) → Fin n → R}
    (hg : LipschitzMax (R := R) K_g g)
    (hf : LipschitzMax (R := R) K_f f)
    (hK_g_nn : 0 ≤ K_g) :
    LipschitzMax (R := R) (K_g * K_f) (fun x => g (f x)) := by
  intro δ x x' h_dx i
  have h_fperturb : ∀ j, |f x j - f x' j| ≤ K_f * δ := fun j => hf x x' h_dx j
  have := hg (f x) (f x') h_fperturb i
  calc |g (f x) i - g (f x') i| ≤ K_g * (K_f * δ) := this
    _ = K_g * K_f * δ := by ring

/-! ## Scalar Lipschitz (for activations, M10) -/

/-- Lipschitz constant of a scalar function `R → R`.  Symmetric form:
`|f a - f b| ≤ K · |a - b|`. -/
def LipschitzScalar (K : R) (f : R → R) : Prop :=
  ∀ a b : R, |f a - f b| ≤ K * |a - b|

/-- Identity scalar function is `1`-Lipschitz. -/
theorem LipschitzScalar.id : LipschitzScalar (R := R) 1 (fun (x : R) => x) := by
  intro a b
  simp

/-- Constant scalar function is `0`-Lipschitz. -/
theorem LipschitzScalar.const (c : R) : LipschitzScalar (R := R) 0 (fun (_ : R) => c) := by
  intro a b
  simp

/-- Composition of scalar Lipschitz functions. -/
theorem LipschitzScalar.comp {K_f K_g : R} {f g : R → R}
    (hg : LipschitzScalar (R := R) K_g g)
    (hf : LipschitzScalar (R := R) K_f f)
    (hK_g_nn : 0 ≤ K_g) :
    LipschitzScalar (R := R) (K_g * K_f) (fun x => g (f x)) := by
  intro a b
  calc |g (f a) - g (f b)| ≤ K_g * |f a - f b| := hg (f a) (f b)
    _ ≤ K_g * (K_f * |a - b|) := mul_le_mul_of_nonneg_left (hf a b) hK_g_nn
    _ = K_g * K_f * |a - b| := by ring

/-! ## Cross-composition: scalar ∘ vector

Applying a scalar Lipschitz function pointwise to a vector function
preserves `LipschitzMax`.  The composition rule is the product of
constants — exactly what you'd expect for activations on top of a
linear layer. -/

/-- A scalar function applied component-wise to a vector function.

If `f : (Fin m → R) → Fin n → R` is `K_f`-`LipschitzMax` and
`σ : R → R` is `K_σ`-`LipschitzScalar`, then `(σ ∘ f)` (applied
component-wise) is `(K_σ · K_f)`-`LipschitzMax`. -/
theorem LipschitzMax.compScalar {m n : ℕ} {K_f K_σ : R}
    {f : (Fin m → R) → Fin n → R} {σ : R → R}
    (hf : LipschitzMax (R := R) K_f f)
    (hσ : LipschitzScalar (R := R) K_σ σ)
    (hK_σ_nn : 0 ≤ K_σ) :
    LipschitzMax (R := R) (K_σ * K_f) (fun x i => σ (f x i)) := by
  intro δ x x' h_dx i
  have h_finner := hf x x' h_dx i
  -- |σ (f x i) - σ (f x' i)| ≤ K_σ · |f x i - f x' i| ≤ K_σ · K_f · δ.
  calc |σ (f x i) - σ (f x' i)|
      ≤ K_σ * |f x i - f x' i| := hσ (f x i) (f x' i)
    _ ≤ K_σ * (K_f * δ) := mul_le_mul_of_nonneg_left h_finner hK_σ_nn
    _ = K_σ * K_f * δ := by ring

end Flean.Lipschitz
