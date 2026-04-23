import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `LipschitzMax` Framework

A foundational notion of Lipschitz continuity tailored to forward-error
analyses on vector-valued functions.  Designed in conjunction with
the floating-point error analyses in `Flean/Operations/MLP.lean` and
companions, but self-contained: this file only depends on Mathlib
arithmetic, no `FloatFormat` or rounding-mode infrastructure.

## The notions

`LipschitzMax K f` for `f : (Fin m → R) → Fin n → R` asserts:

```
∀ δ x x', (∀ j, |x j − x' j| ≤ δ) → ∀ i, |f x i − f x' i| ≤ K · δ
```

i.e. *every output index* changes by at most `K · δ` when *every
input index* perturbs by at most `δ`.  The L∞→L∞ operator-norm
Lipschitz statement, but stated per-output-coordinate (which fits
forward-error analyses verbatim).

`LipschitzScalar K f` for `f : R → R` is the per-element companion,
intended for scalar activations.

`LipschitzMaxOn M K f` is the **bounded-input** variant: the bound
holds when every input has magnitude at most `M`.  Captures locally-
Lipschitz functions (`x²`, `1/x`, polynomial activations) whose
constant depends on the input range.

`ApproximatesUniformly c f g` is a separate tag asserting `|f x i - g x i| ≤ c`
pointwise.  Combined with `LipschitzMaxOn` via `approximatedBound`,
it gives the "exact-Lipschitz function plus bounded approximation"
shape — useful for Taylor truncations, polynomial activations, and
similar approximated math models.

## Key design decisions

* **`0 ≤ K` is baked into the structure** as `K_nn`.  Composition
  derives this automatically; consumers never have to supply it.
* **Custom shape** chosen over Mathlib's `LipschitzWith`.  Mathlib
  needs `PiLp ⊤` instances and `ℝ≥0∞` constants; we want
  `R`-parametric simplicity.
* **Slack is factored**, not bundled.  Rather than a primitive
  `LipschitzMaxWithSlack` (which conflates two orthogonal concepts),
  we expose `LipschitzMaxOn` (locally-Lipschitz math) and
  `ApproximatesUniformly` (approximation), and combine them via
  `approximatedBound`.

## Where Lipschitz fits, and where it doesn't

The framework is for **R-valued** functions (like `Layer.forward`).
The composition propagates δ-perturbations through layers of math.

Per-FP-op "Lipschitz" statements about rounding aren't directly
expressible (rounding is discontinuous at midpoints).  See
`Flean/Operations/LipschitzFp.lean` for the FP-typed sibling
`LipschitzMaxFpSlackOn` that captures "almost-Lipschitz with
magnitude-dependent rounding slack" on `FiniteFp`-typed inputs.
-/

set_option autoImplicit false

namespace Flean.Lipschitz

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Vector → vector Lipschitz -/

/-- Per-output Lipschitz constant of a multivariate vector function.
The constant `K` is required nonneg (`K_nn`); composition derives this
automatically. -/
structure LipschitzMax {m n : ℕ} (K : R) (f : (Fin m → R) → Fin n → R) :
    Prop where
  /-- Lipschitz constant is non-negative. -/
  K_nn : 0 ≤ K
  /-- The Lipschitz bound itself. -/
  bound : ∀ {δ : R} (x x' : Fin m → R), (∀ j, |x j - x' j| ≤ δ) →
    ∀ i, |f x i - f x' i| ≤ K * δ

/-- Identity vector function is `1`-Lipschitz. -/
theorem LipschitzMax.refl {n : ℕ} :
    LipschitzMax (R := R) 1 (fun (x : Fin n → R) => x) where
  K_nn := zero_le_one
  bound := by
    intro δ x x' h_dx i
    simp
    linarith [h_dx i]

/-- A constant function (output is the same vector regardless of input)
is `0`-Lipschitz. -/
theorem LipschitzMax.const {m n : ℕ} (c : Fin n → R) :
    LipschitzMax (R := R) 0 (fun (_ : Fin m → R) => c) where
  K_nn := le_refl 0
  bound := by
    intro δ x x' h_dx i
    simp

/-- Relaxing the constant preserves the Lipschitz property, when the
input vector is nonempty (so `0 ≤ δ` is forced by the hypothesis). -/
theorem LipschitzMax.weaken {m n : ℕ} {K K' : R}
    {f : (Fin m → R) → Fin n → R}
    (hf : LipschitzMax (R := R) K f) (hKK : K ≤ K') (hm : 0 < m) :
    LipschitzMax (R := R) K' f where
  K_nn := le_trans hf.K_nn hKK
  bound := by
    intro δ x x' h_dx i
    have h_orig := hf.bound x x' h_dx i
    have hδ_nn : 0 ≤ δ := le_trans (abs_nonneg _) (h_dx ⟨0, hm⟩)
    have : K * δ ≤ K' * δ := mul_le_mul_of_nonneg_right hKK hδ_nn
    linarith

/-- Composition: `g ∘ f` is `(K_g · K_f)`-Lipschitz. -/
theorem LipschitzMax.comp {m k n : ℕ} {K_f K_g : R}
    {f : (Fin m → R) → Fin k → R} {g : (Fin k → R) → Fin n → R}
    (hg : LipschitzMax (R := R) K_g g)
    (hf : LipschitzMax (R := R) K_f f) :
    LipschitzMax (R := R) (K_g * K_f) (fun x => g (f x)) where
  K_nn := mul_nonneg hg.K_nn hf.K_nn
  bound := by
    intro δ x x' h_dx i
    have h_fperturb : ∀ j, |f x j - f x' j| ≤ K_f * δ := fun j =>
      hf.bound x x' h_dx j
    have := hg.bound (f x) (f x') h_fperturb i
    calc |g (f x) i - g (f x') i| ≤ K_g * (K_f * δ) := this
      _ = K_g * K_f * δ := by ring

/-! ## Scalar Lipschitz (for activations) -/

/-- Lipschitz constant of a scalar function `R → R`.  Symmetric form:
`|f a - f b| ≤ K · |a - b|`.  The constant `K` is required nonneg. -/
structure LipschitzScalar (K : R) (f : R → R) : Prop where
  /-- Lipschitz constant is non-negative. -/
  K_nn : 0 ≤ K
  /-- The Lipschitz bound itself. -/
  bound : ∀ a b : R, |f a - f b| ≤ K * |a - b|

/-- Identity scalar function is `1`-Lipschitz. -/
theorem LipschitzScalar.refl : LipschitzScalar (R := R) 1 (fun (x : R) => x) where
  K_nn := zero_le_one
  bound := by intro a b; simp

/-- Constant scalar function is `0`-Lipschitz. -/
theorem LipschitzScalar.const (c : R) : LipschitzScalar (R := R) 0 (fun (_ : R) => c) where
  K_nn := le_refl 0
  bound := by intro a b; simp

/-- Composition of scalar Lipschitz functions. -/
theorem LipschitzScalar.comp {K_f K_g : R} {f g : R → R}
    (hg : LipschitzScalar (R := R) K_g g)
    (hf : LipschitzScalar (R := R) K_f f) :
    LipschitzScalar (R := R) (K_g * K_f) (fun x => g (f x)) where
  K_nn := mul_nonneg hg.K_nn hf.K_nn
  bound := by
    intro a b
    calc |g (f a) - g (f b)| ≤ K_g * |f a - f b| := hg.bound (f a) (f b)
      _ ≤ K_g * (K_f * |a - b|) := mul_le_mul_of_nonneg_left (hf.bound a b) hg.K_nn
      _ = K_g * K_f * |a - b| := by ring

/-! ## Cross-composition: scalar ∘ vector

A scalar function applied component-wise to a vector function preserves
`LipschitzMax` with the product of constants.  Exactly what's needed
for activations on top of linear layers. -/

theorem LipschitzMax.compScalar {m n : ℕ} {K_f K_σ : R}
    {f : (Fin m → R) → Fin n → R} {σ : R → R}
    (hf : LipschitzMax (R := R) K_f f)
    (hσ : LipschitzScalar (R := R) K_σ σ) :
    LipschitzMax (R := R) (K_σ * K_f) (fun x i => σ (f x i)) where
  K_nn := mul_nonneg hσ.K_nn hf.K_nn
  bound := by
    intro δ x x' h_dx i
    have h_finner := hf.bound x x' h_dx i
    calc |σ (f x i) - σ (f x' i)|
        ≤ K_σ * |f x i - f x' i| := hσ.bound (f x i) (f x' i)
      _ ≤ K_σ * (K_f * δ) := mul_le_mul_of_nonneg_left h_finner hσ.K_nn
      _ = K_σ * K_f * δ := by ring

/-! ## Bounded-input `LipschitzMaxOn`

Many math functions are only locally Lipschitz: `x²` has constant
`2M` on `|x| ≤ M`, `1/x` has constant `1/a²` on `[a, ∞)`, polynomial
activations have constants depending on the input range.  `LipschitzMaxOn`
captures this — the bound holds when every input is `M`-magnitude-bounded.

Globally Lipschitz functions are `LipschitzMaxOn` for any `M` via
`LipschitzMax.toOn`. -/

/-- Bounded-input variant of `LipschitzMax`: the Lipschitz bound holds
on inputs whose per-component magnitude is at most `M`. -/
structure LipschitzMaxOn {m n : ℕ} (M K : R)
    (f : (Fin m → R) → Fin n → R) : Prop where
  /-- Lipschitz constant is non-negative. -/
  K_nn : 0 ≤ K
  /-- The Lipschitz bound on M-bounded inputs. -/
  bound : ∀ (x x' : Fin m → R),
    (∀ j, |x j| ≤ M) → (∀ j, |x' j| ≤ M) →
    ∀ {δ : R}, (∀ j, |x j - x' j| ≤ δ) →
    ∀ i, |f x i - f x' i| ≤ K * δ

omit [IsStrictOrderedRing R] in
/-- Globally Lipschitz functions are `LipschitzMaxOn` for any bound. -/
theorem LipschitzMax.toOn {m n : ℕ} {K M : R}
    {f : (Fin m → R) → Fin n → R} (hf : LipschitzMax (R := R) K f) :
    LipschitzMaxOn (R := R) M K f where
  K_nn := hf.K_nn
  bound := by
    intro x x' _ _ δ h_dx i
    exact hf.bound x x' h_dx i

/-- Composition of bounded-input Lipschitz functions: requires the
inner function's image to lie within the outer function's M-ball. -/
theorem LipschitzMaxOn.comp {m k n : ℕ} {M_x M_int K_f K_g : R}
    {f : (Fin m → R) → Fin k → R} {g : (Fin k → R) → Fin n → R}
    (hg : LipschitzMaxOn (R := R) M_int K_g g)
    (hf : LipschitzMaxOn (R := R) M_x K_f f)
    (h_image : ∀ x : Fin m → R, (∀ j, |x j| ≤ M_x) → ∀ k, |f x k| ≤ M_int) :
    LipschitzMaxOn (R := R) M_x (K_g * K_f) (fun x => g (f x)) where
  K_nn := mul_nonneg hg.K_nn hf.K_nn
  bound := by
    intro x x' hx_M hx'_M δ h_dx i
    have h_fx_M : ∀ k, |f x k| ≤ M_int := h_image x hx_M
    have h_fx'_M : ∀ k, |f x' k| ≤ M_int := h_image x' hx'_M
    have h_finner : ∀ j, |f x j - f x' j| ≤ K_f * δ :=
      fun j => hf.bound x x' hx_M hx'_M h_dx j
    have h_amp := hg.bound (f x) (f x') h_fx_M h_fx'_M h_finner i
    calc |g (f x) i - g (f x') i|
        ≤ K_g * (K_f * δ) := h_amp
      _ = K_g * K_f * δ := by ring

/-! ## Uniform approximation tag

`ApproximatesUniformly c f g` says `f` and `g` agree up to a uniform
pointwise error `c`.  Used to plug an approximation (e.g., a Taylor
truncation, polynomial activation, lookup table) onto an exact-Lipschitz
math function. -/

/-- Pointwise uniform approximation: `|f x i - g x i| ≤ c` everywhere. -/
structure ApproximatesUniformly {m n : ℕ} (c : R)
    (f g : (Fin m → R) → Fin n → R) : Prop where
  /-- Approximation slack is non-negative. -/
  c_nn : 0 ≤ c
  /-- Pointwise approximation bound. -/
  bound : ∀ (x : Fin m → R) (i : Fin n), |f x i - g x i| ≤ c

omit [IsStrictOrderedRing R] in
/-- Symmetry: `f` approximates `g` iff `g` approximates `f`. -/
theorem ApproximatesUniformly.symm {m n : ℕ} {c : R}
    {f g : (Fin m → R) → Fin n → R}
    (h : ApproximatesUniformly (R := R) c f g) :
    ApproximatesUniformly (R := R) c g f where
  c_nn := h.c_nn
  bound := fun x i => by rw [abs_sub_comm]; exact h.bound x i

/-! ## Approximated bound: combining `LipschitzMaxOn` + `ApproximatesUniformly`

Given an exact-Lipschitz math function `g` and an approximation `f`
within `c`, the perturbation bound for `f` is `K · δ + 2c` on the
M-ball — factor of 2 from triangle on both endpoints. -/

/-- **Approximation slack bound**: an approximation of an exact-
Lipschitz function inherits the Lipschitz bound with `2c` slack. -/
theorem LipschitzMaxOn.approximatedBound {m n : ℕ} {M K c : R}
    {f g : (Fin m → R) → Fin n → R}
    (hg : LipschitzMaxOn (R := R) M K g)
    (happ : ApproximatesUniformly (R := R) c f g)
    {x x' : Fin m → R}
    (hx_M : ∀ j, |x j| ≤ M) (hx'_M : ∀ j, |x' j| ≤ M)
    {δ : R} (h_dx : ∀ j, |x j - x' j| ≤ δ)
    (i : Fin n) :
    |f x i - f x' i| ≤ K * δ + 2 * c := by
  have h_app_x := happ.bound x i
  have h_app_x' := happ.bound x' i
  have h_app_x'_sym : |g x' i - f x' i| ≤ c := by
    rw [abs_sub_comm]; exact h_app_x'
  have h_g_lip := hg.bound x x' hx_M hx'_M h_dx i
  -- |f x i - f x' i| ≤ |f x i - g x i| + |g x i - g x' i| + |g x' i - f x' i|.
  have h_split : f x i - f x' i =
      (f x i - g x i) + (g x i - g x' i) + (g x' i - f x' i) := by ring
  have h_tri : |f x i - f x' i|
      ≤ |f x i - g x i| + |g x i - g x' i| + |g x' i - f x' i| := by
    calc |f x i - f x' i|
        = |(f x i - g x i) + (g x i - g x' i) + (g x' i - f x' i)| := by
          rw [h_split]
      _ ≤ |(f x i - g x i) + (g x i - g x' i)| + |g x' i - f x' i| :=
        abs_add_le _ _
      _ ≤ |f x i - g x i| + |g x i - g x' i| + |g x' i - f x' i| := by
        have := abs_add_le (f x i - g x i) (g x i - g x' i)
        linarith
  linarith

/-! ## Forward-error composition

A pattern that recurs whenever we chain a Lipschitz function on top
of a function with bounded error: the outer function amplifies the
inner function's error by its Lipschitz constant, and the outer's own
error contributes additively.

This is the abstract shape of the per-layer composition step in
multi-layer FP forward-error analyses.  Captures the "layer 2
amplifies layer 1's error" pattern that appears in `MLP2.forward_error_bound`,
softmax-then-CE composition, and any future deep-network analysis.
-/

/-- **Forward-error composition** through one Lipschitz layer.

Inputs:
* `lip_g`: outer function `g` is `K_g`-`LipschitzMax`.
* `h_outer`: at the FP-derived point `z` (one specific input vector),
  the outer FP-vs-real bound `|y - g z i| ≤ ε_g`.
* `h_inner`: per-index, the inner FP-vs-real-input deviation
  `|z j - w j| ≤ ε_f`.

Output: `|y - g w i| ≤ ε_g + K_g · ε_f`.

The outer's own error contributes additively; the inner's error gets
amplified by `K_g` via Lipschitz.  This is the load-bearing
composition step in any `forward_error_bound` chain. -/
theorem LipschitzMax.errorAmplification {m n : ℕ} {K_g ε_g ε_f : R}
    {g : (Fin m → R) → Fin n → R}
    (lip_g : LipschitzMax (R := R) K_g g)
    {y : R} {z w : Fin m → R} {i : Fin n}
    (h_outer : |y - g z i| ≤ ε_g)
    (h_inner : ∀ j, |z j - w j| ≤ ε_f) :
    |y - g w i| ≤ ε_g + K_g * ε_f := by
  have h_amp : |g z i - g w i| ≤ K_g * ε_f :=
    lip_g.bound z w h_inner i
  have h_tri : |y - g w i| ≤ |y - g z i| + |g z i - g w i| := by
    have h_split : y - g w i = (y - g z i) + (g z i - g w i) := by ring
    rw [h_split]; exact abs_add_le _ _
  linarith

/-- **Forward-error composition** through one scalar Lipschitz function.

Scalar analog of `LipschitzMax.errorAmplification`: outer error
`|y - g z| ≤ ε_g` plus inner deviation `|z - w| ≤ ε_f` compose to
`|y - g w| ≤ ε_g + K_g · ε_f`.  Used for activation-on-top-of-layer
forward-error bounds. -/
theorem LipschitzScalar.errorAmplification {K_g ε_g ε_f : R}
    {g : R → R} (lip_g : LipschitzScalar (R := R) K_g g)
    {y z w : R}
    (h_outer : |y - g z| ≤ ε_g)
    (h_inner : |z - w| ≤ ε_f) :
    |y - g w| ≤ ε_g + K_g * ε_f := by
  have h_amp : |g z - g w| ≤ K_g * ε_f :=
    le_trans (lip_g.bound z w) (mul_le_mul_of_nonneg_left h_inner lip_g.K_nn)
  have h_tri : |y - g w| ≤ |y - g z| + |g z - g w| := by
    have h_split : y - g w = (y - g z) + (g z - g w) := by ring
    rw [h_split]; exact abs_add_le _ _
  linarith

end Flean.Lipschitz
