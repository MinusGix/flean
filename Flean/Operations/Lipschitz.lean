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

`LipschitzMaxWithSlack K c f` admits an additive slack `c` on the
output bound — the natural shape for FP operations whose rounding
introduces a bounded "fudge" beyond pure Lipschitz behavior:

```
∀ δ x x', (∀ j, |x j − x' j| ≤ δ) → ∀ i, |f x i − f x' i| ≤ K · δ + c
```

## Key design decisions

* **`0 ≤ K` is baked into the structure** as `K_nn`.  Composition
  derives this automatically; consumers never have to supply it.
* **Custom shape** chosen over Mathlib's `LipschitzWith`.  Mathlib
  needs `PiLp ⊤` instances and `ℝ≥0∞` constants; we want
  `R`-parametric simplicity.

## Where Lipschitz fits, and where it doesn't

The framework is for **R-valued** functions (like `Layer.forward`).
The composition propagates δ-perturbations through layers of math.

Per-FP-op "Lipschitz" statements about rounding aren't directly
expressible (rounding is discontinuous at midpoints), but
`LipschitzMaxWithSlack` covers the practical case of "almost-
Lipschitz with bounded slack."
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

/-! ## `LipschitzMax` with additive slack

The slack version `LipschitzMaxWithSlack K c f` admits a bounded
"fudge" `c` beyond the pure Lipschitz contribution.  This is the
natural shape for floating-point operations: `round` is approximately
1-Lipschitz with a half-ulp slack, and richer FP ops compose
similarly.

Composition is more delicate than for pure `LipschitzMax`, but
follows the same shape with slack accumulating linearly through the
chain. -/

/-- Lipschitz with additive slack: `|f x i - f x' i| ≤ K · δ + c`. -/
structure LipschitzMaxWithSlack {m n : ℕ}
    (K c : R) (f : (Fin m → R) → Fin n → R) : Prop where
  /-- Lipschitz constant is non-negative. -/
  K_nn : 0 ≤ K
  /-- Slack is non-negative. -/
  c_nn : 0 ≤ c
  /-- The slack-augmented Lipschitz bound. -/
  bound : ∀ {δ : R} (x x' : Fin m → R), (∀ j, |x j - x' j| ≤ δ) →
    ∀ i, |f x i - f x' i| ≤ K * δ + c

/-- Pure `LipschitzMax K f` is `LipschitzMaxWithSlack K 0 f`.  The
embedding direction. -/
theorem LipschitzMax.toWithSlack {m n : ℕ} {K : R}
    {f : (Fin m → R) → Fin n → R} (hf : LipschitzMax (R := R) K f) :
    LipschitzMaxWithSlack (R := R) K 0 f where
  K_nn := hf.K_nn
  c_nn := le_refl 0
  bound := by
    intro δ x x' h_dx i
    have := hf.bound x x' h_dx i
    linarith

/-- **Decomposition**: a `LipschitzMax K f'` plus a uniform bounded
perturbation `|g x i - f' x i| ≤ c'` constructs `LipschitzMaxWithSlack
K (2c') g`.  The factor of 2 comes from the triangle inequality on
both endpoints. -/
theorem LipschitzMaxWithSlack.ofLipschitzMaxAndPerturbation
    {m n : ℕ} {K c' : R} {f' g : (Fin m → R) → Fin n → R}
    (hf' : LipschitzMax (R := R) K f')
    (hpert : ∀ x i, |g x i - f' x i| ≤ c')
    (hc'_nn : 0 ≤ c') :
    LipschitzMaxWithSlack (R := R) K (2 * c') g where
  K_nn := hf'.K_nn
  c_nn := by linarith
  bound := by
    intro δ x x' h_dx i
    -- |g x i - g x' i| ≤ |g x i - f' x i| + |f' x i - f' x' i| + |f' x' i - g x' i|.
    have h_pert_x := hpert x i
    have h_pert_x' := hpert x' i
    have h_f'_lip := hf'.bound x x' h_dx i
    have h_pert_x'_sym : |f' x' i - g x' i| ≤ c' := by
      rw [abs_sub_comm]; exact h_pert_x'
    have h_tri :
        |g x i - g x' i| ≤
          |g x i - f' x i| + |f' x i - f' x' i| + |f' x' i - g x' i| := by
      have h_sum :
          (g x i - g x' i) =
          (g x i - f' x i) + (f' x i - f' x' i) + (f' x' i - g x' i) := by ring
      rw [h_sum]
      calc |(g x i - f' x i) + (f' x i - f' x' i) + (f' x' i - g x' i)|
          ≤ |(g x i - f' x i) + (f' x i - f' x' i)| + |f' x' i - g x' i| :=
            abs_add_le _ _
        _ ≤ |g x i - f' x i| + |f' x i - f' x' i| + |f' x' i - g x' i| := by
            have := abs_add_le (g x i - f' x i) (f' x i - f' x' i)
            linarith
    linarith

/-- Composition for the slack version: `g ∘ f` where `g` is pure
Lipschitz and `f` has slack. -/
theorem LipschitzMaxWithSlack.compPure {m k n : ℕ} {K_f c_f K_g : R}
    {f : (Fin m → R) → Fin k → R} {g : (Fin k → R) → Fin n → R}
    (hg : LipschitzMax (R := R) K_g g)
    (hf : LipschitzMaxWithSlack (R := R) K_f c_f f) :
    LipschitzMaxWithSlack (R := R) (K_g * K_f) (K_g * c_f) (fun x => g (f x)) where
  K_nn := mul_nonneg hg.K_nn hf.K_nn
  c_nn := mul_nonneg hg.K_nn hf.c_nn
  bound := by
    intro δ x x' h_dx i
    have h_finner : ∀ j, |f x j - f x' j| ≤ K_f * δ + c_f := fun j =>
      hf.bound x x' h_dx j
    have := hg.bound (f x) (f x') h_finner i
    calc |g (f x) i - g (f x') i|
        ≤ K_g * (K_f * δ + c_f) := this
      _ = K_g * K_f * δ + K_g * c_f := by ring

/-- Composition: pure `f`, slack `g`.  Slack carries through directly. -/
theorem LipschitzMaxWithSlack.purePost {m k n : ℕ} {K_f K_g c_g : R}
    {f : (Fin m → R) → Fin k → R} {g : (Fin k → R) → Fin n → R}
    (hg : LipschitzMaxWithSlack (R := R) K_g c_g g)
    (hf : LipschitzMax (R := R) K_f f) :
    LipschitzMaxWithSlack (R := R) (K_g * K_f) c_g (fun x => g (f x)) where
  K_nn := mul_nonneg hg.K_nn hf.K_nn
  c_nn := hg.c_nn
  bound := by
    intro δ x x' h_dx i
    have h_finner : ∀ j, |f x j - f x' j| ≤ K_f * δ := fun j =>
      hf.bound x x' h_dx j
    have := hg.bound (f x) (f x') h_finner i
    calc |g (f x) i - g (f x') i|
        ≤ K_g * (K_f * δ) + c_g := this
      _ = K_g * K_f * δ + c_g := by ring

/-- Composition: both pieces have slack.  Slack accumulates as
`K_g · c_f + c_g`. -/
theorem LipschitzMaxWithSlack.comp {m k n : ℕ} {K_f c_f K_g c_g : R}
    {f : (Fin m → R) → Fin k → R} {g : (Fin k → R) → Fin n → R}
    (hg : LipschitzMaxWithSlack (R := R) K_g c_g g)
    (hf : LipschitzMaxWithSlack (R := R) K_f c_f f) :
    LipschitzMaxWithSlack (R := R) (K_g * K_f) (K_g * c_f + c_g)
      (fun x => g (f x)) where
  K_nn := mul_nonneg hg.K_nn hf.K_nn
  c_nn := add_nonneg (mul_nonneg hg.K_nn hf.c_nn) hg.c_nn
  bound := by
    intro δ x x' h_dx i
    have h_finner : ∀ j, |f x j - f x' j| ≤ K_f * δ + c_f := fun j =>
      hf.bound x x' h_dx j
    have := hg.bound (f x) (f x') h_finner i
    calc |g (f x) i - g (f x') i|
        ≤ K_g * (K_f * δ + c_f) + c_g := this
      _ = K_g * K_f * δ + (K_g * c_f + c_g) := by ring

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

end Flean.Lipschitz
