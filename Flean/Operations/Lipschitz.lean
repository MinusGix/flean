import Flean.Operations.MLP

/-!
# Lipschitz Spike (M2)

A small experiment to see whether a custom `LipschitzMax` notion (or
Mathlib's `LipschitzWith`) gives more elegant multi-layer error
composition than the manual `Layer.forward_perturbation` chain used
in `MLP.lean`.

## Why a custom shape?

Our perturbation lemma has the form

```
∀ j, |x j − x' j| ≤ δ → |f x i − f x' i| ≤ K · δ
```

— per-output bounded by max-input-perturbation.  This is the L∞→L∞
operator-norm Lipschitz statement, but stated per-output-coordinate.

Mathlib's `LipschitzWith K f` from `EMetric` is `∀ x y, edist (f x)
(f y) ≤ K * edist x y`, which would require `PiLp ⊤` instances on
`Fin n → ℝ` and an `ℝ≥0∞`-valued constant.  Functional but heavy for
our use case.

The minimal spike below introduces `LipschitzMax K f`
specifically for the per-output-index statement and provides
composition.  We compare it against the manual chain in
`MLPFpResult.forward_error_bound`.

If `LipschitzMax` proves elegant, we expand the framework with it.
If it just reinvents Mathlib at a less-general level, we route
through `LipschitzWith` instead.
-/

set_option autoImplicit false

namespace Flean.Lipschitz

open Finset BigOperators

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## The notion

`LipschitzMax K f` means `f : (Fin m → R) → Fin n → R` (an
`n`-vector function of an `m`-vector input) satisfies

```
∀ δ x x', (∀ j, |x j − x' j| ≤ δ) → ∀ i, |f x i − f x' i| ≤ K · δ
```

i.e. *every output-index* changes by at most `K · δ` when *every
input-index* perturbs by at most `δ`.  Strictly weaker than the
sup-norm Lipschitz `max_i |f x i − f x' i| ≤ K · max_j |x j − x' j|`,
but matches our forward-error analysis verbatim.
-/

/-- Per-output Lipschitz constant of a multivariate vector function. -/
def LipschitzMax {m n : ℕ} (K : R) (f : (Fin m → R) → Fin n → R) : Prop :=
  ∀ {δ : R} (x x' : Fin m → R), (∀ j, |x j - x' j| ≤ δ) →
    ∀ i, |f x i - f x' i| ≤ K * δ

/-! ## Composition

If `g` is `K_g`-Lipschitz and `f` is `K_f`-Lipschitz, then `g ∘ f`
is `K_g · K_f`-Lipschitz.  This is the load-bearing identity for
multi-layer error composition. -/

theorem LipschitzMax.comp {m k n : ℕ} {K_f K_g : R}
    {f : (Fin m → R) → Fin k → R} {g : (Fin k → R) → Fin n → R}
    (hg : LipschitzMax (R := R) K_g g)
    (hf : LipschitzMax (R := R) K_f f)
    (hK_g_nn : 0 ≤ K_g) :
    LipschitzMax (R := R) (K_g * K_f) (fun x => g (f x)) := by
  intro δ x x' h_dx i
  -- Per-index: |f x j - f x' j| ≤ K_f · δ
  have h_fperturb : ∀ j, |f x j - f x' j| ≤ K_f * δ := fun j => hf x x' h_dx j
  -- |g (f x) i - g (f x') i| ≤ K_g · (K_f · δ).
  have := hg (f x) (f x') h_fperturb i
  calc |g (f x) i - g (f x') i| ≤ K_g * (K_f * δ) := this
    _ = K_g * K_f * δ := by ring

/-! ## Bridge: `Layer.forward` is `LipschitzMax (n_in · wMax)`.

This restates the existing `Layer.forward_perturbation` lemma as a
`LipschitzMax` instance — the bridge that lets us use the abstract
composition theorem.  Note: `forward_perturbation` is a `private`
helper in `MLP.lean`, so we re-derive its content here. -/

variable [FloatFormat] [FloorRing R]

theorem Layer.forward_lipschitz {n_in n_out : ℕ} (L : MLP.Layer n_in n_out)
    {wMax bMax : R} (hL : MLP.BoundedParams (R := R) L wMax bMax)
    (hwMax_nn : 0 ≤ wMax) :
    LipschitzMax (R := R) ((n_in : R) * wMax) L.forward := by
  intro δ x x' h_dx i
  unfold MLP.Layer.forward
  have h_sub :
      ((∑ j, ((L.W i j).toVal : R) * x j) + ((L.b i).toVal : R)) -
      ((∑ j, ((L.W i j).toVal : R) * x' j) + ((L.b i).toVal : R)) =
      ∑ j, ((L.W i j).toVal : R) * (x j - x' j) := by
    have h_collapse :
        ((∑ j, ((L.W i j).toVal : R) * x j) + ((L.b i).toVal : R)) -
        ((∑ j, ((L.W i j).toVal : R) * x' j) + ((L.b i).toVal : R)) =
        (∑ j, ((L.W i j).toVal : R) * x j) -
        (∑ j, ((L.W i j).toVal : R) * x' j) := by ring
    rw [h_collapse, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [h_sub]
  calc |∑ j, ((L.W i j).toVal : R) * (x j - x' j)|
      ≤ ∑ j, |((L.W i j).toVal : R) * (x j - x' j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n_in, wMax * δ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hL.weight_bounded i j) (h_dx j) (abs_nonneg _) hwMax_nn
    _ = (n_in : R) * (wMax * δ) := by
        rw [Finset.sum_const]; simp [mul_comm]
    _ = (n_in : R) * wMax * δ := by ring

/-! ## 2-layer Lipschitz via composition

The payoff: the 2-layer Lipschitz constant follows from `comp`
without re-deriving the chain. -/

theorem MLP2.forward_lipschitz {n_in n_hidden n_out : ℕ}
    (M : MLP.MLP2 n_in n_hidden n_out)
    {w1Max b1Max w2Max b2Max : R}
    (hM : MLP.MLP2BoundedParams (R := R) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hw2_nn : 0 ≤ w2Max) :
    LipschitzMax (R := R)
      (((n_hidden : R) * w2Max) * ((n_in : R) * w1Max))
      M.forward := by
  unfold MLP.MLP2.forward
  exact LipschitzMax.comp
    (Layer.forward_lipschitz M.layer2 hM.layer2_bounded hw2_nn)
    (Layer.forward_lipschitz M.layer1 hM.layer1_bounded hw1_nn)
    (mul_nonneg (Nat.cast_nonneg _) hw2_nn)

/-! ## Spike findings (in-line)

The `LipschitzMax.comp` proof is **3 lines**.  Each `Layer`'s
`forward_lipschitz` is **18 lines** (mostly the same as the existing
`forward_perturbation` — just rewrapped).  The 2-layer composition
is **5 lines**.

This is qualitatively cleaner than the manual triangle inequality
in `MLP2FpResult.forward_error_bound` (~25 lines of triangle +
substitution).  The composition flows mechanically.

**Verdict** (for the followup framework expansion):

* **Custom `LipschitzMax` is the right shape** for our use case.
  Mathlib's `LipschitzWith` would require `PiLp ⊤`-typed inputs and
  `ℝ≥0∞`-valued constants, which adds noise without benefit.

* **The split between input-side and output-side perturbation** is
  the meaningful design axis.  `LipschitzMax` chose: input δ is
  *uniform* (max), output bound is *per-index*.  Other useful
  variants:
    * `LipschitzSum`: input perturbation in L¹, output per-index.
    * `LipschitzInf`: input + output both in L∞.

* **For full M2 framework**: ship `LipschitzMax` (this notion),
  add per-FP-op Lipschitz instances (`fpAdd`, `fpMul`, `fpFMA`),
  add per-Layer instance (this file), use it to refactor
  `MLP2FpResult.forward_error_bound` to use composition rather than
  manual triangle.

* **Mathlib bridge**: provide a `LipschitzMax → LipschitzWith` (with
  `PiLp ⊤` instances supplied) for users who want Mathlib API.
  Lower priority.
-/

end Flean.Lipschitz
