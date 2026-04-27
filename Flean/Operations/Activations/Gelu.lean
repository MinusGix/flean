import Flean.Operations.Activations.Tanh

/-!
# GeLU (tanh approximation form)

```
gelu(x) ≈ 0.5 · x · (1 + tanh(c · (x + α · x³)))
```

where `c = √(2/π) ≈ 0.7978845608` and `α = 0.044715` (Hendrycks–Gimpel
tanh approximation; see Wick's `Activations/Functions.lean`).

This file ships the math reference and identities. The FP forward
implementation lives in `GeluFp.lean` and parametrizes over FiniteFp
approximations of the constants — flean doesn't ship `√(2/π)` as a
FiniteFp, so the user supplies a rounding witness.

## Design notes

We do *not* package `Real.geluTanhApprox` as a `Flean.Activation ℝ`.
The Lipschitz constant of gelu in this form is ~1.13 (max of `|gelu'|`
attained near `x ≈ 0.97`); proving this rigorously requires bounding
`gelu''` on a compact interval plus monotone-decay outside, and isn't
strictly needed for Wisp's per-element backward bridge. Downstream
consumers who need the `Activation ℝ` lift can construct it separately.

## Main definitions

* `Real.geluTanhApprox c α x` — math gelu parametrized over the constants.
* `Real.geluTanhApprox_deriv c α x` — derivative formula.
-/

set_option autoImplicit false

namespace Real

/-- GeLU in tanh-approximation form, parametrized over `half` (≈ 0.5),
`c` (≈ √(2/π)), `α` (≈ 0.044715), and the input `x`.

We expose `half` as a parameter (rather than hardcoding `1/2`) so the
FP closeness lemma can compare the FP impl against the math impl using
the *same* leading factor — avoiding a `|half_fp − 0.5|` error term in
the slack. -/
noncomputable def geluTanhApprox (half c α x : ℝ) : ℝ :=
  half * x * (1 + Real.tanh (c * (x + α * x^3)))

/-- Derivative of the parametric gelu (tanh approximation). Used for
Wisp's per-element backward bridge.

Letting `u(x) := c · (x + α · x³)` and `u'(x) = c · (1 + 3·α·x²)`,
chain + product rule gives:

```
gelu'(x) = half·(1 + tanh(u(x))) + half·x · (1 - tanh²(u(x))) · u'(x)
```

This formula is what `fpGeluDerivFinite` will compute. -/
noncomputable def geluTanhApprox_deriv (half c α x : ℝ) : ℝ :=
  let u := c * (x + α * x^3)
  let up := c * (1 + 3 * α * x^2)
  half * (1 + Real.tanh u) + half * x * (1 - Real.tanh u ^ 2) * up

end Real
