import Flean.Operations.MLP.Layer
import Flean.Operations.MLP.LayerActivated
import Flean.Operations.MLP.MLP2
import Flean.Operations.MLP.ActivatedMLP2

/-!
# Verified Forward Pass of a 2-Layer Linear MLP

**End-to-end capstone.**  Composes every major primitive the library
has built — `FpMatVec`, `FpDotProduct`, `fpAddFinite`, `IsBoundedRange`,
`HasAbsBound` propagation, bundle bridges, Lipschitz framework — over
a realistic ML workload: a 2-layer multilayer perceptron with
constrained ("pixel-style") input.

This file is an aggregator.  Content lives in:

* `MLP/Layer.lean` — single linear layer (struct, real-valued forward,
  parameter bounds, FP-level result, magnitude/error bounds, Lipschitz
  instance, tag bridges).
* `MLP/LayerActivated.lean` — single linear layer with a scalar
  activation applied componentwise (struct, real forward, Lipschitz
  via `compScalar`, FP integration via slack-based soundness).
* `MLP/MLP2.lean` — 2-layer linear composition (struct, real-valued
  forward, composed bounds, FP-level result, error composition via
  Lipschitz, helpers, demo).
* `MLP/ActivatedMLP2.lean` — 2-layer activated composition (pair of
  `ActivatedLayer`s, real/FP forward, composed bounds, error via
  `LipschitzMax.errorAmplification`, ReLU demo).

## Scope

- **Per-layer optional activation**: linear (`Layer`) and activated
  (`ActivatedLayer`) flavors.  Both have corresponding 2-layer
  compositions (`MLP2`, `ActivatedMLP2`).
- **Fixed precision** (same `FloatFormat` throughout — no
  mixed-precision yet).
- **Constrained inputs**: typically `HasAbsBound xMax` (the
  "pixel values in `[0, 1]`" idiom).
- **Bounded parameters**: per-layer `BoundedParams wMax bMax` tag.

## Main results

1. **`MLP2FpResult.toVal_abs_le`** — forward magnitude bound on the
   FP MLP output.
2. **`MLP2FpResult.forward_error_bound`** — forward error bound
   relating the FP-computed output to the real-valued ground-truth
   output.
3. **`MLP2.forward_lipschitz`** — whole-MLP Lipschitz constant
   (input-perturbation analyses; distinct from forward error).
4. **`MLP2FpResult.forward_error_bound_demo`** — runnable smoke test
   on shape (4 → 3 → 2).
5. **`ActivatedLayer.forward_lipschitz`** — activation-on-top-of-layer
   Lipschitz via `LipschitzMax.compScalar`.
6. **`ActivatedLayerFpResult.forward_error_bound`** — activated
   single-layer FP error bound, composed via
   `LipschitzScalar.errorAmplification`.
7. **`ActivatedMLP2FpResult.forward_error_bound`** — activated 2-layer
   FP error bound, composed via `LipschitzMax.errorAmplification` on
   the second activated layer's Lipschitz constant
   `σ₂.K · n_hidden · w2Max`.
-/
