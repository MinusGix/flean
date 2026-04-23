import Flean.Operations.MLP.Layer
import Flean.Operations.MLP.LayerActivated

/-!
# Composable Layer Certificates

A per-layer certificate bundling everything needed to invoke the
single-layer forward-error and magnitude bounds on a single FP input:

* the layer parameters + their `BoundedParams` tag,
* the input vector + its `HasAbsBound` tag,
* the input's `xMax` nonneg fact,
* the parameter-nonneg facts `wMax_nn` / `bMax_nn`,
* the FP witness (`LayerFpResult`).

The certificate exposes the layer's error and magnitude bounds as
one-call methods (`forward_error_bound`, `toVal_abs_le`), and supports
chaining via `.extend` — attach a new layer, and the resulting cert's
input bounds are automatically the previous layer's output bounds.

## Why it's useful

Multi-layer MLPs (MLP₂, MLP₃, …) all share the same per-layer shape:
each layer needs its own parameter bounds + input bounds, and the
intermediate magnitudes chain.  The existing `MLP2FpResult` /
`ActivatedMLP2FpResult` pre-wire this for the 2-layer case; for
arbitrary N, a certificate chain gives the same glue mechanically.

For a 3-layer MLP:

```
let cert1 := LayerResultCert.mk h_in h_hidden1 hM1 hx hxMax_nn fp1
let cert2 := cert1.extend h_hidden2 hM2 hw2_nn fp2
let cert3 := cert2.extend h_out hM3 hw3_nn fp3
cert3.toVal_abs_le k                -- magnitude bound on layer-3 output
cert3.forward_error_bound k         -- per-layer error at layer 3
```

Composing errors across the chain (amplification via Lipschitz) uses
`LipschitzMax.errorAmplification` as usual — the cert holds the
ingredients, the composition stays explicit at the call site (see
`MLP2` / `ActivatedMLP2` for the 2-layer pattern).

## Scope

* `LayerResultCert` for linear layers.
* `ActivatedLayerResultCert` for activated layers.
* `.extend` chain operation on both.
* `forward_error_bound_demo3` — 3-layer linear MLP error chain
  showing the primitive in action (whole-chain bound via iterated
  Lipschitz amplification).
-/

set_option autoImplicit false

namespace MLP

open Finset BigOperators Flean.Tags Flean.Lipschitz

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R]

/-! ## Linear layer certificate -/

/-- **Per-layer certificate**: bundles the layer, its FP input, its
bounds (parameter + input), the nonneg facts, and the FP witness. -/
structure LayerResultCert {n_in n_out : ℕ} (L : Layer n_in n_out)
    (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R] where
  /-- The FP input. -/
  xs : Fin n_in → FiniteFp
  /-- Input magnitude bound. -/
  xMax : R
  /-- Weight magnitude bound. -/
  wMax : R
  /-- Bias magnitude bound. -/
  bMax : R
  /-- Input is bounded. -/
  input_bounded : ∀ j, HasAbsBound (R := R) xMax (xs j)
  /-- Input bound is nonneg. -/
  xMax_nn : 0 ≤ xMax
  /-- Parameters bounded. -/
  params_bounded : BoundedParams (R := R) L wMax bMax
  /-- Weight bound is nonneg. -/
  wMax_nn : 0 ≤ wMax
  /-- Bias bound is nonneg. -/
  bMax_nn : 0 ≤ bMax
  /-- FP forward pass witness. -/
  fp : LayerFpResult L xs R

namespace LayerResultCert

variable {n_in n_out : ℕ} {L : Layer n_in n_out}

/-- Build a certificate from the individual pieces and dim-positivity
(which discharges the parameter-nonneg hypotheses via
`BoundedParams.{wMax,bMax}_nn`). -/
def mk' (h_in : 0 < n_in) (h_out : 0 < n_out)
    (xs : Fin n_in → FiniteFp) {xMax wMax bMax : R}
    (hx : ∀ j, HasAbsBound (R := R) xMax (xs j))
    (hxMax_nn : 0 ≤ xMax)
    (hM : BoundedParams (R := R) L wMax bMax)
    (fp : LayerFpResult L xs R) :
    LayerResultCert L R where
  xs := xs
  xMax := xMax
  wMax := wMax
  bMax := bMax
  input_bounded := hx
  xMax_nn := hxMax_nn
  params_bounded := hM
  wMax_nn := hM.wMax_nn h_in h_out
  bMax_nn := hM.bMax_nn h_out
  fp := fp

/-- Output vector. -/
def output (c : LayerResultCert L R) : Fin n_out → FiniteFp :=
  c.fp.result

/-- Output magnitude bound. -/
noncomputable def outputBound (c : LayerResultCert L R) : R :=
  c.fp.outputBound c.wMax c.xMax c.bMax

/-- Output magnitude bound is nonneg. -/
theorem outputBound_nn (c : LayerResultCert L R) :
    0 ≤ c.outputBound :=
  c.fp.outputBound_nn c.wMax_nn c.xMax_nn c.bMax_nn

/-- Single-layer magnitude bound, applied via the certificate. -/
theorem toVal_abs_le (c : LayerResultCert L R) (i : Fin n_out) :
    |((c.output i).toVal : R)| ≤ c.outputBound :=
  c.fp.toVal_abs_le c.params_bounded c.wMax_nn
    c.input_bounded c.xMax_nn i

/-- Single-layer forward-error bound, applied via the certificate. -/
theorem forward_error_bound (c : LayerResultCert L R) (i : Fin n_out) :
    |((c.output i).toVal : R) -
        L.forward (fun j => ((c.xs j).toVal : R)) i| ≤
      c.fp.errorBound c.wMax c.xMax c.bMax :=
  c.fp.forward_error_bound c.params_bounded c.wMax_nn
    c.input_bounded c.xMax_nn i

/-- **Chain**: extend a layer-k certificate with a new layer L' whose
input is the previous layer's output.  The new cert's input bound is
the previous layer's output bound (automatic), and the new parameter
bounds come from `hM'`.  Enables N-layer composition. -/
noncomputable def extend (c : LayerResultCert L R)
    {n' : ℕ} (h_out' : 0 < n') (L' : Layer n_out n')
    {w'Max b'Max : R} (hM' : BoundedParams (R := R) L' w'Max b'Max)
    (hw'_nn : 0 ≤ w'Max)
    (fp' : LayerFpResult L' c.output R) :
    LayerResultCert L' R where
  xs := c.output
  xMax := c.outputBound
  wMax := w'Max
  bMax := b'Max
  input_bounded := fun j => ⟨c.toVal_abs_le j⟩
  xMax_nn := c.outputBound_nn
  params_bounded := hM'
  wMax_nn := hw'_nn
  bMax_nn := hM'.bMax_nn h_out'
  fp := fp'

end LayerResultCert

/-! ## Activated layer certificate -/

/-- **Per-activated-layer certificate**: the activated analog of
`LayerResultCert`.  Bundles the activated layer, its FP input, its
bounds, the FP witness, and the activation's soundness witness. -/
structure ActivatedLayerResultCert {n_in n_out : ℕ}
    (LA : ActivatedLayer R n_in n_out) (R : Type*) [Field R]
    [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    [RModeConj R] [RModeZero R] where
  /-- FP input. -/
  xs : Fin n_in → FiniteFp
  /-- Input magnitude bound. -/
  xMax : R
  /-- Weight magnitude bound. -/
  wMax : R
  /-- Bias magnitude bound. -/
  bMax : R
  /-- Input is bounded. -/
  input_bounded : ∀ j, HasAbsBound (R := R) xMax (xs j)
  /-- Input bound is nonneg. -/
  xMax_nn : 0 ≤ xMax
  /-- Parameters bounded. -/
  params_bounded : BoundedParams (R := R) LA.layer wMax bMax
  /-- Weight bound is nonneg. -/
  wMax_nn : 0 ≤ wMax
  /-- Bias bound is nonneg. -/
  bMax_nn : 0 ≤ bMax
  /-- FP activated forward pass witness. -/
  fp : ActivatedLayerFpResult LA xs

namespace ActivatedLayerResultCert

variable {n_in n_out : ℕ} {LA : ActivatedLayer R n_in n_out}

/-- Build an activated certificate from the individual pieces. -/
def mk' (h_in : 0 < n_in) (h_out : 0 < n_out)
    (xs : Fin n_in → FiniteFp) {xMax wMax bMax : R}
    (hx : ∀ j, HasAbsBound (R := R) xMax (xs j))
    (hxMax_nn : 0 ≤ xMax)
    (hM : BoundedParams (R := R) LA.layer wMax bMax)
    (fp : ActivatedLayerFpResult LA xs) :
    ActivatedLayerResultCert LA R where
  xs := xs
  xMax := xMax
  wMax := wMax
  bMax := bMax
  input_bounded := hx
  xMax_nn := hxMax_nn
  params_bounded := hM
  wMax_nn := hM.wMax_nn h_in h_out
  bMax_nn := hM.bMax_nn h_out
  fp := fp

/-- Output vector (after activation). -/
def output (c : ActivatedLayerResultCert LA R) : Fin n_out → FiniteFp :=
  c.fp.activated.result

/-- Output magnitude bound (after activation). -/
noncomputable def outputBound (c : ActivatedLayerResultCert LA R) : R :=
  c.fp.outputBound c.wMax c.xMax c.bMax

/-- Output magnitude bound is nonneg. -/
theorem outputBound_nn (c : ActivatedLayerResultCert LA R) :
    0 ≤ c.outputBound :=
  c.fp.outputBound_nn c.wMax_nn c.xMax_nn c.bMax_nn

/-- Single-layer activated magnitude bound via certificate. -/
theorem toVal_abs_le (c : ActivatedLayerResultCert LA R)
    (i : Fin n_out) :
    |((c.output i).toVal : R)| ≤ c.outputBound :=
  c.fp.toVal_abs_le c.params_bounded c.wMax_nn
    c.input_bounded c.xMax_nn i

/-- Single-layer activated forward-error bound via certificate. -/
theorem forward_error_bound (c : ActivatedLayerResultCert LA R)
    (i : Fin n_out) :
    |((c.output i).toVal : R) -
        LA.forward (fun j => ((c.xs j).toVal : R)) i| ≤
      c.fp.errorBound c.wMax c.xMax c.bMax :=
  c.fp.forward_error_bound c.params_bounded c.wMax_nn
    c.input_bounded c.xMax_nn i

/-- **Chain** on activated layers. -/
noncomputable def extend (c : ActivatedLayerResultCert LA R)
    {n' : ℕ} (h_out' : 0 < n')
    (LA' : ActivatedLayer R n_out n')
    {w'Max b'Max : R}
    (hM' : BoundedParams (R := R) LA'.layer w'Max b'Max)
    (hw'_nn : 0 ≤ w'Max)
    (fp' : ActivatedLayerFpResult LA' c.output) :
    ActivatedLayerResultCert LA' R where
  xs := c.output
  xMax := c.outputBound
  wMax := w'Max
  bMax := b'Max
  input_bounded := fun j => ⟨c.toVal_abs_le j⟩
  xMax_nn := c.outputBound_nn
  params_bounded := hM'
  wMax_nn := hw'_nn
  bMax_nn := hM'.bMax_nn h_out'
  fp := fp'

end ActivatedLayerResultCert

/-! ## 3-layer linear MLP chain — demo of N-layer composition

The certificate primitive shines on MLPs with more layers than we've
pre-defined a struct for.  This section demonstrates a 3-layer linear
chain, producing the full `|fp − real|` error bound composed via
`LipschitzMax.errorAmplification` at each step.

For a 3-layer chain `L1 → L2 → L3`, the error decomposes as:

```
ε_total = ε_L3 + K_L3 · (ε_L2 + K_L2 · ε_L1)
        = ε_L3 + K_L3 · ε_L2 + K_L3 · K_L2 · ε_L1
```

where `K_Li = n_{i-1} · wMax_i` is layer i's Lipschitz constant.
-/

/-- **3-layer linear MLP forward-error bound via certificate chain.**

Given three linear-layer certs whose `xs` fields link in a chain
(`c2.xs = c1.output`, `c3.xs = c2.output`), compose the per-layer
errors via iterated `LipschitzMax.errorAmplification` on the
downstream layers.  The output bound is
`ε_L3 + K_L3·ε_L2 + K_L3·K_L2·ε_L1`.

The linking hypotheses come for free when `c2`/`c3` were constructed
via `.extend` (use `rfl`); they also accept any bespoke chain
construction that makes the intermediate identifications explicit. -/
theorem layerCert_chain3_forward_error_bound
    {n₀ n₁ n₂ n₃ : ℕ}
    {L1 : Layer n₀ n₁} {L2 : Layer n₁ n₂} {L3 : Layer n₂ n₃}
    (c1 : LayerResultCert L1 R)
    (c2 : LayerResultCert L2 R)
    (c3 : LayerResultCert L3 R)
    (h_link12 : c2.xs = c1.output)
    (h_link23 : c3.xs = c2.output)
    (k : Fin n₃) :
    |((c3.output k).toVal : R) -
        L3.forward (L2.forward
          (L1.forward (fun j => ((c1.xs j).toVal : R)))) k| ≤
      c3.fp.errorBound c3.wMax c3.xMax c3.bMax +
      (n₂ : R) * c3.wMax *
        (c2.fp.errorBound c2.wMax c2.xMax c2.bMax +
          (n₁ : R) * c2.wMax *
            c1.fp.errorBound c1.wMax c1.xMax c1.bMax) := by
  -- Per-layer error witnesses.
  have h_err1 : ∀ j, |((c1.output j).toVal : R) -
      L1.forward (fun l => ((c1.xs l).toVal : R)) j| ≤
      c1.fp.errorBound c1.wMax c1.xMax c1.bMax :=
    fun j => c1.forward_error_bound j
  have h_err2 : ∀ j, |((c2.output j).toVal : R) -
      L2.forward (fun l => ((c2.xs l).toVal : R)) j| ≤
      c2.fp.errorBound c2.wMax c2.xMax c2.bMax :=
    fun j => c2.forward_error_bound j
  have h_err3 := c3.forward_error_bound k
  -- Lipschitz constants for L2 and L3 on their actual inputs.
  have h_lip2 : LipschitzMax (R := R) ((n₁ : R) * c2.wMax) L2.forward :=
    L2.forward_lipschitz c2.params_bounded c2.wMax_nn
  have h_lip3 : LipschitzMax (R := R) ((n₂ : R) * c3.wMax) L3.forward :=
    L3.forward_lipschitz c3.params_bounded c3.wMax_nn
  -- Inner step 1→2: c1 error fed through L2 (via c2's Lipschitz).
  have h_inner2 : ∀ j, |((c2.xs j).toVal : R) -
      L1.forward (fun l => ((c1.xs l).toVal : R)) j| ≤
      c1.fp.errorBound c1.wMax c1.xMax c1.bMax := by
    intro j
    rw [h_link12]; exact h_err1 j
  have h_step12 : ∀ k₂, |((c2.output k₂).toVal : R) -
      L2.forward (L1.forward (fun l => ((c1.xs l).toVal : R))) k₂| ≤
      c2.fp.errorBound c2.wMax c2.xMax c2.bMax +
      (n₁ : R) * c2.wMax *
        c1.fp.errorBound c1.wMax c1.xMax c1.bMax := fun k₂ =>
    LipschitzMax.errorAmplification h_lip2 (h_err2 k₂) h_inner2
  -- Outer step 2→3: 2-layer error amplified through L3.
  have h_inner3 : ∀ j, |((c3.xs j).toVal : R) -
      L2.forward (L1.forward (fun l => ((c1.xs l).toVal : R))) j| ≤
      c2.fp.errorBound c2.wMax c2.xMax c2.bMax +
      (n₁ : R) * c2.wMax *
        c1.fp.errorBound c1.wMax c1.xMax c1.bMax := by
    intro j
    rw [h_link23]; exact h_step12 j
  exact LipschitzMax.errorAmplification h_lip3 h_err3 h_inner3

end MLP
