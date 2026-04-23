import Flean.Operations.MLP.Layer

/-!
# N-Layer Linear MLP via Inductive Chain

Generalizes `MLP2` to arbitrary layer counts via an inductive type.
A `LayerChain R n_in n_out` is either the identity (no layers) or a
single layer `L : Layer n_in n_mid` followed by a chain from `n_mid`
to `n_out`.  Per-layer parameter bounds live inside each `cons`.

## Contents

* `LayerChain R n_in n_out` — inductive chain with per-layer bounds.
* `LayerChain.forward` — recursive real-valued forward pass.
* `LayerChain.outputBoundReal` — recursive real magnitude bound.
* `LayerChain.forward_abs_le` — real-valued magnitude theorem.
* `LayerChain.lipschitzK` — whole-chain Lipschitz constant
  (product of per-layer `n_in · wMax`s).
* `LayerChain.forward_lipschitz` — whole-chain `LipschitzMax`.
* `LayerChain.FpTrace C xs ys` — inductive FP witness type linking
  `LayerFpResult`s.
* `LayerChain.FpTrace.outputBound` / `toVal_abs_le` — FP magnitude.
* `LayerChain.FpTrace.errorBound` / `forward_error_bound` —
  FP-vs-real error bound, proved by induction using
  `LipschitzMax.errorAmplification` at each recursion step.

Bounds are **per-layer** (not uniform) — each `cons` carries its own
`wMax_i`/`bMax_i`, matching a realistic per-layer constraint model.

## Design

The recursion is head-first: `cons L rest` processes `L` first, then
`rest`.  The chain's forward pass is `rest.forward (L.forward x)`.
The error bound decomposes as

    ε_total = ε_{rest}(L's FP output) + K_{rest} · ε_L

where `K_{rest}` is the rest chain's Lipschitz constant.  This is
exactly the `LipschitzMax.errorAmplification` shape applied one step
at a time; induction on the chain shape closes the proof.
-/

set_option autoImplicit false

universe u

namespace MLP

open Finset BigOperators Flean.Tags Flean.Lipschitz

variable [FloatFormat]
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R]

/-! ## Chain type + real-valued forward pass -/

/-- Inductive chain of linear layers.  Each `cons` carries one
`Layer` plus its parameter bounds (`wMax`, `bMax`, `BoundedParams`)
and the `wMax` nonneg witness (needed for Lipschitz + magnitude
propagation).

Universe bumped one level above `R` (the chain carries `R`-valued
weight/bias bounds in each `cons`). -/
inductive LayerChain (R : Type u)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    ℕ → ℕ → Type (u + 1) where
  /-- Identity chain (no layers). -/
  | id {n : ℕ} : LayerChain R n n
  /-- Prepend one layer with its bounds. -/
  | cons {n_in n_mid n_out : ℕ}
      (L : Layer n_in n_mid) (wMax bMax : R)
      (hL : BoundedParams (R := R) L wMax bMax)
      (hwMax_nn : 0 ≤ wMax) (hbMax_nn : 0 ≤ bMax)
      (rest : LayerChain R n_mid n_out) :
      LayerChain R n_in n_out

namespace LayerChain

/-- Real-valued forward pass by recursion on the chain. -/
noncomputable def forward {n_in n_out : ℕ} :
    LayerChain R n_in n_out → (Fin n_in → R) → (Fin n_out → R)
  | .id, x => x
  | .cons L _ _ _ _ _ rest, x => rest.forward (L.forward x)

/-- Real magnitude bound: chain's output is bounded by recursively
applying `Layer.outputBoundReal` through each layer. -/
noncomputable def outputBoundReal {n_in n_out : ℕ} :
    LayerChain R n_in n_out → R → R
  | .id, xMax => xMax
  | .cons L wMax bMax _ _ _ rest, xMax =>
      rest.outputBoundReal (L.outputBoundReal wMax xMax bMax)

omit [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R] in
/-- The real forward pass's output is bounded by `outputBoundReal`. -/
theorem forward_abs_le {n_in n_out : ℕ}
    (C : LayerChain R n_in n_out)
    {x : Fin n_in → R} {xMax : R}
    (hx : ∀ j, |x j| ≤ xMax) (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |C.forward x k| ≤ C.outputBoundReal xMax := by
  induction C generalizing xMax with
  | id => exact hx k
  | @cons n_in n_mid n_out L wMax bMax hL hwMax_nn hbMax_nn rest ih =>
    -- Goal: |rest.forward (L.forward x) k| ≤ rest.outputBoundReal (L.outputBoundReal wMax xMax bMax)
    have h_L : ∀ j, |L.forward x j| ≤ L.outputBoundReal wMax xMax bMax := fun j =>
      L.forward_abs_le hL hwMax_nn hx hxMax_nn j
    have h_L_nn : 0 ≤ L.outputBoundReal wMax xMax bMax := by
      unfold Layer.outputBoundReal
      have : 0 ≤ (n_in : R) * wMax * xMax :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hwMax_nn) hxMax_nn
      linarith
    exact ih h_L h_L_nn k

/-! ## Whole-chain Lipschitz -/

/-- The whole-chain Lipschitz constant: product of per-layer
Lipschitz constants `n · wMax` for each layer in the chain.  The
`id` chain has constant `1`. -/
noncomputable def lipschitzK {n_in n_out : ℕ} :
    LayerChain R n_in n_out → R
  | .id => 1
  | .cons (n_in := n_in) _ wMax _ _ _ _ rest =>
      rest.lipschitzK * ((n_in : R) * wMax)

omit [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R] in
/-- `lipschitzK` is nonneg. -/
theorem lipschitzK_nn {n_in n_out : ℕ} (C : LayerChain R n_in n_out) :
    0 ≤ C.lipschitzK := by
  induction C with
  | id => exact zero_le_one
  | @cons n_in n_mid n_out L wMax bMax hL hwMax_nn hbMax_nn rest ih =>
    unfold lipschitzK
    exact mul_nonneg ih
      (mul_nonneg (Nat.cast_nonneg _) hwMax_nn)

/-- The whole chain is Lipschitz in its input.  Constant is the
product of per-layer Lipschitz constants. -/
theorem forward_lipschitz {n_in n_out : ℕ} (C : LayerChain R n_in n_out) :
    LipschitzMax (R := R) C.lipschitzK C.forward := by
  induction C with
  | id =>
    -- id chain = identity.  1-Lipschitz.
    refine ⟨zero_le_one, ?_⟩
    intro δ x x' h_dx i
    show |x i - x' i| ≤ 1 * δ
    have := h_dx i; linarith
  | @cons n_in n_mid n_out L wMax bMax hL hwMax_nn hbMax_nn rest ih =>
    -- cons = rest ∘ L.  Lipschitz = rest.K · (n_in · wMax).
    have h_L_lip : LipschitzMax (R := R) ((n_in : R) * wMax) L.forward :=
      L.forward_lipschitz hL hwMax_nn
    -- Compose: rest ∘ L is (rest.K · L.K)-Lipschitz.
    have h_comp : LipschitzMax (R := R) (rest.lipschitzK * ((n_in : R) * wMax))
        (fun x => rest.forward (L.forward x)) :=
      LipschitzMax.comp ih h_L_lip
    -- The forward of (cons L _ _ _ _ _ rest) is fun x => rest.forward (L.forward x).
    exact h_comp

/-! ## FP trace: an inductive witness type -/

/-- FP witness for a chain: a linked list of `LayerFpResult`s where
layer `k+1`'s input is layer `k`'s output.  Mirrors the chain
structure — one `cons` per layer. -/
inductive FpTrace : ∀ {n_in n_out : ℕ}, LayerChain R n_in n_out →
    (Fin n_in → FiniteFp) → (Fin n_out → FiniteFp) → Type (u + 1) where
  /-- Identity trace: input = output. -/
  | id {n : ℕ} (xs : Fin n → FiniteFp) :
      FpTrace (LayerChain.id (R := R)) xs xs
  /-- Step trace: one layer's FP witness + the rest's trace on
  layer's output. -/
  | cons {n_in n_mid n_out : ℕ}
      {L : Layer n_in n_mid} {wMax bMax : R}
      {hL : BoundedParams (R := R) L wMax bMax}
      {hwMax_nn : 0 ≤ wMax} {hbMax_nn : 0 ≤ bMax}
      {rest : LayerChain R n_mid n_out}
      {xs : Fin n_in → FiniteFp} {ys : Fin n_out → FiniteFp}
      (fpL : LayerFpResult L xs R)
      (fpRest : FpTrace rest fpL.result ys) :
      FpTrace (LayerChain.cons L wMax bMax hL hwMax_nn hbMax_nn rest) xs ys

namespace FpTrace

/-- FP magnitude bound on the trace's output.  Recursively applies
`LayerFpResult.outputBound` through each layer, feeding the previous
layer's output bound as the next layer's input bound. -/
noncomputable def outputBound : ∀ {n_in n_out : ℕ} {C : LayerChain R n_in n_out}
    {xs : Fin n_in → FiniteFp} {ys : Fin n_out → FiniteFp},
    FpTrace C xs ys → R → R  -- xMax → bound on |ys|
  | _, _, _, _, _, .id _, xMax => xMax
  | _, _, _, _, _, @FpTrace.cons _ _ _ _ _ _ _ _ _ _ _ wMax bMax _ _ _ _ _ _ fpL fpRest,
    xMax =>
      fpRest.outputBound (fpL.outputBound wMax xMax bMax)

/-- FP output magnitude bound is nonneg given nonneg inputs. -/
theorem outputBound_nn {n_in n_out : ℕ} {C : LayerChain R n_in n_out}
    {xs : Fin n_in → FiniteFp} {ys : Fin n_out → FiniteFp}
    (fpT : FpTrace C xs ys) {xMax : R} (hxMax_nn : 0 ≤ xMax) :
    0 ≤ fpT.outputBound xMax := by
  induction fpT generalizing xMax with
  | id => exact hxMax_nn
  | @cons n_in n_mid n_out L wMax bMax hL hwMax_nn hbMax_nn rest
      xs ys fpL fpRest ih =>
    unfold FpTrace.outputBound
    have h_L_nn : 0 ≤ fpL.outputBound wMax xMax bMax :=
      fpL.outputBound_nn hwMax_nn hxMax_nn hbMax_nn
    exact ih h_L_nn

/-- FP output is magnitude-bounded via recursive application of the
single-layer `toVal_abs_le`. -/
theorem toVal_abs_le {n_in n_out : ℕ} {C : LayerChain R n_in n_out}
    {xs : Fin n_in → FiniteFp} {ys : Fin n_out → FiniteFp}
    (fpT : FpTrace C xs ys) {xMax : R}
    (hx : ∀ j, HasAbsBound (R := R) xMax (xs j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((ys k).toVal : R)| ≤ fpT.outputBound xMax := by
  induction fpT generalizing xMax with
  | id => exact (hx k).toVal_abs_le
  | @cons n_in n_mid n_out L wMax bMax hL hwMax_nn hbMax_nn rest
      xs ys fpL fpRest ih =>
    unfold FpTrace.outputBound
    -- layer's FP output has HasAbsBound (fpL.outputBound wMax xMax bMax).
    have h_L_bound : ∀ j, HasAbsBound (R := R)
        (fpL.outputBound wMax xMax bMax) (fpL.result j) := fun j =>
      ⟨fpL.toVal_abs_le hL hwMax_nn hx hxMax_nn j⟩
    have h_L_nn : 0 ≤ fpL.outputBound wMax xMax bMax :=
      fpL.outputBound_nn hwMax_nn hxMax_nn hbMax_nn
    exact ih h_L_bound h_L_nn k

/-! ## FP-vs-real error bound -/

/-- Error bound for the chain, recursively defined.

At step `cons L rest`, the total error is:

    ε_total = ε_rest (at layer L's FP output)
            + rest.lipschitzK · ε_L

where `ε_L = fpL.errorBound wMax xMax bMax` is layer L's own error,
and `rest.lipschitzK` is the rest chain's Lipschitz amplification of
layer L's error.  The `id` case has zero error. -/
noncomputable def errorBound : ∀ {n_in n_out : ℕ} {C : LayerChain R n_in n_out}
    {xs : Fin n_in → FiniteFp} {ys : Fin n_out → FiniteFp},
    FpTrace C xs ys → R → R  -- xMax → error bound
  | _, _, _, _, _, .id _, _ => 0
  | _, _, _, _, _, @FpTrace.cons _ _ _ _ _ _ _ _ _ _ _ wMax bMax _ _ _
      rest _ _ fpL fpRest, xMax =>
      fpRest.errorBound (fpL.outputBound wMax xMax bMax) +
      rest.lipschitzK * fpL.errorBound wMax xMax bMax

/-- **The whole-chain forward-error bound**, proved by induction on
the trace.  Composes per-layer errors via iterated
`LipschitzMax.errorAmplification` on the downstream chain. -/
theorem forward_error_bound {n_in n_out : ℕ} {C : LayerChain R n_in n_out}
    {xs : Fin n_in → FiniteFp} {ys : Fin n_out → FiniteFp}
    (fpT : FpTrace C xs ys) {xMax : R}
    (hx : ∀ j, HasAbsBound (R := R) xMax (xs j))
    (hxMax_nn : 0 ≤ xMax)
    (k : Fin n_out) :
    |((ys k).toVal : R) -
        C.forward (fun j => ((xs j).toVal : R)) k| ≤
      fpT.errorBound xMax := by
  induction fpT generalizing xMax with
  | id =>
    -- id: ys = xs, C.forward = id.  Error = 0.
    simp [FpTrace.errorBound, LayerChain.forward]
  | @cons n_in n_mid n_out L wMax bMax hL hwMax_nn hbMax_nn rest
      xs ys fpL fpRest ih =>
    -- Goal (under `LayerChain.forward (cons ...) = rest.forward ∘ L.forward`):
    --   |(ys k).toVal - rest.forward (L.forward xs_real) k| ≤ errorBound
    -- Strategy: apply LipschitzMax.errorAmplification on rest's forward.
    -- Outer bound (rest's error at FP-intermediate input fpL.result):
    have h_L_bound : ∀ j, HasAbsBound (R := R)
        (fpL.outputBound wMax xMax bMax) (fpL.result j) := fun j =>
      ⟨fpL.toVal_abs_le hL hwMax_nn hx hxMax_nn j⟩
    have h_L_nn : 0 ≤ fpL.outputBound wMax xMax bMax :=
      fpL.outputBound_nn hwMax_nn hxMax_nn hbMax_nn
    have h_outer : ∀ k', |((ys k').toVal : R) -
        rest.forward (fun j => ((fpL.result j).toVal : R)) k'| ≤
        fpRest.errorBound (fpL.outputBound wMax xMax bMax) :=
      fun k' => ih h_L_bound h_L_nn k'
    -- Inner bound: layer L's own error.
    have h_inner : ∀ j, |((fpL.result j).toVal : R) -
        L.forward (fun l => ((xs l).toVal : R)) j| ≤
        fpL.errorBound wMax xMax bMax := fun j =>
      fpL.forward_error_bound hL hwMax_nn hx hxMax_nn j
    -- rest is Lipschitz with constant rest.lipschitzK.
    have h_rest_lip : LipschitzMax (R := R) rest.lipschitzK rest.forward :=
      rest.forward_lipschitz
    -- Compose via errorAmplification.
    have h_comp := LipschitzMax.errorAmplification h_rest_lip
      (h_outer k) h_inner
    -- h_comp: |(ys k).toVal - rest.forward (L.forward xs_real) k| ≤
    --          fpRest.errorBound ... + rest.lipschitzK · fpL.errorBound ...
    -- That's exactly errorBound (cons ... fpL fpRest) xMax.
    exact h_comp

end FpTrace

/-! ## Demo: N-layer chain

A concrete 3-layer chain built via nested `.cons` demonstrating the
machinery. -/

/-- **3-layer chain demo**: build a 3-layer chain `L1 → L2 → L3`
from three layers with their bounds, producing a `LayerChain`. -/
noncomputable def demo3 {n₀ n₁ n₂ n₃ : ℕ}
    (L1 : Layer n₀ n₁) (L2 : Layer n₁ n₂) (L3 : Layer n₂ n₃)
    {w1Max b1Max w2Max b2Max w3Max b3Max : R}
    (hL1 : BoundedParams (R := R) L1 w1Max b1Max) (hw1_nn : 0 ≤ w1Max)
    (hb1_nn : 0 ≤ b1Max)
    (hL2 : BoundedParams (R := R) L2 w2Max b2Max) (hw2_nn : 0 ≤ w2Max)
    (hb2_nn : 0 ≤ b2Max)
    (hL3 : BoundedParams (R := R) L3 w3Max b3Max) (hw3_nn : 0 ≤ w3Max)
    (hb3_nn : 0 ≤ b3Max) :
    LayerChain R n₀ n₃ :=
  .cons L1 w1Max b1Max hL1 hw1_nn hb1_nn
    (.cons L2 w2Max b2Max hL2 hw2_nn hb2_nn
      (.cons L3 w3Max b3Max hL3 hw3_nn hb3_nn .id))

end LayerChain

end MLP
