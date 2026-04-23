import Flean.Operations.MLP.MLP2
import Flean.Operations.MLP.ActivatedMLP2
import Flean.Operations.CrossEntropy
import Flean.Tags.Prob

/-!
# MLP-on-Cross-Entropy: End-to-End Classification Loss Error Bound

Composes the verified MLP forward pass (`MLP2` / `ActivatedMLP2`) with
the verified cross-entropy pipeline.  Given an FP-computed MLP output
that's close to its real-valued ground truth, and a CE pipeline run on
those FP logits, the composed theorem bounds

```
|loss.toVal − CE(y_real, M.forward(x_real))|
  ≤ ce_err + 2 · Σ|y_i| · mlp_err
```

where

* `ce_err` is the CE pipeline's bound from `FpCrossEntropyResult.error_bound`
  (`|loss − CE(y, xs_fp_real)|`, with `xs_fp_real = xs_fp.toVal`);
* `mlp_err` is the MLP's per-index forward error bound
  (`|xs_fp.toVal − M.forward(x_real)|`);
* `2 · Σ|y_i|` is the Lipschitz constant of `crossEntropy` in its logit
  argument under the L∞ norm (`crossEntropy_lipschitz_logits`).

## Contents

* `MLPCrossEntropy.compose_error_bound` — abstract composition; plug
  any forward-error witness (MLP2 linear, ActivatedMLP2, future N-layer)
  into a CE result.
* `MLP2FpResult.crossEntropy_error_bound` — specialization for the
  linear 2-layer MLP.
* `ActivatedMLP2FpResult.crossEntropy_error_bound` — specialization
  for the activated 2-layer MLP.

Both specializations produce a bound on
`|loss.toVal − CE(y, M.forward(x))|` for the full end-to-end
classifier, composing the respective forward-error bound
(`layer.errorBound`) with the CE pipeline's `error_bound`.
-/

set_option autoImplicit false

namespace MLP

open Finset BigOperators Flean.Tags

variable [FloatFormat]
variable [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

/-! ## Abstract composition

The abstract theorem takes the MLP's output as an already-rounded FP
vector + per-index forward-error bound, plus any CE-vs-FP-logit bound
(typically `FpCrossEntropyResult.error_bound`'s bound), and composes
them via triangle + `crossEntropy_lipschitz_logits`. -/

omit [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound] in
/-- **Abstract end-to-end composition.**

Compose an FP MLP forward-error witness with a CE-vs-FP-logit error
bound to get a bound on the full classification loss relative to the
real-valued ground-truth MLP output. -/
theorem MLPCrossEntropy.compose_error_bound {n : ℕ} (hn : 0 < n)
    (ys : Fin n → FiniteFp) (xs_math : Fin n → ℝ)
    (xs_fp : Fin n → FiniteFp) (mlp_err : ℝ)
    (h_mlp : ∀ k, |((xs_fp k).toVal : ℝ) - xs_math k| ≤ mlp_err)
    (loss : ℝ) (ce_err : ℝ)
    (h_ce : |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((xs_fp i).toVal : ℝ))| ≤ ce_err) :
    |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ)) xs_math| ≤
      ce_err + 2 * (∑ i, |((ys i).toVal : ℝ)|) * mlp_err := by
  -- Lipschitz bound on CE w.r.t. logits.
  have h_lip := CrossEntropy.crossEntropy_lipschitz_logits hn
    (fun i => ((ys i).toVal : ℝ))
    (fun i => ((xs_fp i).toVal : ℝ)) xs_math h_mlp
  -- Triangle: loss vs CE(y, xs_math) decomposes via CE(y, xs_fp).
  have h_split : loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ)) xs_math =
      (loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((xs_fp i).toVal : ℝ))) +
      (CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((xs_fp i).toVal : ℝ)) -
       CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ)) xs_math) := by ring
  calc |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ)) xs_math|
      = |(loss - CrossEntropy.crossEntropy
           (fun i => ((ys i).toVal : ℝ))
           (fun i => ((xs_fp i).toVal : ℝ))) +
         (CrossEntropy.crossEntropy
           (fun i => ((ys i).toVal : ℝ))
           (fun i => ((xs_fp i).toVal : ℝ)) -
          CrossEntropy.crossEntropy
           (fun i => ((ys i).toVal : ℝ)) xs_math)| := by
        rw [← h_split]
    _ ≤ |loss - CrossEntropy.crossEntropy
            (fun i => ((ys i).toVal : ℝ))
            (fun i => ((xs_fp i).toVal : ℝ))| +
        |CrossEntropy.crossEntropy
            (fun i => ((ys i).toVal : ℝ))
            (fun i => ((xs_fp i).toVal : ℝ)) -
          CrossEntropy.crossEntropy
            (fun i => ((ys i).toVal : ℝ)) xs_math| := abs_add_le _ _
    _ ≤ ce_err + 2 * (∑ i, |((ys i).toVal : ℝ)|) * mlp_err := by linarith

/-! ## MLP2 (linear) — CE specialization

The concrete composition for the linear 2-layer MLP.  Takes the MLP
bounded-parameters witness + input magnitude tag, derives the per-index
MLP forward error from `MLP2FpResult.forward_error_bound`, and plugs
into `MLPCrossEntropy.compose_error_bound`. -/

omit [RModeSticky ℝ] [ExpApprox] [ExpApproxSound] in
/-- **End-to-end classification-loss error bound (linear MLP2).**

Combines the linear 2-layer MLP forward error with the CE pipeline
bound, giving a bound on the full loss `|loss.toVal − CE(y, M.forward(x))|`. -/
theorem MLP2FpResult.crossEntropy_error_bound
    {n_in n_hidden n_out : ℕ} (hn_out : 0 < n_out)
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (M_res : MLP2FpResult M x ℝ)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : MLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (ys : Fin n_out → FiniteFp)
    (loss : ℝ) (ce_err : ℝ)
    (h_ce : |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((M_res.layer2.result i).toVal : ℝ))| ≤ ce_err) :
    |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (M.forward (fun j => ((x j).toVal : ℝ)))| ≤
      ce_err + 2 * (∑ i, |((ys i).toVal : ℝ)|) *
        M_res.errorBound w1Max xMax b1Max w2Max b2Max := by
  have h_mlp : ∀ k, |((M_res.layer2.result k).toVal : ℝ) -
      M.forward (fun j => ((x j).toVal : ℝ)) k| ≤
      M_res.errorBound w1Max xMax b1Max w2Max b2Max := fun k =>
    M_res.forward_error_bound hM hw1_nn hb1_nn hw2_nn hx hxMax_nn k
  exact MLPCrossEntropy.compose_error_bound hn_out ys
    (M.forward (fun j => ((x j).toVal : ℝ)))
    M_res.layer2.result (M_res.errorBound w1Max xMax b1Max w2Max b2Max)
    h_mlp loss ce_err h_ce

/-! ## ActivatedMLP2 — CE specialization

Same shape as the linear case, but uses the activated 2-layer forward
error bound (which absorbs both the rounding and the activation slack
for each layer). -/

omit [RModeSticky ℝ] [ExpApprox] [ExpApproxSound] in
/-- **End-to-end classification-loss error bound (activated MLP2).**

Combines the activated 2-layer MLP forward error with the CE pipeline
bound.  The MLP-side contribution to the classification loss is

```
2 · Σ|y_i| · (layer2.errorBound + σ₂.K · n_hidden · w2Max · layer1.errorBound)
```

where each `layer.errorBound` already includes the per-layer activation
slack. -/
theorem ActivatedMLP2FpResult.crossEntropy_error_bound
    {n_in n_hidden n_out : ℕ} (hn_out : 0 < n_out)
    {M : ActivatedMLP2 ℝ n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (M_res : ActivatedMLP2FpResult M x)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : ActivatedMLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (ys : Fin n_out → FiniteFp)
    (loss : ℝ) (ce_err : ℝ)
    (h_ce : |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((M_res.layer2.activated.result i).toVal : ℝ))|
          ≤ ce_err) :
    |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (M.forward (fun j => ((x j).toVal : ℝ)))| ≤
      ce_err + 2 * (∑ i, |((ys i).toVal : ℝ)|) *
        M_res.errorBound w1Max xMax b1Max w2Max b2Max := by
  have h_mlp : ∀ k, |((M_res.layer2.activated.result k).toVal : ℝ) -
      M.forward (fun j => ((x j).toVal : ℝ)) k| ≤
      M_res.errorBound w1Max xMax b1Max w2Max b2Max := fun k =>
    M_res.forward_error_bound hM hw1_nn hb1_nn hw2_nn hx hxMax_nn k
  exact MLPCrossEntropy.compose_error_bound hn_out ys
    (M.forward (fun j => ((x j).toVal : ℝ)))
    M_res.layer2.activated.result
    (M_res.errorBound w1Max xMax b1Max w2Max b2Max)
    h_mlp loss ce_err h_ce

/-! ## Convenience: bind to `FpCrossEntropyResult`

When the caller has a `FpCrossEntropyResult` witness, its `.error_bound`
method supplies the CE-vs-FP-logit piece automatically.  Pair it with a
linear or activated MLP forward result for a direct end-to-end bound. -/

/-- Linear MLP2 + `FpCrossEntropyResult` bundle: end-to-end bound with
`ce_err` supplied by `ce_res.error_bound`.  Abstracts the `ce_err`
expression into an opaque upper bound `ce_err_sup` so the statement
stays readable. -/
theorem MLP2FpResult.crossEntropy_error_bound_of_res
    {n_in n_hidden n_out : ℕ} (hn_out : 0 < n_out)
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (M_res : MLP2FpResult M x ℝ)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : MLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    {ys : Fin n_out → FiniteFp}
    (ce_res : CrossEntropy.FpCrossEntropyResult
      M_res.layer2.result ys hn_out)
    (ce_err_sup : ℝ)
    (h_ce_sup :
      letI ε_sum : ℝ :=
        ((η : ℝ) + ce_res.sum.relErr * (1 + (η : ℝ))) +
          (1 + ce_res.sum.relErr) * (n_out : ℝ) * Softmax.subnormalConst
      letI D_log : ℝ := ε_sum / (1 - ε_sum)
      letI Δ_LSE : ℝ :=
        (η : ℝ) * |LogSumExp.logsumexp
          (fun j => ((M_res.layer2.result j).toVal : ℝ))| +
        (1 + (η : ℝ)) *
          (ce_res.η_log *
              (LogSumExp.logsumexp
                (fun j => ((M_res.layer2.result j).toVal : ℝ)) -
                ((Softmax.fpMax M_res.layer2.result hn_out).toVal : ℝ)) +
            (1 + ce_res.η_log) * D_log + ce_res.logSubConst) +
        Softmax.subnormalConst
      ce_res.dp.relErr *
          ∑ i, |((ys i).toVal : ℝ) * ((ce_res.r i).toVal : ℝ)| +
        ∑ i, |((ys i).toVal : ℝ)| *
          ((η : ℝ) *
              |((M_res.layer2.result i).toVal : ℝ) - (ce_res.lse.toVal : ℝ)| +
            Softmax.subnormalConst + Δ_LSE) ≤ ce_err_sup) :
    |(ce_res.loss.toVal : ℝ) - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (M.forward (fun j => ((x j).toVal : ℝ)))| ≤
      ce_err_sup + 2 * (∑ i, |((ys i).toVal : ℝ)|) *
        M_res.errorBound w1Max xMax b1Max w2Max b2Max := by
  have h_ce := ce_res.error_bound
  have h_ce_sup' : |(ce_res.loss.toVal : ℝ) -
      CrossEntropy.crossEntropy (fun i => ((ys i).toVal : ℝ))
        (fun i => ((M_res.layer2.result i).toVal : ℝ))| ≤ ce_err_sup :=
    le_trans h_ce h_ce_sup
  exact M_res.crossEntropy_error_bound hn_out hM hw1_nn hb1_nn hw2_nn
    hx hxMax_nn ys (ce_res.loss.toVal : ℝ) ce_err_sup h_ce_sup'

/-! ## `IsProb` tightenings

When the target vector `ys` satisfies `IsProb` (non-negative, total
mass at most 1), `Σ|y_i| = Σ y_i ≤ 1`, so the Lipschitz amplification
factor `2 · Σ|y_i|` tightens to `2`:

```
|loss.toVal − CE(y, M.forward(x_real))| ≤ ce_err + 2 · mlp_err
```

This is the realistic shape for classification: `ys` is typically a
one-hot or soft-label probability vector, so `IsProb` holds. -/

omit [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound] in
/-- **Abstract composition, tightened under `IsProb`.**

Same shape as `MLPCrossEntropy.compose_error_bound` but uses
`IsProb.sum_abs_le_one` to drop the `Σ|y_i|` coefficient to `1`. -/
theorem MLPCrossEntropy.compose_error_bound_of_isProb {n : ℕ}
    (hn : 0 < n) (ys : Fin n → FiniteFp)
    (h_prob : Flean.Tags.IsProb (R := ℝ) ys)
    (xs_math : Fin n → ℝ)
    (xs_fp : Fin n → FiniteFp) (mlp_err : ℝ) (h_mlp_nn : 0 ≤ mlp_err)
    (h_mlp : ∀ k, |((xs_fp k).toVal : ℝ) - xs_math k| ≤ mlp_err)
    (loss : ℝ) (ce_err : ℝ)
    (h_ce : |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((xs_fp i).toVal : ℝ))| ≤ ce_err) :
    |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ)) xs_math| ≤
      ce_err + 2 * mlp_err := by
  have h_base := MLPCrossEntropy.compose_error_bound hn ys xs_math
    xs_fp mlp_err h_mlp loss ce_err h_ce
  have h_sum_le := h_prob.sum_abs_le_one (R := ℝ)
  have h_tighten :
      2 * (∑ i, |((ys i).toVal : ℝ)|) * mlp_err ≤ 2 * mlp_err := by
    have h : (∑ i, |((ys i).toVal : ℝ)|) * mlp_err ≤ 1 * mlp_err :=
      mul_le_mul_of_nonneg_right h_sum_le h_mlp_nn
    linarith
  linarith

omit [RModeSticky ℝ] [ExpApprox] [ExpApproxSound] in
/-- **End-to-end classification-loss error bound, tightened (linear MLP2).**

Under `IsProb ys`, the MLP-side contribution to the loss bound
tightens to `2 · M_res.errorBound`. -/
theorem MLP2FpResult.crossEntropy_error_bound_of_isProb
    {n_in n_hidden n_out : ℕ} (hn_out : 0 < n_out)
    {M : MLP2 n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (M_res : MLP2FpResult M x ℝ)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : MLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (ys : Fin n_out → FiniteFp)
    (h_prob : Flean.Tags.IsProb (R := ℝ) ys)
    (loss : ℝ) (ce_err : ℝ)
    (h_ce : |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((M_res.layer2.result i).toVal : ℝ))| ≤ ce_err) :
    |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (M.forward (fun j => ((x j).toVal : ℝ)))| ≤
      ce_err + 2 * M_res.errorBound w1Max xMax b1Max w2Max b2Max := by
  have h_mlp : ∀ k, |((M_res.layer2.result k).toVal : ℝ) -
      M.forward (fun j => ((x j).toVal : ℝ)) k| ≤
      M_res.errorBound w1Max xMax b1Max w2Max b2Max := fun k =>
    M_res.forward_error_bound hM hw1_nn hb1_nn hw2_nn hx hxMax_nn k
  have h_err_nn : 0 ≤ M_res.errorBound w1Max xMax b1Max w2Max b2Max :=
    le_trans (abs_nonneg _) (h_mlp ⟨0, hn_out⟩)
  exact MLPCrossEntropy.compose_error_bound_of_isProb hn_out ys h_prob
    (M.forward (fun j => ((x j).toVal : ℝ)))
    M_res.layer2.result (M_res.errorBound w1Max xMax b1Max w2Max b2Max)
    h_err_nn h_mlp loss ce_err h_ce

omit [RModeSticky ℝ] [ExpApprox] [ExpApproxSound] in
/-- **End-to-end classification-loss error bound, tightened (activated MLP2).**

Under `IsProb ys`, the MLP-side contribution tightens to
`2 · M_res.errorBound` (the full activated-layer error including
per-layer activation slack). -/
theorem ActivatedMLP2FpResult.crossEntropy_error_bound_of_isProb
    {n_in n_hidden n_out : ℕ} (hn_out : 0 < n_out)
    {M : ActivatedMLP2 ℝ n_in n_hidden n_out} {x : Fin n_in → FiniteFp}
    (M_res : ActivatedMLP2FpResult M x)
    {w1Max b1Max w2Max b2Max : ℝ}
    (hM : ActivatedMLP2BoundedParams (R := ℝ) M w1Max b1Max w2Max b2Max)
    (hw1_nn : 0 ≤ w1Max) (hb1_nn : 0 ≤ b1Max) (hw2_nn : 0 ≤ w2Max)
    {xMax : ℝ} (hx : ∀ j, HasAbsBound (R := ℝ) xMax (x j))
    (hxMax_nn : 0 ≤ xMax)
    (ys : Fin n_out → FiniteFp)
    (h_prob : Flean.Tags.IsProb (R := ℝ) ys)
    (loss : ℝ) (ce_err : ℝ)
    (h_ce : |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (fun i => ((M_res.layer2.activated.result i).toVal : ℝ))|
          ≤ ce_err) :
    |loss - CrossEntropy.crossEntropy
        (fun i => ((ys i).toVal : ℝ))
        (M.forward (fun j => ((x j).toVal : ℝ)))| ≤
      ce_err + 2 * M_res.errorBound w1Max xMax b1Max w2Max b2Max := by
  have h_mlp : ∀ k, |((M_res.layer2.activated.result k).toVal : ℝ) -
      M.forward (fun j => ((x j).toVal : ℝ)) k| ≤
      M_res.errorBound w1Max xMax b1Max w2Max b2Max := fun k =>
    M_res.forward_error_bound hM hw1_nn hb1_nn hw2_nn hx hxMax_nn k
  have h_err_nn : 0 ≤ M_res.errorBound w1Max xMax b1Max w2Max b2Max :=
    le_trans (abs_nonneg _) (h_mlp ⟨0, hn_out⟩)
  exact MLPCrossEntropy.compose_error_bound_of_isProb hn_out ys h_prob
    (M.forward (fun j => ((x j).toVal : ℝ)))
    M_res.layer2.activated.result
    (M_res.errorBound w1Max xMax b1Max w2Max b2Max)
    h_err_nn h_mlp loss ce_err h_ce

end MLP
