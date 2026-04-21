import Flean.Operations.LayerNorm
import Flean.Tags.BoundedRange

/-!
# Tag-Specialized LayerNorm: `IsBoundedRange` Wrapper

**Status**: Phase 2 Stage 6 — bridging scaffold.

## What this file delivers

A minimal wrapper that takes `IsBoundedRange I xs` (Phase 1 tag) and
exposes the `|x_i| ≤ I.maxMag` magnitude bound that downstream
LayerNorm error analyses need.  The full end-to-end forward error
bound is composed via `fpLayerNorm_end_to_end_error_bound` (Phase 2
Stage 5) plus accumulated per-step δ's.

## What the tag dematerializes

Under `IsBoundedRange I xs` with `I.lo` and `I.hi` bounded, the
per-component `|xs_i|` magnitude is automatically available via
`IsBoundedRange.toVal_abs_le`.  This feeds into:

- Bounds on `|shifted_i|` after the mean shift.
- Bounds on `|(shifted_i)²|` after squaring.
- Bounds on `|var|` via the variance sum.

The **full** tag-driven automation — discharging every normal-range
precondition on per-step rounding theorems — requires additional
`IsBoundedRange.fpSub` propagation + lower-bound magnitude reasoning
(the tag gives upper bounds easily, but `≥ 2^min_exp` lower bounds
need separation hypotheses).  That work is scoped for a follow-up
session; see the design doc for scope.

## Minimum bridge

The one concrete deliverable: `fpLayerNorm_tagged_bound`, which
takes an `IsBoundedRange` tag + per-step δ hypotheses (rather than
per-step normal-range hypotheses) and reaches the end-to-end bound.
Normal-range discharging stays manual in this Phase 2 delivery, but
the tag still serves a role: it gives the user a uniform way to
describe input bounds, replacing ad-hoc `|xs_i| ≤ c` scattered
through error-bound hypotheses with a single tag carry-through.
-/

set_option autoImplicit false

namespace Flean.Tags

open LayerNorm

variable [FloatFormat]

/-- **Tagged LayerNorm end-to-end bound** (Phase 2 Stage 6).

Thin tag-aware wrapper around `fpLayerNorm_end_to_end_error_bound`.
The `IsBoundedRange I xs` tag is carried through the statement;
currently its role is to expose `|xs_i| ≤ I.maxMag` via `.toVal_abs_le`
to downstream computations that may need it.

Per-step `δ_shift`, `δ_stddev`, `δ_final` are expected to be derived
by the user from concrete summation adapters + per-step rounding
witnesses (see `Flean/Operations/LayerNorm.lean`'s individual step
theorems).  Future work: discharge these δ's automatically from the
tag + separation hypotheses. -/
theorem fpLayerNorm_tagged_bound
    {n : ℕ} {I : FpInterval ℝ} {xs : Fin n → FiniteFp}
    {shifted : Fin n → FiniteFp} {stddev : FiniteFp}
    {result : Fin n → FiniteFp}
    (_hxs : IsBoundedRange (R := ℝ) I xs)
    (i : Fin n) {eps : ℝ} (heps_pos : 0 < eps)
    (hn_pos_r : 0 < (n : ℝ))
    (h_stddev_pos : 0 < (stddev.toVal : ℝ))
    {δ_shift δ_stddev δ_final : ℝ}
    (h_shift :
      |((shifted i).toVal : ℝ) -
          (((xs i).toVal : ℝ) -
            mean (fun j => ((xs j).toVal : ℝ)))| ≤ δ_shift)
    (h_stddev :
      |((stddev.toVal : ℝ)) -
          Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) + eps)| ≤
        δ_stddev)
    (h_final :
      |((result i).toVal : ℝ) -
          (shifted i).toVal / stddev.toVal| ≤ δ_final) :
    |((result i).toVal : ℝ) -
        layerNorm (fun j => ((xs j).toVal : ℝ)) eps i| ≤
      δ_final + δ_shift / stddev.toVal +
        |((xs i).toVal : ℝ) -
            mean (fun j => ((xs j).toVal : ℝ))| * δ_stddev /
          ((stddev.toVal : ℝ) *
            Real.sqrt (variance (fun j => ((xs j).toVal : ℝ)) + eps)) :=
  fpLayerNorm_end_to_end_error_bound i heps_pos hn_pos_r
    h_stddev_pos h_shift h_stddev h_final

/-- **Magnitude corollary** from the tag: under `IsBoundedRange I xs`,
every input has bounded magnitude.  This is the one immediate value
the tag provides to LayerNorm bounds today. -/
theorem fpLayerNorm_input_abs_le
    {n : ℕ} {I : FpInterval ℝ} {xs : Fin n → FiniteFp}
    (hxs : IsBoundedRange (R := ℝ) I xs) (i : Fin n) :
    |((xs i).toVal : ℝ)| ≤ I.maxMag :=
  hxs.toVal_abs_le i

end Flean.Tags
