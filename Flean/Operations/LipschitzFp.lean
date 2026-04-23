import Flean.Operations.Lipschitz
import Flean.Operations.Add
import Flean.Operations.Sub
import Flean.Operations.Mul
import Flean.Operations.FpFiniteRound
import Flean.Rounding.RoundPreserves
import Flean.Tags.FpInterval

/-!
# Per-FP-op Lipschitz-with-slack instances

Companion to `Flean/Operations/Lipschitz.lean`.  The math-level
framework there operates on `(Fin m → R) → Fin n → R` functions; FP
operations have signature `FiniteFp → ... → Fp` (possibly non-finite).
This file introduces an FP-typed Lipschitz-with-slack notion
(`LipschitzMaxFpSlackOn`) and concrete instances for `fpAddFinite`,
`fpSubFinite`, and `fpMulFinite`.

For *math-level* Lipschitz-with-slack (e.g., a Taylor-truncated
function), use `LipschitzMaxOn M K g + ApproximatesUniformly c f g`
plus `LipschitzMaxOn.approximatedBound` from `Lipschitz.lean` — the
FP slack notion here is a separate construct because rounding-slack
is intrinsic to FP ops (no underlying exact-Lipschitz FP function
exists to approximate).

## Design

* `LipschitzMaxFpSlackOn M K c f` — FP-op slack-Lipschitz claim,
  valid on inputs with `|.toVal| ≤ M`.  `M` is a struct parameter
  because the rounding slack depends on input magnitudes.
* Total extensions (`fpAddFinite_safeT` etc.) wrap the partial FP ops;
  non-finite results map to zero.  The slack claim holds only for
  inputs where the op in fact returns finite — this is an external
  premise, supplied as `h_finite : ∀ a b ∈ M-ball, ∃ r, op a b = Fp.finite r`.
* Composition rules are deferred; this file ships the notion + proof
  that it's inhabited for the core binary ops.

## Contents

* `LipschitzMaxFpSlackOn` struct + `K_nn`/`c_nn` fields.
* Per-instance FP error bounds: `fpAddFinite_unified_error`,
  `fpSubFinite_unified_error`, `fpMulFinite_unified_error`.
* Total wrappers: `fpAddFinite_safeT`, `fpSubFinite_safeT`,
  `fpMulFinite_safeT`.
* Concrete slack instances: `fpAddFinite_lipschitz_with_slack_on`,
  `fpSubFinite_lipschitz_with_slack_on`,
  `fpMulFinite_lipschitz_with_slack_on`.
-/

set_option autoImplicit false

namespace Flean.Lipschitz

open Flean.Tags

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable [FloatFormat]
variable [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
  [RModeConj R] [RModeZero R]

/-! ## The notion -/

/-- FP-typed Lipschitz-with-slack notion, valid on inputs whose
per-component `.toVal` magnitude is bounded by `M`.

The `M` parameter is essential: FP rounding slack scales with input
magnitude, so there is no truly uniform Lipschitz-with-slack claim
over all `FiniteFp → FiniteFp` inputs. -/
structure LipschitzMaxFpSlackOn {m n : ℕ} (M K c : R)
    (f : (Fin m → FiniteFp) → Fin n → FiniteFp) : Prop where
  /-- Lipschitz constant is non-negative. -/
  K_nn : 0 ≤ K
  /-- Slack is non-negative. -/
  c_nn : 0 ≤ c
  /-- The slack-Lipschitz bound on M-bounded inputs. -/
  bound : ∀ (x x' : Fin m → FiniteFp),
    (∀ j, |((x j).toVal : R)| ≤ M) →
    (∀ j, |((x' j).toVal : R)| ≤ M) →
    ∀ {δ : R}, (∀ j, |((x j).toVal : R) - ((x' j).toVal : R)| ≤ δ) →
    ∀ i, |((f x i).toVal : R) - ((f x' i).toVal : R)| ≤ K * δ + c

/-! ## Per-instance FP error bounds

Subnormal-tolerant combination of `fp{Add,Sub,Mul}Finite_round_witness`
with `round_preserves_abs_error_unified`. -/

/-- Subnormal-tolerant FP-vs-math error for `fpAddFinite`. -/
theorem fpAddFinite_unified_error
    (x y : FiniteFp) {f : FiniteFp}
    (hf : fpAddFinite x y = Fp.finite f) :
    |((f.toVal : R)) - ((x.toVal : R) + y.toVal)| ≤
      (η : R) * |((x.toVal : R) + y.toVal)| + FpInterval.subnormalConst := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have h := round_preserves_abs_error_unified (R := R)
    ((x.toVal : R) + y.toVal) hg_round
  unfold FpInterval.subnormalConst
  rw [hg_eq] at h
  exact h

/-- Subnormal-tolerant FP-vs-math error for `fpMulFinite`. -/
theorem fpMulFinite_unified_error
    (x y : FiniteFp) {f : FiniteFp}
    (hf : fpMulFinite x y = Fp.finite f) :
    |((f.toVal : R)) - ((x.toVal : R) * y.toVal)| ≤
      (η : R) * |((x.toVal : R) * y.toVal)| + FpInterval.subnormalConst := by
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have h := round_preserves_abs_error_unified (R := R)
    ((x.toVal : R) * y.toVal) hg_round
  unfold FpInterval.subnormalConst
  rw [hg_eq] at h
  exact h

/-! ## Total wrappers

`fpAddFinite`/`fpMulFinite` return `Fp`, which may be non-finite on
overflow.  The `_safeT` extensions map non-finite results to `0` so
the Lipschitz-with-slack claim can be stated on a total function.
The claim is vacuous on overflowing inputs — the `M`-bounded
hypothesis is what ensures non-overflow in practice. -/

/-- Total extension of `fpAddFinite`: non-finite → 0. -/
noncomputable def fpAddFinite_safeT (a b : FiniteFp) : FiniteFp :=
  match fpAddFinite a b with
  | Fp.finite r => r
  | _ => 0

/-- Total extension of `fpMulFinite`: non-finite → 0. -/
noncomputable def fpMulFinite_safeT (a b : FiniteFp) : FiniteFp :=
  match fpMulFinite a b with
  | Fp.finite r => r
  | _ => 0

theorem fpAddFinite_safeT_eq_of_finite (a b : FiniteFp) {r : FiniteFp}
    (h : fpAddFinite a b = Fp.finite r) : fpAddFinite_safeT a b = r := by
  unfold fpAddFinite_safeT; rw [h]

theorem fpMulFinite_safeT_eq_of_finite (a b : FiniteFp) {r : FiniteFp}
    (h : fpMulFinite a b = Fp.finite r) : fpMulFinite_safeT a b = r := by
  unfold fpMulFinite_safeT; rw [h]

/-! ## Slack instances

Shape-shared recipe: (math-op-Lipschitz × M-magnitude-bound) → per-op
slack via triangle on both endpoints.  Factored out for readability.

For each binary op `fpOp(a, b) ↔ mathOp(a, b)`:
* Math `mathOp` is `K_math`-Lipschitz on L∞-pairs (add: 2, mul: 2M).
* Per-instance error: `|(fpOp a b).toVal - mathOp(a, b)| ≤ η · g(a, b) + sc` where `g` bounds on M-balls.
* Slack result: `K = K_math`, `c = 2 · (η · g_max + sc)`. -/

/-- `fpAddFinite` is Lipschitz-with-slack on M-bounded inputs.

K = 2 (L∞ pair-Lipschitz of math `+`).
c = 2 · (η · 2M + subnormalConst). -/
theorem fpAddFinite_lipschitz_with_slack_on
    {M : R} (hM_nn : 0 ≤ M)
    (h_finite : ∀ (a b : FiniteFp),
      |(a.toVal : R)| ≤ M → |(b.toVal : R)| ≤ M →
        ∃ r, fpAddFinite a b = Fp.finite r) :
    LipschitzMaxFpSlackOn (R := R) M 2
      (2 * ((η : R) * (2 * M) + FpInterval.subnormalConst))
      (fun (x : Fin 2 → FiniteFp) (_ : Fin 1) =>
        fpAddFinite_safeT (x 0) (x 1)) where
  K_nn := by norm_num
  c_nn := by
    have hη_nn : (0 : R) ≤ (η : R) := by positivity
    have h2M_nn : (0 : R) ≤ 2 * M := by linarith
    have hsc_nn := FpInterval.subnormalConst_nn (R := R)
    have : (0 : R) ≤ (η : R) * (2 * M) := mul_nonneg hη_nn h2M_nn
    linarith
  bound := by
    intro x x' hx_M hx'_M δ h_dx _
    -- Finiteness witnesses + safeT reductions.
    obtain ⟨r, hr⟩ := h_finite (x 0) (x 1) (hx_M 0) (hx_M 1)
    obtain ⟨r', hr'⟩ := h_finite (x' 0) (x' 1) (hx'_M 0) (hx'_M 1)
    rw [fpAddFinite_safeT_eq_of_finite _ _ hr,
        fpAddFinite_safeT_eq_of_finite _ _ hr']
    -- Per-instance FP-vs-math errors.
    have h_err := fpAddFinite_unified_error (R := R) (x 0) (x 1) hr
    have h_err' := fpAddFinite_unified_error (R := R) (x' 0) (x' 1) hr'
    -- |sum| ≤ 2M, |sum'| ≤ 2M.
    have h_sum_bound : |((x 0).toVal : R) + ((x 1).toVal : R)| ≤ 2 * M := by
      calc |((x 0).toVal : R) + ((x 1).toVal : R)|
          ≤ |((x 0).toVal : R)| + |((x 1).toVal : R)| := abs_add_le _ _
        _ ≤ M + M := by linarith [hx_M 0, hx_M 1]
        _ = 2 * M := by ring
    have h_sum'_bound : |((x' 0).toVal : R) + ((x' 1).toVal : R)| ≤ 2 * M := by
      calc |((x' 0).toVal : R) + ((x' 1).toVal : R)|
          ≤ |((x' 0).toVal : R)| + |((x' 1).toVal : R)| := abs_add_le _ _
        _ ≤ M + M := by linarith [hx'_M 0, hx'_M 1]
        _ = 2 * M := by ring
    have hη_nn : (0 : R) ≤ (η : R) := by positivity
    have h_err_scaled : (η : R) * |((x 0).toVal : R) + ((x 1).toVal : R)|
        ≤ (η : R) * (2 * M) :=
      mul_le_mul_of_nonneg_left h_sum_bound hη_nn
    have h_err'_scaled : (η : R) * |((x' 0).toVal : R) + ((x' 1).toVal : R)|
        ≤ (η : R) * (2 * M) :=
      mul_le_mul_of_nonneg_left h_sum'_bound hη_nn
    -- Math-sum perturbation ≤ 2δ.
    have h_sum_diff :
        |(((x 0).toVal : R) + (x 1).toVal) -
          (((x' 0).toVal : R) + (x' 1).toVal)| ≤ 2 * δ := by
      calc |(((x 0).toVal : R) + (x 1).toVal) -
              (((x' 0).toVal : R) + (x' 1).toVal)|
          = |(((x 0).toVal : R) - (x' 0).toVal) +
              (((x 1).toVal : R) - (x' 1).toVal)| := by
            congr 1; ring
        _ ≤ |((x 0).toVal : R) - (x' 0).toVal| +
              |((x 1).toVal : R) - (x' 1).toVal| := abs_add_le _ _
        _ ≤ δ + δ := by linarith [h_dx 0, h_dx 1]
        _ = 2 * δ := by ring
    -- Triangle: |r - r'| ≤ |r - sum| + |sum - sum'| + |sum' - r'|.
    have h_triangle : |(r.toVal : R) - r'.toVal|
        ≤ |(r.toVal : R) - (((x 0).toVal : R) + (x 1).toVal)|
          + |(((x 0).toVal : R) + (x 1).toVal) -
              (((x' 0).toVal : R) + (x' 1).toVal)|
          + |(((x' 0).toVal : R) + (x' 1).toVal) - (r'.toVal : R)| := by
      have h_split : (r.toVal : R) - r'.toVal =
          ((r.toVal : R) - (((x 0).toVal : R) + (x 1).toVal))
          + ((((x 0).toVal : R) + (x 1).toVal) -
              (((x' 0).toVal : R) + (x' 1).toVal))
          + ((((x' 0).toVal : R) + (x' 1).toVal) - (r'.toVal : R)) := by ring
      calc |(r.toVal : R) - r'.toVal|
          = |((r.toVal : R) - (((x 0).toVal : R) + (x 1).toVal))
              + ((((x 0).toVal : R) + (x 1).toVal) -
                  (((x' 0).toVal : R) + (x' 1).toVal))
              + ((((x' 0).toVal : R) + (x' 1).toVal) - (r'.toVal : R))| := by
            rw [← h_split]
        _ ≤ |((r.toVal : R) - (((x 0).toVal : R) + (x 1).toVal))
              + ((((x 0).toVal : R) + (x 1).toVal) -
                  (((x' 0).toVal : R) + (x' 1).toVal))|
            + |(((x' 0).toVal : R) + (x' 1).toVal) - (r'.toVal : R)| :=
          abs_add_le _ _
        _ ≤ (|(r.toVal : R) - (((x 0).toVal : R) + (x 1).toVal)|
              + |(((x 0).toVal : R) + (x 1).toVal) -
                  (((x' 0).toVal : R) + (x' 1).toVal)|)
            + |(((x' 0).toVal : R) + (x' 1).toVal) - (r'.toVal : R)| := by
            linarith [abs_add_le ((r.toVal : R) - (((x 0).toVal : R) + (x 1).toVal))
              ((((x 0).toVal : R) + (x 1).toVal) -
                (((x' 0).toVal : R) + (x' 1).toVal))]
    -- Flip the third |.| via abs_sub_comm.
    have h_err'_flip :
        |(((x' 0).toVal : R) + (x' 1).toVal) - (r'.toVal : R)|
          = |(r'.toVal : R) - (((x' 0).toVal : R) + (x' 1).toVal)| :=
      abs_sub_comm _ _
    rw [h_err'_flip] at h_triangle
    have hsc_nn := FpInterval.subnormalConst_nn (R := R)
    linarith

/-- Total extension of `fpSubFinite`: non-finite → 0. -/
noncomputable def fpSubFinite_safeT (a b : FiniteFp) : FiniteFp :=
  match fpSubFinite a b with
  | Fp.finite r => r
  | _ => 0

theorem fpSubFinite_safeT_eq_of_finite (a b : FiniteFp) {r : FiniteFp}
    (h : fpSubFinite a b = Fp.finite r) : fpSubFinite_safeT a b = r := by
  unfold fpSubFinite_safeT; rw [h]

/-- Subnormal-tolerant FP-vs-math error for `fpSubFinite`.  Derived
from `fpAddFinite_unified_error` via the identity
`fpSubFinite a b = fpAddFinite a (-b)`. -/
theorem fpSubFinite_unified_error
    (x y : FiniteFp) {f : FiniteFp}
    (hf : fpSubFinite x y = Fp.finite f) :
    |((f.toVal : R)) - ((x.toVal : R) - y.toVal)| ≤
      (η : R) * |((x.toVal : R) - y.toVal)| + FpInterval.subnormalConst := by
  -- `fpSubFinite x y` reduces definitionally to `fpAddFinite x (-y)`.
  have hf' : fpAddFinite x (-y) = Fp.finite f := hf
  have h := fpAddFinite_unified_error (R := R) x (-y) hf'
  rw [FiniteFp.toVal_neg_eq_neg,
      show (x.toVal : R) + -(y.toVal) = (x.toVal : R) - y.toVal from by ring] at h
  exact h

/-- `fpSubFinite` is Lipschitz-with-slack on M-bounded inputs.

K = 2, slack = 2·(η·2M + subnormalConst).  Mirrors `fpAddFinite`'s
shape since `|x - y| ≤ |x| + |y| ≤ 2M` and the math difference is
2-Lipschitz in L∞. -/
theorem fpSubFinite_lipschitz_with_slack_on
    {M : R} (hM_nn : 0 ≤ M)
    (h_finite : ∀ (a b : FiniteFp),
      |(a.toVal : R)| ≤ M → |(b.toVal : R)| ≤ M →
        ∃ r, fpSubFinite a b = Fp.finite r) :
    LipschitzMaxFpSlackOn (R := R) M 2
      (2 * ((η : R) * (2 * M) + FpInterval.subnormalConst))
      (fun (x : Fin 2 → FiniteFp) (_ : Fin 1) =>
        fpSubFinite_safeT (x 0) (x 1)) where
  K_nn := by norm_num
  c_nn := by
    have hη_nn : (0 : R) ≤ (η : R) := by positivity
    have h2M_nn : (0 : R) ≤ 2 * M := by linarith
    have hsc_nn := FpInterval.subnormalConst_nn (R := R)
    have : (0 : R) ≤ (η : R) * (2 * M) := mul_nonneg hη_nn h2M_nn
    linarith
  bound := by
    intro x x' hx_M hx'_M δ h_dx _
    obtain ⟨r, hr⟩ := h_finite (x 0) (x 1) (hx_M 0) (hx_M 1)
    obtain ⟨r', hr'⟩ := h_finite (x' 0) (x' 1) (hx'_M 0) (hx'_M 1)
    rw [fpSubFinite_safeT_eq_of_finite _ _ hr,
        fpSubFinite_safeT_eq_of_finite _ _ hr']
    have h_err := fpSubFinite_unified_error (R := R) (x 0) (x 1) hr
    have h_err' := fpSubFinite_unified_error (R := R) (x' 0) (x' 1) hr'
    have h_diff_bound : |((x 0).toVal : R) - ((x 1).toVal : R)| ≤ 2 * M := by
      calc |((x 0).toVal : R) - ((x 1).toVal : R)|
          ≤ |((x 0).toVal : R)| + |((x 1).toVal : R)| := abs_sub _ _
        _ ≤ M + M := by linarith [hx_M 0, hx_M 1]
        _ = 2 * M := by ring
    have h_diff'_bound : |((x' 0).toVal : R) - ((x' 1).toVal : R)| ≤ 2 * M := by
      calc |((x' 0).toVal : R) - ((x' 1).toVal : R)|
          ≤ |((x' 0).toVal : R)| + |((x' 1).toVal : R)| := abs_sub _ _
        _ ≤ M + M := by linarith [hx'_M 0, hx'_M 1]
        _ = 2 * M := by ring
    have hη_nn : (0 : R) ≤ (η : R) := by positivity
    have h_err_scaled : (η : R) * |((x 0).toVal : R) - ((x 1).toVal : R)|
        ≤ (η : R) * (2 * M) :=
      mul_le_mul_of_nonneg_left h_diff_bound hη_nn
    have h_err'_scaled : (η : R) * |((x' 0).toVal : R) - ((x' 1).toVal : R)|
        ≤ (η : R) * (2 * M) :=
      mul_le_mul_of_nonneg_left h_diff'_bound hη_nn
    have h_diff_diff :
        |(((x 0).toVal : R) - (x 1).toVal) -
          (((x' 0).toVal : R) - (x' 1).toVal)| ≤ 2 * δ := by
      calc |(((x 0).toVal : R) - (x 1).toVal) -
              (((x' 0).toVal : R) - (x' 1).toVal)|
          = |(((x 0).toVal : R) - (x' 0).toVal) -
              (((x 1).toVal : R) - (x' 1).toVal)| := by congr 1; ring
        _ ≤ |((x 0).toVal : R) - (x' 0).toVal| +
              |((x 1).toVal : R) - (x' 1).toVal| := abs_sub _ _
        _ ≤ δ + δ := by linarith [h_dx 0, h_dx 1]
        _ = 2 * δ := by ring
    have h_triangle : |(r.toVal : R) - r'.toVal|
        ≤ |(r.toVal : R) - (((x 0).toVal : R) - (x 1).toVal)|
          + |(((x 0).toVal : R) - (x 1).toVal) -
              (((x' 0).toVal : R) - (x' 1).toVal)|
          + |(((x' 0).toVal : R) - (x' 1).toVal) - (r'.toVal : R)| := by
      have h_split : (r.toVal : R) - r'.toVal =
          ((r.toVal : R) - (((x 0).toVal : R) - (x 1).toVal))
          + ((((x 0).toVal : R) - (x 1).toVal) -
              (((x' 0).toVal : R) - (x' 1).toVal))
          + ((((x' 0).toVal : R) - (x' 1).toVal) - (r'.toVal : R)) := by ring
      calc |(r.toVal : R) - r'.toVal|
          = |((r.toVal : R) - (((x 0).toVal : R) - (x 1).toVal))
              + ((((x 0).toVal : R) - (x 1).toVal) -
                  (((x' 0).toVal : R) - (x' 1).toVal))
              + ((((x' 0).toVal : R) - (x' 1).toVal) - (r'.toVal : R))| := by
            rw [← h_split]
        _ ≤ |((r.toVal : R) - (((x 0).toVal : R) - (x 1).toVal))
              + ((((x 0).toVal : R) - (x 1).toVal) -
                  (((x' 0).toVal : R) - (x' 1).toVal))|
            + |(((x' 0).toVal : R) - (x' 1).toVal) - (r'.toVal : R)| :=
          abs_add_le _ _
        _ ≤ (|(r.toVal : R) - (((x 0).toVal : R) - (x 1).toVal)|
              + |(((x 0).toVal : R) - (x 1).toVal) -
                  (((x' 0).toVal : R) - (x' 1).toVal)|)
            + |(((x' 0).toVal : R) - (x' 1).toVal) - (r'.toVal : R)| := by
            linarith [abs_add_le ((r.toVal : R) - (((x 0).toVal : R) - (x 1).toVal))
              ((((x 0).toVal : R) - (x 1).toVal) -
                (((x' 0).toVal : R) - (x' 1).toVal))]
    have h_err'_flip :
        |(((x' 0).toVal : R) - (x' 1).toVal) - (r'.toVal : R)|
          = |(r'.toVal : R) - (((x' 0).toVal : R) - (x' 1).toVal)| :=
      abs_sub_comm _ _
    rw [h_err'_flip] at h_triangle
    have hsc_nn := FpInterval.subnormalConst_nn (R := R)
    linarith

/-- `fpMulFinite` is Lipschitz-with-slack on M-bounded inputs.

K = 2M (L∞ pair-Lipschitz of math `·` on M-ball: `|ab - a'b'| ≤ M·(|a - a'| + |b - b'|)`).
c = 2 · (η · M² + subnormalConst). -/
theorem fpMulFinite_lipschitz_with_slack_on
    {M : R} (hM_nn : 0 ≤ M)
    (h_finite : ∀ (a b : FiniteFp),
      |(a.toVal : R)| ≤ M → |(b.toVal : R)| ≤ M →
        ∃ r, fpMulFinite a b = Fp.finite r) :
    LipschitzMaxFpSlackOn (R := R) M (2 * M)
      (2 * ((η : R) * (M * M) + FpInterval.subnormalConst))
      (fun (x : Fin 2 → FiniteFp) (_ : Fin 1) =>
        fpMulFinite_safeT (x 0) (x 1)) where
  K_nn := by linarith
  c_nn := by
    have hη_nn : (0 : R) ≤ (η : R) := by positivity
    have hMsq_nn : (0 : R) ≤ M * M := mul_nonneg hM_nn hM_nn
    have hsc_nn := FpInterval.subnormalConst_nn (R := R)
    have : (0 : R) ≤ (η : R) * (M * M) := mul_nonneg hη_nn hMsq_nn
    linarith
  bound := by
    intro x x' hx_M hx'_M δ h_dx _
    obtain ⟨r, hr⟩ := h_finite (x 0) (x 1) (hx_M 0) (hx_M 1)
    obtain ⟨r', hr'⟩ := h_finite (x' 0) (x' 1) (hx'_M 0) (hx'_M 1)
    rw [fpMulFinite_safeT_eq_of_finite _ _ hr,
        fpMulFinite_safeT_eq_of_finite _ _ hr']
    have h_err := fpMulFinite_unified_error (R := R) (x 0) (x 1) hr
    have h_err' := fpMulFinite_unified_error (R := R) (x' 0) (x' 1) hr'
    -- |x0 · x1| ≤ M² (and similarly for primed).
    have h_prod_bound : |((x 0).toVal : R) * (x 1).toVal| ≤ M * M := by
      rw [abs_mul]
      exact mul_le_mul (hx_M 0) (hx_M 1) (abs_nonneg _) hM_nn
    have h_prod'_bound : |((x' 0).toVal : R) * (x' 1).toVal| ≤ M * M := by
      rw [abs_mul]
      exact mul_le_mul (hx'_M 0) (hx'_M 1) (abs_nonneg _) hM_nn
    have hη_nn : (0 : R) ≤ (η : R) := by positivity
    have h_err_scaled :
        (η : R) * |((x 0).toVal : R) * (x 1).toVal| ≤ (η : R) * (M * M) :=
      mul_le_mul_of_nonneg_left h_prod_bound hη_nn
    have h_err'_scaled :
        (η : R) * |((x' 0).toVal : R) * (x' 1).toVal| ≤ (η : R) * (M * M) :=
      mul_le_mul_of_nonneg_left h_prod'_bound hη_nn
    -- |ab - a'b'| ≤ |a·(b - b')| + |(a - a')·b'| ≤ M·|b - b'| + M·|a - a'| ≤ 2M·δ.
    have h_prod_diff :
        |(((x 0).toVal : R) * (x 1).toVal) -
            (((x' 0).toVal : R) * (x' 1).toVal)| ≤ 2 * M * δ := by
      have h_split : ((x 0).toVal : R) * (x 1).toVal -
                       ((x' 0).toVal : R) * (x' 1).toVal
          = ((x 0).toVal : R) * ((x 1).toVal - (x' 1).toVal)
            + ((x 0).toVal - (x' 0).toVal) * ((x' 1).toVal : R) := by ring
      calc |(((x 0).toVal : R) * (x 1).toVal) -
                (((x' 0).toVal : R) * (x' 1).toVal)|
          = |((x 0).toVal : R) * ((x 1).toVal - (x' 1).toVal)
              + ((x 0).toVal - (x' 0).toVal) * ((x' 1).toVal : R)| := by
            rw [h_split]
        _ ≤ |((x 0).toVal : R) * ((x 1).toVal - (x' 1).toVal)|
            + |((x 0).toVal - (x' 0).toVal) * ((x' 1).toVal : R)| := abs_add_le _ _
        _ = |((x 0).toVal : R)| * |((x 1).toVal : R) - (x' 1).toVal|
            + |((x 0).toVal : R) - (x' 0).toVal| * |((x' 1).toVal : R)| := by
            rw [abs_mul, abs_mul]
        _ ≤ M * δ + δ * M := by
            have h1 : |((x 0).toVal : R)| * |((x 1).toVal : R) - (x' 1).toVal|
                      ≤ M * δ :=
              mul_le_mul (hx_M 0) (h_dx 1) (abs_nonneg _) hM_nn
            have h2 : |((x 0).toVal : R) - (x' 0).toVal| * |((x' 1).toVal : R)|
                      ≤ δ * M := by
              have hδ_nn : 0 ≤ δ := le_trans (abs_nonneg _) (h_dx 0)
              exact mul_le_mul (h_dx 0) (hx'_M 1) (abs_nonneg _) hδ_nn
            linarith
        _ = 2 * M * δ := by ring
    -- Triangle: |r - r'| ≤ |r - prod| + |prod - prod'| + |prod' - r'|.
    have h_triangle : |(r.toVal : R) - r'.toVal|
        ≤ |(r.toVal : R) - ((x 0).toVal * (x 1).toVal)|
          + |(((x 0).toVal : R) * (x 1).toVal) -
              (((x' 0).toVal : R) * (x' 1).toVal)|
          + |(((x' 0).toVal : R) * (x' 1).toVal) - (r'.toVal : R)| := by
      have h_split : (r.toVal : R) - r'.toVal =
          ((r.toVal : R) - ((x 0).toVal * (x 1).toVal))
          + (((x 0).toVal * (x 1).toVal) - ((x' 0).toVal * (x' 1).toVal))
          + (((x' 0).toVal * (x' 1).toVal) - (r'.toVal : R)) := by ring
      calc |(r.toVal : R) - r'.toVal|
          = |((r.toVal : R) - ((x 0).toVal * (x 1).toVal))
              + (((x 0).toVal * (x 1).toVal) - ((x' 0).toVal * (x' 1).toVal))
              + (((x' 0).toVal * (x' 1).toVal) - (r'.toVal : R))| := by
            rw [← h_split]
        _ ≤ |((r.toVal : R) - ((x 0).toVal * (x 1).toVal))
              + (((x 0).toVal * (x 1).toVal) - ((x' 0).toVal * (x' 1).toVal))|
            + |(((x' 0).toVal : R) * (x' 1).toVal) - (r'.toVal : R)| :=
          abs_add_le _ _
        _ ≤ (|(r.toVal : R) - ((x 0).toVal * (x 1).toVal)|
              + |(((x 0).toVal : R) * (x 1).toVal) -
                  (((x' 0).toVal : R) * (x' 1).toVal)|)
            + |(((x' 0).toVal : R) * (x' 1).toVal) - (r'.toVal : R)| := by
            linarith [abs_add_le ((r.toVal : R) - ((x 0).toVal * (x 1).toVal))
              ((((x 0).toVal : R) * (x 1).toVal) -
                (((x' 0).toVal : R) * (x' 1).toVal))]
    have h_err'_flip :
        |(((x' 0).toVal : R) * (x' 1).toVal) - (r'.toVal : R)|
          = |(r'.toVal : R) - (((x' 0).toVal : R) * (x' 1).toVal)| :=
      abs_sub_comm _ _
    rw [h_err'_flip] at h_triangle
    have hsc_nn := FpInterval.subnormalConst_nn (R := R)
    -- Goal: |r.toVal - r'.toVal| ≤ 2M · δ + 2·(η·M² + sc).
    linarith

end Flean.Lipschitz
