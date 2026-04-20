import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Operations.FpFiniteRound
import Flean.Rounding.ModeClass
import Flean.Rounding.RoundPreserves
import Flean.Tags.BoundedRange

/-!
# Parametric propagation for `IsBoundedRange`

Per `.claude/notes/tag-framework-phase1-design.md` §1.4 / §3.4.

Propagation lemmas threading `IsBoundedRange lo hi xs` through the
primitive FP ops `fpAddFinite` / `fpMulFinite`.  The input-interval
bounds widen outward to absorb the rounding slack contributed by the
op.

Both lemmas assume the exact real result (sum or product) lies in the
sign-agnostic normal range, i.e.
`(2 : R) ^ FloatFormat.min_exp ≤ |exact result|`.  That forbids the
zero-case and the subnormal tail.  The upper bound of the normal range
is *not* a separate hypothesis — finiteness of the rounded result (via
`hf`) forces `|exact| < 2^(max_exp+1)`, as exploited by the underlying
meta-lemma `round_preserves_abs_error_normal`.

## Output-interval formulas

- **`IsBoundedRange.fpAdd`**:
  - let `M := max |lo₁ + lo₂| |hi₁ + hi₂|` and `slack := η · M`.
  - `lo' := (lo₁ + lo₂) - slack`,  `hi' := (hi₁ + hi₂) + slack`.
  - Satisfies the locked invariants `lo' ≤ lo₁ + lo₂` and
    `hi₁ + hi₂ ≤ hi'` trivially (`slack ≥ 0`).
- **`IsBoundedRange.fpMul`**:
  - let `M₁ := max |lo₁| |hi₁|`, `M₂ := max |lo₂| |hi₂|`, `M := M₁ · M₂`.
  - `lo' := -((1 + η) · M)`,  `hi' := (1 + η) · M`.
  - `|f.toVal| ≤ (1 + η) · M` — a symmetric-around-0 interval.  The
    locked signature does not require any outward-bound invariant
    (since a mixed-sign product has no natural one-sided relation to
    the input endpoints).

## Scope

Sign-general inputs are handled — negative intervals go through the
`RModeConj` branch of `round_preserves_abs_error_normal` automatically.
No sign restriction on `lo*`, `hi*`, `x.toVal`, or `y.toVal`.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Helpers -/

omit [FloatFormat] [FloorRing R] in
private theorem abs_le_max_abs_of_le_le {a lo hi : R}
    (hlo : lo ≤ a) (hhi : a ≤ hi) :
    |a| ≤ max |lo| |hi| := by
  rcases le_or_gt 0 a with ha | ha
  · have : |a| = a := abs_of_nonneg ha
    rw [this]
    exact le_trans (le_trans hhi (le_abs_self hi)) (le_max_right _ _)
  · have habs : |a| = -a := abs_of_neg ha
    have hlo_abs : -a ≤ |lo| := by
      have h_neg : -a ≤ -lo := neg_le_neg hlo
      exact le_trans h_neg (neg_le_abs lo)
    rw [habs]
    exact le_trans hlo_abs (le_max_left _ _)

/-! ## Addition propagation -/

/-- `IsBoundedRange` propagates through `fpAddFinite`.

Given `lo₁ ≤ x.toVal ≤ hi₁` and `lo₂ ≤ y.toVal ≤ hi₂`, and a rounded
sum `f` with the exact sum in the sign-agnostic normal range, the
rounded result lives in a widened interval
`[lo₁ + lo₂ - slack, hi₁ + hi₂ + slack]` where
`slack := η · max |lo₁ + lo₂| |hi₁ + hi₂|` is the nearest-rounding
absolute error bound.

The output lower/upper bounds are weaker than the exact-sum endpoints
by `slack`, matching the locked invariant in the design doc §3.4:
`lo' ≤ lo₁ + lo₂` and `hi₁ + hi₂ ≤ hi'`. -/
theorem IsBoundedRange.fpAdd
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lo₁ hi₁ lo₂ hi₂ : R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => y))
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) + y.toVal|)
    (hf : fpAddFinite x y = Fp.finite f) :
    ∃ (lo' hi' : R),
      lo' ≤ lo₁ + lo₂ ∧ hi₁ + hi₂ ≤ hi' ∧
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f) := by
  set s : R := (x.toVal : R) + y.toVal with hs_def
  set M : R := max |lo₁ + lo₂| |hi₁ + hi₂| with hM_def
  set slack : R := η * M with hslack_def
  -- Input bounds on `s`.
  have hs_lb : lo₁ + lo₂ ≤ s := by
    have h1 := hx.lower 0
    have h2 := hy.lower 0
    simp only at h1 h2
    linarith
  have hs_ub : s ≤ hi₁ + hi₂ := by
    have h1 := hx.upper 0
    have h2 := hy.upper 0
    simp only at h1 h2
    linarith
  have hs_abs_le_M : |s| ≤ M := abs_le_max_abs_of_le_le hs_lb hs_ub
  -- Rounding error bound via the meta-lemma.
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - s| ≤ η * |s| :=
    round_preserves_abs_error_normal h_normal hg_round
  -- Non-negativity of slack.
  have hη_nn : (0 : R) ≤ η := by positivity
  have hM_nn : (0 : R) ≤ M :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have hslack_nn : (0 : R) ≤ slack :=
    mul_nonneg hη_nn hM_nn
  have h_err_le_slack : |(g.toVal : R) - s| ≤ slack := by
    have hstep : η * |s| ≤ η * M := mul_le_mul_of_nonneg_left hs_abs_le_M hη_nn
    exact le_trans h_err hstep
  have h_err_bounds : -slack ≤ (g.toVal : R) - s ∧ (g.toVal : R) - s ≤ slack := by
    exact ⟨(abs_le.mp h_err_le_slack).1, (abs_le.mp h_err_le_slack).2⟩
  refine ⟨(lo₁ + lo₂) - slack, (hi₁ + hi₂) + slack, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · refine ⟨?_, ?_⟩
    · intro _
      show lo₁ + lo₂ - slack ≤ (f.toVal : R)
      rw [← hg_eq]
      linarith [h_err_bounds.1]
    · intro _
      show (f.toVal : R) ≤ hi₁ + hi₂ + slack
      rw [← hg_eq]
      linarith [h_err_bounds.2]

/-! ## Multiplication propagation -/

/-- `IsBoundedRange` propagates through `fpMulFinite`.

Given `lo₁ ≤ x.toVal ≤ hi₁` and `lo₂ ≤ y.toVal ≤ hi₂`, and a rounded
product `f` with the exact product in the sign-agnostic normal range,
the rounded result lives in the symmetric-around-zero interval
`[-(1+η) · M, (1+η) · M]` where `M := max |lo₁| |hi₁| · max |lo₂| |hi₂|`
is the worst-case magnitude of any product of endpoints.

The symmetric form reflects that a mixed-sign product interval
`[lo₁, hi₁] × [lo₂, hi₂]` has no natural one-sided relation to input
endpoints (contrast `fpAdd`, where `lo₁ + lo₂` and `hi₁ + hi₂` remain
meaningful two-sided bounds on the exact sum). -/
theorem IsBoundedRange.fpMul
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lo₁ hi₁ lo₂ hi₂ : R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => y))
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) * y.toVal|)
    (hf : fpMulFinite x y = Fp.finite f) :
    ∃ (lo' hi' : R),
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f) := by
  set p : R := (x.toVal : R) * y.toVal with hp_def
  set M₁ : R := max |lo₁| |hi₁| with hM₁_def
  set M₂ : R := max |lo₂| |hi₂| with hM₂_def
  set M : R := M₁ * M₂ with hM_def
  -- `|x.toVal| ≤ M₁` and `|y.toVal| ≤ M₂`.
  have hx_abs_le : |(x.toVal : R)| ≤ M₁ :=
    abs_le_max_abs_of_le_le (hx.lower 0) (hx.upper 0)
  have hy_abs_le : |(y.toVal : R)| ≤ M₂ :=
    abs_le_max_abs_of_le_le (hy.lower 0) (hy.upper 0)
  have hM₁_nn : (0 : R) ≤ M₁ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM₂_nn : (0 : R) ≤ M₂ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM_nn : (0 : R) ≤ M := mul_nonneg hM₁_nn hM₂_nn
  -- `|p| ≤ M`.
  have hp_abs_le_M : |p| ≤ M := by
    rw [hp_def, abs_mul]
    exact mul_le_mul hx_abs_le hy_abs_le (abs_nonneg _) hM₁_nn
  -- Rounding error bound.
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - p| ≤ η * |p| :=
    round_preserves_abs_error_normal h_normal hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  -- `|g.toVal| ≤ (1+η)·M`.
  have hg_abs_le : |(g.toVal : R)| ≤ (1 + η) * M := by
    have h_step1 : |(g.toVal : R)| ≤ |g.toVal - p| + |p| := by
      have : |((g.toVal - p) + p : R)| ≤ |g.toVal - p| + |p| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - p| + |p| := h_step1
      _ ≤ η * |p| + |p| := by linarith
      _ = (1 + η) * |p| := by ring
      _ ≤ (1 + η) * M := mul_le_mul_of_nonneg_left hp_abs_le_M h1η_nn
  refine ⟨-((1 + η) * M), (1 + η) * M, ?_, ?_⟩
  · intro _
    show -((1 + η) * M) ≤ (f.toVal : R)
    rw [← hg_eq]
    exact (abs_le.mp hg_abs_le).1
  · intro _
    show (f.toVal : R) ≤ (1 + η) * M
    rw [← hg_eq]
    exact (abs_le.mp hg_abs_le).2

end Flean.Tags
