import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Operations.FMA
import Flean.Operations.FpFiniteRound
import Flean.Rounding.ModeClass
import Flean.Rounding.RoundPreserves
import Flean.Tags.BoundedRange

/-!
# Parametric propagation for `IsBoundedRange`

Per `.claude/notes/tag-framework-phase1-design.md` §1.4 / §3.4.

Propagation lemmas threading `IsBoundedRange lo hi xs` through the
primitive FP ops `fpAddFinite` / `fpMulFinite` / `fpFMAFinite`.  The
input-interval bounds widen outward to absorb the rounding slack
contributed by the op.

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
- **`IsBoundedRange.fpFMA`**:
  - let `M := max |lo₁| |hi₁| · max |lo₂| |hi₂| + max |lo₃| |hi₃|`.
  - `lo' := -((1 + η) · M)`,  `hi' := (1 + η) · M`.
  - Single rounding step over exact `a·b + c`; same symmetric form as
    `fpMul` since the embedded product already loses directional
    structure.  Compared to separate `mul` + `add`, FMA absorbs two
    rounding errors into one.

## Scope

Sign-general inputs are handled — negative intervals go through the
`RModeConj` branch of `round_preserves_abs_error_normal` automatically.
No sign restriction on `lo*`, `hi*`, `x.toVal`, or `y.toVal`.

## Two regimes

- **Normal-range variants** (`IsBoundedRange.fp{Add,Mul}`) — take a
  `(2:R)^min_exp ≤ |exact|` hypothesis.  Slack: `η·M`.
- **Unified / subnormal-tolerant variants**
  (`IsBoundedRange.fp{Add,Mul}_unified`) — drop the precondition,
  slack grows to `η·M + sc` where `sc := 2^(min_exp - prec)`.
  Chain composes without per-step normal-range discharge — see the
  `demo_mul_mul_add_unified` in the `Demo` section for the side-by-side
  with the normal-range variant.
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

/-! ## FMA propagation

`fpFMA(a, b, c) = round(a·b + c)` — single rounding step over the
exact real `a·b + c`.  The output interval is symmetric-around-zero
(mirroring `fpMul`), since the product component `a·b` already loses
directional structure under sign mixing, and the final bound is
dominated by the max-magnitude of `a·b + c`. -/

/-- `IsBoundedRange` propagates through `fpFMAFinite` in the
normal-range regime (exact `a·b + c` has `2^min_exp ≤ |·|`).

Output interval: `[-(1+η)·M, (1+η)·M]` where
`M := max |lo₁| |hi₁| · max |lo₂| |hi₂| + max |lo₃| |hi₃|` — the
worst-case magnitude of `a·b + c`. -/
theorem IsBoundedRange.fpFMA
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ : R} {a b c f : FiniteFp}
    (ha : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => a))
    (hb : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => b))
    (hc : IsBoundedRange (R := R) lo₃ hi₃ (fun (_ : Fin 1) => c))
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤
                |(a.toVal : R) * b.toVal + c.toVal|)
    (hf : fpFMAFinite a b c = Fp.finite f) :
    ∃ (lo' hi' : R),
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f) := by
  set e : R := (a.toVal : R) * b.toVal + c.toVal with he_def
  set M₁ : R := max |lo₁| |hi₁| with hM₁_def
  set M₂ : R := max |lo₂| |hi₂| with hM₂_def
  set M₃ : R := max |lo₃| |hi₃| with hM₃_def
  set M : R := M₁ * M₂ + M₃ with hM_def
  -- Input magnitude bounds.
  have ha_abs_le : |(a.toVal : R)| ≤ M₁ :=
    abs_le_max_abs_of_le_le (ha.lower 0) (ha.upper 0)
  have hb_abs_le : |(b.toVal : R)| ≤ M₂ :=
    abs_le_max_abs_of_le_le (hb.lower 0) (hb.upper 0)
  have hc_abs_le : |(c.toVal : R)| ≤ M₃ :=
    abs_le_max_abs_of_le_le (hc.lower 0) (hc.upper 0)
  have hM₁_nn : (0 : R) ≤ M₁ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM₂_nn : (0 : R) ≤ M₂ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM₃_nn : (0 : R) ≤ M₃ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM_nn : (0 : R) ≤ M := by rw [hM_def]; positivity
  -- `|e| ≤ M`.
  have he_abs_le : |e| ≤ M := by
    have h_ab_prod : |(a.toVal : R) * b.toVal| ≤ M₁ * M₂ := by
      rw [abs_mul]
      exact mul_le_mul ha_abs_le hb_abs_le (abs_nonneg _) hM₁_nn
    calc |e|
        = |(a.toVal : R) * b.toVal + c.toVal| := rfl
      _ ≤ |(a.toVal : R) * b.toVal| + |(c.toVal : R)| := abs_add_le _ _
      _ ≤ M₁ * M₂ + M₃ := add_le_add h_ab_prod hc_abs_le
      _ = M := rfl
  -- Rounding error bound.
  obtain ⟨g, hg_round, hg_eq⟩ := fpFMAFinite_round_witness (R := R) a b c hf
  have h_err : |(g.toVal : R) - e| ≤ η * |e| :=
    round_preserves_abs_error_normal h_normal hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  -- `|g.toVal| ≤ (1+η)·M`.
  have hg_abs_le : |(g.toVal : R)| ≤ (1 + η) * M := by
    have h_step1 : |(g.toVal : R)| ≤ |g.toVal - e| + |e| := by
      have : |((g.toVal - e) + e : R)| ≤ |g.toVal - e| + |e| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - e| + |e| := h_step1
      _ ≤ η * |e| + |e| := by linarith
      _ = (1 + η) * |e| := by ring
      _ ≤ (1 + η) * M := mul_le_mul_of_nonneg_left he_abs_le h1η_nn
  refine ⟨-((1 + η) * M), (1 + η) * M, ?_, ?_⟩
  · intro _
    show -((1 + η) * M) ≤ (f.toVal : R)
    rw [← hg_eq]; exact (abs_le.mp hg_abs_le).1
  · intro _
    show (f.toVal : R) ≤ (1 + η) * M
    rw [← hg_eq]; exact (abs_le.mp hg_abs_le).2

/-! ## Subnormal-tolerant variants

Drop the `(2:R)^min_exp ≤ |exact|` precondition from `fpAdd` / `fpMul`
in exchange for an additive `subnormalConst := 2^(min_exp - prec)`
tail in the output-interval widening.  These are the versions a
chained call-site normally wants: they compose without requiring
manual normal-range discharge at every intermediate. -/

section Unified

/-- `IsBoundedRange` propagates through `fpAddFinite`, subnormal-tolerant.

Drops the normal-range hypothesis of `IsBoundedRange.fpAdd` at the
cost of an additive `2^(min_exp - prec)` tail in the slack.  Final
output interval:
  `[lo₁+lo₂ − (η·M + sc), hi₁+hi₂ + (η·M + sc)]`
where `M := max |lo₁+lo₂| |hi₁+hi₂|` and `sc := 2^(min_exp - prec)`. -/
theorem IsBoundedRange.fpAdd_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lo₁ hi₁ lo₂ hi₂ : R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => y))
    (hf : fpAddFinite x y = Fp.finite f) :
    ∃ (lo' hi' : R),
      lo' ≤ lo₁ + lo₂ ∧ hi₁ + hi₂ ≤ hi' ∧
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f) := by
  set s : R := (x.toVal : R) + y.toVal with hs_def
  set M : R := max |lo₁ + lo₂| |hi₁ + hi₂| with hM_def
  set sc : R := (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) with hsc_def
  set slack : R := η * M + sc with hslack_def
  -- Input bounds on `s`.
  have hs_lb : lo₁ + lo₂ ≤ s := by
    have h1 := hx.lower 0; have h2 := hy.lower 0
    simp only at h1 h2; linarith
  have hs_ub : s ≤ hi₁ + hi₂ := by
    have h1 := hx.upper 0; have h2 := hy.upper 0
    simp only at h1 h2; linarith
  have hs_abs_le_M : |s| ≤ M := abs_le_max_abs_of_le_le hs_lb hs_ub
  -- Rounding error bound via the unified meta-lemma.
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - s| ≤ η * |s| + sc :=
    round_preserves_abs_error_unified (R := R) s hg_round
  -- Non-negativity of slack.
  have hη_nn : (0 : R) ≤ η := by positivity
  have hsc_nn : (0 : R) ≤ sc := by rw [hsc_def]; positivity
  have hM_nn : (0 : R) ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hslack_nn : (0 : R) ≤ slack := by
    rw [hslack_def]; exact add_nonneg (mul_nonneg hη_nn hM_nn) hsc_nn
  have h_err_le_slack : |(g.toVal : R) - s| ≤ slack := by
    have hstep : η * |s| ≤ η * M := mul_le_mul_of_nonneg_left hs_abs_le_M hη_nn
    linarith
  have h_err_bounds :
      -slack ≤ (g.toVal : R) - s ∧ (g.toVal : R) - s ≤ slack :=
    ⟨(abs_le.mp h_err_le_slack).1, (abs_le.mp h_err_le_slack).2⟩
  refine ⟨(lo₁ + lo₂) - slack, (hi₁ + hi₂) + slack, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · refine ⟨?_, ?_⟩
    · intro _
      show lo₁ + lo₂ - slack ≤ (f.toVal : R)
      rw [← hg_eq]; linarith [h_err_bounds.1]
    · intro _
      show (f.toVal : R) ≤ hi₁ + hi₂ + slack
      rw [← hg_eq]; linarith [h_err_bounds.2]

/-- `IsBoundedRange` propagates through `fpMulFinite`, subnormal-tolerant.

Drops the normal-range hypothesis at the cost of an additive
`2^(min_exp - prec)` tail.  Final output interval:
  `[-((1+η)·M + sc), (1+η)·M + sc]`
where `M := max |lo₁| |hi₁| · max |lo₂| |hi₂|` and
`sc := 2^(min_exp - prec)`. -/
theorem IsBoundedRange.fpMul_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lo₁ hi₁ lo₂ hi₂ : R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => y))
    (hf : fpMulFinite x y = Fp.finite f) :
    ∃ (lo' hi' : R),
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f) := by
  set p : R := (x.toVal : R) * y.toVal with hp_def
  set M₁ : R := max |lo₁| |hi₁| with hM₁_def
  set M₂ : R := max |lo₂| |hi₂| with hM₂_def
  set M : R := M₁ * M₂ with hM_def
  set sc : R := (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) with hsc_def
  -- Input magnitude bounds.
  have hx_abs_le : |(x.toVal : R)| ≤ M₁ :=
    abs_le_max_abs_of_le_le (hx.lower 0) (hx.upper 0)
  have hy_abs_le : |(y.toVal : R)| ≤ M₂ :=
    abs_le_max_abs_of_le_le (hy.lower 0) (hy.upper 0)
  have hM₁_nn : (0 : R) ≤ M₁ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM₂_nn : (0 : R) ≤ M₂ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hsc_nn : (0 : R) ≤ sc := by rw [hsc_def]; positivity
  have hp_abs_le_M : |p| ≤ M := by
    rw [hp_def, abs_mul]
    exact mul_le_mul hx_abs_le hy_abs_le (abs_nonneg _) hM₁_nn
  -- Rounding error bound.
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - p| ≤ η * |p| + sc :=
    round_preserves_abs_error_unified (R := R) p hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  -- `|g.toVal| ≤ (1+η)·M + sc`.
  have hg_abs_le : |(g.toVal : R)| ≤ (1 + η) * M + sc := by
    have h_step1 : |(g.toVal : R)| ≤ |g.toVal - p| + |p| := by
      have : |((g.toVal - p) + p : R)| ≤ |g.toVal - p| + |p| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - p| + |p| := h_step1
      _ ≤ (η * |p| + sc) + |p| := by linarith
      _ = (1 + η) * |p| + sc := by ring
      _ ≤ (1 + η) * M + sc := by
          have := mul_le_mul_of_nonneg_left hp_abs_le_M h1η_nn
          linarith
  refine ⟨-((1 + η) * M + sc), (1 + η) * M + sc, ?_, ?_⟩
  · intro _
    show -((1 + η) * M + sc) ≤ (f.toVal : R)
    rw [← hg_eq]; exact (abs_le.mp hg_abs_le).1
  · intro _
    show (f.toVal : R) ≤ (1 + η) * M + sc
    rw [← hg_eq]; exact (abs_le.mp hg_abs_le).2

/-- `IsBoundedRange` propagates through `fpFMAFinite`, subnormal-tolerant.

Drops the normal-range hypothesis of `IsBoundedRange.fpFMA` at the
cost of an additive `2^(min_exp - prec)` tail.  Output:
  `[-((1+η)·M + sc), (1+η)·M + sc]`
where `M := max |lo₁| |hi₁| · max |lo₂| |hi₂| + max |lo₃| |hi₃|`
and `sc := 2^(min_exp - prec)`. -/
theorem IsBoundedRange.fpFMA_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ : R} {a b c f : FiniteFp}
    (ha : IsBoundedRange (R := R) lo₁ hi₁ (fun (_ : Fin 1) => a))
    (hb : IsBoundedRange (R := R) lo₂ hi₂ (fun (_ : Fin 1) => b))
    (hc : IsBoundedRange (R := R) lo₃ hi₃ (fun (_ : Fin 1) => c))
    (hf : fpFMAFinite a b c = Fp.finite f) :
    ∃ (lo' hi' : R),
      IsBoundedRange (R := R) lo' hi' (fun (_ : Fin 1) => f) := by
  set e : R := (a.toVal : R) * b.toVal + c.toVal with he_def
  set M₁ : R := max |lo₁| |hi₁| with hM₁_def
  set M₂ : R := max |lo₂| |hi₂| with hM₂_def
  set M₃ : R := max |lo₃| |hi₃| with hM₃_def
  set M : R := M₁ * M₂ + M₃ with hM_def
  set sc : R := (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) with hsc_def
  have ha_abs_le : |(a.toVal : R)| ≤ M₁ :=
    abs_le_max_abs_of_le_le (ha.lower 0) (ha.upper 0)
  have hb_abs_le : |(b.toVal : R)| ≤ M₂ :=
    abs_le_max_abs_of_le_le (hb.lower 0) (hb.upper 0)
  have hc_abs_le : |(c.toVal : R)| ≤ M₃ :=
    abs_le_max_abs_of_le_le (hc.lower 0) (hc.upper 0)
  have hM₁_nn : (0 : R) ≤ M₁ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM₂_nn : (0 : R) ≤ M₂ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM₃_nn : (0 : R) ≤ M₃ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM_nn : (0 : R) ≤ M := by rw [hM_def]; positivity
  have hsc_nn : (0 : R) ≤ sc := by rw [hsc_def]; positivity
  have he_abs_le : |e| ≤ M := by
    have h_ab_prod : |(a.toVal : R) * b.toVal| ≤ M₁ * M₂ := by
      rw [abs_mul]
      exact mul_le_mul ha_abs_le hb_abs_le (abs_nonneg _) hM₁_nn
    calc |e|
        = |(a.toVal : R) * b.toVal + c.toVal| := rfl
      _ ≤ |(a.toVal : R) * b.toVal| + |(c.toVal : R)| := abs_add_le _ _
      _ ≤ M₁ * M₂ + M₃ := add_le_add h_ab_prod hc_abs_le
      _ = M := rfl
  obtain ⟨g, hg_round, hg_eq⟩ := fpFMAFinite_round_witness (R := R) a b c hf
  have h_err : |(g.toVal : R) - e| ≤ η * |e| + sc :=
    round_preserves_abs_error_unified (R := R) e hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have hg_abs_le : |(g.toVal : R)| ≤ (1 + η) * M + sc := by
    have h_step1 : |(g.toVal : R)| ≤ |g.toVal - e| + |e| := by
      have : |((g.toVal - e) + e : R)| ≤ |g.toVal - e| + |e| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - e| + |e| := h_step1
      _ ≤ (η * |e| + sc) + |e| := by linarith
      _ = (1 + η) * |e| + sc := by ring
      _ ≤ (1 + η) * M + sc := by
          have := mul_le_mul_of_nonneg_left he_abs_le h1η_nn
          linarith
  refine ⟨-((1 + η) * M + sc), (1 + η) * M + sc, ?_, ?_⟩
  · intro _
    show -((1 + η) * M + sc) ≤ (f.toVal : R)
    rw [← hg_eq]; exact (abs_le.mp hg_abs_le).1
  · intro _
    show (f.toVal : R) ≤ (1 + η) * M + sc
    rw [← hg_eq]; exact (abs_le.mp hg_abs_le).2

end Unified

/-! ## Demo: 3-op chain validates design doc §3.4 success criterion

The design-doc success criterion for parametric propagation is: "a 3-op
chain can thread `IsBoundedRange` through via three explicit calls, and
the proof reads as interval arithmetic."  The demo below threads the
tag through `r = fpAdd (fpMul x y) (fpMul z w)` via three named
propagation calls.  The proof body is essentially four lines of
`obtain` after the three `IsBoundedRange.fp{Mul,Add}` applications.

### UX findings surfaced by this demo

1. **One normal-range hypothesis per op.**  The chain needs three
   separate `(2:R)^min_exp ≤ |·|` hypotheses (one per FP op).  A
   subnormal-tolerant meta-lemma would let users drop these in exchange
   for an additive `subnormalConst`-style tail.

2. **Existential unpacking is manual.**  Each `IsBoundedRange.fp*`
   call returns `∃ lo' hi', ...`; the user `obtain`s to thread the
   downstream tag.  Tolerable for short chains but scales linearly.
   A wrapper returning a struct-of-intervals (or a `Σ`-type) could
   reduce this, though the current ∃-form keeps the signature honest
   about the output being existentially bound.

3. **No tag-weakening needed in the add.**  Because `IsBoundedRange`'s
   input position is parametric over `lo`/`hi`, the downstream
   `IsBoundedRange.fpAdd` accepts the `fpMul` output intervals
   directly — no explicit `lo' ≤ lo` bridging step.  This confirms
   the design doc's §1.7 stance (defer tag-weakening infrastructure)
   was correct: for same-tag chains, nothing to weaken. -/

section Demo

/-- Three-op chain `r = fpAdd (fpMul x y) (fpMul z w)` threads
`IsBoundedRange` through via three explicit propagation calls. -/
theorem IsBoundedRange.demo_mul_mul_add
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lox hix loy hiy loz hiz low hiw : R}
    {x y z w m₁ m₂ r : FiniteFp}
    (hx : IsBoundedRange (R := R) lox hix (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) loy hiy (fun (_ : Fin 1) => y))
    (hz : IsBoundedRange (R := R) loz hiz (fun (_ : Fin 1) => z))
    (hw : IsBoundedRange (R := R) low hiw (fun (_ : Fin 1) => w))
    (h_xy_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) * y.toVal|)
    (h_zw_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(z.toVal : R) * w.toVal|)
    (h_sum_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(m₁.toVal : R) + m₂.toVal|)
    (hm₁ : fpMulFinite x y = Fp.finite m₁)
    (hm₂ : fpMulFinite z w = Fp.finite m₂)
    (hr : fpAddFinite m₁ m₂ = Fp.finite r) :
    ∃ lo hi : R, IsBoundedRange (R := R) lo hi (fun (_ : Fin 1) => r) := by
  obtain ⟨_, _, hm₁_tag⟩ := IsBoundedRange.fpMul hx hy h_xy_normal hm₁
  obtain ⟨_, _, hm₂_tag⟩ := IsBoundedRange.fpMul hz hw h_zw_normal hm₂
  obtain ⟨lo_r, hi_r, _, _, hr_tag⟩ :=
    IsBoundedRange.fpAdd hm₁_tag hm₂_tag h_sum_normal hr
  exact ⟨lo_r, hi_r, hr_tag⟩

/-- Same three-op chain, subnormal-tolerant form.  The three
`(2:R)^min_exp ≤ |·|` preconditions are gone: the unified propagation
lemmas absorb subnormal rounding into a per-step `sc` tail in the
output slack.  Hypothesis surface: four interval tags + three
finiteness witnesses.  Compare to `demo_mul_mul_add` above, which adds
three normal-range preconditions on top. -/
theorem IsBoundedRange.demo_mul_mul_add_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lox hix loy hiy loz hiz low hiw : R}
    {x y z w m₁ m₂ r : FiniteFp}
    (hx : IsBoundedRange (R := R) lox hix (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) loy hiy (fun (_ : Fin 1) => y))
    (hz : IsBoundedRange (R := R) loz hiz (fun (_ : Fin 1) => z))
    (hw : IsBoundedRange (R := R) low hiw (fun (_ : Fin 1) => w))
    (hm₁ : fpMulFinite x y = Fp.finite m₁)
    (hm₂ : fpMulFinite z w = Fp.finite m₂)
    (hr : fpAddFinite m₁ m₂ = Fp.finite r) :
    ∃ lo hi : R, IsBoundedRange (R := R) lo hi (fun (_ : Fin 1) => r) := by
  obtain ⟨_, _, hm₁_tag⟩ := IsBoundedRange.fpMul_unified hx hy hm₁
  obtain ⟨_, _, hm₂_tag⟩ := IsBoundedRange.fpMul_unified hz hw hm₂
  obtain ⟨lo_r, hi_r, _, _, hr_tag⟩ :=
    IsBoundedRange.fpAdd_unified hm₁_tag hm₂_tag hr
  exact ⟨lo_r, hi_r, hr_tag⟩

/-- Two-FMA chain `r = fpFMA x y (fpFMA z w c)` computing
`x·y + z·w + c` via two FMAs = two rounding steps, vs the three
rounding steps of the mul-mul-add chain in
`demo_mul_mul_add_unified`.  Each FMA absorbs one multiplication +
one addition into a single rounding step with a single error. -/
theorem IsBoundedRange.demo_fma_chain_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {lox hix loy hiy loz hiz low hiw loc hic : R}
    {x y z w c t r : FiniteFp}
    (hx : IsBoundedRange (R := R) lox hix (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) loy hiy (fun (_ : Fin 1) => y))
    (hz : IsBoundedRange (R := R) loz hiz (fun (_ : Fin 1) => z))
    (hw : IsBoundedRange (R := R) low hiw (fun (_ : Fin 1) => w))
    (hc : IsBoundedRange (R := R) loc hic (fun (_ : Fin 1) => c))
    (ht : fpFMAFinite z w c = Fp.finite t)
    (hr : fpFMAFinite x y t = Fp.finite r) :
    ∃ lo hi : R, IsBoundedRange (R := R) lo hi (fun (_ : Fin 1) => r) := by
  obtain ⟨_, _, ht_tag⟩ := IsBoundedRange.fpFMA_unified hz hw hc ht
  obtain ⟨lo_r, hi_r, hr_tag⟩ := IsBoundedRange.fpFMA_unified hx hy ht_tag hr
  exact ⟨lo_r, hi_r, hr_tag⟩

end Demo

end Flean.Tags
