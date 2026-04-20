import Flean.Rounding.ModeClass
import Flean.Order
import Flean.Operations.KahanSum

/-!
# Meta-lemmas: rounding preserves semantic tags

Per `.claude/notes/tag-framework-phase1-design.md` §3.1. Collects the
"round preserves P" meta-lemmas used by tag-framework preservation
proofs. Each lemma takes a pre-existing `RMode` plus the specific
`RMode*` class(es) needed for its preservation law, and lifts a
property on the real pre-image to a property on the rounded float.

Downstream tag preservation theorems (e.g. `IsNonneg.fpAdd` in
`Flean/Tags/Nonneg.lean`) reduce to: get a rounding witness from
`Flean/Operations/FpFiniteRound.lean`, then apply the appropriate
meta-lemma here.

Currently populated:
- `round_preserves_nonneg` — via `RModeMono` + `RModeZero`.
- `round_preserves_abs_bound_normal` — via `RModeNearest` +
  `standard_error_additive`. For parametric `HasAbsBound c` tags in
  the normal-range regime (non-negative inputs only).
- `round_preserves_abs_error_normal` — sign-agnostic additive error
  bound `|f.toVal - x| ≤ η·|x|` for any `x` with
  `2^min_exp ≤ |x|`, via `RModeNearest` + `RModeConj`. Underpins the
  parametric interval-propagation lemmas in
  `Flean/Tags/BoundedRangePropagate.lean`.

Future additions (as tags demand):
- `round_preserves_pos` — `IsPos` is NOT generally round-preserved
  (tiny positives underflow to 0); a useful variant would add a
  lower-magnitude hypothesis that avoids the underflow zone.
- Subnormal-tolerant `round_preserves_abs_bound` — drops the
  `isNormalRange` hypothesis at the cost of a `subnormalConst` tail.
- etc.
-/

section RoundPreserves

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If `x ≥ 0` and rounding `x` yields a finite float `f`, then
`0 ≤ f.toVal`. The universal kernel underlying any "round preserves
non-negative" tag preservation.

Uses only `RModeMono` (order-preservation) and `RModeZero` (zero is
round-stable). All standard rounding modes in Flean satisfy both, so
this lemma composes with any of them. -/
theorem round_preserves_nonneg [RMode R] [RModeMono R] [RModeZero R]
    {x : R} (hx : 0 ≤ x) {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    (0 : R) ≤ f.toVal := by
  have h_mono := RModeMono.round_mono (R := R) hx
  rw [RModeZero.round_zero (R := R), hf] at h_mono
  have hle : (0 : FiniteFp) ≤ f := (Fp.finite_le_finite_iff 0 f).mp h_mono
  have := FiniteFp.le_toVal_le R hle
  rwa [FiniteFp.toVal_zero] at this

/-- If `|x| ≤ c` with `x` in the (positive) normal range, then rounding
`x` yields a finite `f` with `|f.toVal| ≤ (1+η)·c`. The kernel for any
parametric `HasAbsBound c` tag preservation, in the normal-range regime.

Uses `KahanSum.standard_error_additive` (`|f - x| ≤ η·|x|` for normal-range
positive `x` under `RModeNearest`). A sign-agnostic / subnormal-tolerant
version is future work — see the module docstring. -/
theorem round_preserves_abs_bound_normal [FloorRing R] [RMode R] [RModeNearest R]
    {x c : R} (hxc : |x| ≤ c) (hx_normal : isNormalRange x)
    {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    |(f.toVal : R)| ≤ (1 + η) * c := by
  have hx_pos := isNormalRange_pos x hx_normal
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have h_err := KahanSum.standard_error_additive x hx_normal f hf
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have h_step1 : |(f.toVal : R)| ≤ |f.toVal - x| + |x| := by
    have : |((f.toVal - x) + x : R)| ≤ |f.toVal - x| + |x| := abs_add_le _ _
    convert this using 2
    ring
  calc |(f.toVal : R)|
      ≤ |f.toVal - x| + |x| := h_step1
    _ ≤ η * |x| + |x| := by linarith
    _ = (1 + η) * |x| := by ring
    _ ≤ (1 + η) * c := mul_le_mul_of_nonneg_left hxc h1η_nn

/-- Sign-agnostic additive error bound: for any `x` with
`2^min_exp ≤ |x|` (so `x ≠ 0` and is no tinier than the smallest
normal), rounding `x` to a finite float `f` satisfies
`|f.toVal - x| ≤ η · |x|`.

The finiteness hypothesis `hf` forces `|x| < overflowThreshold <
2^(max_exp+1)`, so we don't need to take the upper normal-range bound
as a user hypothesis.

Proof dispatches on the sign of `x`: positive inputs use
`standard_error_additive` directly; negative inputs reduce to the
positive case via `RModeConj.round_neg`.

This is the interval-propagation companion of `round_preserves_abs_bound_normal`
(which fixes a single magnitude bound `c` and is non-negative-only).  -/
theorem round_preserves_abs_error_normal [FloorRing R]
    [RMode R] [RModeNearest R] [RModeConj R]
    {x : R} (hx_lb : (2 : R) ^ FloatFormat.min_exp ≤ |x|)
    {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    |(f.toVal : R) - x| ≤ η * |x| := by
  have h_pos_min : (0 : R) < (2 : R) ^ (FloatFormat.min_exp : ℤ) := by linearize
  have hx_abs_pos : (0 : R) < |x| := lt_of_lt_of_le h_pos_min hx_lb
  have hx_ne : x ≠ 0 := fun h => by
    rw [h, abs_zero] at hx_abs_pos; exact lt_irrefl _ hx_abs_pos
  -- From finiteness of `round x`, derive `|x| < 2^(max_exp+1)`.
  have hx_lt_max : |x| < (2 : R) ^ (FloatFormat.max_exp + 1) := by
    by_contra h; push_neg at h
    have hx_lt_ot_imp : FloatFormat.overflowThreshold R ≤ |x| :=
      le_trans (le_of_lt FloatFormat.overflowThreshold_lt_zpow_max_exp_succ) h
    rcases lt_or_gt_of_ne hx_ne with hneg | hpos
    · have habs_neg : |x| = -x := abs_of_neg hneg
      rw [habs_neg] at hx_lt_ot_imp
      have := RModeNearest.overflow_pos_inf (-x) hx_lt_ot_imp
      have hconj := RModeConj.round_neg x hx_ne
      rw [hf, Fp.neg_finite] at hconj
      rw [hconj] at this; cases this
    · have habs_pos : |x| = x := abs_of_pos hpos
      rw [habs_pos] at hx_lt_ot_imp
      have := RModeNearest.overflow_pos_inf x hx_lt_ot_imp
      rw [this] at hf; cases hf
  rcases lt_or_gt_of_ne hx_ne with hneg | hpos
  · -- Negative input: reduce to positive via `RModeConj`.
    have hNR_neg : isNormalRange (-x) := by
      refine ⟨?_, ?_⟩
      · rwa [abs_of_neg hneg] at hx_lb
      · rwa [abs_of_neg hneg] at hx_lt_max
    have hconj : (RMode.round (-x) : Fp) = Fp.finite (-f) := by
      rw [RModeConj.round_neg x hx_ne, hf, Fp.neg_finite]
    have h := KahanSum.standard_error_additive (-x) hNR_neg (-f) hconj
    rw [FiniteFp.toVal_neg_eq_neg (R := R) f, abs_neg] at h
    have hrewrite : |(-(f.toVal : R)) - (-x)| = |(f.toVal : R) - x| := by
      rw [show (-(f.toVal : R)) - (-x) = -((f.toVal : R) - x) from by ring, abs_neg]
    rwa [hrewrite] at h
  · -- Positive input: direct application.
    have hNR : isNormalRange x := by
      refine ⟨?_, ?_⟩
      · rwa [abs_of_pos hpos] at hx_lb
      · rwa [abs_of_pos hpos] at hx_lt_max
    exact KahanSum.standard_error_additive x hNR f hf

end RoundPreserves
