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
  the normal-range regime.

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

end RoundPreserves
