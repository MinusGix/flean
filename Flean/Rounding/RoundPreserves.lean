import Flean.Rounding.ModeClass
import Flean.Order

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

Future additions (as tags demand):
- `round_preserves_pos` (strict positivity) — needs a strengthened
  version of `RModeMono` that handles `<` directly.
- `round_preserves_abs_bound` — for `|·| ≤ c` tags.
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

end RoundPreserves
