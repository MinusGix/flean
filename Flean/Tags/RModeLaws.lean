import Flean.Operations.RoundIntSig
import Flean.Rounding.ModeClass

/-!
# Bundled Rounding-Mode Laws

Most tag propagation theorems take the same six instance hypotheses:

```
[RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
[RModeConj R] [RModeZero R]
```

`RModeNearest R` already extends `RModeC R → RModeZero R`, so the last
is technically redundant — but Lean's instance inference often
benefits from having it declared explicitly.

This file bundles the remaining (R-parametric `Prop`-valued) laws
into a single convenience class `RModeLaws R`, so call-site `variable`
blocks can shrink from six to three lines.

(Naming: earlier draft called this `FPAxioms`; renamed to `RModeLaws`
to stay in the `RMode*` family used across `Flean/Rounding/` and to
avoid the visual overload of "axiom" in Lean source — these are
provable laws about particular rounding-mode instances, not trusted
`axiom` declarations.)

## Design note

`RMode R` and `RModeExec` are data-providing (not `Prop`-valued), so
they can't cleanly be bundled with the rest.  Users writing new
propagation theorems against `RModeLaws R` still need to take
`[RMode R]` and `[RModeExec]` separately:

```
variable [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R] [RMode R] [RModeExec] [RModeLaws R]
```

Compared to the six-instance list, this is a modest but real
reduction.  Retrofit of existing theorems is **not attempted** here
— the existing explicit-list form continues to work and coexists
with new `RModeLaws`-based code.  A blanket retrofit would touch
20+ files and is deferred.

## Downstream

When a future tag-inference engine lands, it can assume
`[RModeLaws R]` uniformly rather than probe for individual laws.
-/

namespace Flean.Tags

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Bundled rounding-mode laws — the common suite used by tag
propagation theorems.

Does NOT bundle `RMode R` or `RModeExec` (those provide data, not
propositions).  Callers still declare them separately.

`RModeZero R` comes free from `RModeNearest R → RModeC R → RModeZero R`;
included here explicitly for Lean's instance inference. -/
class RModeLaws (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] : Prop extends
    RoundIntSigMSound R, RModeNearest R, RModeConj R, RModeZero R

/-- Construct `RModeLaws R` from the individual law instances.  Callers
with the six-instance list automatically get an `RModeLaws R` instance
via this lemma. -/
instance RModeLaws.ofAll [FloatFormat] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeZero R] :
    RModeLaws R := {}

end Flean.Tags
