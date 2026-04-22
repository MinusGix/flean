import Flean.Operations.RoundIntSig
import Flean.Rounding.ModeClass

/-!
# Bundled FP Soundness Axioms

Most tag propagation theorems take the same six instance hypotheses:

```
[RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
[RModeConj R] [RModeZero R]
```

`RModeNearest R` already extends `RModeC R → RModeZero R`, so the last
is technically redundant — but Lean's instance inference often
benefits from having it declared explicitly.

This file bundles the remaining (R-parametric `Prop`-valued) axioms
into a single convenience class `FPAxioms R`, so call-site `variable`
blocks can shrink from six to three lines.

## Design note

`RMode R` and `RModeExec` are data-providing (not `Prop`-valued), so
they can't cleanly be bundled with the rest.  Users writing new
propagation theorems against `FPAxioms R` still need to take
`[RMode R]` and `[RModeExec]` separately:

```
variable [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R] [RMode R] [RModeExec] [FPAxioms R]
```

Compared to the six-instance list, this is a modest but real
reduction.  Retrofit of existing theorems is **not attempted** here
— the existing explicit-list form continues to work and coexists
with new `FPAxioms`-based code.  A blanket retrofit would touch
20+ files and is deferred.

## Downstream

When a future tag-inference engine lands, it can assume
`[FPAxioms R]` uniformly rather than probe for individual axioms.
-/

namespace Flean.Tags

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Bundled FP soundness axioms — the common suite used by tag
propagation theorems.

Does NOT bundle `RMode R` or `RModeExec` (those provide data, not
propositions).  Callers still declare them separately.

`RModeZero R` comes free from `RModeNearest R → RModeC R → RModeZero R`;
included here explicitly for Lean's instance inference. -/
class FPAxioms (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] : Prop extends
    RoundIntSigMSound R, RModeNearest R, RModeConj R, RModeZero R

/-- Construct `FPAxioms R` from the individual axiom instances.  Callers
with the six-instance list automatically get an `FPAxioms R` instance
via this lemma. -/
instance FPAxioms.ofAll [FloatFormat] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeZero R] :
    FPAxioms R := {}

end Flean.Tags
