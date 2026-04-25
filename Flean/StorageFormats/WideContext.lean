import Flean.Operations.RoundIntSigPolicySound
import Flean.Rounding.RoundPreserves

/-!
# `WideContext`: bundled typeclasses for the wide format in mixed precision

Parallel to `StorageFp.NarrowingContext` (which bundles narrow-format
typeclasses for `sf.toFloatFormat`).  Mixed-precision operations need
typeclass instances at *both* the wide and narrow `FloatFormat`s, and
each invocation refers to a non-ambient format — so each side gets a
bundle.

`WideContext R ff_wide` carries the rounding-mode typeclasses needed to
do FP arithmetic in `ff_wide` and prove its standard error bounds.
-/

set_option autoImplicit false

namespace StorageFp

/-- Bundle of rounding-mode typeclasses at the wide `FloatFormat`. -/
structure WideContext (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat) where
  instM : @RMode R ff_wide
  execWide : @RModeExec ff_wide
  soundWide : @RoundIntSigMSound R _ _ _ _ ff_wide instM execWide
  nearestWide : @RModeNearest R ff_wide _ _ _ _ instM
  conjWide : @RModeConj R ff_wide _ _ instM
  zeroWide : @RModeZero R ff_wide _ instM

namespace WideContext

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable {ff_wide : FloatFormat}

/-- Build a `WideContext` from an ambient
`[UseRoundingPolicy RoundNearestEvenPolicy]` typeclass.

Synthesizes the six rounding-mode instances under a `letI` that fixes
the `FloatFormat` scope to `ff_wide`. -/
def ofRNE (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (ff_wide : FloatFormat)
    [UseRoundingPolicy RoundNearestEvenPolicy] :
    WideContext R ff_wide :=
  letI : FloatFormat := ff_wide
  { instM := inferInstance
    execWide := inferInstance
    soundWide := inferInstance
    nearestWide := inferInstance
    conjWide := inferInstance
    zeroWide := inferInstance }

end WideContext

end StorageFp
