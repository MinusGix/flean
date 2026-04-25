import Flean.StorageFormats.FromFp
import Flean.StorageFormats.Conversion
import Flean.Operations.RoundIntSigPolicySound
import Flean.Rounding.RoundPreserves

/-!
# `NarrowingContext`: bundled typeclasses for narrowing into a `StorageFormat`

The mixed-precision narrowing theorems need *seven* separate hypotheses
about the rounding mode for the narrow `FloatFormat` (`sf.toFloatFormat`):
`RMode`, `RModeExec`, `RoundIntSigMSound`, `RModeNearest`, `RModeConj`,
`RModeZero`, plus an `h_shouldRoundUp = rneRoundUp` law.  When the narrow
format is *different* from the ambient `[FloatFormat]` typeclass, we
cannot supply these as instance arguments without ambiguity, so they
have to be passed as explicit `@`-form arguments — adding ~15 lines of
boilerplate per theorem.

`NarrowingContext R sf` bundles all seven into one structure (plus the
three format-validity proofs `sf.manBits ≥ 1`, etc.), letting consumer
theorems take a single `(ctx : NarrowingContext R sf)` argument.

## Constructing one

The default constructor is `NarrowingContext.ofRNE`, which takes a
`[UseRoundingPolicy RoundNearestEvenPolicy]` instance and the three
format-validity proofs, and synthesizes everything else under a `letI`
that sets the ambient `FloatFormat` to `sf.toFloatFormat`.
-/

namespace StorageFp

/-- Bundle of all rounding-mode typeclasses + format-validity proofs
needed to narrow into a `StorageFormat sf`. -/
structure NarrowingContext (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (sf : StorageFormat) where
  h_prec : sf.manBits ≥ 1
  h_bias : sf.bias ≥ 1
  h_exp : sf.maxExpField > sf.bias
  instM : @RMode R (sf.toFloatFormat h_prec h_bias h_exp)
  execNarrow : @RModeExec (sf.toFloatFormat h_prec h_bias h_exp)
  soundNarrow :
    @RoundIntSigMSound R _ _ _ _ (sf.toFloatFormat h_prec h_bias h_exp) instM execNarrow
  nearestNarrow :
    @RModeNearest R (sf.toFloatFormat h_prec h_bias h_exp) _ _ _ _ instM
  conjNarrow :
    @RModeConj R (sf.toFloatFormat h_prec h_bias h_exp) _ _ instM
  zeroNarrow :
    @RModeZero R (sf.toFloatFormat h_prec h_bias h_exp) _ instM
  isRNE : ∀ s q r sh,
    @RModeExec.shouldRoundUp _ execNarrow s q r sh = rneRoundUp s q r sh

namespace NarrowingContext

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable {sf : StorageFormat}

/-- The narrow `FloatFormat` carried by a `NarrowingContext`. -/
abbrev floatFormat (ctx : NarrowingContext R sf) : FloatFormat :=
  sf.toFloatFormat ctx.h_prec ctx.h_bias ctx.h_exp

/-- Build a `NarrowingContext` from an ambient
`[UseRoundingPolicy RoundNearestEvenPolicy]` typeclass.

The format-validity proofs are taken explicitly; the typeclass
instances for the narrow `sf.toFloatFormat` are synthesized under a
`letI` that fixes the `FloatFormat` scope. -/
def ofRNE (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (sf : StorageFormat)
    (h_prec : sf.manBits ≥ 1) (h_bias : sf.bias ≥ 1) (h_exp : sf.maxExpField > sf.bias)
    [UseRoundingPolicy RoundNearestEvenPolicy] :
    NarrowingContext R sf :=
  letI : FloatFormat := sf.toFloatFormat h_prec h_bias h_exp
  { h_prec := h_prec
    h_bias := h_bias
    h_exp := h_exp
    instM := inferInstance
    execNarrow := inferInstance
    soundNarrow := inferInstance
    nearestNarrow := inferInstance
    conjNarrow := inferInstance
    zeroNarrow := inferInstance
    isRNE := fun _ _ _ _ => rfl }

end NarrowingContext

end StorageFp
