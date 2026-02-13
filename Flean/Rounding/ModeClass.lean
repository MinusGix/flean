import Flean.Rounding.Rounding

/-!
Typeclass-oriented rounding-mode API.

This is the context-style version: one rounding policy is available in typeclass
context at a time (similar to `FloatFormat`).

`RoundingMode` remains available as a temporary compatibility surface while we
migrate callsites away from value-level mode arguments.
-/

section ModeClass

/-- Contextual rounding interface on a source domain `R`. -/
class RMode (R : Type*) [FloatFormat] where
  round : R → Fp

/-- Rounding preserves exact zero. -/
class RModeZero (R : Type*) [FloatFormat] [Zero R] [RMode R] : Prop where
  round_zero :
    RMode.round (R := R) (0 : R) = Fp.finite 0

/-- Rounding is monotone with respect to the source preorder. -/
class RModeMono (R : Type*) [FloatFormat] [Preorder R] [RMode R] : Prop where
  round_mono :
    ∀ {x y : R}, x ≤ y →
      RMode.round (R := R) x ≤ RMode.round (R := R) y

/-- Rounding is idempotent on already-representable finite floats (excluding `-0`). -/
class RModeIdem (R : Type*) [FloatFormat] [Field R] [RMode R] : Prop where
  round_idempotent :
    ∀ (f : FiniteFp),
      (f.s = false ∨ 0 < f.m) →
      RMode.round (R := R) (f.toVal (R := R)) = Fp.finite f

/-- Common law bundle used in many arithmetic proofs. -/
class RModeC (R : Type*)
    [FloatFormat] [Field R] [Preorder R] [RMode R] : Prop
    extends RModeZero R, RModeMono R, RModeIdem R

/-- Conjugation law for rounding under negation. -/
class RModeConj (R : Type*)
    [FloatFormat] [Zero R] [Neg R] [RMode R] : Prop where
  round_neg :
    ∀ (x : R), x ≠ 0 →
      RMode.round (R := R) (-x) =
        -(RMode.round (R := R) x)

/-- Nearest-mode behavior patterns, stated via observable properties. -/
class RModeNearest (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] : Prop extends RModeC R where
  round_eq_roundDown_or_roundUp :
    ∀ (x : R),
      RMode.round (R := R) x = roundDown x ∨
        RMode.round (R := R) x = roundUp x
  roundDown_le_round :
    ∀ (x : R),
      roundDown x ≤ RMode.round (R := R) x
  round_le_roundUp :
    ∀ (x : R),
      RMode.round (R := R) x ≤ roundUp x
  overflow_pos_inf :
    ∀ (x : R),
      FloatFormat.overflowThreshold R ≤ x →
      RMode.round (R := R) x = Fp.infinite false

/-- RoundIntSig-facing execution hooks.

`RModeExec` contains only the operational branch decisions needed by the
`roundIntSig` algorithm. Semantic correctness is tracked separately in
`RModeExecSound`.

`cancelSignOnExactZero` is used by add/FMA exact-cancellation cases: when the
exact result is 0 and operand signs disagree, IEEE-754 chooses `-0` only for
roundTowardNegative. -/
class RModeExec [FloatFormat] where
  shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool
  handleOverflow : Bool → Fp
  cancelSignOnExactZero : Bool := false

/-- Backward-compatible alias (deprecated in favor of `RModeExec`). -/
abbrev RModeRoundIntPolicy [FloatFormat] := RModeExec

/-- Canonical scaled value used by execution-soundness laws. -/
def execScaledVal (R : Type) [Field R] (sign : Bool) (q r shift : ℕ) : R :=
  let mag : R := (q : R) + (r : R) / ((2 : R) ^ (shift : ℤ))
  if sign then -mag else mag

/-- Soundness contract connecting execution hooks to semantic rounding. -/
class RModeExecSound (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] : Prop where
  chooseUp_exact :
    ∀ (sign : Bool) (q shift : ℕ),
      RModeExec.shouldRoundUp sign q 0 shift = false
  overflow_round_characterization :
    ∀ (sign : Bool) (x : R),
      FloatFormat.overflowThreshold R ≤ x →
      RModeExec.handleOverflow sign =
        RMode.round (R := R) (if sign then -x else x)

/-- Tie-breaking policy: ties-to-even. -/
class RModeTieEven [FloatFormat] [RModeExec] : Prop where
  tie_round_up_iff_odd :
    ∀ (sign : Bool) (q shift : ℕ),
      0 < shift →
      RModeExec.shouldRoundUp sign q (2 ^ (shift - 1)) shift = (q % 2 ≠ 0)

/-- Tie-breaking policy: ties-away-from-zero. -/
class RModeTieAway [FloatFormat] [RModeExec] : Prop where
  tie_round_up :
    ∀ (sign : Bool) (q shift : ℕ),
      0 < shift →
      RModeExec.shouldRoundUp sign q (2 ^ (shift - 1)) shift = true

/-- Value-level branch logic for `shouldRoundUp`, used for compatibility shims. -/
def shouldRoundUpMode (mode : RoundingMode) (sign : Bool) (q r : ℕ) (shift : ℕ) : Bool :=
  if r = 0 then false
  else match mode with
  | .Down => sign
  | .Up => !sign
  | .TowardZero => false
  | .NearestTiesToEven =>
    let half := 2^(shift - 1)
    if r > half then true
    else if r < half then false
    else q % 2 ≠ 0
  | .NearestTiesAwayFromZero =>
    let half := 2^(shift - 1)
    r ≥ half

/-- IEEE-754 overflow target for a value-level rounding mode. -/
def handleOverflowMode [FloatFormat] (mode : RoundingMode) (sign : Bool) : Fp :=
  match mode with
  | .Down =>
    if sign then Fp.infinite true
    else Fp.finite FiniteFp.largestFiniteFloat
  | .Up =>
    if sign then Fp.finite (-FiniteFp.largestFiniteFloat)
    else Fp.infinite false
  | .TowardZero =>
    if sign then Fp.finite (-FiniteFp.largestFiniteFloat)
    else Fp.finite FiniteFp.largestFiniteFloat
  | .NearestTiesToEven => Fp.infinite sign
  | .NearestTiesAwayFromZero => Fp.infinite sign

/-- Signed-zero choice for exact cancellation (`+0` vs `-0`). -/
def cancelSignOnExactZeroMode (mode : RoundingMode) : Bool :=
  mode = .Down

/-- Compatibility dictionary: build an `RModeExec` from a value-level mode. -/
def rModeExecOf (mode : RoundingMode) [FloatFormat] : RModeExec where
  shouldRoundUp := shouldRoundUpMode mode
  handleOverflow := handleOverflowMode mode
  cancelSignOnExactZero := cancelSignOnExactZeroMode mode

/-- Compatibility dictionary: build an `RMode` from a value-level mode. -/
def rModeOf (mode : RoundingMode) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [FloatFormat] :
    RMode R where
  round := mode.round

end ModeClass
