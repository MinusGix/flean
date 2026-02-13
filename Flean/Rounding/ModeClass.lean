import Flean.Rounding.Rounding

/-!
Typeclass-oriented rounding-mode API.

This is the context-style version: one rounding policy is available in typeclass
context at a time (similar to `FloatFormat`).
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
  round_le_two_x_sub_pred :
    ∀ (x : R) (hxpos : 0 < x) (_hx : isNormalRange x) (f : FiniteFp),
      RMode.round (R := R) x = Fp.finite f →
      (f.toVal : R) ≤ 2 * x - (findPredecessorPos x hxpos).toVal

/-- RoundIntSig-facing execution hooks.

`RModeExec` contains only the operational branch decisions needed by the
`roundIntSigM` algorithm. Semantic correctness is tracked separately in
`RModeExecSound`.

`cancelSignOnExactZero` is used by add/FMA exact-cancellation cases: when the
exact result is 0 and operand signs disagree, IEEE-754 chooses `-0` only for
roundTowardNegative. -/
class RModeExec [FloatFormat] where
  shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool
  handleOverflow : Bool → Fp
  cancelSignOnExactZero : Bool := false

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

/-! ## Policy Markers -/

/-- Marker type for round-toward-negative-infinity policy. -/
inductive RoundTowardNegPolicy : Type
| tag

/-- Marker type for round-toward-positive-infinity policy. -/
inductive RoundTowardPosPolicy : Type
| tag

/-- Marker type for round-toward-zero policy. -/
inductive RoundTowardZeroPolicy : Type
| tag

/-- Marker type for round-to-nearest, ties-to-even policy. -/
inductive RoundNearestEvenPolicy : Type
| tag

/-- Marker type for round-to-nearest, ties-away-from-zero policy. -/
inductive RoundNearestAwayPolicy : Type
| tag

/-- Activates a contextual rounding-policy marker type. -/
class UseRoundingPolicy (P : Type) : Prop where

/-- Canonical policy identity used for shared adapter theorems. -/
inductive RModePolicyKind : Type
| towardNeg
| towardPos
| towardZero
| nearestEven
| nearestAway
deriving DecidableEq

/-- Canonical policy-level rounding function. -/
def policyRound (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [FloatFormat] (k : RModePolicyKind) : R → Fp :=
  match k with
  | .towardNeg => roundDown
  | .towardPos => roundUp
  | .towardZero => roundTowardZero
  | .nearestEven => roundNearestTiesToEven
  | .nearestAway => roundNearestTiesAwayFromZero

/-- Canonical policy-level tie decision function used by `roundIntSigM`. -/
def policyShouldRoundUp (k : RModePolicyKind) (sign : Bool) (q r shift : ℕ) : Bool :=
  match k with
  | .towardNeg => if r = 0 then false else sign
  | .towardPos => if r = 0 then false else !sign
  | .towardZero => false
  | .nearestEven =>
      if r = 0 then false
      else
        let half := 2 ^ (shift - 1)
        if r > half then true
        else if r < half then false
        else q % 2 ≠ 0
  | .nearestAway =>
      if r = 0 then false
      else
        let half := 2 ^ (shift - 1)
        r ≥ half

/-- Canonical policy-level overflow result. -/
def policyHandleOverflow [FloatFormat] (k : RModePolicyKind) (sign : Bool) : Fp :=
  match k with
  | .towardNeg =>
      if sign then Fp.infinite true else Fp.finite FiniteFp.largestFiniteFloat
  | .towardPos =>
      if sign then Fp.finite (-FiniteFp.largestFiniteFloat) else Fp.infinite false
  | .towardZero =>
      if sign then Fp.finite (-FiniteFp.largestFiniteFloat) else Fp.finite FiniteFp.largestFiniteFloat
  | .nearestEven => Fp.infinite sign
  | .nearestAway => Fp.infinite sign

/-- Canonical exact-cancellation signed-zero behavior for each policy. -/
def policyCancelSignOnExactZero (k : RModePolicyKind) : Bool :=
  decide (k = .towardNeg)

/-- Signed-zero selection for exact cancellation between two signed terms. -/
def exactCancelSign [FloatFormat] [RModeExec] (sx sy : Bool) : Bool :=
  if sx = sy then sx else RModeExec.cancelSignOnExactZero

/-- Policy conjugate used by sign-transport lemmas. -/
def RModePolicyKind.conjugate : RModePolicyKind → RModePolicyKind
  | .towardNeg => .towardPos
  | .towardPos => .towardNeg
  | .towardZero => .towardZero
  | .nearestEven => .nearestEven
  | .nearestAway => .nearestAway

/-- Bridge class exposing which concrete policy dictionary is active. -/
class RModePolicyTag (R : Type*)
    [FloatFormat] [RMode R] [RModeExec] where
  kind : RModePolicyKind

/-- Adapter laws tying contextual dictionaries to the canonical policy profile. -/
class RModePolicySpec (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] extends RModePolicyTag R where
  round_eq_policy :
    ∀ (x : R),
      RMode.round (R := R) x = policyRound R kind x
  shouldRoundUp_eq_policy :
    ∀ (sign : Bool) (q r shift : ℕ),
      RModeExec.shouldRoundUp sign q r shift =
        policyShouldRoundUp kind sign q r shift
  handleOverflow_eq_policy :
    ∀ (sign : Bool),
      RModeExec.handleOverflow sign = policyHandleOverflow kind sign
  cancelSignOnExactZero_eq_policy :
    RModeExec.cancelSignOnExactZero = policyCancelSignOnExactZero kind

/-- `exactCancelSign` reduced to the canonical policy profile. -/
theorem exactCancelSign_eq_policy {R : Type*}
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RModePolicySpec R]
    (sx sy : Bool) :
    exactCancelSign sx sy =
      (if sx = sy then sx else policyCancelSignOnExactZero (RModePolicyTag.kind (R := R))) := by
  simp [exactCancelSign, RModePolicySpec.cancelSignOnExactZero_eq_policy (R := R)]

end ModeClass
