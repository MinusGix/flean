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

/-- Notation for contextual rounding. -/
prefix:max "○" => RMode.round

namespace Fp

variable [FloatFormat]

/-- Explicit-map exactness: `f` is the exact finite result of applying `ρ` to `x`. -/
def ExactRoundWith {R : Type*} [Field R] (ρ : R → Fp) (x : R) (f : FiniteFp) : Prop :=
  ρ x = Fp.finite f ∧ Represents x f

/-- Contextual exactness under the active rounding dictionary. -/
abbrev ExactRound {R : Type*} [Field R] [RMode R] (x : R) (f : FiniteFp) : Prop :=
  ExactRoundWith (fun y => ○y) x f

@[simp] theorem exactRoundWith_iff {R : Type*} [Field R] (ρ : R → Fp) (x : R) (f : FiniteFp) :
    ExactRoundWith ρ x f ↔ ρ x = Fp.finite f ∧ ⌞f⌟ = x := by
  rfl

@[simp] theorem exactRound_iff {R : Type*} [Field R] [RMode R] (x : R) (f : FiniteFp) :
    ExactRound x f ↔ ○x = Fp.finite f ∧ ⌞f⌟ = x := by
  rfl

theorem ExactRoundWith.round_eq {R : Type*} [Field R] {ρ : R → Fp} {x : R} {f : FiniteFp}
    (h : ExactRoundWith ρ x f) : ρ x = Fp.finite f :=
  h.1

theorem ExactRoundWith.toVal_eq {R : Type*} [Field R] {ρ : R → Fp} {x : R} {f : FiniteFp}
    (h : ExactRoundWith ρ x f) : ⌞f⌟ = x :=
  h.2

theorem ExactRound.round_eq {R : Type*} [Field R] [RMode R] {x : R} {f : FiniteFp}
    (h : ExactRound x f) : ○x = Fp.finite f :=
  h.1

theorem ExactRound.toVal_eq {R : Type*} [Field R] [RMode R] {x : R} {f : FiniteFp}
    (h : ExactRound x f) : ⌞f⌟ = x :=
  h.2

end Fp

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

/-- Rounding preserves grid alignment.

If `x = n * 2^g` for integer `n` and grid level `g` at or above the finest
FP grid, then `round(x)` (when finite) is also a multiple of `2^g`.

This holds for all IEEE rounding modes: at any binade whose ULP divides
`2^g`, every candidate float is already a multiple of `2^g`. -/
class RModeGrid (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] : Prop where
  round_preserves_grid :
    ∀ (n : ℤ) (g : ℤ),
      g ≥ FloatFormat.min_exp - FloatFormat.prec + 1 →
      ∀ (f : FiniteFp), ○((n : R) * (2 : R) ^ g) = Fp.finite f →
        ∃ m : ℤ, f.toVal (R := R) = (m : R) * (2 : R) ^ g

/- 2Sum splitting properties under nearest rounding.

For `s = round(a + b)` and `bv = round(s − a)`, the intermediate values
`s − bv` and `b − bv` are always exactly representable. These are the key
exactness properties that make the 6-operation 2Sum algorithm correct.

These hold for all IEEE nearest-rounding modes (ties-to-even and
ties-away-from-zero). The proof uses grid analysis: both `s` and `bv`
inherit the grid alignment of `a + b`, and the coefficient bounds follow
from the nearest-rounding error constraints. -/
/-- Combined representability witness for 2Sum splitting intermediates. -/
structure SplitWitness (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (a b s bv : FiniteFp) where
  /-- Witness for representability of `s - bv` (virtual `a` part). -/
  avRep : FiniteFp
  /-- Witness for representability of `b - bv` (roundoff part). -/
  brRep : FiniteFp
  avValid : avRep.s = false ∨ 0 < avRep.m
  brValid : brRep.s = false ∨ 0 < brRep.m
  avVal : avRep.toVal (R := R) = s.toVal - bv.toVal
  brVal : brRep.toVal (R := R) = b.toVal - bv.toVal

class RModeSplit (R : Type*)
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] where
  /-- After `s = round(a+b)` and `bv = round(s−a)`, both `s − bv` and
      `b − bv` are representable. -/
  split_witness :
    ∀ (a b s : FiniteFp),
      ○((a.toVal : R) + b.toVal) = Fp.finite s →
      ∀ (bv : FiniteFp),
        ○((s.toVal : R) - a.toVal) = Fp.finite bv →
        SplitWitness (R := R) a b s bv

namespace RModeSplit

/-- Projection: representability of `s - bv` from `split_witness`. -/
theorem split_s_sub_bv
    {R : Type*}
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeSplit R]
    (a b s : FiniteFp)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = s.toVal - bv.toVal := by
  let w := RModeSplit.split_witness (R := R) a b s hs bv hbv
  exact ⟨w.avRep, w.avValid, w.avVal⟩

/-- Projection: representability of `b - bv` from `split_witness`. -/
theorem split_b_sub_bv
    {R : Type*}
    [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeSplit R]
    (a b s : FiniteFp)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = b.toVal - bv.toVal := by
  let w := RModeSplit.split_witness (R := R) a b s hs bv hbv
  exact ⟨w.brRep, w.brValid, w.brVal⟩

end RModeSplit

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
  round_ge_two_x_sub_succ :
    ∀ (x : R) (hxpos : 0 < x) (_hx : isNormalRange x)
      (f : FiniteFp) (succ : FiniteFp),
      RMode.round (R := R) x = Fp.finite f →
      findSuccessorPos x hxpos = Fp.finite succ →
      (2 * x - succ.toVal : R) ≤ f.toVal

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
