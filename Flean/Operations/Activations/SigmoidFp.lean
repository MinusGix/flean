import Flean.Operations.Activations.Sigmoid
import Flean.Operations.Exp
import Flean.Operations.Add
import Flean.Operations.Div

/-!
# Floating-Point Sigmoid

FP-arithmetic implementation of the sigmoid activation, paired with the
math reference `Real.sigmoid` shipped in `Activations/Sigmoid.lean`.

## Design

`σ(x) = 1 / (1 + exp(-x))`, computed via three primitive FP operations:

1. `e := fpExpFinite (-x)` — exponentiation. *May overflow* when `-x` is
   very large (i.e. `x` very negative); flean's `fpExpFinite` returns
   `Fp` (not `FiniteFp`) to surface this honestly.
2. `d := 1 + e` — adding the constant `1`. Cannot overflow when `e` is
   finite, since `1 + e ≤ 1 + largestFp ≈ largestFp` (in the standard
   FP formats).
3. `1 / d` — reciprocal. Cannot overflow since `d ≥ 1` ⟹ `1/d ≤ 1`.

We surface the same `Fp → Fp` IEEE-style propagation flean uses for
`fpExp`/`fpLog`:

* `NaN ↦ NaN`;
* `+∞ ↦ 1` (since `σ(+∞) = 1` is exactly representable);
* `-∞ ↦ 0` (since `σ(-∞) = 0` is exactly representable);
* finite input ↦ `fpSigmoidFinite`.

The exp-overflow case (very negative `x`) is short-circuited inside
`fpSigmoidFinite` to `Fp.finite 0` exactly — this corresponds to the
math limit `σ(-∞) = 0` and yields a clean `0` instead of `1 / +∞`.

## Result-shape theorems

* `fpSigmoidFinite_neg_overflow` — overflow path returns `Fp.finite 0`.
* `fpSigmoidFinite_eq_div_of_finite` — when `fpExpFinite (-x)` and
  `1 + e` are both finite, the result is `1 / (1 + e)`.

The toVal-vs-`Real.sigmoid` slack analysis (composing `fpExpFinite_correct`
with the rounding-error bounds on `fpAddFinite` / `fpDivFinite`) is
deferred to a follow-up file shipping the `ActivationFpResult` bundle.
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RModeExec] [ExpApprox]

/-- Floating-point sigmoid kernel for finite inputs.

Computes `1 / (1 + exp(-x))` with explicit propagation of exp's overflow
to a clean `Fp.finite 0` short-circuit. See module docstring for the
overall design and special-case handling.

Defined directly in terms of `fpAddFinite` / `fpDivFinite` (rather than
the overloaded `+` / `/` operators) so that goal-rewriting on result-shape
characterisations matches the theorem hypotheses syntactically. -/
noncomputable def fpSigmoidFinite (x : FiniteFp) : Fp :=
  match fpExpFinite (-x) with
  | .NaN => .NaN
  | .infinite false => .finite 0
  | .infinite true => .NaN
  | .finite e =>
      match fpAddFinite (1 : FiniteFp) e with
      | .NaN => .NaN
      | .infinite s => .infinite s
      | .finite d => fpDivFinite (1 : FiniteFp) d

/-- IEEE-style FP sigmoid: `Fp → Fp` with full special-case propagation. -/
noncomputable def fpSigmoid (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .finite 1
  | .infinite true => .finite 0
  | .finite a => fpSigmoidFinite a

@[simp] theorem fpSigmoid_finite (a : FiniteFp) :
    fpSigmoid (Fp.finite a) = fpSigmoidFinite a := rfl

@[simp] theorem fpSigmoid_nan :
    fpSigmoid Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpSigmoid_pos_inf :
    fpSigmoid (Fp.infinite false) = Fp.finite 1 := rfl

@[simp] theorem fpSigmoid_neg_inf :
    fpSigmoid (Fp.infinite true) = Fp.finite 0 := rfl

/-! ## Result-shape characterisations

The theorem hypotheses use `fpAddFinite` / `fpDivFinite` directly rather
than the overloaded `+` / `/` operators, since the function body's
`(1 : FiniteFp) + e` resolves to `fpAddFinite (1 : FiniteFp) e` and
goal-rewriting is more reliable when the hypothesis matches the same
syntactic form. -/

/-- Overflow short-circuit: if `exp(-x)` overflows to `+∞`, the FP sigmoid
returns `Fp.finite 0` exactly (matching the math limit `σ(-∞) = 0`). -/
theorem fpSigmoidFinite_of_exp_pos_inf (x : FiniteFp)
    (h : fpExpFinite (-x) = Fp.infinite false) :
    fpSigmoidFinite x = Fp.finite 0 := by
  unfold fpSigmoidFinite
  rw [h]

/-- Finite-path reduction: if both `fpExpFinite (-x)` and the subsequent
`fpAddFinite 1 e` land in finite range, `fpSigmoidFinite x` reduces to
`fpDivFinite 1 d`. -/
theorem fpSigmoidFinite_eq_div_of_finite (x : FiniteFp) {e d : FiniteFp}
    (he : fpExpFinite (-x) = Fp.finite e)
    (hd : fpAddFinite (1 : FiniteFp) e = Fp.finite d) :
    fpSigmoidFinite x = fpDivFinite (1 : FiniteFp) d := by
  unfold fpSigmoidFinite
  rw [he]
  simp only
  rw [hd]

/-- Pure NaN propagation through the exp step. -/
theorem fpSigmoidFinite_of_exp_nan (x : FiniteFp)
    (h : fpExpFinite (-x) = Fp.NaN) :
    fpSigmoidFinite x = Fp.NaN := by
  unfold fpSigmoidFinite
  rw [h]

end Flean
