import Flean.Operations.Activations.Tanh
import Flean.Operations.Activations.SigmoidFp
import Flean.Operations.Add
import Flean.Operations.Sub

/-!
# Floating-Point Tanh

FP-arithmetic implementation of `tanh` paired with the math reference
`Real.tanh`. Routes through `fpSigmoidFinite` via the identity
`tanh x = 2·σ(2x) − 1`.

## Pipeline

1. `tx = x + x` (FP doubling — exact when no overflow).
2. `sx = fpSigmoidFinite tx` (= σ(2x)).
3. `tsx = sx + sx` (= 2·σ(2x)).
4. `result = tsx − 1` (= 2σ(2x) − 1).

## Special cases (`fpTanh : Fp → Fp`)

* `NaN ↦ NaN`
* `+∞ ↦ Fp.finite 1` (tanh(+∞) = 1)
* `−∞ ↦ Fp.finite (−1)` (tanh(−∞) = −1)
* finite ↦ `fpTanhFinite`
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RModeExec] [ExpApprox]

/-- Floating-point tanh kernel for finite inputs.

Computes `tanh(x) = 2·σ(2x) − 1` via FP doubling, sigmoid, doubling, sub. -/
noncomputable def fpTanhFinite (x : FiniteFp) : Fp :=
  match fpAddFinite x x with
  | .NaN => .NaN
  | .infinite s => .infinite s
  | .finite tx =>
      match fpSigmoidFinite tx with
      | .NaN => .NaN
      | .infinite s => .infinite s
      | .finite sx =>
          match fpAddFinite sx sx with
          | .NaN => .NaN
          | .infinite s => .infinite s
          | .finite tsx => fpSubFinite tsx (1 : FiniteFp)

/-- IEEE-style FP tanh `Fp → Fp`.

* `NaN ↦ NaN`
* `+∞ ↦ Fp.finite 1` (tanh(+∞) = 1, exactly representable)
* `−∞ ↦ Fp.finite (−1)` (tanh(−∞) = −1, exactly representable)
* finite ↦ `fpTanhFinite` -/
noncomputable def fpTanh (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .finite 1
  | .infinite true => .finite (-1)
  | .finite a => fpTanhFinite a

@[simp] theorem fpTanh_finite (a : FiniteFp) :
    fpTanh (Fp.finite a) = fpTanhFinite a := rfl

@[simp] theorem fpTanh_nan :
    fpTanh Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpTanh_pos_inf :
    fpTanh (Fp.infinite false) = Fp.finite 1 := rfl

@[simp] theorem fpTanh_neg_inf :
    fpTanh (Fp.infinite true) = Fp.finite (-1) := rfl

/-! ## Result-shape characterisations -/

/-- Finite-path reduction: when all four intermediate steps land in
finite range, the result is `fpSubFinite tsx 1`. -/
theorem fpTanhFinite_eq_sub_of_finite (x : FiniteFp) {tx sx tsx : FiniteFp}
    (hdbl1 : fpAddFinite x x = Fp.finite tx)
    (hsig : fpSigmoidFinite tx = Fp.finite sx)
    (hdbl2 : fpAddFinite sx sx = Fp.finite tsx) :
    fpTanhFinite x = fpSubFinite tsx (1 : FiniteFp) := by
  unfold fpTanhFinite
  rw [hdbl1]
  simp only
  rw [hsig]
  simp only
  rw [hdbl2]

/-- NaN propagation through any of the four steps. -/
theorem fpTanhFinite_of_dbl1_nan (x : FiniteFp)
    (h : fpAddFinite x x = Fp.NaN) :
    fpTanhFinite x = Fp.NaN := by
  unfold fpTanhFinite
  rw [h]

end Flean
