import Flean.Operations.Activations.Gelu
import Flean.Operations.Activations.TanhFp
import Flean.Operations.Activations.TanhFpClose
import Flean.Operations.Add
import Flean.Operations.Mul

/-!
# Floating-Point GeLU (tanh approximation)

FP-arithmetic implementation of the gelu tanh-approximation form.
Constants `c ≈ √(2/π)`, `α ≈ 0.044715`, and `0.5` are supplied as
FiniteFp parameters: flean's FloatFormat doesn't ship irrational
constants, so the user provides whatever rounding they want and the
closeness lemma includes the constant-error contribution.

## Pipeline (9 FP ops)

```
1. x² = x · x
2. x³ = x² · x
3. αx³ = α · x³
4. inner = x + αx³
5. u = c · inner
6. t = fpTanh(u)
7. one_plus_t = 1 + t
8. half_x = half · x
9. result = half_x · one_plus_t
```

`fpTanh(u)` itself routes through 4 internal FP ops + `fpSigmoidFinite`
(see `TanhFp.lean`).

## API shape

`fpGeluFinite_with` takes the three FP constants `(half, α, c)` as
explicit arguments. Downstream consumers wanting the "standard" gelu
supply their preferred quantizations; the closeness lemma absorbs
the constant errors into the slack.
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RModeExec] [ExpApprox]

/-- Floating-point gelu (tanh approximation) kernel. Parametrized over
FP approximations of `0.5`, `α`, and `c`. -/
noncomputable def fpGeluFinite_with
    (half α c : FiniteFp) (x : FiniteFp) : Fp :=
  match fpMulFinite x x with
  | .NaN => .NaN
  | .infinite s => .infinite s
  | .finite x_sq =>
      match fpMulFinite x_sq x with
      | .NaN => .NaN
      | .infinite s => .infinite s
      | .finite x_cu =>
          match fpMulFinite α x_cu with
          | .NaN => .NaN
          | .infinite s => .infinite s
          | .finite ax_cu =>
              match fpAddFinite x ax_cu with
              | .NaN => .NaN
              | .infinite s => .infinite s
              | .finite inner =>
                  match fpMulFinite c inner with
                  | .NaN => .NaN
                  | .infinite s => .infinite s
                  | .finite u =>
                      match fpTanhFinite u with
                      | .NaN => .NaN
                      | .infinite s => .infinite s
                      | .finite t =>
                          match fpAddFinite (1 : FiniteFp) t with
                          | .NaN => .NaN
                          | .infinite s => .infinite s
                          | .finite opt =>
                              match fpMulFinite half x with
                              | .NaN => .NaN
                              | .infinite s => .infinite s
                              | .finite hx => fpMulFinite hx opt

/-- IEEE-style FP gelu wrapper.

* `NaN ↦ NaN`
* `+∞ ↦ +∞` (gelu(+∞) = +∞ in the limit; conservatively keep as `+∞`)
* `−∞ ↦ Fp.finite 0` (gelu(−∞) = 0)
* finite ↦ `fpGeluFinite_with half α c` -/
noncomputable def fpGelu_with
    (half α c : FiniteFp) (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .infinite false
  | .infinite true => .finite 0
  | .finite a => fpGeluFinite_with half α c a

@[simp] theorem fpGelu_with_finite (half α c : FiniteFp) (a : FiniteFp) :
    fpGelu_with half α c (Fp.finite a) = fpGeluFinite_with half α c a := rfl

@[simp] theorem fpGelu_with_nan (half α c : FiniteFp) :
    fpGelu_with half α c Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpGelu_with_pos_inf (half α c : FiniteFp) :
    fpGelu_with half α c (Fp.infinite false) = Fp.infinite false := rfl

@[simp] theorem fpGelu_with_neg_inf (half α c : FiniteFp) :
    fpGelu_with half α c (Fp.infinite true) = Fp.finite 0 := rfl

/-! ## Result-shape -/

/-- Per-step finite-path witness bundle. Encapsulates the 9 intermediate
FP results plus their finite-path equalities. -/
structure GeluFpWitness (half α c : FiniteFp) (x : FiniteFp) where
  /-- Step 1: `x²`. -/
  x_sq : FiniteFp
  /-- Step 2: `x³ = x² · x`. -/
  x_cu : FiniteFp
  /-- Step 3: `α · x³`. -/
  ax_cu : FiniteFp
  /-- Step 4: inner sum `x + α·x³`. -/
  inner : FiniteFp
  /-- Step 5: `u = c · inner`. -/
  u : FiniteFp
  /-- Step 6: `t = tanh(u)` (with internal `TanhFpWitness`). -/
  tanh_w : TanhFpWitness u
  /-- Step 7: `1 + t`. -/
  opt : FiniteFp
  /-- Step 8: `half · x`. -/
  hx : FiniteFp
  /-- Step 9: final result `hx · (1 + t)`. -/
  r : FiniteFp
  /-- Step witnesses. -/
  h_sq : fpMulFinite x x = Fp.finite x_sq
  h_cu : fpMulFinite x_sq x = Fp.finite x_cu
  h_ax_cu : fpMulFinite α x_cu = Fp.finite ax_cu
  h_inner : fpAddFinite x ax_cu = Fp.finite inner
  h_u : fpMulFinite c inner = Fp.finite u
  h_opt : fpAddFinite (1 : FiniteFp) tanh_w.r = Fp.finite opt
  h_hx : fpMulFinite half x = Fp.finite hx
  h_r : fpMulFinite hx opt = Fp.finite r

/-- Finite-path reduction: when all 9 steps land in finite range, the
result is `r` (the final FP product). -/
theorem fpGeluFinite_with_eq_of_witness
    (half α c : FiniteFp) (x : FiniteFp) (w : GeluFpWitness half α c x) :
    fpGeluFinite_with half α c x = Fp.finite w.r := by
  -- Derive the tanh result equality from the inner witnesses.
  have h_sig_eq : fpSigmoidFinite w.tanh_w.tx = Fp.finite w.tanh_w.sig.r :=
    (fpSigmoidFinite_eq_div_of_finite w.tanh_w.tx w.tanh_w.sig.he w.tanh_w.sig.hd).trans
      w.tanh_w.sig.hr
  have h_tanh_eq : fpTanhFinite w.u = Fp.finite w.tanh_w.r :=
    (fpTanhFinite_eq_sub_of_finite w.u w.tanh_w.hdbl1 h_sig_eq w.tanh_w.hdbl2).trans
      w.tanh_w.hsub
  unfold fpGeluFinite_with
  rw [w.h_sq]; simp only
  rw [w.h_cu]; simp only
  rw [w.h_ax_cu]; simp only
  rw [w.h_inner]; simp only
  rw [w.h_u]; simp only
  rw [h_tanh_eq]; simp only
  rw [w.h_opt]; simp only
  rw [w.h_hx]; simp only
  exact w.h_r

end Flean
