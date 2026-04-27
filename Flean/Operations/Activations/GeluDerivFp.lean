import Flean.Operations.Activations.Gelu
import Flean.Operations.Activations.GeluFp
import Flean.Operations.Activations.TanhDerivFp

/-!
# Floating-Point GeLU Derivative (tanh approximation)

Following Wick's tanh-approx form, the derivative is:

```
gelu'(x) = half · (1 + tanh(u)) + half · x · (1 − tanh²(u)) · u'
        where u  = c · (x + α · x³)
              u' = c · (1 + 3·α·x²)
```

i.e. one "1 + tanh(u)" term reused from the forward pass, plus an
"x · sech²(u) · u'" correction. We compute it as:

```
gelu_deriv(x) = half_x_plus + half_x · sech_u_sq · u'
```

where `half_x_plus = half · (1 + tanh(u))`, `sech_u_sq = 1 − tanh²(u)`
(reusing `fpTanhDerivFinite`'s structure on the *same* inner tanh value).

## Pipeline (composed on top of the forward gelu witness)

```
1-7. Reuse forward gelu's intermediates: x², x³, αx³, inner, u, t, opt
8.   sq = t · t                            (squared tanh)
9.   sech_sq = 1 − sq                      (sech²(u) = 1 − tanh²(u))
10.  half_opt = half · opt                 (= half · (1 + tanh(u)))
11.  three_α = fpAdd α (fpAdd α α)         (= 3α; user supplies as constant)
12.  three_α_x_sq = three_α · x²
13.  one_plus_3αx² = 1 + three_α_x²
14.  up = c · one_plus_3αx²                (= u'(x))
15.  hx = half · x   (already in gelu witness as `hx`)
16.  hxd = hx · sech_sq                   (= half · x · sech²)
17.  hxdu = hxd · up                       (= half · x · sech² · u')
18.  result = half_opt + hxdu              (final derivative)
```

We parametrize the "3α" constant `three_α : FiniteFp` separately rather
than compute `3·α` from `α` (which would require another FP op). The
user supplies a FiniteFp ≈ 3·α with their preferred rounding.

## Status

This file ships the FP function and witness type. The closeness lemma
against `geluTanhApprox_deriv` requires a substantial composition proof
(this pipeline plus the underlying gelu forward closeness plus the
tanh-deriv closeness for the reused `1 − tanh²` factor). Deferred to
a follow-up; the runnable FP function is sufficient for Wisp's
per-element backward bridge prototype.
-/

set_option autoImplicit false

namespace Flean

variable [FloatFormat] [RModeExec] [ExpApprox]

/-- FP gelu derivative kernel (tanh-approx form), parametrized over
FP approximations of `0.5`, `α`, `3α`, and `c`. -/
noncomputable def fpGeluDerivFinite_with
    (half α three_α c : FiniteFp) (x : FiniteFp) : Fp :=
  -- Steps 1–9: same as forward pipeline up through computing `t = tanh(u)`
  -- and `opt = 1 + t`, plus `hx = half · x`.
  match fpMulFinite x x with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite x_sq =>
  match fpMulFinite x_sq x with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite x_cu =>
  match fpMulFinite α x_cu with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite ax_cu =>
  match fpAddFinite x ax_cu with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite inner =>
  match fpMulFinite c inner with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite u =>
  match fpTanhFinite u with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite t =>
  match fpAddFinite (1 : FiniteFp) t with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite opt =>
  match fpMulFinite half x with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite hx =>
  -- Steps 10–11: sq = t·t, sech_sq = 1 − sq.
  match fpMulFinite t t with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite sq =>
  match fpSubFinite (1 : FiniteFp) sq with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite sech_sq =>
  -- Step 12: half_opt = half · opt.
  match fpMulFinite half opt with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite half_opt =>
  -- Steps 13–14: 3α·x² and 1 + 3α·x².
  match fpMulFinite three_α x_sq with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite three_a_xsq =>
  match fpAddFinite (1 : FiniteFp) three_a_xsq with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite one_plus_3axsq =>
  -- Step 15: up = c · (1 + 3α·x²).
  match fpMulFinite c one_plus_3axsq with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite up =>
  -- Steps 16–17: hxd = hx · sech_sq, hxdu = hxd · up.
  match fpMulFinite hx sech_sq with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite hxd =>
  match fpMulFinite hxd up with
  | .NaN => .NaN | .infinite s => .infinite s
  | .finite hxdu =>
  -- Step 18: result = half_opt + hxdu.
  fpAddFinite half_opt hxdu

/-- IEEE-style FP gelu derivative wrapper.

Special cases:
* `NaN ↦ NaN`
* `+∞ ↦ Fp.finite 1` (gelu'(+∞) → 1 since gelu(x) ≈ x for x ≫ 0)
* `−∞ ↦ Fp.finite 0` (gelu'(−∞) → 0 since gelu(x) → 0 for x ≪ 0) -/
noncomputable def fpGeluDeriv_with
    (half α three_α c : FiniteFp) (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .finite 1
  | .infinite true => .finite 0
  | .finite a => fpGeluDerivFinite_with half α three_α c a

@[simp] theorem fpGeluDeriv_with_finite (half α three_α c : FiniteFp) (a : FiniteFp) :
    fpGeluDeriv_with half α three_α c (Fp.finite a) =
      fpGeluDerivFinite_with half α three_α c a := rfl

@[simp] theorem fpGeluDeriv_with_nan (half α three_α c : FiniteFp) :
    fpGeluDeriv_with half α three_α c Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpGeluDeriv_with_pos_inf (half α three_α c : FiniteFp) :
    fpGeluDeriv_with half α three_α c (Fp.infinite false) = Fp.finite 1 := rfl

@[simp] theorem fpGeluDeriv_with_neg_inf (half α three_α c : FiniteFp) :
    fpGeluDeriv_with half α three_α c (Fp.infinite true) = Fp.finite 0 := rfl

end Flean
