import Flean.Operations.Activations.Gelu
import Flean.Operations.Activations.GeluFp
import Flean.Operations.Activations.GeluFpClose
import Flean.Operations.Activations.TanhDerivFp
import Flean.Operations.KahanSum

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

* FP kernel + IEEE wrapper + simp lemmas.
* `GeluDerivFpWitness` per-input bundle wrapping the forward
  `GeluFpWitness` plus 9 new step witnesses (10–18).
* `fpGeluDerivFinite_with_eq_of_witness` — finite-path reduction.
* Closeness lemma against `geluTanhApprox_deriv` is the natural
  follow-up; deferred pending a refactor of `fpGeluFinite_close`'s
  intermediate-bound proof state into reusable lemmas (current state:
  intermediates `ε_t`, `ε_opt`, `ε_hx`, `M_*` are local to the proof).
  The runnable FP function + witness machinery is sufficient for
  Wisp's per-element backward bridge prototype to consume the kernel.
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

/-! ## Per-input witness bundle -/

/-- Per-input finite-path witness for the FP gelu derivative pipeline.
Bundles the underlying forward `GeluFpWitness` (steps 1–9) with the 9
new step witnesses (10–18). -/
structure GeluDerivFpWitness (half α three_α c : FiniteFp) (x : FiniteFp) where
  /-- Forward gelu witness: provides `x_sq, x_cu, ax_cu, inner, u, tanh_w, opt, hx`. -/
  fwd : GeluFpWitness half α c x
  /-- Step 10: `sq = t · t`. -/
  sq : FiniteFp
  /-- Step 11: `sech_sq = 1 − sq`. -/
  sech_sq : FiniteFp
  /-- Step 12: `half_opt = half · opt`. -/
  half_opt : FiniteFp
  /-- Step 13: `three_a_xsq = three_α · x²`. -/
  three_a_xsq : FiniteFp
  /-- Step 14: `one_plus_3axsq = 1 + three_a_xsq`. -/
  one_plus_3axsq : FiniteFp
  /-- Step 15: `up = c · one_plus_3axsq`. -/
  up : FiniteFp
  /-- Step 16: `hxd = hx · sech_sq`. -/
  hxd : FiniteFp
  /-- Step 17: `hxdu = hxd · up`. -/
  hxdu : FiniteFp
  /-- Step 18: `r = half_opt + hxdu`. -/
  r : FiniteFp
  /-- Step witnesses. -/
  hsq : fpMulFinite fwd.tanh_w.r fwd.tanh_w.r = Fp.finite sq
  hsech_sq : fpSubFinite (1 : FiniteFp) sq = Fp.finite sech_sq
  hhalf_opt : fpMulFinite half fwd.opt = Fp.finite half_opt
  hthree_a_xsq : fpMulFinite three_α fwd.x_sq = Fp.finite three_a_xsq
  hone_plus : fpAddFinite (1 : FiniteFp) three_a_xsq = Fp.finite one_plus_3axsq
  hup : fpMulFinite c one_plus_3axsq = Fp.finite up
  hhxd : fpMulFinite fwd.hx sech_sq = Fp.finite hxd
  hhxdu : fpMulFinite hxd up = Fp.finite hxdu
  hr : fpAddFinite half_opt hxdu = Fp.finite r

/-- Finite-path reduction: when all 18 steps land in finite range, the
result is `r` (the final FP add). -/
theorem fpGeluDerivFinite_with_eq_of_witness
    (half α three_α c : FiniteFp) (x : FiniteFp)
    (w : GeluDerivFpWitness half α three_α c x) :
    fpGeluDerivFinite_with half α three_α c x = Fp.finite w.r := by
  -- Derive the tanh result equality from the inner sigmoid witnesses.
  have h_sig_eq :
      fpSigmoidFinite w.fwd.tanh_w.tx = Fp.finite w.fwd.tanh_w.sig.r :=
    (fpSigmoidFinite_eq_div_of_finite w.fwd.tanh_w.tx w.fwd.tanh_w.sig.he
      w.fwd.tanh_w.sig.hd).trans w.fwd.tanh_w.sig.hr
  have h_tanh_eq : fpTanhFinite w.fwd.u = Fp.finite w.fwd.tanh_w.r :=
    (fpTanhFinite_eq_sub_of_finite w.fwd.u w.fwd.tanh_w.hdbl1 h_sig_eq
      w.fwd.tanh_w.hdbl2).trans w.fwd.tanh_w.hsub
  unfold fpGeluDerivFinite_with
  rw [w.fwd.h_sq]; simp only
  rw [w.fwd.h_cu]; simp only
  rw [w.fwd.h_ax_cu]; simp only
  rw [w.fwd.h_inner]; simp only
  rw [w.fwd.h_u]; simp only
  rw [h_tanh_eq]; simp only
  rw [w.fwd.h_opt]; simp only
  rw [w.fwd.h_hx]; simp only
  rw [w.hsq]; simp only
  rw [w.hsech_sq]; simp only
  rw [w.hhalf_opt]; simp only
  rw [w.hthree_a_xsq]; simp only
  rw [w.hone_plus]; simp only
  rw [w.hup]; simp only
  rw [w.hhxd]; simp only
  rw [w.hhxdu]; simp only
  exact w.hr

end Flean
