import Flean.Operations.JetHorner
import Flean.Operations.KahanSum
import Flean.Operations.Horner
import Flean.Operations.Div

/-!
# Newton's Method via Jet Horner Evaluation

Floating-point Newton's method for polynomial root-finding:
```
x_{n+1} = fl(x_n - fl(p̂(x_n) / p̂'(x_n)))
```
where `p̂` and `p̂'` are computed simultaneously via jet Horner.

## Structure

1. **Jet Horner FP trace**: `JetHornerStep`, `JetHornerTrace` — 4 FP operations per
   coefficient (mul+add for value, mul+add for derivative). Proves the exact decomposition:
   `(v̂, d̂) + error_propagation = (p(x), p'(x))`.

2. **Per-step error bounds**: Each step has error `≤ (2η + η²)(|accumulator|·|x| + |offset|)`,
   proved separately for value and derivative channels.

3. **Exact Newton convergence**: Abstract quadratic convergence with Taylor remainder +
   derivative Lipschitz hypotheses. Perturbed Newton ball invariance by induction.

4. **FP Newton step**: `NewtonStep` chains jet Horner → division → subtraction.
   Per-operation perturbation bounds decompose the total error.

## Key Infrastructure Used

- `JetHorner.jetHornerExact`, `jetHornerL`, `jetHornerExact_affine` — exact 2D recurrence
- `AffineFold.affineFold_affine` — affine splitting for error propagation
- `KahanSum.fpMul_error_or_zero`, `KahanSum.fpAdd_error_or_zero`, `KahanSum.fpDiv_error_or_zero` — per-operation error bounds
-/

namespace NewtonHorner

open JetHorner AffineFold Horner

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Jet Horner FP Step

Each step computes:
- `xv = fl(x · v)`, `v' = fl(xv + coeff)` — value update
- `xd = fl(x · d)`, `d' = fl(xd + v)` — derivative update

Four FP operations total (or two FMAs in the FMA variant). -/

/-- One step of floating-point jet Horner evaluation. -/
structure JetHornerStep [RModeExec] (v d x coeff : FiniteFp) where
  xv : FiniteFp
  hxv : x * v = Fp.finite xv
  v' : FiniteFp
  hv' : xv + coeff = Fp.finite v'
  xd : FiniteFp
  hxd : x * d = Fp.finite xd
  d' : FiniteFp
  hd' : xd + v = Fp.finite d'

/-- Normal range conditions for a jet Horner step. -/
structure JetHornerStepNormalRange [RModeExec] (v d x coeff : FiniteFp)
    (step : JetHornerStep v d x coeff) where
  mul_v_normal : isNormalRange ((x.toVal : R) * v.toVal) ∨ (x.toVal : R) * v.toVal = 0
  add_v_normal : isNormalRange ((step.xv.toVal : R) + coeff.toVal) ∨
                 (step.xv.toVal : R) + coeff.toVal = 0
  mul_d_normal : isNormalRange ((x.toVal : R) * d.toVal) ∨ (x.toVal : R) * d.toVal = 0
  add_d_normal : isNormalRange ((step.xd.toVal : R) + v.toVal) ∨
                 (step.xd.toVal : R) + v.toVal = 0

/-- Trace of a floating-point jet Horner evaluation. -/
inductive JetHornerTrace [RModeExec] (x : FiniteFp) :
    List FiniteFp → FiniteFp → FiniteFp → FiniteFp → FiniteFp → Type where
  | nil (v d : FiniteFp) : JetHornerTrace x [] v d v d
  | cons {v d coeff : FiniteFp} {coeffs : List FiniteFp} {v_final d_final : FiniteFp}
      (step : JetHornerStep v d x coeff)
      (rest : JetHornerTrace x coeffs step.v' step.d' v_final d_final) :
      JetHornerTrace x (coeff :: coeffs) v d v_final d_final

/-- All steps are in normal range. -/
def JetHornerTrace.AllNormalRange [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {v d v_f d_f : FiniteFp} →
    JetHornerTrace x coeffs v d v_f d_f → Prop
  | _, _, _, _, _, .nil _ _ => True
  | _, _, _, _, _, .cons (v := v) (d := d) (coeff := coeff) step rest =>
      JetHornerStepNormalRange (R := R) v d x coeff step ∧ rest.AllNormalRange

/-! ## Per-Step Errors

The error at each step is the pair `(e_v, e_d)` where:
- `e_v = (x·v + coeff) - v'` (value channel rounding error)
- `e_d = (x·d + v) - d'` (derivative channel rounding error)

These match the `jetHornerOffsets` pattern: offsets `(coeff, 0)` become
`(coeff - e_v, 0 - e_d)` = `(coeff, 0) - (e_v, e_d)`. -/

/-- Per-step errors of a jet Horner FP trace. -/
def jetStepErrors [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {v d v_f d_f : FiniteFp} →
    JetHornerTrace x coeffs v d v_f d_f → List (R × R)
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons (v := v) (d := d) (coeff := coeff) step rest =>
      let e_v := (x.toVal : R) * v.toVal + coeff.toVal - step.v'.toVal
      let e_d := (x.toVal : R) * d.toVal + v.toVal - step.d'.toVal
      (e_v, e_d) :: jetStepErrors rest

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
theorem jetStepErrors_length [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {v d v_f d_f : FiniteFp}
    (trace : JetHornerTrace x coeffs v d v_f d_f) :
    (jetStepErrors (R := R) trace).length = coeffs.length := by
  induction trace with
  | nil => simp [jetStepErrors]
  | cons step rest ih => simp [jetStepErrors, ih]

/-! ## Exact Decomposition

The FP trace satisfies the exact decomposition from AffineFold:
`(v_final, d_final) + affineFold(jetHornerL x, errors, (0,0)) = jetHornerExact(coeffs, v, d, x)`

This is the 2D analog of `comp_horner_exact_decomposition`. -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The FP jet Horner trace computes the exact result minus error propagation. -/
theorem jetHorner_fp_exact_decomposition [RModeExec]
    {x : FiniteFp} {coeffs : List FiniteFp} {v d v_f d_f : FiniteFp}
    (trace : JetHornerTrace x coeffs v d v_f d_f) :
    ((v_f.toVal : R), (d_f.toVal : R)) +
      affineFold (jetHornerL (x.toVal : R)) (jetStepErrors (R := R) trace) ((0 : R), (0 : R)) =
      jetHornerExact (coeffs.map (fun c => c.toVal (R := R))) (v.toVal) (d.toVal) (x.toVal) := by
  induction trace with
  | nil =>
    simp [jetStepErrors, affineFold, jetHornerExact]
  | @cons v_cur d_cur coeff coeffs _ _ step rest ih =>
    set x_v := (x.toVal : R)
    set ev := x_v * (v_cur.toVal : R) + (coeff.toVal : R) - (step.v'.toVal : R)
    set ed := x_v * (d_cur.toVal : R) + (v_cur.toVal : R) - (step.d'.toVal : R)
    have hL_add := jetHornerL_additive (R := R) x_v
    -- v' + ev = x*v + c, d' + ed = x*d + v
    have hve : (step.v'.toVal : R) + ev =
        x_v * (v_cur.toVal : R) + (coeff.toVal : R) := by simp [ev]
    have hde : (step.d'.toVal : R) + ed =
        x_v * (d_cur.toVal : R) + (v_cur.toVal : R) := by simp [ed]
    -- Use jetHornerExact_affine to rewrite the RHS
    have hjet := jetHornerExact_affine
      (coeffs.map (fun c => c.toVal (R := R)))
      (step.v'.toVal : R) (step.d'.toVal : R) ev ed x_v
    rw [hve, hde] at hjet
    -- hjet: jetHornerExact(map, x*v+c, x*d+v, x) = (...fst + prop.fst, ...snd + prop.snd)
    -- Rewrite RHS of goal: first unfold jetHornerExact one step
    simp only [jetStepErrors, List.map_cons, jetHornerExact]
    -- Now RHS is jetHornerExact(map, x*v+c, x*d+v, x) which we can rewrite via hjet
    rw [hjet]
    -- Now both sides should involve affineFold + affineProp
    -- LHS: (v_f,d_f) + affineFold L ((ev,ed)::rest) (0,0)
    --     = (v_f,d_f) + affineFold L rest (L(0,0)+(ev,ed))
    -- Unfold the affineFold cons step
    simp only [affineFold, jetHornerL, mul_zero, zero_add, Prod.mk_add_mk]
    -- Decompose fold(rest, (ev,ed)) = fold(rest, (0,0)) + prop(n, (ev,ed))
    have hfold := affineFold_affine (jetHornerL x_v) hL_add
      (jetStepErrors (R := R) rest) ((0 : R), (0 : R)) (ev, ed)
    simp only [Prod.mk_add_mk, zero_add] at hfold
    rw [hfold, ← add_assoc, ih]
    have herr_len := jetStepErrors_length (R := R) rest
    ext <;> simp [Prod.add_def, herr_len]

/-! ## Per-Step Error Bounds

Each of the 4 FP operations has error ≤ η times the exact result.
A mul-then-add pair `z = fl(fl(a·b) + c)` has total error
`|a·b + c - z| ≤ (2η + η²)(|b|·|a| + |c|)`. -/

/-- **Mul-then-add compound error**: `|a·b + c - fl(fl(a·b) + c)| ≤ (2η+η²)(|b|·|a| + |c|)`.

    Shared helper for both value and derivative channels of jet Horner. -/
private theorem mul_add_compound_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {a b c : FiniteFp} {ab_fp result : FiniteFp}
    (hmul_fp : a * b = Fp.finite ab_fp)
    (hadd_fp : ab_fp + c = Fp.finite result)
    (hmul_nr : isNormalRange ((a.toVal : R) * b.toVal) ∨ (a.toVal : R) * b.toVal = 0)
    (hadd_nr : isNormalRange ((ab_fp.toVal : R) + c.toVal) ∨
               (ab_fp.toVal : R) + c.toVal = 0) :
    |(a.toVal : R) * b.toVal + c.toVal - result.toVal| ≤
      (2 * η + η ^ 2) * (|(b.toVal : R)| * |(a.toVal : R)| + |(c.toVal : R)|) := by
  set a_v := (a.toVal : R); set b_v := (b.toVal : R); set c_v := (c.toVal : R)
  set ab_v := (ab_fp.toVal : R); set z_v := (result.toVal : R)
  have hη : (0 : R) ≤ η := by positivity
  have hmul := KahanSum.fpMul_error_or_zero (R := R) a b ab_fp hmul_fp hmul_nr
  have hadd := KahanSum.fpAdd_error_or_zero (R := R) ab_fp c result hadd_fp hadd_nr
  -- |a*b - ab_fp| ≤ η|a*b|, |ab_fp + c - result| ≤ η|ab_fp + c|
  have hmul' : |a_v * b_v - ab_v| ≤ η * |a_v * b_v| := by
    rw [show a_v * b_v - ab_v = -(ab_v - a_v * b_v) from by ring, abs_neg]; exact hmul
  have hadd' : |ab_v + c_v - z_v| ≤ η * |ab_v + c_v| := by
    rw [show ab_v + c_v - z_v = -(z_v - (ab_v + c_v)) from by ring, abs_neg]; exact hadd
  -- Triangle: |a*b + c - z| ≤ |a*b - ab| + |ab + c - z|
  have htri : |a_v * b_v + c_v - z_v| ≤ |a_v * b_v - ab_v| + |ab_v + c_v - z_v| := by
    rw [show a_v * b_v + c_v - z_v = (a_v * b_v - ab_v) + (ab_v + c_v - z_v) from by ring]
    exact abs_add_le _ _
  -- |ab + c| ≤ |a*b + c| + η|a*b|
  have hintermed : |ab_v + c_v| ≤ |a_v * b_v + c_v| + η * |a_v * b_v| := by
    rw [show ab_v + c_v = (a_v * b_v + c_v) + (ab_v - a_v * b_v) from by ring]
    linarith [abs_add_le (a_v * b_v + c_v) (ab_v - a_v * b_v)]
  set A := |b_v| * |a_v| + |c_v|
  have hprod_le : |a_v * b_v| ≤ A := by
    calc |a_v * b_v| = |b_v| * |a_v| := by rw [abs_mul, mul_comm]
      _ ≤ A := le_add_of_nonneg_right (abs_nonneg _)
  have hsum_le : |a_v * b_v + c_v| ≤ A := by
    calc |a_v * b_v + c_v| ≤ |a_v * b_v| + |c_v| := abs_add_le _ _
      _ = |b_v| * |a_v| + |c_v| := by rw [abs_mul, mul_comm]
  calc |a_v * b_v + c_v - z_v|
      ≤ η * |a_v * b_v| + η * |ab_v + c_v| := by linarith [htri, hmul', hadd']
    _ ≤ η * |a_v * b_v| + η * (|a_v * b_v + c_v| + η * |a_v * b_v|) := by
        linarith [mul_le_mul_of_nonneg_left hintermed hη]
    _ = η * (1 + η) * |a_v * b_v| + η * |a_v * b_v + c_v| := by ring
    _ ≤ η * (1 + η) * A + η * A := by
        nlinarith [mul_le_mul_of_nonneg_left hprod_le (mul_nonneg hη (by linarith : (0:R) ≤ 1+η)),
                   mul_le_mul_of_nonneg_left hsum_le hη]
    _ = (2 * η + η ^ 2) * A := by ring

/-- Value channel per-step error: `|x·v + c - v'| ≤ (2η+η²)(|v|·|x| + |c|)`. -/
theorem jetHorner_step_value_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {v d x coeff : FiniteFp} (step : JetHornerStep v d x coeff)
    (hnr : JetHornerStepNormalRange (R := R) v d x coeff step) :
    |(x.toVal : R) * v.toVal + coeff.toVal - step.v'.toVal| ≤
      (2 * η + η ^ 2) * (|(v.toVal : R)| * |(x.toVal : R)| + |(coeff.toVal : R)|) :=
  mul_add_compound_error step.hxv step.hv' hnr.mul_v_normal hnr.add_v_normal

/-- Derivative channel per-step error: `|x·d + v - d'| ≤ (2η+η²)(|d|·|x| + |v|)`. -/
theorem jetHorner_step_deriv_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {v d x coeff : FiniteFp} (step : JetHornerStep v d x coeff)
    (hnr : JetHornerStepNormalRange (R := R) v d x coeff step) :
    |(x.toVal : R) * d.toVal + v.toVal - step.d'.toVal| ≤
      (2 * η + η ^ 2) * (|(d.toVal : R)| * |(x.toVal : R)| + |(v.toVal : R)|) :=
  mul_add_compound_error step.hxd step.hd' hnr.mul_d_normal hnr.add_d_normal

/-! ## Exact Newton Quadratic Convergence

Pure real analysis: if `p(r) = 0` and `p'(x) ≠ 0` with Taylor-type bounds,
then `|x - p(x)/p'(x) - r| ≤ (L + M) · |x - r|² / |p'(x)|`.

The hypotheses are abstract (Taylor remainder bound + derivative Lipschitz),
not derived from `hornerPoly`, making the theorem reusable for any function. -/

omit [FloatFormat] [FloorRing R] in
/-- **Exact Newton quadratic convergence.**

    If `p(r) = 0` and we have:
    - `|p(x) - p'(r)·(x-r)| ≤ M·|x-r|²` (Taylor remainder)
    - `|p'(x) - p'(r)| ≤ L·|x-r|` (derivative Lipschitz)

    then `|x - p(x)/p'(x) - r| ≤ (L + M)·|x-r|² / |p'(x)|`. -/
theorem exact_newton_quadratic
    {p p' : R → R} {r x : R}
    (hp'x_ne : p' x ≠ 0)
    {M : R}
    (hTaylor : |p x - p' r * (x - r)| ≤ M * |x - r| ^ 2)
    {L : R}
    (hLip : |p' x - p' r| ≤ L * |x - r|) :
    |x - p x / p' x - r| ≤ (L + M) * |x - r| ^ 2 / |p' x| := by
  -- Rewrite: x - p(x)/p'(x) - r = ((x-r)·p'(x) - p(x)) / p'(x)
  have hp'x_abs_pos : (0 : R) < |p' x| := abs_pos.mpr hp'x_ne
  rw [show x - p x / p' x - r = ((x - r) * p' x - p x) / p' x from by field_simp; ring]
  rw [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  -- Bound |(x-r)·p'(x) - p(x)|
  -- = |(x-r)·(p'(x) - p'(r)) + (p'(r)·(x-r) - p(x))|
  -- ≤ |x-r|·|p'(x)-p'(r)| + |p(x) - p'(r)·(x-r)|
  -- ≤ |x-r|·L·|x-r| + M·|x-r|²
  -- = (L+M)·|x-r|²
  have heq : (x - r) * p' x - p x =
      (x - r) * (p' x - p' r) + (p' r * (x - r) - p x) := by ring
  rw [heq]
  calc |(x - r) * (p' x - p' r) + (p' r * (x - r) - p x)|
      ≤ |(x - r) * (p' x - p' r)| + |p' r * (x - r) - p x| := abs_add_le _ _
    _ = |x - r| * |p' x - p' r| + |p x - p' r * (x - r)| := by
        rw [abs_mul, show p' r * (x - r) - p x = -(p x - p' r * (x - r)) from by ring, abs_neg]
    _ ≤ |x - r| * (L * |x - r|) + M * |x - r| ^ 2 := by
        linarith [mul_le_mul_of_nonneg_left hLip (abs_nonneg (x - r))]
    _ = (L + M) * |x - r| ^ 2 := by ring

/-! ## Perturbed Newton Convergence

If exact Newton has quadratic convergence `|N(x) - r| ≤ C·|x-r|²`
and each FP step has perturbation `|x' - N(x)| ≤ δ`, then:
1. One step: `|x' - r| ≤ C·|x-r|² + δ`
2. Ball invariance: if `C·ρ² + δ ≤ ρ` then `|x-r| ≤ ρ → |x'-r| ≤ ρ` -/

omit [FloatFormat] [FloorRing R] in
/-- **One-step contraction for perturbed Newton.**
    Quadratic convergence plus bounded perturbation. -/
theorem perturbed_newton_one_step
    {N : R → R} {r x x' : R} {C δ : R}
    (hquad : |N x - r| ≤ C * |x - r| ^ 2)
    (hpert : |x' - N x| ≤ δ) :
    |x' - r| ≤ C * |x - r| ^ 2 + δ := by
  calc |x' - r| = |(x' - N x) + (N x - r)| := by ring_nf
    _ ≤ |x' - N x| + |N x - r| := abs_add_le _ _
    _ ≤ δ + C * |x - r| ^ 2 := add_le_add hpert hquad
    _ = C * |x - r| ^ 2 + δ := by ring

omit [FloatFormat] [FloorRing R] in
/-- **Perturbed Newton stays in a ball.**
    If `|x - r| ≤ ρ` and `C·ρ² + δ ≤ ρ`, then `|x' - r| ≤ ρ`. -/
theorem perturbed_newton_ball
    {N : R → R} {r x x' : R} {C δ ρ : R}
    (hC : 0 ≤ C) (_hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hquad : |N x - r| ≤ C * |x - r| ^ 2)
    (hpert : |x' - N x| ≤ δ)
    (hin : |x - r| ≤ ρ)
    (hball : C * ρ ^ 2 + δ ≤ ρ) :
    |x' - r| ≤ ρ := by
  calc |x' - r| ≤ C * |x - r| ^ 2 + δ :=
        perturbed_newton_one_step hquad hpert
    _ ≤ C * ρ ^ 2 + δ := by
        have h1 : |x - r| * |x - r| ≤ ρ * ρ := mul_le_mul hin hin (abs_nonneg _) hρ
        nlinarith [sq_abs (x - r), sq_abs ρ]
    _ ≤ ρ := hball

omit [FloatFormat] [FloorRing R] in
/-- **Multi-step ball invariance for perturbed Newton.**
    All iterates of a perturbed Newton sequence stay in the ball of radius `ρ`. -/
theorem perturbed_newton_n_steps
    {r : R} {C δ ρ : R}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hball : C * ρ ^ 2 + δ ≤ ρ)
    {xs : ℕ → R} (hx0 : |xs 0 - r| ≤ ρ)
    {N : R → R}
    (hquad : ∀ x, |x - r| ≤ ρ → |N x - r| ≤ C * |x - r| ^ 2)
    (hsteps : ∀ n, |xs (n + 1) - N (xs n)| ≤ δ) :
    ∀ n, |xs n - r| ≤ ρ := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
    exact perturbed_newton_ball hC hδ hρ (hquad _ ih) (hsteps n) ih hball

/-! ## Newton Step Definition

The FP Newton step chains jet Horner → division → subtraction:
`x' = fl(x - fl(p̂(x) / p̂'(x)))` -/

/-- One step of floating-point Newton's method.
    Evaluates `(p̂, p̂')` via jet Horner, divides, subtracts. -/
structure NewtonStep [RModeExec]
    (init : FiniteFp) (coeffs : List FiniteFp) (x_cur : FiniteFp) where
  v_final : FiniteFp
  d_final : FiniteFp
  trace : JetHornerTrace x_cur coeffs init (0 : FiniteFp) v_final d_final
  hd_nonzero : d_final.m ≠ 0
  quot : FiniteFp
  hquot : v_final / d_final = Fp.finite quot
  x_next : FiniteFp
  hx_next : x_cur - quot = Fp.finite x_next

/-- Normal range conditions for a Newton step. -/
structure NewtonStepNormalRange [RModeExec]
    (init : FiniteFp) (coeffs : List FiniteFp) (x_cur : FiniteFp)
    (step : NewtonStep init coeffs x_cur) where
  horner_normal : step.trace.AllNormalRange (R := R)
  div_normal : isNormalRange ((step.v_final.toVal : R) / step.d_final.toVal) ∨
               (step.v_final.toVal : R) / step.d_final.toVal = 0
  sub_normal : isNormalRange ((x_cur.toVal : R) - step.quot.toVal) ∨
               (x_cur.toVal : R) - step.quot.toVal = 0

/-! ## Newton Step Perturbation Bound

The FP Newton step `x' = fl(x - fl(v̂/d̂))` differs from the exact Newton
step `x - p(x)/p'(x)` by a bounded perturbation. We decompose:

  `|x' - (x - p/p')| ≤ |x' - (x - q̂)| + |q̂ - v̂/d̂| + |v̂/d̂ - p/p'|`

where the three terms are subtraction error, division error, and evaluation error. -/

/-- **Newton step perturbation bound** (three-term decomposition).

    The FP Newton step `x'` differs from exact Newton `x - p(x)/p'(x)` by:
    - Subtraction rounding: `|x' - (x - q̂)| ≤ η · |x - q̂|`
    - Division rounding: `|q̂ - v̂/d̂| ≤ η · |v̂/d̂|`

    Combined with jet Horner error bounds on `|v̂/d̂ - p(x)/p'(x)|`,
    these give the total perturbation via triangle inequality. -/
theorem newton_step_sub_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {init : FiniteFp} {coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : NewtonStep init coeffs x_cur)
    (hnr_sub : isNormalRange ((x_cur.toVal : R) - step.quot.toVal) ∨
               (x_cur.toVal : R) - step.quot.toVal = 0) :
    |(step.x_next.toVal : R) - ((x_cur.toVal : R) - step.quot.toVal)| ≤
      η * |(x_cur.toVal : R) - step.quot.toVal| :=
  KahanSum.fpSub_error_or_zero (R := R) x_cur step.quot step.x_next step.hx_next hnr_sub

theorem newton_step_div_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeSticky R]
    {init : FiniteFp} {coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : NewtonStep init coeffs x_cur)
    (hnr_div : isNormalRange ((step.v_final.toVal : R) / step.d_final.toVal) ∨
               (step.v_final.toVal : R) / step.d_final.toVal = 0) :
    |(step.quot.toVal : R) - (step.v_final.toVal : R) / step.d_final.toVal| ≤
      η * |(step.v_final.toVal : R) / step.d_final.toVal| := by
  have hdiv := KahanSum.fpDiv_error_or_zero (R := R) step.v_final step.d_final step.quot
    step.hd_nonzero step.hquot hnr_div
  -- hdiv: |quot - v/d| ≤ η|v/d|, which is the same as our goal (same sign)
  exact hdiv

/-- **Combined Newton step perturbation.**
    Triangle inequality: `|x' - (x - v̂/d̂)| ≤ (1+η)·η·|v̂/d̂| + η·|x - v̂/d̂|`. -/
theorem newton_step_perturbation
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeSticky R]
    {init : FiniteFp} {coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : NewtonStep init coeffs x_cur)
    (hnr : NewtonStepNormalRange (R := R) init coeffs x_cur step) :
    |(step.x_next.toVal : R) - ((x_cur.toVal : R) -
      (step.v_final.toVal : R) / step.d_final.toVal)| ≤
      η * |(x_cur.toVal : R) - step.quot.toVal| +
      |(step.quot.toVal : R) - (step.v_final.toVal : R) / step.d_final.toVal| := by
  set x' := (step.x_next.toVal : R)
  set xv := (x_cur.toVal : R)
  set vd := (step.v_final.toVal : R) / step.d_final.toVal
  set q := (step.quot.toVal : R)
  -- x' - (xv - vd) = (x' - (xv - q)) + -(q - vd)
  have heq : x' - (xv - vd) = (x' - (xv - q)) - (q - vd) := by ring
  rw [heq]
  have hsub := newton_step_sub_error (R := R) step hnr.sub_normal
  calc |(x' - (xv - q)) - (q - vd)|
      ≤ |x' - (xv - q)| + |q - vd| := by
        rw [show (x' - (xv - q)) - (q - vd) = (x' - (xv - q)) + (-(q - vd)) from by ring]
        calc |(x' - (xv - q)) + (-(q - vd))|
            ≤ |x' - (xv - q)| + |-(q - vd)| := abs_add_le _ _
          _ = |x' - (xv - q)| + |q - vd| := by rw [abs_neg]
    _ ≤ η * |xv - q| + |q - vd| := by linarith

/-! ## C. Connection to `hornerPoly`

The value component of `jetHornerExact` equals `hornerPoly` (up to the
commutativity `x * v = v * x` in the accumulator update). -/

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Jet Horner value = standard Horner polynomial. -/
theorem jetHornerExact_fst_eq_hornerPoly (cs : List R) (init x : R) :
    (jetHornerExact cs init 0 x).1 = hornerPoly cs init x := by
  induction cs generalizing init with
  | nil => simp [jetHornerExact, hornerPoly]
  | cons c cs ih =>
    simp only [jetHornerExact, hornerPoly, mul_zero, zero_add]
    rw [jetHorner_value_indep_of_deriv]
    rw [show x * init + c = init * x + c from by ring]
    exact ih _

/-! ## A. Jet Horner Value Error Bound

The value component of jet Horner has 2 rounding errors per step (mul + add),
identical to standard Horner. The accumulated error is `((1+η)^{2n} - 1) · p̃(|x|)`
where `p̃` is the absolute polynomial `hornerPoly(|coeffs|, |init|, |x|)`.

Note: the derivative error bound is more complex due to cross-coupling from the
value channel (the `+v` term in `d' = x·d + v`). The value bound alone suffices
for Newton's method since `p'(x)` appears only in the denominator. -/

set_option maxHeartbeats 800000 in
/-- **Jet Horner value error bound** (`(1+η)^{2n}` form).

    The value component of the FP jet Horner trace satisfies the same error bound
    as standard 2-op Horner:
    `|v̂ - hornerPoly(coeffs, init, x)| ≤ ((1+η)^{2n} - 1) · hornerPoly(|coeffs|, |init|, |x|)` -/
theorem jetHorner_value_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init d_init : FiniteFp} {coeffs : List FiniteFp} {v_final d_final : FiniteFp}
    (trace : JetHornerTrace x coeffs init d_init v_final d_final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(v_final.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      ((1 + η) ^ (2 * coeffs.length) - 1) *
        hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |init.toVal (R := R)| |x.toVal (R := R)| := by
  induction trace with
  | nil =>
    simp only [List.map_nil, hornerPoly, List.length_nil, Nat.mul_zero, pow_zero, sub_self,
               zero_mul, abs_zero, le_refl]
  | @cons v_cur _ coeff coeffs v_f _ step rest ih =>
    simp only [JetHornerTrace.AllNormalRange] at hnr
    obtain ⟨hnr_step, hnr_rest⟩ := hnr
    have hstep := jetHorner_step_value_error (R := R) step hnr_step
    set n := coeffs.length with hn_def
    set x_v := (x.toVal : R)
    set v_v := (v_cur.toVal : R)
    set c_v := (coeff.toVal : R)
    set v'_v := (step.v'.toVal : R)
    set A := |v_v| * |x_v| + |c_v|
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    have h1η2 : (1 : R) ≤ (1 + η) ^ 2 := one_le_pow₀ h1η
    -- (2η+η²) = (1+η)²-1
    have hfactor : (2 : R) * η + η ^ 2 = (1 + η) ^ 2 - 1 := by ring
    -- Per-step error ≤ ((1+η)²-1) · A
    have hstep_A : |x_v * v_v + c_v - v'_v| ≤ ((1 + η) ^ 2 - 1) * A := by
      rw [← hfactor]; exact hstep
    -- |v'| ≤ (1+η)² · A
    have hv'_bound : |v'_v| ≤ (1 + η) ^ 2 * A := by
      have h1 := abs_sub_abs_le_abs_sub v'_v (x_v * v_v + c_v)
      have h2 : |x_v * v_v + c_v| ≤ A := by
        calc |x_v * v_v + c_v| ≤ |x_v * v_v| + |c_v| := abs_add_le _ _
          _ = |v_v| * |x_v| + |c_v| := by rw [abs_mul, mul_comm]
      have h3 : |v'_v - (x_v * v_v + c_v)| = |x_v * v_v + c_v - v'_v| := by
        rw [show v'_v - (x_v * v_v + c_v) = -(x_v * v_v + c_v - v'_v) from by ring, abs_neg]
      linarith
    -- IH
    have ih_bound := ih hnr_rest
    -- Abbreviations for absolute polynomials
    set PA := hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) A |x_v|
    set PA_v' := hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) |v'_v| |x_v|
    have hlen : (coeffs.map (fun c => |c.toVal (R := R)|)).length = n := by simp [hn_def]
    -- PA(|v'|) ≤ PA(A) + (|v'| - A) · |x|^n, and |v'| ≤ (1+η)²·A gives |v'|-A ≤ ((1+η)²-1)A
    have hPA_mono : PA_v' ≤ PA + ((1 + η) ^ 2 - 1) * A * |x_v| ^ n := by
      have hdecomp : |v'_v| = A + (|v'_v| - A) := by ring
      show hornerPoly _ |v'_v| |x_v| ≤ PA + ((1 + η) ^ 2 - 1) * A * |x_v| ^ n
      conv_lhs => rw [hdecomp]
      rw [hornerPoly_affine, hlen]
      have hle : |v'_v| - A ≤ ((1 + η) ^ 2 - 1) * A := by linarith
      linarith [mul_le_mul_of_nonneg_right hle (by positivity : (0 : R) ≤ |x_v| ^ n)]
    -- PA ≥ A · |x|^n
    have hPA_ge : A * |x_v| ^ n ≤ PA := by
      conv_lhs => rw [show A = 0 + A from (zero_add A).symm]
      rw [show PA = hornerPoly _ A _ from rfl, show A = 0 + A from (zero_add A).symm,
          hornerPoly_affine, hlen]
      linarith [hornerPoly_nonneg (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x_v|
        le_rfl (abs_nonneg _) (fun c hc => by
          simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; exact abs_nonneg _)]
    have hPA_nn : (0 : R) ≤ PA := le_trans (by positivity) hPA_ge
    have hA_nn : (0 : R) ≤ A := by positivity
    have hxpow_nn : (0 : R) ≤ |x_v| ^ n := by positivity
    -- Powers
    have hpow_2n : (1 : R) ≤ (1 + η) ^ (2 * n) := one_le_pow₀ h1η
    have hpow_2n_nn : (0 : R) ≤ (1 + η) ^ (2 * n) := le_trans zero_le_one hpow_2n
    -- Triangle via hornerPoly_affine: split the error using v' vs x*v+c
    have htri : |(v_f.toVal : R) -
        hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (x_v * v_v + c_v) x_v| ≤
        |(v_f.toVal : R) -
          hornerPoly (coeffs.map (fun c => c.toVal (R := R))) v'_v x_v| +
        |v'_v - (x_v * v_v + c_v)| * |x_v| ^ n := by
      have hlen2 : (coeffs.map (fun c => (c.toVal : R))).length = n := by simp [hn_def]
      have haffine : hornerPoly (coeffs.map (fun c => (c.toVal : R))) v'_v x_v =
          hornerPoly (coeffs.map (fun c => (c.toVal : R))) (x_v * v_v + c_v) x_v +
          (v'_v - (x_v * v_v + c_v)) * x_v ^ n := by
        conv_lhs => rw [show v'_v = (x_v * v_v + c_v) + (v'_v - (x_v * v_v + c_v)) from by ring]
        rw [hornerPoly_affine, hlen2]
      have heq : (v_f.toVal : R) -
          hornerPoly (coeffs.map (fun c => (c.toVal : R))) (x_v * v_v + c_v) x_v =
          ((v_f.toVal : R) -
            hornerPoly (coeffs.map (fun c => (c.toVal : R))) v'_v x_v) +
          (v'_v - (x_v * v_v + c_v)) * x_v ^ n := by linarith
      rw [heq]
      have := abs_add_le
        ((v_f.toVal : R) - hornerPoly (coeffs.map (fun c => (c.toVal : R))) v'_v x_v)
        ((v'_v - (x_v * v_v + c_v)) * x_v ^ n)
      rwa [abs_mul, abs_pow] at this
    -- Combine
    have hstep_xpow : |v'_v - (x_v * v_v + c_v)| * |x_v| ^ n ≤
        ((1 + η) ^ 2 - 1) * A * |x_v| ^ n := by
      rw [show v'_v - (x_v * v_v + c_v) = -(x_v * v_v + c_v - v'_v) from by ring, abs_neg]
      exact mul_le_mul_of_nonneg_right hstep_A hxpow_nn
    set E := ((1 + η) ^ 2 - 1) * A * |x_v| ^ n
    have hE_nn : (0 : R) ≤ E := by
      apply mul_nonneg (mul_nonneg _ hA_nn) hxpow_nn; linarith
    have hE_le_PA : E ≤ ((1 + η) ^ 2 - 1) * PA := by
      show ((1 + η) ^ 2 - 1) * A * |x_v| ^ n ≤ ((1 + η) ^ 2 - 1) * PA
      nlinarith [mul_le_mul_of_nonneg_left hPA_ge (by linarith : (0:R) ≤ (1+η)^2-1)]
    have htotal : |(v_f.toVal : R) -
        hornerPoly (coeffs.map (fun c => (c.toVal : R))) (x_v * v_v + c_v) x_v| ≤
        ((1 + η) ^ (2 * (n + 1)) - 1) * PA := by
      have h1 : |(v_f.toVal : R) -
          hornerPoly (coeffs.map (fun c => (c.toVal : R))) (x_v * v_v + c_v) x_v| ≤
          ((1 + η) ^ (2 * n) - 1) * (PA + E) + E := by
        have hih_exp : |(v_f.toVal : R) -
            hornerPoly (coeffs.map (fun c => (c.toVal : R))) v'_v x_v| ≤
            ((1 + η) ^ (2 * n) - 1) * (PA + E) := by
          calc |(v_f.toVal : R) -
                  hornerPoly (coeffs.map (fun c => (c.toVal : R))) v'_v x_v|
              ≤ ((1 + η) ^ (2 * n) - 1) * PA_v' := ih_bound
            _ ≤ ((1 + η) ^ (2 * n) - 1) * (PA + E) := by
                apply mul_le_mul_of_nonneg_left _ (by linarith)
                linarith [hPA_mono]
        linarith [htri, hstep_xpow]
      -- ((1+η)^{2n}-1)(PA+E) + E ≤ ((1+η)^{2(n+1)}-1)PA
      have h2 : ((1 + η) ^ (2 * n) - 1) * (PA + E) + E ≤
          ((1 + η) ^ (2 * (n + 1)) - 1) * PA := by
        have hkey := mul_le_mul_of_nonneg_left hE_le_PA hpow_2n_nn
        have hpow_step : (1 + η : R) ^ (2 * (n + 1)) = (1 + η) ^ (2 * n) * (1 + η) ^ 2 := by
          rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add]
        rw [hpow_step]
        nlinarith [mul_nonneg (by linarith : (0:R) ≤ (1+η)^(2*n) - 1) hPA_nn,
                   mul_nonneg hpow_2n_nn hE_nn]
      linarith
    -- Unfold hornerPoly cons
    simp only [List.length_cons, List.map_cons, hornerPoly]
    have hcomm : v_v * x_v + c_v = x_v * v_v + c_v := by ring
    rw [hcomm]
    convert htotal using 2

/-! ## A'. Jet Horner Derivative Error Bound (Gauge Form)

The derivative error is bounded via the L1 gauge `ν(v,d) = |v| + |d|` on
the 2D error state. The linear map `jetHornerL x` contracts under this gauge
with rate `κ = |x| + 1`, so `affineFold_gauge_per_index` gives a per-step
weighted bound. This captures both direct derivative errors and cross-coupling
from value rounding in a single framework.

The bound: `|d̂ - exact.2| ≤ Σ_k (|x|+1)^{n-1-k} · (|e_v^k| + |e_d^k|)`
where each per-step error pair is bounded by `jetHorner_step_{value,deriv}_error`. -/

-- Gauge definition and contraction for jetHornerL

/-- L1 gauge on `R × R`: `ν(v, d) = |v| + |d|`. -/
def jetHornerL1Gauge : Gauge (R × R) R where
  val := fun (v, d) => |v| + |d|
  nonneg := fun (v, d) => by positivity
  zero := by simp
  symmetric := fun (v, d) => by simp [abs_neg]
  triangle := fun (v₁, d₁) (v₂, d₂) => by
    calc |v₁ + v₂| + |d₁ + d₂|
        ≤ (|v₁| + |v₂|) + (|d₁| + |d₂|) := by linarith [abs_add_le v₁ v₂, abs_add_le d₁ d₂]
      _ = (|v₁| + |d₁|) + (|v₂| + |d₂|) := by ring

omit [FloatFormat] [FloorRing R] in
/-- `jetHornerL x` contracts under the L1 gauge with rate `|x| + 1`. -/
theorem jetHornerL1Gauge_contraction (x_v : R) (p : R × R) :
    (jetHornerL1Gauge (R := R)).val (jetHornerL x_v p) ≤
      (|x_v| + 1) * (jetHornerL1Gauge (R := R)).val p := by
  obtain ⟨v, d⟩ := p
  simp only [jetHornerL1Gauge, jetHornerL]
  calc |x_v * v| + |x_v * d + v|
      ≤ |x_v| * |v| + (|x_v| * |d| + |v|) := by
        linarith [abs_mul x_v v, abs_add_le (x_v * d) v, abs_mul x_v d]
    _ = (|x_v| + 1) * |v| + |x_v| * |d| := by ring
    _ ≤ (|x_v| + 1) * |v| + (|x_v| + 1) * |d| := by linarith [abs_nonneg d]
    _ = (|x_v| + 1) * (|v| + |d|) := by ring

set_option maxHeartbeats 1600000 in
/-- **Jet Horner derivative error bound** (gauge per-index form).

    The derivative error of the FP jet Horner trace is bounded by a weighted
    sum of per-step 2D errors under the L1 gauge `ν(v,d) = |v| + |d|`
    with contraction `κ = |x| + 1`:

    `|d̂ - exact.2| ≤ Σ_k (|x|+1)^{n-1-k} · (|e_v^k| + |e_d^k|)`

    Each `|e_v^k| + |e_d^k|` is bounded by `(2η+η²)·((|x|+1)·|v̂_k| + |c_k| + |x|·|d̂_k|)`
    via `jetHorner_step_{value,deriv}_error`. Combined with the value bound
    `jetHorner_value_error_bound`, this gives the complete 2D error analysis. -/
theorem jetHorner_deriv_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init d_init : FiniteFp} {coeffs : List FiniteFp} {v_final d_final : FiniteFp}
    (trace : JetHornerTrace x coeffs init d_init v_final d_final)
    (_hnr : trace.AllNormalRange (R := R)) :
    |(d_final.toVal : R) -
      (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal) (d_init.toVal) (x.toVal)).2| ≤
      weightedGaugeSum (jetHornerL1Gauge (R := R)) (|x.toVal (R := R)| + 1)
        (jetStepErrors (R := R) trace) := by
  -- Use the exact decomposition: (v_f, d_f) + affineFold(L, errors, 0) = exact
  -- So d_f - exact.2 = -(affineFold L errors 0).2
  -- Then |(v,d).2| ≤ ν(v,d) for the L1 gauge, and affineFold_gauge_per_index closes.
  have hdecomp := jetHorner_fp_exact_decomposition (R := R) trace
  have hd_eq : (d_final.toVal : R) -
      (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal) (d_init.toVal) (x.toVal)).2 =
      -(affineFold (jetHornerL (x.toVal : R))
        (jetStepErrors (R := R) trace) ((0 : R), (0 : R))).2 := by
    have h2 := congr_arg Prod.snd hdecomp
    simp only [Prod.add_def] at h2; linarith
  rw [hd_eq, abs_neg]
  set errors := jetStepErrors (R := R) trace
  set fold := affineFold (jetHornerL (x.toVal : R)) errors ((0 : R), (0 : R))
  have hsnd_le : |fold.2| ≤ (jetHornerL1Gauge (R := R)).val fold := by
    obtain ⟨v, d⟩ := fold; simp only [jetHornerL1Gauge]; linarith [abs_nonneg v]
  have hgauge := affineFold_gauge_per_index (jetHornerL (x.toVal : R))
    (jetHornerL_additive (x.toVal : R))
    (jetHornerL1Gauge (R := R)) (|x.toVal (R := R)| + 1)
    (by linarith [abs_nonneg (x.toVal : R)])
    (jetHornerL1Gauge_contraction (x.toVal : R))
    errors
  calc |fold.2|
      ≤ (jetHornerL1Gauge (R := R)).val fold := hsnd_le
    _ ≤ weightedGaugeSum (jetHornerL1Gauge (R := R)) (|x.toVal (R := R)| + 1) errors := hgauge

/-! ## B. Quotient Perturbation

Pure algebra: `|a/b - c/d| ≤ (|a-c|·|d| + |c|·|b-d|) / (|b|·|d|)` for b,d ≠ 0. -/

omit [FloatFormat] [FloorRing R] in
/-- **Quotient perturbation bound.**
    If `b ≠ 0` and `d ≠ 0`, then
    `|a/b - c/d| ≤ (|a - c| · |d| + |c| · |b - d|) / (|b| · |d|)`. -/
theorem quotient_perturbation
    {a b c d : R} (hb : b ≠ 0) (hd : d ≠ 0) :
    |a / b - c / d| ≤ (|a - c| * |d| + |c| * |b - d|) / (|b| * |d|) := by
  rw [div_sub_div _ _ hb hd, abs_div]
  rw [show |b * d| = |b| * |d| from abs_mul b d]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc |a * d - b * c|
      = |(a - c) * d + c * (d - b)| := by congr 1; ring
    _ ≤ |(a - c) * d| + |c * (d - b)| := abs_add_le _ _
    _ = |a - c| * |d| + |c| * |b - d| := by
        rw [abs_mul, abs_mul, abs_sub_comm d b]

/-! ## D. Full Newton-Horner Composition

Chain the pieces: jet Horner value error (A) → quotient perturbation (B) →
Newton perturbation → perturbed Newton convergence.

The capstone states: if the polynomial has a simple root and the initial
approximation is close enough, FP Newton converges to an O(η)-ball. -/

omit [FloorRing R] in
/-- **Generic Newton perturbation from evaluation errors.**

    Given evaluation errors `|v̂ - p(x)| ≤ δ_v` and `|d̂ - p'(x)| ≤ δ_d`,
    with machine epsilon `η` on division and subtraction rounding, the
    Newton step perturbation is bounded.

    This is the core composition theorem for Newton's method. Instantiate
    `δ_v, δ_d` with bounds from any evaluation strategy:
    - Standard Horner: `δ_v = ((1+η)^{2n}-1)·p̃(|x|)`, `δ_d = ((1+η)^{2n}-1)·p̃'(|x|)`
    - Compensated Horner: `δ_v = O(η)` (much tighter near roots)
    - Jet Horner: value channel error for δ_v, derivative channel for δ_d

    See `newton_horner_perturbation_bound` and `comp_newton_perturbation`
    for concrete instantiations. -/
theorem newton_perturbation_from_eval_errors
    {x_v p_x p'_x v_hat d_hat q_v x'_v δ_v δ_d : R}
    (hp'_ne : p'_x ≠ 0) (hd_ne : d_hat ≠ 0)
    -- Rounding errors
    (hsub : |x'_v - (x_v - q_v)| ≤ η * |x_v - q_v|)
    (hdiv : |q_v - v_hat / d_hat| ≤ η * |v_hat / d_hat|)
    -- Evaluation errors
    (hv : |v_hat - p_x| ≤ δ_v)
    (hd : |d_hat - p'_x| ≤ δ_d) :
    |x'_v - (x_v - p_x / p'_x)| ≤
      η * |x_v - q_v| + η * |v_hat / d_hat| +
      (δ_v * |p'_x| + |p_x| * δ_d) / (|d_hat| * |p'_x|) := by
  -- Triangle: split at the computed quotient
  have htri : |x'_v - (x_v - p_x / p'_x)| ≤
      |x'_v - (x_v - v_hat / d_hat)| + |v_hat / d_hat - p_x / p'_x| := by
    have heq : x'_v - (x_v - p_x / p'_x) =
      (x'_v - (x_v - v_hat / d_hat)) - (v_hat / d_hat - p_x / p'_x) := by ring
    rw [heq, show (x'_v - (x_v - v_hat / d_hat)) - (v_hat / d_hat - p_x / p'_x) =
      (x'_v - (x_v - v_hat / d_hat)) + (-(v_hat / d_hat - p_x / p'_x)) from by ring]
    exact le_trans (abs_add_le _ _) (by rw [abs_neg])
  -- First part: subtraction + division rounding
  have h1 : |x'_v - (x_v - v_hat / d_hat)| ≤ η * |x_v - q_v| + η * |v_hat / d_hat| := by
    have heq : x'_v - (x_v - v_hat / d_hat) =
      (x'_v - (x_v - q_v)) - (q_v - v_hat / d_hat) := by ring
    rw [heq, show (x'_v - (x_v - q_v)) - (q_v - v_hat / d_hat) =
      (x'_v - (x_v - q_v)) + (-(q_v - v_hat / d_hat)) from by ring]
    calc |(x'_v - (x_v - q_v)) + (-(q_v - v_hat / d_hat))|
        ≤ |x'_v - (x_v - q_v)| + |-(q_v - v_hat / d_hat)| := abs_add_le _ _
      _ = |x'_v - (x_v - q_v)| + |q_v - v_hat / d_hat| := by rw [abs_neg]
      _ ≤ η * |x_v - q_v| + η * |v_hat / d_hat| := by linarith
  -- Second part: quotient perturbation
  have h2 := quotient_perturbation (R := R) hd_ne hp'_ne (a := v_hat) (b := d_hat)
    (c := p_x) (d := p'_x)
  -- Bound the numerator using δ_v, δ_d
  have hnum : |v_hat - p_x| * |p'_x| + |p_x| * |d_hat - p'_x| ≤
      δ_v * |p'_x| + |p_x| * δ_d := by
    have := mul_le_mul_of_nonneg_right hv (abs_nonneg p'_x)
    have := mul_le_mul_of_nonneg_left hd (abs_nonneg p_x)
    linarith
  have hden_pos : (0 : R) < |d_hat| * |p'_x| := by positivity
  linarith [div_le_div_of_nonneg_right hnum hden_pos.le]

/-- **Newton-Horner perturbation bound with closed-form value error**.

    Strengthens `newton_horner_perturbation_bound` by substituting the closed-form
    Jet-Horner value bound `((1+η)^{2n} - 1) · p̃(|x|)` for the literal value
    deviation `|v̂ - p(x)|`. The derivative bound `δ_d` is left as a parameter —
    callers plug in `jetHorner_deriv_error_bound`'s gauge form, a tighter
    application-specific bound, or just `|d̂ - p'(x)|` itself for the trivial
    case (recovering the weak `newton_horner_perturbation_bound`).

    The full bound captures the four error sources of one FP Newton step:
    - subtraction rounding (`η · |x - q̂|`)
    - division rounding (`η · |v̂/d̂|`)
    - polynomial-value evaluation (`((1+η)^{2n} - 1) · p̃(|x|)`)
    - polynomial-derivative evaluation (`δ_d`, parameterized) -/
theorem newton_horner_perturbation_concrete
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeSticky R]
    {init : FiniteFp} {coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : NewtonStep init coeffs x_cur)
    (hnr : NewtonStepNormalRange (R := R) init coeffs x_cur step)
    (hd_hat_ne : (step.d_final.toVal : R) ≠ 0)
    (hd_exact_ne : (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) 0 (x_cur.toVal : R)).2 ≠ 0)
    {δ_d : R}
    (hδd : |(step.d_final.toVal : R) -
        (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
          (init.toVal : R) 0 (x_cur.toVal : R)).2| ≤ δ_d) :
    let x_v := (x_cur.toVal : R)
    let p_exact := hornerPoly (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) x_v
    let d_exact := (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) 0 x_v).2
    let v_hat := (step.v_final.toVal : R)
    let d_hat := (step.d_final.toVal : R)
    let p_abs := hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
        |(init.toVal : R)| |x_v|
    |(step.x_next.toVal : R) - (x_v - p_exact / d_exact)| ≤
      η * |x_v - step.quot.toVal| +
      η * |v_hat / d_hat| +
      (((1 + η) ^ (2 * coeffs.length) - 1) * p_abs * |d_exact| +
       |p_exact| * δ_d) /
        (|d_hat| * |d_exact|) := by
  intro x_v p_exact d_exact v_hat d_hat p_abs
  have hp_eq : p_exact = (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
      (init.toVal : R) 0 x_v).1 :=
    (jetHornerExact_fst_eq_hornerPoly _ _ _).symm
  rw [hp_eq]
  refine newton_perturbation_from_eval_errors hd_exact_ne hd_hat_ne
    (newton_step_sub_error (R := R) step hnr.sub_normal)
    (newton_step_div_error (R := R) step hnr.div_normal)
    ?_ hδd
  have h := jetHorner_value_error_bound (R := R) step.trace hnr.horner_normal
  rw [← jetHornerExact_fst_eq_hornerPoly] at h
  exact h

/-- **Newton-Horner perturbation bound** (jet Horner instantiation).

    Corollary of `newton_perturbation_from_eval_errors` with jet Horner
    rounding errors. -/
theorem newton_horner_perturbation_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeSticky R]
    {init : FiniteFp} {coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : NewtonStep init coeffs x_cur)
    (hnr : NewtonStepNormalRange (R := R) init coeffs x_cur step)
    (hd_hat_ne : (step.d_final.toVal : R) ≠ 0)
    (hd_exact_ne : (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) 0 (x_cur.toVal : R)).2 ≠ 0) :
    let x_v := (x_cur.toVal : R)
    let p_exact := hornerPoly (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) x_v
    let d_exact := (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) 0 x_v).2
    let v_hat := (step.v_final.toVal : R)
    let d_hat := (step.d_final.toVal : R)
    |(step.x_next.toVal : R) - (x_v - p_exact / d_exact)| ≤
      η * |x_v - step.quot.toVal| +
      η * |v_hat / d_hat| +
      (|v_hat - p_exact| * |d_exact| + |p_exact| * |d_hat - d_exact|) /
        (|d_hat| * |d_exact|) := by
  intro x_v p_exact d_exact v_hat d_hat
  have hp_eq : p_exact = (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
      (init.toVal : R) 0 x_v).1 :=
    (jetHornerExact_fst_eq_hornerPoly _ _ _).symm
  rw [hp_eq]
  exact newton_perturbation_from_eval_errors hd_exact_ne hd_hat_ne
    (newton_step_sub_error (R := R) step hnr.sub_normal)
    (newton_step_div_error (R := R) step hnr.div_normal)
    (by linarith [jetHorner_value_error_bound (R := R) step.trace hnr.horner_normal])
    (by linarith [jetHorner_value_error_bound (R := R) step.trace hnr.horner_normal])

/-- **Fully-instantiated Newton-Horner perturbation bound**.

    Plugs the jet-Horner derivative gauge bound into `newton_horner_perturbation_concrete`,
    closing the composition loop entirely. The remaining unknowns are the dimensional
    quantities `|d̂|`, `|d_exact|`, and `|p_exact|` — the user's only remaining task is
    to bound the magnitude of the polynomial value/derivative for their specific `x`. -/
theorem newton_horner_perturbation_full
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeSticky R]
    {init : FiniteFp} {coeffs : List FiniteFp} {x_cur : FiniteFp}
    (step : NewtonStep init coeffs x_cur)
    (hnr : NewtonStepNormalRange (R := R) init coeffs x_cur step)
    (hd_hat_ne : (step.d_final.toVal : R) ≠ 0)
    (hd_exact_ne : (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) 0 (x_cur.toVal : R)).2 ≠ 0) :
    let x_v := (x_cur.toVal : R)
    let p_exact := hornerPoly (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) x_v
    let d_exact := (jetHornerExact (coeffs.map (fun c => c.toVal (R := R)))
        (init.toVal : R) 0 x_v).2
    let v_hat := (step.v_final.toVal : R)
    let d_hat := (step.d_final.toVal : R)
    let p_abs := hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
        |(init.toVal : R)| |x_v|
    let δ_d := weightedGaugeSum (jetHornerL1Gauge (R := R)) (|x_v| + 1)
        (jetStepErrors (R := R) step.trace)
    |(step.x_next.toVal : R) - (x_v - p_exact / d_exact)| ≤
      η * |x_v - step.quot.toVal| +
      η * |v_hat / d_hat| +
      (((1 + η) ^ (2 * coeffs.length) - 1) * p_abs * |d_exact| +
       |p_exact| * δ_d) /
        (|d_hat| * |d_exact|) := by
  have h_deriv := jetHorner_deriv_error_bound (R := R) step.trace hnr.horner_normal
  simp only [FiniteFp.toVal_zero] at h_deriv
  exact newton_horner_perturbation_concrete step hnr hd_hat_ne hd_exact_ne h_deriv

end NewtonHorner
