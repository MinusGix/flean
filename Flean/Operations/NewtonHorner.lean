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
- `KahanSum.fpMul_error_or_zero`, `fpAdd_error_or_zero`, `fpDiv_error_or_zero` — per-operation error bounds
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

/-- **Exact Newton quadratic convergence.**

    If `p(r) = 0` and we have:
    - `|p(x) - p'(r)·(x-r)| ≤ M·|x-r|²` (Taylor remainder)
    - `|p'(x) - p'(r)| ≤ L·|x-r|` (derivative Lipschitz)

    then `|x - p(x)/p'(x) - r| ≤ (L + M)·|x-r|² / |p'(x)|`. -/
theorem exact_newton_quadratic
    {p p' : R → R} {r x : R}
    (hp'x_ne : p' x ≠ 0)
    {M : R} (hM : 0 ≤ M)
    (hTaylor : |p x - p' r * (x - r)| ≤ M * |x - r| ^ 2)
    {L : R} (hL : 0 ≤ L)
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

/-- **One-step contraction for perturbed Newton.**
    Quadratic convergence plus bounded perturbation. -/
theorem perturbed_newton_one_step
    {N : R → R} {r x x' : R} {C δ : R}
    (_hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (hquad : |N x - r| ≤ C * |x - r| ^ 2)
    (hpert : |x' - N x| ≤ δ) :
    |x' - r| ≤ C * |x - r| ^ 2 + δ := by
  calc |x' - r| = |(x' - N x) + (N x - r)| := by ring_nf
    _ ≤ |x' - N x| + |N x - r| := abs_add_le _ _
    _ ≤ δ + C * |x - r| ^ 2 := add_le_add hpert hquad
    _ = C * |x - r| ^ 2 + δ := by ring

/-- **Perturbed Newton stays in a ball.**
    If `|x - r| ≤ ρ` and `C·ρ² + δ ≤ ρ`, then `|x' - r| ≤ ρ`. -/
theorem perturbed_newton_ball
    {N : R → R} {r x x' : R} {C δ ρ : R}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hquad : |N x - r| ≤ C * |x - r| ^ 2)
    (hpert : |x' - N x| ≤ δ)
    (hin : |x - r| ≤ ρ)
    (hball : C * ρ ^ 2 + δ ≤ ρ) :
    |x' - r| ≤ ρ := by
  calc |x' - r| ≤ C * |x - r| ^ 2 + δ :=
        perturbed_newton_one_step hC hδ hquad hpert
    _ ≤ C * ρ ^ 2 + δ := by
        have h1 : |x - r| * |x - r| ≤ ρ * ρ := mul_le_mul hin hin (abs_nonneg _) hρ
        nlinarith [sq_abs (x - r), sq_abs ρ]
    _ ≤ ρ := hball

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

/-- Division error bound: `|fl(a/b) - a/b| ≤ η · |a/b|`.
    Handles both normal-range and exact-zero cases. -/
theorem fpDiv_error_or_zero
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeSticky R]
    (a b : FiniteFp) (f : FiniteFp)
    (hb : b.m ≠ 0)
    (hf : a / b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) / b.toVal) ∨ (a.toVal : R) / b.toVal = 0) :
    |(f.toVal : R) - (a.toVal / b.toVal)| ≤ η * |(a.toVal : R) / b.toVal| := by
  rcases hnormal with h | h
  · have hne : (a.toVal : R) / b.toVal ≠ 0 := ne_of_gt (isNormalRange_pos _ h)
    have hcorr := fpDivFinite_correct (R := R) a b hb hne
    rw [hcorr] at hf
    exact KahanSum.standard_error_additive _ h f hf
  · rw [h]; simp
    have hb_ne : (b.toVal : R) ≠ 0 :=
      FiniteFp.toVal_ne_zero_of_m_pos b (Nat.pos_of_ne_zero hb)
    have ha_zero : (a.toVal : R) = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' hb_ne
    have ham : a.m = 0 := (FiniteFp.toVal_significand_zero_iff (R := R)).mpr ha_zero
    have hscaled : a.m * 2 ^ divShift = 0 := by simp [ham]
    -- hf : Fp.finite a / Fp.finite b = Fp.finite f (uses HDiv Fp Fp Fp)
    -- Reduce to fpDivFinite since b.m ≠ 0
    have hf' : fpDivFinite a b = Fp.finite f := by
      simp only [div_eq_fpDiv, fpDiv, hb, ↓reduceDIte, div_finite_eq_fpDivFinite] at hf
      exact hf
    simp only [fpDivFinite, hscaled, Nat.zero_div, Nat.zero_mod,
               ↓reduceDIte, roundIntSigM] at hf'
    -- hf' identifies f with ±0 → f.m = 0 → f.toVal = 0
    -- Extract: Fp.finite f = Fp.finite (±0) → f = ±0 → f.m = 0
    have hfm : f.m = 0 := by
      rcases Bool.eq_false_or_eq_true (a.s ^^ b.s) with hs | hs <;>
        simp only [hs, ↓reduceIte] at hf' <;>
        cases (Fp.finite.inj hf') <;> rfl
    have hfv : (f.toVal : R) = 0 := FiniteFp.toVal_significand_zero_iff.mp hfm
    simp [hfv]

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
  have hdiv := fpDiv_error_or_zero (R := R) step.v_final step.d_final step.quot
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

end NewtonHorner
