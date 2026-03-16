import Flean.Operations.JetHorner
import Flean.Operations.KahanSum
import Flean.Operations.Horner

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

2. **Jet Horner error bound**: Using the 2D AffineFold gauge framework with
   `ν(v,d) = |v| + |d|` and contraction factor `κ = |x| + 1`.

## Key Infrastructure Used

- `JetHorner.jetHornerExact`, `jetHornerL`, `jetHorner_exact_decomposition` — exact 2D recurrence
- `AffineFold.affineFold_gauge_per_index` — per-index weighted error bound with gauges
- `KahanSum.fpMul_error_or_zero`, `fpAdd_error_or_zero` — per-operation error bounds
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
The value channel error satisfies `|e_v| ≤ (2η + η²)|x·v + c|`
(two operations: multiply then add), and similarly for derivative. -/

/-- Value channel per-step error: bounded in terms of `|v|·|x| + |c|`. -/
theorem jetHorner_step_value_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {v d x coeff : FiniteFp} (step : JetHornerStep v d x coeff)
    (hnr : JetHornerStepNormalRange (R := R) v d x coeff step) :
    |(x.toVal : R) * v.toVal + coeff.toVal - step.v'.toVal| ≤
      (2 * η + η ^ 2) * (|(v.toVal : R)| * |(x.toVal : R)| + |(coeff.toVal : R)|) := by
  set x_v := (x.toVal : R)
  set v_v := (v.toVal : R)
  set c_v := (coeff.toVal : R)
  set xv_v := (step.xv.toVal : R)
  set v'_v := (step.v'.toVal : R)
  have hη : (0 : R) ≤ η := by positivity
  -- Mul error: |xv - x*v| ≤ η|x*v|
  have hmul := KahanSum.fpMul_error_or_zero (R := R) x v step.xv step.hxv hnr.mul_v_normal
  -- Add error: |v' - (xv + c)| ≤ η|xv + c|
  have hadd := KahanSum.fpAdd_error_or_zero (R := R) step.xv coeff step.v' step.hv' hnr.add_v_normal
  -- Triangle
  have htri : |x_v * v_v + c_v - v'_v| ≤ |x_v * v_v - xv_v| + |xv_v + c_v - v'_v| := by
    have : x_v * v_v + c_v - v'_v = (x_v * v_v - xv_v) + (xv_v + c_v - v'_v) := by ring
    rw [this]; exact abs_add_le _ _
  have hmul' : |x_v * v_v - xv_v| ≤ η * |x_v * v_v| := by
    rw [show x_v * v_v - xv_v = -(xv_v - x_v * v_v) from by ring, abs_neg]; exact hmul
  have hadd' : |xv_v + c_v - v'_v| ≤ η * |xv_v + c_v| := by
    rw [show xv_v + c_v - v'_v = -(v'_v - (xv_v + c_v)) from by ring, abs_neg]; exact hadd
  -- |xv + c| ≤ |x*v + c| + η|x*v| (from mul error)
  have hxvc : |xv_v + c_v| ≤ |x_v * v_v + c_v| + η * |x_v * v_v| := by
    have : xv_v + c_v = (x_v * v_v + c_v) + (xv_v - x_v * v_v) := by ring
    rw [this]
    calc |x_v * v_v + c_v + (xv_v - x_v * v_v)|
        ≤ |x_v * v_v + c_v| + |xv_v - x_v * v_v| := abs_add_le _ _
      _ ≤ |x_v * v_v + c_v| + η * |x_v * v_v| := by linarith [hmul']
  -- Set A = |v|·|x| + |c|
  set A := |v_v| * |x_v| + |c_v|
  -- |x*v + c| ≤ A and |x*v| ≤ A
  have hxv_le_A : |x_v * v_v| ≤ A := by
    calc |x_v * v_v| = |v_v| * |x_v| := by rw [abs_mul, mul_comm]
      _ ≤ A := le_add_of_nonneg_right (abs_nonneg _)
  have hxvc_le_A : |x_v * v_v + c_v| ≤ A := by
    calc |x_v * v_v + c_v| ≤ |x_v * v_v| + |c_v| := abs_add_le _ _
      _ = |v_v| * |x_v| + |c_v| := by rw [abs_mul, mul_comm]
      _ ≤ A := le_refl _
  -- Combine: error ≤ η|x*v| + η(|x*v+c| + η|x*v|) = η(1+η)|x*v| + η|x*v+c|
  --                ≤ η(1+η)A + ηA = (2η + η²)A
  calc |x_v * v_v + c_v - v'_v|
      ≤ η * |x_v * v_v| + η * |xv_v + c_v| := by linarith [htri, hmul', hadd']
    _ ≤ η * |x_v * v_v| + η * (|x_v * v_v + c_v| + η * |x_v * v_v|) := by
        linarith [mul_le_mul_of_nonneg_left hxvc hη]
    _ = η * (1 + η) * |x_v * v_v| + η * |x_v * v_v + c_v| := by ring
    _ ≤ η * (1 + η) * A + η * A := by
        have h1η : (0 : R) ≤ 1 + η := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hxv_le_A (mul_nonneg hη h1η),
                   mul_le_mul_of_nonneg_left hxvc_le_A hη]
    _ = (2 * η + η ^ 2) * A := by ring

/-- Derivative channel per-step error: bounded in terms of `|d|·|x| + |v|`. -/
theorem jetHorner_step_deriv_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {v d x coeff : FiniteFp} (step : JetHornerStep v d x coeff)
    (hnr : JetHornerStepNormalRange (R := R) v d x coeff step) :
    |(x.toVal : R) * d.toVal + v.toVal - step.d'.toVal| ≤
      (2 * η + η ^ 2) * (|(d.toVal : R)| * |(x.toVal : R)| + |(v.toVal : R)|) := by
  set x_v := (x.toVal : R)
  set d_v := (d.toVal : R)
  set v_v := (v.toVal : R)
  set xd_v := (step.xd.toVal : R)
  set d'_v := (step.d'.toVal : R)
  have hη : (0 : R) ≤ η := by positivity
  -- Mul error: |xd - x*d| ≤ η|x*d|
  have hmul := KahanSum.fpMul_error_or_zero (R := R) x d step.xd step.hxd hnr.mul_d_normal
  -- Add error: |d' - (xd + v)| ≤ η|xd + v|
  have hadd := KahanSum.fpAdd_error_or_zero (R := R) step.xd v step.d' step.hd' hnr.add_d_normal
  -- Triangle
  have htri : |x_v * d_v + v_v - d'_v| ≤ |x_v * d_v - xd_v| + |xd_v + v_v - d'_v| := by
    have : x_v * d_v + v_v - d'_v = (x_v * d_v - xd_v) + (xd_v + v_v - d'_v) := by ring
    rw [this]; exact abs_add_le _ _
  have hmul' : |x_v * d_v - xd_v| ≤ η * |x_v * d_v| := by
    rw [show x_v * d_v - xd_v = -(xd_v - x_v * d_v) from by ring, abs_neg]; exact hmul
  have hadd' : |xd_v + v_v - d'_v| ≤ η * |xd_v + v_v| := by
    rw [show xd_v + v_v - d'_v = -(d'_v - (xd_v + v_v)) from by ring, abs_neg]; exact hadd
  -- |xd + v| ≤ |x*d + v| + η|x*d|
  have hxdv : |xd_v + v_v| ≤ |x_v * d_v + v_v| + η * |x_v * d_v| := by
    have : xd_v + v_v = (x_v * d_v + v_v) + (xd_v - x_v * d_v) := by ring
    rw [this]
    calc |x_v * d_v + v_v + (xd_v - x_v * d_v)|
        ≤ |x_v * d_v + v_v| + |xd_v - x_v * d_v| := abs_add_le _ _
      _ ≤ |x_v * d_v + v_v| + η * |x_v * d_v| := by linarith [hmul']
  -- Set B = |d|·|x| + |v|
  set B := |d_v| * |x_v| + |v_v|
  have hxd_le_B : |x_v * d_v| ≤ B := by
    calc |x_v * d_v| = |d_v| * |x_v| := by rw [abs_mul, mul_comm]
      _ ≤ B := le_add_of_nonneg_right (abs_nonneg _)
  have hxdv_le_B : |x_v * d_v + v_v| ≤ B := by
    calc |x_v * d_v + v_v| ≤ |x_v * d_v| + |v_v| := abs_add_le _ _
      _ = |d_v| * |x_v| + |v_v| := by rw [abs_mul, mul_comm]
      _ ≤ B := le_refl _
  calc |x_v * d_v + v_v - d'_v|
      ≤ η * |x_v * d_v| + η * |xd_v + v_v| := by linarith [htri, hmul', hadd']
    _ ≤ η * |x_v * d_v| + η * (|x_v * d_v + v_v| + η * |x_v * d_v|) := by
        linarith [mul_le_mul_of_nonneg_left hxdv hη]
    _ = η * (1 + η) * |x_v * d_v| + η * |x_v * d_v + v_v| := by ring
    _ ≤ η * (1 + η) * B + η * B := by
        have h1η : (0 : R) ≤ 1 + η := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hxd_le_B (mul_nonneg hη h1η),
                   mul_le_mul_of_nonneg_left hxdv_le_B hη]
    _ = (2 * η + η ^ 2) * B := by ring

end NewtonHorner
