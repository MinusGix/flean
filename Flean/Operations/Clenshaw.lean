import Flean.Operations.KahanSum

/-!
# Clenshaw's Algorithm — 2D Affine Structure

Clenshaw's algorithm evaluates `p(x) = Σ cₖ Tₖ(x)` using the three-term recurrence:
```
(a, b) ↦ (w·a - b + cₖ, a)
```
where `w = 2x`. The state is 2-dimensional, and each step is an **affine** map —
linear in `(a, b)` plus the additive coefficient `cₖ`.

## Key Results

- `clenshawExact_affine`: perturbation `(ea, eb)` propagates via `clenshawProp`
  (the LINEAR part of the recurrence, without coefficients)
- `clenshaw_exact_decomposition`: computed state + error propagation = exact state

The propagation function `clenshawProp n ea eb w` iterates `(ea, eb) ↦ (w·ea - eb, ea)`
without additive coefficients, capturing how perturbations propagate through the recurrence.
-/

namespace Clenshaw

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Exact Evaluation and Propagation -/

/-- Exact Clenshaw evaluation: `(a, b) ↦ (w·a - b + c, a)` for each coefficient. -/
def clenshawExact : List R → R → R → R → R × R
  | [], a, b, _ => (a, b)
  | c :: cs, a, b, w => clenshawExact cs (w * a - b + c) a w

/-- Propagation of perturbation: the LINEAR part of the Clenshaw recurrence
    (same step without the additive coefficient). Iterates `(ea, eb) ↦ (w·ea - eb, ea)`. -/
def clenshawProp : ℕ → R → R → R → R × R
  | 0, ea, eb, _ => (ea, eb)
  | n + 1, ea, eb, w => clenshawProp n (w * ea - eb) ea w

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- **2D affine property**: perturbing the initial state by `(ea, eb)` shifts the
    final state by `clenshawProp(n, ea, eb, w)` — the perturbation propagated
    through the LINEAR part of the recurrence (no coefficients).

    Generalizes `hornerPoly_affine` to 2D state. -/
theorem clenshawExact_affine (cs : List R) (a b ea eb w : R) :
    clenshawExact cs (a + ea) (b + eb) w =
      ((clenshawExact cs a b w).1 + (clenshawProp cs.length ea eb w).1,
       (clenshawExact cs a b w).2 + (clenshawProp cs.length ea eb w).2) := by
  induction cs generalizing a b ea eb with
  | nil => simp [clenshawExact, clenshawProp]
  | cons c cs ih =>
    simp only [clenshawExact, clenshawProp, List.length_cons]
    -- (a+ea)*w - (b+eb) + c = (w*a - b + c) + (w*ea - eb)
    have h1 : w * (a + ea) - (b + eb) + c = (w * a - b + c) + (w * ea - eb) := by ring
    rw [h1]
    exact ih _ _ _ _

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Propagation with zero perturbation gives zero. -/
theorem clenshawProp_zero (n : ℕ) (w : R) : clenshawProp n 0 0 w = (0, 0) := by
  induction n with
  | zero => simp [clenshawProp]
  | succ n ih => simp [clenshawProp, ih]

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Propagation is odd: negating the perturbation negates the result. -/
theorem clenshawProp_neg (n : ℕ) (ea eb w : R) :
    clenshawProp n (-ea) (-eb) w =
      (-(clenshawProp n ea eb w).1, -(clenshawProp n ea eb w).2) := by
  induction n generalizing ea eb with
  | zero => simp [clenshawProp]
  | succ n ih =>
    simp only [clenshawProp]
    have h : w * (-ea) - (-eb) = -(w * ea - eb) := by ring
    rw [h]
    exact ih _ _

/-! ## State and Trace -/

/-- State of Clenshaw evaluation: two consecutive recurrence values. -/
structure CState where
  a : FiniteFp
  b : FiniteFp

/-- One step of Clenshaw: `prod = fl(w·a)`, `diff = fl(prod - b)`, `next_a = fl(diff + c)`.
    The second component `next_b = a` is exact. -/
structure CStep [RModeExec] (st : CState) (w coeff : FiniteFp) where
  prod : FiniteFp
  hprod : w * st.a = Fp.finite prod
  diff : FiniteFp
  hdiff : prod - st.b = Fp.finite diff
  next_a : FiniteFp
  hnext : diff + coeff = Fp.finite next_a

def CStep.nextState [RModeExec] {st : CState} {w coeff : FiniteFp}
    (step : CStep st w coeff) : CState :=
  ⟨step.next_a, st.a⟩

/-- Trace of Clenshaw evaluation with fixed multiplier `w` (typically `fl(2x)`). -/
inductive CTrace [RModeExec] (w : FiniteFp) :
    List FiniteFp → CState → CState → Type where
  | nil (st : CState) : CTrace w [] st st
  | cons {st : CState} {coeff : FiniteFp} {coeffs : List FiniteFp} {final : CState}
      (step : CStep st w coeff)
      (rest : CTrace w coeffs step.nextState final) :
      CTrace w (coeff :: coeffs) st final

/-! ## Per-Step Error -/

/-- Per-step rounding error: `eₖ = (w·a - b + c) - next_a`. -/
def stepError [RModeExec] (st : CState) (w coeff : FiniteFp)
    (step : CStep st w coeff) : R :=
  (w.toVal (R := R)) * st.a.toVal - st.b.toVal + coeff.toVal - step.next_a.toVal

/-- Extract per-step errors from a Clenshaw trace. -/
def CTrace.stepErrors [RModeExec] {w : FiniteFp} :
    {coeffs : List FiniteFp} → {init final : CState} →
    CTrace w coeffs init final → List R
  | _, _, _, .nil _ => []
  | _, _, _, .cons (st := st) (coeff := coeff) step rest =>
      stepError (R := R) st w coeff step :: rest.stepErrors

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem CTrace.stepErrors_length [RModeExec] {w : FiniteFp}
    {coeffs : List FiniteFp} {init final : CState}
    (trace : CTrace w coeffs init final) :
    (trace.stepErrors (R := R)).length = coeffs.length := by
  induction trace with
  | nil => simp [CTrace.stepErrors]
  | cons _ _ ih => simp [CTrace.stepErrors, ih]

/-! ## Exact Decomposition -/

omit [FloorRing R] in
/-- **Exact decomposition for Clenshaw** (2D version).

    The computed state plus the propagated errors equals the exact state:
    ```
    final.a + errorProp.1 = exact.1
    final.b + errorProp.2 = exact.2
    ```
    where `errorProp = clenshawExact(errors, 0, 0, w)` propagates the per-step
    errors through the Clenshaw recurrence.

    Proof: by induction using `clenshawExact_affine`. At each step, the rounding
    error `eₖ` perturbs the first component by `-eₖ`. Since `next_b = a` is exact,
    the second component perturbation is 0 at the step level. The affine property
    ensures these perturbations compose correctly through the recurrence. -/
theorem clenshaw_exact_decomposition [RModeExec]
    {w : FiniteFp} {coeffs : List FiniteFp} {init final : CState}
    (trace : CTrace w coeffs init final) :
    let w_val := w.toVal (R := R)
    let errors := trace.stepErrors (R := R)
    let exact := clenshawExact (coeffs.map (fun c => c.toVal (R := R)))
      (init.a.toVal) (init.b.toVal) w_val
    let errProp := clenshawExact errors 0 0 w_val
    (final.a.toVal (R := R)) + errProp.1 = exact.1 ∧
    (final.b.toVal (R := R)) + errProp.2 = exact.2 := by
  induction trace with
  | nil => simp [CTrace.stepErrors, clenshawExact]
  | @cons st coeff coeffs final step rest ih =>
    simp only [CTrace.stepErrors, clenshawExact, List.map_cons]
    obtain ⟨ih_a, ih_b⟩ := ih
    set e := stepError (R := R) st w coeff step
    set w_val := (w.toVal : R)
    -- next_a = w*a - b + c - e
    have hnext : (step.next_a.toVal : R) =
        w_val * st.a.toVal - st.b.toVal + coeff.toVal - e := by
      simp only [stepError, e, w_val]; ring
    -- nextState = (next_a, st.a) = ((w*a-b+c) - e, a)
    --           = ((w*a-b+c) + (-e), a + 0)
    -- By IH on rest (starting from nextState):
    --   final.a + clenshawExact(rest_errors, 0, 0, w).1 = clenshawExact(rest_map, next_a, st.a, w).1
    -- By affine: clenshawExact(rest_map, (w*a-b+c) + (-e), a + 0, w) =
    --   (clenshawExact(rest_map, w*a-b+c, a, w).1 + clenshawProp(m, -e, 0, w).1, ...)
    -- So: clenshawExact(rest_map, next_a, a, w).1 =
    --   clenshawExact(rest_map, w*a-b+c, a, w).1 + clenshawProp(m, -e, 0, w).1
    -- And from IH: final.a + clenshawExact(rest_errors, 0, 0, w).1 =
    --   clenshawExact(rest_map, w*a-b+c, a, w).1 + clenshawProp(m, -e, 0, w).1
    -- We need: final.a + clenshawExact(e :: rest_errors, 0, 0, w).1 =
    --   clenshawExact(rest_map, w*a-b+c, a, w).1
    -- clenshawExact(e :: rest_errors, 0, 0, w) = clenshawExact(rest_errors, w*0-0+e, 0, w)
    --                                           = clenshawExact(rest_errors, e, 0, w)
    -- By affine: clenshawExact(rest_errors, e, 0, w) =
    --   (clenshawExact(rest_errors, 0, 0, w).1 + clenshawProp(m, e, 0, w).1, ...)
    -- So: final.a + clenshawExact(rest_errors, 0, 0, w).1 + clenshawProp(m, e, 0, w).1 =
    --   clenshawExact(rest_map, w*a-b+c, a, w).1 + clenshawProp(m, -e, 0, w).1 + clenshawProp(m, e, 0, w).1
    -- Need: clenshawProp(m, -e, 0, w) + clenshawProp(m, e, 0, w) = (0, 0)
    -- i.e., clenshawProp is odd: prop(m, -e, -eb, w) = -prop(m, e, eb, w)
    set rest_map := coeffs.map (fun c => c.toVal (R := R))
    set rest_errors := rest.stepErrors (R := R)
    -- Length fact: rest_map.length = rest_errors.length
    have hlen : rest_map.length = rest_errors.length := by
      simp only [rest_map, rest_errors, List.length_map]
      exact (rest.stepErrors_length (R := R)).symm
    set m := rest_errors.length
    -- Apply affine to split: clenshawExact rest_errors e 0 w_val
    -- = clenshawExact rest_errors 0 0 w_val + clenshawProp(m, e, 0, w_val)
    have haffine_err : clenshawExact rest_errors e 0 w_val =
        ((clenshawExact rest_errors 0 0 w_val).1 + (clenshawProp m e 0 w_val).1,
         (clenshawExact rest_errors 0 0 w_val).2 + (clenshawProp m e 0 w_val).2) := by
      have h := clenshawExact_affine rest_errors 0 0 e 0 w_val
      simp only [zero_add] at h
      exact h
    -- Apply affine on rhs: next_a = (w*a-b+c) + (-e), st.a = a + 0
    have haffine_rhs : clenshawExact rest_map (step.next_a.toVal (R := R)) (st.a.toVal) w_val =
        ((clenshawExact rest_map (w_val * st.a.toVal - st.b.toVal + coeff.toVal) (st.a.toVal) w_val).1
          + (clenshawProp m (-e) 0 w_val).1,
         (clenshawExact rest_map (w_val * st.a.toVal - st.b.toVal + coeff.toVal) (st.a.toVal) w_val).2
          + (clenshawProp m (-e) 0 w_val).2) := by
      have h := clenshawExact_affine rest_map
        (w_val * st.a.toVal - st.b.toVal + coeff.toVal) (st.a.toVal) (-e) 0 w_val
      simp only [add_zero] at h
      rw [hlen] at h
      convert h using 2
      linarith [hnext]
    -- clenshawProp_neg: clenshawProp m (-e) 0 w_val = -(clenshawProp m e 0 w_val)
    have hneg : (clenshawProp m (-e) 0 w_val).1 = -(clenshawProp m e 0 w_val).1 ∧
                (clenshawProp m (-e) 0 w_val).2 = -(clenshawProp m e 0 w_val).2 := by
      have h := clenshawProp_neg m e 0 w_val
      simp only [neg_zero] at h
      exact ⟨(Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
    -- Unfold step.nextState in IH to expose step.next_a and st.a
    simp only [CStep.nextState] at ih_a ih_b
    -- Rewrite IH using haffine_rhs
    rw [haffine_rhs] at ih_a ih_b
    -- Goal has: clenshawExact rest_errors (w_val * 0 - 0 + e) 0 w_val
    -- which equals clenshawExact rest_errors e 0 w_val
    have hgoal_simp : w_val * (0 : R) - 0 + e = e := by ring
    constructor
    · rw [hgoal_simp, haffine_err]
      linarith [hneg.1]
    · rw [hgoal_simp, haffine_err]
      linarith [hneg.2]

end Clenshaw
