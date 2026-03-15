import Flean.Operations.AffineFold
import Flean.Operations.Horner
import Flean.Operations.Clenshaw
import Flean.Operations.CompensatedHorner

/-!
# AffineFold Instances: Horner and Clenshaw

Shows that Horner (1D) and Clenshaw (2D) are instances of the generic `AffineFold`
framework, validating the abstraction.

For each algorithm:
1. The linear map `L` is additive
2. `affineFold L` equals the concrete evaluation function
3. `affineProp L` equals the concrete propagation function
4. The concrete affine theorem follows as a corollary
-/

namespace AffineFoldInstances

open AffineFold Horner Clenshaw

/-! ## Horner Instance -/

section Horner

variable {R : Type*} [Field R]

/-- Horner's linear map: `L(a) = x * a`. -/
def hornerL (x : R) : R → R := (x * ·)

theorem hornerL_additive (x : R) : ∀ a b : R, hornerL x (a + b) = hornerL x a + hornerL x b :=
  fun a b => by unfold hornerL; ring

/-- `affineFold` with `hornerL` equals `hornerPoly`. -/
theorem affineFold_eq_hornerPoly (cs : List R) (a x : R) :
    affineFold (hornerL x) cs a = hornerPoly cs a x := by
  induction cs generalizing a with
  | nil => simp [affineFold, hornerPoly]
  | cons c cs ih =>
    simp only [affineFold, hornerPoly, hornerL]
    rw [mul_comm x a]
    rw [ih]

/-- `affineProp` with `hornerL` equals `e * x^n`. -/
theorem affineProp_eq_horner (n : ℕ) (e x : R) :
    affineProp (hornerL x) n e = e * x ^ n := by
  induction n generalizing e with
  | zero => simp [affineProp]
  | succ n ih => simp only [affineProp, hornerL]; rw [ih]; ring

/-- `hornerPoly_affine` as a corollary of `affineFold_affine`. -/
theorem hornerPoly_affine_from_generic (cs : List R) (a e x : R) :
    hornerPoly cs (a + e) x = hornerPoly cs a x + e * x ^ cs.length := by
  rw [← affineFold_eq_hornerPoly, ← affineFold_eq_hornerPoly,
      ← affineProp_eq_horner]
  exact affineFold_affine (hornerL x) (hornerL_additive x) cs a e

end Horner

/-! ## Clenshaw Instance -/

section Clenshaw

variable {R : Type*} [Field R]

/-- Clenshaw's linear map: `L(a, b) = (w * a - b, a)`. -/
def clenshawL (w : R) : R × R → R × R := fun (a, b) => (w * a - b, a)

theorem clenshawL_additive (w : R) :
    ∀ a b, clenshawL w (a + b) = clenshawL w a + clenshawL w b :=
  fun (a₁, b₁) (a₂, b₂) => by
    simp only [clenshawL]
    simp [Prod.add_def, Prod.ext_iff]
    ring

/-- Convert a coefficient list to Clenshaw offsets `(c, 0)`. -/
def clenshawOffsets (cs : List R) : List (R × R) := cs.map (·, 0)

/-- `affineFold` with `clenshawL` and `clenshawOffsets` equals `clenshawExact`. -/
theorem affineFold_eq_clenshawExact (cs : List R) (a b w : R) :
    affineFold (clenshawL w) (clenshawOffsets cs) (a, b) = clenshawExact cs a b w := by
  induction cs generalizing a b with
  | nil => simp [affineFold, clenshawOffsets, clenshawExact]
  | cons c cs ih =>
    simp only [affineFold, clenshawOffsets, clenshawExact, clenshawL, List.map_cons]
    have : (w * a - b, a) + (c, (0 : R)) = (w * a - b + c, a) := by
      ext <;> simp [Prod.add_def]
    rw [this]
    exact ih _ _

/-- `affineProp` with `clenshawL` equals `clenshawProp`. -/
theorem affineProp_eq_clenshawProp (n : ℕ) (ea eb w : R) :
    affineProp (clenshawL w) n (ea, eb) = clenshawProp n ea eb w := by
  induction n generalizing ea eb with
  | zero => simp [affineProp, clenshawProp]
  | succ n ih => simp only [affineProp, clenshawProp, clenshawL]; exact ih _ _

/-- `clenshawExact_affine` as a corollary of `affineFold_affine`. -/
theorem clenshawExact_affine_from_generic (cs : List R) (a b ea eb w : R) :
    clenshawExact cs (a + ea) (b + eb) w =
      ((clenshawExact cs a b w).1 + (clenshawProp cs.length ea eb w).1,
       (clenshawExact cs a b w).2 + (clenshawProp cs.length ea eb w).2) := by
  have h := affineFold_affine (clenshawL w) (clenshawL_additive w)
    (clenshawOffsets cs) (a, b) (ea, eb)
  rw [affineFold_eq_clenshawExact, affineFold_eq_clenshawExact] at h
  have hlen : (clenshawOffsets cs).length = cs.length := by simp [clenshawOffsets]
  rw [hlen] at h
  rw [affineProp_eq_clenshawProp] at h
  simp only [Prod.add_def] at h
  have h1 := congr_arg Prod.fst h
  have h2 := congr_arg Prod.snd h
  simp only [] at h1 h2
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h1, h2⟩

end Clenshaw

/-! ## Horner Error Bound from Generic Framework -/

section HornerErrorBound

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- `hornerL x` has contraction bound `|x|`: `|L(e)| = |x * e| = |x| · |e|`. -/
theorem hornerL_bound (x : R) (e : R) : |hornerL x e| ≤ |x| * |e| := by
  simp [hornerL, abs_mul]

/-- **Propagation bound for Horner** (derived from generic `affineProp_abs_le`):
    `|affineProp (hornerL x) n e| ≤ |x|^n · |e|`.

    This is `|e · x^n| ≤ |x|^n · |e|` — obvious, but derived generically. -/
theorem horner_prop_bound (x : R) (n : ℕ) (e : R) :
    |affineProp (hornerL x) n e| ≤ |x| ^ n * |e| :=
  affineProp_abs_le (hornerL x) |x| (abs_nonneg x) (hornerL_bound x) n e

/-- **Horner uniform error bound from generic framework.**

    If each per-step error satisfies `|εₖ| ≤ δ` and `|x| ≥ 1`, then:
    `|hornerPoly(errors, 0, x)| ≤ n · δ · |x|^n`

    Derived from `affineFold_error_uniform_bound` with `κ = |x|`. -/
theorem horner_error_uniform_from_generic (x : R) (hx : 1 ≤ |x|)
    (errors : List R) (δ : R) (hδ : 0 ≤ δ)
    (herr : ∀ e ∈ errors, |e| ≤ δ) :
    |hornerPoly errors 0 x| ≤ (errors.length : R) * δ * |x| ^ errors.length := by
  rw [← affineFold_eq_hornerPoly]
  exact affineFold_error_uniform_bound (hornerL x) (hornerL_additive x) |x| hx
    (hornerL_bound x) errors δ hδ herr

/-- **Exact decomposition for Horner from generic framework.**

    `computed + hornerPoly(errors, 0, x) = hornerPoly(coeffs, init, x)`

    Derived from `affineFold_exact_decomposition`. -/
theorem horner_exact_decomposition_from_generic
    (coeffs errors : List R) (init : R) (computed : R) (x : R)
    (hlen : coeffs.length = errors.length)
    (hcomputed : computed = hornerPoly (List.zipWith (· - ·) coeffs errors) init x) :
    computed + hornerPoly errors 0 x = hornerPoly coeffs init x := by
  simp only [← affineFold_eq_hornerPoly] at hcomputed ⊢
  exact affineFold_exact_decomposition (hornerL x) (hornerL_additive x)
    coeffs errors init computed hlen hcomputed

/-! ### Bridge: weightedErrorSum = hornerPoly of absolute errors -/

/-- The weighted error sum `Σ|eₖ|·|x|^{n-1-k}` IS `hornerPoly(|errors|, 0, |x|)`.

    This connects the AffineFold per-index bound to the Horner absolute polynomial. -/
theorem weightedErrorSum_eq_hornerPoly (x : R) (errors : List R) :
    weightedErrorSum |x| errors = hornerPoly (errors.map (|·|)) 0 |x| := by
  induction errors with
  | nil => simp [weightedErrorSum, hornerPoly]
  | cons e es ih =>
    simp only [weightedErrorSum, hornerPoly, List.map_cons, zero_mul, zero_add]
    -- Goal: |x|^es.length * |e| + weightedErrorSum |x| es = hornerPoly(es.map|·|, |e|, |x|)
    -- By IH: weightedErrorSum |x| es = hornerPoly(es.map|·|, 0, |x|)
    -- By affine: hornerPoly(es.map|·|, |e|, |x|) = hornerPoly(es.map|·|, 0, |x|) + |e|*|x|^m
    rw [ih]
    have haffine := hornerPoly_affine (es.map (|·|)) 0 |e| |x|
    simp only [zero_add, List.length_map] at haffine
    linarith

/-- **Horner error via per-index bound**: for any errors list,
    `|hornerPoly(errors, 0, x)| ≤ hornerPoly(|errors|, 0, |x|)`.

    Combines the AffineFold per-index bound with the structural bridge. -/
theorem hornerPoly_abs_le_per_index (x : R) (errors : List R) :
    |hornerPoly errors 0 x| ≤ hornerPoly (errors.map (|·|)) 0 |x| := by
  rw [← affineFold_eq_hornerPoly, ← weightedErrorSum_eq_hornerPoly]
  exact affineFold_error_per_index (hornerL x) (hornerL_additive x)
    |x| (abs_nonneg x) (hornerL_bound x) errors

/-- **Full Horner error chain from generic framework.**

    Given per-step error bounds, derive the Horner error bound:
    `|computed - exact| ≤ hornerPoly(|error_bounds|, 0, |x|)`

    This composes: exact decomposition → per-index bound → hornerPoly bridge.

    To get `((1+η)^n - 1)·p̃(|x|)`, instantiate with per-step bounds
    `|eₖ| ≤ ((1+η)^2-1)·(|sₖ|·|x| + |cₖ|)` and use `hornerPoly_mono`. -/
theorem horner_error_from_framework
    (coeffs errors : List R) (init : R) (computed : R) (x : R)
    (hlen : coeffs.length = errors.length)
    (hcomputed : computed = hornerPoly (List.zipWith (· - ·) coeffs errors) init x) :
    |computed - hornerPoly coeffs init x| ≤
      hornerPoly (errors.map (|·|)) 0 |x| := by
  -- From exact decomposition: computed + hornerPoly(errors, 0, x) = exact
  have hdecomp := horner_exact_decomposition_from_generic coeffs errors init computed x
    hlen hcomputed
  -- So computed - exact = -hornerPoly(errors, 0, x)
  have heq : computed - hornerPoly coeffs init x = -(hornerPoly errors 0 x) := by linarith
  rw [heq, abs_neg]
  exact hornerPoly_abs_le_per_index x errors

/-- **Coefficient-list monotonicity for hornerPoly**: if `aᵢ ≤ bᵢ` element-wise,
    `acc_a ≤ acc_b`, and `x ≥ 0`, then `hornerPoly(as, acc_a, x) ≤ hornerPoly(bs, acc_b, x)`. -/
theorem hornerPoly_mono_coeffs (as bs : List R) (acc_a acc_b xv : R)
    (hlen : as.length = bs.length) (hacc : acc_a ≤ acc_b) (hx : 0 ≤ xv)
    (hcoeffs : ∀ i (hi : i < as.length), as[i] ≤ bs[i]'(by omega)) :
    hornerPoly as acc_a xv ≤ hornerPoly bs acc_b xv := by
  induction as generalizing bs acc_a acc_b with
  | nil =>
    match bs with
    | [] => exact hacc
    | _ :: _ => simp at hlen
  | cons a as ih =>
    match bs, hlen with
    | b :: bs, hlen =>
      simp only [hornerPoly]
      have hlen' : as.length = bs.length := by
        simp only [List.length_cons] at hlen; omega
      have ha_le : a ≤ b := by
        have := hcoeffs 0 (List.length_pos_of_ne_nil (by intro h; simp [h] at hlen))
        simpa using this
      apply ih bs (acc_a * xv + a) (acc_b * xv + b) hlen' <;> try assumption
      · nlinarith [mul_le_mul_of_nonneg_right hacc hx]
      · intro i hi; have := hcoeffs (i + 1) (by simp; omega); simpa using this

/-! ### Standard `((1+η)^{2n}-1)·p̃(|x|)` from Framework

The full derivation composes:
1. Exact decomposition: `final + hornerPoly(errors, 0, x) = exact`
2. Per-index bound: `|hornerPoly(errors, 0, x)| ≤ hornerPoly(|errors|, 0, |x|)`
3. Monotonicity: bound `hornerPoly(|errors|, 0, |x|)` using per-step bounds
4. Result: `|final - exact| ≤ hornerPoly(bounds, 0, |x|)` -/

/-- **Horner bound from exact decomposition + per-index + monotonicity.**

    Given per-step error bounds `|eₖ| ≤ bₖ`:
    `|final - exact| ≤ hornerPoly(bounds, 0, |x|)`

    To get `((1+η)^{2n}-1)·p̃(|x|)`, instantiate each `bₖ` with the
    per-step FP error bound and use `hornerPoly_mono`. -/
theorem horner_bound_from_decomposition
    [RModeExec]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : Horner.HornerTrace x coeffs init final)
    (bounds : List R)
    (hlen : (CompensatedHorner.stepErrors trace (R := R)).length = bounds.length)
    (hbounds_nn : ∀ b ∈ bounds, 0 ≤ b)
    (hstep_bounds : ∀ i (hi : i < bounds.length),
      |(CompensatedHorner.stepErrors trace (R := R))[i]'(by omega)| ≤ bounds[i]) :
    |(final.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      hornerPoly bounds 0 |x.toVal (R := R)| := by
  -- Step 1: exact decomposition gives final + hornerPoly(errors, 0, x) = exact
  have hdecomp := CompensatedHorner.comp_horner_exact_decomposition (R := R) trace
  -- So |final - exact| = |hornerPoly(errors, 0, x)|
  have herr : |(final.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| =
      |hornerPoly (CompensatedHorner.stepErrors trace (R := R)) 0 (x.toVal)| := by
    have : (final.toVal : R) -
        hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal) =
        -(hornerPoly (CompensatedHorner.stepErrors trace (R := R)) 0 (x.toVal)) := by linarith
    rw [this, abs_neg]
  rw [herr]
  -- Step 2: per-index bound gives |hornerPoly(errors, 0, x)| ≤ hornerPoly(|errors|, 0, |x|)
  have hpi := hornerPoly_abs_le_per_index (x.toVal (R := R)) (CompensatedHorner.stepErrors trace (R := R))
  -- Step 3: monotonicity — bound |errors| by bounds element-wise
  -- hornerPoly(|errors|, 0, |x|) ≤ hornerPoly(bounds, 0, |x|) since |eₖ| ≤ bₖ
  suffices hmono : hornerPoly ((CompensatedHorner.stepErrors trace (R := R)).map (|·|)) 0 |x.toVal (R := R)| ≤
      hornerPoly bounds 0 |x.toVal (R := R)| from le_trans hpi hmono
  have hlen_map : ((CompensatedHorner.stepErrors trace (R := R)).map (|·|)).length =
      bounds.length := by simp [hlen]
  exact hornerPoly_mono_coeffs _ bounds 0 0 |x.toVal| hlen_map
    le_rfl (abs_nonneg _)
    (fun i hi => by
      simp only [List.getElem_map]
      exact hstep_bounds i (by rw [← hlen]; simp at hi ⊢; exact hi))

end HornerErrorBound

end AffineFoldInstances
