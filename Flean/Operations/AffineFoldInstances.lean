import Flean.Operations.AffineFold
import Flean.Operations.Horner
import Flean.Operations.HornerFMA
import Flean.Operations.Clenshaw
import Flean.Operations.CompensatedHorner
import Flean.Operations.DotProduct
import Flean.Operations.DotProductFMA
import Flean.Operations.GeneralAccum

/-!
# AffineFold Instances: Horner, Clenshaw, and Dot Product

Shows that Horner (1D), Clenshaw (2D), and dot product (κ=1) are instances of
the generic `AffineFold` framework, validating the abstraction.

For each algorithm:
1. The linear map `L` is additive
2. `affineFold L` equals the concrete evaluation function
3. `affineProp L` equals the concrete propagation function
4. The concrete affine theorem follows as a corollary
-/

namespace AffineFoldInstances

open AffineFold Horner Clenshaw DotProduct DotProductFMA

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

omit [FloatFormat] [FloorRing R] in
/-- `hornerL x` has contraction bound `|x|`: `|L(e)| = |x * e| = |x| · |e|`. -/
theorem hornerL_bound (x : R) (e : R) : |hornerL x e| ≤ |x| * |e| := by
  simp [hornerL, abs_mul]

omit [FloatFormat] [FloorRing R] in
/-- **Propagation bound for Horner** (derived from generic `affineProp_abs_le`):
    `|affineProp (hornerL x) n e| ≤ |x|^n · |e|`.

    This is `|e · x^n| ≤ |x|^n · |e|` — obvious, but derived generically. -/
theorem horner_prop_bound (x : R) (n : ℕ) (e : R) :
    |affineProp (hornerL x) n e| ≤ |x| ^ n * |e| :=
  affineProp_abs_le (hornerL x) |x| (abs_nonneg x) (hornerL_bound x) n e

omit [FloatFormat] [FloorRing R] in
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

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
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

omit [FloatFormat] [FloorRing R] in
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

omit [FloatFormat] [FloorRing R] in
/-- **Horner error via per-index bound**: for any errors list,
    `|hornerPoly(errors, 0, x)| ≤ hornerPoly(|errors|, 0, |x|)`.

    Combines the AffineFold per-index bound with the structural bridge. -/
theorem hornerPoly_abs_le_per_index (x : R) (errors : List R) :
    |hornerPoly errors 0 x| ≤ hornerPoly (errors.map (|·|)) 0 |x| := by
  rw [← affineFold_eq_hornerPoly, ← weightedErrorSum_eq_hornerPoly]
  exact affineFold_error_per_index (hornerL x) (hornerL_additive x)
    |x| (abs_nonneg x) (hornerL_bound x) errors

omit [FloatFormat] [FloorRing R] in
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

omit [FloatFormat] [FloorRing R] in
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

omit [FloorRing R] in
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

omit [FloatFormat] [FloorRing R] in
/-- `acc · x^n ≤ hornerPoly(cs, acc, x)` when all inputs are nonneg. -/
theorem hornerPoly_ge_acc_xpow (cs : List R) (acc xv : R)
    (hx : 0 ≤ xv) (hcs : ∀ c ∈ cs, 0 ≤ c) :
    acc * xv ^ cs.length ≤ hornerPoly cs acc xv := by
  have h := hornerPoly_affine cs 0 acc xv
  simp only [zero_add] at h; rw [h]
  linarith [hornerPoly_nonneg cs 0 xv le_rfl hx hcs]

/-! ### Generic Weighted Error Sum Bound

The core algebraic lemma for accumulator algorithms with relative per-step
errors. Given:
- Per-step error: `|e_k| ≤ α · (κ · mag_k + offset_k)`
- Magnitude recurrence: `mag_{k+1} ≤ (1+α) · (κ · mag_k + offset_k)`

Then: `weightedErrorSum κ errors ≤ ((1+α)^n - 1) · hornerPoly(offsets, mag₀, κ)`

This captures Horner (κ=|x|, α=(1+η)²-1), HornerFMA (κ=|x|, α=η),
DotProduct (κ=1, α=(1+η)²-1), DotProductFMA (κ=1, α=η). -/

omit [FloatFormat] [FloorRing R] in
set_option maxHeartbeats 800000 in
/-- **Generic weighted error sum bound for accumulator algorithms.**

    Given errors, offsets, and per-step magnitudes satisfying a relative error
    model and magnitude recurrence, the weighted error sum is bounded by
    `((1+α)^n - 1) · hornerPoly(offsets, mag₀, κ)`.

    The algebraic core: at each step, the per-step error `α · M` weighted by
    `κ^{remaining}` is absorbed into the growing polynomial bound via the
    identity `(1+α)^n · α + ((1+α)^n - 1) = (1+α)^{n+1} - 1`. -/
theorem weightedErrorSum_le_of_relative_errors
    (κ α : R) (hκ : 0 ≤ κ) (hα : 0 ≤ α)
    (errors offsets : List R) (mags : ℕ → R)
    (hlen : errors.length = offsets.length)
    (hoffsets : ∀ c ∈ offsets, 0 ≤ c)
    (hmags_nn : ∀ k, 0 ≤ mags k)
    (herr : ∀ k (hk : k < errors.length),
        |errors[k]| ≤ α * (κ * mags k + offsets[k]'(by omega)))
    (hrecur : ∀ k (hk : k < errors.length),
        mags (k + 1) ≤ (1 + α) * (κ * mags k + offsets[k]'(by omega))) :
    weightedErrorSum κ errors ≤
      ((1 + α) ^ errors.length - 1) * hornerPoly offsets (mags 0) κ := by
  induction errors generalizing offsets mags with
  | nil => simp [weightedErrorSum]
  | cons e es ih =>
    match offsets, hlen with
    | c :: cs, hlen' =>
    simp only [weightedErrorSum, List.length_cons, hornerPoly]
    set n := es.length
    -- M matches hornerPoly's unfolding: acc * x + c
    set M := mags 0 * κ + c with hM_def
    set P := hornerPoly cs M κ
    -- Per-step error: |e| ≤ α * M (note κ * mags 0 + c = mags 0 * κ + c)
    have hMcomm : κ * mags 0 + c = M := by rw [hM_def, mul_comm]
    have he : |e| ≤ α * M := by rw [← hMcomm]; exact herr 0 (by simp)
    -- Magnitude recurrence: mags 1 ≤ (1+α) * M
    have hm1 : mags 1 ≤ (1 + α) * M := by rw [← hMcomm]; exact hrecur 0 (by simp)
    -- IH with shifted indices
    have hlen_tail : es.length = cs.length := by simpa using hlen'
    have hcs_nn : ∀ c' ∈ cs, 0 ≤ c' := fun c' hc' => hoffsets c' (List.mem_cons_of_mem _ hc')
    have ih_bound := ih cs (fun k => mags (k + 1)) hlen_tail hcs_nn
      (fun k => hmags_nn (k + 1))
      (fun k hk => herr (k + 1) (by simp; omega))
      (fun k hk => hrecur (k + 1) (by simp; omega))
    -- Positivity
    have hc_nn : (0 : R) ≤ c := hoffsets c List.mem_cons_self
    have hM_nn : (0 : R) ≤ M := add_nonneg (mul_nonneg (hmags_nn 0) hκ) hc_nn
    have hκn : (0 : R) ≤ κ ^ n := pow_nonneg hκ n
    have h1α : (1 : R) ≤ 1 + α := by linarith
    have h1αn : (0 : R) ≤ (1 + α) ^ n := pow_nonneg (by linarith) n
    have h1αn_sub : (0 : R) ≤ (1 + α) ^ n - 1 := by linarith [one_le_pow₀ h1α (n := n)]
    -- Monotonicity: hornerPoly cs (mags 1) κ ≤ hornerPoly cs ((1+α)*M) κ
    have hP_mono : hornerPoly cs (mags 1) κ ≤ hornerPoly cs ((1 + α) * M) κ :=
      hornerPoly_mono cs _ _ κ hm1 hκ hcs_nn
    -- Affine: hornerPoly cs ((1+α)*M) κ = P + α*M*κ^n
    have hP_affine : hornerPoly cs ((1 + α) * M) κ = P + α * M * κ ^ n := by
      have h := hornerPoly_affine cs M (α * M) κ
      rw [show M + α * M = (1 + α) * M from by ring] at h
      simp only [List.length_cons] at hlen'
      rw [show cs.length = n from by omega] at h
      exact h
    -- Dominance: M * κ^n ≤ P
    have hMκn_le : M * κ ^ n ≤ P := by
      have := hornerPoly_ge_acc_xpow cs M κ hκ hcs_nn
      rw [show cs.length = n from by omega] at this; exact this
    have hP_nn : (0 : R) ≤ P := le_trans (mul_nonneg hM_nn hκn) hMκn_le
    -- Power identity: (1+α)^{n+1} - 1 = (1+α)^n · α + ((1+α)^n - 1)
    have hpow_split : (1 + α) ^ (n + 1) - 1 =
        (1 + α) ^ n * α + ((1 + α) ^ n - 1) := by rw [pow_succ]; ring
    -- Main algebra:
    -- κ^n·|e| + wes(es) ≤ κ^n·α·M + ((1+α)^n-1)·(P + α·M·κ^n)
    --   = ((1+α)^n·α)·M·κ^n + ((1+α)^n-1)·P
    --   ≤ ((1+α)^n·α)·P + ((1+α)^n-1)·P = ((1+α)^{n+1}-1)·P
    rw [hpow_split]
    nlinarith [mul_le_mul_of_nonneg_right he hκn,
               mul_le_mul_of_nonneg_left (le_trans hP_mono (le_of_eq hP_affine)) h1αn_sub,
               mul_le_mul_of_nonneg_left hMκn_le (mul_nonneg h1αn hα)]

/-! ### Simplified Error Bound via Actual Magnitudes

The main `weightedErrorSum_le_of_relative_errors` requires a magnitude function
satisfying a recurrence. In practice, we always use `actual(k) = |fp_acc_k|`.
The recurrence `actual(k+1) ≤ (1+α) · (κ · actual(k) + offset(k))` follows
from `magnitude_of_relative_error` at each step. This wrapper handles the
monotonicity lifting internally. -/

omit [FloatFormat] [FloorRing R] in
/-- **Simplified generic weighted error sum bound.**

    Only requires per-step error bounds against *actual* FP magnitudes.
    The magnitude recurrence lifts to the generic theorem internally. -/
theorem weightedErrorSum_le_of_step_errors
    (κ α : R) (hκ : 0 ≤ κ) (hα : 0 ≤ α)
    (errors offsets : List R) (actual : ℕ → R) (init : R)
    (hlen : errors.length = offsets.length)
    (hoffsets : ∀ c ∈ offsets, 0 ≤ c)
    (hinit : actual 0 ≤ init)
    (hactual_nn : ∀ k, 0 ≤ actual k)
    (herr : ∀ k (hk : k < errors.length),
        |errors[k]| ≤ α * (κ * actual k + offsets[k]'(by omega)))
    (hrecur : ∀ k (hk : k < errors.length),
        actual (k + 1) ≤ (1 + α) * (κ * actual k + offsets[k]'(by omega))) :
    weightedErrorSum κ errors ≤
      ((1 + α) ^ errors.length - 1) * hornerPoly offsets init κ := by
  -- Use actual magnitudes directly, but with init as the starting point for the bound.
  -- We need: actual(k) ≤ wcm(k) where wcm satisfies the same recurrence starting at init.
  -- Then error bounds transfer: |e_k| ≤ α * (κ * actual(k) + offset_k) ≤ α * (κ * wcm(k) + offset_k).
  -- Instead of defining wcm explicitly, just show `actual` itself works up to init:
  -- Apply the original theorem with a monotone wrapper.
  refine weightedErrorSum_le_of_relative_errors κ α hκ hα errors offsets
    actual hlen hoffsets hactual_nn herr hrecur |>.trans ?_
  -- Need: hornerPoly offsets (actual 0) κ ≤ hornerPoly offsets init κ
  exact mul_le_mul_of_nonneg_left
    (hornerPoly_mono offsets _ init κ hinit hκ hoffsets)
    (by linarith [one_le_pow₀ (show (1 : R) ≤ 1 + α by linarith) (n := errors.length)])

/-! ### Helper: Magnitude from Relative Error

If `|exact - fp| ≤ α * M` and `|exact| ≤ M`, then `|fp| ≤ (1+α) * M`.
Eliminates the need for separate magnitude proofs per algorithm. -/

omit [FloatFormat] [FloorRing R] in
/-- Derive FP magnitude bound from relative error bound.
    `|fp| ≤ |exact| + |error| ≤ M + α*M = (1+α)*M`. -/
theorem magnitude_of_relative_error (exact fp M α : R)
    (hexact : |exact| ≤ M) (herr : |exact - fp| ≤ α * M) :
    |fp| ≤ (1 + α) * M := by
  have h := abs_sub_abs_le_abs_sub fp exact
  linarith [abs_sub_comm exact fp]

/-! ### Master Composition Theorem

Combines exact decomposition + per-index bound + generic weighted error sum
into a single theorem. Each algorithm only needs to provide:
- Step errors and exact decomposition
- Per-step error bound and magnitude recurrence (via `weightedErrorSum_le_of_relative_errors`)
-/

omit [FloatFormat] [FloorRing R] in
/-- **Master accumulator error bound.**

    Given an exact decomposition and a weighted error sum bound,
    derive `|final - exact| ≤ bound`. Composes:
    1. Exact decomposition: `final + hornerPoly(errors, 0, x) = exact`
    2. Per-index: `|hornerPoly(errors, 0, x)| ≤ weightedErrorSum |x| errors`
    3. Weighted sum bound: `weightedErrorSum |x| errors ≤ bound` -/
theorem accumulator_error_bound
    (final exact_val x : R) (errors : List R) (bound : R)
    (hdecomp : final + hornerPoly errors 0 x = exact_val)
    (hwes : weightedErrorSum |x| errors ≤ bound) :
    |final - exact_val| ≤ bound := by
  have herr : final - exact_val = -(hornerPoly errors 0 x) := by linarith
  rw [herr, abs_neg]
  have hpi := hornerPoly_abs_le_per_index x errors
  rw [← weightedErrorSum_eq_hornerPoly] at hpi
  linarith

/-! ### Full `((1+η)^{2n}-1)·p̃(|x|)` via AffineFold Framework

The full derivation composes:
1. Per-step combined error: `|acc·x + c - next| ≤ ((1+η)²-1)·(|acc|·|x| + |c|)`
2. Per-step magnitude: `|next| ≤ (1+η)²·(|acc|·|x| + |c|)` (derived from error via `magnitude_of_relative_error`)
3. Weighted error sum bound via generic `weightedErrorSum_le_of_relative_errors`
4. Composition via `accumulator_error_bound` -/

/-- Per-step combined FP error for one Horner step: the combined error from
    multiplication followed by addition is at most `((1+η)²-1)` times the
    absolute magnitude of the exact operation on FP inputs. -/
theorem horner_step_combined_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x coeff : FiniteFp}
    (step : HornerStep acc x coeff)
    (hnr : HornerStepNormalRange (R := R) acc x coeff step) :
    |(acc.toVal : R) * x.toVal + coeff.toVal - step.next.toVal| ≤
      ((1 + η) ^ 2 - 1) * (|(acc.toVal : R)| * |x.toVal| + |coeff.toVal|) := by
  set av := (acc.toVal : R); set xv := (x.toVal : R); set cv := (coeff.toVal : R)
  set pv := (step.prod.toVal : R); set nv := (step.next.toVal : R)
  have hη : (0 : R) ≤ η := by positivity
  have hmul := KahanSum.fpMul_error_or_zero (R := R) acc x step.prod step.hprod hnr.mul_normal
  have hadd := KahanSum.fpAdd_error_or_zero (R := R) step.prod coeff step.next step.hnext
    hnr.add_normal
  have hprod : |pv| ≤ (1 + η) * (|av| * |xv|) := by
    have := le_trans (abs_sub_abs_le_abs_sub pv (av * xv)) hmul; rw [abs_mul] at this; linarith
  have hpc : |pv + cv| ≤ (1 + η) * (|av| * |xv|) + |cv| :=
    le_trans (abs_add_le pv cv) (by linarith)
  have htri : |av * xv + cv - nv| ≤ |nv - (pv + cv)| + |pv - av * xv| := by
    have : av * xv + cv - nv = -(nv - (pv + cv)) + -(pv - av * xv) := by ring
    rw [this]; linarith [abs_add_le (-(nv - (pv + cv))) (-(pv - av * xv)),
      abs_neg (nv - (pv + cv)), abs_neg (pv - av * xv)]
  have hmul_rw : |pv - av * xv| ≤ η * (|av| * |xv|) := by rwa [abs_mul] at hmul
  nlinarith [mul_le_mul_of_nonneg_left hpc hη, abs_nonneg cv,
             mul_nonneg hη (abs_nonneg cv)]

/-- One-step magnitude bound: `|next| ≤ (1+η)²·(|acc|·|x| + |c|)`.
    Derived from `horner_step_combined_error` via `magnitude_of_relative_error`. -/
theorem horner_step_magnitude
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x coeff : FiniteFp}
    (step : HornerStep acc x coeff)
    (hnr : HornerStepNormalRange (R := R) acc x coeff step) :
    |step.next.toVal (R := R)| ≤
      (1 + η) ^ 2 * (|(acc.toVal : R)| * |x.toVal| + |coeff.toVal|) := by
  have herr := horner_step_combined_error (R := R) step hnr
  have hexact : |(acc.toVal : R) * x.toVal + coeff.toVal| ≤
      |(acc.toVal : R)| * |x.toVal| + |coeff.toVal| :=
    le_trans (abs_add_le _ _) (by rw [abs_mul])
  have hα : (0 : R) ≤ (1 + η) ^ 2 - 1 := by nlinarith [show (0 : R) ≤ η from by positivity]
  have hmag := magnitude_of_relative_error _ _ _ _ hexact herr
  linarith [show (1 : R) + ((1 + η) ^ 2 - 1) = (1 + η) ^ 2 from by ring]

/-- Extract accumulator magnitudes from a Horner trace: `|acc_k|` at each step. -/
def hornerTraceMags [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {acc final : FiniteFp} →
    HornerTrace x coeffs acc final → ℕ → R
  | _, acc, _, .nil _, _ => |(acc.toVal : R)|
  | _, acc, _, .cons _ _, 0 => |(acc.toVal : R)|
  | _, _, _, .cons _ rest, n + 1 => hornerTraceMags rest n

omit [FloorRing R] in
theorem hornerTraceMags_nonneg [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : HornerTrace x coeffs acc final) (k : ℕ) :
    0 ≤ hornerTraceMags (R := R) trace k := by
  match trace, k with
  | .nil _, _ | .cons _ _, 0 => exact abs_nonneg _
  | .cons _ rest, k + 1 => exact hornerTraceMags_nonneg rest k

omit [IsStrictOrderedRing R] [FloorRing R] in
@[simp] theorem hornerTraceMags_zero [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : HornerTrace x coeffs acc final) :
    hornerTraceMags (R := R) trace 0 = |(acc.toVal : R)| := by
  cases trace <;> rfl

/-- The per-step error bound holds for each step of the trace. -/
theorem horner_trace_step_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x : FiniteFp} {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : HornerTrace x coeffs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < coeffs.length) :
    |(CompensatedHorner.stepErrors trace (R := R))[k]'(by rw [CompensatedHorner.stepErrors_length]; exact hk)| ≤
      ((1 + η) ^ 2 - 1) *
        (|x.toVal (R := R)| * hornerTraceMags trace k +
         |(coeffs[k]'hk).toVal (R := R)|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) step rest, hnr, 0, hk =>
    simp only [HornerTrace.AllNormalRange] at hnr
    simp only [CompensatedHorner.stepErrors, List.getElem_cons_zero, hornerTraceMags]
    have h := horner_step_combined_error (R := R) step hnr.1
    linarith [abs_mul (a.toVal : R) (x.toVal : R)]
  | .cons (coeffs := cs) step rest, hnr, k + 1, hk =>
    simp only [HornerTrace.AllNormalRange] at hnr
    simp only [CompensatedHorner.stepErrors, List.getElem_cons_succ, hornerTraceMags]
    exact horner_trace_step_error rest hnr.2 k (by simp at hk; omega)

/-- The magnitude recurrence holds for each step of the trace. -/
theorem horner_trace_mag_recur
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x : FiniteFp} {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : HornerTrace x coeffs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < coeffs.length) :
    hornerTraceMags trace (k + 1) ≤
      (1 + ((1 + η) ^ 2 - 1)) *
        (|x.toVal (R := R)| * hornerTraceMags trace k +
         |(coeffs[k]'hk).toVal (R := R)|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) step rest, hnr, 0, hk =>
    simp only [HornerTrace.AllNormalRange] at hnr
    show hornerTraceMags rest 0 ≤ _
    rw [hornerTraceMags_zero]
    simp only [List.getElem_cons_zero, hornerTraceMags_zero (R := R)]
    have h := horner_step_magnitude (R := R) step hnr.1
    have : (1 : R) + ((1 + η) ^ 2 - 1) = (1 + η) ^ 2 := by ring
    rw [this]; linarith [abs_mul (a.toVal : R) (x.toVal : R)]
  | .cons (coeffs := cs) step rest, hnr, k + 1, hk =>
    simp only [HornerTrace.AllNormalRange] at hnr
    simp only [hornerTraceMags, List.getElem_cons_succ]
    exact horner_trace_mag_recur rest hnr.2 k (by simp at hk; omega)

set_option maxHeartbeats 800000 in
/-- **Weighted error sum bound** via `weightedErrorSum_le_of_step_errors`.

    Instantiates with `κ = |x|`, `α = (1+η)²-1`, `actual k = |acc_at_step_k|`. -/
theorem horner_weighted_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x : FiniteFp} {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : HornerTrace x coeffs acc final)
    (hnr : trace.AllNormalRange (R := R)) :
    weightedErrorSum |x.toVal (R := R)| (CompensatedHorner.stepErrors trace (R := R)) ≤
      ((1 + η) ^ (2 * coeffs.length) - 1) *
        hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |acc.toVal (R := R)| |x.toVal (R := R)| := by
  have hη : (0 : R) ≤ η := by positivity
  have hα : (0 : R) ≤ (1 + (η : R)) ^ 2 - 1 := by
    nlinarith [one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith) (n := 2)]
  have hgen := weightedErrorSum_le_of_step_errors
    |x.toVal (R := R)| ((1 + (η : R)) ^ 2 - 1)
    (abs_nonneg _) hα
    (CompensatedHorner.stepErrors trace (R := R))
    (coeffs.map (fun c => |c.toVal (R := R)|))
    (hornerTraceMags trace)
    |acc.toVal (R := R)|
    (by rw [CompensatedHorner.stepErrors_length]; simp)
    (fun c hc => by simp at hc; obtain ⟨_, _, rfl⟩ := hc; exact abs_nonneg _)
    (by rw [hornerTraceMags_zero])
    (hornerTraceMags_nonneg (R := R) trace)
    (fun k hk => by
      rw [CompensatedHorner.stepErrors_length] at hk
      simp only [List.getElem_map]
      exact horner_trace_step_error (R := R) trace hnr k hk)
    (fun k hk => by
      rw [CompensatedHorner.stepErrors_length] at hk
      simp only [List.getElem_map]
      exact horner_trace_mag_recur (R := R) trace hnr k hk)
  -- Bridge: (1 + ((1+η)²-1))^n = (1+η)^{2n}
  have hpow : (1 + ((1 + (η : R)) ^ 2 - 1)) ^ (CompensatedHorner.stepErrors trace (R := R)).length =
      (1 + η) ^ (2 * coeffs.length) := by
    rw [show (1 : R) + ((1 + η) ^ 2 - 1) = (1 + η) ^ 2 from by ring,
        ← pow_mul, CompensatedHorner.stepErrors_length]
  linarith [hpow ▸ hgen]

/-- **Horner error bound via AffineFold framework** (`(1+η)^{2n}` form).

    Derives the same `((1+η)^{2n}-1)·p̃(|x|)` bound as `horner_error_bound`
    via `accumulator_error_bound` + `horner_weighted_error_bound`. -/
theorem horner_error_bound_via_affineFold
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : HornerTrace x coeffs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      ((1 + η) ^ (2 * coeffs.length) - 1) *
        hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |init.toVal (R := R)| |x.toVal (R := R)| :=
  accumulator_error_bound _ _ _ _ _
    (CompensatedHorner.comp_horner_exact_decomposition (R := R) trace)
    (horner_weighted_error_bound (R := R) trace hnr)

end HornerErrorBound

/-! ## FMA Horner Error Bound via Generic Framework

Same structure as the Horner case, but with `α = η` (single FMA per step)
instead of `α = (1+η)²-1` (mul + add). The exponent is `n` instead of `2n`. -/

section FMAHornerErrorBound

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

open HornerFMA Horner

/-- Extract accumulator magnitudes from an FMA Horner trace. -/
def fmaTraceMags [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {acc final : FiniteFp} →
    FMATrace x coeffs acc final → ℕ → R
  | _, acc, _, .nil _, _ => |(acc.toVal : R)|
  | _, acc, _, .cons _ _, 0 => |(acc.toVal : R)|
  | _, _, _, .cons _ rest, n + 1 => fmaTraceMags rest n

omit [FloorRing R] in
theorem fmaTraceMags_nonneg [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : FMATrace x coeffs acc final) (k : ℕ) :
    0 ≤ fmaTraceMags (R := R) trace k := by
  match trace, k with
  | .nil _, _ | .cons _ _, 0 => exact abs_nonneg _
  | .cons _ rest, k + 1 => exact fmaTraceMags_nonneg rest k

omit [IsStrictOrderedRing R] [FloorRing R] in
@[simp] theorem fmaTraceMags_zero [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : FMATrace x coeffs acc final) :
    fmaTraceMags (R := R) trace 0 = |(acc.toVal : R)| := by
  cases trace <;> rfl

/-- Step errors for an FMA Horner trace. -/
def fmaHornerStepErrors [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {acc final : FiniteFp} →
    FMATrace x coeffs acc final → List R
  | _, _, _, .nil _ => []
  | _, acc, _, .cons (coeff := coeff) step rest =>
    ((acc.toVal : R) * x.toVal + coeff.toVal - step.next.toVal) ::
      fmaHornerStepErrors rest

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
theorem fmaHornerStepErrors_length [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : FMATrace x coeffs acc final) :
    (fmaHornerStepErrors (R := R) trace).length = coeffs.length := by
  match trace with
  | .nil _ => simp [fmaHornerStepErrors]
  | .cons _ rest => simp [fmaHornerStepErrors, fmaHornerStepErrors_length rest]

omit [FloorRing R] in
/-- FMA exact decomposition: `final + hornerPoly(errors, 0, x) = hornerPoly(coeffs, init, x)`. -/
theorem fma_horner_exact_decomposition [RModeExec] {x : FiniteFp}
    {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : FMATrace x coeffs acc final) :
    (final.toVal : R) +
      hornerPoly (fmaHornerStepErrors (R := R) trace) 0 (x.toVal) =
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (acc.toVal) (x.toVal) := by
  induction trace with
  | nil _ => simp [fmaHornerStepErrors, hornerPoly]
  | @cons acc coeff coeffs final step rest ih =>
    -- Unfold one step on each side
    show (final.toVal : R) + hornerPoly _ (0 * (x.toVal : R) + _) (x.toVal) =
        hornerPoly _ ((acc.toVal : R) * x.toVal + coeff.toVal) (x.toVal)
    -- Use affine on both sides to factor out the per-step error e
    set e := (acc.toVal : R) * x.toVal + coeff.toVal - step.next.toVal
    -- LHS: P(errors, 0 + e) = P(errors, 0) + e * x^n by affine
    rw [show (0 : R) * (x.toVal : R) + e = 0 + e from by ring]
    rw [hornerPoly_affine (fmaHornerStepErrors (R := R) rest) 0 e (x.toVal)]
    -- RHS: P(coeffs, acc*x+c) = P(coeffs, next + e) = P(coeffs, next) + e * x^n
    rw [show (acc.toVal : R) * x.toVal + coeff.toVal = (step.next.toVal : R) + e from by
      simp only [e]; ring]
    rw [hornerPoly_affine (coeffs.map (fun c => c.toVal (R := R))) (step.next.toVal : R) e (x.toVal)]
    -- Now: final + (P_err(0) + e * x^n1) = P_coeff(next) + e * x^n2
    -- where n1, n2 are the respective lengths
    rw [fmaHornerStepErrors_length, List.length_map]
    -- Now: final + P_err(0) + e*x^n = P_coeff(next) + e*x^n, cancel, get ih
    linarith

set_option maxHeartbeats 400000 in
/-- Per-step FMA error bound: `|error_k| ≤ η · (|x| · mag_k + |coeff_k|)`. -/
theorem fma_trace_step_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x : FiniteFp} {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : FMATrace x coeffs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < coeffs.length) :
    |(fmaHornerStepErrors trace (R := R))[k]'(by rw [fmaHornerStepErrors_length]; exact hk)| ≤
      η * (|x.toVal (R := R)| * fmaTraceMags trace k +
           |(coeffs[k]'hk).toVal (R := R)|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (coeff := c) step rest, hnr, 0, hk =>
    simp only [FMATrace.AllNormalRange] at hnr
    simp only [fmaHornerStepErrors, List.getElem_cons_zero, fmaTraceMags]
    have hfma := fpFMA_error_or_zero (R := R) a x c step.next step.hnext hnr.1.fma_normal
    have hη : (0 : R) ≤ η := by positivity
    have hab : |(a.toVal : R) * x.toVal + c.toVal - step.next.toVal| =
        |step.next.toVal - (a.toVal * x.toVal + c.toVal)| := by
      rw [show (a.toVal : R) * x.toVal + c.toVal - step.next.toVal =
          -(step.next.toVal - (a.toVal * x.toVal + c.toVal)) from by ring, abs_neg]
    rw [hab]
    calc |step.next.toVal - ((a.toVal : R) * x.toVal + c.toVal)|
        ≤ η * |(a.toVal : R) * x.toVal + c.toVal| := hfma
      _ ≤ η * (|(a.toVal : R)| * |x.toVal| + |c.toVal|) := by
          apply mul_le_mul_of_nonneg_left _ hη
          exact le_trans (abs_add_le _ _) (by rw [abs_mul])
      _ = η * (|x.toVal| * |(a.toVal : R)| + |c.toVal|) := by rw [mul_comm |(a.toVal : R)|]
  | .cons step rest, hnr, k + 1, hk =>
    simp only [FMATrace.AllNormalRange] at hnr
    simp only [fmaHornerStepErrors, List.getElem_cons_succ, fmaTraceMags]
    exact fma_trace_step_error rest hnr.2 k (by simp at hk; omega)

/-- Per-step FMA magnitude recurrence: `mag_{k+1} ≤ (1+η) · (|x| · mag_k + |coeff_k|)`.
    Derived from `fma_trace_step_error` via `magnitude_of_relative_error`. -/
theorem fma_trace_mag_recur
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x : FiniteFp} {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : FMATrace x coeffs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < coeffs.length) :
    fmaTraceMags trace (k + 1) ≤
      (1 + η) * (|x.toVal (R := R)| * fmaTraceMags trace k +
                  |(coeffs[k]'hk).toVal (R := R)|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (coeff := c) step rest, hnr, 0, hk =>
    simp only [FMATrace.AllNormalRange] at hnr
    show fmaTraceMags rest 0 ≤ _
    rw [fmaTraceMags_zero]
    simp only [List.getElem_cons_zero, fmaTraceMags_zero (R := R)]
    have hfma := fpFMA_error_or_zero (R := R) a x c step.next step.hnext hnr.1.fma_normal
    have hexact : |(a.toVal : R) * x.toVal + c.toVal| ≤
        |x.toVal| * |(a.toVal : R)| + |c.toVal| :=
      le_trans (abs_add_le _ _) (by rw [abs_mul, mul_comm])
    have hη : (0 : R) ≤ η := by positivity
    have herr : |(a.toVal : R) * x.toVal + c.toVal - step.next.toVal| ≤
        η * (|x.toVal| * |(a.toVal : R)| + |c.toVal|) := by
      rw [abs_sub_comm] at hfma; linarith [mul_le_mul_of_nonneg_left hexact hη]
    exact magnitude_of_relative_error _ _ _ _ hexact herr
  | .cons step rest, hnr, k + 1, hk =>
    simp only [FMATrace.AllNormalRange] at hnr
    simp only [fmaTraceMags, List.getElem_cons_succ]
    exact fma_trace_mag_recur rest hnr.2 k (by simp at hk; omega)

/-- Weighted error sum bound for FMA Horner via `weightedErrorSum_le_of_step_errors`. -/
theorem fma_horner_weighted_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x : FiniteFp} {coeffs : List FiniteFp} {acc final : FiniteFp}
    (trace : FMATrace x coeffs acc final)
    (hnr : trace.AllNormalRange (R := R)) :
    weightedErrorSum |x.toVal (R := R)| (fmaHornerStepErrors trace (R := R)) ≤
      ((1 + η) ^ coeffs.length - 1) *
        hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |acc.toVal (R := R)| |x.toVal (R := R)| := by
  have hη : (0 : R) ≤ η := by positivity
  have h := weightedErrorSum_le_of_step_errors
    |x.toVal (R := R)| (η : R) (abs_nonneg _) hη
    (fmaHornerStepErrors trace (R := R))
    (coeffs.map (fun c => |c.toVal (R := R)|))
    (fmaTraceMags trace)
    |acc.toVal (R := R)|
    (by rw [fmaHornerStepErrors_length]; simp)
    (fun c hc => by simp at hc; obtain ⟨_, _, rfl⟩ := hc; exact abs_nonneg _)
    (by rw [fmaTraceMags_zero])
    (fmaTraceMags_nonneg (R := R) trace)
    (fun k hk => by
      rw [fmaHornerStepErrors_length] at hk
      simp only [List.getElem_map]
      exact fma_trace_step_error (R := R) trace hnr k hk)
    (fun k hk => by
      rw [fmaHornerStepErrors_length] at hk
      simp only [List.getElem_map]
      exact fma_trace_mag_recur (R := R) trace hnr k hk)
  rw [fmaHornerStepErrors_length] at h; exact h

/-- **FMA Horner error bound via generic framework** (`(1+η)^n` form).

    Derives the same `((1+η)^n - 1) · p̃(|x|)` bound as `fma_horner_error_bound`
    via `accumulator_error_bound` + `fma_horner_weighted_error_bound`. -/
theorem fma_horner_error_bound_via_affineFold
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : FMATrace x coeffs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      ((1 + η) ^ coeffs.length - 1) *
        hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |init.toVal (R := R)| |x.toVal (R := R)| :=
  accumulator_error_bound _ _ _ _ _
    (fma_horner_exact_decomposition (R := R) trace)
    (fma_horner_weighted_error_bound (R := R) trace hnr)

end FMAHornerErrorBound

/-! ## Dot Product Error Bound via Framework

The sequential dot product `sₖ = fl(s_{k-1} + fl(xₖ·yₖ))` is an accumulator fold
with `κ = 1` (identity linear map) and `α = (1+η)²-1` (two roundings per step).
The framework gives `((1+η)^{2n}-1) · (|init| + Σ|xᵢyᵢ|)`, which is looser than
the manually-proved `((1+η)^n-1)` bound in `DotProduct.lean` (which exploits the
zero-init trick and tracks mul/add errors separately). This section validates
that the generic framework applies to κ=1 algorithms. -/

section DotProductErrorBound

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Extract per-step rounding errors from a dot product trace.
    `eₖ = (s_{k-1} + xₖ·yₖ) - sₖ` (exact minus computed). -/
def dpStepErrors [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} → {acc final : FiniteFp} →
    DPTrace pairs acc final → List R
  | _, _, _, .nil _ => []
  | _, _, _, .cons (acc := acc) (x := x) (y := y) step rest =>
    ((acc.toVal : R) + x.toVal * y.toVal - step.next.toVal) :: dpStepErrors rest

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
theorem dpStepErrors_length [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final) :
    (dpStepErrors (R := R) trace).length = pairs.length := by
  induction trace with
  | nil => simp [dpStepErrors]
  | cons _ _ ih => simp [dpStepErrors, ih]

omit [FloorRing R] in
/-- Exact decomposition for dot product: `final + hornerPoly(errors, 0, 1) = init + Σ(xᵢyᵢ)`. -/
theorem dp_exact_decomposition [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DPTrace pairs init final) :
    (final.toVal : R) +
      hornerPoly (dpStepErrors trace (R := R)) 0 1 =
      hornerPoly (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)) (init.toVal) 1 := by
  induction trace with
  | nil => simp [dpStepErrors, hornerPoly]
  | @cons acc x y pairs final step rest ih =>
    simp only [dpStepErrors, hornerPoly, List.map_cons, mul_one, zero_add]
    set e := (acc.toVal : R) + x.toVal * y.toVal - step.next.toVal
    have haffine_err := hornerPoly_affine (dpStepErrors (R := R) rest) 0 e 1
    simp only [zero_add, one_pow, mul_one] at haffine_err
    have hnext_sub : (step.next.toVal : R) =
        (acc.toVal : R) + x.toVal * y.toVal + -e := by simp only [e]; ring
    rw [hnext_sub] at ih
    have haffine_main := hornerPoly_affine
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal))
      ((acc.toVal : R) + x.toVal * y.toVal)
      (-e) 1
    simp only [one_pow, mul_one] at haffine_main
    linarith

/-- Per-step combined FP error for one dot product step:
    `|acc + x·y - next| ≤ ((1+η)²-1) · (|acc| + |x·y|)`. -/
theorem dp_step_combined_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x y : FiniteFp} (step : DPStep acc x y)
    (hnr : DPStepNormalRange (R := R) acc x y step) :
    |(acc.toVal : R) + x.toVal * y.toVal - step.next.toVal| ≤
      ((1 + η) ^ 2 - 1) * (|(acc.toVal : R)| + |x.toVal * y.toVal|) := by
  set av := (acc.toVal : R); set xv := (x.toVal : R); set yv := (y.toVal : R)
  set pv := (step.prod.toVal : R); set nv := (step.next.toVal : R)
  have hη : (0 : R) ≤ η := by positivity
  have hmul := KahanSum.fpMul_error_or_zero (R := R) x y step.prod step.hprod hnr.mul_normal
  have hadd := KahanSum.fpAdd_error_or_zero (R := R) acc step.prod step.next step.hnext
    hnr.add_normal
  have hprod : |pv| ≤ (1 + η) * |xv * yv| := by
    have := le_trans (abs_sub_abs_le_abs_sub pv (xv * yv)) hmul
    linarith
  have hap : |av + pv| ≤ |av| + (1 + η) * |xv * yv| :=
    le_trans (abs_add_le av pv) (by linarith)
  have htri : |av + xv * yv - nv| ≤ |nv - (av + pv)| + |pv - xv * yv| := by
    have : av + xv * yv - nv = -(nv - (av + pv)) + -(pv - xv * yv) := by ring
    rw [this]; linarith [abs_add_le (-(nv - (av + pv))) (-(pv - xv * yv)),
      abs_neg (nv - (av + pv)), abs_neg (pv - xv * yv)]
  nlinarith [htri, hadd, hmul, mul_le_mul_of_nonneg_left hap hη,
             abs_nonneg av, abs_nonneg (xv * yv),
             mul_nonneg hη (abs_nonneg av),
             mul_nonneg hη (abs_nonneg (xv * yv))]

/-- One-step magnitude bound: `|next| ≤ (1+η)² · (|acc| + |x·y|)`. -/
theorem dp_step_magnitude
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x y : FiniteFp} (step : DPStep acc x y)
    (hnr : DPStepNormalRange (R := R) acc x y step) :
    |step.next.toVal (R := R)| ≤
      (1 + η) ^ 2 * (|(acc.toVal : R)| + |x.toVal * y.toVal|) := by
  have herr := dp_step_combined_error (R := R) step hnr
  have hexact : |(acc.toVal : R) + x.toVal * y.toVal| ≤
      |(acc.toVal : R)| + |x.toVal * y.toVal| := abs_add_le _ _
  have hα : (0 : R) ≤ (1 + η) ^ 2 - 1 := by nlinarith [show (0 : R) ≤ η from by positivity]
  have hmag := magnitude_of_relative_error _ _ _ _ hexact herr
  linarith [show (1 : R) + ((1 + η) ^ 2 - 1) = (1 + η) ^ 2 from by ring]

/-- Extract accumulator magnitudes from a dot product trace. -/
def dpTraceMags [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} → {acc final : FiniteFp} →
    DPTrace pairs acc final → ℕ → R
  | _, acc, _, .nil _, _ => |(acc.toVal : R)|
  | _, acc, _, .cons _ _, 0 => |(acc.toVal : R)|
  | _, _, _, .cons _ rest, n + 1 => dpTraceMags rest n

omit [FloorRing R] in
theorem dpTraceMags_nonneg [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final) (k : ℕ) :
    0 ≤ dpTraceMags (R := R) trace k := by
  match trace, k with
  | .nil _, _ | .cons _ _, 0 => exact abs_nonneg _
  | .cons _ rest, k + 1 => exact dpTraceMags_nonneg rest k

omit [IsStrictOrderedRing R] [FloorRing R] in
@[simp] theorem dpTraceMags_zero [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final) :
    dpTraceMags (R := R) trace 0 = |(acc.toVal : R)| := by
  cases trace <;> rfl

/-- Per-step error bound for each step of the dot product trace. -/
theorem dp_trace_step_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < pairs.length) :
    |(dpStepErrors trace (R := R))[k]'(by rw [dpStepErrors_length]; exact hk)| ≤
      ((1 + η) ^ 2 - 1) *
        (1 * dpTraceMags trace k +
         |(pairs[k]'hk).1.toVal (R := R) * (pairs[k]'hk).2.toVal|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (x := x) (y := y) step rest, hnr, 0, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    simp only [dpStepErrors, List.getElem_cons_zero, dpTraceMags, one_mul]
    exact dp_step_combined_error (R := R) step hnr.1
  | .cons step rest, hnr, k + 1, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    simp only [dpStepErrors, List.getElem_cons_succ, dpTraceMags]
    exact dp_trace_step_error rest hnr.2 k (by simp at hk; omega)

/-- Magnitude recurrence for each step of the dot product trace. -/
theorem dp_trace_mag_recur
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < pairs.length) :
    dpTraceMags trace (k + 1) ≤
      (1 + ((1 + η) ^ 2 - 1)) *
        (1 * dpTraceMags trace k +
         |(pairs[k]'hk).1.toVal (R := R) * (pairs[k]'hk).2.toVal|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (x := x) (y := y) step rest, hnr, 0, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    show dpTraceMags rest 0 ≤ _
    rw [dpTraceMags_zero]
    simp only [List.getElem_cons_zero, dpTraceMags_zero (R := R), one_mul]
    have h := dp_step_magnitude (R := R) step hnr.1
    linarith [show (1 : R) + ((1 + η) ^ 2 - 1) = (1 + η) ^ 2 from by ring]
  | .cons step rest, hnr, k + 1, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    simp only [dpTraceMags, List.getElem_cons_succ]
    exact dp_trace_mag_recur rest hnr.2 k (by simp at hk; omega)

set_option maxHeartbeats 800000 in
/-- **Weighted error sum bound for dot product** via `weightedErrorSum_le_of_step_errors`.
    Instantiates with `κ = 1`, `α = (1+η)²-1`. -/
theorem dp_weighted_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R)) :
    weightedErrorSum 1 (dpStepErrors trace (R := R)) ≤
      ((1 + η) ^ (2 * pairs.length) - 1) *
        hornerPoly (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|))
          |acc.toVal (R := R)| 1 := by
  have hη : (0 : R) ≤ η := by positivity
  have hα : (0 : R) ≤ (1 + (η : R)) ^ 2 - 1 := by
    nlinarith [one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith) (n := 2)]
  have hgen := weightedErrorSum_le_of_step_errors
    1 ((1 + (η : R)) ^ 2 - 1)
    zero_le_one hα
    (dpStepErrors trace (R := R))
    (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|))
    (dpTraceMags trace)
    |acc.toVal (R := R)|
    (by rw [dpStepErrors_length]; simp)
    (fun c hc => by simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; positivity)
    (by rw [dpTraceMags_zero])
    (dpTraceMags_nonneg (R := R) trace)
    (fun k hk => by
      rw [dpStepErrors_length] at hk
      simp only [List.getElem_map]
      exact dp_trace_step_error (R := R) trace hnr k hk)
    (fun k hk => by
      rw [dpStepErrors_length] at hk
      simp only [List.getElem_map]
      exact dp_trace_mag_recur (R := R) trace hnr k hk)
  have hpow : (1 + ((1 + (η : R)) ^ 2 - 1)) ^ (dpStepErrors trace (R := R)).length =
      (1 + η) ^ (2 * pairs.length) := by
    rw [show (1 : R) + ((1 + η) ^ 2 - 1) = (1 + η) ^ 2 from by ring,
        ← pow_mul, dpStepErrors_length]
  linarith [hpow ▸ hgen]

/-- **Dot product error bound via AffineFold framework** (`(1+η)^{2n}` form).

    `|final - (init + Σxᵢyᵢ)| ≤ ((1+η)^{2n}-1) · (|init| + Σ|xᵢyᵢ|)`

    Note: this is looser than the manually-proved `((1+η)^n-1)` bound in
    `DotProduct.dp_error_bound`, which exploits zero-init and separate mul/add
    tracking. This bound applies to arbitrary initial accumulators. -/
theorem dp_error_bound_via_affineFold
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DPTrace pairs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      hornerPoly (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)) (init.toVal) 1| ≤
      ((1 + η) ^ (2 * pairs.length) - 1) *
        hornerPoly (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|))
          |init.toVal (R := R)| 1 := by
  refine accumulator_error_bound _ _ (1 : R) _ _
    (dp_exact_decomposition (R := R) trace) ?_
  simp only [abs_one]
  exact dp_weighted_error_bound (R := R) trace hnr

end DotProductErrorBound

/-! ## Tight Dot Product Error Bound via Four-Parameter Framework

The four-parameter model with `α_acc = η, α_off = (1+η)²-1, β_acc = η, β_off = (1+η)²-1`
gives a two-term bound with exponent `n` instead of `2n`:

  `geomBound(η, η, n) · |init| + ((1+η)²-1 + η·(1+η)²·geomBound(1, η, n)) · Σ|xᵢyᵢ|`

With zero init, the init term vanishes. The coefficient on `Σ|xᵢyᵢ|` is
`O(2η + η·n·η) = O(η)` for small η, comparable to the manual proof's `((1+η)^n-1)`. -/

section DotProductTightBound

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Per-step split error bound: `|error_k| ≤ η·|acc_k| + ((1+η)²-1)·|xy_k|`.
    The accumulator contributes only `η` (from the add), while the offset
    contributes `(1+η)²-1 ≈ 2η` (from mul + add). -/
theorem dp_step_split_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x y : FiniteFp} (step : DPStep acc x y)
    (hnr : DPStepNormalRange (R := R) acc x y step) :
    |(acc.toVal : R) + x.toVal * y.toVal - step.next.toVal| ≤
      η * (1 * |(acc.toVal : R)|) + ((1 + η) ^ 2 - 1) * |x.toVal * y.toVal| := by
  set av := (acc.toVal : R); set xv := (x.toVal : R); set yv := (y.toVal : R)
  set pv := (step.prod.toVal : R); set nv := (step.next.toVal : R)
  have hη : (0 : R) ≤ η := by positivity
  have hmul := KahanSum.fpMul_error_or_zero (R := R) x y step.prod step.hprod hnr.mul_normal
  have hadd := KahanSum.fpAdd_error_or_zero (R := R) acc step.prod step.next step.hnext
    hnr.add_normal
  -- |prod - xy| ≤ η|xy|
  have hmul_bound : |pv - xv * yv| ≤ η * |xv * yv| := hmul
  -- |prod| ≤ (1+η)|xy|
  have hprod_bound : |pv| ≤ (1 + η) * |xv * yv| := by
    linarith [le_trans (abs_sub_abs_le_abs_sub pv (xv * yv)) hmul_bound]
  -- |acc + prod| ≤ |acc| + (1+η)|xy|
  have hap : |av + pv| ≤ |av| + (1 + η) * |xv * yv| :=
    le_trans (abs_add_le av pv) (by linarith)
  -- |next - (acc + prod)| ≤ η · (|acc| + (1+η)|xy|)
  have hadd_bound : |nv - (av + pv)| ≤ η * (|av| + (1 + η) * |xv * yv|) :=
    le_trans hadd (mul_le_mul_of_nonneg_left hap hη)
  -- Triangle: |acc + xy - next| ≤ |next - (acc+prod)| + |prod - xy|
  have htri : |av + xv * yv - nv| ≤ |nv - (av + pv)| + |pv - xv * yv| := by
    have : av + xv * yv - nv = -(nv - (av + pv)) + -(pv - xv * yv) := by ring
    rw [this]; linarith [abs_add_le (-(nv - (av + pv))) (-(pv - xv * yv)),
      abs_neg (nv - (av + pv)), abs_neg (pv - xv * yv)]
  -- Combine: η|acc| + η(1+η)|xy| + η|xy| = η|acc| + (2η+η²)|xy| = η|acc| + ((1+η)²-1)|xy|
  nlinarith [abs_nonneg av, abs_nonneg (xv * yv),
             mul_nonneg hη (abs_nonneg av), mul_nonneg hη (abs_nonneg (xv * yv))]

/-- Per-step split magnitude: `|next| ≤ (1+η)·|acc| + (1+η)²·|xy|`.
    The accumulator grows by `(1+η)` (add only), while the offset enters
    with factor `(1+η)²` (mul then add). -/
theorem dp_step_split_magnitude
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x y : FiniteFp} (step : DPStep acc x y)
    (hnr : DPStepNormalRange (R := R) acc x y step) :
    |step.next.toVal (R := R)| ≤
      (1 + η) * (1 * |(acc.toVal : R)|) + (1 + ((1 + η) ^ 2 - 1)) * |x.toVal * y.toVal| := by
  -- (1 + ((1+η)²-1)) = (1+η)²
  have h1βoff : (1 : R) + ((1 + η) ^ 2 - 1) = (1 + η) ^ 2 := by ring
  rw [h1βoff, one_mul]
  set av := (acc.toVal : R); set xv := (x.toVal : R); set yv := (y.toVal : R)
  set nv := (step.next.toVal : R)
  have hη : (0 : R) ≤ η := by positivity
  have herr := dp_step_split_error (R := R) step hnr
  simp only [one_mul] at herr
  -- |nv| ≤ |av + xv*yv| + |error|
  have htri : |nv| - |av + xv * yv| ≤ |nv - (av + xv * yv)| :=
    abs_sub_abs_le_abs_sub nv (av + xv * yv)
  -- |error| = |av + xv*yv - nv|
  have herr_sym : |nv - (av + xv * yv)| = |av + xv * yv - nv| := abs_sub_comm _ _
  have hsum : |av + xv * yv| ≤ |av| + |xv * yv| := abs_add_le _ _
  have h2sq : (1 + η : R) ^ 2 = 1 + 2 * η + η ^ 2 := by ring
  nlinarith [abs_nonneg av, abs_nonneg (xv * yv), abs_nonneg nv]

/-- Per-step split error for trace index k. -/
theorem dp_trace_split_step_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < pairs.length) :
    |(dpStepErrors trace (R := R))[k]'(by rw [dpStepErrors_length]; exact hk)| ≤
      η * (1 * dpTraceMags trace k) +
      ((1 + η) ^ 2 - 1) * |(pairs[k]'hk).1.toVal (R := R) * (pairs[k]'hk).2.toVal| := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (x := x) (y := y) step rest, hnr, 0, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    simp only [dpStepErrors, List.getElem_cons_zero, dpTraceMags]
    exact dp_step_split_error (R := R) step hnr.1
  | .cons step rest, hnr, k + 1, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    simp only [dpStepErrors, List.getElem_cons_succ, dpTraceMags]
    exact dp_trace_split_step_error rest hnr.2 k (by simp at hk; omega)

/-- Per-step split magnitude recurrence for trace index k. -/
theorem dp_trace_split_mag_recur
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : DPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < pairs.length) :
    dpTraceMags trace (k + 1) ≤
      (1 + η) * (1 * dpTraceMags trace k) +
      (1 + ((1 + η) ^ 2 - 1)) * |(pairs[k]'hk).1.toVal (R := R) * (pairs[k]'hk).2.toVal| := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (x := x) (y := y) step rest, hnr, 0, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    show dpTraceMags rest 0 ≤ _
    rw [dpTraceMags_zero]
    simp only [List.getElem_cons_zero, dpTraceMags_zero (R := R)]
    exact dp_step_split_magnitude (R := R) step hnr.1
  | .cons step rest, hnr, k + 1, hk =>
    simp only [DPTrace.AllNormalRange] at hnr
    simp only [dpTraceMags, List.getElem_cons_succ]
    exact dp_trace_split_mag_recur rest hnr.2 k (by simp at hk; omega)

/-- **Tight dot product error bound via four-parameter framework** (two-term output).

    Uses `α_acc = η, α_off = (1+η)²-1, β_acc = η, β_off = (1+η)²-1` to get
    exponent `n` instead of `2n`. The init term grows as `geomBound(η, η, n)·|init|`
    and the offset term captures the per-product error. -/
theorem dp_error_bound_tight
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DPTrace pairs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      hornerPoly (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)) (init.toVal) 1| ≤
      GeomBound.geomBound η η pairs.length * 1 ^ pairs.length * |init.toVal (R := R)| +
      (((1 + η) ^ 2 - 1) + η * (1 + ((1 + η) ^ 2 - 1)) *
        GeomBound.geomBound 1 η pairs.length) *
        hornerPoly (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)) 0 1 := by
  -- Use accumulator_error_bound with the decomposition
  have hdecomp := dp_exact_decomposition (R := R) trace
  -- Apply the four-parameter framework
  have hwes := GeneralAccum.weightedErrorSum_le_of_general_step
    (1 : R) η ((1 + η) ^ 2 - 1) η ((1 + η) ^ 2 - 1)
    zero_le_one (by positivity) (by nlinarith [show (0:R) ≤ η from by positivity])
    (by positivity) (by nlinarith [show (0:R) ≤ η from by positivity])
    (dpStepErrors trace (R := R))
    (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|))
    (dpTraceMags trace)
    (by rw [dpStepErrors_length]; simp)
    (fun c hc => by simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; positivity)
    (dpTraceMags_nonneg (R := R) trace)
    (fun k hk => by
      rw [dpStepErrors_length] at hk
      simp only [List.getElem_map]
      exact dp_trace_split_step_error (R := R) trace hnr k hk)
    (fun k hk => by
      rw [dpStepErrors_length] at hk
      simp only [List.getElem_map]
      exact dp_trace_split_mag_recur (R := R) trace hnr k hk)
  -- Bridge: |final - exact| ≤ wes ≤ bound
  have herr : final.toVal (R := R) - hornerPoly (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)) (init.toVal) 1 =
      -(hornerPoly (dpStepErrors trace (R := R)) 0 1) := by linarith
  rw [herr, abs_neg]
  have hpi := hornerPoly_abs_le_per_index (1 : R) (dpStepErrors trace (R := R))
  rw [← weightedErrorSum_eq_hornerPoly] at hpi
  simp only [abs_one] at hpi
  -- Bridge: dpStepErrors length = pairs.length, dpTraceMags 0 = |init|
  rw [dpStepErrors_length] at hwes
  rw [dpTraceMags_zero] at hwes
  linarith

end DotProductTightBound

/-! ## FMA Dot Product Error Bound via Framework

The FMA dot product `sₖ = fma(xₖ, yₖ, s_{k-1})` is an accumulator fold with
`κ = 1` and `α = η` (single rounding per step). The framework gives
`((1+η)^n-1) · (|init| + Σ|xᵢyᵢ|)`, which matches the manually-proved bound
in `DotProductFMA.lean` (with zero init). -/

section FMADotProductErrorBound

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Extract per-step rounding errors from an FMA dot product trace.
    `eₖ = (xₖ·yₖ + s_{k-1}) - sₖ`. -/
def fmaDPStepErrors [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} → {acc final : FiniteFp} →
    FMADPTrace pairs acc final → List R
  | _, _, _, .nil _ => []
  | _, _, _, .cons (acc := acc) (x := x) (y := y) step rest =>
    ((acc.toVal : R) + x.toVal * y.toVal - step.next.toVal) :: fmaDPStepErrors rest

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
theorem fmaDPStepErrors_length [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : FMADPTrace pairs acc final) :
    (fmaDPStepErrors (R := R) trace).length = pairs.length := by
  induction trace with
  | nil => simp [fmaDPStepErrors]
  | cons _ _ ih => simp [fmaDPStepErrors, ih]

omit [FloorRing R] in
/-- Exact decomposition for FMA dot product. -/
theorem fma_dp_exact_decomposition [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : FMADPTrace pairs init final) :
    (final.toVal : R) +
      hornerPoly (fmaDPStepErrors trace (R := R)) 0 1 =
      hornerPoly (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)) (init.toVal) 1 := by
  induction trace with
  | nil => simp [fmaDPStepErrors, hornerPoly]
  | @cons acc x y pairs final step rest ih =>
    simp only [fmaDPStepErrors, hornerPoly, List.map_cons, mul_one, zero_add]
    set e := (acc.toVal : R) + x.toVal * y.toVal - step.next.toVal
    have haffine_err := hornerPoly_affine (fmaDPStepErrors (R := R) rest) 0 e 1
    simp only [zero_add, one_pow, mul_one] at haffine_err
    have hnext_sub : (step.next.toVal : R) =
        (acc.toVal : R) + x.toVal * y.toVal + -e := by simp only [e]; ring
    rw [hnext_sub] at ih
    have haffine_main := hornerPoly_affine
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal))
      ((acc.toVal : R) + x.toVal * y.toVal)
      (-e) 1
    simp only [one_pow, mul_one] at haffine_main
    linarith

/-- Per-step FMA error: `|acc + x·y - next| ≤ η · (|acc| + |x·y|)`. -/
theorem fma_dp_step_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x y : FiniteFp} (step : FMADPStep acc x y)
    (hnr : FMADPStepNormalRange (R := R) acc x y step) :
    |(acc.toVal : R) + x.toVal * y.toVal - step.next.toVal| ≤
      η * (|(acc.toVal : R)| + |x.toVal * y.toVal|) := by
  have hfma := HornerFMA.fpFMA_error_or_zero (R := R) x y acc step.next step.hnext
    hnr.fma_normal
  have hη : (0 : R) ≤ η := by positivity
  calc |(acc.toVal : R) + x.toVal * y.toVal - step.next.toVal|
      = |step.next.toVal - (x.toVal * y.toVal + acc.toVal)| := by
        rw [abs_sub_comm]; ring_nf
    _ ≤ η * |x.toVal * y.toVal + acc.toVal| := hfma
    _ ≤ η * (|x.toVal * y.toVal| + |acc.toVal|) := by
        apply mul_le_mul_of_nonneg_left (abs_add_le _ _) hη
    _ = η * (|(acc.toVal : R)| + |x.toVal * y.toVal|) := by ring

/-- One-step magnitude: `|next| ≤ (1+η) · (|acc| + |x·y|)`. -/
theorem fma_dp_step_magnitude
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {acc x y : FiniteFp} (step : FMADPStep acc x y)
    (hnr : FMADPStepNormalRange (R := R) acc x y step) :
    |step.next.toVal (R := R)| ≤
      (1 + η) * (|(acc.toVal : R)| + |x.toVal * y.toVal|) := by
  have herr := fma_dp_step_error (R := R) step hnr
  have hexact : |(acc.toVal : R) + x.toVal * y.toVal| ≤
      |(acc.toVal : R)| + |x.toVal * y.toVal| := abs_add_le _ _
  have hα : (0 : R) ≤ η := by positivity
  have hmag := magnitude_of_relative_error _ _ _ _ hexact herr
  linarith

/-- Extract accumulator magnitudes from an FMA dot product trace. -/
def fmaDPTraceMags [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} → {acc final : FiniteFp} →
    FMADPTrace pairs acc final → ℕ → R
  | _, acc, _, .nil _, _ => |(acc.toVal : R)|
  | _, acc, _, .cons _ _, 0 => |(acc.toVal : R)|
  | _, _, _, .cons _ rest, n + 1 => fmaDPTraceMags rest n

omit [FloorRing R] in
theorem fmaDPTraceMags_nonneg [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : FMADPTrace pairs acc final) (k : ℕ) :
    0 ≤ fmaDPTraceMags (R := R) trace k := by
  match trace, k with
  | .nil _, _ | .cons _ _, 0 => exact abs_nonneg _
  | .cons _ rest, k + 1 => exact fmaDPTraceMags_nonneg rest k

omit [IsStrictOrderedRing R] [FloorRing R] in
@[simp] theorem fmaDPTraceMags_zero [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : FMADPTrace pairs acc final) :
    fmaDPTraceMags (R := R) trace 0 = |(acc.toVal : R)| := by
  cases trace <;> rfl

/-- Per-step error bound for each step of the FMA dot product trace. -/
theorem fma_dp_trace_step_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : FMADPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < pairs.length) :
    |(fmaDPStepErrors trace (R := R))[k]'(by rw [fmaDPStepErrors_length]; exact hk)| ≤
      η *
        (1 * fmaDPTraceMags trace k +
         |(pairs[k]'hk).1.toVal (R := R) * (pairs[k]'hk).2.toVal|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (x := x) (y := y) step rest, hnr, 0, hk =>
    simp only [FMADPTrace.AllNormalRange] at hnr
    simp only [fmaDPStepErrors, List.getElem_cons_zero, fmaDPTraceMags, one_mul]
    exact fma_dp_step_error (R := R) step hnr.1
  | .cons step rest, hnr, k + 1, hk =>
    simp only [FMADPTrace.AllNormalRange] at hnr
    simp only [fmaDPStepErrors, List.getElem_cons_succ, fmaDPTraceMags]
    exact fma_dp_trace_step_error rest hnr.2 k (by simp at hk; omega)

/-- Magnitude recurrence for each step of the FMA dot product trace. -/
theorem fma_dp_trace_mag_recur
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : FMADPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R))
    (k : ℕ) (hk : k < pairs.length) :
    fmaDPTraceMags trace (k + 1) ≤
      (1 + η) *
        (1 * fmaDPTraceMags trace k +
         |(pairs[k]'hk).1.toVal (R := R) * (pairs[k]'hk).2.toVal|) := by
  match trace, hnr, k, hk with
  | .cons (acc := a) (x := x) (y := y) step rest, hnr, 0, hk =>
    simp only [FMADPTrace.AllNormalRange] at hnr
    show fmaDPTraceMags rest 0 ≤ _
    rw [fmaDPTraceMags_zero]
    simp only [List.getElem_cons_zero, fmaDPTraceMags_zero (R := R), one_mul]
    exact fma_dp_step_magnitude (R := R) step hnr.1
  | .cons step rest, hnr, k + 1, hk =>
    simp only [FMADPTrace.AllNormalRange] at hnr
    simp only [fmaDPTraceMags, List.getElem_cons_succ]
    exact fma_dp_trace_mag_recur rest hnr.2 k (by simp at hk; omega)

set_option maxHeartbeats 800000 in
/-- **Weighted error sum bound for FMA dot product** via `weightedErrorSum_le_of_step_errors`.
    Instantiates with `κ = 1`, `α = η`. -/
theorem fma_dp_weighted_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {acc final : FiniteFp}
    (trace : FMADPTrace pairs acc final)
    (hnr : trace.AllNormalRange (R := R)) :
    weightedErrorSum 1 (fmaDPStepErrors trace (R := R)) ≤
      ((1 + η) ^ pairs.length - 1) *
        hornerPoly (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|))
          |acc.toVal (R := R)| 1 := by
  have hη : (0 : R) ≤ η := by positivity
  have hgen := weightedErrorSum_le_of_step_errors
    1 (η : R)
    zero_le_one hη
    (fmaDPStepErrors trace (R := R))
    (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|))
    (fmaDPTraceMags trace)
    |acc.toVal (R := R)|
    (by rw [fmaDPStepErrors_length]; simp)
    (fun c hc => by simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; positivity)
    (by rw [fmaDPTraceMags_zero])
    (fmaDPTraceMags_nonneg (R := R) trace)
    (fun k hk => by
      rw [fmaDPStepErrors_length] at hk
      simp only [List.getElem_map]
      exact fma_dp_trace_step_error (R := R) trace hnr k hk)
    (fun k hk => by
      rw [fmaDPStepErrors_length] at hk
      simp only [List.getElem_map]
      exact fma_dp_trace_mag_recur (R := R) trace hnr k hk)
  rw [fmaDPStepErrors_length] at hgen
  linarith

/-- **FMA dot product error bound via AffineFold framework** (`(1+η)^n` form).

    `|final - (init + Σxᵢyᵢ)| ≤ ((1+η)^n-1) · (|init| + Σ|xᵢyᵢ|)`

    With zero init, this matches `DotProductFMA.fma_dp_error_bound`. -/
theorem fma_dp_error_bound_via_affineFold
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : FMADPTrace pairs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      hornerPoly (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)) (init.toVal) 1| ≤
      ((1 + η) ^ pairs.length - 1) *
        hornerPoly (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|))
          |init.toVal (R := R)| 1 := by
  refine accumulator_error_bound _ _ (1 : R) _ _
    (fma_dp_exact_decomposition (R := R) trace) ?_
  simp only [abs_one]
  exact fma_dp_weighted_error_bound (R := R) trace hnr

end FMADotProductErrorBound

end AffineFoldInstances
