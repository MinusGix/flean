import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Abel
import Flean.FloatFormat

/-!
# Affine Fold: Generic Error Propagation for Iterated Affine Maps

Many floating-point evaluation algorithms (Horner, Clenshaw, de Casteljau, jet evaluation)
share a common structure: iteratively apply an **affine map** `s ↦ L(s) + v` where
`L` is linear and `v` is an offset (coefficient).

This file provides the generic framework:

- `affineFold L vs s`: fold the affine map over offsets `vs`, starting from state `s`
- `affineProp L n e`: propagate perturbation `e` through `n` applications of `L`
- `affineFold_affine`: **the core theorem** — `fold(s + e) = fold(s) + prop(n, e)`
- `affineFold_exact_decomposition`: computed + propagated errors = exact

## Instances

- **Horner** (`S = R`): `L(a) = x·a`, propagation = `e·x^n`
- **Clenshaw** (`S = R × R`): `L(a,b) = (w·a-b, a)`, propagation = `clenshawProp`
- **Jet Horner** (`S = R × R`): `L(p,p') = (x·p, x·p'+p)`, for value + derivative
-/

namespace AffineFold

variable {S : Type*} [AddCommGroup S]

/-! ## Definitions -/

/-- Fold an affine map `s ↦ L(s) + v` over a list of offsets. -/
def affineFold (L : S → S) : List S → S → S
  | [], s => s
  | v :: vs, s => affineFold L vs (L s + v)

/-- Propagate a perturbation through `n` applications of the linear part `L`. -/
def affineProp (L : S → S) : ℕ → S → S
  | 0, e => e
  | n + 1, e => affineProp L n (L e)

/-! ## Core Theorems -/

/-- **Affine fold theorem**: perturbing the initial state by `e` shifts the
    final state by `affineProp L n e` — the perturbation propagated through
    the linear part only.

    This unifies `hornerPoly_affine` (1D) and `clenshawExact_affine` (2D). -/
theorem affineFold_affine (L : S → S) (hL : ∀ a b, L (a + b) = L a + L b)
    (vs : List S) (s e : S) :
    affineFold L vs (s + e) = affineFold L vs s + affineProp L vs.length e := by
  induction vs generalizing s e with
  | nil => simp [affineFold, affineProp]
  | cons v vs ih =>
    simp only [affineFold, affineProp, List.length_cons]
    rw [hL, show L s + L e + v = (L s + v) + L e from by abel]
    exact ih _ _

/-- Propagation of zero is zero. -/
theorem affineProp_zero (L : S → S) (hL : ∀ a b, L (a + b) = L a + L b)
    (n : ℕ) : affineProp L n 0 = 0 := by
  induction n with
  | zero => simp [affineProp]
  | succ n ih =>
    simp only [affineProp]
    have hL0 : L 0 = 0 := by
      have h := hL 0 0
      rw [add_zero] at h
      have := congr_arg (· - L 0) h
      simp only [sub_self, add_sub_cancel_right] at this
      exact this.symm
    rw [hL0, ih]

/-- Propagation respects negation (linearity). -/
theorem affineProp_neg (L : S → S) (hL : ∀ a b, L (a + b) = L a + L b)
    (n : ℕ) (e : S) : affineProp L n (-e) = -affineProp L n e := by
  induction n generalizing e with
  | zero => simp [affineProp]
  | succ n ih =>
    simp only [affineProp]
    have hLneg : L (-e) = -L e := by
      have hL0 : L 0 = 0 := by
        have h := hL 0 0; rw [add_zero] at h
        have := congr_arg (· - L 0) h
        simp only [sub_self, add_sub_cancel_right] at this
        exact this.symm
      have h := hL e (-e)
      rw [add_neg_cancel, hL0] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    rw [hLneg, ih]

/-- Propagation respects addition (full linearity). -/
theorem affineProp_add (L : S → S) (hL : ∀ a b, L (a + b) = L a + L b)
    (n : ℕ) (e₁ e₂ : S) :
    affineProp L n (e₁ + e₂) = affineProp L n e₁ + affineProp L n e₂ := by
  induction n generalizing e₁ e₂ with
  | zero => simp [affineProp]
  | succ n ih =>
    simp only [affineProp]
    rw [hL, ih]

/-! ## Exact Decomposition -/

/-- **Generic exact decomposition**: if `computed_k = exact_k - error_k` at each step,
    then the total error is propagated through the affine fold.

    Extract per-step "errors" from two parallel folds: the exact fold and the
    computed fold. The error at step k is `exact_step - computed_step`.
    In practice, the "computed fold" has rounding errors at each step, and the
    per-step error `eₖ = L(sₖ) + vₖ - computed_nextₖ` is captured by EFTs.

    Specifically: `computed + affineFold L errors 0 = exact`

    where `errors = [e₁, ..., eₙ]` are the per-step rounding errors.

    This unifies `comp_horner_exact_decomposition` and `clenshaw_exact_decomposition`. -/
theorem affineFold_exact_decomposition (L : S → S) (hL : ∀ a b, L (a + b) = L a + L b)
    (vs errors : List S) (s : S) (computed : S)
    (hlen : vs.length = errors.length)
    -- The computed value satisfies: at each step, computed_next = L(computed_prev) + v - e
    -- Equivalently: computed is the result of folding with (v - e) offsets
    (hcomputed : computed = affineFold L (List.zipWith (· - ·) vs errors) s) :
    computed + affineFold L errors 0 = affineFold L vs s := by
  subst hcomputed
  induction vs generalizing errors s with
  | nil =>
    simp only [List.length_nil] at hlen
    have : errors = [] := List.length_eq_zero_iff.mp hlen.symm
    subst this
    simp [affineFold]
  | cons v vs ih =>
    match errors with
    | [] => simp at hlen
    | e :: es =>
      simp only [affineFold, List.zipWith_cons_cons, List.length_cons] at hlen ⊢
      -- zipWith step: v - e, so computed step goes to L(s) + (v - e) = (L s + v) + (-e)
      have hstep : L s + (v - e) = (L s + v) + (-e) := by abel
      rw [hstep]
      -- Apply IH with s' = L s + v, e' in first position
      -- and L 0 = 0, so affineFold L (e :: es) 0 = affineFold L es (L 0 + e) = affineFold L es e
      have hL0 : L (0 : S) = 0 := by
        have h := hL 0 0; rw [add_zero] at h
        have := congr_arg (· - L 0) h
        simp only [sub_self, add_sub_cancel_right] at this
        exact this.symm
      -- IH: affineFold (zipWith vs es) (L s + v) + affineFold es 0 = affineFold vs (L s + v)
      have hih := ih es (L s + v) (by omega)
      -- Use affine property: fold((L s + v) + (-e)) = fold(L s + v) + prop(len, -e)
      -- Use affine property: fold_err(e :: es) 0 = fold_err es 0 + prop(len, e)
      rw [hL0, zero_add]
      have haffine1 := affineFold_affine L hL (List.zipWith (· - ·) vs es) (L s + v) (-e)
      have haffine2 := affineFold_affine L hL es (0 : S) e
      simp only [zero_add] at haffine2
      rw [haffine1, haffine2]
      have hlen2 : (List.zipWith (· - ·) vs es).length = es.length := by
        rw [List.length_zipWith]; omega
      rw [hlen2]
      have hneg := affineProp_neg L hL es.length e
      -- Goal: (fold(zipWith vs es)(L s+v) + prop(-e)) + (fold_err(es)(0) + prop(e)) = fold vs (L s+v)
      -- this : fold(zipWith vs es)(L s+v) + fold_err(es)(0) = fold vs (L s+v)
      -- hneg : prop(-e) = -prop(e)
      -- Rewrite hneg and cancel ±prop(e) terms using abel
      rw [hneg]
      calc (affineFold L (List.zipWith (· - ·) vs es) (L s + v) + (-affineProp L es.length e)) +
              (affineFold L es 0 + affineProp L es.length e)
          = affineFold L (List.zipWith (· - ·) vs es) (L s + v) + affineFold L es 0 := by abel
        _ = affineFold L vs (L s + v) := hih

/-! ## Generic Propagation Bounds

The propagation bound `|affineProp L n e| ≤ κ^n · |e|` when `|L(e)| ≤ κ · |e|`.
This is the scalar (1D) version; for products, use component-wise bounds.

The generic error bound for any affine fold:
  `|final - exact| ≤ Σₖ |εₖ| · κ^{n-k}`
where `εₖ` are per-step rounding errors and `κ` bounds `L`'s contraction/expansion. -/

section ScalarBounds

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Propagation bound**: if `|L(e)| ≤ κ · |e|` for all `e`, then
    `|affineProp L n e| ≤ κ^n · |e|`. -/
theorem affineProp_abs_le (L : R → R) (κ : R) (hκ : 0 ≤ κ)
    (hL : ∀ e, |L e| ≤ κ * |e|)
    (n : ℕ) (e : R) :
    |affineProp L n e| ≤ κ ^ n * |e| := by
  induction n generalizing e with
  | zero => simp [affineProp]
  | succ n ih =>
    simp only [affineProp]
    calc |affineProp L n (L e)|
        ≤ κ ^ n * |L e| := ih (L e)
      _ ≤ κ ^ n * (κ * |e|) := by
          exact mul_le_mul_of_nonneg_left (hL e) (pow_nonneg hκ n)
      _ = κ ^ (n + 1) * |e| := by rw [pow_succ]; ring

/-- **Uniform error bound for scalar affine folds.**

    If each per-step error satisfies `|εₖ| ≤ δ`, then:
    `|affineFold L errors 0| ≤ δ · n · κ^{n-1}`

    (using the uniform bound `κ^{n-1-k} ≤ κ^{n-1}` for all k). -/
theorem affineFold_error_uniform_bound (L : R → R)
    (hL : ∀ a b, L (a + b) = L a + L b)
    (κ : R) (hκ : 1 ≤ κ) (hLbound : ∀ e, |L e| ≤ κ * |e|)
    (errors : List R) (δ : R) (hδ : 0 ≤ δ)
    (herr : ∀ e ∈ errors, |e| ≤ δ) :
    |affineFold L errors 0| ≤ (errors.length : R) * δ * κ ^ errors.length := by
  induction errors with
  | nil => simp [affineFold]
  | cons e es ih =>
    simp only [affineFold, List.length_cons]
    -- affineFold L (e :: es) 0 = affineFold L es (L 0 + e) = affineFold L es e
    have hL0 : L (0 : R) = 0 := by
      have h := hL 0 0; rw [add_zero] at h
      have := congr_arg (· - L 0) h
      simp only [sub_self, add_sub_cancel_right] at this; exact this.symm
    rw [hL0, zero_add]
    -- By affine: affineFold L es e = affineFold L es 0 + affineProp L es.length e
    have haffine := affineFold_affine L hL es 0 e
    rw [zero_add] at haffine
    rw [haffine]
    -- |fold(es, 0) + prop(m, e)| ≤ |fold(es, 0)| + |prop(m, e)|
    have htri := abs_add_le (affineFold L es 0) (affineProp L es.length e)
    -- |prop(m, e)| ≤ κ^m · |e| ≤ κ^m · δ
    have hprop := affineProp_abs_le L κ (le_trans zero_le_one hκ) hLbound es.length e
    have he : |e| ≤ δ := herr e List.mem_cons_self
    -- |fold(es, 0)| ≤ m · δ · κ^m (IH)
    have hih := ih (fun e' he' => herr e' (List.mem_cons_of_mem _ he'))
    -- Total: m·δ·κ^m + κ^m·δ = (m+1)·δ·κ^m
    -- Need: (m+1)·δ·κ^m ≤ (m+1)·δ·κ^{m+1} since κ ≥ 1
    have hκ_nn : (0 : R) ≤ κ := le_trans zero_le_one hκ
    have hκm : (0 : R) ≤ κ ^ es.length := pow_nonneg hκ_nn es.length
    have hκm1 : κ ^ es.length ≤ κ ^ (es.length + 1) :=
      pow_le_pow_right₀ hκ (Nat.le_succ _)
    push_cast
    have hpropδ : κ ^ es.length * |e| ≤ κ ^ es.length * δ :=
      mul_le_mul_of_nonneg_left he hκm
    have hstep : (es.length : R) * δ * κ ^ es.length ≤
        (es.length : R) * δ * κ ^ (es.length + 1) :=
      mul_le_mul_of_nonneg_left hκm1 (mul_nonneg (Nat.cast_nonneg' (n := es.length)) hδ)
    nlinarith [mul_nonneg hδ hκm, abs_nonneg (affineFold L es 0),
               abs_nonneg (affineProp L es.length e)]

/-! ### Per-Index Error Bound -/

/-- Weighted error sum: `Σ |eₖ| · κ^{n-1-k}`, weighting each error by how many
    propagation steps remain after it's introduced.

    `weightedErrorSum κ [e₀, e₁, ..., eₙ₋₁] = |e₀|·κ^{n-1} + |e₁|·κ^{n-2} + ... + |eₙ₋₁|` -/
def weightedErrorSum (κ : R) : List R → R
  | [] => 0
  | e :: es => κ ^ es.length * |e| + weightedErrorSum κ es

theorem weightedErrorSum_nonneg (κ : R) (hκ : 0 ≤ κ) (errors : List R) :
    0 ≤ weightedErrorSum κ errors := by
  induction errors with
  | nil => simp [weightedErrorSum]
  | cons e es ih =>
    simp only [weightedErrorSum]
    exact add_nonneg (mul_nonneg (pow_nonneg hκ es.length) (abs_nonneg e)) ih

/-- **Per-index error bound**: `|affineFold L errors 0| ≤ Σ |eₖ| · κ^{n-1-k}`.

    Tighter than the uniform bound `n·δ·κ^n` because each error is weighted by
    its actual propagation distance, not the maximum. -/
theorem affineFold_error_per_index (L : R → R)
    (hL : ∀ a b, L (a + b) = L a + L b)
    (κ : R) (hκ : 0 ≤ κ) (hLbound : ∀ e, |L e| ≤ κ * |e|)
    (errors : List R) :
    |affineFold L errors 0| ≤ weightedErrorSum κ errors := by
  induction errors with
  | nil => simp [affineFold, weightedErrorSum]
  | cons e es ih =>
    simp only [affineFold, weightedErrorSum]
    -- L 0 = 0
    have hL0 : L (0 : R) = 0 := by
      have h := hL 0 0; rw [add_zero] at h
      linarith
    rw [hL0, zero_add]
    -- affineFold L es e = affineFold L es 0 + affineProp L m e (by affine)
    have haffine := affineFold_affine L hL es 0 e
    rw [zero_add] at haffine; rw [haffine]
    -- Triangle + bounds
    have htri := abs_add_le (affineFold L es 0) (affineProp L es.length e)
    have hprop := affineProp_abs_le L κ hκ hLbound es.length e
    linarith

end ScalarBounds

/-! ## Gauge-Based Bounds (Generic over State Type)

The scalar bounds above only work for `S = R`. For multi-dimensional state
(e.g., Clenshaw with `S = R × R`), we parameterize by a **gauge function**
`ν : S → R` satisfying:
- Nonnegativity: `0 ≤ ν(s)`
- Triangle inequality: `ν(a + b) ≤ ν(a) + ν(b)`
- Contraction: `ν(L(s)) ≤ κ · ν(s)` for some `κ ≥ 0`

The choice of gauge dramatically affects bound quality:
- L1 norm `|a| + |b|`: easy to prove, but may give large κ
- L∞ norm `max(|a|, |b|)`: similarly easy, similar κ
- Energy/Lyapunov norms: can match spectral radius, giving tight bounds

Example: Clenshaw with `w = 2x`, `|x| ≤ 1`:
- L1/L∞ give κ = |2x| + 1 ≤ 3 → exponential growth 3^n (very loose)
- Spectral radius is 1 → linear growth (tight, but requires eigenvalue analysis)
- An energy norm matching the spectral radius would give κ = 1 generically -/

section GaugeBounds

variable {S : Type*} [AddCommGroup S]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A gauge on `S` with values in `R`: nonnegative, symmetric, sub-additive. -/
structure Gauge (S : Type*) [AddCommGroup S] (R : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  val : S → R
  nonneg : ∀ s, 0 ≤ val s
  zero : val 0 = 0
  symmetric : ∀ s, val (-s) = val s
  triangle : ∀ a b, val (a + b) ≤ val a + val b

/-- **Propagation bound with gauge**: if `ν(L(s)) ≤ κ · ν(s)`, then
    `ν(affineProp L n e) ≤ κ^n · ν(e)`. -/
theorem affineProp_gauge_le (L : S → S) (ν : Gauge S R) (κ : R) (hκ : 0 ≤ κ)
    (hL : ∀ s, ν.val (L s) ≤ κ * ν.val s)
    (n : ℕ) (e : S) :
    ν.val (affineProp L n e) ≤ κ ^ n * ν.val e := by
  induction n generalizing e with
  | zero => simp [affineProp]
  | succ n ih =>
    simp only [affineProp]
    calc ν.val (affineProp L n (L e))
        ≤ κ ^ n * ν.val (L e) := ih (L e)
      _ ≤ κ ^ n * (κ * ν.val e) :=
          mul_le_mul_of_nonneg_left (hL e) (pow_nonneg hκ n)
      _ = κ ^ (n + 1) * ν.val e := by rw [pow_succ]; ring

/-- **Uniform error bound with gauge**: if each `ν(eₖ) ≤ δ` and `κ ≥ 1`, then
    `ν(affineFold L errors 0) ≤ n · δ · κ^n`. -/
theorem affineFold_gauge_uniform_bound (L : S → S)
    (hL : ∀ a b, L (a + b) = L a + L b)
    (ν : Gauge S R) (κ : R) (hκ : 1 ≤ κ)
    (hLν : ∀ s, ν.val (L s) ≤ κ * ν.val s)
    (errors : List S) (δ : R) (hδ : 0 ≤ δ)
    (herr : ∀ e ∈ errors, ν.val e ≤ δ) :
    ν.val (affineFold L errors 0) ≤ (errors.length : R) * δ * κ ^ errors.length := by
  induction errors with
  | nil =>
    simp only [affineFold, List.length_nil, Nat.cast_zero, zero_mul]
    change ν.val 0 ≤ 0; linarith [ν.zero]
  | cons e es ih =>
    simp only [affineFold, List.length_cons]
    have hL0 : L (0 : S) = 0 := by
      have h := hL 0 0; rw [add_zero] at h
      have := congr_arg (· - L 0) h
      simp only [sub_self, add_sub_cancel_right] at this; exact this.symm
    rw [hL0, zero_add]
    -- affineFold L es e = affineFold L es 0 + affineProp L es.length e (by affine)
    have haffine := affineFold_affine L hL es 0 e
    rw [zero_add] at haffine; rw [haffine]
    -- ν(fold + prop) ≤ ν(fold) + ν(prop)
    have htri := ν.triangle (affineFold L es 0) (affineProp L es.length e)
    -- ν(prop) ≤ κ^m · ν(e) ≤ κ^m · δ
    have hprop := affineProp_gauge_le L ν κ (le_trans zero_le_one hκ) hLν es.length e
    have he := herr e List.mem_cons_self
    -- ν(fold) ≤ m · δ · κ^m (IH)
    have hih := ih (fun e' he' => herr e' (List.mem_cons_of_mem _ he'))
    -- κ^m ≤ κ^{m+1}
    have hκ_nn : (0 : R) ≤ κ := le_trans zero_le_one hκ
    have hκm : (0 : R) ≤ κ ^ es.length := pow_nonneg hκ_nn es.length
    have hκm1 : κ ^ es.length ≤ κ ^ (es.length + 1) :=
      pow_le_pow_right₀ hκ (Nat.le_succ _)
    -- Combine
    have hpropδ : κ ^ es.length * ν.val e ≤ κ ^ es.length * δ :=
      mul_le_mul_of_nonneg_left he hκm
    have hstep : (es.length : R) * δ * κ ^ es.length ≤
        (es.length : R) * δ * κ ^ (es.length + 1) :=
      mul_le_mul_of_nonneg_left hκm1 (mul_nonneg (Nat.cast_nonneg' (n := es.length)) hδ)
    push_cast
    nlinarith [ν.nonneg (affineFold L es 0), ν.nonneg (affineProp L es.length e),
               mul_nonneg hδ hκm]

/-! ### Per-Index Gauge Bound -/

/-- Weighted error sum for gauge: `Σ ν(eₖ) · κ^{n-1-k}`. -/
def weightedGaugeSum (ν : Gauge S R) (κ : R) : List S → R
  | [] => 0
  | e :: es => κ ^ es.length * ν.val e + weightedGaugeSum ν κ es

theorem weightedGaugeSum_nonneg (ν : Gauge S R) (κ : R) (hκ : 0 ≤ κ)
    (errors : List S) : 0 ≤ weightedGaugeSum ν κ errors := by
  induction errors with
  | nil => simp [weightedGaugeSum]
  | cons e es ih =>
    simp only [weightedGaugeSum]
    exact add_nonneg (mul_nonneg (pow_nonneg hκ _) (ν.nonneg _)) ih

/-- **Per-index gauge bound**: `ν(affineFold L errors 0) ≤ Σ ν(eₖ) · κ^{n-1-k}`. -/
theorem affineFold_gauge_per_index (L : S → S)
    (hL : ∀ a b, L (a + b) = L a + L b)
    (ν : Gauge S R) (κ : R) (hκ : 0 ≤ κ)
    (hLν : ∀ s, ν.val (L s) ≤ κ * ν.val s)
    (errors : List S) :
    ν.val (affineFold L errors 0) ≤ weightedGaugeSum ν κ errors := by
  induction errors with
  | nil =>
    simp only [affineFold, weightedGaugeSum]
    linarith [ν.zero]
  | cons e es ih =>
    simp only [affineFold, weightedGaugeSum]
    have hL0 : L (0 : S) = 0 := by
      have h := hL 0 0; rw [add_zero] at h
      have := congr_arg (· - L 0) h
      simp only [sub_self, add_sub_cancel_right] at this; exact this.symm
    rw [hL0, zero_add]
    have haffine := affineFold_affine L hL es 0 e
    rw [zero_add] at haffine; rw [haffine]
    have htri := ν.triangle (affineFold L es 0) (affineProp L es.length e)
    have hprop := affineProp_gauge_le L ν κ hκ hLν es.length e
    linarith

end GaugeBounds

end AffineFold
