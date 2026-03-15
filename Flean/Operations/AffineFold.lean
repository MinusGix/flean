import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Abel

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

end AffineFold
