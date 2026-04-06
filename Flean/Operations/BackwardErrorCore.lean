import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Flean.FloatFormat
import Flean.Operations.AffineFold

/-!
# Backward Error Framework — Core

Pure mathematical infrastructure for backward error analysis, with no
floating-point dependencies. This file can be imported by any module
(including KahanSum) without circular dependencies.

## Core structures

- `PerturbationGauge`: measures how far a perturbed input `x'` is from the original `x`
- `BackwardResult`: strict backward error — `f(x') = ŷ` with bounded perturbation
- `MixedResult`: backward + forward residual — `ŷ = f(x') + r` with both bounded

## Key theorems

- `error_distributable`: `|E| ≤ ε·Σ|vᵢ|` → constructive `μᵢ` with `E = Σ μᵢvᵢ`
- `backwardResult_of_forward_sum_bound`: forward → backward bridge for sums
- `backwardResult_of_forward_fin_bound`: Fin-indexed version
- `forward_le_cond_mul_backward`: forward error ≤ ε · condition number
- `backward_compose_one_round`: scalar composition of backward errors (unstructured)

## Composition

Two tracks for composing backward results:

**Multiplicative** (for `componentwiseRelGauge`):
- `BackwardResult.compose_scalar_sum`: `(1+δ)·Σ` with bound `(1+ε_A)(1+ε_B) - 1`
- `BackwardResult.compose_scalar_weighted_sum`: same for weighted sums

**Additive** (for gauges with triangle inequality):
- `PerturbationMetric`: gauge + triangle inequality
- `PerturbationLift`: pullback of output perturbations through `f`
- `BackwardResult.compose`: general `g ∘ f` with bound `ε_A + Λ·ε_B`

## References

- Higham, *Accuracy and Stability of Numerical Algorithms*, Ch. 1–4, 7
- Ogita, Rump, Oishi, "Accurate Sum and Dot Product" (2005)
-/

namespace BackwardError

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Perturbation Gauge -/

/-- A perturbation gauge measures the size of a perturbation from `x` to `x'`.

    Different choices of gauge give different backward error notions:
    - Componentwise relative: `max_i |x'_i - x_i| / |x_i|`
    - Normwise relative: `‖x' - x‖ / ‖x‖`
    - Weighted: `max_i |x'_i - x_i| / w_i` -/
structure PerturbationGauge (X : Type*) (R : Type*) [Zero R] [LE R] where
  /-- Size of perturbation from `x` to `x'`. -/
  dist : X → X → R
  /-- Non-negative. -/
  nonneg : ∀ x x', 0 ≤ dist x x'
  /-- Zero perturbation has zero size. -/
  self : ∀ x, dist x x = 0

/-! ### Gauge instances -/

/-- Uniform perturbation gauge: all per-element perturbations bounded by a single scalar.

    For a list of perturbation factors `μ : Fin n → R`, the gauge value is `max_i |μ_i|`.
    This is the natural gauge for componentwise backward error: given `x'_i = (1 + μ_i)·x_i`,
    the backward error is `max_i |μ_i|`.

    We define this on `Fin n → R` for `n > 0`. -/
def uniformGauge (n : ℕ) (hn : 0 < n) : PerturbationGauge (Fin n → R) R where
  dist x x' := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => |x' i - x i|)
  nonneg x x' := le_trans (abs_nonneg _)
    (Finset.le_sup' (fun i => |x' i - x i|) (Finset.mem_univ ⟨0, hn⟩))
  self x := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => by simp)
    · exact le_trans (abs_nonneg (x ⟨0, hn⟩ - x ⟨0, hn⟩))
        (Finset.le_sup' (fun i => |x i - x i|) (Finset.mem_univ ⟨0, hn⟩))

/-- Trivial gauge: perturbation size is always 0. Useful as a placeholder
    or for `MixedResult` where we don't care about input perturbation. -/
def trivialGauge (X : Type*) : PerturbationGauge X R where
  dist _ _ := 0
  nonneg _ _ := le_refl 0
  self _ := rfl

/-- Scalar absolute gauge: `dist(y, y') = |y' - y|`.
    The natural gauge for a single scalar output. -/
def scalarAbsGauge : PerturbationGauge R R where
  dist y y' := |y' - y|
  nonneg _ _ := abs_nonneg _
  self _ := by simp

/-- Componentwise relative gauge: `max_i |x'_i - x_i| / |x_i|`.

    For zero inputs, the term is 0 (multiplicative perturbation of 0 is 0).
    This is the standard gauge for backward error: if `x'_i = (1+μ_i)·x_i`
    then `dist(x, x') = max_i |μ_i|`. -/
def componentwiseRelGauge (n : ℕ) (hn : 0 < n) : PerturbationGauge (Fin n → R) R where
  dist x x' := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => if x i = 0 then 0 else |x' i - x i| / |x i|)
  nonneg x x' := by
    apply le_trans _ (Finset.le_sup' _ (Finset.mem_univ ⟨0, hn⟩))
    split_ifs with h
    · exact le_refl 0
    · exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  self x := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => by simp)
    · apply le_trans _ (Finset.le_sup' _ (Finset.mem_univ ⟨0, hn⟩))
      split_ifs with h <;> simp

/-! ## Backward Error Results -/

/-- **Strict backward error**: the computed result equals `f(x')` for some `x'`
    that is close to `x` under the perturbation gauge.

    Constructive: provides the actual perturbed input `x'`.

    Example: for summation, `BackwardResult` says
    `fl(Σxᵢ) = Σx'ᵢ` where `max_i |x'_i - x_i|/|x_i| ≤ ε`. -/
structure BackwardResult {X Y : Type*}
    (G : PerturbationGauge X R) (f : X → Y) (x : X) (computed : Y) where
  /-- The perturbed input. -/
  x' : X
  /-- Exactness: `f(x') = computed`. -/
  exact : f x' = computed
  /-- Backward error bound. -/
  eps : R
  /-- Non-negative bound. -/
  eps_nonneg : 0 ≤ eps
  /-- The perturbation is bounded by `eps` under the gauge. -/
  bound : G.dist x x' ≤ eps

/-- **Mixed backward-forward error**: the computed result equals `f(x')` plus a
    small residual, with both the input perturbation and residual bounded.

    This is the natural form for:
    - Compensated algorithms (exact backward + O(η²) residual)
    - Composition where strict backward may not compose cleanly
    - AffineFold decompositions: `computed + error_fold = exact_fold`

    A `BackwardResult` embeds into `MixedResult` with `residual = 0`. -/
structure MixedResult {X Y : Type*} [AddCommGroup Y]
    (G_in : PerturbationGauge X R)
    (G_out : AffineFold.Gauge Y R)
    (f : X → Y) (x : X) (computed : Y) where
  /-- The perturbed input. -/
  x' : X
  /-- The residual (forward error after backward attribution). -/
  residual : Y
  /-- Decomposition: `computed = f(x') + residual`. -/
  decomp : computed = f x' + residual
  /-- Backward error bound. -/
  eps_back : R
  /-- Non-negative backward bound. -/
  eps_back_nonneg : 0 ≤ eps_back
  /-- Input perturbation bounded. -/
  back_bound : G_in.dist x x' ≤ eps_back
  /-- Forward residual bound. -/
  eps_fwd : R
  /-- Non-negative forward bound. -/
  eps_fwd_nonneg : 0 ≤ eps_fwd
  /-- Residual bounded under the output gauge. -/
  residual_bound : G_out.val residual ≤ eps_fwd

/-! ### Conversions -/

/-- Embed a strict backward result into a mixed result with zero residual.
    Works with any output gauge (residual is 0, so `G_out.val 0 = 0 ≤ 0`). -/
def BackwardResult.toMixed {X Y : Type*} [AddCommGroup Y]
    {G : PerturbationGauge X R} {f : X → Y} {x : X} {computed : Y}
    (br : BackwardResult (R := R) G f x computed)
    (G_out : AffineFold.Gauge Y R) :
    MixedResult (R := R) G G_out f x computed where
  x' := br.x'
  residual := 0
  decomp := by rw [add_zero]; exact br.exact.symm
  eps_back := br.eps
  eps_back_nonneg := br.eps_nonneg
  back_bound := br.bound
  eps_fwd := 0
  eps_fwd_nonneg := le_refl 0
  residual_bound := le_of_eq G_out.zero

/-! ### AffineFold → MixedResult bridge -/

/-- Every `affineFold_exact_decomposition` produces a `MixedResult` with zero backward error
    and forward residual bounded by the gauge.

    Given `computed + affineFold L errors 0 = affineFold L vs s` (the exact decomposition),
    this yields `computed = f(s) + residual` where `f = affineFold L vs`,
    `residual = -(affineFold L errors 0)`, and the residual is gauge-bounded. -/
def MixedResult.ofAffineFold {S : Type*} [AddCommGroup S]
    {G_in : PerturbationGauge S R} (G_out : AffineFold.Gauge S R)
    {L : S → S} {vs errors : List S} {s computed : S}
    (hdecomp : computed + AffineFold.affineFold L errors 0 = AffineFold.affineFold L vs s)
    (eps_fwd : R) (heps_fwd : 0 ≤ eps_fwd)
    (hresidual : G_out.val (AffineFold.affineFold L errors 0) ≤ eps_fwd) :
    MixedResult (R := R) G_in G_out (AffineFold.affineFold L vs) s computed where
  x' := s
  residual := -(AffineFold.affineFold L errors 0)
  decomp := by
    have : computed = AffineFold.affineFold L vs s - AffineFold.affineFold L errors 0 :=
      eq_sub_of_add_eq hdecomp
    rw [this]; abel
  eps_back := 0
  eps_back_nonneg := le_refl 0
  back_bound := le_of_eq (G_in.self _)
  eps_fwd := eps_fwd
  eps_fwd_nonneg := heps_fwd
  residual_bound := by rw [G_out.symmetric]; exact hresidual

/-- Convenience: `MixedResult` from an exact decomposition + per-index gauge bound.

    Uses `affineFold_gauge_per_index` to bound the residual by the weighted gauge sum
    `Σ G_out(eₖ) · κ^{n-1-k}`. -/
def MixedResult.ofAffineFoldGauge {S : Type*} [AddCommGroup S]
    {G_in : PerturbationGauge S R} (G_out : AffineFold.Gauge S R)
    {L : S → S} (hL : ∀ a b, L (a + b) = L a + L b)
    {vs errors : List S} {s computed : S}
    (hdecomp : computed + AffineFold.affineFold L errors 0 = AffineFold.affineFold L vs s)
    (κ : R) (hκ : 0 ≤ κ)
    (hLG : ∀ t, G_out.val (L t) ≤ κ * G_out.val t) :
    MixedResult (R := R) G_in G_out (AffineFold.affineFold L vs) s computed :=
  MixedResult.ofAffineFold G_out hdecomp
    (AffineFold.weightedGaugeSum G_out κ errors)
    (AffineFold.weightedGaugeSum_nonneg G_out κ hκ errors)
    (AffineFold.affineFold_gauge_per_index L hL G_out κ hκ hLG errors)

/-! ## Backward Error for Linear Functions (Summation) -/

section LinearBackward

/-! We now prove backward error for functions of the form `f(x) = Σ v(xᵢ)`,
    bridging from forward error bounds `|E| ≤ ε·Σ|v(xᵢ)|` to constructive
    per-component perturbations. -/

lemma abs_div_mul_self' (x : R) : |x| / x * x = |x| := by
  by_cases hx : x = 0
  · simp [hx]
  · exact div_mul_cancel₀ _ hx

lemma abs_abs_div_self_le_one' (x : R) : |( |x| / x )| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h, div_self hx, abs_one]
    · rw [abs_of_neg h, neg_div, abs_neg, div_self hx, abs_one]

/-- Convert a list/Finset sum to the Fin index form. -/
lemma list_map_sum_eq_finset_sum' {α : Type*} {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → M) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
  simp [List.sum_ofFn, Function.comp]

/-- **Error distribution**: if `|E| ≤ ε · Σ|v(xᵢ)|`, then `E = Σ μᵢ · v(xᵢ)`
    with `|μᵢ| ≤ ε`.

    Constructive: `μᵢ = (E/Σ|v(xⱼ)|) · (|v(xᵢ)|/v(xᵢ))`. -/
theorem error_distributable {α : Type*} (xs : List α) (v : α → R) (E eps : R)
    (heps : 0 ≤ eps)
    (hbound : |E| ≤ eps * (xs.map (fun x => |v x|)).sum) :
    ∃ mu : Fin xs.length → R,
      E = ∑ i : Fin xs.length, mu i * v (xs.get i) ∧
      ∀ i, |mu i| ≤ eps := by
  set S := (xs.map (fun x => |v x|)).sum with hS_def
  by_cases hS : S = 0
  · exact ⟨fun _ => 0, by simp [abs_nonpos_iff.mp (by rw [hS, mul_zero] at hbound; exact hbound)],
      fun _ => by simp [heps]⟩
  · have hS_pos : 0 < S := lt_of_le_of_ne
      (List.sum_nonneg (fun y hy => by
        simp only [List.mem_map] at hy; obtain ⟨z, _, rfl⟩ := hy; exact abs_nonneg _))
      (Ne.symm hS)
    have hES : |E| / S ≤ eps := by rwa [div_le_iff₀ hS_pos]
    have hES_nn : 0 ≤ |E| / S := div_nonneg (abs_nonneg E) (le_of_lt hS_pos)
    refine ⟨fun i => E / S * (|v (xs.get i)| / v (xs.get i)), ?_, ?_⟩
    · simp_rw [show ∀ i : Fin xs.length,
        E / S * (|v (xs.get i)| / v (xs.get i)) * v (xs.get i) =
        E / S * |v (xs.get i)| from fun i => by rw [mul_assoc, abs_div_mul_self']]
      rw [← Finset.mul_sum, show ∑ i : Fin xs.length, |v (xs.get i)| = S from by
        rw [hS_def, list_map_sum_eq_finset_sum']]
      exact (div_mul_cancel₀ E (ne_of_gt hS_pos)).symm
    · intro i
      rw [abs_mul, abs_div, abs_of_pos hS_pos]
      exact le_trans (mul_le_mul_of_nonneg_left (abs_abs_div_self_le_one' _) hES_nn)
        (by rw [mul_one]; exact hES)

/-- **Forward-to-backward bridge for summation**: if the forward error of a
    computed sum satisfies `|result - Σv(xᵢ)| ≤ ε · Σ|v(xᵢ)|`, then
    the result equals the exact sum of perturbed inputs:
    `result = Σ(1 + μᵢ) · v(xᵢ)` with `|μᵢ| ≤ ε`.

    This is the standard componentwise backward error for summation-like functions. -/
theorem backwardResult_of_forward_sum_bound {α : Type*}
    (xs : List α) (v : α → R) (result : R) (eps : R) (heps : 0 ≤ eps)
    (hfwd : |result - (xs.map v).sum| ≤ eps * (xs.map (fun x => |v x|)).sum) :
    ∃ mu : Fin xs.length → R,
      result = ∑ i : Fin xs.length, (1 + mu i) * v (xs.get i) ∧
      ∀ i, |mu i| ≤ eps := by
  obtain ⟨mu, hmu_eq, hmu_bnd⟩ := error_distributable xs v _ eps heps hfwd
  refine ⟨mu, ?_, hmu_bnd⟩
  rw [list_map_sum_eq_finset_sum'] at hmu_eq
  rw [show result = (xs.map v).sum + (result - (xs.map v).sum) from by ring,
      list_map_sum_eq_finset_sum', hmu_eq, ← Finset.sum_add_distrib]
  simp_rw [show ∀ i : Fin xs.length,
    v (xs.get i) + mu i * v (xs.get i) = (1 + mu i) * v (xs.get i) from fun _ => by ring]

/-- **Backward error for bilinear functions (dot product form)**: if
    `|result - Σ a(xᵢ)·b(xᵢ)| ≤ ε · Σ|a(xᵢ)·b(xᵢ)|`, then
    `result = Σ(1 + μᵢ)·a(xᵢ)·b(xᵢ)` with `|μᵢ| ≤ ε`.

    This attributes all backward error to the products. For symmetric attribution
    to both factors, use with `ε/2` bounds on each factor. -/
theorem backwardResult_of_forward_bilinear_bound {α : Type*}
    (xs : List α) (a b : α → R) (result : R) (eps : R) (heps : 0 ≤ eps)
    (hfwd : |result - (xs.map (fun x => a x * b x)).sum| ≤
            eps * (xs.map (fun x => |a x * b x|)).sum) :
    ∃ mu : Fin xs.length → R,
      result = ∑ i : Fin xs.length, (1 + mu i) * (a (xs.get i) * b (xs.get i)) ∧
      ∀ i, |mu i| ≤ eps :=
  backwardResult_of_forward_sum_bound xs (fun x => a x * b x) result eps heps hfwd

/-- **Fin-indexed forward-to-backward bridge**: if `|result - Σ v(i)| ≤ ε · Σ|v(i)|`,
    then `result = Σ(1+μᵢ)·v(i)` with `|μᵢ| ≤ ε`. -/
theorem backwardResult_of_forward_fin_bound (n : ℕ) (v : Fin n → R)
    (result eps : R) (heps : 0 ≤ eps)
    (hfwd : |result - ∑ i : Fin n, v i| ≤ eps * ∑ i : Fin n, |v i|) :
    ∃ mu : Fin n → R,
      result = ∑ i : Fin n, (1 + mu i) * v i ∧
      ∀ i, |mu i| ≤ eps := by
  set E := result - ∑ i : Fin n, v i
  set S := ∑ i : Fin n, |v i|
  by_cases hS : S = 0
  · -- S = 0 means |E| ≤ 0, so E = 0
    have hE_zero : |E| ≤ 0 := le_trans hfwd (by rw [hS, mul_zero])
    have hE : E = 0 := abs_eq_zero.mp (le_antisymm hE_zero (abs_nonneg _))
    have hvi : ∀ i, v i = 0 := fun i => abs_eq_zero.mp (le_antisymm
      (le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i))
        (le_of_eq hS)) (abs_nonneg _))
    refine ⟨fun _ => 0, ?_, fun _ => by simp [heps]⟩
    have hsum_zero : (∑ i : Fin n, v i) = 0 := Finset.sum_eq_zero (fun i _ => hvi i)
    have hresult : result = 0 := by
      have : result - ∑ i : Fin n, v i = 0 := hE
      rw [hsum_zero, sub_zero] at this; exact this
    simp [hresult, hvi]
  · have hS_pos : 0 < S := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => abs_nonneg (v i))) (Ne.symm hS)
    have hES : |E| / S ≤ eps := by rwa [div_le_iff₀ hS_pos]
    have hES_nn : 0 ≤ |E| / S := div_nonneg (abs_nonneg E) hS_pos.le
    refine ⟨fun i => E / S * (|v i| / v i), ?_, ?_⟩
    · -- Distribute error: E = Σ μᵢ · vᵢ
      set mu := fun i : Fin n => E / S * (|v i| / v i)
      have hdist : E = ∑ i : Fin n, mu i * v i := by
        show E = ∑ i, E / S * (|v i| / v i) * v i
        simp_rw [show ∀ i : Fin n,
          E / S * (|v i| / v i) * v i = E / S * |v i| from
          fun i => by rw [mul_assoc, abs_div_mul_self']]
        rw [← Finset.mul_sum]
        exact (div_mul_cancel₀ E (ne_of_gt hS_pos)).symm
      -- result = Σ vᵢ + E = Σ vᵢ + Σ μᵢvᵢ = Σ (1 + μᵢ)vᵢ
      show result = ∑ i : Fin n, (1 + mu i) * v i
      have hresult : result = (∑ i : Fin n, v i) + E := by
        show result = _ + (result - _); ring
      rw [hresult, hdist, ← Finset.sum_add_distrib]
      congr 1; ext i; ring
    · intro i
      rw [abs_mul, abs_div, abs_of_pos hS_pos]
      exact le_trans (mul_le_mul_of_nonneg_left (abs_abs_div_self_le_one' _) hES_nn)
        (by rw [mul_one]; exact hES)

/-- **Structured backward result from forward sum bound**: lifts
    `backwardResult_of_forward_fin_bound` into a `BackwardResult` with
    `componentwiseRelGauge`.

    For `n > 0`: `computed = (∑ v_i)` up to forward error gives
    `BackwardResult` with `x'_i = (1+μ_i)·v_i` and `max_i |μ_i| ≤ ε`. -/
noncomputable def backwardResult_struct_of_forward_fin_bound
    {n : ℕ} (hn : 0 < n) (v : Fin n → R)
    (result eps : R) (heps : 0 ≤ eps)
    (hfwd : |result - ∑ i : Fin n, v i| ≤ eps * ∑ i : Fin n, |v i|) :
    BackwardResult (componentwiseRelGauge n hn) (fun w => ∑ i : Fin n, w i)
      v result := by
  choose mu hmu_eq hmu_bnd using backwardResult_of_forward_fin_bound n v result eps heps hfwd
  exact {
    x' := fun i => (1 + mu i) * v i
    exact := hmu_eq.symm
    eps := eps
    eps_nonneg := heps
    bound := by
      unfold componentwiseRelGauge
      dsimp only
      apply Finset.sup'_le
      intro i _
      by_cases hvi : v i = 0
      · simp [hvi, heps]
      · rw [if_neg hvi, show (1 + mu i) * v i - v i = mu i * v i from by ring,
            abs_mul, mul_div_cancel_of_imp (by intro h; exact absurd (abs_eq_zero.mp h) hvi)]
        exact hmu_bnd i
  }

/-- **Structured backward result for weighted sums**: if
    `|result - Σ c_i·w_i| ≤ ε · Σ|c_i·w_i|`, then there is a `BackwardResult`
    on the **coefficient space** with `f(c) = Σ c_i·w_i` and componentwise gauge.

    This is the key bridge for Horner backward error: the weights `w_i = x^{n-1-i}`
    are fixed, and the coefficients `c_i` are the "inputs" being perturbed. -/
noncomputable def backwardResult_struct_of_forward_weighted_bound
    {n : ℕ} (hn : 0 < n) (c w : Fin n → R)
    (result eps : R) (heps : 0 ≤ eps)
    (hfwd : |result - ∑ i : Fin n, c i * w i| ≤
            eps * ∑ i : Fin n, |c i * w i|) :
    BackwardResult (componentwiseRelGauge n hn)
      (fun c' => ∑ i : Fin n, c' i * w i) c result := by
  choose mu hmu_eq hmu_bnd using
    backwardResult_of_forward_fin_bound n (fun i => c i * w i) result eps heps hfwd
  exact {
    x' := fun i => (1 + mu i) * c i
    exact := by
      convert hmu_eq.symm using 1
      congr 1; ext i; ring
    eps := eps
    eps_nonneg := heps
    bound := by
      unfold componentwiseRelGauge
      dsimp only
      apply Finset.sup'_le
      intro i _
      by_cases hci : c i = 0
      · simp [hci, heps]
      · rw [if_neg hci, show (1 + mu i) * c i - c i = mu i * c i from by ring,
            abs_mul, mul_div_cancel_of_imp (by intro h; exact absurd (abs_eq_zero.mp h) hci)]
        exact hmu_bnd i
  }

/-- Zero coefficients have zero perturbed values in `backwardResult_struct_of_forward_weighted_bound`.
    Since `x' i = (1 + μ_i) · c i`, when `c i = 0` we get `x' i = 0`. -/
theorem backwardResult_struct_of_forward_weighted_bound_zero
    {n : ℕ} (hn : 0 < n) (c w : Fin n → R)
    (result eps : R) (heps : 0 ≤ eps)
    (hfwd : |result - ∑ i : Fin n, c i * w i| ≤
            eps * ∑ i : Fin n, |c i * w i|)
    (i : Fin n) (hci : c i = 0) :
    (backwardResult_struct_of_forward_weighted_bound hn c w result eps heps hfwd).x' i = 0 := by
  simp only [backwardResult_struct_of_forward_weighted_bound]
  rw [hci, mul_zero]

end LinearBackward

/-! ## Condition Number -/

section ConditionNumber

/-- **Componentwise condition number** for a function `f : (Fin n → R) → R` at `x`:
    the worst-case ratio of relative output change to relative input change.

    `κ(f, x) = Σ |x_i · ∂f/∂x_i(x)| / |f(x)|`

    For summation `f(x) = Σxᵢ`: `κ = Σ|xᵢ| / |Σxᵢ|`.
    For dot product `f(x,y) = Σxᵢyᵢ`: `κ = Σ|xᵢyᵢ| / |Σxᵢyᵢ|`. -/
noncomputable def componentwiseCondNumber (n : ℕ)
    (f : (Fin n → R) → R) (partials : Fin n → R) (x : Fin n → R) : R :=
  if f x = 0 then 0
  else (∑ i : Fin n, |x i * partials i|) / |f x|

/-- **Forward ≤ condition × backward** (first-order): if the computed result
    has componentwise backward error `ε`, then the forward relative error
    is bounded by `κ · ε` where `κ` is the componentwise condition number.

    For summation `f(x) = Σxᵢ`, the condition number is `Σ|xᵢ|/|Σxᵢ|`,
    so `rel_fwd_error ≤ ε · Σ|xᵢ|/|Σxᵢ|`.

    This is the fundamental relation connecting forward error, backward error,
    and conditioning. -/
theorem forward_le_cond_mul_backward (n : ℕ)
    (v : Fin n → R) (mu : Fin n → R) (eps : R)
    (hmu : ∀ i, |mu i| ≤ eps) :
    |(∑ i : Fin n, (1 + mu i) * v i) - (∑ i : Fin n, v i)| ≤
    eps * (∑ i : Fin n, |v i|) := by
  -- LHS = |Σ μᵢ · vᵢ|
  have hlhs : (∑ i : Fin n, (1 + mu i) * v i) - (∑ i : Fin n, v i) =
      ∑ i : Fin n, mu i * v i := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext i; ring
  rw [hlhs]
  -- |Σ μᵢvᵢ| ≤ Σ |μᵢvᵢ| ≤ ε · Σ|vᵢ|
  calc |(∑ i : Fin n, mu i * v i)|
      ≤ ∑ i : Fin n, |mu i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |mu i| * |v i| := by congr 1; ext i; exact abs_mul _ _
    _ ≤ ∑ i : Fin n, eps * |v i| := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_right (hmu i) (abs_nonneg _)
    _ = eps * ∑ i : Fin n, |v i| := (Finset.mul_sum ..).symm

/-- Relative forward error version: divide both sides by `|Σvᵢ|`. -/
theorem forward_rel_le_cond_mul_backward (n : ℕ)
    (v : Fin n → R) (mu : Fin n → R) (eps : R)
    (hmu : ∀ i, |mu i| ≤ eps)
    (hS : (∑ i : Fin n, v i) ≠ 0) :
    |(∑ i : Fin n, (1 + mu i) * v i) - (∑ i : Fin n, v i)| /
      |(∑ i : Fin n, v i)| ≤
    eps * ((∑ i : Fin n, |v i|) / |(∑ i : Fin n, v i)|) := by
  have habsS : (0 : R) < |∑ i : Fin n, v i| := abs_pos.mpr hS
  have h := forward_le_cond_mul_backward n v mu eps hmu
  calc |(∑ i, (1 + mu i) * v i) - ∑ i, v i| / |∑ i, v i|
      ≤ (eps * ∑ i, |v i|) / |∑ i, v i| := by
        exact div_le_div_of_nonneg_right h habsS.le
    _ = eps * ((∑ i, |v i|) / |∑ i, v i|) := by rw [mul_div_assoc]

/-! ### BackwardResult → Forward Error Bridge -/

/-- Extract per-component bound from `componentwiseRelGauge`: for nonzero `v i`,
    `|x' i - v i| ≤ eps * |v i|`. -/
theorem componentwiseRelGauge_component_bound {n : ℕ} (hn : 0 < n)
    {v x' : Fin n → R} {eps : R}
    (hbound : (componentwiseRelGauge n hn).dist v x' ≤ eps)
    (i : Fin n) (hvi : v i ≠ 0) :
    |x' i - v i| ≤ eps * |v i| := by
  have hle : |x' i - v i| / |v i| ≤ eps := by
    have := le_trans (Finset.le_sup' (fun j => if v j = 0 then 0
      else |x' j - v j| / |v j|) (Finset.mem_univ i)) hbound
    simp only [componentwiseRelGauge] at this
    rwa [if_neg hvi] at this
  rwa [div_le_iff₀ (abs_pos.mpr hvi)] at hle

/-- **Forward error from structured backward result** (summation).

    Given a `BackwardResult` with `componentwiseRelGauge` for `f = Σ`,
    the forward error is `|computed - Σvᵢ| ≤ ε · Σ|vᵢ|`.

    The `hzero` hypothesis ensures zero inputs have zero perturbation.
    This is needed because `componentwiseRelGauge` ignores zero-input components
    (they contribute 0 to the gauge), so `br.x' i` is unconstrained when `v i = 0`.
    Without `hzero`, the forward error could be arbitrarily large.
    All `BackwardResult` instances built by `backwardResult_struct_of_forward_*` satisfy
    this automatically (see `backwardResult_struct_of_forward_weighted_bound_zero`).
    this holds for all results constructed via
    `backwardResult_struct_of_forward_fin_bound`. -/
theorem forward_from_sum_backward {n : ℕ} (hn : 0 < n)
    {v : Fin n → R} {computed : R}
    (br : BackwardResult (componentwiseRelGauge n hn) (fun w => ∑ i : Fin n, w i)
      v computed)
    (hzero : ∀ i, v i = 0 → br.x' i = 0) :
    |computed - ∑ i : Fin n, v i| ≤ br.eps * ∑ i : Fin n, |v i| := by
  have hexact : computed = ∑ i : Fin n, br.x' i := br.exact.symm
  calc |computed - ∑ i, v i|
      = |(∑ i, br.x' i) - ∑ i, v i| := by conv_lhs => rw [hexact]
    _ = |∑ i, (br.x' i - v i)| := by rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i, |br.x' i - v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, br.eps * |v i| := by
        apply Finset.sum_le_sum; intro i _
        by_cases hvi : v i = 0
        · simp [hvi, hzero i hvi]
        · exact componentwiseRelGauge_component_bound hn br.bound i hvi
    _ = br.eps * ∑ i, |v i| := (Finset.mul_sum ..).symm

/-- **Relative forward error from backward result** (summation + condition number).

    `|computed - Σvᵢ| / |Σvᵢ| ≤ ε · κ` where `κ = Σ|vᵢ|/|Σvᵢ|`
    is the componentwise condition number for summation.

    This is Higham's fundamental relation: backward stability + conditioning
    → forward error. -/
theorem forward_rel_from_sum_backward {n : ℕ} (hn : 0 < n)
    {v : Fin n → R} {computed : R}
    (br : BackwardResult (componentwiseRelGauge n hn) (fun w => ∑ i : Fin n, w i)
      v computed)
    (hzero : ∀ i, v i = 0 → br.x' i = 0)
    (hS : (∑ i : Fin n, v i) ≠ 0) :
    |computed - ∑ i : Fin n, v i| / |∑ i : Fin n, v i| ≤
    br.eps * componentwiseCondNumber n (fun w => ∑ i : Fin n, w i) (fun _ => 1) v := by
  have habsS : (0 : R) < |∑ i : Fin n, v i| := abs_pos.mpr hS
  have hfwd := forward_from_sum_backward hn br hzero
  rw [componentwiseCondNumber, if_neg hS]
  simp only [mul_one]
  calc |computed - ∑ i, v i| / |∑ i, v i|
      ≤ (br.eps * ∑ i, |v i|) / |∑ i, v i| :=
        div_le_div_of_nonneg_right hfwd habsS.le
    _ = br.eps * ((∑ i, |v i|) / |∑ i, v i|) := mul_div_assoc _ _ _

end ConditionNumber

/-! ## Composition -/

-- NOTE: Full gauge-based composition (PerturbationLift + BackwardResult.compose)
-- requires triangle inequality on PerturbationGauge, which the current structure
-- doesn't have. The general composition theorem also needs a lift (pullback) that
-- only exists for linear/affine functions. Rather than add structure we don't yet
-- need, we prove the concrete scalar composition that our algorithms actually use.
-- See BackwardErrorDesign.md for the full framework sketch.

/-- **Scalar composition**: if `result₁ = Σ(1+μᵢ)·vᵢ` with `|μᵢ| ≤ ε₁`,
    and `result₂ = (1 + δ)·result₁` with `|δ| ≤ ε₂` (one more rounding),
    then `result₂ = Σ(1+μ'ᵢ)·vᵢ` with `|μ'ᵢ| ≤ ε₁ + ε₂ + ε₁·ε₂`. -/
theorem backward_compose_one_round (n : ℕ)
    (v : Fin n → R) (mu : Fin n → R) (delta eps₁ eps₂ : R)
    (hmu : ∀ i, |mu i| ≤ eps₁)
    (hdelta : |delta| ≤ eps₂)
    (heps₁ : 0 ≤ eps₁) :
    let mu' := fun i => mu i + delta + mu i * delta
    (∀ i, |mu' i| ≤ eps₁ + eps₂ + eps₁ * eps₂) ∧
    (1 + delta) * (∑ i : Fin n, (1 + mu i) * v i) =
      ∑ i : Fin n, (1 + mu' i) * v i := by
  constructor
  · intro i
    show |mu i + delta + mu i * delta| ≤ eps₁ + eps₂ + eps₁ * eps₂
    have hmu_i := hmu i
    have habs_mu : |mu i| ≤ eps₁ := hmu_i
    have habs_delta : |delta| ≤ eps₂ := hdelta
    -- |a + b + c| ≤ |a| + |b| + |c|
    have h1 : |mu i + delta + mu i * delta| ≤ |mu i| + |delta| + |mu i| * |delta| := by
      calc |mu i + delta + mu i * delta|
          ≤ |mu i + delta| + |mu i * delta| := abs_add_le _ _
        _ ≤ (|mu i| + |delta|) + |mu i| * |delta| := by
            rw [abs_mul]; linarith [abs_add_le (mu i) delta]
    -- |μ|·|δ| ≤ ε₁·ε₂
    have h2 : |mu i| * |delta| ≤ eps₁ * eps₂ :=
      mul_le_mul habs_mu habs_delta (abs_nonneg _) heps₁
    linarith
  · simp only
    rw [Finset.mul_sum]
    congr 1; ext i
    ring

/-- Establish `componentwiseRelGauge` bound from per-component bounds.
    Converse direction of `componentwiseRelGauge_component_bound`.
    Only needs bounds for nonzero components — zero components contribute 0 to the gauge. -/
theorem componentwiseRelGauge_dist_le {n : ℕ} (hn : 0 < n)
    {v x' : Fin n → R} {eps : R} (heps : 0 ≤ eps)
    (hnonzero : ∀ i, v i ≠ 0 → |x' i - v i| / |v i| ≤ eps) :
    (componentwiseRelGauge n hn).dist v x' ≤ eps := by
  simp only [componentwiseRelGauge]
  apply Finset.sup'_le
  intro i _
  split_ifs with h
  · exact heps
  · exact hnonzero i h

/-- Helper: `|(1+δ)·x' - v| ≤ (ε_A + ε_B + ε_A·ε_B)·|v|` when `|x' - v| ≤ ε_A·|v|`
    and `|δ| ≤ ε_B`. Used by all multiplicative composition theorems. -/
private theorem scalar_compose_component_bound
    (x'_i v_i delta eps_A eps_B : R)
    (hcomp : |x'_i - v_i| ≤ eps_A * |v_i|)
    (hdelta : |delta| ≤ eps_B)
    (_heps_A : 0 ≤ eps_A) (heps_B : 0 ≤ eps_B) (hvi : (0 : R) < |v_i|) :
    |(1 + delta) * x'_i - v_i| ≤ (eps_A + eps_B + eps_A * eps_B) * |v_i| := by
  -- (1+δ)·x' - v = (1+δ)·(x' - v) + δ·v
  have key : (1 + delta) * x'_i - v_i =
      (1 + delta) * (x'_i - v_i) + delta * v_i := by ring
  calc |(1 + delta) * x'_i - v_i|
      = |(1 + delta) * (x'_i - v_i) + delta * v_i| := by rw [key]
    _ ≤ |(1 + delta) * (x'_i - v_i)| + |delta * v_i| := abs_add_le _ _
    _ = |(1 + delta)| * |x'_i - v_i| + |delta| * |v_i| := by
        simp only [abs_mul]
    _ ≤ (1 + eps_B) * (eps_A * |v_i|) + eps_B * |v_i| := by
        have h1 : |(1 + delta)| ≤ 1 + eps_B := calc
          |(1 + delta)| ≤ |1| + |delta| := abs_add_le _ _
          _ = 1 + |delta| := by rw [abs_one]
          _ ≤ 1 + eps_B := by linarith
        have h2 := mul_le_mul h1 hcomp (abs_nonneg _) (by linarith)
        linarith [mul_le_mul_of_nonneg_right hdelta hvi.le]
    _ = (eps_A + eps_B + eps_A * eps_B) * |v_i| := by ring

/-- **Scalar post-composition**: given a `BackwardResult` for `f` and a scalar
    multiplication `(1 + δ)`, produce a `BackwardResult` for `(1+δ)·f`.

    The perturbed input stays the same as `brA.x'`, so the backward error
    is unchanged. This is the trivial direction — the scalar just passes through. -/
def BackwardResult.scale {X : Type*}
    {G : PerturbationGauge X R} {f : X → R} {x : X} {computed : R}
    (brA : BackwardResult G f x computed)
    (c : R) :
    BackwardResult G (fun w => c * f w) x (c * computed) where
  x' := brA.x'
  exact := by rw [brA.exact]
  eps := brA.eps
  eps_nonneg := brA.eps_nonneg
  bound := brA.bound

/-- **Weaken** a backward result by relaxing the error bound.
    Useful for simplifying bounds, e.g., `(1+η)^n - 1 ≤ γ_n`. -/
def BackwardResult.weaken {X Y : Type*}
    {G : PerturbationGauge X R} {f : X → Y} {x : X} {computed : Y}
    (br : BackwardResult G f x computed)
    {eps' : R} (heps' : br.eps ≤ eps') (heps'_nn : 0 ≤ eps') :
    BackwardResult G f x computed where
  x' := br.x'
  exact := br.exact
  eps := eps'
  eps_nonneg := heps'_nn
  bound := le_trans br.bound heps'

/-- **Scalar composition for summation**: given a `BackwardResult` for `f = Σ`
    with `componentwiseRelGauge`, and a scalar perturbation `(1 + δ)`,
    produce a `BackwardResult` for the **same function** `f = Σ`.

    Absorbs `(1+δ)` into each component perturbation via the identity
    `(1+δ)·Σ(1+μᵢ)·vᵢ = Σ(1+μ'ᵢ)·vᵢ` where `μ'ᵢ = μᵢ + δ + μᵢ·δ`.
    The bound grows multiplicatively: `ε' = ε_A + ε_B + ε_A·ε_B = (1+ε_A)(1+ε_B) - 1`. -/
noncomputable def BackwardResult.compose_scalar_sum {n : ℕ} (hn : 0 < n)
    {v : Fin n → R} {computed : R}
    (brA : BackwardResult (componentwiseRelGauge n hn)
      (fun w => ∑ i : Fin n, w i) v computed)
    (delta eps_B : R)
    (hdelta : |delta| ≤ eps_B) (heps_B : 0 ≤ eps_B) :
    BackwardResult (componentwiseRelGauge n hn)
      (fun w => ∑ i : Fin n, w i) v ((1 + delta) * computed) where
  x' i := (1 + delta) * brA.x' i
  exact := by
    simp only []
    rw [← Finset.mul_sum, brA.exact]
  eps := brA.eps + eps_B + brA.eps * eps_B
  eps_nonneg := by nlinarith [brA.eps_nonneg]
  bound := by
    apply componentwiseRelGauge_dist_le hn (by nlinarith [brA.eps_nonneg])
    intro i hvi
    have habsvi := abs_pos.mpr hvi
    rw [div_le_iff₀ habsvi]
    exact scalar_compose_component_bound _ _ _ _ _
      (componentwiseRelGauge_component_bound hn brA.bound i hvi)
      hdelta brA.eps_nonneg heps_B habsvi

/-- **Scalar composition for weighted sums**: given a `BackwardResult` for
    `f(c) = Σ cᵢ·wᵢ` with `componentwiseRelGauge` on coefficients `c`,
    and a scalar perturbation `(1 + δ)`, produce a `BackwardResult` for the
    same weighted sum function (absorbing `(1+δ)` into coefficient perturbations). -/
noncomputable def BackwardResult.compose_scalar_weighted_sum {n : ℕ} (hn : 0 < n)
    {w v : Fin n → R} {computed : R}
    (brA : BackwardResult (componentwiseRelGauge n hn)
      (fun c => ∑ i : Fin n, c i * w i) v computed)
    (delta eps_B : R)
    (hdelta : |delta| ≤ eps_B) (heps_B : 0 ≤ eps_B) :
    BackwardResult (componentwiseRelGauge n hn)
      (fun c => ∑ i : Fin n, c i * w i) v ((1 + delta) * computed) where
  x' i := (1 + delta) * brA.x' i
  exact := by
    show ∑ i : Fin n, ((1 + delta) * brA.x' i) * w i = (1 + delta) * computed
    have : ∀ i : Fin n, (1 + delta) * brA.x' i * w i =
        (1 + delta) * (brA.x' i * w i) := fun i => by ring
    simp_rw [this, ← Finset.mul_sum]
    congr 1
    exact brA.exact
  eps := brA.eps + eps_B + brA.eps * eps_B
  eps_nonneg := by nlinarith [brA.eps_nonneg]
  bound := by
    apply componentwiseRelGauge_dist_le hn (by nlinarith [brA.eps_nonneg])
    intro i hvi
    have habsvi := abs_pos.mpr hvi
    rw [div_le_iff₀ habsvi]
    exact scalar_compose_component_bound _ _ _ _ _
      (componentwiseRelGauge_component_bound hn brA.bound i hvi)
      hdelta brA.eps_nonneg heps_B habsvi

/-- **Multiplicative eps composition**: if `ε₁ = ε_A + ε_B + ε_A·ε_B`,
    then `1 + ε₁ = (1 + ε_A)(1 + ε_B)`.

    This is the key algebraic identity for chaining scalar compositions:
    after `m` roundings with bound `η` on initial error `ε₀`, the total
    is `(1 + ε₀)·(1 + η)^m - 1`. -/
theorem compose_eps_mul (eps_A eps_B : R) :
    1 + (eps_A + eps_B + eps_A * eps_B) = (1 + eps_A) * (1 + eps_B) := by ring

/-! ## Additive Composition Framework -/

/-- A perturbation metric is a `PerturbationGauge` with the triangle inequality.

    `componentwiseRelGauge` does NOT satisfy this (different denominators),
    but `uniformGauge` does. For `componentwiseRelGauge`, use the multiplicative
    composition (`compose_scalar`, `compose_scalar_sum`) instead. -/
structure PerturbationMetric (X : Type*) (R : Type*) [Zero R] [LE R] [Add R]
    extends PerturbationGauge X R where
  triangle : ∀ x x' x'', dist x x'' ≤ dist x x' + dist x' x''

/-- `uniformGauge` satisfies the triangle inequality via `|a - c| ≤ |a - b| + |b - c|`. -/
noncomputable def uniformGauge_metric (n : ℕ) (hn : 0 < n) :
    PerturbationMetric (Fin n → R) R where
  toPerturbationGauge := uniformGauge n hn
  triangle x x' x'' := by
    show (uniformGauge n hn).dist x x'' ≤
      (uniformGauge n hn).dist x x' + (uniformGauge n hn).dist x' x''
    simp only [uniformGauge]
    apply Finset.sup'_le
    intro i _
    calc |x'' i - x i|
        = |(x' i - x i) + (x'' i - x' i)| := by ring_nf
      _ ≤ |x' i - x i| + |x'' i - x' i| := abs_add_le _ _
      _ ≤ Finset.sup' Finset.univ _ (fun j => |x' j - x j|) +
          Finset.sup' Finset.univ _ (fun j => |x'' j - x' j|) :=
          add_le_add
            (Finset.le_sup' (fun j => |x' j - x j|) (Finset.mem_univ i))
            (Finset.le_sup' (fun j => |x'' j - x' j|) (Finset.mem_univ i))

/-- `scalarAbsGauge` satisfies the triangle inequality: `|z - x| ≤ |y - x| + |z - y|`. -/
noncomputable def scalarAbsGauge_metric :
    PerturbationMetric R R where
  toPerturbationGauge := scalarAbsGauge
  triangle x x' x'' := by
    show |x'' - x| ≤ |x' - x| + |x'' - x'|
    calc |x'' - x| = |(x' - x) + (x'' - x')| := by ring_nf
      _ ≤ |x' - x| + |x'' - x'| := abs_add_le _ _

/-- A perturbation lift for `f`: output perturbations of `f(x₀)` in `G_Y` can be
    pulled back to input perturbations of `x₀` in `G_X`, with amplification factor `Λ`.

    For linear functions, `Λ` is related to the condition number.
    For affine functions (AffineFold), `Λ` comes from the linear part. -/
structure PerturbationLift {X Y : Type*}
    (G_X : PerturbationGauge X R) (G_Y : PerturbationGauge Y R)
    (f : X → Y) where
  /-- Amplification factor. -/
  Lambda : R
  Lambda_nonneg : 0 ≤ Lambda
  /-- The lift: given base point `x₀` and target `y'` near `f(x₀)`,
      produce `x'` near `x₀` with `f(x') = y'` and bounded perturbation. -/
  lift : (x₀ : X) → (y' : Y) → (delta : R) →
         G_Y.dist (f x₀) y' ≤ delta → 0 ≤ delta →
         { x' : X // f x' = y' ∧ G_X.dist x₀ x' ≤ Lambda * delta }

/-- **General composition of backward results** via `PerturbationMetric` and `PerturbationLift`.

    Given:
    - `brA`: backward stability of algorithm A for `f` with error `ε_A`
    - `brB`: backward stability of algorithm B for `g` at the intermediate value with error `ε_B`
    - `plift`: output perturbations of `f` pull back with amplification `Λ`
    - Triangle inequality on `G_X`

    Produces backward stability of B∘A for `g ∘ f` with error `ε_A + Λ·ε_B`.

    Note: `brB` is stated at reference input `intermediate`, which equals `f brA.x'`
    by `brA.exact`. The lift pulls back B's perturbation through `f`. -/
noncomputable def BackwardResult.compose {X Y Z : Type*}
    {G_X : PerturbationMetric X R} {G_Y : PerturbationGauge Y R}
    {f : X → Y} {g : Y → Z} {x : X} {intermediate : Y} {computed : Z}
    (brA : BackwardResult G_X.toPerturbationGauge f x intermediate)
    (brB : BackwardResult G_Y g intermediate computed)
    (plift : PerturbationLift (R := R) G_X.toPerturbationGauge G_Y f) :
    BackwardResult G_X.toPerturbationGauge (g ∘ f) x computed := by
  -- brA.exact : f brA.x' = intermediate
  -- brB.bound : G_Y.dist intermediate brB.x' ≤ brB.eps
  -- Rewrite brB.bound to use f brA.x' as reference
  have hbound_at_x' : G_Y.dist (f brA.x') brB.x' ≤ brB.eps := by
    rw [brA.exact]; exact brB.bound
  -- Apply the lift to pull back brB.x' through f
  obtain ⟨x'', hfx'', hdist_x''⟩ :=
    plift.lift brA.x' brB.x' brB.eps hbound_at_x' brB.eps_nonneg
  exact {
    x' := x''
    exact := by
      simp only [Function.comp]
      rw [hfx'']
      exact brB.exact
    eps := brA.eps + plift.Lambda * brB.eps
    eps_nonneg := add_nonneg brA.eps_nonneg (mul_nonneg plift.Lambda_nonneg brB.eps_nonneg)
    bound := calc G_X.dist x x''
        ≤ G_X.dist x brA.x' + G_X.dist brA.x' x'' := G_X.triangle x brA.x' x''
      _ ≤ brA.eps + plift.Lambda * brB.eps := add_le_add brA.bound hdist_x''
  }

/-! ## Concrete PerturbationLift Instances -/

/-- **Summation lift**: perturbations of `∑ wᵢ` in `scalarAbsGauge` can be pulled back
    to perturbations of `w` in `uniformGauge` with amplification `Λ = 1`.

    Construction: given target `y'` with `|y' - ∑ w₀ᵢ| ≤ δ`, set
    `w'ᵢ = w₀ᵢ + (y' - ∑ w₀ⱼ) / n`. Then `∑ w'ᵢ = y'` and
    `max_i |w'ᵢ - w₀ᵢ| = |y' - ∑ w₀ⱼ| / n ≤ δ / n ≤ δ = 1 · δ`. -/
noncomputable def summationLift (n : ℕ) (hn : 0 < n) :
    PerturbationLift (R := R) (uniformGauge n hn) scalarAbsGauge
      (fun w => ∑ i : Fin n, w i) where
  Lambda := 1
  Lambda_nonneg := zero_le_one
  lift w₀ y' delta hdist _hdelta_nn := by
    -- hdist : |y' - ∑ w₀ᵢ| ≤ delta
    simp only [scalarAbsGauge] at hdist
    -- Construct w' by distributing the difference evenly
    let diff := y' - ∑ i : Fin n, w₀ i
    let w' : Fin n → R := fun i => w₀ i + diff / (n : R)
    refine ⟨w', ?_, ?_⟩
    · -- ∑ w'ᵢ = y'
      show ∑ i : Fin n, (w₀ i + diff / (n : R)) = y'
      have hn_ne : (n : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      field_simp
      simp [diff]
    · -- max_i |w'ᵢ - w₀ᵢ| ≤ 1 * delta
      show (uniformGauge n hn).dist w₀ w' ≤ 1 * delta
      rw [one_mul]
      simp only [uniformGauge]
      apply Finset.sup'_le
      intro i _
      show |w' i - w₀ i| ≤ delta
      -- |w'ᵢ - w₀ᵢ| = |diff / n| ≤ |diff| / n ≤ |diff| ≤ delta
      simp only [w', add_sub_cancel_left]
      have hn_pos : (0 : R) < (n : R) := Nat.cast_pos.mpr hn
      rw [abs_div]
      calc |diff| / |(n : R)|
          = |diff| / (n : R) := by rw [abs_of_pos hn_pos]
        _ ≤ |diff| := by
            rw [div_le_iff₀ hn_pos]
            calc |diff| = |diff| * 1 := by ring
              _ ≤ |diff| * (n : R) :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (abs_nonneg _)
        _ ≤ delta := hdist

/-- **Weighted sum lift**: perturbations of `Σ xᵢaᵢ` in `scalarAbsGauge` can be
    pulled back to perturbations of `x` in `uniformGauge` with amplification
    `Λ = 1 / max|aᵢ|`.

    Construction: pick the index `k` with largest `|aₖ|` and perturb only that
    component: `x'ₖ = x₀ₖ + (y' - Σ x₀ⱼaⱼ)/aₖ`. Then `Σ x'ᵢaᵢ = y'` and
    `max_i |x'ᵢ - x₀ᵢ| = |y' - Σ x₀ⱼaⱼ|/|aₖ| ≤ δ/max|aᵢ|`.

    Requires at least one nonzero weight. -/
noncomputable def weightedSumLift (n : ℕ) (hn : 0 < n)
    (a : Fin n → R) (k : Fin n) (hak : a k ≠ 0)
    (hmax : ∀ i, |a i| ≤ |a k|) :
    PerturbationLift (R := R) (uniformGauge n hn) scalarAbsGauge
      (fun x => ∑ i : Fin n, x i * a i) where
  Lambda := 1 / |a k|
  Lambda_nonneg := div_nonneg zero_le_one (abs_nonneg _)
  lift x₀ y' delta hdist hdelta_nn := by
    simp only [scalarAbsGauge] at hdist
    let diff := y' - ∑ i : Fin n, x₀ i * a i
    -- Perturb only component k
    let x' : Fin n → R := fun i => if i = k then x₀ i + diff / a k else x₀ i
    refine ⟨x', ?_, ?_⟩
    · -- ∑ x'ᵢ · aᵢ = y'
      show ∑ i : Fin n, x' i * a i = y'
      -- Split sum: only k-th term differs
      have : ∑ i : Fin n, x' i * a i =
          ∑ i : Fin n, x₀ i * a i + diff / a k * a k := by
        have hsame : ∀ i, x' i * a i =
            x₀ i * a i + if i = k then diff / a k * a k else 0 := by
          intro i; simp only [x']; split_ifs with h
          · subst h; ring
          · ring
        simp_rw [hsame, Finset.sum_add_distrib]
        congr 1
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      rw [this, div_mul_cancel₀ _ hak]; simp [diff]
    · -- max_i |x'ᵢ - x₀ᵢ| ≤ (1/|aₖ|) · δ
      show (uniformGauge n hn).dist x₀ x' ≤ 1 / |a k| * delta
      simp only [uniformGauge]
      apply Finset.sup'_le
      intro i _
      show |x' i - x₀ i| ≤ 1 / |a k| * delta
      simp only [x']
      split_ifs with h
      · subst h
        simp only [add_sub_cancel_left, abs_div, one_div, diff]
        rw [inv_mul_eq_div]
        exact div_le_div_of_nonneg_right hdist (abs_nonneg _)
      · simp only [sub_self, abs_zero]
        exact mul_nonneg (div_nonneg zero_le_one (abs_nonneg _)) hdelta_nn

/-! ## Mixed Composition -/

/-- **Composition without lift**: when no perturbation lift exists, composing two
    backward results produces a `MixedResult` with backward error from the first
    algorithm and forward residual from the second.

    Given:
    - `brA`: backward stability of A for `f` with error `ε_A`
    - `brB`: backward stability of B for `g` at `intermediate = f(x'_A)` with error `ε_B`
    - `hLip`: a Lipschitz-like bound `G_out.val (g(y₁) - g(y₂)) ≤ L · G_Y.dist(y₁, y₂)`

    Produces: `computed = (g ∘ f)(x'_A) + residual` with `G_out.val(residual) ≤ L · ε_B`.

    The backward error is just `ε_A` (from A only), and the forward residual
    captures B's error as measured through g's Lipschitz constant. -/
noncomputable def MixedResult.compose_no_lift {X Y Z : Type*} [AddCommGroup Z]
    {G_X : PerturbationGauge X R}
    {G_Y : PerturbationGauge Y R}
    {G_out : AffineFold.Gauge Z R}
    {f : X → Y} {g : Y → Z} {x : X} {intermediate : Y} {computed : Z}
    (brA : BackwardResult G_X f x intermediate)
    (brB : BackwardResult G_Y g intermediate computed)
    (L : R) (hL : 0 ≤ L)
    (hLip : ∀ y₁ y₂ : Y, G_out.val (g y₁ - g y₂) ≤ L * G_Y.dist y₁ y₂) :
    MixedResult (R := R) G_X G_out (g ∘ f) x computed where
  x' := brA.x'
  residual := computed - g (f brA.x')
  decomp := by simp [Function.comp]
  eps_back := brA.eps
  eps_back_nonneg := brA.eps_nonneg
  back_bound := brA.bound
  eps_fwd := L * brB.eps
  eps_fwd_nonneg := mul_nonneg hL brB.eps_nonneg
  residual_bound := by
    -- computed = g(brB.x'), and intermediate = f(brA.x')
    -- residual = g(brB.x') - g(f(brA.x'))
    -- residual = computed - (g∘f)(x'_A)
    -- computed = g(x'_B) by brB.exact
    -- intermediate = f(x'_A) by brA.exact
    -- So residual = g(x'_B) - g(intermediate) = -(g(intermediate) - g(x'_B))
    calc G_out.val (computed - g (f brA.x'))
        = G_out.val (-(g (f brA.x') - computed)) := by
          congr 1; abel
      _ = G_out.val (g (f brA.x') - computed) := G_out.symmetric _
      _ = G_out.val (g (f brA.x') - g brB.x') := by rw [brB.exact]
      _ = G_out.val (g intermediate - g brB.x') := by rw [brA.exact]
      _ ≤ L * G_Y.dist intermediate brB.x' := hLip intermediate brB.x'
      _ ≤ L * brB.eps := mul_le_mul_of_nonneg_left brB.bound hL

end BackwardError
