import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Flean.Operations.DotProduct
import Flean.Operations.Horner

/-!
# Backward Error Framework

Backward error analysis asks: given a computed result `ŷ`, what nearby input `x'` would
produce `ŷ` exactly? This cleanly separates algorithm quality (backward error) from
problem sensitivity (condition number).

## Core structures

- `PerturbationGauge`: measures how far a perturbed input `x'` is from the original `x`
- `BackwardResult`: strict backward error — `f(x') = ŷ` with bounded perturbation
- `MixedResult`: backward + forward residual — `ŷ = f(x') + r` with both bounded

## Instances

- `componentwiseGauge`: `max_i |x'_i - x_i| / |x_i|` (relative, per-component)
- `weightedGauge`: `max_i |x'_i - x_i| / w_i` (generalizes componentwise and normwise)

## Key theorems

- `backwardResult_of_forward_bound`: convert `|ŷ - Σv(xᵢ)| ≤ ε·Σ|v(xᵢ)|` to backward form
- `BackwardResult.toMixed`: embed strict backward error into mixed form

## Relationship to existing infrastructure

- Generalizes `error_distributable` and `backward_from_forward` from KahanSum.lean
- Output residual in `MixedResult` uses the existing `Gauge` from AffineFold.lean
- The `affineFold_exact_decomposition` pattern gives `MixedResult` directly

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
  /-- Forward residual bound (as a real number). -/
  fwd_bound : R
  /-- Non-negative forward bound. -/
  fwd_bound_nonneg : 0 ≤ fwd_bound

/-! ### Conversions -/

/-- Embed a strict backward result into a mixed result with zero residual. -/
def BackwardResult.toMixed {X Y : Type*} [AddCommGroup Y]
    {G : PerturbationGauge X R} {f : X → Y} {x : X} {computed : Y}
    (br : BackwardResult (R := R) G f x computed) :
    MixedResult (R := R) G f x computed where
  x' := br.x'
  residual := 0
  decomp := by rw [add_zero]; exact br.exact.symm
  eps_back := br.eps
  eps_back_nonneg := br.eps_nonneg
  back_bound := br.bound
  fwd_bound := 0
  fwd_bound_nonneg := le_refl 0

/-! ## Backward Error for Linear Functions (Summation) -/

section LinearBackward

/-! We now prove backward error for functions of the form `f(x) = Σ v(xᵢ)`,
    bridging from forward error bounds `|E| ≤ ε·Σ|v(xᵢ)|` to constructive
    per-component perturbations.

    This generalizes `error_distributable` and `backward_from_forward` from KahanSum. -/

private lemma abs_div_mul_self' (x : R) : |x| / x * x = |x| := by
  by_cases hx : x = 0
  · simp [hx]
  · exact div_mul_cancel₀ _ hx

private lemma abs_abs_div_self_le_one' (x : R) : |( |x| / x )| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h, div_self hx, abs_one]
    · rw [abs_of_neg h, neg_div, abs_neg, div_self hx, abs_one]

/-- Convert a list/Finset sum to the Fin index form. -/
private lemma list_map_sum_eq_finset_sum' {α : Type*} {M : Type*} [AddCommMonoid M]
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

end ConditionNumber

end BackwardError

/-! ## Floating-Point Backward Error Instances -/

namespace BackwardError

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ### Dot Product Backward Error -/

/-- **Backward error for dot product**: the computed dot product equals the exact
    dot product of slightly perturbed input pairs:

    `fl(x · y) = Σ(1 + μᵢ) · xᵢyᵢ` where `|μᵢ| ≤ (1+η)^n - 1`.

    This attributes all backward error to the products `xᵢyᵢ`. The perturbation
    bound `(1+η)^n - 1` is the same as the forward error constant from
    `DotProduct.dp_error_bound` (Higham's Theorem 3.1). -/
theorem dp_backward_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DotProduct.DPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    ∃ mu : Fin pairs.length → R,
      (final.toVal : R) =
        ∑ i : Fin pairs.length,
          (1 + mu i) * ((pairs.get i).1.toVal (R := R) * (pairs.get i).2.toVal) ∧
      ∀ i, |mu i| ≤ (1 + η) ^ pairs.length - 1 :=
  backwardResult_of_forward_bilinear_bound
    pairs (fun p => p.1.toVal) (fun p => p.2.toVal)
    (final.toVal : R) ((1 + η) ^ pairs.length - 1)
    (by have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
        exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith)))
    (DotProduct.dp_error_bound trace hinit hnr)

/-- **Backward error for dot product (γ form)**: `|μᵢ| ≤ γ_n = nη/(1-nη)`. -/
theorem dp_backward_error_gamma
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DotProduct.DPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (pairs.length : R) * η < 1) :
    ∃ mu : Fin pairs.length → R,
      (final.toVal : R) =
        ∑ i : Fin pairs.length,
          (1 + mu i) * ((pairs.get i).1.toVal (R := R) * (pairs.get i).2.toVal) ∧
      ∀ i, |mu i| ≤ gamma_n (R := R) pairs.length := by
  obtain ⟨mu, heq, hbnd⟩ := dp_backward_error trace hinit hnr
  exact ⟨mu, heq, fun i => le_trans (hbnd i) (pow_sub_one_le_gamma pairs.length hsmall)⟩

/-! ### Horner Backward Error (Coefficient Perturbation) -/

/-! ### Horner Polynomial ↔ Fin Sum -/

/-- `hornerPoly cs 0 x = Σ_{i} cs[i] · x^{n-1-i}` where `n = cs.length`.

    This connects the recursive Horner evaluation to an explicit power series sum,
    enabling backward error analysis via `backwardResult_of_forward_sum_bound`. -/
private theorem hornerPoly_acc_eq (cs : List R) (acc x : R) :
    Horner.hornerPoly cs acc x =
      acc * x ^ cs.length + Horner.hornerPoly cs 0 x := by
  induction cs generalizing acc with
  | nil => simp [Horner.hornerPoly]
  | cons c cs ih =>
    simp only [Horner.hornerPoly, zero_mul, zero_add, List.length_cons]
    rw [ih (acc * x + c), ih c]
    ring

/-- `hornerPoly cs 0 x` as a Finset sum over `Fin cs.length`. -/
theorem hornerPoly_eq_fin_sum (cs : List R) (x : R) :
    Horner.hornerPoly cs 0 x =
      ∑ i : Fin cs.length, cs.get i * x ^ (cs.length - 1 - i.val) := by
  induction cs with
  | nil => simp [Horner.hornerPoly]
  | cons c cs ih =>
    simp only [Horner.hornerPoly, zero_mul, zero_add, List.length_cons]
    rw [hornerPoly_acc_eq cs c x, ih, add_comm, Fin.sum_univ_succ]
    simp only [List.get_cons_zero, Fin.val_zero, Nat.sub_zero]
    rw [show c * x ^ cs.length = c * x ^ (cs.length + 1 - 1) by
      simp]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val < cs.length := i.isLt
    have hexp : cs.length - 1 - i.val = cs.length + 1 - 1 - i.succ.val := by
      simp [Fin.val_succ]
      omega
    rw [hexp]
    rfl

/-- Absolute version: `hornerPoly |cs| 0 |x| = Σ |cs[i]| · |x|^{n-1-i}`. -/
theorem hornerPoly_abs_eq_fin_sum (cs : List R) (x : R) :
    Horner.hornerPoly (cs.map (fun c => |c|)) 0 |x| =
      ∑ i : Fin cs.length, |cs.get i| * |x| ^ (cs.length - 1 - i.val) := by
  induction cs with
  | nil => simp [Horner.hornerPoly]
  | cons c cs ih =>
    simp only [Horner.hornerPoly, zero_mul, zero_add, List.map_cons, List.length_cons]
    rw [hornerPoly_acc_eq, ih, add_comm, Fin.sum_univ_succ]
    simp only [List.get_cons_zero, Fin.val_zero, Nat.sub_zero, List.length_map]
    rw [show |c| * |x| ^ cs.length = |c| * |x| ^ (cs.length + 1 - 1) by simp]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hexp : cs.length - 1 - i.val = cs.length + 1 - 1 - i.succ.val := by
      simp [Fin.val_succ]; omega
    rw [hexp]; rfl

/-- `Σ |cs[i]| · |x|^k = Σ |cs[i] · x^k|`. -/
theorem abs_horner_sum_eq (cs : List R) (x : R) :
    (∑ i : Fin cs.length, |cs.get i| * |x| ^ (cs.length - 1 - i.val)) =
      ∑ i : Fin cs.length, |cs.get i * x ^ (cs.length - 1 - i.val)| := by
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_mul, abs_pow]

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
    refine ⟨fun _ => 0, ?_, fun _ => by simp [heps]⟩
    show result = ∑ i : Fin n, (1 + 0) * v i
    simp only [add_zero, one_mul]
    linarith [show E = result - ∑ i : Fin n, v i from rfl]
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

/-- **Backward error for Horner evaluation**: the computed polynomial evaluation
    equals a polynomial with perturbed coefficients evaluated at the exact `x`:

    `fl(p(x)) = Σ(1 + μᵢ) · cᵢ · x^{n-1-i}` where `|μᵢ| ≤ (1+η)^{2n} - 1`.

    Requires `init = 0` (standard polynomial evaluation, not accumulated). -/
theorem horner_backward_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : Horner.HornerTrace x coeffs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    ∃ mu : Fin coeffs.length → R,
      (final.toVal : R) =
        ∑ i : Fin coeffs.length,
          (1 + mu i) * ((coeffs.get i).toVal (R := R) *
            (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)) ∧
      ∀ i, |mu i| ≤ (1 + η) ^ (2 * coeffs.length) - 1 := by
  -- Forward error bound from Horner.horner_error_bound
  have hfwd := Horner.horner_error_bound trace hnr
  -- Simplify with init = 0
  simp only [hinit, abs_zero] at hfwd
  -- The forward bound involves:
  --   LHS: hornerPoly (coeffs.map toVal) 0 x.toVal
  --   RHS: hornerPoly (coeffs.map |toVal|) 0 |x.toVal|
  -- Rewrite both to Fin sums
  -- Rewrite the value-side hornerPoly to a Fin sum
  set vfun : Fin coeffs.length → R :=
    fun i => (coeffs.get i).toVal (R := R) *
      (x.toVal (R := R)) ^ (coeffs.length - 1 - i.val)
  -- The forward bound says |result - Σ vfun| ≤ ε · Σ|vfun|
  -- Restate the forward bound using vfun
  have hval : Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
      ∑ i, vfun i := by
    calc
      Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) 0 (x.toVal) =
          ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            (coeffs.map (fun c => c.toVal (R := R))).get i *
              (x.toVal (R := R)) ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            exact hornerPoly_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, vfun i := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i
          simp
        · intro i _
          simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map]
  have habs : Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
      ∑ i, |vfun i| := by
    calc
      Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|)) 0 |x.toVal (R := R)| =
          ∑ i : Fin (coeffs.map (fun c => c.toVal (R := R))).length,
            |(coeffs.map (fun c => c.toVal (R := R))).get i| *
              |x.toVal (R := R)| ^
                ((coeffs.map (fun c => c.toVal (R := R))).length - 1 - i.val) := by
            simpa [List.map_map]
              using hornerPoly_abs_eq_fin_sum (coeffs.map (fun c => c.toVal (R := R))) (x.toVal)
      _ = ∑ i : Fin coeffs.length, |vfun i| := by
        refine Finset.sum_equiv
          (finCongr (List.length_map (f := fun c : FiniteFp => c.toVal (R := R)) (as := coeffs))) ?_ ?_
        · intro i
          simp
        · intro i _
          simp [vfun, List.length_map, List.get_eq_getElem, List.getElem_map, abs_mul, abs_pow]
  have hfwd' : |(final.toVal : R) - ∑ i, vfun i| ≤
      ((1 + η) ^ (2 * coeffs.length) - 1) * ∑ i, |vfun i| := by
    rw [← hval, ← habs]; exact hfwd
  -- Apply the Fin-indexed bridge
  have heps_nn : (0 : R) ≤ (1 + η) ^ (2 * coeffs.length) - 1 := by
    have : (0 : R) < η := by simp only [FloatFormat.hEps_def]; positivity
    exact sub_nonneg.mpr (one_le_pow₀ (show (1 : R) ≤ 1 + η by linarith))
  exact backwardResult_of_forward_fin_bound coeffs.length vfun
    (final.toVal : R) _ heps_nn hfwd'

end BackwardError

/-! ## Phase 2: Composition -/

namespace BackwardError

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Perturbation Lift

A perturbation lift for `f` at `x`: perturbations of `f(x)` can be pulled back
to perturbations of `x`, with bounded amplification. This is the key interface
for composing backward-stable algorithms.

For linear `f`, the lift always exists with `Λ = ‖f⁻¹‖` (the condition number).
For affine fold computations, the affine structure gives a natural lift. -/

-- NOTE: Full gauge-based composition (PerturbationLift + BackwardResult.compose)
-- requires triangle inequality on PerturbationGauge, which the current structure
-- doesn't have. The general composition theorem also needs a lift (pullback) that
-- only exists for linear/affine functions. Rather than add structure we don't yet
-- need, we prove the concrete scalar composition that our algorithms actually use.
-- See design doc for the full framework sketch.

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

end BackwardError
