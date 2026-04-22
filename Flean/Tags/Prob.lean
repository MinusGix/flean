import Flean.Tags.Attributes
import Flean.Tags.Nonneg
import Flean.Tags.AbsBound
import Flean.Tags.Simplex
import Flean.Tags.OneHot
import Flean.Operations.CrossEntropy

/-!
# Tag: `IsProb`

R-parametric tag asserting that a vector `y : Fin n → FiniteFp` is a
(sub-)probability distribution: every entry non-negative and total
mass at most 1.

## Design

Slightly **weaker** than `IsSimplex` (which requires `∑ = 1` and
derives `0 < n`).  `IsProb` allows:

- Proper probability distributions (`∑ y = 1`): `IsSimplex` fits here.
- One-hot encodings (`∑ y = 1`, concentrated at one index):
  `IsOneHot` fits here.
- Sub-probability distributions (`∑ y < 1`): label-smoothing, soft
  unsupervised targets, dropout-style noise models.
- The zero vector (`∑ y = 0`, all entries zero): degenerate but valid.

Strictly stronger than `IsNonneg` (adds the upper-bound on total mass).

## Position in the tag lattice

```
     IsOneHot   IsSimplex
         │         │
         └─►IsProb◄─┘
              │
              ▼
           IsNonneg  (per-index)
              │
              ▼
       HasAbsBound 1 (per-index)
```

## Payoff

Under `IsProb y`, several CE-bound terms simplify:
- `|y_i| = y_i` (since `y_i ≥ 0`).
- `Σ |y_i| = Σ y_i ≤ 1` — the weighted-sum "total mass" coefficient
  drops below 1 automatically.
- `Σ y_i · f i` is the **expectation** under `y` interpreted as a
  probability measure — ML-meaningful.

The CE specialization (`fpCrossEntropy_isProb_error_bound`) rephrases
the general bound in expectation form, which is how the loss is
naturally interpreted in classifier training.
-/

set_option autoImplicit false

namespace Flean.Tags

open Finset BigOperators

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## The tag -/

/-- `IsProb (R := R) y` asserts `y` is a sub-probability distribution:
every entry non-negative and total mass ≤ 1. -/
structure IsProb {n : ℕ} (y : Fin n → FiniteFp) : Prop where
  /-- Each entry is non-negative. -/
  nonneg : ∀ i, (0 : R) ≤ ((y i).toVal : R)
  /-- Total mass at most 1. -/
  sum_le_one : (∑ i, ((y i).toVal : R)) ≤ 1

/-! ## Basic derived facts -/

/-- Under `IsProb`, magnitudes equal values: `|y_i| = y_i`. -/
theorem IsProb.abs_eq {n : ℕ} {y : Fin n → FiniteFp}
    (h : IsProb (R := R) y) (i : Fin n) :
    |((y i).toVal : R)| = (y i).toVal :=
  abs_of_nonneg (h.nonneg i)

/-- Under `IsProb`, `Σ |y_i| = Σ y_i ≤ 1`. -/
theorem IsProb.sum_abs_le_one {n : ℕ} {y : Fin n → FiniteFp}
    (h : IsProb (R := R) y) :
    (∑ i, |((y i).toVal : R)|) ≤ 1 := by
  have h_eq : (∑ i, |((y i).toVal : R)|) = ∑ i, ((y i).toVal : R) :=
    Finset.sum_congr rfl (fun i _ => h.abs_eq i)
  rw [h_eq]; exact h.sum_le_one

/-- Under `IsProb`, `Σ |y_i| = Σ y_i` as an equation. -/
theorem IsProb.sum_abs_eq_sum {n : ℕ} {y : Fin n → FiniteFp}
    (h : IsProb (R := R) y) :
    (∑ i, |((y i).toVal : R)|) = ∑ i, ((y i).toVal : R) :=
  Finset.sum_congr rfl (fun i _ => h.abs_eq i)

/-- Per-index bound: each entry is ≤ 1.  Follows from `y_i ≤ Σ y_j ≤ 1`
using non-negativity of the other entries. -/
theorem IsProb.toVal_le_one {n : ℕ} {y : Fin n → FiniteFp}
    (h : IsProb (R := R) y) (i : Fin n) :
    ((y i).toVal : R) ≤ 1 := by
  have h_single : ((y i).toVal : R) ≤ ∑ j, ((y j).toVal : R) :=
    Finset.single_le_sum (f := fun j => ((y j).toVal : R))
      (fun j _ => h.nonneg j) (Finset.mem_univ i)
  exact le_trans h_single h.sum_le_one

/-! ## Generators (weaker tags) -/

/-- **Generator**: `IsProb y` → each entry is non-negative. -/
@[tag_generator]
theorem IsProb.toIsNonneg {n : ℕ} {y : Fin n → FiniteFp}
    (h : IsProb (R := R) y) (i : Fin n) :
    IsNonneg (R := R) (y i) :=
  ⟨h.nonneg i⟩

/-- **Generator**: `IsProb y` → each entry has magnitude ≤ 1. -/
@[tag_generator]
theorem IsProb.toHasAbsBound_one {n : ℕ} {y : Fin n → FiniteFp}
    (h : IsProb (R := R) y) (i : Fin n) :
    HasAbsBound (R := R) 1 (y i) := by
  refine ⟨?_⟩
  rw [h.abs_eq i]
  exact h.toVal_le_one i

/-! ## Ingress generators (stronger tags → IsProb) -/

/-- **Ingress**: `IsOneHot j y` → `IsProb y`.

The hot entry is `1`, every other is `0`; sum = 1 ≤ 1, entries
non-negative. -/
@[tag_generator]
theorem IsOneHot.toIsProb {n : ℕ} {j : Fin n} {y : Fin n → FiniteFp}
    (h : IsOneHot (R := R) j y) :
    IsProb (R := R) y where
  nonneg := h.toVal_nonneg
  sum_le_one := by
    have h_sum : (∑ i, ((y i).toVal : R)) = 1 := by
      rw [Finset.sum_eq_single j]
      · exact h.hot
      · intro i _ hij; exact h.cold i hij
      · intro hmem; exact absurd (Finset.mem_univ j) hmem
    rw [h_sum]

/-- **Ingress**: `IsSimplex ws` → `IsProb ws`.  Simplex entries
sum to 1 ≤ 1. -/
@[tag_generator]
theorem IsSimplex.toIsProb {n : ℕ} {ws : Fin n → FiniteFp}
    (h : IsSimplex (R := R) ws) :
    IsProb (R := R) ws where
  nonneg := h.nonneg
  sum_le_one := by rw [h.sum_one]

end Flean.Tags

/-! ## Tag-specialized cross-entropy bound

Under `IsProb ys`, CE's general bound becomes an **expectation** under
`ys` as a probability measure — the ML-natural framing.  Concretely,
`|y_i| = y_i` drops, and `Σ|y_i| ≤ 1` tames the weighted-sum
coefficient. -/

namespace CrossEntropy

open Finset BigOperators LogSumExp Softmax Flean.Tags

variable [FloatFormat] [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
  [RModeNearest ℝ] [RModeConj ℝ] [ExpApprox] [ExpApproxSound]

variable {n : ℕ}

/-- **Probability-distribution cross-entropy error bound**.

Under `IsProb ys`, CE's general bound reframes as an **expectation
under `ys`**:

```
|loss - CE| ≤ dp.relErr · Σ y_i · |r_i|
            + Σ y_i · (η·|x_i - lse| + subnormalConst + Δ_LSE)
```

The absolute values on `ys_i` drop (they equal `ys_i`), and the
weighted-sum structure is preserved.  Interpretation: the CE error is
bounded by the expected per-index errors, weighted by the target
probabilities. -/
theorem fpCrossEntropy_isProb_error_bound
    (hn : 0 < n)
    (xs : Fin n → FiniteFp)
    (ys : Fin n → FiniteFp)
    (h_prob : IsProb (R := ℝ) ys)
    (xs' : Fin n → FiniteFp)
    (h_shift_exact : ∀ k,
      ((xs' k).toVal : ℝ) = ((xs k).toVal : ℝ) - ((fpMax xs hn).toVal : ℝ))
    (exps : Fin n → FiniteFp)
    (h_exp : ∀ i, fpExpFinite (xs' i) = Fp.finite (exps i))
    (sum : FpSum.FpSumBound exps ℝ)
    (h_margin :
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst < 1)
    (logResult : FiniteFp) (η_log : ℝ) (h_η_log_nn : 0 ≤ η_log)
    (logSubConst : ℝ) (h_logSub_nn : 0 ≤ logSubConst)
    (h_log_close :
      |(logResult.toVal : ℝ) - Real.log ((sum.result.toVal : ℝ))| ≤
        η_log * |Real.log ((sum.result.toVal : ℝ))| + logSubConst)
    (lse : FiniteFp)
    (h_final_add : fpAddFinite (fpMax xs hn) logResult = Fp.finite lse)
    (h_final_ne : ((fpMax xs hn).toVal : ℝ) + logResult.toVal ≠ 0)
    (r : Fin n → FiniteFp)
    (h_shift_close : ∀ i,
      |((r i).toVal : ℝ) - (((xs i).toVal : ℝ) - (lse.toVal : ℝ))| ≤
        (η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst)
    (dp : FpDotProduct.FpDotProductBound ys r ℝ) :
    letI ε_sum : ℝ :=
      ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
        (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst
    letI D_log : ℝ := ε_sum / (1 - ε_sum)
    letI Δ_LSE : ℝ :=
      (η : ℝ) * |logsumexp (fun k => ((xs k).toVal : ℝ))| +
      (1 + (η : ℝ)) *
        (η_log *
            (logsumexp (fun k => ((xs k).toVal : ℝ)) -
              ((fpMax xs hn).toVal : ℝ)) +
          (1 + η_log) * D_log + logSubConst) +
      Softmax.subnormalConst
    |(((- dp.result).toVal : ℝ)) -
        crossEntropy (fun i => ((ys i).toVal : ℝ))
                     (fun i => ((xs i).toVal : ℝ))| ≤
      dp.relErr * ∑ i, ((ys i).toVal : ℝ) * |((r i).toVal : ℝ)| +
      ∑ i, ((ys i).toVal : ℝ) *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst + Δ_LSE) := by
  set ε_sum : ℝ :=
    ((η : ℝ) + sum.relErr * (1 + (η : ℝ))) +
      (1 + sum.relErr) * (n : ℝ) * Softmax.subnormalConst with hε_def
  set D_log : ℝ := ε_sum / (1 - ε_sum) with hDlog_def
  set Δ_LSE : ℝ :=
    (η : ℝ) * |logsumexp (fun k => ((xs k).toVal : ℝ))| +
    (1 + (η : ℝ)) *
      (η_log *
          (logsumexp (fun k => ((xs k).toVal : ℝ)) -
            ((fpMax xs hn).toVal : ℝ)) +
        (1 + η_log) * D_log + logSubConst) +
    Softmax.subnormalConst with hΔ_def
  have h_gen := fpCrossEntropy_end_to_end_error_bound hn xs ys
    xs' h_shift_exact exps h_exp sum h_margin
    logResult η_log h_η_log_nn logSubConst h_logSub_nn h_log_close
    lse h_final_add h_final_ne
    r h_shift_close dp
  simp only [← hε_def, ← hDlog_def, ← hΔ_def] at h_gen
  -- Drop the absolute values on ys_i.
  have h_dp_rewrite :
      (∑ i, |((ys i).toVal : ℝ) * ((r i).toVal : ℝ)|) =
        ∑ i, ((ys i).toVal : ℝ) * |((r i).toVal : ℝ)| := by
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, h_prob.abs_eq]
  have h_weighted_rewrite :
      (∑ i, |((ys i).toVal : ℝ)| *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst + Δ_LSE)) =
      (∑ i, ((ys i).toVal : ℝ) *
        ((η : ℝ) * |((xs i).toVal : ℝ) - (lse.toVal : ℝ)| +
          Softmax.subnormalConst + Δ_LSE)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h_prob.abs_eq]
  rw [h_dp_rewrite, h_weighted_rewrite] at h_gen
  exact h_gen

end CrossEntropy
