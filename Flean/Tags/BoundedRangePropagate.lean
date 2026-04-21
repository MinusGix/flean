import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Operations.FMA
import Flean.Operations.FpFiniteRound
import Flean.Rounding.ModeClass
import Flean.Rounding.RoundPreserves
import Flean.Tags.BoundedRange
import Flean.Tags.FpInterval

/-!
# Parametric propagation for `IsBoundedRange`

Per `.claude/notes/tag-framework-phase1-design.md` §1.4 / §3.4.

Propagation lemmas threading `IsBoundedRange I xs` through the
primitive FP ops `fpAddFinite` / `fpMulFinite` / `fpFMAFinite`.  The
input-interval bounds widen outward to absorb the rounding slack
contributed by the op.  The widened output interval is produced by
the operations in `Flean/Tags/FpInterval.lean` — this file provides
the semantic bridge from the interval-algebra definitions to actual
FP-primitive correctness.

## Reading the signatures

With the `FpInterval`-parametric tag, propagation reads as algebra:

```
theorem IsBoundedRange.fpMul_unified
    (hx : IsBoundedRange A (fun _ => x))
    (hy : IsBoundedRange B (fun _ => y))
    (hf : fpMulFinite x y = Fp.finite f) :
    IsBoundedRange (A ⊠ B) (fun _ => f)
```

Chained: `(A ⊞ B) ⊠ C` — the tag output of one theorem plugs straight
into the next theorem's input.  No `obtain` dance.

## Two regimes

- **Normal-range variants** (`IsBoundedRange.fp{Add,Mul,FMA}`) — take
  a `(2:R)^min_exp ≤ |exact|` hypothesis.  Output uses `fpAddN` /
  `fpMulN` / `fpFMAN` (no `sc` tail).
- **Unified / subnormal-tolerant variants**
  (`IsBoundedRange.fp{Add,Mul,FMA}_unified`) — drop the precondition;
  output uses `fpAdd` / `fpMul` / `fpFMA` (with `+ subnormalConst`
  tail).  See `demo_mul_mul_add_unified` for the hypothesis-shaving
  benefit on a 3-op chain.

## Scope

Sign-general inputs throughout — negative intervals go through
`RModeConj` inside the meta-lemmas.  No sign restriction on
`I.lo` / `I.hi` / `x.toVal`.
-/

set_option autoImplicit false

namespace Flean.Tags

open scoped Flean.Tags -- for ⊞ / ⊠

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Proof-closing macros

Two macros that capture the mechanical finale of every propagation
theorem: split `IsBoundedRange` into `.lower` / `.upper`, introduce the
`Fin 1` index, rewrite `(f.toVal : R)` to `(g.toVal : R)` via the
round-witness equality, then unfold the FpInterval op to close. -/

/-- Close both output-interval sub-goals when the bound comes from a
single `|g.toVal| ≤ ...` hypothesis (symmetric-around-0 intervals, as
for `fpMul` / `fpFMA`).  Usage:
```
close_interval_via_abs rw:hg_eq from:hg_abs_le unfolding FpInterval.fpMul
```
-/
macro "close_interval_via_abs"
    "rw:" hg_eq:term "from:" h_abs:term
    "unfolding" unfold_target:ident : tactic => `(tactic|(
  refine ⟨?_, ?_⟩
  · intro _
    rw [← $hg_eq]
    unfold $unfold_target
    exact (abs_le.mp $h_abs).1
  · intro _
    rw [← $hg_eq]
    unfold $unfold_target
    exact (abs_le.mp $h_abs).2))

/-- Close both output-interval sub-goals when the bound comes from a
`-slack ≤ g.toVal - s ∧ g.toVal - s ≤ slack` pair (asymmetric
intervals widened from an exact sum, as for `fpAdd`).  Usage:
```
close_interval_via_slack rw:hg_eq from:h_err_bounds unfolding FpInterval.fpAdd
```
-/
macro "close_interval_via_slack"
    "rw:" hg_eq:term "from:" h_pair:term
    "unfolding" unfold_target:ident : tactic => `(tactic|(
  refine ⟨?_, ?_⟩
  · intro _
    rw [← $hg_eq]
    unfold $unfold_target
    linarith [($h_pair).1]
  · intro _
    rw [← $hg_eq]
    unfold $unfold_target
    linarith [($h_pair).2]))

/-! ## `FpInterval` widening facts

The propagation signatures don't carry the outward-widening invariant
`(A ⊞ B).lo ≤ A.lo + B.lo` inline — the interval-arithmetic definition
already forces it.  For callers who need the invariants explicitly,
these lemmas pull them out. -/

omit [FloorRing R] in
theorem FpInterval.fpAddN_lo_le (A B : FpInterval R) :
    (A.fpAddN B).lo ≤ A.lo + B.lo := by
  unfold FpInterval.fpAddN
  have hη_nn : (0 : R) ≤ η := by positivity
  have hmax_nn : (0 : R) ≤ max |A.lo + B.lo| |A.hi + B.hi| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have : (0 : R) ≤ η * max |A.lo + B.lo| |A.hi + B.hi| :=
    mul_nonneg hη_nn hmax_nn
  linarith

omit [FloorRing R] in
theorem FpInterval.fpAddN_hi_ge (A B : FpInterval R) :
    A.hi + B.hi ≤ (A.fpAddN B).hi := by
  unfold FpInterval.fpAddN
  have hη_nn : (0 : R) ≤ η := by positivity
  have hmax_nn : (0 : R) ≤ max |A.lo + B.lo| |A.hi + B.hi| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have : (0 : R) ≤ η * max |A.lo + B.lo| |A.hi + B.hi| :=
    mul_nonneg hη_nn hmax_nn
  linarith

omit [FloorRing R] in
theorem FpInterval.fpAdd_lo_le (A B : FpInterval R) :
    (A ⊞ B).lo ≤ A.lo + B.lo := by
  unfold FpInterval.fpAdd
  have hη_nn : (0 : R) ≤ η := by positivity
  have hmax_nn : (0 : R) ≤ max |A.lo + B.lo| |A.hi + B.hi| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have hsc_nn : (0 : R) ≤ FpInterval.subnormalConst :=
    FpInterval.subnormalConst_nn
  have : (0 : R) ≤ η * max |A.lo + B.lo| |A.hi + B.hi| + FpInterval.subnormalConst :=
    add_nonneg (mul_nonneg hη_nn hmax_nn) hsc_nn
  linarith

omit [FloorRing R] in
theorem FpInterval.fpAdd_hi_ge (A B : FpInterval R) :
    A.hi + B.hi ≤ (A ⊞ B).hi := by
  unfold FpInterval.fpAdd
  have hη_nn : (0 : R) ≤ η := by positivity
  have hmax_nn : (0 : R) ≤ max |A.lo + B.lo| |A.hi + B.hi| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have hsc_nn : (0 : R) ≤ FpInterval.subnormalConst :=
    FpInterval.subnormalConst_nn
  have : (0 : R) ≤ η * max |A.lo + B.lo| |A.hi + B.hi| + FpInterval.subnormalConst :=
    add_nonneg (mul_nonneg hη_nn hmax_nn) hsc_nn
  linarith

/-! ## Addition propagation -/

/-- `IsBoundedRange` propagates through `fpAddFinite` in the normal-range
regime.  Output interval: `A.fpAddN B`. -/
theorem IsBoundedRange.fpAdd
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B : FpInterval R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) A (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) B (fun (_ : Fin 1) => y))
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) + y.toVal|)
    (hf : fpAddFinite x y = Fp.finite f) :
    IsBoundedRange (R := R) (A.fpAddN B) (fun (_ : Fin 1) => f) := by
  set s : R := (x.toVal : R) + y.toVal with hs_def
  set M : R := max |A.lo + B.lo| |A.hi + B.hi| with hM_def
  set slack : R := η * M with hslack_def
  have hs_lb : A.lo + B.lo ≤ s := by
    have h1 := hx.lower 0; have h2 := hy.lower 0
    simp only at h1 h2; linarith
  have hs_ub : s ≤ A.hi + B.hi := by
    have h1 := hx.upper 0; have h2 := hy.upper 0
    simp only at h1 h2; linarith
  have hs_abs_le_M : |s| ≤ M := by
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · rw [abs_of_nonneg hs_nn]
      exact le_trans (le_trans hs_ub (le_abs_self _)) (le_max_right _ _)
    · rw [abs_of_neg hs_neg]
      have : -s ≤ -(A.lo + B.lo) := neg_le_neg hs_lb
      exact le_trans (le_trans this (neg_le_abs _)) (le_max_left _ _)
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - s| ≤ η * |s| :=
    round_preserves_abs_error_normal h_normal hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have hM_nn : (0 : R) ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hslack_nn : (0 : R) ≤ slack := mul_nonneg hη_nn hM_nn
  have h_err_le_slack : |(g.toVal : R) - s| ≤ slack := by
    have hstep : η * |s| ≤ η * M := mul_le_mul_of_nonneg_left hs_abs_le_M hη_nn
    exact le_trans h_err hstep
  have h_err_bounds :
      -slack ≤ (g.toVal : R) - s ∧ (g.toVal : R) - s ≤ slack :=
    ⟨(abs_le.mp h_err_le_slack).1, (abs_le.mp h_err_le_slack).2⟩
  close_interval_via_slack rw:hg_eq from:h_err_bounds unfolding FpInterval.fpAddN

/-- `IsBoundedRange` propagates through `fpAddFinite`, subnormal-tolerant.
Output interval: `A ⊞ B`.  Drops the normal-range precondition in
exchange for the `+ sc` slack. -/
theorem IsBoundedRange.fpAdd_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B : FpInterval R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) A (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) B (fun (_ : Fin 1) => y))
    (hf : fpAddFinite x y = Fp.finite f) :
    IsBoundedRange (R := R) (A ⊞ B) (fun (_ : Fin 1) => f) := by
  set s : R := (x.toVal : R) + y.toVal with hs_def
  set M : R := max |A.lo + B.lo| |A.hi + B.hi| with hM_def
  set slack : R := η * M + FpInterval.subnormalConst with hslack_def
  have hs_lb : A.lo + B.lo ≤ s := by
    have h1 := hx.lower 0; have h2 := hy.lower 0
    simp only at h1 h2; linarith
  have hs_ub : s ≤ A.hi + B.hi := by
    have h1 := hx.upper 0; have h2 := hy.upper 0
    simp only at h1 h2; linarith
  have hs_abs_le_M : |s| ≤ M := by
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · rw [abs_of_nonneg hs_nn]
      exact le_trans (le_trans hs_ub (le_abs_self _)) (le_max_right _ _)
    · rw [abs_of_neg hs_neg]
      have : -s ≤ -(A.lo + B.lo) := neg_le_neg hs_lb
      exact le_trans (le_trans this (neg_le_abs _)) (le_max_left _ _)
  obtain ⟨g, hg_round, hg_eq⟩ := fpAddFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - s| ≤ η * |s| + FpInterval.subnormalConst :=
    round_preserves_abs_error_unified (R := R) s hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have hsc_nn : (0 : R) ≤ FpInterval.subnormalConst := FpInterval.subnormalConst_nn
  have hM_nn : (0 : R) ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hslack_nn : (0 : R) ≤ slack :=
    add_nonneg (mul_nonneg hη_nn hM_nn) hsc_nn
  have h_err_le_slack : |(g.toVal : R) - s| ≤ slack := by
    have hstep : η * |s| ≤ η * M := mul_le_mul_of_nonneg_left hs_abs_le_M hη_nn
    linarith
  have h_err_bounds :
      -slack ≤ (g.toVal : R) - s ∧ (g.toVal : R) - s ≤ slack :=
    ⟨(abs_le.mp h_err_le_slack).1, (abs_le.mp h_err_le_slack).2⟩
  close_interval_via_slack rw:hg_eq from:h_err_bounds unfolding FpInterval.fpAdd

/-! ## Subtraction propagation

`fpSubFinite` is defined as `fpAddFinite (·) (-·)`, so subtraction
propagation reduces to (1) negation propagation on the interval side
and (2) the existing addition propagation.  We expose both a
normal-range and a subnormal-tolerant variant. -/

omit [FloorRing R] in
/-- Negation preserves `IsBoundedRange`: the interval endpoints swap
sign (lo ↔ -hi, hi ↔ -lo). -/
theorem IsBoundedRange.neg {A : FpInterval R} {m : ℕ}
    {xs : Fin m → FiniteFp} (h : IsBoundedRange (R := R) A xs) :
    IsBoundedRange (R := R) A.neg (fun i => -(xs i)) := by
  refine ⟨?_, ?_⟩
  · intro i
    show (A.neg.lo : R) ≤ ((-(xs i)).toVal : R)
    rw [FpInterval.neg, FiniteFp.toVal_neg_eq_neg (R := R)]
    exact neg_le_neg (h.upper i)
  · intro i
    show ((-(xs i)).toVal : R) ≤ A.neg.hi
    rw [FpInterval.neg, FiniteFp.toVal_neg_eq_neg (R := R)]
    exact neg_le_neg (h.lower i)

/-- `IsBoundedRange` propagates through `fpSubFinite` in the normal-range
regime.  Output interval: `A.fpSubN B = A.fpAddN B.neg`. -/
theorem IsBoundedRange.fpSub
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B : FpInterval R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) A (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) B (fun (_ : Fin 1) => y))
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) - y.toVal|)
    (hf : fpSubFinite x y = Fp.finite f) :
    IsBoundedRange (R := R) (A.fpSubN B) (fun (_ : Fin 1) => f) := by
  have hy_neg : IsBoundedRange (R := R) B.neg (fun (_ : Fin 1) => -y) := hy.neg
  have hf_add : fpAddFinite x (-y) = Fp.finite f := hf
  have h_normal' : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) + (-y).toVal| := by
    rw [FiniteFp.toVal_neg_eq_neg (R := R)]
    convert h_normal using 2; ring
  exact IsBoundedRange.fpAdd hx hy_neg h_normal' hf_add

/-- `IsBoundedRange` propagates through `fpSubFinite`, subnormal-tolerant.
Output: `A ⊟ B`. -/
theorem IsBoundedRange.fpSub_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B : FpInterval R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) A (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) B (fun (_ : Fin 1) => y))
    (hf : fpSubFinite x y = Fp.finite f) :
    IsBoundedRange (R := R) (A ⊟ B) (fun (_ : Fin 1) => f) := by
  have hy_neg : IsBoundedRange (R := R) B.neg (fun (_ : Fin 1) => -y) := hy.neg
  have hf_add : fpAddFinite x (-y) = Fp.finite f := hf
  exact IsBoundedRange.fpAdd_unified hx hy_neg hf_add

/-! ## Multiplication propagation -/

/-- `IsBoundedRange` propagates through `fpMulFinite` in the normal-range
regime.  Output interval: `A.fpMulN B`. -/
theorem IsBoundedRange.fpMul
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B : FpInterval R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) A (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) B (fun (_ : Fin 1) => y))
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) * y.toVal|)
    (hf : fpMulFinite x y = Fp.finite f) :
    IsBoundedRange (R := R) (A.fpMulN B) (fun (_ : Fin 1) => f) := by
  set p : R := (x.toVal : R) * y.toVal with hp_def
  have hx_abs_le : |(x.toVal : R)| ≤ A.maxMag := hx.toVal_abs_le 0
  have hy_abs_le : |(y.toVal : R)| ≤ B.maxMag := hy.toVal_abs_le 0
  have hA_nn : (0 : R) ≤ A.maxMag := A.maxMag_nn
  have hB_nn : (0 : R) ≤ B.maxMag := B.maxMag_nn
  have hp_abs_le : |p| ≤ A.maxMag * B.maxMag := by
    rw [hp_def, abs_mul]
    exact mul_le_mul hx_abs_le hy_abs_le (abs_nonneg _) hA_nn
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - p| ≤ η * |p| :=
    round_preserves_abs_error_normal h_normal hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have hg_abs_le : |(g.toVal : R)| ≤ (1 + η) * (A.maxMag * B.maxMag) := by
    have h_step : |(g.toVal : R)| ≤ |g.toVal - p| + |p| := by
      have : |((g.toVal - p) + p : R)| ≤ |g.toVal - p| + |p| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - p| + |p| := h_step
      _ ≤ η * |p| + |p| := by linarith
      _ = (1 + η) * |p| := by ring
      _ ≤ (1 + η) * (A.maxMag * B.maxMag) :=
          mul_le_mul_of_nonneg_left hp_abs_le h1η_nn
  close_interval_via_abs rw:hg_eq from:hg_abs_le unfolding FpInterval.fpMulN

/-- `IsBoundedRange` propagates through `fpMulFinite`, subnormal-tolerant.
Output: `A ⊠ B`. -/
theorem IsBoundedRange.fpMul_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B : FpInterval R} {x y f : FiniteFp}
    (hx : IsBoundedRange (R := R) A (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) B (fun (_ : Fin 1) => y))
    (hf : fpMulFinite x y = Fp.finite f) :
    IsBoundedRange (R := R) (A ⊠ B) (fun (_ : Fin 1) => f) := by
  set p : R := (x.toVal : R) * y.toVal with hp_def
  have hx_abs_le : |(x.toVal : R)| ≤ A.maxMag := hx.toVal_abs_le 0
  have hy_abs_le : |(y.toVal : R)| ≤ B.maxMag := hy.toVal_abs_le 0
  have hA_nn : (0 : R) ≤ A.maxMag := A.maxMag_nn
  have hB_nn : (0 : R) ≤ B.maxMag := B.maxMag_nn
  have hsc_nn : (0 : R) ≤ FpInterval.subnormalConst := FpInterval.subnormalConst_nn
  have hp_abs_le : |p| ≤ A.maxMag * B.maxMag := by
    rw [hp_def, abs_mul]
    exact mul_le_mul hx_abs_le hy_abs_le (abs_nonneg _) hA_nn
  obtain ⟨g, hg_round, hg_eq⟩ := fpMulFinite_round_witness (R := R) x y hf
  have h_err : |(g.toVal : R) - p| ≤ η * |p| + FpInterval.subnormalConst :=
    round_preserves_abs_error_unified (R := R) p hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have hg_abs_le :
      |(g.toVal : R)| ≤ (1 + η) * (A.maxMag * B.maxMag) + FpInterval.subnormalConst := by
    have h_step : |(g.toVal : R)| ≤ |g.toVal - p| + |p| := by
      have : |((g.toVal - p) + p : R)| ≤ |g.toVal - p| + |p| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - p| + |p| := h_step
      _ ≤ (η * |p| + FpInterval.subnormalConst) + |p| := by linarith
      _ = (1 + η) * |p| + FpInterval.subnormalConst := by ring
      _ ≤ (1 + η) * (A.maxMag * B.maxMag) + FpInterval.subnormalConst := by
          have := mul_le_mul_of_nonneg_left hp_abs_le h1η_nn
          linarith
  close_interval_via_abs rw:hg_eq from:hg_abs_le unfolding FpInterval.fpMul

/-! ## FMA propagation -/

/-- `IsBoundedRange` propagates through `fpFMAFinite` in the normal-range
regime.  Output: `A.fpFMAN B C`. -/
theorem IsBoundedRange.fpFMA
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B C : FpInterval R} {a b c f : FiniteFp}
    (ha : IsBoundedRange (R := R) A (fun (_ : Fin 1) => a))
    (hb : IsBoundedRange (R := R) B (fun (_ : Fin 1) => b))
    (hc : IsBoundedRange (R := R) C (fun (_ : Fin 1) => c))
    (h_normal : (2 : R) ^ FloatFormat.min_exp ≤
                |(a.toVal : R) * b.toVal + c.toVal|)
    (hf : fpFMAFinite a b c = Fp.finite f) :
    IsBoundedRange (R := R) (A.fpFMAN B C) (fun (_ : Fin 1) => f) := by
  set e : R := (a.toVal : R) * b.toVal + c.toVal with he_def
  set M : R := A.maxMag * B.maxMag + C.maxMag with hM_def
  have ha_abs_le : |(a.toVal : R)| ≤ A.maxMag := ha.toVal_abs_le 0
  have hb_abs_le : |(b.toVal : R)| ≤ B.maxMag := hb.toVal_abs_le 0
  have hc_abs_le : |(c.toVal : R)| ≤ C.maxMag := hc.toVal_abs_le 0
  have hA_nn : (0 : R) ≤ A.maxMag := A.maxMag_nn
  have hB_nn : (0 : R) ≤ B.maxMag := B.maxMag_nn
  have hC_nn : (0 : R) ≤ C.maxMag := C.maxMag_nn
  have hM_nn : (0 : R) ≤ M := by rw [hM_def]; positivity
  have he_abs_le : |e| ≤ M := by
    have h_ab : |(a.toVal : R) * b.toVal| ≤ A.maxMag * B.maxMag := by
      rw [abs_mul]
      exact mul_le_mul ha_abs_le hb_abs_le (abs_nonneg _) hA_nn
    calc |e|
        = |(a.toVal : R) * b.toVal + c.toVal| := rfl
      _ ≤ |(a.toVal : R) * b.toVal| + |(c.toVal : R)| := abs_add_le _ _
      _ ≤ A.maxMag * B.maxMag + C.maxMag := add_le_add h_ab hc_abs_le
      _ = M := rfl
  obtain ⟨g, hg_round, hg_eq⟩ := fpFMAFinite_round_witness (R := R) a b c hf
  have h_err : |(g.toVal : R) - e| ≤ η * |e| :=
    round_preserves_abs_error_normal h_normal hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have hg_abs_le : |(g.toVal : R)| ≤ (1 + η) * M := by
    have h_step : |(g.toVal : R)| ≤ |g.toVal - e| + |e| := by
      have : |((g.toVal - e) + e : R)| ≤ |g.toVal - e| + |e| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - e| + |e| := h_step
      _ ≤ η * |e| + |e| := by linarith
      _ = (1 + η) * |e| := by ring
      _ ≤ (1 + η) * M := mul_le_mul_of_nonneg_left he_abs_le h1η_nn
  close_interval_via_abs rw:hg_eq from:hg_abs_le unfolding FpInterval.fpFMAN

/-- `IsBoundedRange` propagates through `fpFMAFinite`, subnormal-tolerant.
Output: `FpInterval.fpFMA A B C`. -/
theorem IsBoundedRange.fpFMA_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {A B C : FpInterval R} {a b c f : FiniteFp}
    (ha : IsBoundedRange (R := R) A (fun (_ : Fin 1) => a))
    (hb : IsBoundedRange (R := R) B (fun (_ : Fin 1) => b))
    (hc : IsBoundedRange (R := R) C (fun (_ : Fin 1) => c))
    (hf : fpFMAFinite a b c = Fp.finite f) :
    IsBoundedRange (R := R) (FpInterval.fpFMA A B C) (fun (_ : Fin 1) => f) := by
  set e : R := (a.toVal : R) * b.toVal + c.toVal with he_def
  set M : R := A.maxMag * B.maxMag + C.maxMag with hM_def
  have ha_abs_le : |(a.toVal : R)| ≤ A.maxMag := ha.toVal_abs_le 0
  have hb_abs_le : |(b.toVal : R)| ≤ B.maxMag := hb.toVal_abs_le 0
  have hc_abs_le : |(c.toVal : R)| ≤ C.maxMag := hc.toVal_abs_le 0
  have hA_nn : (0 : R) ≤ A.maxMag := A.maxMag_nn
  have hB_nn : (0 : R) ≤ B.maxMag := B.maxMag_nn
  have hC_nn : (0 : R) ≤ C.maxMag := C.maxMag_nn
  have hM_nn : (0 : R) ≤ M := by rw [hM_def]; positivity
  have hsc_nn : (0 : R) ≤ FpInterval.subnormalConst := FpInterval.subnormalConst_nn
  have he_abs_le : |e| ≤ M := by
    have h_ab : |(a.toVal : R) * b.toVal| ≤ A.maxMag * B.maxMag := by
      rw [abs_mul]
      exact mul_le_mul ha_abs_le hb_abs_le (abs_nonneg _) hA_nn
    calc |e|
        = |(a.toVal : R) * b.toVal + c.toVal| := rfl
      _ ≤ |(a.toVal : R) * b.toVal| + |(c.toVal : R)| := abs_add_le _ _
      _ ≤ A.maxMag * B.maxMag + C.maxMag := add_le_add h_ab hc_abs_le
      _ = M := rfl
  obtain ⟨g, hg_round, hg_eq⟩ := fpFMAFinite_round_witness (R := R) a b c hf
  have h_err : |(g.toVal : R) - e| ≤ η * |e| + FpInterval.subnormalConst :=
    round_preserves_abs_error_unified (R := R) e hg_round
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have hg_abs_le : |(g.toVal : R)| ≤ (1 + η) * M + FpInterval.subnormalConst := by
    have h_step : |(g.toVal : R)| ≤ |g.toVal - e| + |e| := by
      have : |((g.toVal - e) + e : R)| ≤ |g.toVal - e| + |e| := abs_add_le _ _
      convert this using 2; ring
    calc |(g.toVal : R)|
        ≤ |g.toVal - e| + |e| := h_step
      _ ≤ (η * |e| + FpInterval.subnormalConst) + |e| := by linarith
      _ = (1 + η) * |e| + FpInterval.subnormalConst := by ring
      _ ≤ (1 + η) * M + FpInterval.subnormalConst := by
          have := mul_le_mul_of_nonneg_left he_abs_le h1η_nn
          linarith
  close_interval_via_abs rw:hg_eq from:hg_abs_le unfolding FpInterval.fpFMA

/-! ## Demos: 3-op chains

See `IsBoundedRange.toVal_abs_le` (in `BoundedRange.lean`) for the
general magnitude corollary — apply it to any of the output intervals
below to get `|f.toVal| ≤ (output).maxMag`. -/

section Demo

/-- Normal-range 3-op chain `r = fpAdd (fpMul x y) (fpMul z w)` threads
`IsBoundedRange` through three explicit propagation calls — `obtain`-free. -/
theorem IsBoundedRange.demo_mul_mul_add
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {Ax Ay Az Aw : FpInterval R}
    {x y z w m₁ m₂ r : FiniteFp}
    (hx : IsBoundedRange (R := R) Ax (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) Ay (fun (_ : Fin 1) => y))
    (hz : IsBoundedRange (R := R) Az (fun (_ : Fin 1) => z))
    (hw : IsBoundedRange (R := R) Aw (fun (_ : Fin 1) => w))
    (h_xy_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(x.toVal : R) * y.toVal|)
    (h_zw_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(z.toVal : R) * w.toVal|)
    (h_sum_normal : (2 : R) ^ FloatFormat.min_exp ≤ |(m₁.toVal : R) + m₂.toVal|)
    (hm₁ : fpMulFinite x y = Fp.finite m₁)
    (hm₂ : fpMulFinite z w = Fp.finite m₂)
    (hr : fpAddFinite m₁ m₂ = Fp.finite r) :
    IsBoundedRange (R := R) ((Ax.fpMulN Ay).fpAddN (Az.fpMulN Aw))
      (fun (_ : Fin 1) => r) :=
  (IsBoundedRange.fpMul hx hy h_xy_normal hm₁).fpAdd
    (IsBoundedRange.fpMul hz hw h_zw_normal hm₂) h_sum_normal hr

/-- Same three-op chain, subnormal-tolerant.  All three normal-range
preconditions are gone — the unified variants absorb subnormal
rounding into per-step `sc` tails.  Output: `(Ax ⊠ Ay) ⊞ (Az ⊠ Aw)` —
interval arithmetic, read as written. -/
theorem IsBoundedRange.demo_mul_mul_add_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {Ax Ay Az Aw : FpInterval R}
    {x y z w m₁ m₂ r : FiniteFp}
    (hx : IsBoundedRange (R := R) Ax (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) Ay (fun (_ : Fin 1) => y))
    (hz : IsBoundedRange (R := R) Az (fun (_ : Fin 1) => z))
    (hw : IsBoundedRange (R := R) Aw (fun (_ : Fin 1) => w))
    (hm₁ : fpMulFinite x y = Fp.finite m₁)
    (hm₂ : fpMulFinite z w = Fp.finite m₂)
    (hr : fpAddFinite m₁ m₂ = Fp.finite r) :
    IsBoundedRange (R := R) ((Ax ⊠ Ay) ⊞ (Az ⊠ Aw))
      (fun (_ : Fin 1) => r) :=
  (IsBoundedRange.fpMul_unified hx hy hm₁).fpAdd_unified
    (IsBoundedRange.fpMul_unified hz hw hm₂) hr

/-- Two-FMA chain `r = fpFMA x y (fpFMA z w c)` computing
`x·y + z·w + c` in two rounding steps.  Output: `fpFMA Ax Ay (fpFMA Az Aw Ac)`. -/
theorem IsBoundedRange.demo_fma_chain_unified
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeZero R]
    {Ax Ay Az Aw Ac : FpInterval R}
    {x y z w c t r : FiniteFp}
    (hx : IsBoundedRange (R := R) Ax (fun (_ : Fin 1) => x))
    (hy : IsBoundedRange (R := R) Ay (fun (_ : Fin 1) => y))
    (hz : IsBoundedRange (R := R) Az (fun (_ : Fin 1) => z))
    (hw : IsBoundedRange (R := R) Aw (fun (_ : Fin 1) => w))
    (hc : IsBoundedRange (R := R) Ac (fun (_ : Fin 1) => c))
    (ht : fpFMAFinite z w c = Fp.finite t)
    (hr : fpFMAFinite x y t = Fp.finite r) :
    IsBoundedRange (R := R)
      (FpInterval.fpFMA Ax Ay (FpInterval.fpFMA Az Aw Ac))
      (fun (_ : Fin 1) => r) :=
  IsBoundedRange.fpFMA_unified hx hy
    (IsBoundedRange.fpFMA_unified hz hw hc ht) hr

end Demo

end Flean.Tags
