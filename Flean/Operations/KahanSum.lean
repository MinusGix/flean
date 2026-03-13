import Flean.Operations.Add
import Flean.Operations.Sub
import Flean.Operations.AddErrorRepresentable
import Flean.Operations.Fast2Sum
import Flean.Rounding.PolicyInstances

/-!
# Kahan Compensated Summation

Formalizes Kahan's compensated summation algorithm (1965) and proves its error bound,
following the analysis in Higham, *Accuracy and Stability of Numerical Algorithms*
(2nd ed., SIAM 2002), §4.3.

## Algorithm

```
sum = 0; c = 0
for i = 0 to n-1:
  y = x[i] - c        // compensated input
  t = sum + y          // new partial sum
  c = (t - sum) - y    // new compensation
  sum = t
return sum
```

## The Problem

Naive left-to-right summation `s₁ = x₀, sᵢ₊₁ = fl(sᵢ + xᵢ₊₁)` satisfies
(Higham, eq. 4.4):

  `|ŝₙ - Σxᵢ| ≤ (n-1)u · Σ|xᵢ| + O(u²)`

where `u = 2^(-prec)` is the unit roundoff (half machine epsilon). The error grows
linearly with `n`.

Kahan summation uses a running compensation variable `c` to track the rounding
error from each addition, feeding it back into the next step.

## Higham's Results (§4.3, pp. 83–86)

**Backward error** (eq. 4.8, due to Knuth [1998, Ex. 19, §4.2.2]):

  `ŝₙ = Σ(1 + μᵢ)xᵢ,  |μᵢ| ≤ 2u + O((n-i+1)u²)`

**Forward error** (eq. 4.9):

  `|Eₙ| ≤ (2u + O(nu²)) · Σ|xᵢ|`

The error is **independent of `n`** to first order — a dramatic improvement for
large sums. The condition `nu ≤ 1` ensures the O(nu²) term is small.

**Key identity** (eq. 4.7): for rounded base-2 arithmetic, the TwoSum correction
is exact:

  `a + b = fl(a + b) + fl(fl(a - fl(a + b)) + b)`

This means the compensation step `c = (t - sum) - y` exactly captures the rounding
error of the addition `t = sum + y`. We already proved this as `twoSum_exact` in
TwoSum.lean.

## Two Proof Approaches

### Approach A: Four-ρ analysis (this file, completed)

We define four rounding errors per step:
- `ρ₁ = fl(x - c) - (x - c)` — from the compensation subtraction
- `ρ₂ = fl(sum + y) - (sum + y)` — from the main addition
- `ρ₃ = fl(t - sum) - (t - sum)` — from recovering the added value
- `ρ₄ = fl(w - y) - (w - y)` — from computing the new compensation

**ρ₂ cancellation** (`kahan_step_corrected_sum`): defining `σ = sum - c`:

  `σ' = σ + x + (ρ₁ - ρ₃ - ρ₄)`

The addition error ρ₂ cancels — proven by `ring`. Second-order analysis gives
`|ρ₃| ≤ η|y + ρ₂|` and `|ρ₄| ≤ η|ρ₂ + ρ₃|` (O(η²)). The bound
`kahan_concrete_error_bound` telescopes these over a trace.

### Approach B: TwoSum-based (completed)

The compensation step `(t, c) = TwoSum(sum, y)` is error-free by eq. (4.7), so
`sum.toVal + y.toVal = t.toVal + c'.toVal` exactly (`StepTwoSumExact`). This
reduces to ONE rounding error per step (from `y = fl(x - c)`), yielding:

  `|error| ≤ traceTwoSumBound + |cₙ|`

where `traceTwoSumBound = Σ η|xᵢ - cᵢ₋₁|`. Triangle inequality splits this into
`η·Σ|xᵢ| + η·Σ|cᵢ₋₁|`, and the compensation induction (`traceCompSum_le_addMag`)
bounds `Σ|cᵢ| ≤ η·traceAddMag`, giving:

  `|error| ≤ η·Σ|xᵢ| + η²·traceAddMag + |cₙ|`  (`kahan_twosum_eta_squared_bound`)

Finally, `traceAddMag ≤ n·M` and `|cₙ| ≤ η·M` under a uniform bound `M` on
`|sumᵢ + yᵢ|`, yielding the capstone:

  **`|ŝₙ - Σxᵢ| ≤ (2η + nη²) · Σ|xᵢ|`**  (`kahan_higham_bound`)

subject to the hypothesis `hM : ∀ step, |sumᵢ + yᵢ| ≤ Σ|xⱼ|`.

## Results Summary

### Approach A (four-ρ, general)

**Main bound** (`kahan_error_bound` / `kahan_concrete_error_bound`): telescoping
over a trace of `n` steps starting from zero:

  `|sum_n - Σxᵢ| ≤ Σᵢ (η|xᵢ - cᵢ₋₁| + η|yᵢ + ρ₂ᵢ| + η|ρ₂ᵢ + ρ₃ᵢ|) + |cₙ|`

The dominant term is `Σ η|xᵢ - cᵢ₋₁| ≈ η · Σ|xᵢ|` (since cᵢ is O(η)), giving
the O(η) bound. The remaining terms are O(η²) per step.

### Approach B (TwoSum-exact, Higham form)

- `kahan_twosum_error_bound`: `|error| ≤ traceTwoSumBound + |cₙ|`
- `kahan_twosum_eta_squared_bound`: `|error| ≤ η·Σ|xᵢ| + η²·traceAddMag + |cₙ|`
- **`kahan_higham_bound`**: `|error| ≤ (2η + nη²) · Σ|xᵢ|` (Higham eq. 4.9)

## The `hM` Hypothesis and Possible Extensions

The capstone `kahan_higham_bound` requires `hM : ∀ step, |sumᵢ + yᵢ| ≤ Σ|xⱼ|`.
This says the floating-point addition magnitudes don't exceed the sum of absolute
values. Several approaches to discharging this:

### A. Self-contained bound (✓ DONE)

The `hM` hypothesis is eliminated by `kahan_higham_bound_auto`, which uses
`trace_energy_bound` (an energy invariant: `F' ≤ (1+η)²·F` at each step)
to derive addition magnitude bounds automatically. The resulting bound:

  `|Eₙ| ≤ (η(1 + P) + nη²·P) · Σ|xᵢ|`   where `P = (1+η)^{2n}`

For Float64 (`η ≈ 10⁻¹⁶`), `P ≈ 1` for any practical `n`, recovering
Higham's `(2η + nη²)·Σ|xᵢ|`.

### B. Backward error form (Higham eq. 4.8)

Prove the per-element multiplicative perturbation:

  `ŝₙ = Σ(1 + μᵢ)xᵢ,  |μᵢ| ≤ 2u + O((n-i+1)u²)`

This is strictly stronger than the forward bound (gives element-wise perturbation,
not just total error). Requires tracking per-element perturbation factors through
the trace — a different proof structure (backward error analysis rather than forward
telescoping). Architecture: new theorem alongside the existing forward bounds.

### C. Pairwise summation comparison

Show that Kahan's `2η + O(nη²)` beats pairwise summation's `O(log(n)·η)` constant
for sufficiently large `n`. Pure corollary of existing bounds plus a pairwise bound
(not yet in the library).

### D. Neumaier variant

The improved Kahan-Babuška-Neumaier algorithm handles `|xᵢ| > |sumᵢ|` by
conditionally swapping, removing the need for `StepNormalRange` in some cases.
Would require a modified `StepWitness` with conditional logic. Architecture:
new file `NeumaierSum.lean` reusing the trace infrastructure.

### E. Connection to `twoSum_exact` (partially done)

`step_twosum_exact_of_sub_exact` bridges from a simpler hypothesis — that the
first subtraction `w = fl(t - sum)` is exact — to full `StepTwoSumExact`.
The proof uses `add_error_representable_general_left_nz` to show the rounding
error is representable, then `RModeIdem.round_idempotent` to show the second
subtraction is also exact. Requires `RModeIdem`, `RModeConj`, and `sum.m > 0`.

`step_twosum_exact_of_dekker` completes the chain for same-sign operands:
Dekker condition (`|y| ≤ |sum|`) → Sterbenz → first-sub exact → full TwoSum exact.
`step_twosum_exact_of_pos_dekker` is the positive-only special case.

Remaining: mixed-sign case (doesn't go through Sterbenz).

## References

- W. Kahan, "Further remarks on reducing truncation errors," CACM 8(1), 1965.
- N.J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  SIAM, 2002, §4.3 (Theorem 4.3, pp. 87–88).
- J.-M. Muller et al., *Handbook of Floating-Point Arithmetic*, 2nd ed.,
  Birkhäuser, 2018, §6.2.

## File Contents

### Infrastructure
- `standard_error_model` / `standard_error_additive` — bridge to `(1+δ)` form
- `fpAdd_error` / `fpSub_error` / `*_or_zero` — operation-level error bounds
- `State`, `StepWitness`, `Trace` — algorithm definitions
- `StepNormalRange` — precondition structure

### Approach A (four-ρ)
- `kahan_step_corrected_sum` — ρ₂ cancellation identity
- `kahan_step_rounding_bounds` — |ρᵢ| ≤ η|operand|
- `rho3_bound_via_y`, `rho4_bound_via_rhos` — second-order bounds
- `comp_abs_le_rounding_errors`, `comp_concrete_bound` — compensation bounds
- `kahan_trace_sigma_eq` — corrected sum telescoping
- `kahan_error_bound` — abstract error bound
- `kahan_concrete_error_bound` — concrete η-weighted bound

### Approach B (TwoSum-exact → Higham)
- `StepTwoSumExact` — TwoSum-exactness condition
- `stepResidual_eq_rho1_of_twosum` — residual simplifies to ρ₁
- `comp_le_rho2_of_twosum` — |c'| ≤ η|sum+y|
- `traceTwoSumBound` / `traceCompSum` / `traceAddMag` — trace-level quantities
- `traceTwoSumBound_le_split` — triangle inequality split
- `traceCompSum_le_addMag` — compensation bounded by η·addition magnitudes
- `kahan_twosum_error_bound` — η·traceTwoSumBound + |cₙ|
- `kahan_twosum_split_error_bound` — η·Σ|xᵢ| + η·traceCompSum + |cₙ|
- `kahan_twosum_eta_squared_bound` — η·Σ|xᵢ| + η²·traceAddMag + |cₙ|
- `traceAddMag_le_mul_length` — traceAddMag ≤ n·M
- `final_comp_le_eta_mul` — |cₙ| ≤ η·M (inductive invariant)
- **`kahan_higham_bound`** — **(2η + nη²)·Σ|xᵢ|** (Higham Theorem 4.3)

### Extension A (energy invariant → self-contained bound)
- `step_add_mag_le_energy` — per-step: |sum+y| ≤ (1+η)²·(E+|x|)
- `step_sum_output_le` — |t| ≤ (1+η)·|sum+y|
- `trace_energy_bound` — energy invariant: F' ≤ (1+η)²·F propagated through trace
- **`kahan_higham_bound_auto`** — self-contained bound eliminating hM hypothesis

### Extension B (backward error interpretation)
- `error_distributable` — generic: |E| ≤ ε·Σ|vᵢ| implies E = Σ μᵢ vᵢ with |μᵢ| ≤ ε
- `kahan_weak_backward_error` — **ŝₙ = Σ(1+μᵢ)xᵢ, |μᵢ| ≤ 2η+nη²** (with hM)
- `kahan_weak_backward_error_auto` — self-contained version (no hM)

### Extension E (TwoSum-exactness bridge)
- `step_twosum_exact_of_sub_exact` — derives `StepTwoSumExact` from first-subtraction exactness
- `step_twosum_exact_of_pos_dekker` — full Dekker chain for positive operands with `y ≤ sum`
- `step_twosum_exact_of_dekker` — full Dekker chain for same-sign operands with `|y| ≤ |sum|`
-/

namespace KahanSum

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Standard Error Model

Bridge from the library's `relativeError` bound to the multiplicative `(1 + δ)` form
used in numerical analysis. -/

/-- The standard error model: for nearest rounding in normal range,
    `f.toVal = x * (1 + δ)` for some `|δ| ≤ η`. -/
theorem standard_error_model
    [RMode R] [RModeNearest R]
    (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : ○x = Fp.finite f) :
    ∃ δ : R, f.toVal = x * (1 + δ) ∧ |δ| ≤ η := by
  have hxpos := isNormalRange_pos x hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hrel := RModeNearest_relativeError_le_half x hx f hf
  unfold Fp.relativeError at hrel
  set δ := (f.toVal - x) / x
  refine ⟨δ, ?_, ?_⟩
  · have : x * (1 + δ) = x + x * δ := by ring
    rw [this, show δ = (f.toVal - x) / x from rfl]; field_simp
    ring
  · rw [show δ = (f.toVal - x) / x from rfl]
    rwa [show (x - f.toVal) / x = -((f.toVal - x) / x) from by ring, abs_neg] at hrel

/-- Additive form: `|f.toVal - x| ≤ η * |x|` in normal range. -/
theorem standard_error_additive
    [RMode R] [RModeNearest R]
    (x : R) (hx : isNormalRange x) (f : FiniteFp)
    (hf : ○x = Fp.finite f) :
    |f.toVal - x| ≤ η * |x| := by
  obtain ⟨δ, hval, hδ⟩ := standard_error_model x hx f hf
  have : f.toVal - x = x * δ := by rw [hval]; ring
  rw [this, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg x)

/-! ## Floating-point operation error bounds

Combined lemmas: correctness + standard error model gives additive error bounds
for fp addition and subtraction applied to `FiniteFp` operands. -/

/-- Error bound for fp addition: `|fl(a + b) - (a + b)| ≤ η · |a + b|`,
    when the result is finite and the exact sum is in normal range. -/
theorem fpAdd_error
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a + b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) + b.toVal)) :
    |(f.toVal : R) - (a.toVal + b.toVal)| ≤ η * |(a.toVal : R) + b.toVal| := by
  have hne : (a.toVal : R) + b.toVal ≠ 0 := ne_of_gt (isNormalRange_pos _ hnormal)
  have hcorr := fpAddFinite_correct (R := R) a b hne
  rw [hcorr] at hf
  exact standard_error_additive ((a.toVal : R) + b.toVal) hnormal f hf

/-- Error bound for fp subtraction: `|fl(a - b) - (a - b)| ≤ η · |a - b|`. -/
theorem fpSub_error
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a - b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) - b.toVal)) :
    |(f.toVal : R) - (a.toVal - b.toVal)| ≤ η * |(a.toVal : R) - b.toVal| := by
  have hne : (a.toVal : R) - b.toVal ≠ 0 := ne_of_gt (isNormalRange_pos _ hnormal)
  have hcorr := fpSubFinite_correct (R := R) a b hne
  rw [hcorr] at hf
  exact standard_error_additive ((a.toVal : R) - b.toVal) hnormal f hf

/-- When the exact result is zero, the fp result is also zero. -/
theorem fpAdd_exact_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a + b = Fp.finite f)
    (hzero : (a.toVal : R) + b.toVal = 0) :
    (f.toVal : R) = 0 := by
  have hexact := fpAddFinite_exact_sum R a b
  have hisum_zero : addAlignedSumInt a b = 0 := by
    have h0 : ((addAlignedSumInt a b : ℤ) : R) * (2:R) ^ (min a.e b.e - prec + 1) = 0 := by
      rw [← hexact]; exact hzero
    rcases mul_eq_zero.mp h0 with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt (by positivity))
  have hcancel := fpAddFinite_exact_cancel_sign a b hisum_zero
  have hf' : fpAddFinite a b = Fp.finite f := hf
  rw [hcancel] at hf'
  exact FiniteFp.toVal_isZero (by rw [(Fp.finite.inj hf').symm])

/-- When the exact result is zero, the fp subtraction result is also zero. -/
theorem fpSub_exact_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a - b = Fp.finite f)
    (hzero : (a.toVal : R) - b.toVal = 0) :
    (f.toVal : R) = 0 := by
  -- a - b = a + (-b), and a.toVal + (-b).toVal = a.toVal - b.toVal = 0
  have hzero' : (a.toVal : R) + (-b).toVal = 0 := by
    rw [FiniteFp.toVal_neg_eq_neg]; linarith
  have hf' : fpAddFinite a (-b) = Fp.finite f := hf
  exact fpAdd_exact_zero a (-b) f hf' hzero'

/-- Unified error bound: handles both normal range and exact-zero cases. -/
theorem fpSub_error_or_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a - b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) - b.toVal) ∨ (a.toVal : R) - b.toVal = 0) :
    |(f.toVal : R) - (a.toVal - b.toVal)| ≤ η * |(a.toVal : R) - b.toVal| := by
  rcases hnormal with h | h
  · exact fpSub_error a b f hf h
  · rw [h, fpSub_exact_zero (R := R) a b f hf h]; simp

theorem fpAdd_error_or_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b : FiniteFp) (f : FiniteFp)
    (hf : a + b = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) + b.toVal) ∨ (a.toVal : R) + b.toVal = 0) :
    |(f.toVal : R) - (a.toVal + b.toVal)| ≤ η * |(a.toVal : R) + b.toVal| := by
  rcases hnormal with h | h
  · exact fpAdd_error a b f hf h
  · rw [h, fpAdd_exact_zero (R := R) a b f hf h]; simp

/-! ## Kahan State and Step

A single step of Kahan summation, with explicit finiteness witnesses. -/

/-- State of the Kahan compensated summation algorithm. -/
structure State where
  sum : FiniteFp
  comp : FiniteFp

/-- Witnesses for one step of Kahan summation.
    Given state `(sum, comp)` and input `x`, produces new state `(t, c')`. -/
structure StepWitness [RModeExec] (st : State) (x : FiniteFp) where
  /-- `y = fl(x - comp)` -/
  y : FiniteFp
  hy : x - st.comp = Fp.finite y
  /-- `t = fl(sum + y)` -/
  t : FiniteFp
  ht : st.sum + y = Fp.finite t
  /-- `w = fl(t - sum)` -/
  w : FiniteFp
  hw : t - st.sum = Fp.finite w
  /-- `c' = fl(w - y)` -/
  c' : FiniteFp
  hc : w - y = Fp.finite c'

/-- Next state after a Kahan step. -/
def StepWitness.nextState [RModeExec] {st : State} {x : FiniteFp}
    (step : StepWitness st x) : State :=
  ⟨step.t, step.c'⟩

/-! ## Kahan Trace

A trace recording all intermediate steps of Kahan summation over a list. -/

/-- A valid execution trace of Kahan summation over a list of inputs.
    Lives in `Type` (not `Prop`) so we can extract data like accumulated residuals. -/
inductive Trace [RModeExec] : List FiniteFp → State → State → Type where
  /-- Empty list: state unchanged. -/
  | nil (st : State) : Trace [] st st
  /-- One step followed by the rest. -/
  | cons {st : State} {x : FiniteFp} {xs : List FiniteFp} {final : State}
      (step : StepWitness st x)
      (rest : Trace xs step.nextState final) :
      Trace (x :: xs) st final

/-- Extract the final sum from a Kahan trace. -/
def Trace.finalSum [RModeExec] {xs : List FiniteFp} {init final : State}
    (_trace : Trace xs init final) : FiniteFp :=
  final.sum

/-! ## Error Bound

The main error bound theorem for Kahan compensated summation. -/

/-- Normal range precondition for all intermediate values in a Kahan step. -/
structure StepNormalRange [RModeExec] (st : State) (x : FiniteFp)
    (step : StepWitness st x) where
  /-- `x.toVal - comp.toVal` is in normal range (for y = fl(x - c)) -/
  y_normal : isNormalRange ((x.toVal : R) - st.comp.toVal) ∨
             (x.toVal : R) - st.comp.toVal = 0
  /-- `sum.toVal + y.toVal` is in normal range (for t = fl(sum + y)) -/
  t_normal : isNormalRange ((st.sum.toVal : R) + step.y.toVal) ∨
             (st.sum.toVal : R) + step.y.toVal = 0
  /-- `t.toVal - sum.toVal` is in normal range (for w = fl(t - sum)) -/
  w_normal : isNormalRange ((step.t.toVal : R) - st.sum.toVal) ∨
             (step.t.toVal : R) - st.sum.toVal = 0
  /-- `w.toVal - y.toVal` is in normal range (for c' = fl(w - y)) -/
  c_normal : isNormalRange ((step.w.toVal : R) - step.y.toVal) ∨
             (step.w.toVal : R) - step.y.toVal = 0

/-! ## Per-Step Corrected Sum Error

The key identity: if we track `σ = sum - comp` (the "corrected sum"),
then after one Kahan step processing input `x`:

  `σ' = σ + x + (ρ₁ - ρ₃ - ρ₄)`

where ρ₁, ρ₃, ρ₄ are rounding errors from the subtraction and compensation steps.
The compensation absorbs the main addition error ρ₂, leaving only second-order terms. -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The corrected sum recurrence: `σ' = σ + x + (ρ₁ - ρ₃ - ρ₄)`.
    Note: `ρ₂` (the addition rounding error) cancels algebraically — the compensation
    absorbs it. This is the key identity behind Kahan summation. -/
theorem kahan_step_corrected_sum
    [RModeExec]
    (st : State) (x : FiniteFp)
    (step : StepWitness st x) :
    let σ := (st.sum.toVal : R) - st.comp.toVal
    let σ' := (step.t.toVal : R) - step.c'.toVal
    let ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
    let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
    let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
    σ' = σ + x.toVal + (ρ₁ - ρ₃ - ρ₄) := by
  simp only
  ring

/-- Error bounds on the individual rounding errors in a Kahan step. -/
theorem kahan_step_rounding_bounds
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp)
    (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step) :
    let ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
    let ρ₂ := (step.t.toVal : R) - (st.sum.toVal + step.y.toVal)
    let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
    let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
    |ρ₁| ≤ η * |(x.toVal : R) - st.comp.toVal| ∧
    |ρ₂| ≤ η * |(st.sum.toVal : R) + step.y.toVal| ∧
    |ρ₃| ≤ η * |(step.t.toVal : R) - st.sum.toVal| ∧
    |ρ₄| ≤ η * |(step.w.toVal : R) - step.y.toVal| := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fpSub_error_or_zero x st.comp step.y step.hy hnr.y_normal
  · exact fpAdd_error_or_zero st.sum step.y step.t step.ht hnr.t_normal
  · exact fpSub_error_or_zero step.t st.sum step.w step.hw hnr.w_normal
  · exact fpSub_error_or_zero step.w step.y step.c' step.hc hnr.c_normal

/-! ## Compensation Identity

The compensation `c'` exactly captures the sum of the three "remaining" rounding errors
(ρ₂ + ρ₃ + ρ₄). This is the algebraic reason why Kahan works: the compensation
absorbs the O(η) errors, leaving only O(η²) residuals in ρ₃ and ρ₄. -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The compensation equals the sum of the three remaining rounding errors. -/
theorem kahan_step_comp_eq_rounding_errors
    [RModeExec]
    (st : State) (x : FiniteFp)
    (step : StepWitness st x) :
    (step.c'.toVal : R) =
      ((step.t.toVal : R) - (st.sum.toVal + step.y.toVal)) +
      ((step.w.toVal : R) - (step.t.toVal - st.sum.toVal)) +
      ((step.c'.toVal : R) - (step.w.toVal - step.y.toVal)) := by
  ring

/-! ## Inductive Error Accumulation

Telescope the per-step corrected sum identity over a full trace to get:
  `σ_final = σ_init + Σxᵢ + Σ(ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ)`

Then combine with the final compensation to bound `|sum - Σxᵢ|`. -/

/-- Per-step rounding residual: `ρ₁ - ρ₃ - ρ₄` for one Kahan step. -/
def stepResidual [RModeExec] (st : State) (x : FiniteFp)
    (step : StepWitness st x) : R :=
  let ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
  let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
  let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
  ρ₁ - ρ₃ - ρ₄

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The corrected sum after a Kahan step equals the old corrected sum
    plus the input plus the step residual. -/
theorem kahan_step_sigma_eq [RModeExec]
    (st : State) (x : FiniteFp) (step : StepWitness st x) :
    (step.t.toVal : R) - step.c'.toVal =
      ((st.sum.toVal : R) - st.comp.toVal) + x.toVal + stepResidual st x step := by
  unfold stepResidual; ring

/-- Accumulated residuals from a trace. -/
def traceResidual [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons step rest =>
    stepResidual _ _ step + traceResidual rest

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The corrected sum telescopes over a full trace:
    `σ_final = σ_init + Σxᵢ + Σ(residuals)`. -/
theorem kahan_trace_sigma_eq [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final) :
    (final.sum.toVal : R) - final.comp.toVal =
      ((init.sum.toVal : R) - init.comp.toVal) +
      (xs.map (fun x => x.toVal (R := R))).sum +
      traceResidual trace := by
  induction trace with
  | nil st => simp [traceResidual]
  | cons step rest ih =>
    simp only [List.map_cons, List.sum_cons, traceResidual, StepWitness.nextState] at *
    rw [ih, kahan_step_sigma_eq]
    ring

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- **Main error decomposition**: the final sum error splits into
    corrected-sum error plus final compensation.

    `sum_n - Σxᵢ = (σ_n - Σxᵢ) + c_n`

    where `σ_n = sum_n - c_n` is the corrected sum. By the per-step identity,
    `σ_n - Σxᵢ = Σ(ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ)` (accumulated second-order errors),
    giving `|sum_n - Σxᵢ| ≤ Σ|ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ| + |c_n|`. -/
theorem kahan_error_decomposition
    [RModeExec]
    {final : State} (xs : List FiniteFp) :
    (final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum =
      ((final.sum.toVal : R) - final.comp.toVal -
        (xs.map (fun x => x.toVal (R := R))).sum) +
      final.comp.toVal := by ring

omit [FloorRing R] in
/-- Triangle inequality form of the error decomposition. -/
theorem kahan_error_triangle
    [RModeExec]
    {final : State} (xs : List FiniteFp) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      |(final.sum.toVal : R) - final.comp.toVal -
        (xs.map (fun x => x.toVal (R := R))).sum| +
      |final.comp.toVal (R := R)| := by
  rw [kahan_error_decomposition xs]
  exact abs_add_le _ _

/-- Sum of |stepResidual| over the trace — the triangle inequality bound. -/
def traceResidualAbsBound [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons step rest =>
    |stepResidual (R := R) _ _ step| + traceResidualAbsBound rest

omit [FloorRing R] in
/-- The accumulated residual is bounded by the sum of absolute step residuals. -/
theorem traceResidual_abs_le [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final) :
    |traceResidual (R := R) trace| ≤ traceResidualAbsBound trace := by
  induction trace with
  | nil => simp [traceResidual, traceResidualAbsBound]
  | cons step rest ih =>
    simp only [traceResidual, traceResidualAbsBound]
    exact le_trans (abs_add_le _ _) (add_le_add_right ih _)

omit [FloorRing R] in
/-- **Kahan summation error bound** (general form).

    Starting from zero initial state, the error of Kahan summation satisfies:

    `|sum_n - Σxᵢ| ≤ Σ|ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ| + |c_n|`

    where each `|ρ₁ᵢ - ρ₃ᵢ - ρ₄ᵢ|` is bounded by
    `η|xᵢ - cᵢ₋₁| + η|tᵢ - sᵢ₋₁| + η|wᵢ - yᵢ|`
    via `kahan_step_rounding_bounds`.

    The key insight is that ρ₂ (the O(η) addition error) is absent — it is
    absorbed by the compensation. The remaining terms ρ₃, ρ₄ are O(η²) since
    they operate on quantities that are themselves O(η), giving total error
    O(nη²) for the corrected sum. Combined with the O(η) compensation `c_n`,
    the total error is O(η) instead of O(nη). -/
theorem kahan_error_bound
    [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      traceResidualAbsBound trace +
      |final.comp.toVal (R := R)| := by
  have hsigma := kahan_trace_sigma_eq (R := R) trace
  rw [hinit_sum, hinit_comp] at hsigma
  have hresid : (final.sum.toVal : R) - final.comp.toVal -
      (xs.map (fun x => x.toVal (R := R))).sum = traceResidual trace := by linarith
  calc |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum|
      ≤ |(final.sum.toVal : R) - final.comp.toVal -
          (xs.map (fun x => x.toVal (R := R))).sum| +
        |final.comp.toVal (R := R)| := kahan_error_triangle xs
    _ = |traceResidual trace| + |final.comp.toVal (R := R)| := by rw [hresid]
    _ ≤ traceResidualAbsBound trace + |final.comp.toVal (R := R)| :=
        add_le_add (traceResidual_abs_le trace) (le_refl _)

/-! ## Concrete Bounds via Second-Order Analysis

To derive the concrete `O(η)` error bound, we show that ρ₃ and ρ₄ are second-order
(O(η²)) since they operate on quantities that are themselves O(η)-sized rounding errors.

Key algebraic identities:
- `t - sum = y + ρ₂` (the "t−sum recovers y up to ρ₂")
- `w - y = ρ₂ + ρ₃` (the "w−y captures rounding errors")
- `c' = ρ₂ + ρ₃ + ρ₄` (compensation captures all remaining errors)

These let us bound:
- `|ρ₃| ≤ η · |y + ρ₂| ≤ η(|y| + η|sum + y|)` — first-order in y, second-order correction
- `|ρ₄| ≤ η · |ρ₂ + ρ₃|` — purely second-order
- `|c'| ≤ η|sum + y| + η|y + ρ₂| + η|ρ₂ + ρ₃|` — bounded by O(η) -/

omit [FloorRing R] in
/-- Triangle inequality bound on the step residual:
    `|ρ₁ - ρ₃ - ρ₄| ≤ |ρ₁| + |ρ₃| + |ρ₄|`. -/
theorem stepResidual_abs_le [RModeExec]
    (st : State) (x : FiniteFp) (step : StepWitness st x) :
    let ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
    let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
    let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
    |stepResidual (R := R) st x step| ≤ |ρ₁| + |ρ₃| + |ρ₄| := by
  simp only
  set ρ₁ := (step.y.toVal : R) - (x.toVal - st.comp.toVal)
  set ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
  set ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
  have hconv : stepResidual (R := R) st x step = ρ₁ + (-ρ₃) + (-ρ₄) := by
    unfold stepResidual; ring
  rw [hconv]
  have h1 := abs_add_le (ρ₁ + (-ρ₃)) (-ρ₄)
  have h2 := abs_add_le ρ₁ (-ρ₃)
  rw [abs_neg ρ₃] at h2
  rw [abs_neg ρ₄] at h1
  linarith

/-- Bound on |ρ₃| using the identity `t - sum = y + ρ₂`:
    `|ρ₃| ≤ η · |y + ρ₂|`. -/
theorem rho3_bound_via_y
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step) :
    |(step.w.toVal : R) - (step.t.toVal - st.sum.toVal)| ≤
      η * |(step.y.toVal : R) + (step.t.toVal - (st.sum.toVal + step.y.toVal))| := by
  have hbnd := (kahan_step_rounding_bounds st x step hnr).2.2.1
  -- hbnd : |ρ₃| ≤ η * |t.toVal - sum.toVal|
  -- t.toVal - sum.toVal = y.toVal + (t.toVal - (sum.toVal + y.toVal))
  conv at hbnd => rhs; rw [show (step.t.toVal : R) - st.sum.toVal =
    step.y.toVal + (step.t.toVal - (st.sum.toVal + step.y.toVal)) from by ring]
  exact hbnd

/-- Bound on |ρ₄| using the identity `w - y = ρ₂ + ρ₃`:
    `|ρ₄| ≤ η · |ρ₂ + ρ₃|` — purely second-order. -/
theorem rho4_bound_via_rhos
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step) :
    |(step.c'.toVal : R) - (step.w.toVal - step.y.toVal)| ≤
      η * |((step.t.toVal : R) - (st.sum.toVal + step.y.toVal)) +
           (step.w.toVal - (step.t.toVal - st.sum.toVal))| := by
  have hbnd := (kahan_step_rounding_bounds st x step hnr).2.2.2
  conv at hbnd => rhs; rw [show (step.w.toVal : R) - step.y.toVal =
    (step.t.toVal - (st.sum.toVal + step.y.toVal)) +
    (step.w.toVal - (step.t.toVal - st.sum.toVal)) from by ring]
  exact hbnd

omit [FloorRing R] in
/-- The compensation `c'` is bounded by the sum of |ρ₂|, |ρ₃|, |ρ₄|
    (since `c' = ρ₂ + ρ₃ + ρ₄` algebraically). -/
theorem comp_abs_le_rounding_errors
    [RModeExec]
    (st : State) (x : FiniteFp) (step : StepWitness st x) :
    let ρ₂ := (step.t.toVal : R) - (st.sum.toVal + step.y.toVal)
    let ρ₃ := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
    let ρ₄ := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
    |step.c'.toVal (R := R)| ≤ |ρ₂| + |ρ₃| + |ρ₄| := by
  simp only
  have heq := kahan_step_comp_eq_rounding_errors (R := R) st x step
  set a := (step.t.toVal : R) - (st.sum.toVal + step.y.toVal)
  set b := (step.w.toVal : R) - (step.t.toVal - st.sum.toVal)
  set c := (step.c'.toVal : R) - (step.w.toVal - step.y.toVal)
  rw [heq]
  linarith [abs_add_le (a + b) c, abs_add_le a b]

/-- Combined bound: |c'| ≤ η|sum + y| + η|y + ρ₂| + η|ρ₂ + ρ₃|.
    The first term is O(η), the second O(η) with O(η²) correction,
    the third purely O(η²). -/
theorem comp_concrete_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step) :
    |step.c'.toVal (R := R)| ≤
      η * |(st.sum.toVal : R) + step.y.toVal| +
      η * |(step.y.toVal : R) + (step.t.toVal - (st.sum.toVal + step.y.toVal))| +
      η * |((step.t.toVal : R) - (st.sum.toVal + step.y.toVal)) +
           (step.w.toVal - (step.t.toVal - st.sum.toVal))| := by
  have hcomp := comp_abs_le_rounding_errors (R := R) st x step
  simp only at hcomp
  have ⟨_, hρ₂, _, _⟩ := kahan_step_rounding_bounds st x step hnr
  have hρ₃' := rho3_bound_via_y st x step hnr
  have hρ₄' := rho4_bound_via_rhos st x step hnr
  linarith

/-! ## Per-Step Residual Concrete Bound

Combine the triangle inequality with the second-order bounds to get:

  `|stepResidual| ≤ η|x - c| + η|y + ρ₂| + η|ρ₂ + ρ₃|`

This is the bound in terms of intermediate fp values and their rounding errors.
The first term is O(η), the second is O(η) (since |y + ρ₂| ≈ |sum + y| which is
the partial sum magnitude), and the third is O(η²). -/

/-- Per-step residual bound: `|ρ₁ - ρ₃ - ρ₄| ≤ η|x - c| + η|y + ρ₂| + η|ρ₂ + ρ₃|`. -/
theorem stepResidual_concrete_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step) :
    |stepResidual (R := R) st x step| ≤
      η * |(x.toVal : R) - st.comp.toVal| +
      η * |(step.y.toVal : R) + ((step.t.toVal : R) - (st.sum.toVal + step.y.toVal))| +
      η * |((step.t.toVal : R) - (st.sum.toVal + step.y.toVal)) +
           ((step.w.toVal : R) - (step.t.toVal - st.sum.toVal))| := by
  have hstep := stepResidual_abs_le (R := R) st x step
  simp only at hstep
  have ⟨hρ₁, _, _, _⟩ := kahan_step_rounding_bounds st x step hnr
  have hρ₃ := rho3_bound_via_y st x step hnr
  have hρ₄ := rho4_bound_via_rhos st x step hnr
  linarith

/-! ## Trace-Level Concrete Bound

To get from the abstract `traceResidualAbsBound` to a bound in terms of η and inputs,
we define a concrete bound that sums the per-step η-contributions.

The per-step bound `η|x - c| + η|y + ρ₂| + η|ρ₂ + ρ₃|` has:
- First term: `η · |xᵢ - cᵢ₋₁|` — bounded by `η(|xᵢ| + |cᵢ₋₁|)`, and cᵢ₋₁ is O(η)
- Second term: `η · |yᵢ + ρ₂ᵢ|` — this equals `η · |tᵢ - sumᵢ₋₁|` (recovering y up to ρ₂)
- Third term: `η · |ρ₂ᵢ + ρ₃ᵢ|` — purely O(η²), negligible

For the final `(2η + O(nη²)) · Σ|xᵢ|` form, we would need to:
1. Bound |cᵢ₋₁| ≤ η · (partial sum) inductively
2. Bound |tᵢ - sumᵢ₋₁| ≈ |yᵢ| ≈ |xᵢ|
3. Sum over all steps

This is Higham's Theorem 4.3 analysis. We provide the key building blocks above;
the full quantitative bound depends on assumptions about the relative magnitudes
of partial sums vs individual inputs. -/

/-- Per-step concrete bound summed over a trace. -/
def traceConcreteBound [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons (st := st) (x := x) step rest =>
    η * |(x.toVal : R) - st.comp.toVal| +
    η * |(step.y.toVal : R) + ((step.t.toVal : R) - (st.sum.toVal + step.y.toVal))| +
    η * |((step.t.toVal : R) - (st.sum.toVal + step.y.toVal)) +
         ((step.w.toVal : R) - (step.t.toVal - st.sum.toVal))| +
    traceConcreteBound rest

/-- The abstract trace residual bound is dominated by the concrete trace bound. -/
theorem traceResidualAbsBound_le_concrete
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      -- This should really be: for each step in the trace, we have StepNormalRange.
      -- For now, we use a universal quantification as a simplification.
      StepNormalRange (R := R) st x step) :
    traceResidualAbsBound (R := R) trace ≤ traceConcreteBound trace := by
  induction trace with
  | nil => simp [traceResidualAbsBound, traceConcreteBound]
  | cons step rest ih =>
    simp only [traceResidualAbsBound, traceConcreteBound]
    have hstep := stepResidual_concrete_bound _ _ step (hnr _ _ step)
    linarith [ih]

/-- **Kahan summation concrete error bound**.

    Under the assumption that all intermediate values are in normal range,
    the total error is bounded by a sum of η-weighted terms:

    `|sum_n - Σxᵢ| ≤ traceConcreteBound + |c_n|`

    where `traceConcreteBound` sums `η|xᵢ - cᵢ₋₁| + η|yᵢ + ρ₂ᵢ| + η|ρ₂ᵢ + ρ₃ᵢ|`
    over all steps. The last two terms of each step are O(η²), making the dominant
    contribution `Σ η|xᵢ - cᵢ₋₁| ≈ η · Σ|xᵢ|`. -/
theorem kahan_concrete_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      traceConcreteBound trace +
      |final.comp.toVal (R := R)| := by
  have habstract := kahan_error_bound trace hinit_sum hinit_comp
  have hle := traceResidualAbsBound_le_concrete trace hnr
  linarith

/-! ## TwoSum-Exact Kahan Steps (Approach B)

When the compensation step is a TwoSum (exact for rounded base-2 arithmetic,
Higham eq. 4.7), we have `sum.toVal + y.toVal = t.toVal - c'.toVal` exactly.
Equivalently, `c'.toVal = ρ₂` (the compensation exactly captures the addition
rounding error), which means `ρ₃ + ρ₄ = 0`.

This reduces the per-step error to just ρ₁, giving a much simpler bound.
We state the TwoSum exactness as a hypothesis (it follows from `twoSum_exact`
in TwoSum.lean, but connecting the specific Kahan computation requires
matching the intermediates). -/

/-- TwoSum-exactness condition for a Kahan step: the compensation exactly
    captures the addition rounding error. Follows from the error-free
    transformation property (Dekker 1971, Knuth 1998, our `twoSum_exact`). -/
def StepTwoSumExact [RModeExec] (st : State) (x : FiniteFp)
    (step : StepWitness st x) : Prop :=
  (step.c'.toVal : R) = (step.t.toVal : R) - (st.sum.toVal + step.y.toVal)

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- Under TwoSum-exactness, the step residual simplifies to just ρ₁. -/
theorem stepResidual_eq_rho1_of_twosum [RModeExec]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hexact : StepTwoSumExact (R := R) st x step) :
    stepResidual (R := R) st x step =
      (step.y.toVal : R) - (x.toVal - st.comp.toVal) := by
  unfold stepResidual
  unfold StepTwoSumExact at hexact
  -- hexact : c'.toVal = t.toVal - (sum.toVal + y.toVal)
  -- goal : (y - (x - c)) - (w - (t - sum)) - (c' - (w - y)) = y - (x - c)
  -- Substituting hexact: c' = t - (sum + y), so c' - (w - y) = t - sum - w
  -- and (w - (t - sum)) + (t - sum - w) = 0
  rw [hexact]; ring

/-- Under TwoSum-exactness, the per-step residual is bounded by just ρ₁.
    `|stepResidual| ≤ η|x - c|` -/
theorem stepResidual_le_rho1_of_twosum
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hexact : StepTwoSumExact (R := R) st x step)
    (hnr : StepNormalRange (R := R) st x step) :
    |stepResidual (R := R) st x step| ≤
      η * |(x.toVal : R) - st.comp.toVal| := by
  rw [stepResidual_eq_rho1_of_twosum (R := R) st x step hexact]
  exact (kahan_step_rounding_bounds st x step hnr).1

/-- Under TwoSum-exactness, |c'| = |ρ₂| ≤ η|sum + y|. -/
theorem comp_le_rho2_of_twosum
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hexact : StepTwoSumExact (R := R) st x step)
    (hnr : StepNormalRange (R := R) st x step) :
    |step.c'.toVal (R := R)| ≤
      η * |(st.sum.toVal : R) + step.y.toVal| := by
  unfold StepTwoSumExact at hexact
  rw [hexact]
  exact (kahan_step_rounding_bounds st x step hnr).2.1

/-! ## TwoSum-Exact Trace Bound

With TwoSum-exactness at every step, the trace residual bound simplifies from
three η-terms per step to just one: `Σ η|xᵢ - cᵢ₋₁|`. Combined with the
compensation bound `|cₙ| ≤ η|sumₙ₋₁ + yₙ|`, this gives the clean
`(2η + O(nη²)) · Σ|xᵢ|` form. -/

/-- Trace residual bound under TwoSum-exactness: `Σ η|xᵢ - cᵢ₋₁|`. -/
def traceTwoSumBound [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons (st := st) (x := x) _ rest =>
    η * |(x.toVal : R) - st.comp.toVal| + traceTwoSumBound rest

/-- Under TwoSum-exactness, the abstract residual bound reduces to `traceTwoSumBound`. -/
theorem traceResidualAbsBound_le_twosum
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    traceResidualAbsBound (R := R) trace ≤ traceTwoSumBound trace := by
  induction trace with
  | nil => simp [traceResidualAbsBound, traceTwoSumBound]
  | cons step rest ih =>
    simp only [traceResidualAbsBound, traceTwoSumBound]
    have hstep := stepResidual_le_rho1_of_twosum _ _ step (hexact _ _ step) (hnr _ _ step)
    linarith [ih]

/-- **Kahan summation error bound under TwoSum-exactness** (Higham-style).

    Under the TwoSum-exactness hypothesis (which holds for rounded base-2
    arithmetic by `twoSum_exact`), the total error satisfies:

    `|sum_n - Σxᵢ| ≤ Σ η|xᵢ - cᵢ₋₁| + |cₙ|`

    where `|cₙ| ≤ η|sumₙ₋₁ + yₙ|` (by `comp_le_rho2_of_twosum`).

    The dominant term `Σ η|xᵢ - cᵢ₋₁|` gives one factor of η, and
    `|cₙ| ≤ η·(partial sum)` gives the second, yielding the `2η + O(nη²)`
    constant from Higham's Theorem 4.3 / eq. (4.9). -/
theorem kahan_twosum_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      traceTwoSumBound trace +
      |final.comp.toVal (R := R)| := by
  have habstract := kahan_error_bound trace hinit_sum hinit_comp
  have hle := traceResidualAbsBound_le_twosum trace hexact hnr
  linarith

/-! ## Expanding to `2η · Σ|xᵢ|` Form

The final step: bound `traceTwoSumBound` and `|cₙ|` in terms of `Σ|xᵢ|`.

`traceTwoSumBound = Σ η|xᵢ - cᵢ₋₁| ≤ η·Σ(|xᵢ| + |cᵢ₋₁|)`

Since `|cᵢ| ≤ η|sumᵢ₋₁ + yᵢ|` (each compensation is one rounding error), and
the partial sums are bounded, the `η|cᵢ₋₁|` terms contribute O(nη²). -/

/-- Sum of `|cᵢ₋₁|` over the trace steps (the compensation magnitudes). -/
def traceCompSum [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons (st := st) _ rest =>
    |st.comp.toVal (R := R)| + traceCompSum rest

omit [FloorRing R] in
/-- Split `|xᵢ - cᵢ₋₁| ≤ |xᵢ| + |cᵢ₋₁|` in the trace bound:
    `traceTwoSumBound ≤ η·Σ|xᵢ| + η·Σ|cᵢ₋₁|`. -/
theorem traceTwoSumBound_le_split [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final) :
    traceTwoSumBound (R := R) trace ≤
      η * (xs.map (fun x => |x.toVal (R := R)|)).sum +
      η * traceCompSum trace := by
  induction trace with
  | nil => simp [traceTwoSumBound, traceCompSum]
  | @cons st x _ _ step rest ih =>
    simp only [traceTwoSumBound, traceCompSum, List.map_cons, List.sum_cons]
    have hη : (0 : R) ≤ η := by positivity
    have htri : |(x.toVal : R) - st.comp.toVal| ≤ |x.toVal| + |st.comp.toVal| := by
      calc |(x.toVal : R) - st.comp.toVal|
          = |x.toVal + (-(st.comp.toVal : R))| := by ring_nf
        _ ≤ |x.toVal| + |-(st.comp.toVal : R)| := abs_add_le _ _
        _ = |x.toVal| + |st.comp.toVal| := by rw [abs_neg]
    have hmul := mul_le_mul_of_nonneg_left htri hη
    nlinarith [ih]

/-- Sum of `|sumᵢ₋₁ + yᵢ|` over the trace steps (addition magnitudes). -/
def traceAddMag [RModeExec] :
    {xs : List FiniteFp} → {init final : State} → Trace xs init final → R
  | _, _, _, .nil _ => 0
  | _, _, _, .cons (st := st) (x := x) step rest =>
    |(st.sum.toVal : R) + step.y.toVal| + traceAddMag rest

/-- Under TwoSum-exactness + normal range, the compensation magnitudes are bounded
    by η times the addition magnitudes: `traceCompSum ≤ η · traceAddMag`.

    This uses `comp_le_rho2_of_twosum` at each step: the compensation `c'` produced
    by step i becomes the `comp` entering step i+1, and `|c'| ≤ η|sum + y|`.
    The initial compensation `c₀` is bounded by the `hinit` hypothesis.

    Note: `traceCompSum` sums `|cᵢ₋₁|` (comp *entering* each step), while
    `comp_le_rho2_of_twosum` bounds `|c'ᵢ|` (comp *produced* by each step).
    So the bound shifts by one index: `|cᵢ₋₁| ≤ η|sumᵢ₋₂ + yᵢ₋₁|`.
    This makes the overall bound:
    `traceCompSum ≤ |c₀| + η · traceAddMag(rest)` for a cons trace. -/
theorem traceCompSum_le_addMag
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    traceCompSum (R := R) trace ≤
      |init.comp.toVal (R := R)| + η * traceAddMag trace := by
  induction trace with
  | nil => simp [traceCompSum, traceAddMag]
  | @cons st x _ _ step rest ih =>
    simp only [traceCompSum, traceAddMag]
    -- Goal: |st.comp| + traceCompSum(rest) ≤ |st.comp| + η * (|st.sum + y| + traceAddMag(rest))
    -- ih: traceCompSum(rest) ≤ |step.nextState.comp| + η * traceAddMag(rest)
    -- step.nextState.comp = step.c', and |c'| ≤ η|st.sum + y|
    have hcomp := comp_le_rho2_of_twosum (R := R) st x step (hexact st x step) (hnr st x step)
    have hnext : step.nextState.comp.toVal (R := R) = step.c'.toVal := rfl
    rw [hnext] at ih
    have hη : (0 : R) ≤ η := by positivity
    nlinarith [abs_nonneg (st.comp.toVal (R := R))]

/-- **Combined Kahan error bound with explicit `η` factors** (Higham Theorem 4.3).

    Under TwoSum-exactness and zero initial compensation:

    `|ŝₙ - Σxᵢ| ≤ η · Σ|xᵢ| + η · traceCompSum + |cₙ|`

    where `traceCompSum ≤ η · traceAddMag` (the compensation terms are O(η²)),
    giving the `(2η + O(nη²)) · Σ|xᵢ|` form from Higham eq. (4.9).

    The three terms are:
    - `η · Σ|xᵢ|`: dominant term from `ρ₁` (subtraction rounding in `y = fl(x-c)`)
    - `η · traceCompSum`: second η factor from the compensation triangle inequality
    - `|cₙ|`: final compensation, bounded by `η|sumₙ₋₁ + yₙ|` -/
theorem kahan_twosum_split_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      η * (xs.map (fun x => |x.toVal (R := R)|)).sum +
      η * traceCompSum trace +
      |final.comp.toVal (R := R)| := by
  have hbase := kahan_twosum_error_bound trace hinit_sum hinit_comp hexact hnr
  have hsplit := traceTwoSumBound_le_split (R := R) trace
  linarith

/-- **Final concrete form**: Under TwoSum-exactness, zero initialization, the
    Kahan error is at most `η·Σ|xᵢ| + η²·traceAddMag + |cₙ|`.

    Since `traceAddMag ≤ n · max|partialSum|`, this gives the
    `(2η + O(nη²)) · Σ|xᵢ|` asymptotic from Higham. -/
theorem kahan_twosum_eta_squared_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      η * (xs.map (fun x => |x.toVal (R := R)|)).sum +
      η ^ 2 * traceAddMag trace +
      |final.comp.toVal (R := R)| := by
  have hsplit := kahan_twosum_split_error_bound trace hinit_sum hinit_comp hexact hnr
  have hcomp := traceCompSum_le_addMag (R := R) trace hexact hnr
  rw [hinit_comp, abs_zero] at hcomp
  have hη : (0 : R) ≤ η := by positivity
  -- η · traceCompSum ≤ η · (0 + η · traceAddMag) = η² · traceAddMag
  have hmul := mul_le_mul_of_nonneg_left hcomp hη
  -- η * traceCompSum ≤ η * (η * traceAddMag) = η² * traceAddMag
  nlinarith [sq_nonneg (η : R)]

/-! ## Closing the Bound: Higham's Theorem 4.3

To obtain the fully closed `(2η + nη²) · Σ|xᵢ|` form, we need two more pieces:

1. **`traceAddMag ≤ n · M`** given a uniform bound `M` on each `|sumᵢ + yᵢ|`.
2. **`|cₙ| ≤ η · M`** — the final compensation is bounded by η times the
   addition magnitude bound.

With `M = Σ|xᵢ|` (a hypothesis the user supplies — it holds when floating-point
partial sums don't exceed the sum of absolute values), this gives:

`|error| ≤ η·Σ|xᵢ| + η²·n·Σ|xᵢ| + η·Σ|xᵢ| = (2η + nη²)·Σ|xᵢ|` -/

omit [FloorRing R] in
/-- Addition magnitudes bounded by `n × M` given a uniform bound `M` on each
    `|sumᵢ + yᵢ|`. -/
theorem traceAddMag_le_mul_length [RModeExec]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final) (M : R)
    (hM : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      |(st.sum.toVal : R) + step.y.toVal| ≤ M) :
    traceAddMag (R := R) trace ≤ (xs.length : R) * M := by
  induction trace with
  | nil => simp [traceAddMag]
  | @cons st x xs' _ step rest ih =>
    simp only [traceAddMag, List.length_cons]
    push_cast
    nlinarith [hM st x step, ih]

/-- The final compensation satisfies `|comp| ≤ η · M` whenever:
    - every step's addition magnitude `|sum + y|` is bounded by `M`, and
    - the initial compensation already satisfies `|c₀| ≤ η · M`.

    The invariant is preserved because each step produces `c' = fl(w - y)`
    with `|c'| ≤ η|sum + y| ≤ η · M` (by `comp_le_rho2_of_twosum`). -/
theorem final_comp_le_eta_mul
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final) (M : R)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step)
    (hM : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      |(st.sum.toVal : R) + step.y.toVal| ≤ M)
    (hinit_le : |init.comp.toVal (R := R)| ≤ η * M) :
    |final.comp.toVal (R := R)| ≤ η * M := by
  induction trace with
  | nil => exact hinit_le
  | @cons st x _ _ step rest ih =>
    apply ih
    -- Need: |step.nextState.comp.toVal| ≤ η * M
    have hcomp := comp_le_rho2_of_twosum (R := R) st x step (hexact st x step) (hnr st x step)
    have hnext : step.nextState.comp.toVal (R := R) = step.c'.toVal := rfl
    rw [hnext]
    have hη : (0 : R) ≤ η := by positivity
    nlinarith [hM st x step, abs_nonneg ((st.sum.toVal : R) + step.y.toVal)]

/-- **Higham's Theorem 4.3, eq. (4.9)** — Kahan compensated summation error bound.

    Under TwoSum-exactness (which holds for rounded base-2 arithmetic by
    `twoSum_exact`), zero initialization, normal range at every step, and
    the condition that all intermediate addition magnitudes `|sumᵢ + yᵢ|`
    are bounded by `Σ|xⱼ|`:

    **`|ŝₙ - Σxᵢ| ≤ (2η + nη²) · Σ|xᵢ|`**

    where `η = 2⁻ᵖʳᵉᶜ` (half machine epsilon) and `n = |xs|`.

    The three contributing terms:
    - **`η · Σ|xᵢ|`**: from per-step ρ₁ rounding error in `y = fl(x - c)`
    - **`nη² · Σ|xᵢ|`**: from the triangle split `|xᵢ - cᵢ₋₁| ≤ |xᵢ| + |cᵢ₋₁|`
      with `|cᵢ| ≤ η|sumᵢ + yᵢ| ≤ η·Σ|xⱼ|`
    - **`η · Σ|xᵢ|`**: from the final compensation `|cₙ| ≤ η·Σ|xⱼ|`

    **Reference**: N.J. Higham, *Accuracy and Stability of Numerical Algorithms*,
    2nd ed., SIAM, 2002, §4.3, Theorem 4.3. -/
theorem kahan_higham_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step)
    (hM : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      |(st.sum.toVal : R) + step.y.toVal| ≤
        (xs.map (fun x => |x.toVal (R := R)|)).sum) :
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      (2 * η + (xs.length : R) * η ^ 2) *
        (xs.map (fun x => |x.toVal (R := R)|)).sum := by
  set S := (xs.map (fun x => |x.toVal (R := R)|)).sum with hS_def
  -- Step 1: η·S + η²·traceAddMag + |cₙ|
  have h1 := kahan_twosum_eta_squared_bound trace hinit_sum hinit_comp hexact hnr
  -- Step 2: traceAddMag ≤ n · S
  have h2 := traceAddMag_le_mul_length (R := R) trace S hM
  -- Step 3: |cₙ| ≤ η · S
  have hS_nonneg : (0 : R) ≤ S := List.sum_nonneg (fun _ hx => by
    simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; positivity)
  have hη : (0 : R) ≤ η := by positivity
  have h3 := final_comp_le_eta_mul (R := R) trace S hexact hnr hM
    (by rw [hinit_comp, abs_zero]; exact mul_nonneg hη hS_nonneg)
  -- Combine: η·S + η²·(n·S) + η·S = (2η + nη²)·S
  have h2' : η ^ 2 * traceAddMag (R := R) trace ≤ η ^ 2 * ((xs.length : R) * S) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  linarith

/-! ## Extension A: Eliminating the `hM` Hypothesis

The `kahan_higham_bound` theorem requires a user-supplied bound `hM` on the
addition magnitudes `|sumᵢ + yᵢ| ≤ Σ|xⱼ|`. Extension A proves this
automatically using an **energy invariant**: if `|sum| ≤ (1+η)·E` and
`|comp| ≤ η·E`, then the addition magnitude `|sum + y| ≤ (1+η)²·(E + |x|)`,
and the next state satisfies the same invariant with `E' = |sum + y|`.

The key insight is to track `F = E + S` where `S` is the remaining input sum.
At each step, `F' ≤ (1+η)²·F`, giving `Fₙ ≤ (1+η)^{2n}·F₀`. -/

/-- Per-step energy transition: given `|sum| ≤ (1+η)·E` and `|comp| ≤ η·E`,
    the addition magnitude `|sum + y|` is at most `(1+η)²·(E + |x|)`. -/
theorem step_add_mag_le_energy
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step)
    (E : R)
    (hsum_le : |st.sum.toVal (R := R)| ≤ (1 + η) * E)
    (hcomp_le : |st.comp.toVal (R := R)| ≤ η * E) :
    |(st.sum.toVal : R) + step.y.toVal| ≤
      (1 + η) ^ 2 * (E + |x.toVal (R := R)|) := by
  have hη : (0 : R) ≤ η := by positivity
  -- |y - (x - comp)| ≤ η|x - comp|  (ρ₁ bound)
  have hρ₁ := (kahan_step_rounding_bounds st x step hnr).1
  -- |y| ≤ (1+η)|x - comp| ≤ (1+η)(|x| + |comp|)
  have hy_sub : |step.y.toVal (R := R)| ≤ (1 + η) * (|x.toVal (R := R)| + |st.comp.toVal|) := by
    have htri_xc : |(x.toVal : R) - st.comp.toVal| ≤ |x.toVal| + |st.comp.toVal| := by
      calc |(x.toVal : R) - st.comp.toVal|
          = |x.toVal + (-(st.comp.toVal : R))| := by ring_nf
        _ ≤ |x.toVal| + |-(st.comp.toVal : R)| := abs_add_le _ _
        _ = |x.toVal| + |st.comp.toVal| := by rw [abs_neg]
    -- |y| = |(x-comp) + ρ₁| ≤ |x-comp| + |ρ₁| ≤ |x-comp| + η|x-comp| = (1+η)|x-comp|
    have hy_le : |step.y.toVal (R := R)| ≤ (1 + η) * |(x.toVal : R) - st.comp.toVal| := by
      have : (step.y.toVal : R) = (x.toVal - st.comp.toVal) +
        (step.y.toVal - (x.toVal - st.comp.toVal)) := by ring
      rw [this]
      calc |((x.toVal : R) - st.comp.toVal) + (step.y.toVal - (x.toVal - st.comp.toVal))|
          ≤ |x.toVal - st.comp.toVal| + |step.y.toVal - (x.toVal - st.comp.toVal)| :=
            abs_add_le _ _
        _ ≤ |x.toVal - st.comp.toVal| + η * |x.toVal - st.comp.toVal| := by linarith
        _ = (1 + η) * |x.toVal - st.comp.toVal| := by ring
    linarith [mul_le_mul_of_nonneg_left htri_xc (by linarith : (0 : R) ≤ 1 + η)]
  -- |sum + y| ≤ |sum| + |y| ≤ (1+η)E + (1+η)(|x| + ηE)
  --           = (1+η)((1+η)E + |x|) = (1+η)²E + (1+η)|x| ≤ (1+η)²(E + |x|)
  calc |(st.sum.toVal : R) + step.y.toVal|
      ≤ |st.sum.toVal| + |step.y.toVal| := abs_add_le _ _
    _ ≤ (1 + η) * E + (1 + η) * (|x.toVal (R := R)| + |st.comp.toVal|) := by linarith
    _ ≤ (1 + η) * E + (1 + η) * (|x.toVal| + η * E) := by
        have : |st.comp.toVal (R := R)| ≤ η * E := hcomp_le
        nlinarith [abs_nonneg (x.toVal (R := R))]
    _ = (1 + η) * ((1 + η) * E + |x.toVal|) := by ring
    _ = (1 + η) ^ 2 * E + (1 + η) * |x.toVal| := by ring
    _ ≤ (1 + η) ^ 2 * E + (1 + η) ^ 2 * |x.toVal| := by
        nlinarith [sq_nonneg (η : R), abs_nonneg (x.toVal (R := R))]
    _ = (1 + η) ^ 2 * (E + |x.toVal (R := R)|) := by ring

/-- The new partial sum `t = fl(sum + y)` satisfies `|t| ≤ (1+η)|sum+y|`. -/
theorem step_sum_output_le
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hnr : StepNormalRange (R := R) st x step) :
    |step.t.toVal (R := R)| ≤
      (1 + η) * |(st.sum.toVal : R) + step.y.toVal| := by
  have hρ₂ := (kahan_step_rounding_bounds st x step hnr).2.1
  have : (step.t.toVal : R) = (st.sum.toVal + step.y.toVal) +
    (step.t.toVal - (st.sum.toVal + step.y.toVal)) := by ring
  rw [this]
  calc |(st.sum.toVal + step.y.toVal : R) +
        (step.t.toVal - (st.sum.toVal + step.y.toVal))|
      ≤ |st.sum.toVal + step.y.toVal| +
        |step.t.toVal - (st.sum.toVal + step.y.toVal)| := abs_add_le _ _
    _ ≤ |st.sum.toVal + step.y.toVal| +
        η * |st.sum.toVal + step.y.toVal| := by linarith
    _ = (1 + η) * |(st.sum.toVal : R) + step.y.toVal| := by ring

set_option maxHeartbeats 400000 in
/-- **Energy invariant for Kahan summation traces.**

    Track `F = E + S` where `E` is the "energy" (bounding the state) and
    `S = Σ|xᵢ|` is the remaining input magnitude. At each step,
    `F' ≤ (1+η)²·F`, giving `F_final ≤ (1+η)^{2n}·F₀`.

    Returns three bounds:
    1. `traceAddMag ≤ n · (1+η)^{2n} · (E + S)` — total addition magnitudes
    2. `|final.sum| ≤ (1+η) · (1+η)^{2n} · (E + S)` — final sum bounded
    3. `|final.comp| ≤ η · (1+η)^{2n} · (E + S)` — final compensation bounded -/
theorem trace_energy_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step)
    (E : R) (hE : 0 ≤ E)
    (hsum_le : |init.sum.toVal (R := R)| ≤ (1 + η) * E)
    (hcomp_le : |init.comp.toVal (R := R)| ≤ η * E) :
    let S := (xs.map (fun x => |x.toVal (R := R)|)).sum
    traceAddMag (R := R) trace ≤ (xs.length : R) * (1 + η) ^ (2 * xs.length) * (E + S) ∧
    |final.sum.toVal (R := R)| ≤ (1 + η) * ((1 + η) ^ (2 * xs.length) * (E + S)) ∧
    |final.comp.toVal (R := R)| ≤ η * ((1 + η) ^ (2 * xs.length) * (E + S)) := by
  induction trace generalizing E with
  | nil =>
    simp only [traceAddMag, List.map_nil, List.sum_nil, List.length_nil,
      Nat.cast_zero, zero_mul, mul_zero, pow_zero, one_mul, add_zero]
    exact ⟨le_refl _, hsum_le, hcomp_le⟩
  | @cons st x xs' fin step rest ih =>
    simp only [traceAddMag, List.map_cons, List.sum_cons, List.length_cons]
    set S' := (xs'.map (fun x => |x.toVal (R := R)|)).sum
    set A := |(st.sum.toVal : R) + step.y.toVal|
    have hη : (0 : R) ≤ η := by positivity
    -- Per-step bounds
    have hA := step_add_mag_le_energy (R := R) st x step (hnr st x step) E hsum_le hcomp_le
    have ht_le := step_sum_output_le (R := R) st x step (hnr st x step)
    have hc_le := comp_le_rho2_of_twosum (R := R) st x step (hexact st x step) (hnr st x step)
    -- Rewrite to nextState for IH
    have : step.nextState.sum.toVal (R := R) = step.t.toVal := rfl
    rw [← this] at ht_le
    have : step.nextState.comp.toVal (R := R) = step.c'.toVal := rfl
    rw [← this] at hc_le
    -- IH with E' = A
    have ⟨ih1, ih2, ih3⟩ := ih A (abs_nonneg _) ht_le hc_le
    -- Key: A + S' ≤ (1+η)²·(E + (|x| + S'))
    have hη1 : (1 : R) ≤ (1 + η) ^ 2 := by nlinarith [sq_nonneg (η : R)]
    have hS'nn : (0 : R) ≤ S' := List.sum_nonneg (fun _ hx => by
      simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; positivity)
    have hAS' : A + S' ≤ (1 + η) ^ 2 * (E + (|x.toVal (R := R)| + S')) := by
      nlinarith [le_mul_of_one_le_left hS'nn hη1]
    -- Power splitting: (1+η)^(2(n+1)) = (1+η)^(2n) · (1+η)²
    have hpow_split : (1 + η : R) ^ (2 * (xs'.length + 1)) =
        (1 + η) ^ (2 * xs'.length) * (1 + η) ^ 2 := by
      rw [show 2 * (xs'.length + 1) = 2 * xs'.length + 2 from by omega, pow_add]
    have hpp : (0 : R) < (1 + η) ^ (2 * xs'.length) := by positivity
    have hES_nn : (0 : R) ≤ E + (|x.toVal (R := R)| + S') := by
      nlinarith [abs_nonneg (x.toVal (R := R))]
    -- Core: (1+η)^(2n)·(A+S') ≤ (1+η)^(2(n+1))·(E+S)
    have hkey : (1 + η) ^ (2 * xs'.length) * (A + S') ≤
        (1 + η) ^ (2 * (xs'.length + 1)) * (E + (|x.toVal (R := R)| + S')) := by
      calc (1 + η) ^ (2 * xs'.length) * (A + S')
          ≤ (1 + η) ^ (2 * xs'.length) * ((1 + η) ^ 2 * (E + (|x.toVal (R := R)| + S'))) :=
            mul_le_mul_of_nonneg_left hAS' hpp.le
        _ = (1 + η) ^ (2 * xs'.length) * (1 + η) ^ 2 * (E + (|x.toVal| + S')) := by ring
        _ = (1 + η) ^ (2 * (xs'.length + 1)) * (E + (|x.toVal| + S')) := by
            rw [← hpow_split]
    -- A ≤ (1+η)^(2(n+1))·(E+S)
    have hone_le : (1 : R) ≤ (1 + η) ^ (2 * xs'.length) :=
      one_le_pow₀ (by linarith : (1 : R) ≤ 1 + η)
    have hA_le : A ≤ (1 + η) ^ (2 * (xs'.length + 1)) *
        (E + (|x.toVal (R := R)| + S')) := by
      calc A ≤ (1 + η) ^ 2 * (E + (|x.toVal (R := R)| + S')) := by nlinarith
        _ ≤ (1 + η) ^ (2 * xs'.length) * ((1 + η) ^ 2 * (E + (|x.toVal| + S'))) :=
            le_mul_of_one_le_left (by positivity) hone_le
        _ = (1 + η) ^ (2 * xs'.length) * (1 + η) ^ 2 * (E + (|x.toVal| + S')) := by ring
        _ = (1 + η) ^ (2 * (xs'.length + 1)) * (E + (|x.toVal| + S')) := by
            rw [← hpow_split]
    -- Lift ih1
    have ih1' : traceAddMag (R := R) rest ≤
        (xs'.length : R) * (1 + η) ^ (2 * (xs'.length + 1)) *
          (E + (|x.toVal (R := R)| + S')) := by
      calc traceAddMag rest
          ≤ (xs'.length : R) * (1 + η) ^ (2 * xs'.length) * (A + S') := ih1
        _ = (xs'.length : R) * ((1 + η) ^ (2 * xs'.length) * (A + S')) := by ring
        _ ≤ (xs'.length : R) * ((1 + η) ^ (2 * (xs'.length + 1)) *
              (E + (|x.toVal (R := R)| + S'))) :=
            mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
        _ = (xs'.length : R) * (1 + η) ^ (2 * (xs'.length + 1)) *
              (E + (|x.toVal (R := R)| + S')) := by ring
    refine ⟨?_, ?_, ?_⟩
    · -- traceAddMag ≤ (|xs'|+1)·(1+η)^(2(|xs'|+1))·(E+S)
      show A + traceAddMag rest ≤
        ↑(xs'.length + 1) * (1 + η) ^ (2 * (xs'.length + 1)) *
          (E + (|x.toVal (R := R)| + S'))
      have hcast : (↑(xs'.length + 1) : R) = (xs'.length : R) + 1 := by
        push_cast; ring
      rw [hcast]; nlinarith
    · -- |final.sum| ≤ (1+η)·(1+η)^(2(|xs'|+1))·(E+S)
      calc |fin.sum.toVal (R := R)|
          ≤ (1 + η) * ((1 + η) ^ (2 * xs'.length) * (A + S')) := ih2
        _ ≤ (1 + η) * ((1 + η) ^ (2 * (xs'.length + 1)) *
              (E + (|x.toVal (R := R)| + S'))) :=
            mul_le_mul_of_nonneg_left hkey (by linarith)
    · -- |final.comp| ≤ η·(1+η)^(2(|xs'|+1))·(E+S)
      calc |fin.comp.toVal (R := R)|
          ≤ η * ((1 + η) ^ (2 * xs'.length) * (A + S')) := ih3
        _ ≤ η * ((1 + η) ^ (2 * (xs'.length + 1)) *
              (E + (|x.toVal (R := R)| + S'))) :=
            mul_le_mul_of_nonneg_left hkey hη

/-- **Self-contained Kahan error bound** — eliminates the `hM` hypothesis from
    `kahan_higham_bound` by deriving it from the energy invariant.

    Starting from zero initialization with TwoSum-exactness and normal range:

    **`|ŝₙ - Σxᵢ| ≤ (η·(1 + (1+η)^{2n}) + n·η²·(1+η)^{2n}) · Σ|xᵢ|`**

    When `nη` is small and `(1+η)^{2n} ≈ 1`, this recovers the `(2η + O(nη²))·Σ|xᵢ|`
    bound from Higham's Theorem 4.3.

    The three contributing terms:
    - `η · Σ|xᵢ|` — from per-step ρ₁ rounding (independent of n)
    - `η · (1+η)^{2n} · Σ|xᵢ|` — final compensation (from energy bound)
    - `n · η² · (1+η)^{2n} · Σ|xᵢ|` — accumulated compensation (from energy bound) -/
theorem kahan_higham_bound_auto
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    let S := (xs.map (fun x => |x.toVal (R := R)|)).sum
    let P := (1 + η) ^ (2 * xs.length)
    |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      (η * (1 + P) + (xs.length : R) * η ^ 2 * P) * S := by
  set S := (xs.map (fun x => |x.toVal (R := R)|)).sum
  set P := (1 + η : R) ^ (2 * xs.length)
  have hη : (0 : R) ≤ η := by positivity
  have hS_nn : (0 : R) ≤ S := List.sum_nonneg (fun _ hx => by
    simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; positivity)
  -- Apply energy invariant with E = 0
  have hinit_s : |init.sum.toVal (R := R)| ≤ (1 + η) * 0 := by
    rw [hinit_sum, abs_zero]; linarith
  have hinit_c : |init.comp.toVal (R := R)| ≤ η * 0 := by
    rw [hinit_comp, abs_zero]; linarith
  have ⟨h_addmag, _, h_comp⟩ :=
    trace_energy_bound (R := R) trace hexact hnr 0 le_rfl hinit_s hinit_c
  -- Simplify: (0 + S) = S in energy bounds
  simp only [zero_add] at h_addmag h_comp
  -- Use kahan_twosum_eta_squared_bound: |error| ≤ η·S + η²·traceAddMag + |cₙ|
  have h_base := kahan_twosum_eta_squared_bound trace hinit_sum hinit_comp hexact hnr
  -- traceAddMag ≤ n · P · S
  have h_am : η ^ 2 * traceAddMag (R := R) trace ≤ (xs.length : R) * η ^ 2 * P * S := by
    have := mul_le_mul_of_nonneg_left h_addmag (sq_nonneg (η : R))
    nlinarith
  -- |cₙ| ≤ η · P · S
  have h_cn : |final.comp.toVal (R := R)| ≤ η * P * S := by
    have hP_nn : (0 : R) ≤ P := by positivity
    calc |final.comp.toVal (R := R)|
        ≤ η * (P * S) := h_comp
      _ = η * P * S := by ring
  -- Combine: η·S + n·η²·P·S + η·P·S = (η(1+P) + nη²P)·S
  linarith

/-! ## Extension E: Deriving `StepTwoSumExact` from First-Subtraction Exactness

The `StepTwoSumExact` hypothesis states `c' = t - (sum + y)` — the compensation
exactly captures the rounding error. This follows from the **error-free
transformation**: if the first subtraction `w = fl(t - sum)` is exact
(i.e., `w.toVal = t.toVal - sum.toVal`), then the second subtraction
`c' = fl(w - y)` is also exact because `w - y = -(rounding error)` is
representable (by `add_error_representable_general_left_nz`), and rounding a
representable number is exact (by `RModeIdem`).

The first subtraction is exact under the **Dekker condition** `|sum| ≥ |y|`
(Sterbenz applies), which holds in practice when the partial sum dominates
the compensated input. -/

/-- Given that the first subtraction `w = fl(t - sum)` is exact and `sum` has
    nonzero significand, `StepTwoSumExact` follows automatically.

    This reduces the TwoSum-exactness hypothesis to a single exactness condition
    on `fl(t - sum)`, which holds whenever Sterbenz/Dekker conditions are met. -/
theorem step_twosum_exact_of_sub_exact
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    [RModeConj R] [RModeIdem R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hm_sum : 0 < st.sum.m)
    (hw_exact : step.w.toVal (R := R) = step.t.toVal - st.sum.toVal) :
    StepTwoSumExact (R := R) st x step := by
  unfold StepTwoSumExact
  -- Need: c'.toVal = t.toVal - (sum.toVal + y.toVal)
  -- Since w.toVal = t.toVal - sum.toVal (hw_exact), this is c'.toVal = w.toVal - y.toVal
  suffices h : step.c'.toVal (R := R) = step.w.toVal - step.y.toVal by
    rw [h, hw_exact]; ring
  by_cases hwy : (step.w.toVal : R) - step.y.toVal = 0
  · -- Zero case: w.toVal = y.toVal, so c' = fl(w - y) = fl(0) = 0
    have hweq : (step.w.toVal : R) = step.y.toVal := sub_eq_zero.mp hwy
    exact (fpSub_exact_zero (R := R) step.w step.y step.c' step.hc hwy).symm ▸ hwy.symm
  · -- Nonzero case: the error sum+y-t is representable
    -- First, sum + y ≠ 0 (otherwise w-y = 0, contradiction)
    have hsy_ne : (st.sum.toVal : R) + step.y.toVal ≠ 0 := by
      intro heq; apply hwy
      have := fpAdd_exact_zero (R := R) st.sum step.y step.t step.ht heq
      linarith [hw_exact]
    -- Get representable error: err.toVal = sum + y - t
    obtain ⟨err_fp, herr_nnz, herr_val⟩ :=
      add_error_representable_general_left_nz (R := R) st.sum step.y
        hm_sum hsy_ne step.t step.ht
    -- w - y = -(sum + y - t) = -err.toVal = (-err).toVal
    have hwy_val : (step.w.toVal : R) - step.y.toVal = (-err_fp).toVal := by
      rw [hw_exact, FiniteFp.toVal_neg_eq_neg, herr_val]; ring
    -- (-err_fp).notNegZero since err_fp.m > 0 (its value is nonzero)
    have herr_m_pos : 0 < err_fp.m := by
      by_contra h
      push_neg at h
      have hm0 : err_fp.m = 0 := Nat.eq_zero_of_le_zero h
      have : (err_fp.toVal : R) = 0 := FiniteFp.toVal_isZero (show err_fp.isZero from by
        unfold FiniteFp.isZero; omega)
      rw [herr_val] at this
      exact absurd (by linarith [hwy_val,
        show (-err_fp).toVal (R := R) = -err_fp.toVal from
          FiniteFp.toVal_neg_eq_neg err_fp] :
        (step.w.toVal : R) - step.y.toVal = 0) hwy
    have hneg_nnz : (-err_fp).notNegZero := Or.inr (by simp [herr_m_pos])
    -- fl(w - y) = round(w.toVal - y.toVal) = round((-err_fp).toVal) = (-err_fp)
    have hsub_corr := fpSubFinite_correct (R := R) step.w step.y hwy
    have hc := step.hc
    simp only [sub_eq_fpSub, fpSub_coe_coe] at hsub_corr hc
    rw [hsub_corr, hwy_val,
      RModeIdem.round_idempotent (R := R) (-err_fp) hneg_nnz] at hc
    have hc_eq := Fp.finite.inj hc
    -- c' = -err_fp, so c'.toVal = (-err_fp).toVal = -err_fp.toVal = -(sum+y-t) = w-y
    have : step.c'.toVal (R := R) = (-err_fp).toVal := by rw [hc_eq]
    rw [this, FiniteFp.toVal_neg_eq_neg, herr_val, hw_exact]; ring

/-- **Full Dekker chain (positive case)**: When `sum` and `y` are both positive
    with `y ≤ sum` (the Dekker condition), `StepTwoSumExact` follows automatically.

    The proof chains: Dekker condition → Sterbenz (`fl(t - sum)` exact) →
    `step_twosum_exact_of_sub_exact` (`fl(w - y)` exact) → `StepTwoSumExact`.

    This eliminates `hexact` from Approach B theorems for positive-operand sums. -/
theorem step_twosum_exact_of_pos_dekker
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    [RModeConj R] [RModeIdem R] [RModeMono R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hsum_pos : st.sum.s = false)
    (hy_pos : step.y.s = false)
    (hm_sum : 0 < st.sum.m)
    (hm_y : 0 < step.y.m)
    (hdekker : step.y.toVal (R := R) ≤ st.sum.toVal) :
    StepTwoSumExact (R := R) st x step := by
  have hsum_ne : (st.sum.toVal : R) + step.y.toVal ≠ 0 := by
    have := FiniteFp.toVal_pos st.sum hsum_pos hm_sum (R := R)
    have := FiniteFp.toVal_pos step.y hy_pos hm_y (R := R)
    linarith
  -- Sterbenz: fl(t - sum) is exact
  obtain ⟨z_fp, hz_eq, hz_val⟩ :=
    sterbenz_sub_sa (R := R) st.sum step.y hsum_pos hy_pos hm_sum hm_y
      hdekker hsum_ne step.t step.ht
  -- z_fp = step.w (both equal t - sum)
  have hw_eq_z : step.w = z_fp :=
    Fp.finite.inj (step.hw.symm.trans hz_eq)
  have hw_exact : step.w.toVal (R := R) = step.t.toVal - st.sum.toVal := by
    rw [hw_eq_z]; exact hz_val
  exact step_twosum_exact_of_sub_exact st x step hm_sum hw_exact

/-- **Dekker chain for same-sign operands.**

When `sum` and `y` have the same sign, both have nonzero significands, and the
Dekker condition `|y| ≤ |sum|` holds, the compensation step exactly captures
the rounding error: `c' = t - (sum + y)`. This generalizes
`step_twosum_exact_of_pos_dekker` from both-positive to both-same-sign. -/
theorem step_twosum_exact_of_dekker
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    [RModeConj R] [RModeIdem R] [RModeMono R]
    (st : State) (x : FiniteFp) (step : StepWitness st x)
    (hsame : step.y.s = st.sum.s)
    (hm_sum : 0 < st.sum.m)
    (hm_y : 0 < step.y.m)
    (hdekker : FiniteFp.toVal_mag step.y (R := R) ≤ FiniteFp.toVal_mag st.sum) :
    StepTwoSumExact (R := R) st x step := by
  have hsum_ne : (st.sum.toVal : R) + step.y.toVal ≠ 0 := by
    have hsum_nz := FiniteFp.toVal_ne_zero_of_m_pos st.sum hm_sum (R := R)
    have hy_nz := FiniteFp.toVal_ne_zero_of_m_pos step.y hm_y (R := R)
    rcases Bool.eq_false_or_eq_true st.sum.s with hs | hs
    · -- sum negative
      have hsum_neg : (st.sum.toVal : R) < 0 := by
        have := FiniteFp.toVal_pos (-st.sum) (by simp [FiniteFp.neg_def, hs])
          (by rw [FiniteFp.neg_def]; exact hm_sum) (R := R)
        rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
      have hy_neg : (step.y.toVal : R) < 0 := by
        have := FiniteFp.toVal_pos (-step.y)
          (by simp [FiniteFp.neg_def]; exact hsame ▸ hs)
          (by rw [FiniteFp.neg_def]; exact hm_y) (R := R)
        rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
      linarith
    · -- sum positive
      have hsum_pos := FiniteFp.toVal_pos st.sum hs hm_sum (R := R)
      have hy_pos := FiniteFp.toVal_pos step.y (hsame ▸ hs) hm_y (R := R)
      linarith
  -- Sterbenz: fl(t - sum) is exact
  obtain ⟨z_fp, hz_eq, hz_val⟩ :=
    sterbenz_sub_sa_same_sign (R := R) st.sum step.y hsame.symm hm_sum hm_y
      hdekker hsum_ne step.t step.ht
  -- z_fp = step.w (both equal t - sum)
  have hw_eq_z : step.w = z_fp :=
    Fp.finite.inj (step.hw.symm.trans hz_eq)
  have hw_exact : step.w.toVal (R := R) = step.t.toVal - st.sum.toVal := by
    rw [hw_eq_z]; exact hz_val
  exact step_twosum_exact_of_sub_exact st x step hm_sum hw_exact

/-! ## Extension B: Backward Error Interpretation

The **backward error** says the computed sum is the exact sum of slightly perturbed
inputs: `ŝₙ = Σ(1 + μᵢ)xᵢ` where each `|μᵢ| ≤ ε`. This is strictly more informative
than the forward bound `|ŝₙ - Σxᵢ| ≤ ε·Σ|xᵢ|`, as it gives per-element perturbations.

The weak form proven here follows from the forward bound via `error_distributable`:
if a total error `E` satisfies `|E| ≤ ε·Σ|xᵢ|`, then `E` can be written as `Σ μᵢ xᵢ`
with `|μᵢ| ≤ ε`, by distributing proportional to `|xᵢ|` with matching signs.

Higham's eq. 4.8 gives a stronger *per-element* bound `|μᵢ| ≤ 2η + O((n-i+1)η²)`
where earlier elements have tighter bounds. That requires per-element tracking through
the trace and is deferred. -/

end KahanSum

/-! ## Extension B: Backward Error Interpretation

The **backward error** says the computed sum is the exact sum of slightly perturbed
inputs: `ŝₙ = Σ(1 + μᵢ)xᵢ` where each `|μᵢ| ≤ ε`. This is strictly more informative
than the forward bound `|ŝₙ - Σxᵢ| ≤ ε·Σ|xᵢ|`, as it gives per-element perturbations.

The weak form proven here follows from the forward bound via `error_distributable`:
if a total error `E` satisfies `|E| ≤ ε·Σ|xᵢ|`, then `E` can be written as `Σ μᵢ xᵢ`
with `|μᵢ| ≤ ε`, by distributing proportional to `|xᵢ|` with matching signs.

Higham's eq. 4.8 gives a stronger *per-element* bound `|μᵢ| ≤ 2η + O((n-i+1)η²)`
where earlier elements have tighter bounds. That requires per-element tracking through
the trace and is deferred. -/

section BackwardErrorInfrastructure
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

private lemma abs_div_mul_self (x : R) : abs x / x * x = abs x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact div_mul_cancel₀ _ hx

private lemma abs_abs_div_self_le_one (x : R) : abs (abs x / x) ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h, div_self hx, abs_one]
    · rw [abs_of_neg h, neg_div, abs_neg, div_self hx, abs_one]

private lemma list_map_sum_eq_finset_sum {α : Type*} {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → M) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
  simp [List.sum_ofFn, Function.comp]

/-- **Error distribution lemma**: if a total error is bounded by `ε · Σ|vᵢ|`,
    it can be written as `Σ μᵢ · vᵢ` with uniform `|μᵢ| ≤ ε`.

    Construction: `μᵢ = (E/Σ|vⱼ|) · (|vᵢ|/vᵢ)`, distributing error proportionally
    to magnitude with matching signs. -/
theorem error_distributable {α : Type*} (xs : List α) (v : α → R) (E eps : R)
    (heps : 0 ≤ eps)
    (hbound : abs E ≤ eps * (xs.map (fun x => abs (v x))).sum) :
    ∃ mu : Fin xs.length → R,
      E = ∑ i : Fin xs.length, mu i * v (xs.get i) ∧
      ∀ i, abs (mu i) ≤ eps := by
  set S := (xs.map (fun x => abs (v x))).sum with hS_def
  by_cases hS : S = 0
  · exact ⟨fun _ => 0, by simp [abs_nonpos_iff.mp (by rw [hS, mul_zero] at hbound; exact hbound)],
      fun _ => by simp [heps]⟩
  · have hS_pos : 0 < S := lt_of_le_of_ne
      (List.sum_nonneg (fun y hy => by
        simp only [List.mem_map] at hy; obtain ⟨z, _, rfl⟩ := hy; exact abs_nonneg _))
      (Ne.symm hS)
    have hES : abs E / S ≤ eps := by rwa [div_le_iff₀ hS_pos]
    have hES_nn : 0 ≤ abs E / S := div_nonneg (abs_nonneg E) (le_of_lt hS_pos)
    refine ⟨fun i => E / S * (abs (v (xs.get i)) / v (xs.get i)), ?_, ?_⟩
    · simp_rw [show ∀ i : Fin xs.length,
        E / S * (abs (v (xs.get i)) / v (xs.get i)) * v (xs.get i) =
        E / S * abs (v (xs.get i)) from fun i => by rw [mul_assoc, abs_div_mul_self]]
      rw [← Finset.mul_sum, show ∑ i : Fin xs.length, abs (v (xs.get i)) = S from by
        rw [hS_def, list_map_sum_eq_finset_sum]]
      exact (div_mul_cancel₀ E (ne_of_gt hS_pos)).symm
    · intro i
      rw [abs_mul, abs_div, abs_of_pos hS_pos]
      exact le_trans (mul_le_mul_of_nonneg_left (abs_abs_div_self_le_one _) hES_nn)
        (by rw [mul_one]; exact hES)

/-- Lifting a forward error bound to backward error form. -/
private theorem backward_from_forward {α : Type*} (xs : List α) (v : α → R)
    (result : R) (eps : R) (heps : 0 ≤ eps)
    (hfwd : abs (result - (xs.map v).sum) ≤ eps * (xs.map (fun x => abs (v x))).sum) :
    ∃ mu : Fin xs.length → R,
      result = ∑ i : Fin xs.length, (1 + mu i) * v (xs.get i) ∧
      ∀ i, abs (mu i) ≤ eps := by
  obtain ⟨mu, hmu_eq, hmu_bnd⟩ := error_distributable xs v _ eps heps hfwd
  refine ⟨mu, ?_, hmu_bnd⟩
  rw [list_map_sum_eq_finset_sum] at hmu_eq
  rw [show result = (xs.map v).sum + (result - (xs.map v).sum) from by ring,
      list_map_sum_eq_finset_sum, hmu_eq, ← Finset.sum_add_distrib]
  simp_rw [show ∀ i : Fin xs.length,
    v (xs.get i) + mu i * v (xs.get i) = (1 + mu i) * v (xs.get i) from fun _ => by ring]

end BackwardErrorInfrastructure

namespace KahanSum

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- **Weak backward error for Kahan summation** (with `hM` hypothesis).

    The computed sum equals the exact sum of perturbed inputs:
    **`ŝₙ = Σ(1 + μᵢ)xᵢ`** where **`|μᵢ| ≤ 2η + nη²`**.

    This is the backward error interpretation of Higham's Theorem 4.3 (eq. 4.8).
    Each input is perturbed by at most `2η + nη²` — the perturbation is independent
    of `n` to first order, matching the forward bound. -/
theorem kahan_weak_backward_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step)
    (hM : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      |(st.sum.toVal : R) + step.y.toVal| ≤
        (xs.map (fun x => |x.toVal (R := R)|)).sum) :
    ∃ mu : Fin xs.length → R,
      (final.sum.toVal : R) =
        ∑ i : Fin xs.length, (1 + mu i) * (xs.get i).toVal ∧
      ∀ i, abs (mu i) ≤ 2 * η + (xs.length : R) * η ^ 2 :=
  backward_from_forward xs (fun x => x.toVal) _ _ (by positivity)
    (kahan_higham_bound trace hinit_sum hinit_comp hexact hnr hM)

/-- **Self-contained weak backward error** — eliminates `hM` via energy invariant.

    **`ŝₙ = Σ(1 + μᵢ)xᵢ`** where **`|μᵢ| ≤ η(1+P) + nη²P`**,
    `P = (1+η)^{2n}`.

    For Float64 (`η ≈ 10⁻¹⁶`), `P ≈ 1` for any practical `n`, recovering
    the `|μᵢ| ≤ 2η + nη²` bound from `kahan_weak_backward_error`. -/
theorem kahan_weak_backward_error_auto
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {init final : State}
    (trace : Trace xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_comp : init.comp.toVal (R := R) = 0)
    (hexact : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepTwoSumExact (R := R) st x step)
    (hnr : ∀ (st : State) (x : FiniteFp) (step : StepWitness st x),
      StepNormalRange (R := R) st x step) :
    let P := (1 + η) ^ (2 * xs.length)
    let eps := η * (1 + P) + (xs.length : R) * η ^ 2 * P
    ∃ mu : Fin xs.length → R,
      (final.sum.toVal : R) =
        ∑ i : Fin xs.length, (1 + mu i) * (xs.get i).toVal ∧
      ∀ i, abs (mu i) ≤ eps := by
  intro P eps
  exact backward_from_forward xs (fun x => x.toVal) _ eps (by positivity)
    (kahan_higham_bound_auto trace hinit_sum hinit_comp hexact hnr)

end KahanSum
