import Flean.Operations.KahanSum
import Flean.Operations.Mul

/-!
# Dot Product Error Bound

Error analysis for the sequential dot product algorithm:
```
s₀ = 0
sₖ = fl(s_{k-1} + fl(xₖ * yₖ))   for k = 1, ..., n
```

## Main Results

- `dp_error_bound`: `|sₙ - x·y| ≤ ((1+η)^n - 1) · Σ|xᵢyᵢ|` (Higham's Theorem 3.1)
- `dp_error_bound_gamma`: `|sₙ - x·y| ≤ γₙ · Σ|xᵢyᵢ|` where `γₙ = nη/(1-nη)`

The tight `(1+η)^n` bound (rather than `(1+η)^{n+1}`) exploits that the first
addition `fl(0 + fl(x₁y₁)) = fl(x₁y₁)` is exact: adding a zero accumulator
introduces no rounding error, saving one factor.
-/

namespace DotProduct

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Dot Product Step and Trace -/

/-- One step of dot product accumulation: multiply then add. -/
structure DPStep [RModeExec] (acc : FiniteFp) (x y : FiniteFp) where
  prod : FiniteFp
  hprod : x * y = Fp.finite prod
  next : FiniteFp
  hnext : acc + prod = Fp.finite next

/-- Normal range hypothesis for a dot product step. -/
structure DPStepNormalRange [RModeExec] (acc : FiniteFp) (x y : FiniteFp)
    (step : DPStep acc x y) where
  mul_normal : isNormalRange ((x.toVal : R) * y.toVal) ∨ (x.toVal : R) * y.toVal = 0
  add_normal : isNormalRange ((acc.toVal : R) + step.prod.toVal) ∨
               (acc.toVal : R) + step.prod.toVal = 0

/-- Trace of a sequential dot product computation. -/
inductive DPTrace [RModeExec] :
    List (FiniteFp × FiniteFp) → FiniteFp → FiniteFp → Type where
  | nil (acc : FiniteFp) : DPTrace [] acc acc
  | cons {acc : FiniteFp} {x y : FiniteFp}
      {pairs : List (FiniteFp × FiniteFp)} {final : FiniteFp}
      (step : DPStep acc x y)
      (rest : DPTrace pairs step.next final) :
      DPTrace ((x, y) :: pairs) acc final

/-- All steps are in normal range. -/
def DPTrace.AllNormalRange [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} → {acc final : FiniteFp} →
    DPTrace pairs acc final → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons (acc := acc) (x := x) (y := y) step rest =>
      DPStepNormalRange (R := R) acc x y step ∧ rest.AllNormalRange

/-! ## Error Bound -/

/-- **General dot product error bound** (with arbitrary initial accumulator).

    `|final - (init + Σxᵢyᵢ)| ≤ ((1+η)^n - 1)·|init| + ((1+η)^(n+1) - 1)·Σ|xᵢyᵢ|`

    The term `((1+η)^n - 1)·|init|` tracks how the initial value accumulates errors,
    and `((1+η)^(n+1) - 1)·Σ|xᵢyᵢ|` tracks per-product errors. -/
private theorem dp_error_bound_gen
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DPTrace pairs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      (init.toVal + (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum)| ≤
      ((1 + η) ^ pairs.length - 1) * |init.toVal (R := R)| +
      ((1 + η) ^ (pairs.length + 1) - 1) *
        (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum := by
  induction trace with
  | nil acc =>
    simp only [List.map_nil, List.sum_nil, add_zero, sub_self, abs_zero, List.length_nil,
               pow_zero, sub_self, mul_zero, zero_mul, zero_add, le_refl]
  | @cons acc x y pairs final step rest ih =>
    simp only [DPTrace.AllNormalRange] at hnr
    obtain ⟨hnr_step, hnr_rest⟩ := hnr
    -- Extract multiplication and addition error bounds
    have hmul_err := KahanSum.fpMul_error_or_zero (R := R) x y step.prod step.hprod hnr_step.mul_normal
    have hadd_err := KahanSum.fpAdd_error_or_zero (R := R) acc step.prod step.next step.hnext
                      hnr_step.add_normal
    -- Abbreviations
    set n := pairs.length with hn_def
    set S := (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum with hS_def
    set T := (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum with hT_def
    set xy := (x.toVal : R) * y.toVal with hxy_def
    set acc_v := (acc.toVal : R) with hacc_def
    set prod_v := (step.prod.toVal : R) with hprod_def
    set next_v := (step.next.toVal : R) with hnext_def
    -- Apply IH to rest (starting at step.next)
    -- IH: |final - (next_v + S)| ≤ ((1+η)^n - 1)*|next_v| + ((1+η)^(n+1) - 1)*T
    have ih_bound : |(final.toVal : R) - (next_v + S)| ≤
        ((1 + η) ^ n - 1) * |next_v| + ((1 + η) ^ (n + 1) - 1) * T := ih hnr_rest
    -- η ≥ 0
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    have hT_nn : (0 : R) ≤ T := List.sum_nonneg (fun y hy => by
      simp only [List.mem_map] at hy; obtain ⟨_, _, rfl⟩ := hy; exact abs_nonneg _)
    have hxy_nn : (0 : R) ≤ |xy| := abs_nonneg _
    have hacc_nn : (0 : R) ≤ |acc_v| := abs_nonneg _
    have hnext_nn : (0 : R) ≤ |next_v| := abs_nonneg _
    -- Powers
    have hpow_n : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
    have hpow_n1 : (1 : R) ≤ (1 + η) ^ (n + 1) := one_le_pow₀ h1η
    have hpow_n_nn : (0 : R) ≤ (1 + η) ^ n := le_trans zero_le_one hpow_n
    have hpow_n1_nn : (0 : R) ≤ (1 + η) ^ (n + 1) := le_trans zero_le_one hpow_n1
    -- Multiplication error: |prod_v - xy| ≤ η|xy|
    have hmul : |prod_v - xy| ≤ η * |xy| := hmul_err
    -- prod bound: |prod_v| ≤ (1+η)|xy|
    have hprod_bound : |prod_v| ≤ (1 + η) * |xy| := by
      have h1 : |prod_v| - |xy| ≤ η * |xy| := le_trans (abs_sub_abs_le_abs_sub prod_v xy) hmul
      linarith
    -- Addition error: |next_v - (acc_v + prod_v)| ≤ η(|acc_v| + (1+η)|xy|)
    have hacc_prod : |acc_v + prod_v| ≤ |acc_v| + (1 + η) * |xy| := by
      calc |acc_v + prod_v| ≤ |acc_v| + |prod_v| := abs_add_le _ _
        _ ≤ |acc_v| + (1 + η) * |xy| := by linarith
    have hadd_step : |next_v - (acc_v + prod_v)| ≤ η * (|acc_v| + (1 + η) * |xy|) := by
      calc |next_v - (acc_v + prod_v)|
          ≤ η * |acc_v + prod_v| := hadd_err
        _ ≤ η * (|acc_v| + (1 + η) * |xy|) := by
            apply mul_le_mul_of_nonneg_left hacc_prod hη
    -- Combined: |next_v - (acc_v + xy)| ≤ η|acc_v| + (2η + η²)|xy|
    have hnext_err : |next_v - (acc_v + xy)| ≤ η * |acc_v| + (2 * η + η ^ 2) * |xy| := by
      have htri : next_v - (acc_v + xy) =
          (next_v - (acc_v + prod_v)) + (prod_v - xy) := by ring
      have : |next_v - (acc_v + xy)| ≤
          |next_v - (acc_v + prod_v)| + |prod_v - xy| := by
        rw [htri]; exact abs_add_le _ _
      have hmul' : |prod_v - xy| ≤ η * |xy| := hmul
      linarith [mul_nonneg hη hxy_nn, mul_nonneg hη hacc_nn,
                mul_nonneg (mul_nonneg hη hη) hxy_nn]
    -- |next_v| ≤ (1+η)|acc_v| + (1+η)²|xy|
    have hnext_v_bound : |next_v| ≤ (1 + η) * |acc_v| + (1 + η) ^ 2 * |xy| := by
      have hacc_xy : |acc_v + xy| ≤ |acc_v| + |xy| := abs_add_le _ _
      have hrev : |next_v| ≤ |acc_v + xy| + (η * |acc_v| + (2 * η + η ^ 2) * |xy|) := by
        have h := abs_sub_abs_le_abs_sub next_v (acc_v + xy)
        linarith [hnext_err]
      have h2sq : (1 + η : R) ^ 2 = 1 + 2 * η + η ^ 2 := by ring
      linarith
    -- IH bound expanded
    have hih_expanded : |(final.toVal : R) - (next_v + S)| ≤
        ((1 + η) ^ n - 1) * ((1 + η) * |acc_v| + (1 + η) ^ 2 * |xy|) +
        ((1 + η) ^ (n + 1) - 1) * T := by
      have h1 : ((1 + η) ^ n - 1) * |next_v| ≤
          ((1 + η) ^ n - 1) * ((1 + η) * |acc_v| + (1 + η) ^ 2 * |xy|) :=
        mul_le_mul_of_nonneg_left hnext_v_bound (by linarith)
      linarith
    -- Algebra: simplify the combined bound
    -- ((1+η)^n - 1)((1+η)|acc_v|) + η|acc_v| = ((1+η)^(n+1) - 1)|acc_v|
    have hstep_acc :
        ((1 + η) ^ n - 1) * ((1 + η) * |acc_v|) + η * |acc_v| =
        ((1 + η) ^ (n + 1) - 1) * |acc_v| := by
      rw [pow_succ]; ring
    -- ((1+η)^n - 1)(1+η)²|xy| + (2η + η²)|xy| = ((1+η)^(n+2) - 1)|xy|
    have hstep_xy :
        ((1 + η) ^ n - 1) * ((1 + η) ^ 2 * |xy|) + (2 * η + η ^ 2) * |xy| =
        ((1 + η) ^ (n + 2) - 1) * |xy| := by
      have hpow2 : (1 + η : R) ^ (n + 2) = (1 + η) ^ n * (1 + η) ^ 2 := pow_add (1 + η) n 2
      have hexp2 : (1 + η : R) ^ 2 = 1 + 2 * η + η ^ 2 := by ring
      rw [hpow2, hexp2]
      ring
    -- T bound: ((1+η)^(n+1) - 1)T ≤ ((1+η)^(n+2) - 1)T
    have hT_mono :
        ((1 + η) ^ (n + 1) - 1) * T ≤ ((1 + η) ^ (n + 2) - 1) * T := by
      have hpow_step : (1 + η : R) ^ (n + 2) = (1 + η) ^ (n + 1) * (1 + η) :=
        pow_succ (1 + η) (n + 1)
      nlinarith [mul_nonneg hpow_n1_nn hη, mul_nonneg hpow_n1_nn hT_nn,
                 mul_nonneg hη hT_nn]
    -- Triangle for final error
    have htri : |(final.toVal : R) - (acc_v + (xy + S))| ≤
        |(final.toVal : R) - (next_v + S)| + |next_v - (acc_v + xy)| := by
      have heq : (final.toVal : R) - (acc_v + (xy + S)) =
          ((final.toVal : R) - (next_v + S)) + (next_v - (acc_v + xy)) := by ring
      rw [heq]; exact abs_add_le _ _
    -- Combine everything
    have hpow_n2_nn : (0 : R) ≤ (1 + η) ^ (n + 2) - 1 := by
      have h := one_le_pow₀ (show (1:R) ≤ 1+η by linarith) (n := n+2)
      linarith
    have htotal : |(final.toVal : R) - (acc_v + (xy + S))| ≤
        ((1 + η) ^ (n + 1) - 1) * |acc_v| + ((1 + η) ^ (n + 2) - 1) * (|xy| + T) := by
      linarith [htri, hih_expanded, hnext_err, hstep_acc, hstep_xy, hT_mono,
                mul_nonneg hpow_n2_nn hxy_nn]
    -- Translate to list form (goal has cons list)
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    linarith [htotal]

/-- **Dot product error bound** (tight `(1+η)^n` form, matching Higham's Theorem 3.1).

    `|sₙ - Σxᵢyᵢ| ≤ ((1+η)^n - 1) · Σ|xᵢyᵢ|`

    The bound is tighter than the naive `(1+η)^{n+1}` form: the first addition
    `fl(0 + fl(x₁y₁)) = fl(x₁y₁)` is exact (adding zero is free), so we save
    one factor of `(1+η)`.  This requires `RModeIdem` to show that rounding
    an already-representable value is idempotent. -/
theorem dp_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum| ≤
      ((1 + η) ^ pairs.length - 1) *
      (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum := by
  -- Recover init.m = 0 from init.toVal = 0
  have hinit_m : init.m = 0 := (FiniteFp.toVal_significand_zero_iff (R := R)).mpr hinit
  induction trace with
  | nil acc =>
    simp only [List.map_nil, List.sum_nil, sub_zero, List.length_nil, pow_zero, sub_self, zero_mul]
    simp [hinit]
  | @cons acc x y pairs final step rest ih =>
    simp only [DPTrace.AllNormalRange] at hnr
    obtain ⟨hnr_step, hnr_rest⟩ := hnr
    -- Extract multiplication error bound
    have hmul_err := KahanSum.fpMul_error_or_zero (R := R) x y step.prod step.hprod hnr_step.mul_normal
    -- Key: fl(acc + prod) has the same value as prod (zero-add is exact)
    have hnext_val : (step.next.toVal : R) = step.prod.toVal :=
      fpAddFinite_zero_left_val acc step.prod hinit_m step.next step.hnext
    -- η ≥ 0
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    -- Abbreviations
    set n := pairs.length with hn_def
    set S := (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum with hS_def
    set T := (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum with hT_def
    set xy := (x.toVal : R) * y.toVal with hxy_def
    set prod_v := (step.prod.toVal : R) with hprod_def
    set next_v := (step.next.toVal : R) with hnext_def
    -- next_v = prod_v (exact zero-add)
    have hnext_eq : next_v = prod_v := hnext_val
    -- prod error: |prod_v - xy| ≤ η|xy|
    have hmul : |prod_v - xy| ≤ η * |xy| := hmul_err
    -- prod bound: |prod_v| ≤ (1+η)|xy|
    have hprod_bound : |prod_v| ≤ (1 + η) * |xy| := by
      have h1 : |prod_v| - |xy| ≤ η * |xy| := le_trans (abs_sub_abs_le_abs_sub prod_v xy) hmul
      linarith
    -- next_v = prod_v, so same bound
    have hnext_bound : |next_v| ≤ (1 + η) * |xy| := hnext_eq ▸ hprod_bound
    -- Apply general bound to rest: |final - (next + S)| ≤ ((1+η)^n - 1)*|next| + ((1+η)^{n+1} - 1)*T
    have hgen_rest := dp_error_bound_gen (R := R) rest hnr_rest
    -- Powers
    have hpow_n : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
    have hpow_n1 : (1 : R) ≤ (1 + η) ^ (n + 1) := one_le_pow₀ h1η
    have hpow_n_nn : (0 : R) ≤ (1 + η) ^ n := le_trans zero_le_one hpow_n
    have hpow_n1_nn : (0 : R) ≤ (1 + η) ^ (n + 1) := le_trans zero_le_one hpow_n1
    have hxy_nn : (0 : R) ≤ |xy| := abs_nonneg _
    have hT_nn : (0 : R) ≤ T := List.sum_nonneg (fun y hy => by
      simp only [List.mem_map] at hy; obtain ⟨_, _, rfl⟩ := hy; exact abs_nonneg _)
    -- IH for rest: |final - (next + S)| ≤ ((1+η)^n - 1)*|next| + ((1+η)^{n+1} - 1)*T
    -- (dp_error_bound_gen applied with init = step.next)
    -- Note: hnext_def = next_v
    -- Triangle inequality
    have htri : |(final.toVal : R) - (xy + S)| ≤
        |(final.toVal : R) - (next_v + S)| + |next_v - xy| := by
      have : (final.toVal : R) - (xy + S) =
          ((final.toVal : R) - (next_v + S)) + (next_v - xy) := by ring
      rw [this]; exact abs_add_le _ _
    -- next_v - xy = prod_v - xy (since next_v = prod_v), so |next_v - xy| ≤ η|xy|
    have hnext_err : |next_v - xy| ≤ η * |xy| := hnext_eq ▸ hmul
    -- IH bound with next_v ≤ (1+η)|xy|
    have hih_expanded : |(final.toVal : R) - (next_v + S)| ≤
        ((1 + η) ^ n - 1) * ((1 + η) * |xy|) + ((1 + η) ^ (n + 1) - 1) * T := by
      have h1 : ((1 + η) ^ n - 1) * |next_v| ≤
          ((1 + η) ^ n - 1) * ((1 + η) * |xy|) :=
        mul_le_mul_of_nonneg_left hnext_bound (by linarith [hpow_n])
      linarith [hgen_rest]
    -- Algebra: ((1+η)^n - 1)*(1+η)*|xy| + η*|xy| = ((1+η)^{n+1} - 1)*|xy|
    have hstep_xy : ((1 + η) ^ n - 1) * ((1 + η) * |xy|) + η * |xy| =
        ((1 + η) ^ (n + 1) - 1) * |xy| := by
      rw [pow_succ]; ring
    -- Monotonicity: ((1+η)^{n+1} - 1)*T ≤ ((1+η)^{n+1} - 1)*T (trivial, just for shape)
    -- Combined bound
    have htotal : |(final.toVal : R) - (xy + S)| ≤
        ((1 + η) ^ (n + 1) - 1) * (|xy| + T) := by
      linarith [htri, hih_expanded, hnext_err, hstep_xy,
                mul_nonneg (by linarith : (0:R) ≤ (1+η)^(n+1) - 1) hT_nn]
    -- Translate to list form
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    linarith [htotal]

/-- **Dot product error bound** (γₙ form, matching Higham's Theorem 3.1).

    `|sₙ - x·y| ≤ γₙ · Σ|xᵢyᵢ|`

    Uses the tight `(1+η)^n` bound. -/
theorem dp_error_bound_gamma
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeIdem R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : DPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (pairs.length : R) * η < 1) :
    |(final.toVal : R) -
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum| ≤
      gamma_n (R := R) pairs.length *
      (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum := by
  have h1 := dp_error_bound (R := R) trace hinit hnr
  have h2 := pow_sub_one_le_gamma (R := R) pairs.length hsmall
  have habs_nn : (0 : R) ≤ (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum :=
    List.sum_nonneg (fun y hy => by
      simp only [List.mem_map] at hy; obtain ⟨_, _, rfl⟩ := hy; exact abs_nonneg _)
  nlinarith

end DotProduct
