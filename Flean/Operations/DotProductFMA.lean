import Flean.Operations.DotProduct
import Flean.Operations.HornerFMA

/-!
# FMA-Based Dot Product Error Bound

When the dot product uses FMA: `sₖ = fma(xₖ, yₖ, s_{k-1})`, each step has
only ONE rounding (the FMA), giving a tighter bound than the two-operation version.

  `|sₙ - x·y| ≤ ((1+η)^n - 1) · Σ|xᵢyᵢ|  ≤  γₙ · Σ|xᵢyᵢ|`

compared to the non-FMA bound `((1+η)^{n+1} - 1)` (which uses `γ_{n+1}` via
separate mul + add). With FMA and zero init, the first step `fma(x₁,y₁,0)` rounds
`x₁y₁` once, so n pairs give exactly n roundings.
-/

namespace DotProductFMA

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Step and Trace -/

/-- One step of FMA dot product: `next = fma(x, y, acc)`. -/
structure FMADPStep [RModeExec] (acc x y : FiniteFp) where
  next : FiniteFp
  hnext : fpFMAFinite x y acc = Fp.finite next

/-- Normal range hypothesis for an FMA dot product step. -/
structure FMADPStepNormalRange [RModeExec] (acc x y : FiniteFp)
    (step : FMADPStep acc x y) where
  fma_normal : isNormalRange ((x.toVal : R) * y.toVal + acc.toVal) ∨
               (x.toVal : R) * y.toVal + acc.toVal = 0

/-- Trace of FMA-based dot product. -/
inductive FMADPTrace [RModeExec] :
    List (FiniteFp × FiniteFp) → FiniteFp → FiniteFp → Type where
  | nil (acc : FiniteFp) : FMADPTrace [] acc acc
  | cons {acc : FiniteFp} {x y : FiniteFp}
      {pairs : List (FiniteFp × FiniteFp)} {final : FiniteFp}
      (step : FMADPStep acc x y)
      (rest : FMADPTrace pairs step.next final) :
      FMADPTrace ((x, y) :: pairs) acc final

/-- All steps are in normal range. -/
def FMADPTrace.AllNormalRange [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} → {acc final : FiniteFp} →
    FMADPTrace pairs acc final → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons (acc := acc) (x := x) (y := y) step rest =>
      FMADPStepNormalRange (R := R) acc x y step ∧ rest.AllNormalRange

/-! ## Error Bound -/

/-- **General FMA dot product error bound** (arbitrary initial accumulator).

    `|final - (init + Σxᵢyᵢ)| ≤ ((1+η)^n - 1) · (|init| + Σ|xᵢyᵢ|)` -/
private theorem fma_dp_error_bound_gen
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : FMADPTrace pairs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      (init.toVal + (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum)| ≤
      ((1 + η) ^ pairs.length - 1) *
        (|init.toVal (R := R)| +
         (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum) := by
  induction trace with
  | nil => simp
  | @cons acc x y pairs final step rest ih =>
    simp only [FMADPTrace.AllNormalRange] at hnr
    obtain ⟨hnr_step, hnr_rest⟩ := hnr
    -- FMA error: |next - (x*y + acc)| ≤ η|x*y + acc|
    have hfma := HornerFMA.fpFMA_error_or_zero (R := R) x y acc step.next step.hnext
      hnr_step.fma_normal
    -- Abbreviations
    set n := pairs.length with hn_def
    set acc_v := (acc.toVal : R)
    set x_v := (x.toVal : R)
    set y_v := (y.toVal : R)
    set next_v := (step.next.toVal : R)
    set xy := x_v * y_v
    set S := (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum
    set T := (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    -- Per-step: |next - (xy + acc)| ≤ η|xy + acc| ≤ η(|xy| + |acc|)
    have hstep : |next_v - (xy + acc_v)| ≤ η * (|xy| + |acc_v|) := by
      calc |next_v - (xy + acc_v)|
          = |next_v - (x_v * y_v + acc_v)| := rfl
        _ ≤ η * |x_v * y_v + acc_v| := hfma
        _ ≤ η * (|xy| + |acc_v|) := by
            apply mul_le_mul_of_nonneg_left _ hη
            exact le_trans (abs_add_le _ _) (by rw [add_comm])
    -- |next| ≤ (1+η)(|xy| + |acc|)
    have hnext_bound : |next_v| ≤ (1 + η) * (|xy| + |acc_v|) := by
      have h := abs_sub_abs_le_abs_sub next_v (xy + acc_v)
      have h2 : |xy + acc_v| ≤ |xy| + |acc_v| := abs_add_le _ _
      linarith
    -- IH: |final - (next + S)| ≤ ((1+η)^n - 1)(|next| + T)
    have ih_bound := ih hnr_rest
    -- Powers
    have hpow_n : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
    have hpow_n_nn : (0 : R) ≤ (1 + η) ^ n := le_trans zero_le_one hpow_n
    have hT_nn : (0 : R) ≤ T := List.sum_nonneg (fun z hz => by
      simp only [List.mem_map] at hz; obtain ⟨_, _, rfl⟩ := hz; exact abs_nonneg _)
    -- Triangle: |final - (acc + xy + S)| ≤ |final - (next + S)| + |next - (xy + acc)|
    have htri : |(final.toVal : R) - (acc_v + (xy + S))| ≤
        |(final.toVal : R) - (next_v + S)| + |next_v - (xy + acc_v)| := by
      have heq : (final.toVal : R) - (acc_v + (xy + S)) =
          ((final.toVal : R) - (next_v + S)) + (next_v - (xy + acc_v)) := by ring
      rw [heq]; exact abs_add_le _ _
    -- IH expanded with |next| bound
    have hih_exp : |(final.toVal : R) - (next_v + S)| ≤
        ((1 + η) ^ n - 1) * ((1 + η) * (|xy| + |acc_v|) + T) := by
      calc |(final.toVal : R) - (next_v + S)|
          ≤ ((1 + η) ^ n - 1) * (|next_v| + T) := ih_bound
        _ ≤ ((1 + η) ^ n - 1) * ((1 + η) * (|xy| + |acc_v|) + T) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            linarith
    -- Algebra: ((1+η)^n - 1)((1+η)(|xy|+|acc|) + T) + η(|xy|+|acc|)
    --        = ((1+η)^{n+1} - 1)(|xy|+|acc|) + ((1+η)^n - 1)T
    --        ≤ ((1+η)^{n+1} - 1)(|xy| + |acc| + T)  [since (1+η)^n ≤ (1+η)^{n+1}]
    have hacc_xy : ((1 + η) ^ n - 1) * ((1 + η) * (|xy| + |acc_v|)) + η * (|xy| + |acc_v|) =
        ((1 + η) ^ (n + 1) - 1) * (|xy| + |acc_v|) := by
      rw [pow_succ]; ring
    have hpow_mono : ((1 + η) ^ n - 1) * T ≤ ((1 + η) ^ (n + 1) - 1) * T := by
      have hps : (1 + η : R) ^ (n + 1) = (1 + η) ^ n * (1 + η) := pow_succ (1 + η) n
      nlinarith [mul_nonneg hpow_n_nn hη, mul_nonneg hη hT_nn]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    -- Goal: |final - (acc + (xy + S))| ≤ ((1+η)^{n+1} - 1)(|acc| + (|xy| + T))
    have hxy_nn := abs_nonneg xy
    have hacc_nn := abs_nonneg acc_v
    have hpow_n1 : (1 : R) ≤ (1 + η) ^ (n + 1) := one_le_pow₀ h1η
    nlinarith

/-- **FMA dot product error bound** (with zero init).

    `|sₙ - Σxᵢyᵢ| ≤ ((1+η)^n - 1) · Σ|xᵢyᵢ|`

    Same exponent `n` as non-FMA (which gets `n` via the zero-init trick),
    but the FMA version also works with nonzero init via `fma_dp_error_bound_gen`. -/
theorem fma_dp_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : FMADPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum| ≤
      ((1 + η) ^ pairs.length - 1) *
        (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum := by
  have hgen := fma_dp_error_bound_gen trace hnr
  simp only [hinit, abs_zero, zero_add] at hgen
  exact hgen

/-- **FMA dot product error bound** (γₙ form). -/
theorem fma_dp_error_bound_gamma
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)} {init final : FiniteFp}
    (trace : FMADPTrace pairs init final)
    (hinit : init.toVal (R := R) = 0)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (pairs.length : R) * η < 1) :
    |(final.toVal : R) -
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum| ≤
      gamma_n (R := R) pairs.length *
        (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum := by
  have h1 := fma_dp_error_bound trace hinit hnr
  have h2 := pow_sub_one_le_gamma (R := R) pairs.length (by push_cast; exact hsmall)
  have habs_nn : (0 : R) ≤ (pairs.map (fun p => |p.1.toVal (R := R) * p.2.toVal|)).sum :=
    List.sum_nonneg (fun z hz => by
      simp only [List.mem_map] at hz; obtain ⟨_, _, rfl⟩ := hz; exact abs_nonneg _)
  nlinarith

end DotProductFMA
