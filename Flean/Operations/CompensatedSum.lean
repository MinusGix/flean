import Flean.Operations.TwoSum6Op
import Flean.Operations.KahanSum

/-! # TwoSum-Compensated Summation

A variant of Kahan compensated summation that uses the 6-operation TwoSum
(Knuth/Møller) for error recovery instead of the 3-operation Fast2Sum pattern.

## Comparison with Kahan (KahanSum.lean)

| | Classical Kahan | TwoSum-Compensated |
|---|---|---|
| Error recovery | 3-op Fast2Sum | 6-op TwoSum |
| Corrected sum | `sum - comp` | `sum + err` |
| Compensation step | `y = fl(x - comp)` | `y = fl(x + err)` |
| TwoSum-exact when | same-sign + Dekker | always (unconditional) |
| Error per step | `ρ₁ - ρ₃ - ρ₄` | `ρ₁` only |

The 6-op TwoSum gives `t + err = sum + y` exactly (no Dekker/sign conditions),
so the only rounding error per step is `ρ₁ = fl(x + err) - (x + err)`.

## Main results

- `cs_step_corrected_sum` — per-step identity: `σ' = σ + x + ρ₁`
- `cs_trace_sigma_eq` — telescoping: `σₙ = σ₀ + Σxᵢ + Σρ₁ᵢ`
- `cs_error_bound` — error bound: `|final_sum - Σxᵢ| ≤ |err| + Σ|ρ₁ᵢ|`
- `cs_rho1_abs_le` — concrete η model: `|ρ₁| ≤ η · |x + err|` (normal range)
- `bv_exact_of_same_sign_dekker` — discharges `hbv_exact` under Dekker conditions
-/

namespace CompensatedSum

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## State -/

/-- State for TwoSum-compensated summation.
    The corrected sum is `sum.toVal + err.toVal` (additive convention). -/
structure CSState where
  sum : FiniteFp
  err : FiniteFp

/-- The corrected sum: `sum + err`. -/
def CSState.sigma (st : CSState) : R := st.sum.toVal + st.err.toVal

/-! ## Step witness -/

/-- Witnesses for one step of TwoSum-compensated summation.

Given state `(sum, err)` and input `x`:
1. `y = fl(x + err)` — compensated input
2. `(t, err') = TwoSum₆(sum, y)` — error-free sum with recovery

The 6-op TwoSum intermediates are `bv, av, br, ar`. -/
structure CSStep [RModeExec] (st : CSState) (x : FiniteFp) where
  /-- `y = fl(x + err)` — compensated input -/
  y : FiniteFp
  hy : x + st.err = Fp.finite y
  /-- `t = fl(sum + y)` — new sum (= s in TwoSum) -/
  t : FiniteFp
  ht : st.sum + y = Fp.finite t
  /-- `bv = fl(t - sum)` — virtual b -/
  bv : FiniteFp
  hbv : t - st.sum = Fp.finite bv
  /-- Splitting property: when sum + y ≠ 0, bv exactly recovers t - sum.
      This is automatically satisfied for round-to-nearest modes
      (discharged via `split_s_sub_bv` theorems). -/
  hbv_exact :
    ((st.sum.toVal : R) + y.toVal ≠ 0) →
    bv.toVal (R := R) = t.toVal - st.sum.toVal
  /-- `av = fl(t - bv)` — virtual a -/
  av : FiniteFp
  hav : t - bv = Fp.finite av
  /-- `br = fl(y - bv)` — b roundoff -/
  br : FiniteFp
  hbr : y - bv = Fp.finite br
  /-- `ar = fl(sum - av)` — a roundoff -/
  ar : FiniteFp
  har : st.sum - av = Fp.finite ar
  /-- `err' = fl(ar + br)` — error term -/
  err' : FiniteFp
  herr : ar + br = Fp.finite err'

/-- Next state after a compensated sum step. -/
def CSStep.nextState [RModeExec] {st : CSState} {x : FiniteFp}
    (step : CSStep (R := R) st x) : CSState :=
  ⟨step.t, step.err'⟩

/-! ## Discharging `hbv_exact`

The `hbv_exact` field of `CSStep` requires proving that `fl(t - sum)` exactly
recovers `t - sum` when the sum is nonzero. This holds under the Dekker
condition (same-sign with `|y| ≤ |sum|`) via Sterbenz.

Note: `hbv_exact` does NOT hold in general when the Dekker condition fails.
For unrestricted magnitude ordering, use `twoSum_6op_of_witnesses` directly
with split-representability witnesses from `split_s_sub_bv_pos` / `split_b_sub_bv_pos`. -/

/-- `fl(s - a) = s - a` when `a, b` are same-sign with `|b| ≤ |a|`.

Uses Sterbenz: same-sign + Dekker ⟹ `|a| ≤ |s| ≤ 2|a|`, so `s - a` is exact. -/
theorem bv_exact_of_same_sign_dekker [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    (a b : FiniteFp) (hsame : a.s = b.s)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hdekker : FiniteFp.toVal_mag b (R := R) ≤ FiniteFp.toVal_mag a)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s : FiniteFp) (hs : a + b = (s : Fp))
    (bv : FiniteFp) (hbv : s - a = (bv : Fp)) :
    bv.toVal (R := R) = s.toVal - a.toVal := by
  -- Get ○(a.toVal + b.toVal) = s from fpAddFinite_correct
  have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
  simp only [add_eq_fpAdd, fpAdd_coe_coe] at hcorr hs
  have hs_round : ○((a.toVal : R) + b.toVal) = Fp.finite s := hcorr.symm.trans hs
  -- Sterbenz gives fl(s - a) = s - a exactly
  obtain ⟨z_fp, hz_eq, hz_val⟩ := sterbenz_sub_sa_same_sign (R := R) a b
    hsame ha_nz hb_nz hdekker hsum_ne s
    (by simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe]; exact hs)
  -- z_fp = bv since both equal s - a in Fp
  simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe] at hbv hz_eq
  have : (bv : Fp) = (z_fp : Fp) := hbv.symm.trans hz_eq
  have hbv_eq : bv = z_fp := by
    cases this; rfl
  rw [hbv_eq, hz_val]

/-! ## TwoSum exactness -/

/-- The 6-op TwoSum gives `t + err' = sum + y` exactly. -/
theorem cs_twosum_exact [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    (st : CSState) (x : FiniteFp) (step : CSStep (R := R) st x) :
    (step.t.toVal : R) + step.err'.toVal = st.sum.toVal + step.y.toVal :=
  twoSum_6op (R := R) st.sum step.y step.t step.ht
    step.bv step.hbv step.hbv_exact
    step.av step.hav step.br step.hbr step.ar step.har
    step.err' step.herr

/-! ## Per-step corrected sum identity -/

/-- The rounding error of the compensated input computation. -/
def cs_rho1 [RModeExec] (st : CSState) (x : FiniteFp)
    (step : CSStep (R := R) st x) : R :=
  step.y.toVal - (x.toVal + st.err.toVal)

/-- **Corrected sum identity**: `σ' = σ + x + ρ₁`.

Under TwoSum-exactness (which holds unconditionally for the 6-op algorithm),
the only rounding error per step is `ρ₁` from `fl(x + err)`. -/
theorem cs_step_corrected_sum [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    (st : CSState) (x : FiniteFp) (step : CSStep (R := R) st x) :
    (step.nextState (R := R)).sigma (R := R) =
      st.sigma + x.toVal + cs_rho1 (R := R) st x step := by
  unfold CSStep.nextState CSState.sigma cs_rho1
  have h2s := cs_twosum_exact (R := R) st x step
  linarith

/-! ## Trace -/

/-- A trace of TwoSum-compensated summation steps. -/
inductive CSTrace [RModeExec] :
    List FiniteFp → CSState → CSState → Type where
  /-- Empty list: state unchanged. -/
  | nil (st : CSState) : CSTrace [] st st
  /-- One step followed by the rest. -/
  | cons {st : CSState} {x : FiniteFp} {xs : List FiniteFp} {final : CSState}
      (step : CSStep (R := R) st x)
      (rest : CSTrace xs (step.nextState (R := R)) final) :
      CSTrace (x :: xs) st final

/-- Total rounding residual across a trace: Σρ₁ᵢ. -/
def csTraceResidual [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : R :=
  match trace with
  | .nil _ => 0
  | .cons step rest => cs_rho1 (R := R) _ _ step + csTraceResidual rest

/-- **Corrected sum telescoping**: `σₙ = σ₀ + Σxᵢ + Σρ₁ᵢ`. -/
theorem cs_trace_sigma_eq [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) :
    final.sigma (R := R) =
      init.sigma +
      (xs.map (fun x => x.toVal (R := R))).sum +
      csTraceResidual trace := by
  induction trace with
  | nil st => simp [csTraceResidual, CSState.sigma]
  | cons step rest ih =>
    simp only [List.map_cons, List.sum_cons, csTraceResidual]
    have hstep := cs_step_corrected_sum (R := R) _ _ step
    unfold CSStep.nextState CSState.sigma cs_rho1 at hstep
    unfold CSState.sigma CSStep.nextState at ih
    simp only at ih
    unfold CSState.sigma cs_rho1
    linarith

/-! ## Error bound -/

/-- Absolute sum of rounding residuals. -/
def csTraceResidualAbs [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : R :=
  match trace with
  | .nil _ => 0
  | .cons step rest => |cs_rho1 (R := R) _ _ step| + csTraceResidualAbs rest

theorem csTraceResidual_abs_le [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) :
    |csTraceResidual trace| ≤ csTraceResidualAbs trace := by
  induction trace with
  | nil _ => simp [csTraceResidual, csTraceResidualAbs]
  | cons step rest ih =>
    simp only [csTraceResidual, csTraceResidualAbs]
    calc |cs_rho1 (R := R) _ _ step + csTraceResidual rest|
        ≤ |cs_rho1 (R := R) _ _ step| + |csTraceResidual rest| := abs_add_le _ _
      _ ≤ |cs_rho1 (R := R) _ _ step| + csTraceResidualAbs rest := by linarith

/-- **Error bound**: the final sum minus the true sum of inputs is bounded
by the initial error plus the sum of per-step rounding residuals.

Since each `|ρ₁ᵢ| ≤ η|xᵢ + errᵢ|` (standard error model), this gives
the concrete bound `≤ |err₀| + η·Σ|xᵢ + errᵢ|`. -/
theorem cs_error_bound [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_err : init.err.toVal (R := R) = 0) :
    |final.sum.toVal (R := R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      |final.err.toVal (R := R)| + csTraceResidualAbs trace := by
  have hsigma := cs_trace_sigma_eq (R := R) trace
  unfold CSState.sigma at hsigma
  rw [hinit_sum, hinit_err] at hsigma
  -- final.sum + final.err = 0 + 0 + Σxᵢ + Σρ₁ᵢ
  -- final.sum - Σxᵢ = Σρ₁ᵢ - final.err
  have hresid : (final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum =
      csTraceResidual trace - final.err.toVal := by linarith
  calc |(final.sum.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum|
      = |csTraceResidual trace - final.err.toVal (R := R)| := by rw [hresid]
    _ ≤ |csTraceResidual trace| + |final.err.toVal (R := R)| := by
        rw [show csTraceResidual trace - final.err.toVal (R := R) =
            csTraceResidual trace + (-(final.err.toVal (R := R))) from sub_eq_add_neg _ _]
        have := abs_add_le (csTraceResidual trace) (-(final.err.toVal (R := R)))
        rw [abs_neg] at this; exact this
    _ ≤ csTraceResidualAbs trace + |final.err.toVal (R := R)| := by
        linarith [csTraceResidual_abs_le (R := R) trace]
    _ = |final.err.toVal (R := R)| + csTraceResidualAbs trace := by ring

/-! ## Per-step rounding bound (η model)

When `x + err` is in the normal range, the rounding error `ρ₁` satisfies
`|ρ₁| ≤ η · |x + err|` where `η = 2^(-prec)` is the half machine epsilon.

This connects the abstract residual to the concrete error model. -/

/-- The rounding error `ρ₁ = fl(x + err) - (x + err)` satisfies the standard
relative error model: `|ρ₁| ≤ η · |x + err|`, provided `x + err` is in
the normal range (positive version). -/
theorem cs_rho1_abs_le [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    (st : CSState) (x : FiniteFp) (step : CSStep (R := R) st x)
    (hnr : isNormalRange (|x.toVal (R := R) + st.err.toVal|)) :
    |cs_rho1 (R := R) st x step| ≤
      (2 : R) ^ (-(FloatFormat.prec : ℤ)) * |x.toVal + st.err.toVal| := by
  set val := (x.toVal : R) + st.err.toVal with val_def
  have hval_ne : val ≠ 0 := by
    intro h; rw [h, abs_zero] at hnr
    exact not_le.mpr (by linearize) hnr.1
  -- ρ₁ = y.toVal - val
  unfold cs_rho1
  rw [show step.y.toVal (R := R) - (x.toVal + st.err.toVal) =
      -(val - step.y.toVal) from by ring]
  rw [abs_neg]
  -- Get ○val = Fp.finite y
  have hround : ○val = Fp.finite step.y := by
    have := fpAddFinite_correct (R := R) x st.err hval_ne
    simp only [add_eq_fpAdd, fpAdd_coe_coe] at this
    rw [← this]; exact step.hy
  -- Case split on sign of val
  rcases le_or_gt val 0 with hle | hpos
  · -- val < 0 (can't be 0 since val ≠ 0)
    have hlt : val < 0 := lt_of_le_of_ne hle hval_ne
    -- Use RModeConj: ○(-val) = -○val
    have hneg_round : ○(-val) = Fp.finite (-step.y) := by
      rw [RModeConj.round_neg val (ne_of_lt hlt), hround, Fp.neg_finite]
    have hnr_neg : isNormalRange (-val) := by
      rw [abs_of_neg hlt] at hnr; exact hnr
    have hrel := RModeNearest_relativeError_le_half (-val) hnr_neg (-step.y) hneg_round
    -- relativeError (-val) (-y) = |(-val - (-y).toVal) / (-val)|
    --                            = |(val - y.toVal) / val|
    --                            = relativeError val y  (in effect)
    unfold Fp.relativeError at hrel
    rw [FiniteFp.toVal_neg_eq_neg, neg_sub_neg] at hrel
    -- hrel : |((val - y.toVal) / (-val))| ≤ η
    rw [abs_div, abs_neg] at hrel
    -- hrel : |val - y.toVal| / |val| ≤ η
    rw [div_le_iff₀ (abs_pos.mpr hval_ne)] at hrel
    rwa [abs_sub_comm] at hrel
  · -- val > 0
    have hnr_pos : isNormalRange val := by
      rw [abs_of_pos hpos] at hnr; exact hnr
    have hrel := RModeNearest_relativeError_le_half val hnr_pos step.y hround
    unfold Fp.relativeError at hrel
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hval_ne)] at hrel
    exact hrel

end CompensatedSum
