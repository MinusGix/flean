import Flean.Operations.TwoSum6Op
import Flean.Operations.KahanSum
import Flean.Rounding.SplitPositive

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
- `cs_trace_residual_abs_le_eta` — trace-level: `Σ|ρ₁ᵢ| ≤ η · Σ|xᵢ + errᵢ|`
- `twoSum_6op_pos` — auto-derives split witnesses for positive operands
- `twoSum_6op_same_sign` — auto-derives for same-sign operands
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

The intermediate 6-op TwoSum values (bv, av, br, ar) are abstracted away;
only the exactness result `twosum_exact` is stored. Prove it via one of:
- `twoSum_6op` (with Dekker/Sterbenz path)
- `twoSum_6op_pos` (positive operands + `RModeGrid`)
- `twoSum_6op_same_sign` (same-sign + `RModeGrid`)
- `twoSum_6op_of_witnesses` (explicit split witnesses) -/
structure CSStep [RModeExec] (st : CSState) (x : FiniteFp) where
  /-- `y = fl(x + err)` — compensated input -/
  y : FiniteFp
  hy : x + st.err = Fp.finite y
  /-- `t = fl(sum + y)` — new sum -/
  t : FiniteFp
  ht : st.sum + y = Fp.finite t
  /-- `err' = TwoSum₆(sum, y).err` — recovered error -/
  err' : FiniteFp
  /-- The 6-op TwoSum gives `t + err' = sum + y` exactly. -/
  twosum_exact : (t.toVal : R) + err'.toVal = st.sum.toVal + y.toVal

/-- Next state after a compensated sum step. -/
def CSStep.nextState [RModeExec] {st : CSState} {x : FiniteFp}
    (step : CSStep (R := R) st x) : CSState :=
  ⟨step.t, step.err'⟩

/-- The compensated input value: `x + err`. -/
def CSStep.compInputVal [RModeExec] {st : CSState} {x : FiniteFp}
    (_ : CSStep (R := R) st x) : R :=
  x.toVal + st.err.toVal

/-! ## Proving `twosum_exact`

The `twosum_exact` field of `CSStep` can be proved via several strategies:
- **Dekker path**: `bv_exact_of_same_sign_dekker` + `twoSum_6op` for same-sign
  operands with `|y| ≤ |sum|` (uses Sterbenz)
- **Grid path**: `twoSum_6op_pos` or `twoSum_6op_same_sign` for positive or
  same-sign operands with `RModeGrid` (no magnitude ordering needed)
- **Explicit witnesses**: `twoSum_6op_of_witnesses` with split-representability
  witnesses from `split_s_sub_bv_pos` / `split_b_sub_bv_pos` -/

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

/-- **6-op 2Sum for positive operands** — auto-derives split witnesses via `RModeGrid`.

No Dekker condition or explicit witnesses needed. Works for any positive
nonzero operands under round-to-nearest with grid preservation. -/
theorem twoSum_6op_pos [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R] [RModeGrid R]
    (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (s : FiniteFp) (hs : a + b = (s : Fp))
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by linarith
  -- Bridge fpAdd/fpSub to rounding form
  have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
  simp only [add_eq_fpAdd, fpAdd_coe_coe] at hcorr hs
  have hs_round : ○((a.toVal : R) + b.toVal) = Fp.finite s := hcorr.symm.trans hs
  -- For bv: need ○(s.toVal - a.toVal) = Fp.finite bv
  -- s.toVal - a.toVal ≠ 0 since s = ○(a+b) ≥ a > 0, so s-a ≥ 0, and s-a = 0 only if s=a
  -- But if s=a then ○(a+b) = a, which with b > 0 means b rounds away — still s ≥ a
  -- Actually we only need the sub correctness when sum ≠ 0 (which is always here)
  by_cases hsa_ne : (s.toVal : R) - a.toVal = 0
  · -- s.toVal = a.toVal: bv = fl(0) = 0, so bv.toVal = 0 = s.toVal - a.toVal
    -- In this case the split witnesses are trivial
    have hsa_eq : (s.toVal : R) = a.toVal := sub_eq_zero.mp hsa_ne
    obtain ⟨bv', hbv'_eq, hbv'_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s a hsa_eq
    simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe] at hbv hbv'_eq
    have : bv = bv' := by cases hbv.symm.trans hbv'_eq; rfl
    have hbv_exact : bv.toVal (R := R) = s.toVal - a.toVal := by
      rw [this, hbv'_val, hsa_ne]
    -- Reconstruct hs/hbv in Fp form for twoSum_6op
    have hs' : (a : Fp) + b = s := by
      simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe]; exact hs
    have hbv' : (s : Fp) - a = bv := by
      simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe]; exact hbv
    exact twoSum_6op (R := R) a b s hs' bv hbv'
      (fun _ => hbv_exact) av hav br hbr ar har t ht
  · -- s.toVal ≠ a.toVal: derive round form for bv
    have hscorr := fpSubFinite_correct (R := R) s a hsa_ne
    simp only [sub_eq_fpSub, fpSub_coe_coe] at hscorr hbv
    have hbv_round : ○((s.toVal : R) - a.toVal) = Fp.finite bv := hscorr.symm.trans hbv
    -- Get split witnesses from SplitPositive
    have hs_sub := split_s_sub_bv_pos (R := R) a b s ha hb ha_nz hb_nz hsum_ne
      hs_round bv hbv_round
    have hb_sub := split_b_sub_bv_pos (R := R) a b s ha hb ha_nz hb_nz hsum_ne
      hs_round bv hbv_round
    have hs' : (a : Fp) + b = s := by
      simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe]; exact hs
    have hbv' : (s : Fp) - a = bv := by
      simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe]; exact hbv
    exact twoSum_6op_of_witnesses (R := R) a b ha_nz hb_nz s hs'
      bv hbv' (fun _ => hs_sub) av hav (fun _ => hb_sub) br hbr ar har t ht

/-- **6-op 2Sum for same-sign operands** — auto-derives split witnesses via `RModeGrid`.

Like `twoSum_6op_pos` but handles both-positive and both-negative cases. -/
theorem twoSum_6op_same_sign [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R] [RModeGrid R]
    (a b : FiniteFp) (hsame : a.s = b.s)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s : FiniteFp) (hs : a + b = (s : Fp))
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  -- Bridge fpAdd/fpSub to rounding form
  have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
  simp only [add_eq_fpAdd, fpAdd_coe_coe] at hcorr hs
  have hs_round : ○((a.toVal : R) + b.toVal) = Fp.finite s := hcorr.symm.trans hs
  by_cases hsa_ne : (s.toVal : R) - a.toVal = 0
  · -- s.toVal = a.toVal: bv = fl(0) = 0
    have hsa_eq : (s.toVal : R) = a.toVal := sub_eq_zero.mp hsa_ne
    obtain ⟨bv', hbv'_eq, hbv'_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s a hsa_eq
    simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe] at hbv hbv'_eq
    have : bv = bv' := by cases hbv.symm.trans hbv'_eq; rfl
    have hbv_exact : bv.toVal (R := R) = s.toVal - a.toVal := by
      rw [this, hbv'_val, hsa_ne]
    have hs' : (a : Fp) + b = s := by
      simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe]; exact hs
    have hbv' : (s : Fp) - a = bv := by
      simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe]; exact hbv
    exact twoSum_6op (R := R) a b s hs' bv hbv'
      (fun _ => hbv_exact) av hav br hbr ar har t ht
  · -- s.toVal ≠ a.toVal: derive round form for bv
    have hscorr := fpSubFinite_correct (R := R) s a hsa_ne
    simp only [sub_eq_fpSub, fpSub_coe_coe] at hscorr hbv
    have hbv_round : ○((s.toVal : R) - a.toVal) = Fp.finite bv := hscorr.symm.trans hbv
    -- Get split witnesses from same-sign splits
    have hs_sub := split_s_sub_bv_same_sign (R := R) a b s hsame ha_nz hb_nz hsum_ne
      hs_round bv hbv_round
    have hb_sub := split_b_sub_bv_same_sign (R := R) a b s hsame ha_nz hb_nz hsum_ne
      hs_round bv hbv_round
    have hs' : (a : Fp) + b = s := by
      simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe]; exact hs
    have hbv' : (s : Fp) - a = bv := by
      simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe]; exact hbv
    exact twoSum_6op_of_witnesses (R := R) a b ha_nz hb_nz s hs'
      bv hbv' (fun _ => hs_sub) av hav (fun _ => hb_sub) br hbr ar har t ht

/-! ## TwoSum exactness -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- The 6-op TwoSum gives `t + err' = sum + y` exactly. -/
theorem cs_twosum_exact [RModeExec]
    (st : CSState) (x : FiniteFp) (step : CSStep (R := R) st x) :
    (step.t.toVal : R) + step.err'.toVal = st.sum.toVal + step.y.toVal :=
  step.twosum_exact

/-! ## Per-step corrected sum identity -/

/-- The rounding error of the compensated input computation. -/
def cs_rho1 [RModeExec] (st : CSState) (x : FiniteFp)
    (step : CSStep (R := R) st x) : R :=
  step.y.toVal - (x.toVal + st.err.toVal)

omit [FloorRing R] in
/-- **Corrected sum identity**: `σ' = σ + x + ρ₁`.

Under TwoSum-exactness (which holds unconditionally for the 6-op algorithm),
the only rounding error per step is `ρ₁` from `fl(x + err)`. -/
theorem cs_step_corrected_sum [RModeExec]
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
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : R :=
  match trace with
  | .nil _ => 0
  | .cons step rest => cs_rho1 (R := R) _ _ step + csTraceResidual rest

omit [FloorRing R] in
/-- **Corrected sum telescoping**: `σₙ = σ₀ + Σxᵢ + Σρ₁ᵢ`. -/
theorem cs_trace_sigma_eq [RModeExec]
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
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : R :=
  match trace with
  | .nil _ => 0
  | .cons step rest => |cs_rho1 (R := R) _ _ step| + csTraceResidualAbs rest

omit [FloorRing R] in
theorem csTraceResidual_abs_le [RModeExec]
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

omit [FloorRing R] in
/-- **Error bound**: the final sum minus the true sum of inputs is bounded
by the initial error plus the sum of per-step rounding residuals.

Since each `|ρ₁ᵢ| ≤ η|xᵢ + errᵢ|` (standard error model), this gives
the concrete bound `≤ |err₀| + η·Σ|xᵢ + errᵢ|`. -/
theorem cs_error_bound [RModeExec]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_err : init.err.toVal (R := R) = 0) :
    |final.sum.toVal (R := R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      |final.err.toVal (R := R)| + csTraceResidualAbs trace := by
  have hsigma := cs_trace_sigma_eq (R := R) trace
  unfold CSState.sigma at hsigma
  rw [hinit_sum, hinit_err] at hsigma
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

/-! ## Per-step ULP bound (subnormal-safe)

`cs_rho1_abs_le` gives a *relative* bound `|ρ₁| ≤ η · |val|` but requires
`val` to be in normal range. For subnormal `val`, the relative error can
exceed `η` (ulp is constant `2^(min_exp - prec + 1)`, not proportional to `|val|`).

`cs_rho1_abs_le_ulp_half` gives an *absolute* bound `|ρ₁| ≤ ulp(|val|) / 2`
that works for all nonzero inputs. For normal inputs the two are equivalent
(`ulp(x) = 2^(1-prec) · x` in normal range). For subnormal inputs, the ULP
bound is a constant `2^(min_exp - prec)` — weaker than `η · |val|` relative
to `|val|`, but always valid.

**Trace-level implications**: a trace bound using the ULP version would be
`Σ ulp(|xᵢ + errᵢ|) / 2` rather than `η · Σ|xᵢ + errᵢ|`. This is strictly
more general but less tight for normal inputs. A mixed bound splitting normal
and subnormal steps may be desirable. -/

/-- The rounding error `ρ₁` satisfies the absolute ULP-based bound:
`|ρ₁| ≤ ulp(|x + err|) / 2`, for any nonzero compensated input.

Unlike `cs_rho1_abs_le`, this does **not** require normal range — it works
for subnormal inputs too, using `RModeNearest_abs_error_le_ulp_half_pos`. -/
theorem cs_rho1_abs_le_ulp_half [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    (st : CSState) (x : FiniteFp) (step : CSStep (R := R) st x)
    (hne : x.toVal (R := R) + st.err.toVal ≠ 0) :
    |cs_rho1 (R := R) st x step| ≤ Fp.ulp (|x.toVal (R := R) + st.err.toVal|) / 2 := by
  set val := (x.toVal : R) + st.err.toVal with val_def
  -- ρ₁ = y.toVal - val = -(val - y.toVal)
  unfold cs_rho1
  rw [show step.y.toVal (R := R) - (x.toVal + st.err.toVal) =
      -(val - step.y.toVal) from by ring]
  rw [abs_neg]
  -- Get ○val = Fp.finite y
  have hround : ○val = Fp.finite step.y := by
    have := fpAddFinite_correct (R := R) x st.err hne
    simp only [add_eq_fpAdd, fpAdd_coe_coe] at this
    rw [← this]; exact step.hy
  -- Case split on sign of val
  rcases le_or_gt val 0 with hle | hpos
  · -- val < 0
    have hlt : val < 0 := lt_of_le_of_ne hle hne
    have hpos_neg : 0 < -val := neg_pos.mpr hlt
    have hneg_round : ○(-val) = Fp.finite (-step.y) := by
      rw [RModeConj.round_neg val (ne_of_lt hlt), hround, Fp.neg_finite]
    have h := RModeNearest_abs_error_le_ulp_half_pos (-val) hpos_neg (-step.y) hneg_round
    rw [FiniteFp.toVal_neg_eq_neg, neg_sub_neg, abs_sub_comm] at h
    rwa [abs_of_neg hlt]
  · -- val > 0
    have h := RModeNearest_abs_error_le_ulp_half_pos val hpos step.y hround
    rwa [abs_of_pos hpos]

/-! ## Trace-level η bound

Combines `cs_rho1_abs_le` across a full trace to get the textbook bound:
`Σ|ρ₁ᵢ| ≤ η · Σ|xᵢ + errᵢ|` where η = 2^(-prec), assuming all
compensated inputs are in normal range. -/

/-- Sum of compensated input magnitudes: `Σ|xᵢ + errᵢ|`. -/
def csTraceCompInputAbs [RModeExec]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : R :=
  match trace with
  | .nil _ => 0
  | .cons step rest => |step.compInputVal| + csTraceCompInputAbs rest

/-- All compensated inputs `|xᵢ + errᵢ|` are in normal range. -/
def csTraceAllNormal [RModeExec]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) : Prop :=
  match trace with
  | .nil _ => True
  | .cons step rest => isNormalRange (|step.compInputVal|) ∧ csTraceAllNormal rest

omit [FloorRing R] in
theorem csTraceCompInputAbs_nonneg [RModeExec]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final) :
    0 ≤ csTraceCompInputAbs trace := by
  match trace with
  | .nil _ => simp [csTraceCompInputAbs]
  | .cons step rest =>
    simp only [csTraceCompInputAbs]
    linarith [abs_nonneg step.compInputVal, csTraceCompInputAbs_nonneg rest]

/-- **Trace-level η bound**: when all compensated inputs are in normal range,
`Σ|ρ₁ᵢ| ≤ η · Σ|xᵢ + errᵢ|` where `η = 2^(-prec)`.

Combined with `cs_error_bound`, this gives the textbook result:
`|final_sum - Σxᵢ| ≤ |err_final| + η · Σ|xᵢ + errᵢ|`. -/
theorem cs_trace_residual_abs_le_eta [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final)
    (hnr : csTraceAllNormal trace) :
    csTraceResidualAbs trace ≤
      (2 : R) ^ (-(FloatFormat.prec : ℤ)) * csTraceCompInputAbs trace := by
  match trace, hnr with
  | .nil _, _ => simp [csTraceResidualAbs, csTraceCompInputAbs]
  | .cons step rest, hnr =>
    have hnr' : isNormalRange (|step.compInputVal|) ∧ csTraceAllNormal rest := hnr
    simp only [CSStep.compInputVal] at hnr'
    have h1 := cs_rho1_abs_le (R := R) _ _ step hnr'.1
    have h2 := cs_trace_residual_abs_le_eta rest hnr'.2
    have hη_pos : (0 : R) < (2 : R) ^ (-(FloatFormat.prec : ℤ)) := by linearize
    have hci_nonneg := csTraceCompInputAbs_nonneg rest
    simp only [csTraceResidualAbs, csTraceCompInputAbs, CSStep.compInputVal]
    nlinarith

/-- **End-to-end error bound**: starting from zero initial state and assuming
all compensated inputs are in normal range:

`|final_sum - Σxᵢ| ≤ |err_final| + η · Σ|xᵢ + errᵢ|`

This is the textbook result combining `cs_error_bound` with
`cs_trace_residual_abs_le_eta`. -/
theorem cs_error_bound_eta [RModeExec]
    [RMode R] [RModeNearest R] [RoundIntSigMSound R] [RModeConj R]
    {xs : List FiniteFp} {init final : CSState}
    (trace : CSTrace (R := R) xs init final)
    (hinit_sum : init.sum.toVal (R := R) = 0)
    (hinit_err : init.err.toVal (R := R) = 0)
    (hnr : csTraceAllNormal trace) :
    |final.sum.toVal (R := R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      |final.err.toVal (R := R)| +
        (2 : R) ^ (-(FloatFormat.prec : ℤ)) * csTraceCompInputAbs trace := by
  have h1 := cs_error_bound (R := R) trace hinit_sum hinit_err
  have h2 := cs_trace_residual_abs_le_eta trace hnr
  linarith

end CompensatedSum
