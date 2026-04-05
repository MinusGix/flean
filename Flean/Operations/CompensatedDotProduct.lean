import Flean.Operations.DotProduct
import Flean.Operations.KahanSum

/-!
# Compensated Dot Product (Ogita-Rump-Oishi)

The compensated dot product uses TwoProduct and TwoSum to recover rounding
errors from the standard dot product and accumulate them in a secondary lane:

```
s₀ = 0, c₀ = 0
for i = 1..n:
  (pᵢ, πᵢ) = TwoProduct(xᵢ, yᵢ)    // pᵢ = fl(xᵢyᵢ), πᵢ + pᵢ = xᵢyᵢ exactly
  (sᵢ, σᵢ) = TwoSum(sᵢ₋₁, pᵢ)     // sᵢ = fl(sᵢ₋₁ + pᵢ), σᵢ + sᵢ = sᵢ₋₁ + pᵢ exactly
  cᵢ = fl(cᵢ₋₁ + fl(πᵢ + σᵢ))      // naive accumulation of corrections
result = fl(sₙ + cₙ)
```

## Main results

- `cdp_exact_decomposition`: `sₙ + Σ(σᵢ + πᵢ) = Σ(xᵢyᵢ)` (exact)
- `cdp_error_bound`: `|result - Σxᵢyᵢ| ≤ η|sₙ + cₙ| + ((1+η)^{2n}-1) · Σ|σᵢ+πᵢ|`

## References

- Ogita, Rump, Oishi, "Accurate Sum and Dot Product" (2005), Theorem 4.3
-/

namespace CompensatedDotProduct

open DotProduct

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Step and Trace -/

/-- One step of compensated dot product (computation witnesses, R-free). -/
structure CDPStep [RModeExec] (s_prev c_prev : FiniteFp) (x y : FiniteFp) where
  p : FiniteFp
  hp : x * y = Fp.finite p
  pi : FiniteFp
  s_new : FiniteFp
  hs : s_prev + p = Fp.finite s_new
  sigma : FiniteFp
  q : FiniteFp
  hq : pi + sigma = Fp.finite q
  c_new : FiniteFp
  hc : c_prev + q = Fp.finite c_new

/-- EFT (error-free transformation) exactness for a compensated dot product step. -/
structure CDPStepExact [RModeExec] (s_prev c_prev : FiniteFp) (x y : FiniteFp)
    (step : CDPStep s_prev c_prev x y) where
  /-- TwoProduct: `p + π = x * y` exactly -/
  hpi : (step.p.toVal : R) + step.pi.toVal = x.toVal * y.toVal
  /-- TwoSum: `s_new + σ = s_prev + p` exactly -/
  hsigma : (step.s_new.toVal : R) + step.sigma.toVal = s_prev.toVal + step.p.toVal

/-- Normal range hypotheses for c-lane operations. -/
structure CDPStepNormalRange [RModeExec] {s_prev : FiniteFp} (c_prev : FiniteFp)
    {x y : FiniteFp} (step : CDPStep s_prev c_prev x y) where
  q_normal : isNormalRange ((step.pi.toVal : R) + step.sigma.toVal) ∨
             (step.pi.toVal : R) + step.sigma.toVal = 0
  c_normal : isNormalRange ((c_prev.toVal : R) + step.q.toVal) ∨
             (c_prev.toVal : R) + step.q.toVal = 0

/-- Trace of a compensated dot product computation (R-free). -/
inductive CDPTrace [RModeExec] :
    List (FiniteFp × FiniteFp) → FiniteFp → FiniteFp → FiniteFp → FiniteFp → Type where
  | nil (s c : FiniteFp) : CDPTrace [] s c s c
  | cons {s_prev c_prev : FiniteFp} {x y : FiniteFp}
      {pairs : List (FiniteFp × FiniteFp)} {s_final c_final : FiniteFp}
      (step : CDPStep s_prev c_prev x y)
      (rest : CDPTrace pairs step.s_new step.c_new s_final c_final) :
      CDPTrace ((x, y) :: pairs) s_prev c_prev s_final c_final

/-- All EFT exactness properties hold. -/
def CDPTrace.AllExact [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} →
    {s_init c_init s_final c_final : FiniteFp} →
    CDPTrace pairs s_init c_init s_final c_final → Prop
  | _, _, _, _, _, .nil _ _ => True
  | _, _, _, _, _, .cons (s_prev := s) (c_prev := c) (x := x) (y := y) step rest =>
      CDPStepExact (R := R) s c x y step ∧ rest.AllExact

/-- All c-lane operations are in normal range. -/
def CDPTrace.AllNormalRange [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} →
    {s_init c_init s_final c_final : FiniteFp} →
    CDPTrace pairs s_init c_init s_final c_final → Prop
  | _, _, _, _, _, .nil _ _ => True
  | _, _, _, _, _, .cons (c_prev := c) step rest =>
      CDPStepNormalRange (R := R) c step ∧ rest.AllNormalRange

/-! ## Error extraction -/

/-- Extract the per-step correction terms `σᵢ + πᵢ` from a trace. -/
def cdpCorrections [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} →
    {s_init c_init s_final c_final : FiniteFp} →
    CDPTrace pairs s_init c_init s_final c_final → List R
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons step rest =>
    (step.sigma.toVal (R := R) + step.pi.toVal) :: cdpCorrections rest

theorem cdpCorrections_length [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)}
    {s_init c_init s_final c_final : FiniteFp}
    (trace : CDPTrace pairs s_init c_init s_final c_final) :
    (cdpCorrections (R := R) trace).length = pairs.length := by
  induction trace with
  | nil => simp [cdpCorrections]
  | cons _ _ ih => simp [cdpCorrections, ih]

/-- Extract per-step c-lane rounding errors: `(c_prev + σ + π) - c_new`. -/
def cdpCLaneErrors [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} →
    {s_init c_init s_final c_final : FiniteFp} →
    CDPTrace pairs s_init c_init s_final c_final → List R
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons (c_prev := c_prev) step rest =>
    ((c_prev.toVal : R) + step.sigma.toVal + step.pi.toVal - step.c_new.toVal) ::
      cdpCLaneErrors rest

theorem cdpCLaneErrors_length [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)}
    {s_init c_init s_final c_final : FiniteFp}
    (trace : CDPTrace pairs s_init c_init s_final c_final) :
    (cdpCLaneErrors (R := R) trace).length = pairs.length := by
  induction trace with
  | nil => simp [cdpCLaneErrors]
  | cons _ _ ih => simp [cdpCLaneErrors, ih]

/-! ## Exact decomposition -/

/-- **Exact decomposition**: `s_final + Σ(σᵢ + πᵢ) = s_init + Σ(xᵢ · yᵢ)`.

    At each step: TwoSum gives `s_new + σ = s_prev + p` and TwoProduct gives
    `p + π = x · y`. So `s_new + (σ + π) = s_prev + x · y`. Telescoping
    gives the identity. -/
theorem cdp_exact_decomposition [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)}
    {s_init c_init s_final c_final : FiniteFp}
    (trace : CDPTrace pairs s_init c_init s_final c_final)
    (hexact : trace.AllExact (R := R)) :
    (s_final.toVal : R) +
      (cdpCorrections (R := R) trace).sum =
      (s_init.toVal : R) +
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum := by
  induction trace with
  | nil => simp [cdpCorrections]
  | @cons s_prev c_prev x y pairs s_final c_final step rest ih =>
    simp only [CDPTrace.AllExact] at hexact
    obtain ⟨⟨hpi, hsigma⟩, hexact_rest⟩ := hexact
    simp only [cdpCorrections, List.sum_cons, List.map_cons, List.sum_cons]
    -- IH: s_final + Σ(rest corrections) = s_new + Σ(rest products)
    have ih_bound := ih hexact_rest
    -- Step: s_new + σ = s_prev + p  (hsigma)
    --       p + π = x * y           (hpi)
    -- So: s_new + (σ + π) = s_prev + x*y
    linarith

/-- **C-lane telescoping**: `c_final + Σ(c-lane errors) = c_init + Σ(σᵢ + πᵢ)`. -/
theorem c_lane_telescoping [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)}
    {s_init c_init s_final c_final : FiniteFp}
    (trace : CDPTrace pairs s_init c_init s_final c_final) :
    (c_final.toVal : R) +
      (cdpCLaneErrors (R := R) trace).sum =
      (c_init.toVal : R) +
      (cdpCorrections (R := R) trace).sum := by
  induction trace with
  | nil => simp [cdpCLaneErrors, cdpCorrections]
  | @cons s_prev c_prev x y pairs s_final c_final step rest ih =>
    simp only [cdpCLaneErrors, cdpCorrections, List.sum_cons]
    linarith

/-! ## C-lane error bound -/

/-- Per-step c-lane error: `|(c_prev + σ + π) - c_new| ≤ ((1+η)²-1) · (|c_prev| + |σ+π|)`.
    Two roundings (fl(π+σ) then fl(c+q)) give the same compound error as DotProduct. -/
theorem cdp_clane_step_error
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {s_prev c_prev x y : FiniteFp}
    (step : CDPStep s_prev c_prev x y)
    (hnr : CDPStepNormalRange (R := R) c_prev step) :
    |(c_prev.toVal : R) + step.sigma.toVal + step.pi.toVal - step.c_new.toVal| ≤
      ((1 + η) ^ 2 - 1) * (|(c_prev.toVal : R)| + |step.sigma.toVal + step.pi.toVal|) := by
  set cv := (c_prev.toVal : R)
  set corr : R := step.sigma.toVal + step.pi.toVal
  set qv : R := step.q.toVal
  set nv : R := step.c_new.toVal
  have hη : (0 : R) ≤ η := by positivity
  have hq := KahanSum.fpAdd_error_or_zero (R := R) step.pi step.sigma step.q step.hq hnr.q_normal
  have hc := KahanSum.fpAdd_error_or_zero (R := R) c_prev step.q step.c_new step.hc hnr.c_normal
  have hq_err : |qv - corr| ≤ η * |corr| := by
    simpa [qv, corr, add_comm, add_left_comm, add_assoc] using hq
  have hq_bound : |qv| ≤ (1 + η) * |corr| := by
    have h1 : |qv| - |corr| ≤ η * |corr| := le_trans (abs_sub_abs_le_abs_sub qv corr) hq_err
    linarith
  have hc_sum : |cv + qv| ≤ |cv| + (1 + η) * |corr| := by
    calc
      |cv + qv| ≤ |cv| + |qv| := abs_add_le _ _
      _ ≤ |cv| + (1 + η) * |corr| := by linarith
  have hc_err : |nv - (cv + qv)| ≤ η * (|cv| + (1 + η) * |corr|) := by
    calc
      |nv - (cv + qv)| ≤ η * |cv + qv| := hc
      _ ≤ η * (|cv| + (1 + η) * |corr|) := by
          exact mul_le_mul_of_nonneg_left hc_sum hη
  have htri : |cv + corr - nv| ≤ |nv - (cv + qv)| + |qv - corr| := by
    have : cv + corr - nv = -(nv - (cv + qv)) + -(qv - corr) := by ring
    rw [this]
    linarith [abs_add_le (-(nv - (cv + qv))) (-(qv - corr)),
      abs_neg (nv - (cv + qv)), abs_neg (qv - corr)]
  have hcombine : |cv + corr - nv| ≤ η * |cv| + (2 * (η : R) + η ^ 2) * |corr| := by
    nlinarith [htri, hc_err, hq_err,
      mul_nonneg hη (abs_nonneg cv),
      mul_nonneg hη (abs_nonneg corr),
      mul_nonneg (mul_nonneg hη hη) (abs_nonneg corr)]
  have hη_le : (η : R) ≤ 2 * η + η ^ 2 := by
    nlinarith
  have hslack :
      η * |cv| + (2 * (η : R) + η ^ 2) * |corr| ≤
        (((1 + (η : R)) ^ 2 - 1) : R) * (|cv| + |corr|) := by
    have hpow2 : (((1 + (η : R)) ^ 2 - 1) : R) = 2 * η + η ^ 2 := by ring
    rw [hpow2]
    nlinarith [hη_le, abs_nonneg cv, abs_nonneg corr]
  simpa [corr, add_assoc] using (le_trans hcombine hslack)

/-- C-lane magnitude: `|c_new| ≤ (1+η)² · (|c_prev| + |σ+π|)`. -/
theorem cdp_clane_step_magnitude
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {s_prev c_prev x y : FiniteFp}
    (step : CDPStep s_prev c_prev x y)
    (hnr : CDPStepNormalRange (R := R) c_prev step) :
    |step.c_new.toVal (R := R)| ≤
      (1 + η) ^ 2 * (|(c_prev.toVal : R)| + |step.sigma.toVal + step.pi.toVal|) := by
  set exact_val : R := (c_prev.toVal : R) + (step.sigma.toVal + step.pi.toVal)
  set M : R := |(c_prev.toVal : R)| + |step.sigma.toVal + step.pi.toVal|
  have herr := cdp_clane_step_error (R := R) step hnr
  have herr' : |step.c_new.toVal (R := R) - exact_val| ≤ (((1 + (η : R)) ^ 2 - 1) : R) * M := by
    simpa [exact_val, M, add_assoc, abs_sub_comm] using herr
  have hexact : |exact_val| ≤ M := by
    dsimp [exact_val, M]
    exact abs_add_le _ _
  have hsub : |step.c_new.toVal (R := R)| - |exact_val| ≤
      |step.c_new.toVal (R := R) - exact_val| := by
    exact abs_sub_abs_le_abs_sub _ _
  have hcn : |step.c_new.toVal (R := R)| ≤ |exact_val| + (((1 + (η : R)) ^ 2 - 1) : R) * M := by
    linarith
  have hpow2 : |exact_val| + (((1 + (η : R)) ^ 2 - 1) : R) * M ≤ ((1 + η) ^ 2) * M := by
    have : ((1 + (η : R)) ^ 2) * M = M + (((1 + η) ^ 2 - 1) : R) * M := by ring
    linarith
  linarith

/-! ## Main error bound -/

-- Helper: extract c-lane magnitudes for the DotProduct-style framework
def cdpCLaneMags [RModeExec] :
    {pairs : List (FiniteFp × FiniteFp)} →
    {s_init c_init s_final c_final : FiniteFp} →
    CDPTrace pairs s_init c_init s_final c_final → ℕ → R
  | _, _, c, _, _, .nil _ _, _ => |(c.toVal : R)|
  | _, _, c, _, _, .cons _ _, 0 => |(c.toVal : R)|
  | _, _, _, _, _, .cons _ rest, n + 1 => cdpCLaneMags rest n

theorem cdpCLaneMags_nonneg [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)}
    {s_init c_init s_final c_final : FiniteFp}
    (trace : CDPTrace pairs s_init c_init s_final c_final) (k : ℕ) :
    0 ≤ cdpCLaneMags (R := R) trace k := by
  match trace, k with
  | .nil _ _, _ | .cons _ _, 0 => exact abs_nonneg _
  | .cons _ rest, k + 1 => exact cdpCLaneMags_nonneg rest k

@[simp] theorem cdpCLaneMags_zero [RModeExec]
    {pairs : List (FiniteFp × FiniteFp)}
    {s_init c_init s_final c_final : FiniteFp}
    (trace : CDPTrace pairs s_init c_init s_final c_final) :
    cdpCLaneMags (R := R) trace 0 = |(c_init.toVal : R)| := by
  cases trace <;> rfl

/-- **Compensated dot product error bound.**

    `|result - Σxᵢyᵢ| ≤ η · |sₙ + cₙ| + ((1+η)^{2n}-1) · Σ|σᵢ + πᵢ|`

    The first term is a single final rounding. The second term bounds the c-lane's
    naive accumulation error. Since each `|σᵢ + πᵢ| = O(η · |xᵢyᵢ|)`, the
    combined bound is `O(η + n²η²) · Σ|xᵢyᵢ|`. -/
theorem cdp_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {pairs : List (FiniteFp × FiniteFp)}
    {s_init c_init s_final c_final : FiniteFp}
    (trace : CDPTrace pairs s_init c_init s_final c_final)
    (hexact : trace.AllExact (R := R))
    (hnr : trace.AllNormalRange (R := R))
    (hinit_s : s_init.toVal (R := R) = 0)
    (hinit_c : c_init.toVal (R := R) = 0)
    (result : FiniteFp)
    (hresult : s_final + c_final = Fp.finite result)
    (hresult_nr : isNormalRange ((s_final.toVal : R) + c_final.toVal) ∨
                  (s_final.toVal : R) + c_final.toVal = 0) :
    |(result.toVal (R := R)) -
      (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum| ≤
      η * |(s_final.toVal : R) + c_final.toVal| +
      ((1 + η) ^ (2 * pairs.length) - 1) *
        ((cdpCorrections (R := R) trace).map (|·|)).sum := by
  have hclane :
      ∀ {pairs : List (FiniteFp × FiniteFp)}
        {s_init c_init s_final c_final : FiniteFp}
        (trace : CDPTrace pairs s_init c_init s_final c_final),
        trace.AllNormalRange (R := R) →
        |(c_final.toVal : R) -
          ((c_init.toVal : R) + (cdpCorrections (R := R) trace).sum)| ≤
          ((1 + η) ^ (2 * pairs.length) - 1) *
            (|(c_init.toVal : R)| + ((cdpCorrections (R := R) trace).map (|·|)).sum) := by
    intro pairs s_init c_init s_final c_final trace
    induction trace with
    | nil c =>
      intro _
      simp [cdpCorrections]
    | @cons s_prev c_prev x y pairs s_final c_final step rest ih =>
      intro hnr
      simp only [CDPTrace.AllNormalRange] at hnr
      obtain ⟨hnr_step, hnr_rest⟩ := hnr
      simp only [cdpCorrections, List.sum_cons, List.map_cons, List.sum_cons]
      set corr : R := step.sigma.toVal + step.pi.toVal
      set restSum : R := (cdpCorrections (R := R) rest).sum
      set restAbs : R := ((cdpCorrections (R := R) rest).map (|·|)).sum
      set B : R := |(c_prev.toVal : R)| + |corr|
      set Arest : R := (1 + η) ^ (2 * pairs.length) - 1
      set Atotal : R := (1 + η) ^ (2 * (pairs.length + 1)) - 1
      set α : R := (1 + η) ^ 2 - 1
      have ih_bound :
          |(c_final.toVal : R) - (step.c_new.toVal + restSum)| ≤
            Arest * (|step.c_new.toVal (R := R)| + restAbs) := by
        simpa [Arest, restSum, restAbs] using ih hnr_rest
      have hstep_err :
          |step.c_new.toVal (R := R) - ((c_prev.toVal : R) + corr)| ≤ α * B := by
        simpa [corr, B, α, add_assoc, add_comm, add_left_comm, abs_sub_comm] using
          cdp_clane_step_error (R := R) step hnr_step
      have hstep_mag :
          |step.c_new.toVal (R := R)| ≤ (1 + η) ^ 2 * B := by
        simpa [corr, B, add_assoc] using cdp_clane_step_magnitude (R := R) step hnr_step
      have htri :
          |(c_final.toVal : R) - ((c_prev.toVal : R) + (corr + restSum))| ≤
            |(c_final.toVal : R) - (step.c_new.toVal + restSum)| +
            |step.c_new.toVal (R := R) - ((c_prev.toVal : R) + corr)| := by
        have :
            (c_final.toVal : R) - ((c_prev.toVal : R) + (corr + restSum)) =
              ((c_final.toVal : R) - (step.c_new.toVal + restSum)) +
              (step.c_new.toVal - ((c_prev.toVal : R) + corr)) := by
          ring
        rw [this]
        exact abs_add_le _ _
      have hη : (0 : R) ≤ η := by positivity
      have h1η : (1 : R) ≤ 1 + η := by linarith
      have hArest_nn : (0 : R) ≤ Arest := by
        have hpow : (1 : R) ≤ (1 + η) ^ (2 * pairs.length) := one_le_pow₀ h1η
        linarith [Arest]
      have hrestAbs_nn : (0 : R) ≤ restAbs := by
        refine List.sum_nonneg ?_
        intro z hz
        simp only [List.mem_map] at hz
        obtain ⟨w, _, rfl⟩ := hz
        exact abs_nonneg w
      have htotal :
          |(c_final.toVal : R) - ((c_prev.toVal : R) + (corr + restSum))| ≤
            Arest * (|step.c_new.toVal (R := R)| + restAbs) + α * B := by
        linarith
      have htotal' :
          |(c_final.toVal : R) - ((c_prev.toVal : R) + (corr + restSum))| ≤
            Arest * ((1 + η) ^ 2 * B + restAbs) + α * B := by
        have hmul :
            Arest * |step.c_new.toVal (R := R)| ≤ Arest * ((1 + η) ^ 2 * B) :=
          mul_le_mul_of_nonneg_left hstep_mag hArest_nn
        linarith
      have hAtotal_ge : Arest ≤ Atotal := by
        have hpow_eq :
            (1 + (η : R)) ^ (2 * (pairs.length + 1)) =
              (1 + η) ^ (2 * pairs.length) * (1 + η) ^ 2 := by
          have hnat : 2 * (pairs.length + 1) = 2 * pairs.length + 2 := by omega
          rw [hnat, pow_add]
        have hpow_nn : (0 : R) ≤ (1 + η) ^ (2 * pairs.length) := by
          positivity
        have hpow2_ge1 : (1 : R) ≤ (1 + η) ^ 2 := one_le_pow₀ h1η
        dsimp [Arest, Atotal]
        nlinarith [hpow_eq, hpow_nn, hpow2_ge1]
      have hrest_mono : Arest * restAbs ≤ Atotal * restAbs := by
        exact mul_le_mul_of_nonneg_right hAtotal_ge hrestAbs_nn
      have hmain_eq :
          Arest * ((1 + η) ^ 2 * B + restAbs) + α * B =
            Atotal * B + Arest * restAbs := by
        have hpow_eq :
            (1 + (η : R)) ^ (2 * (pairs.length + 1)) =
              (1 + η) ^ (2 * pairs.length) * (1 + η) ^ 2 := by
          have hnat : 2 * (pairs.length + 1) = 2 * pairs.length + 2 := by omega
          rw [hnat, pow_add]
        dsimp [Arest, Atotal, α]
        rw [hpow_eq]
        ring
      have hfinal :
          |(c_final.toVal : R) - ((c_prev.toVal : R) + (corr + restSum))| ≤
            Atotal * B + Atotal * restAbs := by
        linarith
      have hsum :
          Atotal * B + Atotal * restAbs = Atotal * (B + restAbs) := by ring
      simpa [B, corr, restSum, restAbs, Atotal, add_assoc, add_left_comm, add_comm] using
        hfinal.trans_eq hsum
  -- Final rounding: |result - (s+c)| ≤ η|s+c|
  have hfinal := KahanSum.fpAdd_error_or_zero (R := R) s_final c_final result
    hresult hresult_nr
  -- Exact decomposition: s_final + Σ(σ+π) = Σ(xy)
  have hdecomp := cdp_exact_decomposition (R := R) trace hexact
  rw [hinit_s, zero_add] at hdecomp
  set S := (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum
  set sc := (s_final.toVal : R) + c_final.toVal
  -- Triangle: |result - S| ≤ |result - sc| + |sc - S|
  have htri : |(result.toVal : R) - S| ≤ |result.toVal - sc| + |sc - S| := by
    have : (result.toVal : R) - S = (result.toVal - sc) + (sc - S) := by ring
    rw [this]; exact abs_add_le _ _
  have hclane_bound :
      |sc - S| ≤
        ((1 + η) ^ (2 * pairs.length) - 1) *
          ((cdpCorrections (R := R) trace).map (|·|)).sum := by
    have h := hclane trace hnr
    rw [hinit_c, zero_add] at h
    have hsc_eq : sc - S = (c_final.toVal : R) - (cdpCorrections (R := R) trace).sum := by
      linarith [hdecomp]
    rw [hsc_eq]
    simpa using h
  linarith

end CompensatedDotProduct
