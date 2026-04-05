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
  sorry

/-- C-lane magnitude: `|c_new| ≤ (1+η)² · (|c_prev| + |σ+π|)`. -/
theorem cdp_clane_step_magnitude
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {s_prev c_prev x y : FiniteFp}
    (step : CDPStep s_prev c_prev x y)
    (hnr : CDPStepNormalRange (R := R) c_prev step) :
    |step.c_new.toVal (R := R)| ≤
      (1 + η) ^ 2 * (|(c_prev.toVal : R)| + |step.sigma.toVal + step.pi.toVal|) := by
  sorry

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
  -- Final rounding: |result - (s+c)| ≤ η|s+c|
  have hfinal := KahanSum.fpAdd_error_or_zero (R := R) s_final c_final result
    hresult hresult_nr
  -- Exact decomposition: s_final + Σ(σ+π) = Σ(xy)
  have hdecomp := cdp_exact_decomposition (R := R) trace hexact
  rw [hinit_s, zero_add] at hdecomp
  -- C-lane telescoping: c_final + Σ(c-errors) = Σ(corrections)
  have hc_tele := c_lane_telescoping (R := R) trace
  rw [hinit_c, zero_add] at hc_tele
  -- Combine: Σ(xy) - (s+c) = Σ(c-errors)
  set S := (pairs.map (fun p => p.1.toVal (R := R) * p.2.toVal)).sum
  set sc := (s_final.toVal : R) + c_final.toVal
  -- Triangle: |result - S| ≤ |result - sc| + |sc - S|
  have htri : |(result.toVal : R) - S| ≤ |result.toVal - sc| + |sc - S| := by
    have : (result.toVal : R) - S = (result.toVal - sc) + (sc - S) := by ring
    rw [this]; exact abs_add_le _ _
  -- |sc - S| = |Σ(c-errors)| (since S = s + Σcorr and sc = c + Σ(c-errors) + s - Σ(c-errors)...)
  -- Actually: S = s_final + Σcorr (from hdecomp)
  --           c_final + Σ(c-errors) = Σcorr (from hc_tele)
  --           sc = s_final + c_final
  --           S - sc = Σcorr - c_final = Σ(c-errors)
  have hsc_diff : S - sc = (cdpCLaneErrors (R := R) trace).sum := by linarith
  -- Need: |Σ(c-errors)| ≤ ((1+η)^{2n}-1) · Σ|corrections|
  -- The c-lane is a naive summation with two roundings per step.
  -- Each c-lane error ≤ ((1+η)²-1) · (|c_k| + |corr_k|).
  -- This is exactly the DotProduct error structure with κ=1, α=(1+η)²-1.
  sorry

end CompensatedDotProduct
