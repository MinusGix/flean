import Flean.Operations.StickyExtract
import Flean.Rounding.PolicyInstances
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Floating-Point Exponential (Skeleton + Constructive Roadmap)

This module provides the operation-layer skeleton for `exp` in the same style as
other operations:

- execution path computes either an exact integer-significand representation or
  a sticky representative,
- semantic correctness is discharged separately via typeclass contracts,
- sticky correctness reuses `sticky_roundIntSig_eq_round_tc`.

The current implementation keeps algorithmic details behind `ExpApprox` / `OpRefExec expTarget`.
The long-term plan is a fully constructive, softfloat-style kernel.

## Constructive Roadmap (deferred)

1. Target contract:
   - keep `OpRefExec.run` executable (no `Real` decisions in code),
   - prove `OpRefExecSound expTarget` in `ℝ`,
   - retain adapter instances so operation-level correctness is unchanged.
2. Executable numeric layer:
   - define dyadic/fixed-point values and computable intervals,
   - implement interval ops (`add`, `mul`, scaling by `2^k`, Horner step),
   - prove each op sound w.r.t. real semantics.
3. Constructive range reduction:
   - compute `k` and remainder enclosure using integer arithmetic and certified
     constants for `log 2` / `1/log 2`,
   - prove `x = k*log 2 + r` with `r` inside a small interval.
4. Constructive core approximation:
   - use Taylor or table+polynomial on reduced domain,
   - produce an interval enclosing `exp r`,
   - prove enclosure with explicit truncation and arithmetic error bounds.
5. Reconstruction and witness extraction:
   - scale interval by `2^k` (and table factor if present),
   - extract sticky witness `(q, e_base)` via integer arithmetic only,
   - prove `2^(prec+2) ≤ q` and `inStickyInterval q e_base (exp x)`.
6. Error-budget framework:
   - combine all approximation + arithmetic errors into one theorem,
   - show final enclosure width is small enough for sticky-cell containment.
7. Integration path:
   - land interval kernel + proofs,
   - land range reduction + proofs,
   - land baseline constructive `OpRefExec expTarget`,
   - optimize with tables later without changing high-level contracts.
-/

section Exp

variable [FloatFormat]

/-- Design hook for range reduction: `x = k * ln(2) + r` with a small remainder. -/
structure ExpRangeReduction (x : ℝ) where
  k : ℤ
  r : ℝ
  decomp : x = (k : ℝ) * Real.log 2 + r
  r_small : |r| ≤ Real.log 2 / 2

/-- Output shape of the finite exp approximation stage.

- `exact mag e_base` means `exp(x) = mag * 2^e_base` exactly.
- `sticky q e_base` means `exp(x)` lies in the sticky interval for `(q, e_base)`.
-/
inductive ExpApproxData where
  | exact (mag : ℕ) (e_base : ℤ)
  | sticky (q : ℕ) (e_base : ℤ)
deriving Repr

/-- Execution hook for finite `exp` approximation.

Implementations typically do range reduction + core approximation + reconstruction,
then return either an exact integer-significand representation or a sticky one.
-/
class ExpApprox where
  approx : FiniteFp → ExpApproxData

/-- Semantic contract for `ExpApprox` against the real `exp` function. -/
class ExpApproxSound [ExpApprox] : Prop where
  exact_mag_ne_zero :
    ∀ (a : FiniteFp) (mag : ℕ) (e_base : ℤ),
      ExpApprox.approx a = .exact mag e_base →
      mag ≠ 0
  exact_value :
    ∀ (a : FiniteFp) (mag : ℕ) (e_base : ℤ),
      ExpApprox.approx a = .exact mag e_base →
      intSigVal (R := ℝ) false mag e_base = Real.exp (a.toVal : ℝ)
  sticky_q_lower :
    ∀ (a : FiniteFp) (q : ℕ) (e_base : ℤ),
      ExpApprox.approx a = .sticky q e_base →
      2 ^ (FloatFormat.prec.toNat + 2) ≤ q
  sticky_interval :
    ∀ (a : FiniteFp) (q : ℕ) (e_base : ℤ),
      ExpApprox.approx a = .sticky q e_base →
      inStickyInterval (R := ℝ) q e_base (Real.exp (a.toVal : ℝ))

/-- Finite-input exponential using the approximation hook.

Exact branch: call `roundIntSigM` directly.
Sticky branch: call `roundIntSigM` with `2*q+1` so sticky correctness applies.
-/
def fpExpFinite [RModeExec] [ExpApprox] (a : FiniteFp) : Fp :=
  match ExpApprox.approx a with
  | .exact mag e_base =>
      roundIntSigM false mag e_base
  | .sticky q e_base =>
      roundIntSigM false (2 * q + 1) e_base

/-- IEEE-style `exp` at the `Fp` level.

Special cases:
- `NaN -> NaN`
- `+∞ -> +∞`
- `-∞ -> +0`
- finite -> `fpExpFinite`
-/
def fpExp [RModeExec] [ExpApprox] (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite false => .infinite false
  | .infinite true => .finite 0
  | .finite a => fpExpFinite a

@[simp] theorem fpExp_finite [RModeExec] [ExpApprox] (a : FiniteFp) :
    fpExp (Fp.finite a) = fpExpFinite a := rfl

@[simp] theorem fpExp_nan [RModeExec] [ExpApprox] :
    fpExp Fp.NaN = Fp.NaN := rfl

@[simp] theorem fpExp_pos_inf [RModeExec] [ExpApprox] :
    fpExp (Fp.infinite false) = Fp.infinite false := rfl

@[simp] theorem fpExp_neg_inf [RModeExec] [ExpApprox] :
    fpExp (Fp.infinite true) = Fp.finite 0 := rfl

/-- Finite-case correctness template for exp.

This is where sticky interval proofs plug in:
- exact branch uses `roundIntSigM_correct_tc`,
- sticky branch uses `sticky_roundIntSig_eq_round_tc`.
-/
theorem fpExpFinite_correct
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [ExpApprox] [ExpApproxSound]
    (a : FiniteFp) :
    fpExpFinite a = ○(Real.exp (a.toVal : ℝ)) := by
  unfold fpExpFinite
  cases happrox : ExpApprox.approx a with
  | exact mag e_base =>
      simp
      have hmag_ne : mag ≠ 0 :=
        ExpApproxSound.exact_mag_ne_zero a mag e_base happrox
      have hexact : intSigVal (R := ℝ) false mag e_base = Real.exp (a.toVal : ℝ) :=
        ExpApproxSound.exact_value a mag e_base happrox
      rw [roundIntSigM_correct_tc (R := ℝ) false mag e_base hmag_ne]
      simp [hexact]
  | sticky q e_base =>
      simp
      have hq_lower : 2 ^ (FloatFormat.prec.toNat + 2) ≤ q :=
        ExpApproxSound.sticky_q_lower a q e_base happrox
      have h_exact_in :
          inStickyInterval (R := ℝ) q e_base (Real.exp (a.toVal : ℝ)) :=
        ExpApproxSound.sticky_interval a q e_base happrox
      rw [sticky_roundIntSig_eq_round_tc (R := ℝ) (sign := false)
        (q := q) (e_base := e_base) (hq_lower := hq_lower)
        (abs_exact := Real.exp (a.toVal : ℝ)) (h_exact_in := h_exact_in)]
      simp

/-! ## Concrete Approximation Instance

This instance is noncomputable and directly uses `Real.exp`:

- choose a scaling exponent so the scaled exact value is above the sticky lower bound,
- take `q = floor(scaled)`,
- if `scaled = q`, emit an `exact` branch with `mag = 2*q`,
- otherwise emit `sticky q`.

This guarantees a valid witness for every finite input without requiring
transcendence/irrationality arguments.
-/

private abbrev expStickyLowerNat : ℕ :=
  2 ^ (FloatFormat.prec.toNat + 2)

private noncomputable def expX (a : FiniteFp) : ℝ :=
  Real.exp (a.toVal : ℝ)

private noncomputable def expN (a : FiniteFp) : ℕ :=
  Nat.find (exists_nat_gt ((expStickyLowerNat : ℝ) / expX a))

private noncomputable def expEBase (a : FiniteFp) : ℤ :=
  -((expN a : ℤ)) - 1

private noncomputable def expScaled (a : FiniteFp) : ℝ :=
  expX a / (2 : ℝ) ^ (expEBase a + 1)

private noncomputable def expQ (a : FiniteFp) : ℕ :=
  Nat.floor (expScaled a)

private theorem expX_pos (a : FiniteFp) : 0 < expX a := by
  unfold expX
  exact Real.exp_pos _

private theorem expEBase_add_one (a : FiniteFp) :
    expEBase a + 1 = -((expN a : ℤ)) := by
  unfold expEBase
  omega

private theorem expScaled_eq_mul_pow (a : FiniteFp) :
    expScaled a = expX a * (2 : ℝ) ^ (expN a : ℤ) := by
  unfold expScaled
  rw [expEBase_add_one, zpow_neg, div_eq_mul_inv, inv_inv]

private theorem expScaled_nonneg (a : FiniteFp) : 0 ≤ expScaled a := by
  unfold expScaled
  exact div_nonneg (le_of_lt (expX_pos a)) (by positivity)

private theorem expScaled_pos (a : FiniteFp) : 0 < expScaled a := by
  unfold expScaled
  exact div_pos (expX_pos a) (by positivity)

private theorem expScaled_gt_stickyLower (a : FiniteFp) :
    (expStickyLowerNat : ℝ) < expScaled a := by
  have hfind :
      ((expStickyLowerNat : ℝ) / expX a) < (expN a : ℝ) :=
    Nat.find_spec (exists_nat_gt ((expStickyLowerNat : ℝ) / expX a))
  have hpow : (expN a : ℝ) < (2 : ℝ) ^ (expN a : ℕ) := by
    exact_mod_cast (Nat.lt_two_pow_self : expN a < 2 ^ expN a)
  have hdiv :
      ((expStickyLowerNat : ℝ) / expX a) < (2 : ℝ) ^ (expN a : ℕ) :=
    lt_trans hfind hpow
  have hmul' : (expStickyLowerNat : ℝ) < (2 : ℝ) ^ (expN a : ℕ) * expX a :=
    (div_lt_iff₀ (expX_pos a)).mp hdiv
  have hmul : (expStickyLowerNat : ℝ) < expX a * (2 : ℝ) ^ (expN a : ℕ) := by
    simpa [mul_comm] using hmul'
  have hzpow : (expStickyLowerNat : ℝ) < expX a * (2 : ℝ) ^ (expN a : ℤ) := by
    simpa [zpow_natCast] using hmul
  simpa [expScaled_eq_mul_pow] using hzpow

private theorem expQ_lower (a : FiniteFp) :
    expStickyLowerNat ≤ expQ a := by
  unfold expQ
  refine (Nat.le_floor_iff (expScaled_nonneg a)).2 ?_
  exact le_of_lt (expScaled_gt_stickyLower a)

private theorem expQ_le_scaled (a : FiniteFp) :
    (expQ a : ℝ) ≤ expScaled a := by
  unfold expQ
  exact Nat.floor_le (expScaled_nonneg a)

private theorem expScaled_lt_q_add_one (a : FiniteFp) :
    expScaled a < (expQ a : ℝ) + 1 := by
  unfold expQ
  simpa using Nat.lt_floor_add_one (expScaled a)

omit [FloatFormat] in
private theorem sticky_lo_rewrite (q : ℕ) (e : ℤ) :
    (2 * (q : ℝ)) * (2 : ℝ) ^ e = (q : ℝ) * (2 : ℝ) ^ (e + 1) := by
  rw [show e + 1 = e + (1 : ℤ) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

omit [FloatFormat] in
private theorem sticky_hi_rewrite (q : ℕ) (e : ℤ) :
    (2 * ((q : ℝ) + 1)) * (2 : ℝ) ^ e = ((q : ℝ) + 1) * (2 : ℝ) ^ (e + 1) := by
  rw [show e + 1 = e + (1 : ℤ) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

omit [FloatFormat] in
private theorem even_mag_rewrite (q : ℕ) (e : ℤ) :
    (((2 * q : ℕ) : ℝ) * (2 : ℝ) ^ e) = (q : ℝ) * (2 : ℝ) ^ (e + 1) := by
  have hcast : (((2 * q : ℕ) : ℝ)) = 2 * (q : ℝ) := by
    norm_num
  rw [hcast, sticky_lo_rewrite]

private noncomputable def expApproxConcrete (a : FiniteFp) : ExpApproxData :=
  if _ : a.m = 0 then
    .exact 2 (-1)
  else if _ : expScaled a = (expQ a : ℝ) then
    .exact (2 * expQ a) (expEBase a)
  else
    .sticky (expQ a) (expEBase a)

noncomputable instance (priority := 100) : ExpApprox where
  approx := expApproxConcrete

noncomputable instance (priority := 100) : ExpApproxSound where
  exact_mag_ne_zero := by
    intro a mag e_base h
    change expApproxConcrete a = .exact mag e_base at h
    unfold expApproxConcrete at h
    split_ifs at h with hz hExact
    · injection h with hmag _
      subst hmag
      norm_num
    · injection h with hmag _
      subst hmag
      have hQpos : 0 < expStickyLowerNat := by
        unfold expStickyLowerNat
        exact Nat.two_pow_pos _
      have hqpos : 0 < expQ a := lt_of_lt_of_le hQpos (expQ_lower a)
      omega
  exact_value := by
    intro a mag e_base h
    change expApproxConcrete a = .exact mag e_base at h
    unfold expApproxConcrete at h
    split_ifs at h with hz hExact
    · injection h with hmag he
      subst hmag
      subst he
      have htoVal0 : (a.toVal : ℝ) = 0 :=
        (FiniteFp.toVal_significand_zero_iff (R := ℝ)).mp hz
      unfold intSigVal
      simp [htoVal0]
    · injection h with hmag he
      subst hmag
      subst he
      have hpow_ne : (2 : ℝ) ^ (expEBase a + 1) ≠ 0 := by positivity
      have hx :
          expX a = (expQ a : ℝ) * (2 : ℝ) ^ (expEBase a + 1) := by
        have hscaled : expScaled a = (expQ a : ℝ) := hExact
        unfold expScaled at hscaled
        exact (div_eq_iff hpow_ne).mp hscaled
      unfold intSigVal
      calc
        (((2 * expQ a : ℕ) : ℝ) * (2 : ℝ) ^ expEBase a)
            = (expQ a : ℝ) * (2 : ℝ) ^ (expEBase a + 1) := by
              exact even_mag_rewrite _ _
        _ = expX a := hx.symm
        _ = Real.exp (a.toVal : ℝ) := rfl
  sticky_q_lower := by
    intro a q e_base h
    change expApproxConcrete a = .sticky q e_base at h
    by_cases hz : a.m = 0
    · simp [expApproxConcrete, hz] at h
    · by_cases hExact : expScaled a = (expQ a : ℝ)
      · simp [expApproxConcrete, hz, hExact] at h
      · have hsticky :
          ExpApproxData.sticky (expQ a) (expEBase a) = ExpApproxData.sticky q e_base := by
            simpa [expApproxConcrete, hz, hExact] using h
        injection hsticky with hq _
        subst hq
        exact expQ_lower a
  sticky_interval := by
    intro a q e_base h
    change expApproxConcrete a = .sticky q e_base at h
    by_cases hz : a.m = 0
    · simp [expApproxConcrete, hz] at h
    · by_cases hExact : expScaled a = (expQ a : ℝ)
      · simp [expApproxConcrete, hz, hExact] at h
      · have hsticky :
          ExpApproxData.sticky (expQ a) (expEBase a) = ExpApproxData.sticky q e_base := by
            simpa [expApproxConcrete, hz, hExact] using h
        injection hsticky with hq he
        subst hq
        subst he
        have hq_le : (expQ a : ℝ) ≤ expScaled a := expQ_le_scaled a
        have hq_lt : (expQ a : ℝ) < expScaled a := by
          exact lt_of_le_of_ne hq_le (by symm; exact hExact)
        have hq_hi : expScaled a < (expQ a : ℝ) + 1 := expScaled_lt_q_add_one a
        have hpow_pos : 0 < (2 : ℝ) ^ (expEBase a + 1) := by positivity
        have hlo_mul : (expQ a : ℝ) * (2 : ℝ) ^ (expEBase a + 1) < expX a := by
          have hdiv : (expQ a : ℝ) < expX a / (2 : ℝ) ^ (expEBase a + 1) := by
            simpa [expScaled] using hq_lt
          exact (lt_div_iff₀ hpow_pos).mp hdiv
        have hhi_mul : expX a < ((expQ a : ℝ) + 1) * (2 : ℝ) ^ (expEBase a + 1) := by
          have hdiv : expX a / (2 : ℝ) ^ (expEBase a + 1) < (expQ a : ℝ) + 1 := by
            simpa [expScaled] using hq_hi
          exact (div_lt_iff₀ hpow_pos).mp hdiv
        have hlo : (2 * (expQ a : ℝ)) * (2 : ℝ) ^ (expEBase a) < expX a := by
          rw [sticky_lo_rewrite]
          exact hlo_mul
        have hhi : expX a < (2 * ((expQ a : ℝ) + 1)) * (2 : ℝ) ^ (expEBase a) := by
          calc
            expX a < ((expQ a : ℝ) + 1) * (2 : ℝ) ^ (expEBase a + 1) := hhi_mul
            _ = (2 * ((expQ a : ℝ) + 1)) * (2 : ℝ) ^ (expEBase a) := by
                rw [sticky_hi_rewrite]
        simpa [inStickyInterval, expX] using And.intro hlo hhi

/-! ## Computable Reference-Kernel Scaffolding

This section introduces a computable execution interface meant for a softfloat-style
`exp` kernel (fixed-point range reduction + polynomial + reconstruction), together
with a soundness contract and adapter instances.
-/

namespace OpRefOut

/-- Convert executable reference output into operation-layer approximation data. -/
def toExpApproxData [FloatFormat] (o : OpRefOut) : ExpApproxData :=
  if o.isExact then .exact (2 * o.q) o.e_base else .sticky o.q o.e_base

/-- Helper constructor in quotient/remainder form, matching softfloat conventions. -/
def ofQuotRem (q rem : ℕ) (e_base : ℤ) : OpRefOut :=
  { q := q, e_base := e_base, isExact := decide (rem = 0) }

end OpRefOut

/-- The target function for exp: `a ↦ exp(toVal(a))`. Always positive. -/
noncomputable def expTarget (a : FiniteFp) : ℝ := Real.exp (a.toVal : ℝ)

-- Exp uses the generic `OpRefExec expTarget` and `OpRefExecSound expTarget` classes
-- from StickyExtract.lean. No exp-specific execution classes needed.

private noncomputable def expRefConcreteRun (a : FiniteFp) : OpRefOut :=
  if _ : a.m = 0 then
    { q := 1, e_base := -1, isExact := true }
  else if _ : expScaled a = (expQ a : ℝ) then
    { q := expQ a, e_base := expEBase a, isExact := true }
  else
    { q := expQ a, e_base := expEBase a, isExact := false }

private theorem expRefConcrete_toApproxData (a : FiniteFp) :
    OpRefOut.toExpApproxData (expRefConcreteRun a) = expApproxConcrete a := by
  unfold expRefConcreteRun OpRefOut.toExpApproxData expApproxConcrete
  by_cases hz : a.m = 0
  · simp [hz]
  · by_cases hEq : expScaled a = (expQ a : ℝ)
    · simp [hz, hEq]
    · simp [hz, hEq]

noncomputable instance (priority := 120) : OpRefExec expTarget where
  run := expRefConcreteRun

noncomputable instance (priority := 120) : OpRefExecSound expTarget where
  exact_mag_ne_zero := by
    intro a o hr hExact
    have ho : o = expRefConcreteRun a := by
      simpa [OpRefExec.run] using hr.symm
    subst ho
    have hto : OpRefOut.toExpApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .exact (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base := by
      simpa [OpRefOut.toExpApproxData, hExact] using hto.symm
    exact ExpApproxSound.exact_mag_ne_zero a
      (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base happ
  exact_value := by
    intro a o hr hExact
    have ho : o = expRefConcreteRun a := by
      simpa [OpRefExec.run] using hr.symm
    subst ho
    have hto : OpRefOut.toExpApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .exact (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base := by
      simpa [OpRefOut.toExpApproxData, hExact] using hto.symm
    exact ExpApproxSound.exact_value a
      (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base happ
  sticky_q_lower := by
    intro a o hr hFalse
    have ho : o = expRefConcreteRun a := by
      simpa [OpRefExec.run] using hr.symm
    subst ho
    have hto : OpRefOut.toExpApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .sticky (expRefConcreteRun a).q (expRefConcreteRun a).e_base := by
      simpa [OpRefOut.toExpApproxData, hFalse] using hto.symm
    exact ExpApproxSound.sticky_q_lower a
      (expRefConcreteRun a).q (expRefConcreteRun a).e_base happ
  sticky_interval := by
    intro a o hr hFalse
    have ho : o = expRefConcreteRun a := by
      simpa [OpRefExec.run] using hr.symm
    subst ho
    have hto : OpRefOut.toExpApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .sticky (expRefConcreteRun a).q (expRefConcreteRun a).e_base := by
      simpa [OpRefOut.toExpApproxData, hFalse] using hto.symm
    exact ExpApproxSound.sticky_interval a
      (expRefConcreteRun a).q (expRefConcreteRun a).e_base happ

instance (priority := 1000) [OpRefExec expTarget] : ExpApprox where
  approx a := OpRefOut.toExpApproxData (OpRefExec.run (target := expTarget) a)

/-- When `toExpApproxData o = .exact mag e_base`, we get `o.isExact = true` and parameter equalities. -/
private theorem toExpApproxData_exact {o : OpRefOut} {mag : ℕ} {e_base : ℤ}
    (h : o.toExpApproxData = .exact mag e_base) :
    o.isExact = true ∧ mag = 2 * o.q ∧ e_base = o.e_base := by
  simp only [OpRefOut.toExpApproxData] at h
  split at h <;> simp_all

/-- When `toExpApproxData o = .sticky q e_base`, we get `o.isExact = false` and parameter equalities. -/
private theorem toExpApproxData_sticky {o : OpRefOut} {q : ℕ} {e_base : ℤ}
    (h : o.toExpApproxData = .sticky q e_base) :
    o.isExact = false ∧ q = o.q ∧ e_base = o.e_base := by
  simp only [OpRefOut.toExpApproxData] at h
  split at h <;> simp_all

instance (priority := 1000) [OpRefExec expTarget] [OpRefExecSound expTarget] : ExpApproxSound where
  exact_mag_ne_zero := by
    intro a mag e_base h
    obtain ⟨hExact, hmag, he⟩ := toExpApproxData_exact h
    subst hmag; subst he
    exact OpRefExecSound.exact_mag_ne_zero (target := expTarget) a _ rfl hExact
  exact_value := by
    intro a mag e_base h
    obtain ⟨hExact, hmag, he⟩ := toExpApproxData_exact h
    subst hmag; subst he
    exact OpRefExecSound.exact_value (target := expTarget) a _ rfl hExact
  sticky_q_lower := by
    intro a q e_base h
    obtain ⟨hFalse, hq, he⟩ := toExpApproxData_sticky h
    subst hq; subst he
    exact OpRefExecSound.sticky_q_lower (target := expTarget) a _ rfl hFalse
  sticky_interval := by
    intro a q e_base h
    obtain ⟨hFalse, hq, he⟩ := toExpApproxData_sticky h
    subst hq; subst he
    exact OpRefExecSound.sticky_interval (target := expTarget) a _ rfl hFalse

/-! ## Overflow behavior -/

/-- When `exp(a)` overflows (i.e., `exp(a.toVal) ≥ overflowThreshold`), `fpExp` returns `+∞`. -/
theorem fpExpFinite_overflow
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]
    (a : FiniteFp)
    (h_overflow : FloatFormat.overflowThreshold ℝ ≤ Real.exp (a.toVal : ℝ)) :
    fpExpFinite a = Fp.infinite false := by
  rw [fpExpFinite_correct a]
  exact RModeNearest.overflow_pos_inf _ h_overflow

/-- `fpExp` on a finite input whose `exp` overflows returns `+∞`. -/
theorem fpExp_finite_overflow
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]
    (a : FiniteFp)
    (h_overflow : FloatFormat.overflowThreshold ℝ ≤ Real.exp (a.toVal : ℝ)) :
    fpExp (Fp.finite a) = Fp.infinite false := by
  simp [fpExpFinite_overflow a h_overflow]

/-! ## Monotonicity -/

/-- `fpExpFinite` is monotone: if `a.toVal ≤ b.toVal` then `fpExpFinite a ≤ fpExpFinite b`. -/
theorem fpExpFinite_mono
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeMono ℝ] [ExpApprox] [ExpApproxSound]
    (a b : FiniteFp) (h : (a.toVal : ℝ) ≤ (b.toVal : ℝ)) :
    fpExpFinite a ≤ fpExpFinite b := by
  rw [fpExpFinite_correct a, fpExpFinite_correct b]
  exact RModeMono.round_mono (Real.exp_monotone h)

/-- `fpExp` is monotone on finite inputs. -/
theorem fpExp_finite_mono
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeMono ℝ] [ExpApprox] [ExpApproxSound]
    (a b : FiniteFp) (h : (a.toVal : ℝ) ≤ (b.toVal : ℝ)) :
    fpExp (Fp.finite a) ≤ fpExp (Fp.finite b) := by
  simp only [fpExp_finite]
  exact fpExpFinite_mono a b h

/-! ## Relative error -/

/-- Relative error bound for `fpExpFinite` under nearest rounding modes.
When `exp(a.toVal)` is in normal range and the result is finite, the relative
error is at most half machine epsilon `2^(-prec)`. -/
theorem fpExpFinite_relativeError_le
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]
    (a : FiniteFp)
    (h_normal : isNormalRange (Real.exp (a.toVal : ℝ)))
    (f : FiniteFp) (hf : fpExpFinite a = Fp.finite f) :
    Fp.relativeError (Real.exp (a.toVal : ℝ)) f ≤
      (2 : ℝ) ^ (-(FloatFormat.prec : ℤ)) := by
  rw [fpExpFinite_correct a] at hf
  exact RModeNearest_relativeError_le_half _ h_normal f hf

/-! ## Faithfulness -/

/-- `fpExpFinite` is faithfully rounded: the result is either `roundDown` or `roundUp`
of the exact exponential. -/
theorem fpExpFinite_faithful
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]
    (a : FiniteFp) :
    fpExpFinite a = roundDown (Real.exp (a.toVal : ℝ)) ∨
      fpExpFinite a = roundUp (Real.exp (a.toVal : ℝ)) := by
  rw [fpExpFinite_correct a]
  exact RModeNearest.round_eq_roundDown_or_roundUp _

/-! ## Exact case -/

/-- `exp(+0) = 1.0` exactly: the exponential of positive zero is the float `1`. -/
theorem fpExpFinite_zero
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeC ℝ] [ExpApprox] [ExpApproxSound]
    : fpExpFinite (0 : FiniteFp) = Fp.finite 1 := by
  rw [fpExpFinite_correct (0 : FiniteFp)]
  rw [FiniteFp.toVal_zero, Real.exp_zero]
  rw [show (1 : ℝ) = (FiniteFp.toVal (1 : FiniteFp) : ℝ) from
    (FiniteFp.toVal_one).symm]
  exact RModeIdem.round_idempotent (1 : FiniteFp) (Or.inl rfl)

/-- `fpExp(+0) = 1.0` at the `Fp` level. -/
theorem fpExp_zero
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeC ℝ] [ExpApprox] [ExpApproxSound]
    : fpExp (Fp.finite 0) = Fp.finite 1 := by
  simp [fpExpFinite_zero]

/-! ## Non-negativity and underflow -/

/-- `fpExpFinite` always returns a non-negative result (`≥ +0`).
This follows from `exp(x) > 0`, monotonicity of rounding, and `round(0) = +0`. -/
theorem fpExpFinite_nonneg
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeC ℝ] [ExpApprox] [ExpApproxSound]
    (a : FiniteFp) :
    Fp.finite 0 ≤ fpExpFinite a := by
  rw [fpExpFinite_correct a]
  rw [← RModeZero.round_zero (R := ℝ)]
  exact RModeMono.round_mono (le_of_lt (Real.exp_pos _))

/-- When `exp(a.toVal)` is below the smallest positive subnormal, `fpExpFinite` returns
either `+0` or the smallest subnormal (i.e., a flush-to-zero or minimum representable). -/
theorem fpExpFinite_underflow
    [RMode ℝ] [RModeExec] [RoundIntSigMSound ℝ] [RModeSticky ℝ]
    [RModeNearest ℝ] [ExpApprox] [ExpApproxSound]
    (a : FiniteFp)
    (h : Real.exp (a.toVal : ℝ) < FiniteFp.smallestPosSubnormal.toVal) :
    fpExpFinite a = Fp.finite 0 ∨
      fpExpFinite a = Fp.finite FiniteFp.smallestPosSubnormal := by
  rw [fpExpFinite_correct a]
  have hpos := Real.exp_pos (a.toVal : ℝ)
  rcases RModeNearest.round_eq_roundDown_or_roundUp (Real.exp (a.toVal : ℝ)) with hrd | hru
  · left; rw [hrd]
    exact roundDown_lt_smallestPosSubnormal _ hpos h
  · right; rw [hru]
    exact roundUp_lt_smallestPosSubnormal _ hpos h

end Exp
