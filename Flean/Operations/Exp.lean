import Flean.Operations.RoundIntSig
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Floating-Point Exponential (Skeleton + Constructive Roadmap)

This module provides the operation-layer skeleton for `exp` in the same style as
other operations:

- execution path computes either an exact integer-significand representation or
  a sticky representative,
- semantic correctness is discharged separately via typeclass contracts,
- sticky correctness reuses `sticky_roundIntSig_eq_round_tc`.

The current implementation keeps algorithmic details behind `ExpApprox` / `ExpRefExec`.
The long-term plan is a fully constructive, softfloat-style kernel.

## Constructive Roadmap (deferred)

1. Target contract:
   - keep `ExpRefExec.run` executable (no `Real` decisions in code),
   - prove `ExpRefExecSound` in `ℝ`,
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
   - land baseline constructive `ExpRefExec`,
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
    · have hcontra : ExpApproxData.exact 2 (-1) = ExpApproxData.sticky q e_base := by
        simpa [expApproxConcrete, hz] using h
      cases hcontra
    · by_cases hExact : expScaled a = (expQ a : ℝ)
      · have hcontra :
          ExpApproxData.exact (2 * expQ a) (expEBase a) = ExpApproxData.sticky q e_base := by
            simpa [expApproxConcrete, hz, hExact] using h
        cases hcontra
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
    · have hcontra : ExpApproxData.exact 2 (-1) = ExpApproxData.sticky q e_base := by
        simpa [expApproxConcrete, hz] using h
      cases hcontra
    · by_cases hExact : expScaled a = (expQ a : ℝ)
      · have hcontra :
          ExpApproxData.exact (2 * expQ a) (expEBase a) = ExpApproxData.sticky q e_base := by
            simpa [expApproxConcrete, hz, hExact] using h
        cases hcontra
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

/-- Executable reference-kernel output shape.

`isExact = true` encodes exact branch with magnitude `2*q`.
`isExact = false` encodes sticky branch with sticky index `q`.
-/
structure ExpRefOut where
  q : ℕ
  e_base : ℤ
  isExact : Bool
deriving Repr, DecidableEq

/-- Convert executable reference output into operation-layer approximation data. -/
def ExpRefOut.toApproxData (o : ExpRefOut) : ExpApproxData :=
  if o.isExact then .exact (2 * o.q) o.e_base else .sticky o.q o.e_base

/-- Helper constructor in quotient/remainder form, matching softfloat conventions. -/
def ExpRefOut.ofQuotRem (q rem : ℕ) (e_base : ℤ) : ExpRefOut :=
  { q := q, e_base := e_base, isExact := decide (rem = 0) }

/-- Computable reference-kernel execution hook for `exp`. -/
class ExpRefExec where
  run : FiniteFp → ExpRefOut

/-- Soundness contract for a computable reference-kernel execution hook. -/
class ExpRefExecSound [ExpRefExec] : Prop where
  exact_mag_ne_zero :
    ∀ (a : FiniteFp) (o : ExpRefOut),
      ExpRefExec.run a = o →
      o.isExact = true →
      (2 * o.q) ≠ 0
  exact_value :
    ∀ (a : FiniteFp) (o : ExpRefOut),
      ExpRefExec.run a = o →
      o.isExact = true →
      intSigVal (R := ℝ) false (2 * o.q) o.e_base = Real.exp (a.toVal : ℝ)
  sticky_q_lower :
    ∀ (a : FiniteFp) (o : ExpRefOut),
      ExpRefExec.run a = o →
      o.isExact = false →
      2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q
  sticky_interval :
    ∀ (a : FiniteFp) (o : ExpRefOut),
      ExpRefExec.run a = o →
      o.isExact = false →
      inStickyInterval (R := ℝ) o.q o.e_base (Real.exp (a.toVal : ℝ))

private noncomputable def expRefConcreteRun (a : FiniteFp) : ExpRefOut :=
  if _ : a.m = 0 then
    { q := 1, e_base := -1, isExact := true }
  else if _ : expScaled a = (expQ a : ℝ) then
    { q := expQ a, e_base := expEBase a, isExact := true }
  else
    { q := expQ a, e_base := expEBase a, isExact := false }

private theorem expRefConcrete_toApproxData (a : FiniteFp) :
    ExpRefOut.toApproxData (expRefConcreteRun a) = expApproxConcrete a := by
  unfold expRefConcreteRun ExpRefOut.toApproxData expApproxConcrete
  by_cases hz : a.m = 0
  · simp [hz]
  · by_cases hEq : expScaled a = (expQ a : ℝ)
    · simp [hz, hEq]
    · simp [hz, hEq]

noncomputable instance (priority := 120) : ExpRefExec where
  run := expRefConcreteRun

noncomputable instance (priority := 120) : ExpRefExecSound where
  exact_mag_ne_zero := by
    intro a o hr hExact
    have ho : o = expRefConcreteRun a := by
      simpa [ExpRefExec.run] using hr.symm
    subst ho
    have hto : ExpRefOut.toApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .exact (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base := by
      simpa [ExpRefOut.toApproxData, hExact] using hto.symm
    exact ExpApproxSound.exact_mag_ne_zero a
      (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base happ
  exact_value := by
    intro a o hr hExact
    have ho : o = expRefConcreteRun a := by
      simpa [ExpRefExec.run] using hr.symm
    subst ho
    have hto : ExpRefOut.toApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .exact (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base := by
      simpa [ExpRefOut.toApproxData, hExact] using hto.symm
    exact ExpApproxSound.exact_value a
      (2 * (expRefConcreteRun a).q) (expRefConcreteRun a).e_base happ
  sticky_q_lower := by
    intro a o hr hFalse
    have ho : o = expRefConcreteRun a := by
      simpa [ExpRefExec.run] using hr.symm
    subst ho
    have hto : ExpRefOut.toApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .sticky (expRefConcreteRun a).q (expRefConcreteRun a).e_base := by
      simpa [ExpRefOut.toApproxData, hFalse] using hto.symm
    exact ExpApproxSound.sticky_q_lower a
      (expRefConcreteRun a).q (expRefConcreteRun a).e_base happ
  sticky_interval := by
    intro a o hr hFalse
    have ho : o = expRefConcreteRun a := by
      simpa [ExpRefExec.run] using hr.symm
    subst ho
    have hto : ExpRefOut.toApproxData (expRefConcreteRun a) = expApproxConcrete a :=
      expRefConcrete_toApproxData a
    have happ : expApproxConcrete a =
        .sticky (expRefConcreteRun a).q (expRefConcreteRun a).e_base := by
      simpa [ExpRefOut.toApproxData, hFalse] using hto.symm
    exact ExpApproxSound.sticky_interval a
      (expRefConcreteRun a).q (expRefConcreteRun a).e_base happ

instance (priority := 1000) [ExpRefExec] : ExpApprox where
  approx a := (ExpRefOut.toApproxData (ExpRefExec.run a))

instance (priority := 1000) [ExpRefExec] [ExpRefExecSound] : ExpApproxSound where
  exact_mag_ne_zero := by
    intro a mag e_base h
    let o := ExpRefExec.run a
    have hr : ExpRefExec.run a = o := rfl
    change ExpRefOut.toApproxData o = .exact mag e_base at h
    by_cases hExact : o.isExact = true
    · have hEq : ExpApproxData.exact (2 * o.q) o.e_base = ExpApproxData.exact mag e_base := by
        simpa [ExpRefOut.toApproxData, hExact] using h
      injection hEq with hmag _
      subst hmag
      exact ExpRefExecSound.exact_mag_ne_zero a o hr hExact
    · have hContra : ExpApproxData.sticky o.q o.e_base = ExpApproxData.exact mag e_base := by
        simpa [ExpRefOut.toApproxData, hExact] using h
      cases hContra
  exact_value := by
    intro a mag e_base h
    let o := ExpRefExec.run a
    have hr : ExpRefExec.run a = o := rfl
    change ExpRefOut.toApproxData o = .exact mag e_base at h
    by_cases hExact : o.isExact = true
    · have hEq : ExpApproxData.exact (2 * o.q) o.e_base = ExpApproxData.exact mag e_base := by
        simpa [ExpRefOut.toApproxData, hExact] using h
      injection hEq with hmag he
      subst hmag
      subst he
      exact ExpRefExecSound.exact_value a o hr hExact
    · have hContra : ExpApproxData.sticky o.q o.e_base = ExpApproxData.exact mag e_base := by
        simpa [ExpRefOut.toApproxData, hExact] using h
      cases hContra
  sticky_q_lower := by
    intro a q e_base h
    let o := ExpRefExec.run a
    have hr : ExpRefExec.run a = o := rfl
    change ExpRefOut.toApproxData o = .sticky q e_base at h
    by_cases hExact : o.isExact = true
    · have hContra : ExpApproxData.exact (2 * o.q) o.e_base = ExpApproxData.sticky q e_base := by
        simpa [ExpRefOut.toApproxData, hExact] using h
      cases hContra
    · have hFalse : o.isExact = false := by
        cases hB : o.isExact
        · simpa [hB]
        · exfalso
          exact hExact (by simpa [hB])
      have hEq : ExpApproxData.sticky o.q o.e_base = ExpApproxData.sticky q e_base := by
        simpa [ExpRefOut.toApproxData, hFalse] using h
      injection hEq with hq _
      subst hq
      exact ExpRefExecSound.sticky_q_lower a o hr hFalse
  sticky_interval := by
    intro a q e_base h
    let o := ExpRefExec.run a
    have hr : ExpRefExec.run a = o := rfl
    change ExpRefOut.toApproxData o = .sticky q e_base at h
    by_cases hExact : o.isExact = true
    · have hContra : ExpApproxData.exact (2 * o.q) o.e_base = ExpApproxData.sticky q e_base := by
        simpa [ExpRefOut.toApproxData, hExact] using h
      cases hContra
    · have hFalse : o.isExact = false := by
        cases hB : o.isExact
        · simpa [hB]
        · exfalso
          exact hExact (by simpa [hB])
      have hEq : ExpApproxData.sticky o.q o.e_base = ExpApproxData.sticky q e_base := by
        simpa [ExpRefOut.toApproxData, hFalse] using h
      injection hEq with hq he
      subst hq
      subst he
      exact ExpRefExecSound.sticky_interval a o hr hFalse

end Exp
