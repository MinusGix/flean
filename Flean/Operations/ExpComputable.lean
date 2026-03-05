import Flean.Operations.ExpComputableSound
import Flean.Operations.ExpTermination

/-! # Computable `OpRefExec` and `OpRefExecSound` Instances for exp

Provides a fully verified computable `exp` for floating-point arithmetic. The computation
returns either an exact representation or a "sticky cell" bracketing `exp(x)`, and the
proof establishes that the result is always correct. **All proofs are sorry-free.**

## Algorithm

1. **Special case**: `x = ±0` → return exact `exp(0) = 1`.
2. **Argument reduction** (`expArgRedK`): compute `k = round(x / ln 2)` using a rational
   approximation to `ln 2`, giving `exp(x) = 2^k · exp(r)` with `|r| < 1`.
3. **Iterative refinement** (`stickyExtractLoop (expBounds x k)`): at increasing precision
   levels `iter`, compute rational brackets `(lower, upper)` around `exp(x)` via Taylor
   series with explicit Lagrange remainder (`expBounds`), then check if
   `⌊lower · 2^s⌋ = ⌊upper · 2^s⌋`. When floors agree, we've identified the sticky cell.
4. **Output**: `{q, e_base, isExact}` where `exp(x) ∈ (2q · 2^e_base, 2(q+1) · 2^e_base)`.

## Proof structure

Two independent threads meet at `expLoop_sound`:

### Thread 1 — Bracket correctness (each step is sound)
```
taylorExpQ_lt_exp, exp_le_taylor_upper    -- Taylor bounds on exp(r)
    → expBounds_lower_lt_exp              -- lower < exp(x)
    → expBounds_exp_le_upper              -- exp(x) ≤ upper
    → inStickyInterval_of_bracket         -- floor agreement → sticky cell
    → stickyTryOne_sound / stickyExtractLoop_sound  -- generic loop soundness
```

### Thread 2 — Termination (the loop eventually succeeds within `expFuel x` steps)
```
pade_effective_delta (PadeExp.lean)        -- ∃ δ > 0, exp(x)·2^s avoids integers by ≥ δ
    → padeConvergenceN₀_le                -- Padé threshold ≤ 27·ab
    → pade_delta_log_bound                -- 1/δ ≤ 2^(114·ab·log(ab))
    → expBounds_width_bound               -- bracket width ≤ C · (1/N! + 1/2^N_ln2)
    → expFuel_sufficient                  -- ∃ iter < expFuel(x), width < δ
    → stickyTryOne_expBounds_terminates
```

### Meeting point: `expLoop_sound`
Combines `stickyExtractLoop_sound` (correctness) with `stickyTryOne_expBounds_terminates`
(termination) to prove the loop output is valid. The four `OpRefExecSound expTarget`
obligations then follow directly.

## File organization
- `StickyExtract.lean`: generic sticky cell extraction (`stickyTryOne`, `stickyExtractLoop`)
- `ExpTaylor.lean`: Taylor series machinery (`taylorExpQ`, `taylorRemainder`, bounds)
- `ExpComputableDefs.lean`: computation definitions + `expBounds` + `OpRefExec expTarget` instance
- `ExpComputableSound.lean`: bracket correctness (Thread 1)
- `ExpTermination.lean`: width bounds + termination proof (Thread 2)
- `ExpComputable.lean` (this file): final assembly + `OpRefExecSound expTarget` instance
-/

section ExpComputable

variable [FloatFormat]

/-- **Meeting point of correctness and termination.**

For nonzero x, the loop output brackets exp(x) in a valid sticky cell with q ≥ 2^(prec+2).

This is where Thread 1 (bracket correctness) and Thread 2 (termination) meet:
- `stickyExtractLoop_sound` needs `0 < s.q` to conclude the result is correct.
- `stickyExtractLoop_pos_of_success` derives `0 < s.q` from `stickyTryOne_expBounds_terminates`,
  which guarantees some iteration succeeds within `expFuel x` steps.
- `stickyExtractLoop_q_ge` then lifts `0 < s.q` to `2^(prec+2) ≤ s.q`. -/
private theorem expLoop_sound (x : ℚ) (hx : x ≠ 0) (k : ℤ)
    (hk_bound : |(x : ℝ) - ↑k * Real.log 2| < 1) :
    let s := stickyExtractLoop (expBounds x k) 0 (expFuel x)
    2 ^ (FloatFormat.prec.toNat + 2) ≤ s.q ∧
    inStickyInterval (R := ℝ) s.q s.e_base (Real.exp (x : ℝ)) := by
  set s := stickyExtractLoop (expBounds x k) 0 (expFuel x) with hs
  suffices hq_pos : 0 < s.q by
    exact ⟨stickyExtractLoop_q_ge (expBounds x k) 0 (expFuel x)
              (fun i => expBounds_lower_pos x k i) hq_pos,
           stickyExtractLoop_sound (expBounds x k) 0 (expFuel x) (Real.exp (x : ℝ))
              (fun i => expBounds_lower_pos x k i)
              (fun i => expBounds_lower_lt_exp x hx k i hk_bound)
              (fun i => expBounds_exp_le_upper x k i hk_bound) hq_pos⟩
  rw [hs]
  apply stickyExtractLoop_pos_of_success (expBounds x k) 0 (expFuel x)
    (fun i => expBounds_lower_pos x k i)
  exact stickyTryOne_expBounds_terminates x hx k hk_bound

/-! ## Main soundness theorems -/

/-- Shared preamble for the sticky-cell proofs: for nonzero input, `expComputableRun`
reduces to `stickyExtractLoop` and `expLoop_sound` applies. -/
private theorem expComputableRun_loop_sound (a : FiniteFp) (o : OpRefOut)
    (hr : expComputableRun a = o) (hFalse : o.isExact = false) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q ∧
    inStickyInterval (R := ℝ) o.q o.e_base (Real.exp (a.toVal (R := ℚ) : ℝ)) := by
  have hm : a.m ≠ 0 := by
    intro h; rw [expComputableRun_zero a h] at hr; rw [← hr] at hFalse; exact absurd hFalse (by decide)
  have hx : (a.toVal : ℚ) ≠ 0 :=
    FiniteFp.toVal_ne_zero_of_m_pos a (Nat.pos_of_ne_zero hm)
  set x : ℚ := a.toVal with hx_def
  set k := expArgRedK x with hk_def
  have hval : expComputableRun a =
      (stickyExtractLoop (expBounds x k) 0 (expFuel x)).toOpRefOut := by
    simp only [expComputableRun, hm, ↓reduceIte, hx_def, hk_def]
  rw [hval] at hr; rw [← hr]
  simp only [StickyOut.toOpRefOut_q, StickyOut.toOpRefOut_e_base]
  exact expLoop_sound x hx k (expArgRedK_bound x)

private theorem expComputableRun_sticky_q_lower (a : FiniteFp) (o : OpRefOut)
    (hr : expComputableRun a = o) (hFalse : o.isExact = false) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q :=
  (expComputableRun_loop_sound a o hr hFalse).1

private theorem expComputableRun_sticky_interval (a : FiniteFp) (o : OpRefOut)
    (hr : expComputableRun a = o) (hFalse : o.isExact = false) :
    inStickyInterval (R := ℝ) o.q o.e_base (Real.exp (a.toVal : ℝ)) := by
  have hsound := (expComputableRun_loop_sound a o hr hFalse).2
  rw [← FiniteFp.toVal_ratCast]; exact hsound

/-! ## OpRefExecSound expTarget instance

The final assembly. Each obligation routes through `expLoop_sound`:
- `exact_value`, `exact_mag_ne_zero`: the `x = 0` branch (trivial).
- `sticky_q_lower`, `sticky_interval`: the `x ≠ 0` branch, via `expLoop_sound`. -/

instance (priority := 500) : OpRefExecSound expTarget where
  exact_mag_ne_zero := fun a o hr hExact => by
    have := expComputableRun_exact_mag_ne_zero a o hr hExact; omega
  exact_value := fun a o hr hExact =>
    expComputableRun_exact_value a o hr hExact
  sticky_q_lower := fun a o hr hFalse =>
    expComputableRun_sticky_q_lower a o hr hFalse
  sticky_interval := fun a o hr hFalse =>
    expComputableRun_sticky_interval a o hr hFalse

end ExpComputable

/-! ## Smoke tests -/

-- exp(0) = 1: exact case
#eval
  letI : FloatFormat := FloatFormat.Binary16.toFloatFormat
  expComputableRun (0 : FiniteFp)

-- exp(1) for binary16 (s=false, e=0, m=2^10=1024)
#eval
  letI : FloatFormat := FloatFormat.Binary16.toFloatFormat
  expComputableRun ⟨false, 0, 1024, by native_decide⟩
