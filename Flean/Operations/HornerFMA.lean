import Flean.Operations.KahanSum
import Flean.Operations.FMA
import Flean.Operations.Horner

/-!
# FMA-Based Horner's Method Error Bound

When Horner's method uses fused multiply-add (FMA), each step
`sₖ = fma(s_{k-1}, x, a_{n-k})` incurs only ONE rounding error instead of two.
This halves the error exponent from `2n` to `n`:

  `|fl(p(x)) - p(x)| ≤ ((1+η)^n - 1) · p̃(|x|) ≤ γₙ · p̃(|x|)`

compared to the non-FMA bound `γ_{2n} · p̃(|x|)`.
-/

namespace HornerFMA

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## FMA Error Bound -/

/-- When the exact FMA result is zero, the fp result is also zero. -/
private theorem fpFMA_exact_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b c : FiniteFp) (f : FiniteFp)
    (hf : fpFMAFinite a b c = Fp.finite f)
    (hzero : (a.toVal : R) * b.toVal + c.toVal = 0) :
    (f.toVal : R) = 0 := by
  have hsum_zero : fmaAlignedSumInt a b c = 0 := by
    have hexact := fpFMAFinite_exact_sum R a b c
    rw [hzero] at hexact
    have h0 : ((fmaAlignedSumInt a b c : ℤ) : R) * (2 : R) ^ (fmaEMin a b c - FloatFormat.prec + 1) = 0 :=
      hexact.symm
    rcases mul_eq_zero.mp h0 with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt (by positivity))
  have hcancel := fpFMAFinite_exact_cancel_sign a b c hsum_zero
  rw [hcancel] at hf
  exact FiniteFp.toVal_isZero (by rw [← Fp.finite.inj hf])

/-- FMA error bound: `|fl(a*b + c) - (a*b + c)| ≤ η · |a*b + c|`. -/
theorem fpFMA_error_or_zero
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (a b c : FiniteFp) (f : FiniteFp)
    (hf : fpFMAFinite a b c = Fp.finite f)
    (hnormal : isNormalRange ((a.toVal : R) * b.toVal + c.toVal) ∨
               (a.toVal : R) * b.toVal + c.toVal = 0) :
    |(f.toVal : R) - (a.toVal * b.toVal + c.toVal)| ≤
      η * |(a.toVal : R) * b.toVal + c.toVal| := by
  rcases hnormal with h | h
  · have hne : (a.toVal : R) * b.toVal + c.toVal ≠ 0 := ne_of_gt (isNormalRange_pos _ h)
    have hcorr := fpFMAFinite_correct (R := R) a b c hne
    rw [hcorr] at hf
    exact KahanSum.standard_error_additive _ h f hf
  · rw [h, fpFMA_exact_zero (R := R) a b c f hf h]; simp

/-! ## Step and Trace -/

/-- One step of FMA-based Horner: `next = fma(acc, x, coeff)`. -/
structure FMAStep [RModeExec] (acc x coeff : FiniteFp) where
  next : FiniteFp
  hnext : fpFMAFinite acc x coeff = Fp.finite next

/-- Normal range hypothesis for an FMA Horner step. -/
structure FMAStepNormalRange [RModeExec] (acc x coeff : FiniteFp)
    (step : FMAStep acc x coeff) where
  fma_normal : isNormalRange ((acc.toVal : R) * x.toVal + coeff.toVal) ∨
               (acc.toVal : R) * x.toVal + coeff.toVal = 0

/-- Trace of FMA-based Horner evaluation. -/
inductive FMATrace [RModeExec] (x : FiniteFp) :
    List FiniteFp → FiniteFp → FiniteFp → Type where
  | nil (acc : FiniteFp) : FMATrace x [] acc acc
  | cons {acc coeff : FiniteFp} {coeffs : List FiniteFp} {final : FiniteFp}
      (step : FMAStep acc x coeff)
      (rest : FMATrace x coeffs step.next final) :
      FMATrace x (coeff :: coeffs) acc final

/-- All steps are in normal range. -/
def FMATrace.AllNormalRange [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {acc final : FiniteFp} →
    FMATrace x coeffs acc final → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons (acc := acc) (coeff := coeff) step rest =>
      FMAStepNormalRange (R := R) acc x coeff step ∧ rest.AllNormalRange

/-! ## Error Bound -/

/-- **FMA Horner error bound** (`(1+η)^n` form).

    With FMA, each step has only ONE rounding error, giving exponent `n` instead of `2n`:
    `|final - hornerPoly(coeffs, init, x)| ≤ ((1+η)^n - 1) · hornerPoly(|coeffs|, |init|, |x|)`

    This is half the exponent of the non-FMA bound. -/
theorem fma_horner_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : FMATrace x coeffs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      ((1 + η) ^ coeffs.length - 1) *
        Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |init.toVal (R := R)| |x.toVal (R := R)| := by
  induction trace with
  | nil acc =>
    simp only [List.map_nil, Horner.hornerPoly, List.length_nil, pow_zero, sub_self, zero_mul,
               abs_zero, le_refl]
  | @cons acc coeff coeffs final step rest ih =>
    simp only [FMATrace.AllNormalRange] at hnr
    obtain ⟨hnr_step, hnr_rest⟩ := hnr
    -- FMA error: |next - (acc*x + coeff)| ≤ η|acc*x + coeff|
    have hfma := fpFMA_error_or_zero (R := R) acc x coeff step.next step.hnext
      hnr_step.fma_normal
    -- Abbreviations
    set n := coeffs.length with hn_def
    set acc_v := (acc.toVal : R)
    set x_v := (x.toVal : R)
    set c_v := (coeff.toVal : R)
    set next_v := (step.next.toVal : R)
    set A := |acc_v| * |x_v| + |c_v|
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    -- Per-step error: |next - (acc*x + c)| ≤ η * |acc*x + c| ≤ η * A
    have hstep_err : |next_v - (acc_v * x_v + c_v)| ≤ η * A := by
      calc |next_v - (acc_v * x_v + c_v)|
          ≤ η * |acc_v * x_v + c_v| := hfma
        _ ≤ η * A := by
            apply mul_le_mul_of_nonneg_left _ hη
            calc |acc_v * x_v + c_v| ≤ |acc_v * x_v| + |c_v| := abs_add_le _ _
              _ = |acc_v| * |x_v| + |c_v| := by rw [abs_mul]
    -- |next| ≤ (1+η) * A
    have hnext_bound : |next_v| ≤ (1 + η) * A := by
      have h1 := abs_sub_abs_le_abs_sub next_v (acc_v * x_v + c_v)
      have h2 : |acc_v * x_v + c_v| ≤ A := by
        calc |acc_v * x_v + c_v| ≤ |acc_v * x_v| + |c_v| := abs_add_le _ _
          _ = A := by rw [abs_mul]
      linarith
    -- IH
    have ih_bound := ih hnr_rest
    -- Powers and nonnegativity
    have hpow_n : (1 : R) ≤ (1 + η) ^ n := one_le_pow₀ h1η
    have hpow_n_nn : (0 : R) ≤ (1 + η) ^ n := le_trans zero_le_one hpow_n
    have hA_nn : (0 : R) ≤ A := by positivity
    have hxabs_nn : (0 : R) ≤ |x_v| := abs_nonneg _
    have hxpow_nn : (0 : R) ≤ |x_v| ^ n := by positivity
    -- Absolute polynomial abbreviations
    set PA := Horner.hornerPoly (coeffs.map (fun c => |(c.toVal : R)|)) A |x_v|
    set PA_nxt := Horner.hornerPoly (coeffs.map (fun c => |(c.toVal : R)|)) |next_v| |x_v|
    have hlen : (coeffs.map (fun c => |(c.toVal : R)|)).length = n := by simp [hn_def]
    -- PA(|next|) ≤ PA(A) + (η * A) * |x|^n  (via affine + |next| ≤ (1+η)A)
    have hPA_mono : PA_nxt ≤ PA + η * A * |x_v| ^ n := by
      have hdecomp : |next_v| = A + (|next_v| - A) := by ring
      show Horner.hornerPoly _ |next_v| |x_v| ≤ PA + η * A * |x_v| ^ n
      conv_lhs => rw [hdecomp]
      rw [Horner.hornerPoly_affine, hlen]
      have hle : |next_v| - A ≤ η * A := by linarith
      linarith [mul_le_mul_of_nonneg_right hle hxpow_nn]
    -- PA ≥ A * |x|^n  (the accumulator part)
    have hPA_ge : A * |x_v| ^ n ≤ PA := by
      conv_lhs => rw [show A = 0 + A from (zero_add A).symm]
      rw [show PA = Horner.hornerPoly _ A _ from rfl]
      rw [show A = 0 + A from (zero_add A).symm, Horner.hornerPoly_affine, hlen]
      linarith [Horner.hornerPoly_nonneg (coeffs.map (fun c => |(c.toVal : R)|)) 0 |x_v|
        le_rfl (abs_nonneg _) (fun c hc => by
          simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; exact abs_nonneg _)]
    have hPA_nn : (0 : R) ≤ PA := le_trans (mul_nonneg hA_nn hxpow_nn) hPA_ge
    -- Triangle via hornerPoly_affine
    have htri : |(final.toVal : R) -
        Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v| ≤
        |(final.toVal : R) -
          Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v| +
        |next_v - (acc_v * x_v + c_v)| * |x_v| ^ n := by
      have hlen2 : (coeffs.map (fun c => (c.toVal : R))).length = n := by simp [hn_def]
      have haffine : Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v =
          Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v +
          (next_v - (acc_v * x_v + c_v)) * x_v ^ n := by
        conv_lhs => rw [show next_v = (acc_v * x_v + c_v) + (next_v - (acc_v * x_v + c_v)) from
                        by ring]
        rw [Horner.hornerPoly_affine, hlen2]
      have heq : (final.toVal : R) -
          Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v =
          ((final.toVal : R) -
            Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v) +
          (next_v - (acc_v * x_v + c_v)) * x_v ^ n := by linarith
      rw [heq]
      have := abs_add_le
        ((final.toVal : R) - Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v)
        ((next_v - (acc_v * x_v + c_v)) * x_v ^ n)
      rwa [abs_mul, abs_pow] at this
    -- Combine: total ≤ ((1+η)^n - 1)(PA + ηA|x|^n) + ηA|x|^n
    --              = ((1+η)^n - 1)PA + (1+η)^n · ηA|x|^n
    --              ≤ ((1+η)^n - 1)PA + (1+η)^n · η · PA  [since A|x|^n ≤ PA]
    --              = ((1+η)^{n+1} - 1)PA
    have hstep_xpow : |next_v - (acc_v * x_v + c_v)| * |x_v| ^ n ≤ η * A * |x_v| ^ n := by
      exact mul_le_mul_of_nonneg_right hstep_err hxpow_nn
    set E := η * A * |x_v| ^ n
    have hE_nn : (0 : R) ≤ E := mul_nonneg (mul_nonneg hη hA_nn) hxpow_nn
    have hE_le_PA : E ≤ η * PA := by
      show η * A * |x_v| ^ n ≤ η * PA
      have hkey : η * (A * |x_v| ^ n) ≤ η * PA :=
        mul_le_mul_of_nonneg_left hPA_ge hη
      linarith [mul_assoc η A (|x_v| ^ n)]
    have htotal : |(final.toVal : R) -
        Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v| ≤
        ((1 + η) ^ (n + 1) - 1) * PA := by
      have h1 : |(final.toVal : R) -
          Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v| ≤
          ((1 + η) ^ n - 1) * (PA + E) + E := by
        have hih_exp : |(final.toVal : R) -
            Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v| ≤
            ((1 + η) ^ n - 1) * (PA + E) := by
          calc |(final.toVal : R) - Horner.hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v|
              ≤ ((1 + η) ^ n - 1) * PA_nxt := ih_bound
            _ ≤ ((1 + η) ^ n - 1) * (PA + E) := by
                apply mul_le_mul_of_nonneg_left
                · linarith [hPA_mono]
                · linarith
        linarith [htri, hstep_xpow]
      -- ((1+η)^n - 1)(PA + E) + E = ((1+η)^n - 1)PA + (1+η)^n E
      -- ≤ ((1+η)^n - 1)PA + (1+η)^n · η · PA = ((1+η)^{n+1} - 1)PA
      have h2 : ((1 + η) ^ n - 1) * (PA + E) + E ≤ ((1 + η) ^ (n + 1) - 1) * PA := by
        have hkey := mul_le_mul_of_nonneg_left hE_le_PA hpow_n_nn
        -- (1+η)^n * E ≤ (1+η)^n * η * PA
        have hpow_succ : (1 + η : R) ^ (n + 1) = (1 + η) ^ n * (1 + η) := pow_succ (1 + η) n
        rw [hpow_succ]
        nlinarith [mul_nonneg (by linarith : (0:R) ≤ (1+η)^n - 1) hPA_nn,
                   mul_nonneg hpow_n_nn hE_nn]
      linarith
    -- Unfold hornerPoly cons
    simp only [List.length_cons, List.map_cons, Horner.hornerPoly]
    convert htotal using 2

/-- **FMA Horner error bound** (γ form).

    `|fl(p(x)) - p(x)| ≤ γₙ · p̃(|x|)` — half the error of non-FMA Horner. -/
theorem fma_horner_error_bound_gamma
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : FMATrace x coeffs init final)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (coeffs.length : R) * η < 1) :
    |(final.toVal : R) -
      Horner.hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      gamma_n (R := R) coeffs.length *
        Horner.hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |init.toVal (R := R)| |x.toVal (R := R)| := by
  have h1 := fma_horner_error_bound trace hnr
  have h2 := pow_sub_one_le_gamma (R := R) coeffs.length (by exact hsmall)
  have hpoly_nn := Horner.hornerPoly_nonneg
    (coeffs.map (fun c => |c.toVal (R := R)|)) |init.toVal (R := R)| |x.toVal (R := R)|
    (abs_nonneg _) (abs_nonneg _) (fun c hc => by
      simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; exact abs_nonneg _)
  nlinarith

end HornerFMA
