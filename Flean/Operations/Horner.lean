import Flean.Operations.KahanSum
import Flean.Operations.Mul

/-!
# Horner's Method Error Bound

Error analysis for Horner's polynomial evaluation:
```
s₀ = aₙ
sₖ = fl(s_{k-1} * x + a_{n-k})   for k = 1, ..., n
```

## Main Results

- `horner_error_bound`: `|fl(p(x)) - p(x)| ≤ ((1+η)^{2n} - 1) · p̃(|x|)`
- `horner_error_bound_gamma`: `|fl(p(x)) - p(x)| ≤ γ_{2n} · p̃(|x|)`

where `p̃(|x|) = Σ|aᵢ|·|x|^i` is the polynomial evaluated with absolute values (Higham Thm 5.1).
-/

namespace Horner

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Polynomial Evaluation -/

/-- Exact Horner evaluation: `hornerPoly [c₀,...,c_{n-1}] init x` computes
    `init · x^n + c₀ · x^{n-1} + ... + c_{n-1}` via the recurrence
    `acc ← acc * x + c`. -/
def hornerPoly : List R → R → R → R
  | [], acc, _ => acc
  | c :: cs, acc, x => hornerPoly cs (acc * x + c) x

theorem hornerPoly_nonneg (coeffs : List R) (acc x : R)
    (hacc : 0 ≤ acc) (hx : 0 ≤ x)
    (hcoeffs : ∀ c ∈ coeffs, 0 ≤ c) :
    0 ≤ hornerPoly coeffs acc x := by
  induction coeffs generalizing acc with
  | nil => exact hacc
  | cons c cs ih =>
    simp only [hornerPoly]
    apply ih
    · exact add_nonneg (mul_nonneg hacc hx) (hcoeffs c (List.mem_cons.mpr (Or.inl rfl)))
    · intro d hd
      exact hcoeffs d (List.mem_cons.mpr (Or.inr hd))

/-- Horner polynomial is affine in the accumulator:
    `hornerPoly cs (a + e) x = hornerPoly cs a x + e * x^{cs.length}`.

    This is the key structural lemma: shifting the initial accumulator by `e`
    shifts the output by exactly `e * x^n`. -/
private theorem hornerPoly_affine (cs : List R) (a e x : R) :
    hornerPoly cs (a + e) x = hornerPoly cs a x + e * x ^ cs.length := by
  induction cs generalizing a e with
  | nil => simp [hornerPoly]
  | cons c cs ih =>
    simp only [hornerPoly, List.length_cons, pow_succ]
    have heq : (a + e) * x + c = (a * x + c) + (e * x) := by ring
    rw [heq, ih]
    ring

/-- Horner polynomial is monotone in the accumulator when `x ≥ 0`
    and all coefficients are nonneg. -/
private theorem hornerPoly_mono (cs : List R) (a b x : R)
    (hab : a ≤ b) (hx : 0 ≤ x) (hcs : ∀ c ∈ cs, 0 ≤ c) :
    hornerPoly cs a x ≤ hornerPoly cs b x := by
  induction cs generalizing a b with
  | nil => exact hab
  | cons c cs ih =>
    simp only [hornerPoly]
    apply ih
    · have hc : 0 ≤ c := hcs c (List.mem_cons.mpr (Or.inl rfl))
      nlinarith [mul_le_mul_of_nonneg_right hab hx]
    · exact fun d hd => hcs d (List.mem_cons.mpr (Or.inr hd))

/-! ## Step and Trace -/

/-- One step of Horner evaluation: multiply accumulator by x, then add coefficient. -/
structure HornerStep [RModeExec] (acc x coeff : FiniteFp) where
  prod : FiniteFp
  hprod : acc * x = Fp.finite prod
  next : FiniteFp
  hnext : prod + coeff = Fp.finite next

/-- Normal range hypothesis for a Horner step. -/
structure HornerStepNormalRange [RModeExec] (acc x coeff : FiniteFp)
    (step : HornerStep acc x coeff) where
  mul_normal : isNormalRange ((acc.toVal : R) * x.toVal) ∨ (acc.toVal : R) * x.toVal = 0
  add_normal : isNormalRange ((step.prod.toVal : R) + coeff.toVal) ∨
               (step.prod.toVal : R) + coeff.toVal = 0

/-- Trace of Horner evaluation with fixed evaluation point `x`. -/
inductive HornerTrace [RModeExec] (x : FiniteFp) :
    List FiniteFp → FiniteFp → FiniteFp → Type where
  | nil (acc : FiniteFp) : HornerTrace x [] acc acc
  | cons {acc coeff : FiniteFp} {coeffs : List FiniteFp} {final : FiniteFp}
      (step : HornerStep acc x coeff)
      (rest : HornerTrace x coeffs step.next final) :
      HornerTrace x (coeff :: coeffs) acc final

/-- All steps are in normal range. -/
def HornerTrace.AllNormalRange [RModeExec] {x : FiniteFp} :
    {coeffs : List FiniteFp} → {acc final : FiniteFp} →
    HornerTrace x coeffs acc final → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons (acc := acc) (coeff := coeff) step rest =>
      HornerStepNormalRange (R := R) acc x coeff step ∧ rest.AllNormalRange

/-! ## Error Bound -/

set_option maxHeartbeats 800000 in
/-- **Horner error bound** (`(1+η)^{2n}` form).

    For a Horner trace with `n` steps (evaluating a degree-n polynomial):
    `|final - hornerPoly(coeffs, init, x)| ≤ ((1+η)^{2n} - 1) · hornerPoly(|coeffs|, |init|, |x|)`

    The `2n` exponent reflects `n` multiplications and `n` additions. -/
theorem horner_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : HornerTrace x coeffs init final)
    (hnr : trace.AllNormalRange (R := R)) :
    |(final.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      ((1 + η) ^ (2 * coeffs.length) - 1) *
        hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |init.toVal (R := R)| |x.toVal (R := R)| := by
  induction trace with
  | nil acc =>
    simp only [List.map_nil, hornerPoly, List.length_nil, Nat.mul_zero, pow_zero, sub_self,
               zero_mul, abs_zero, le_refl]
  | @cons acc coeff coeffs final step rest ih =>
    simp only [HornerTrace.AllNormalRange] at hnr
    obtain ⟨hnr_step, hnr_rest⟩ := hnr
    -- Extract multiplication and addition error bounds
    have hmul_err := KahanSum.fpMul_error_or_zero (R := R) acc x step.prod step.hprod
                      hnr_step.mul_normal
    have hadd_err := KahanSum.fpAdd_error_or_zero (R := R) step.prod coeff step.next step.hnext
                      hnr_step.add_normal
    -- Abbreviations
    set n := coeffs.length with hn_def
    set acc_v  := (acc.toVal : R) with hacc_def
    set x_v    := (x.toVal : R) with hx_def
    set c_v    := (coeff.toVal : R) with hc_def
    set prod_v := (step.prod.toVal : R) with hprod_def
    set next_v := (step.next.toVal : R) with hnext_def
    -- η ≥ 0 and basic power facts
    have hη : (0 : R) ≤ η := by positivity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    -- Abbreviation for the "absolute" accumulator at this step
    set A := |acc_v| * |x_v| + |c_v| with hA_def
    -- IH applied to rest (starting at step.next)
    have ih_bound := ih hnr_rest
    -- Multiplication error: |prod_v - acc_v * x_v| ≤ η * |acc_v * x_v|
    have hmul : |prod_v - acc_v * x_v| ≤ η * |acc_v * x_v| := hmul_err
    -- Addition error: |next_v - (prod_v + c_v)| ≤ η * |prod_v + c_v|
    have hadd : |next_v - (prod_v + c_v)| ≤ η * |prod_v + c_v| := hadd_err
    -- |acc_v * x_v| = |acc_v| * |x_v|
    have habs_mul : |acc_v * x_v| = |acc_v| * |x_v| := abs_mul acc_v x_v
    -- prod bound: |prod_v| ≤ (1+η)|acc_v||x_v|
    have hprod_bound : |prod_v| ≤ (1 + η) * (|acc_v| * |x_v|) := by
      have h1 : |prod_v| - |acc_v * x_v| ≤ η * |acc_v * x_v| :=
        le_trans (abs_sub_abs_le_abs_sub prod_v (acc_v * x_v)) hmul
      linarith [habs_mul.symm ▸ h1]
    -- |prod_v + c_v| ≤ (1+η)*|acc_v|*|x_v| + |c_v|
    have hprod_c_bound : |prod_v + c_v| ≤ (1 + η) * (|acc_v| * |x_v|) + |c_v| := by
      calc |prod_v + c_v| ≤ |prod_v| + |c_v| := abs_add_le _ _
        _ ≤ (1 + η) * (|acc_v| * |x_v|) + |c_v| := by linarith [abs_nonneg c_v]
    -- Combined per-step error: |next_v - (acc_v * x_v + c_v)| ≤ ((1+η)^2 - 1) * A
    have hstep_err : |next_v - (acc_v * x_v + c_v)| ≤ ((1 + η) ^ 2 - 1) * A := by
      have htri : next_v - (acc_v * x_v + c_v) =
          (next_v - (prod_v + c_v)) + (prod_v - acc_v * x_v) := by ring
      have htri_abs : |next_v - (acc_v * x_v + c_v)| ≤
          |next_v - (prod_v + c_v)| + |prod_v - acc_v * x_v| := htri ▸ abs_add_le _ _
      have hstep1 : |next_v - (prod_v + c_v)| ≤ η * ((1 + η) * (|acc_v| * |x_v|) + |c_v|) := by
        calc |next_v - (prod_v + c_v)| ≤ η * |prod_v + c_v| := hadd
          _ ≤ η * ((1 + η) * (|acc_v| * |x_v|) + |c_v|) :=
              mul_le_mul_of_nonneg_left hprod_c_bound hη
      have hstep2 : |prod_v - acc_v * x_v| ≤ η * (|acc_v| * |x_v|) := habs_mul ▸ hmul
      have h2sq : ((1 + η) : R) ^ 2 - 1 = 2 * η + η ^ 2 := by ring
      rw [h2sq, hA_def]
      nlinarith [abs_nonneg c_v, abs_nonneg acc_v, abs_nonneg x_v,
                 mul_nonneg hη (abs_nonneg acc_v), mul_nonneg hη (abs_nonneg x_v),
                 mul_nonneg (abs_nonneg acc_v) (abs_nonneg x_v)]
    -- |next_v| ≤ (1+η)^2 * A
    have hnext_bound : |next_v| ≤ (1 + η) ^ 2 * A := by
      have hA_nn : (0 : R) ≤ A := by positivity
      have h2sq1 : ((1 + η) : R) ^ 2 - 1 ≥ 0 := by nlinarith
      -- |next_v| ≤ |acc_v * x_v + c_v| + |next_v - (acc_v * x_v + c_v)|
      have hrev : |next_v| ≤ |acc_v * x_v + c_v| + |next_v - (acc_v * x_v + c_v)| := by
        have := abs_sub_abs_le_abs_sub next_v (acc_v * x_v + c_v)
        have htri2 := abs_sub_le next_v (acc_v * x_v + c_v)
        linarith [abs_nonneg (next_v - (acc_v * x_v + c_v))]
      have habs_exact : |acc_v * x_v + c_v| ≤ A := by
        calc |acc_v * x_v + c_v| ≤ |acc_v * x_v| + |c_v| := abs_add_le _ _
          _ = |acc_v| * |x_v| + |c_v| := by rw [habs_mul]
          _ = A := rfl
      have h2sq_expand : ((1 + η : R) ^ 2 - 1) * A = (2 * η + η ^ 2) * A := by ring
      linarith [hstep_err, mul_nonneg h2sq1 hA_nn]
    -- Powers
    have hpow_2n : (1 : R) ≤ (1 + η) ^ (2 * n) := one_le_pow₀ h1η
    have hpow_2n_nn : (0 : R) ≤ (1 + η) ^ (2 * n) := le_trans zero_le_one hpow_2n
    have hpow_2_ge1 : (1 : R) ≤ (1 + η) ^ 2 := one_le_pow₀ h1η
    have hpow_2_sub : (0 : R) ≤ (1 + η) ^ 2 - 1 := by linarith
    have hA_nn : (0 : R) ≤ A := by positivity
    have hxabs_nn : (0 : R) ≤ |x_v| := abs_nonneg _
    have hxpow_nn : (0 : R) ≤ |x_v| ^ n := by positivity
    -- The absolute polynomial at this step level
    set PA_cs_A  := hornerPoly (coeffs.map (fun c => |(c.toVal : R)|)) A |x_v| with hPA_A_def
    set PA_cs_nxt := hornerPoly (coeffs.map (fun c => |(c.toVal : R)|)) |next_v| |x_v| with hPA_nxt_def
    -- Shared: List.length_map for coeffs
    have hlen : (coeffs.map (fun c => |(c.toVal : R)|)).length = n := by simp [hn_def]
    -- PA(cs, |next_v|, |x_v|) ≤ PA(cs, A, |x_v|) + ((1+η)^2 - 1)*A*|x_v|^n
    -- via hornerPoly_affine with |next_v| = A + (|next_v| - A)
    have hPA_mono_bound : PA_cs_nxt ≤ PA_cs_A + ((1 + η) ^ 2 - 1) * A * |x_v| ^ n := by
      have haffine_abs : PA_cs_nxt =
          PA_cs_A + (|next_v| - A) * |x_v| ^ n := by
        rw [hPA_nxt_def, hPA_A_def]
        have hdecomp : |next_v| = A + (|next_v| - A) := by ring
        conv_lhs => rw [hdecomp]
        rw [hornerPoly_affine, hlen]
      rw [haffine_abs]
      have hle : |next_v| - A ≤ ((1 + η) ^ 2 - 1) * A := by linarith
      have hprod_nn := mul_nonneg hA_nn hxpow_nn
      have hstep : (|next_v| - A) * |x_v| ^ n ≤ ((1 + η) ^ 2 - 1) * A * |x_v| ^ n :=
        mul_le_mul_of_nonneg_right hle hxpow_nn
      linarith
    -- PA_cs_A ≥ A * |x_v|^n (the accumulator part dominates)
    have hPA_ge_axpow : A * |x_v| ^ n ≤ PA_cs_A := by
      rw [hPA_A_def]
      have haffine0 : hornerPoly (coeffs.map (fun c => |(c.toVal : R)|)) A |x_v| =
          hornerPoly (coeffs.map (fun c => |(c.toVal : R)|)) 0 |x_v| + A * |x_v| ^ n := by
        conv_lhs => rw [show A = 0 + A from (zero_add A).symm]
        rw [hornerPoly_affine, hlen]
      rw [haffine0]
      have hzero_nn : 0 ≤ hornerPoly (coeffs.map (fun c => |(c.toVal : R)|)) 0 |x_v| :=
        hornerPoly_nonneg _ 0 |x_v| le_rfl (abs_nonneg _) (fun c hc => by
          simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; exact abs_nonneg _)
      linarith
    have hPA_A_nn : (0 : R) ≤ PA_cs_A := le_trans (mul_nonneg hA_nn hxpow_nn) hPA_ge_axpow
    -- Triangle inequality: split the error at (acc_v*x_v + c_v) vs next_v level
    have htri_full : |(final.toVal : R) -
        hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v| ≤
        |(final.toVal : R) - hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v| +
        |next_v - (acc_v * x_v + c_v)| * |x_v| ^ n := by
      -- Use hornerPoly_affine to express the difference
      have hlen2 : (coeffs.map (fun c => (c.toVal : R))).length = n := by simp [hn_def]
      have haffine : hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v =
          hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v +
          (next_v - (acc_v * x_v + c_v)) * x_v ^ n := by
        conv_lhs => rw [show next_v = (acc_v * x_v + c_v) + (next_v - (acc_v * x_v + c_v)) from
                        by ring]
        rw [hornerPoly_affine, hlen2]
      have heq : (final.toVal : R) -
          hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v =
          ((final.toVal : R) - hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v) +
          (next_v - (acc_v * x_v + c_v)) * x_v ^ n := by
        linarith
      rw [heq]
      have := abs_add_le
        ((final.toVal : R) - hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v)
        ((next_v - (acc_v * x_v + c_v)) * x_v ^ n)
      rwa [abs_mul, abs_pow] at this
    -- IH gives: |final - hornerPoly(cs, next_v, x_v)| ≤ ((1+η)^{2n} - 1) * PA_cs_nxt
    -- Combined with PA_cs_nxt ≤ PA_cs_A + E (where E = ((1+η)^2-1)*A*|x_v|^n):
    have hih_expanded : |(final.toVal : R) -
        hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v| ≤
        ((1 + η) ^ (2 * n) - 1) * (PA_cs_A + ((1 + η) ^ 2 - 1) * A * |x_v| ^ n) := by
      calc |(final.toVal : R) - hornerPoly (coeffs.map (fun c => (c.toVal : R))) next_v x_v|
          ≤ ((1 + η) ^ (2 * n) - 1) * PA_cs_nxt := ih_bound
        _ ≤ ((1 + η) ^ (2 * n) - 1) * (PA_cs_A + ((1 + η) ^ 2 - 1) * A * |x_v| ^ n) :=
            mul_le_mul_of_nonneg_left hPA_mono_bound (by linarith)
    -- Algebra: ((1+η)^{2(n+1)} - 1) = (1+η)^{2n}*(1+η)^2 - 1
    have hpow_split : (1 + η : R) ^ (2 * (n + 1)) = (1 + η) ^ (2 * n) * (1 + η) ^ 2 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
    -- Main algebraic identity:
    -- Total ≤ ((1+η)^{2n}-1)*(PA + E) + E
    --       = ((1+η)^{2n}-1)*PA + (1+η)^{2n}*E
    -- Target = ((1+η)^{2n+2}-1)*PA
    -- So we need: (1+η)^{2n}*E ≤ ((1+η)^{2n+2} - (1+η)^{2n})*PA
    --            = (1+η)^{2n}*((1+η)^2-1)*PA
    -- i.e. E = ((1+η)^2-1)*A*|x_v|^n ≤ ((1+η)^2-1)*PA_cs_A
    -- i.e. A*|x_v|^n ≤ PA_cs_A  -- proved above!
    -- Shorthand for the per-step error contribution
    set E := ((1 + η : R) ^ 2 - 1) * A * |x_v| ^ n with hE_def
    have hE_nn : (0 : R) ≤ E := mul_nonneg (mul_nonneg hpow_2_sub hA_nn) hxpow_nn
    have hE_le_PA : E ≤ ((1 + η) ^ 2 - 1) * PA_cs_A := by
      show ((1 + η : R) ^ 2 - 1) * A * |x_v| ^ n ≤ ((1 + η) ^ 2 - 1) * PA_cs_A
      have hkey : ((1 + η : R) ^ 2 - 1) * (A * |x_v| ^ n) ≤ ((1 + η) ^ 2 - 1) * PA_cs_A :=
        mul_le_mul_of_nonneg_left hPA_ge_axpow hpow_2_sub
      nlinarith [mul_nonneg hpow_2_sub (mul_nonneg hA_nn hxpow_nn)]
    -- The per-step error satisfies: |next - exact| * |x|^n ≤ E
    have hstep_xpow : |next_v - (acc_v * x_v + c_v)| * |x_v| ^ n ≤ E := by
      show |next_v - (acc_v * x_v + c_v)| * |x_v| ^ n ≤ ((1 + η) ^ 2 - 1) * A * |x_v| ^ n
      have := mul_le_mul_of_nonneg_right hstep_err hxpow_nn
      linarith
    have htotal : |(final.toVal : R) -
        hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v| ≤
        ((1 + η) ^ (2 * (n + 1)) - 1) * PA_cs_A := by
      rw [hpow_split]
      -- Goal: |...| ≤ ((1+η)^{2n} * (1+η)^2 - 1) * PA_cs_A
      -- Step 1: total ≤ ((1+η)^{2n}-1)*(PA+E) + E
      have h1 : |(final.toVal : R) -
          hornerPoly (coeffs.map (fun c => (c.toVal : R))) (acc_v * x_v + c_v) x_v| ≤
          ((1 + η) ^ (2 * n) - 1) * (PA_cs_A + E) + E := by
        linarith [htri_full, hih_expanded, hstep_xpow]
      -- Step 2: algebra to bound by target
      -- ((1+η)^{2n}-1)*(PA+E) + E
      -- = ((1+η)^{2n}-1)*PA + ((1+η)^{2n}-1)*E + E
      -- = ((1+η)^{2n}-1)*PA + (1+η)^{2n}*E
      -- ≤ ((1+η)^{2n}-1)*PA + (1+η)^{2n}*((1+η)^2-1)*PA  [since E ≤ ((1+η)^2-1)*PA]
      -- = ((1+η)^{2n}*(1+η)^2 - 1)*PA
      have h2 : ((1 + η : R) ^ (2 * n) - 1) * (PA_cs_A + E) + E ≤
          ((1 + η) ^ (2 * n) * (1 + η) ^ 2 - 1) * PA_cs_A := by
        have hkey := mul_le_mul_of_nonneg_left hE_le_PA hpow_2n_nn
        -- hkey : (1+η)^{2n} * E ≤ (1+η)^{2n} * ((1+η)^2-1) * PA_cs_A
        nlinarith [mul_nonneg (by linarith : (0:R) ≤ (1+η)^(2*n) - 1) hPA_A_nn,
                   mul_nonneg hpow_2n_nn hE_nn,
                   mul_nonneg hpow_2n_nn hpow_2_sub]
      linarith
    -- Unfold hornerPoly and list operations to match the goal
    simp only [List.length_cons, List.map_cons, hornerPoly]
    -- Goal after simp: |final - hornerPoly(rest_map, acc_v * x_v + c_v, x_v)|
    --     ≤ ((1+η)^{2*(n+1)} - 1) * hornerPoly(|rest|_map, |acc_v|*|x_v| + |c_v|, |x_v|)
    -- htotal: same with PA_cs_A = hornerPoly(|rest|_map, A, |x_v|) and A = |acc_v|*|x_v|+|c_v|
    -- The goal should match htotal exactly since c_v := coeff.toVal and n = coeffs.length
    convert htotal using 2

/-- **Horner error bound** (γ form, Higham Theorem 5.1).

    `|fl(p(x)) - p(x)| ≤ γ_{2n} · p̃(|x|)` -/
theorem horner_error_bound_gamma
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {x init final : FiniteFp} {coeffs : List FiniteFp}
    (trace : HornerTrace x coeffs init final)
    (hnr : trace.AllNormalRange (R := R))
    (hsmall : (2 * coeffs.length : R) * η < 1) :
    |(final.toVal : R) -
      hornerPoly (coeffs.map (fun c => c.toVal (R := R))) (init.toVal) (x.toVal)| ≤
      gamma_n (R := R) (2 * coeffs.length) *
        hornerPoly (coeffs.map (fun c => |c.toVal (R := R)|))
          |init.toVal (R := R)| |x.toVal (R := R)| := by
  have h1 := horner_error_bound trace hnr
  have h2 := pow_sub_one_le_gamma (R := R) (2 * coeffs.length) (by push_cast; exact hsmall)
  have hpoly_nn := hornerPoly_nonneg
    (coeffs.map (fun c => |c.toVal (R := R)|)) |init.toVal (R := R)| |x.toVal (R := R)|
    (abs_nonneg _) (abs_nonneg _) (fun c hc => by
      simp only [List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; exact abs_nonneg _)
  nlinarith

end Horner
