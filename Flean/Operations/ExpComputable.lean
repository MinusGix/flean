import Flean.Operations.Exp

/-! # Computable `ExpRefExec` Instance

Evaluates `exp(x)` using rational Taylor series with argument reduction:

1. Convert input to `ℚ` via `FiniteFp.toVal`
2. Reduce argument: `exp(x) = exp(x/2^n)^(2^n)` with `|x/2^n| ≤ 1/2`
3. Taylor series for `exp(y)` with `|y| ≤ 1/2` (fast convergence)
4. Recover via repeated squaring in `ℚ`
5. Extract sticky cell `(q, e_base)` for `roundIntSigM`

Soundness proofs (`ExpRefExecSound`) are deferred — the sorry'd instance lets
`fpExp` be evaluated on concrete inputs right away.
-/

section ExpComputable

variable [FloatFormat]

/-! ## Taylor series -/

/-- Number of Taylor terms. `prec + 10` guard terms ensures the truncation
error is negligible compared to sticky cell width for `|y| ≤ 1/2`. -/
private def expNumTerms : ℕ := FloatFormat.prec.toNat + 10

/-- Evaluate `exp(y) ≈ Σ_{k=0}^{numTerms} y^k/k!` in ℚ.
Uses forward recurrence `term_{k+1} = term_k · y / (k+1)`.
All terms are positive when `y > 0`, guaranteeing a lower bound. -/
private def taylorExpQ (y : ℚ) (numTerms : ℕ) : ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ → ℚ
    | 0, _, acc, _ => acc
    | fuel + 1, k, acc, term =>
        let nextTerm := term * y / (k + 1)
        go fuel (k + 1) (acc + nextTerm) nextTerm
  go numTerms 0 1 1  -- start: k=0, acc=1 (term_0), term=1 (term_0)

/-! ## Argument reduction -/

/-- Smallest `n` such that `abs_x / 2^n ≤ 1/2`, i.e., `2 · abs_x ≤ 2^n`.
Returns 0 when `abs_x ≤ 1/2`. -/
private def expArgRedN (abs_x : ℚ) : ℕ :=
  let two_abs_x := 2 * abs_x
  if two_abs_x ≤ 1 then 0
  else
    -- ⌈2·|x|⌉ ≤ 2^n, so n = Nat.log2(⌈2·|x|⌉) + 1 suffices
    -- (Nat.log2 k gives the floor log, so 2^(log2 k + 1) > k)
    let upper := (⌈two_abs_x⌉).toNat  -- ⌈two_abs_x⌉ ≥ 1 here
    Nat.log2 upper + 1

/-! ## Repeated squaring -/

/-- Compute `base^(2^n)` by `n` successive squarings. -/
private def repeatedSquare (base : ℚ) : ℕ → ℚ
  | 0 => base
  | n + 1 => let half := repeatedSquare base n; half * half

/-! ## Sticky cell extraction -/

/-- Extract `(q, e_base)` from a positive rational `result`.

Finds shift `s` such that `q := ⌊result · 2^s⌋` has at least `prec + 2` bits
(guaranteed by `initial_q_ge_minQ`),
then sets `e_base := -(s + 1)` so that `result ≈ 2q · 2^e_base`. -/
private def expExtract (result : ℚ) : ExpRefOut :=
  let p := result.num.natAbs
  let d := result.den
  let targetBits := FloatFormat.prec.toNat + 3
  -- Approximate shift: s ≈ targetBits + log2(d) - log2(p)
  -- Use Int to avoid Nat subtraction underflow
  let s_int : ℤ := (targetBits : ℤ) + (Nat.log2 d : ℤ) - (Nat.log2 p : ℤ)
  let s := s_int.toNat  -- clamp negative to 0
  -- Compute q = ⌊p · 2^s / d⌋ (≥ 2^(prec+2) by initial_q_ge_minQ)
  let q := p * 2 ^ s / d
  let e_base : ℤ := -((s : ℤ)) - 1
  { q := q, e_base := e_base, isExact := false }

/-! ## Main kernel -/

/-- Computable exp reference kernel.

For `a.m = 0` (input is ±0): returns exact result for `exp(0) = 1`.
Otherwise: rational Taylor series with argument reduction. -/
def expComputableRun (a : FiniteFp) : ExpRefOut :=
  if a.m = 0 then
    -- exp(0) = 1 = 2 · 1 · 2^(-1)
    { q := 1, e_base := -1, isExact := true }
  else
    let x : ℚ := a.toVal
    let abs_x : ℚ := |x|
    -- Argument reduction: find n such that abs_x / 2^n ≤ 1/2
    let n := expArgRedN abs_x
    let y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
    -- Taylor approximation of exp(y) for y ∈ (0, 1/2]
    let ty := taylorExpQ y expNumTerms
    -- Repeated squaring: exp(|x|) ≈ ty^(2^n)
    let pos_result := repeatedSquare ty n
    -- Handle sign: exp(-|x|) = 1/exp(|x|)
    let result : ℚ := if x < 0 then 1 / pos_result else pos_result
    -- Extract sticky cell
    expExtract result

instance (priority := 500) : ExpRefExec where
  run := expComputableRun

/-! ## Soundness helpers -/

omit [FloatFormat] in
/-- Taylor series with nonneg input gives result ≥ 1 (since first term is 1 and rest are nonneg). -/
private theorem taylorExpQ_ge_one (y : ℚ) (hy : 0 ≤ y) (n : ℕ) :
    1 ≤ taylorExpQ y n := by
  simp only [taylorExpQ]
  -- The recursive function accumulates nonneg terms starting from acc=1
  suffices ∀ fuel k (acc term : ℚ), 1 ≤ acc → 0 ≤ term →
    1 ≤ taylorExpQ.go y fuel k acc term from
    this n 0 1 1 (le_refl _) (by norm_num)
  intro fuel
  induction fuel with
  | zero => simp [taylorExpQ.go]; intros; assumption
  | succ n ih =>
    intro k acc term hacc hterm
    simp only [taylorExpQ.go]
    have hnext : 0 ≤ term * y / (↑k + 1) :=
      div_nonneg (mul_nonneg hterm hy) (by positivity)
    exact ih _ _ _ (by linarith) hnext

omit [FloatFormat] in
/-- Repeated squaring of a positive value is positive. -/
private theorem repeatedSquare_pos (base : ℚ) (hb : 0 < base) (n : ℕ) :
    0 < repeatedSquare base n := by
  induction n with
  | zero => exact hb
  | succ n ih => exact mul_pos ih ih

/-- The result passed to `expExtract` in the non-zero branch is positive. -/
private theorem expComputableRun_result_pos (a : FiniteFp) (_hm : a.m ≠ 0) :
    let x : ℚ := a.toVal
    let abs_x : ℚ := |x|
    let n := expArgRedN abs_x
    let y : ℚ := abs_x / (2 : ℚ) ^ (n : ℕ)
    let ty := taylorExpQ y expNumTerms
    let pos_result := repeatedSquare ty n
    let result : ℚ := if x < 0 then 1 / pos_result else pos_result
    0 < result := by
  simp only
  have habs : 0 ≤ |a.toVal (R := ℚ)| := abs_nonneg _
  have hy_nonneg : 0 ≤ |a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ) :=
    div_nonneg habs (by positivity)
  have hty_ge : 1 ≤ taylorExpQ (|a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms :=
    taylorExpQ_ge_one _ hy_nonneg _
  have hty_pos : 0 < taylorExpQ (|a.toVal (R := ℚ)| / (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms :=
    lt_of_lt_of_le (by norm_num) hty_ge
  have hpos := repeatedSquare_pos _ hty_pos (expArgRedN |a.toVal (R := ℚ)|)
  split_ifs <;> positivity

/-- `expExtract` always returns `isExact = false`. -/
private theorem expExtract_isExact_false (result : ℚ) :
    (expExtract result).isExact = false := by
  simp [expExtract]

/-- Core arithmetic: with the log2-based shift, `p * 2^s / d ≥ 2^(prec+2)`. -/
private theorem initial_q_ge_minQ (p d : ℕ) (hp : 0 < p) (hd : 0 < d) :
    let s_int : ℤ := ((FloatFormat.prec.toNat + 3 : ℕ) : ℤ) +
      ((Nat.log2 d : ℕ) : ℤ) - ((Nat.log2 p : ℕ) : ℤ)
    2 ^ (FloatFormat.prec.toNat + 2) ≤ p * 2 ^ s_int.toNat / d := by
  simp only
  set prec2 := FloatFormat.prec.toNat + 2
  set lp := Nat.log2 p
  set ld := Nat.log2 d
  set s_int : ℤ := ((prec2 + 1 : ℕ) : ℤ) + (ld : ℤ) - (lp : ℤ)
  set s := s_int.toNat
  have hp_ne : p ≠ 0 := by omega
  have hd_ne : d ≠ 0 := by omega
  have hlp : 2 ^ lp ≤ p := Nat.log2_self_le hp_ne
  have hdlt : d < 2 ^ (ld + 1) := (Nat.log2_lt hd_ne).mp (Nat.lt_succ_of_le (le_refl ld))
  rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
  -- Need: 2^prec2 * d ≤ p * 2^s
  -- Split on whether s_int ≥ 0
  by_cases hs : (0 : ℤ) ≤ s_int
  · -- s = prec2 + 1 + ld - lp (as ℕ, since s_int ≥ 0 means lp ≤ prec2 + 1 + ld)
    have hlp_le : lp ≤ prec2 + 1 + ld := by omega
    have hs_eq : s = prec2 + 1 + ld - lp := by
      omega
    -- p * 2^s ≥ 2^lp * 2^(prec2+1+ld-lp) = 2^(prec2+1+ld)
    have key : 2 ^ (prec2 + 1 + ld) ≤ p * 2 ^ s := by
      calc 2 ^ (prec2 + 1 + ld)
          = 2 ^ (lp + (prec2 + 1 + ld - lp)) := by congr 1; omega
        _ = 2 ^ lp * 2 ^ (prec2 + 1 + ld - lp) := by rw [Nat.pow_add]
        _ ≤ p * 2 ^ s := by rw [hs_eq]; exact Nat.mul_le_mul_right _ hlp
    -- 2^prec2 * d < 2^(prec2+1+ld) ≤ p * 2^s
    exact le_of_lt (calc 2 ^ prec2 * d
        < 2 ^ prec2 * 2 ^ (ld + 1) :=
          Nat.mul_lt_mul_of_pos_left hdlt (by positivity)
      _ = 2 ^ (prec2 + 1 + ld) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ p * 2 ^ s := key)
  · -- s = 0 (s_int < 0)
    push_neg at hs
    have hs_eq : s = 0 := Int.toNat_eq_zero.mpr (le_of_lt hs)
    -- lp ≥ prec2 + 2 + ld (from s_int < 0)
    rw [hs_eq, Nat.pow_zero, Nat.mul_one]
    have step1 : 2 ^ prec2 * d < 2 ^ (prec2 + ld + 1) := by
      calc 2 ^ prec2 * d < 2 ^ prec2 * 2 ^ (ld + 1) :=
            Nat.mul_lt_mul_of_pos_left hdlt (by positivity)
        _ = 2 ^ (prec2 + (ld + 1)) := by rw [← Nat.pow_add]
        _ = 2 ^ (prec2 + ld + 1) := by ring_nf
    have step2 : prec2 + ld + 1 ≤ lp := by omega
    exact le_of_lt (lt_of_lt_of_le step1
      (le_trans (Nat.pow_le_pow_right (by omega) step2) hlp))

/-- `expExtract` produces `q ≥ 2^(prec+2)` for positive rational input. -/
private theorem expExtract_q_ge (result : ℚ) (hpos : 0 < result) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ (expExtract result).q := by
  have hp : 0 < result.num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hpos))
  exact initial_q_ge_minQ result.num.natAbs result.den hp result.den_pos

/-- When `isExact = true`, we must be in the zero branch. -/
private theorem expComputableRun_exact_is_zero (a : FiniteFp)
    (hExact : (expComputableRun a).isExact = true) : a.m = 0 := by
  by_contra h
  have : (expComputableRun a).isExact = false := by
    simp only [expComputableRun, h, ↓reduceIte, expExtract_isExact_false]
  rw [this] at hExact; exact absurd hExact (by decide)

/-- In the zero branch, the output is `{q := 1, e_base := -1, isExact := true}`. -/
private theorem expComputableRun_zero (a : FiniteFp) (hm : a.m = 0) :
    expComputableRun a = { q := 1, e_base := -1, isExact := true } := by
  simp [expComputableRun, hm]

/-! ## Soundness -/

instance (priority := 500) : ExpRefExecSound where
  exact_mag_ne_zero := by
    intro a o hr hExact
    have hrun : ExpRefExec.run a = expComputableRun a := rfl
    rw [hrun] at hr
    have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
    rw [expComputableRun_zero a hm] at hr
    subst hr
    norm_num
  exact_value := by
    intro a o hr hExact
    have hrun : ExpRefExec.run a = expComputableRun a := rfl
    rw [hrun] at hr
    have hm := expComputableRun_exact_is_zero a (hr ▸ hExact)
    rw [expComputableRun_zero a hm] at hr
    subst hr
    simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
    have hval : (a.toVal : ℝ) = 0 :=
      FiniteFp.toVal_isZero (show a.isZero from hm)
    rw [hval, Real.exp_zero]
    norm_num
  sticky_q_lower := by
    intro a o hr hFalse
    have hrun : ExpRefExec.run a = expComputableRun a := rfl
    rw [hrun] at hr
    -- isExact = false means we're in the non-zero branch
    have hm : a.m ≠ 0 := by
      intro h
      rw [expComputableRun_zero a h] at hr
      rw [← hr] at hFalse; exact absurd hFalse (by decide)
    -- In the non-zero branch, output comes from expExtract
    have hnonzero : expComputableRun a = expExtract
        (if a.toVal (R := ℚ) < 0
         then 1 / repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms)
           (expArgRedN |a.toVal (R := ℚ)|)
         else repeatedSquare (taylorExpQ (|a.toVal (R := ℚ)| /
           (2 : ℚ) ^ (expArgRedN |a.toVal (R := ℚ)| : ℕ)) expNumTerms)
           (expArgRedN |a.toVal (R := ℚ)|)) := by
      simp only [expComputableRun, hm, ↓reduceIte]
    rw [hnonzero] at hr; rw [← hr]
    exact expExtract_q_ge _ (expComputableRun_result_pos a hm)
  sticky_interval := by
    intro a o hr hFalse
    sorry

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
