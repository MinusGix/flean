import Flean.Operations.RoundIntSig
import Flean.Rounding.OddInterval

/-! # Floating-Point Division

Softfloat-style floating-point division using `roundIntSig` as the rounding primitive.

## Algorithm

Division cannot directly use `roundIntSig` because `a.m / b.m` is not necessarily an integer.
The standard softfloat approach:

1. Scale the dividend: `scaled = a.m * 2^shift` (with `shift = 2 * prec.toNat + 2`)
2. Euclidean division: `q = scaled / b.m`, `r = scaled % b.m`
3. Sticky bit: if `r ≠ 0`, set `mag = 2*q + 1`; otherwise `mag = 2*q`
4. Feed `mag` and adjusted exponent into `roundIntSig`

The "sticky bit" trick: when the division has a nonzero remainder, `2*q + 1` (an odd number)
ensures that `roundIntSig`'s internal shifting produces a nonzero remainder, correctly signaling
that the exact quotient is not on a grid point. This preserves correct rounding for all modes.

## Exact quotient formula

`a.toVal / b.toVal = ±(q + r/b.m) * 2^(a.e - b.e - shift)`

When `r = 0`: `intSigVal sign (2*q) e_base = a.toVal / b.toVal` exactly.
When `r ≠ 0`: `intSigVal sign (2*q+1) e_base ≈ a.toVal / b.toVal` (the sticky bit
  preserves correct rounding).
-/

section Div

variable [FloatFormat]

/-- The scaling factor for division: we left-shift the dividend by this many bits
to ensure the quotient has enough precision for correct rounding. -/
abbrev divShift : ℕ := 2 * FloatFormat.prec.toNat + 2

/-- Divide two finite floating-point numbers with the given rounding mode.

Requires `b.m ≠ 0` for correct results; when `b.m = 0`, the definition produces
a meaningless value (handled by `fpDiv` at the `Fp` level). -/
def fpDivFinite (mode : RoundingMode) (a b : FiniteFp) : Fp :=
  let sign := a.s ^^ b.s
  let scaled := a.m * 2 ^ divShift
  let q := scaled / b.m
  let r := scaled % b.m
  -- Sticky bit: if remainder is nonzero, force the LSB to preserve rounding info
  let mag := 2 * q + (if r = 0 then 0 else 1)
  let e_base := a.e - b.e - (2 * FloatFormat.prec + 2) - 1
  roundIntSig mode sign mag e_base

/-- IEEE 754 floating-point division with full special-case handling.

Special cases:
- Any NaN operand produces NaN
- ∞ / ∞ = NaN
- ∞ / finite = ∞ (sign = XOR)
- finite / ∞ = ±0 (sign = XOR)
- nonzero / 0 = ∞ (sign = XOR)
- 0 / 0 = NaN
- finite / finite delegates to `fpDivFinite` -/
def fpDiv (mode : RoundingMode) (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | .infinite _, .infinite _ => .NaN
  | .infinite sx, .finite f => .infinite (sx ^^ f.s)
  | .finite f, .infinite sy =>
    Fp.finite ⟨f.s ^^ sy, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  | .finite a, .finite b =>
    if b.m = 0 then
      if a.m = 0 then .NaN
      else .infinite (a.s ^^ b.s)
    else fpDivFinite mode a b

/-! ## Exact Quotient Representation -/

/-- The exact quotient of two finite floats in terms of the scaled Euclidean division.

`a.toVal / b.toVal = ±(q + r/b.m) * 2^(a.e - b.e - shift)`

where `q = (a.m * 2^shift) / b.m` and `r = (a.m * 2^shift) % b.m`. -/
theorem fpDivFinite_exact_quotient {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : FiniteFp) (hb : b.m ≠ 0) :
    let q := (a.m * 2 ^ divShift) / b.m
    let r := (a.m * 2 ^ divShift) % b.m
    (a.toVal : R) / b.toVal =
    (if (a.s ^^ b.s) = true then -1 else (1 : R)) *
      ((q : R) + (r : R) / (b.m : R)) * (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2)) := by
  intro q r
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  have hb_pos : (0 : R) < (b.m : R) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
  have hb_ne : (b.m : R) ≠ 0 := ne_of_gt hb_pos
  -- Euclidean division: a.m * 2^shift = b.m * q + r
  have hdiv_eq : a.m * 2 ^ divShift = b.m * q + r := (Nat.div_add_mod _ _).symm
  -- Cast to R: b.m * q + r = a.m * 2^divShift
  have hcast : (b.m : R) * (q : R) + (r : R) = (a.m : R) * (2 : R) ^ (divShift : ℕ) := by
    have hnat : (b.m * q + r : ℕ) = a.m * 2 ^ divShift := hdiv_eq.symm
    have := congr_arg (Nat.cast (R := R)) hnat
    push_cast [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at this
    linarith
  -- Exponent identity: 2^(a.e-p+1) = 2^(b.e-p+1) * 2^divShift * 2^(a.e-b.e-(2p+2))
  have hexp : (2 : R) ^ (a.e - FloatFormat.prec + 1) =
      (2 : R) ^ (b.e - FloatFormat.prec + 1) * (2 : R) ^ (divShift : ℕ) *
      (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2)) := by
    have hds : (divShift : ℤ) = 2 * FloatFormat.prec + 2 := by
      unfold divShift
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, FloatFormat.prec_toNat_eq]
    rw [← zpow_natCast (2 : R) divShift]
    conv_rhs => rw [← zpow_add₀ (by norm_num : (2:R) ≠ 0) (b.e - FloatFormat.prec + 1),
                     ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]
    exact congrArg ((2 : R) ^ ·) (by omega)
  -- All sign cases: field_simp clears divisions, then algebraic identity
  cases a.s <;> cases b.s <;> simp <;> field_simp <;>
    (try rw [← neg_add_rev]) <;> rw [hcast, hexp] <;> ring

/-! ## Correctness for Exact Division -/

/-- When the division is exact (no remainder), `fpDivFinite` correctly rounds the quotient.

This is a special case of the full correctness theorem, covering cases like
division by powers of 2 where `b.m` divides `a.m * 2^shift`. -/
theorem fpDivFinite_correct_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp)
    (hb : b.m ≠ 0)
    (hquot : (a.toVal : R) / b.toVal ≠ 0)
    (hexact : (a.m * 2 ^ divShift) % b.m = 0) :
    fpDivFinite mode a b = mode.round ((a.toVal : R) / b.toVal) := by
  -- When remainder = 0, mag = 2*q and intSigVal equals exact quotient
  set q := (a.m * 2 ^ divShift) / b.m with hq_def
  -- mag = 2 * q (since r = 0)
  have hmag_eq : 2 * q + (if (a.m * 2 ^ divShift) % b.m = 0 then 0 else 1) = 2 * q := by
    simp [hexact]
  -- The quotient is nonzero
  have hq_ne : q ≠ 0 := by
    intro hzero
    apply hquot
    have hexact_form := fpDivFinite_exact_quotient (R := R) a b hb
    have hq_zero : (a.m * 2 ^ divShift) / b.m = 0 := by rw [← hq_def]; exact hzero
    simp only [hexact, hq_zero, Nat.cast_zero, zero_div, add_zero, mul_zero, zero_mul] at hexact_form
    exact hexact_form
  have hmag_ne : 2 * q ≠ 0 := by omega
  -- intSigVal equals exact quotient when r = 0
  have hbridge : intSigVal (R := R) (a.s ^^ b.s) (2 * q)
      (a.e - b.e - (2 * FloatFormat.prec + 2) - 1) = (a.toVal : R) / b.toVal := by
    have hexact_form := fpDivFinite_exact_quotient (R := R) a b hb
    have hq_fold : (a.m * 2 ^ divShift) / b.m = q := hq_def.symm
    simp only [hexact, hq_fold, Nat.cast_zero, zero_div, add_zero] at hexact_form
    rw [hexact_form]
    unfold intSigVal
    -- (2*q) * 2^(e - 1) = q * 2^e
    have h2q : (↑(2 * q) : R) = 2 * (q : R) := by push_cast; ring
    have hexp : (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2) - 1) =
        (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2)) / 2 := by
      rw [zpow_sub₀ (by norm_num : (2:R) ≠ 0), zpow_one]
    split_ifs <;> rw [h2q, hexp] <;> ring
  -- Unfold and apply roundIntSig_correct
  show roundIntSig mode (a.s ^^ b.s)
    (2 * q + (if (a.m * 2 ^ divShift) % b.m = 0 then 0 else 1))
    (a.e - b.e - (2 * FloatFormat.prec + 2) - 1) = _
  rw [hmag_eq, roundIntSig_correct (R := R) mode _ _ _ hmag_ne, hbridge]

/-! ## Sticky Bit Correctness -/

/-- No positive representable float has toVal in the open interval
    `((n-1) * 2^e_base, (n+1) * 2^e_base)` when `n` is odd and `n > 2^prec`.

    This is the key parity lemma: representable values `m * 2^d` satisfy
    - d ≥ 1: `m * 2^d` is even, `n` is odd → parity mismatch
    - d = 0: `m < 2^prec < n` → too small
    - d ≤ -1: `m * 2^d < 2^(prec-1) < n - 1` → below the interval -/
theorem no_representable_in_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ FloatFormat.prec.toNat < n)
    (f : FiniteFp) (hfs : f.s = false) (hfm : 0 < f.m) :
    ¬(((n : ℤ) - 1 : R) * (2 : R) ^ e_base < (f.toVal : R) ∧
      (f.toVal : R) < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base) := by
  intro ⟨hlo, hhi⟩
  -- Unfold toVal for positive float: f.toVal = f.m * 2^(f.e - prec + 1)
  have htoVal : (f.toVal : R) = ↑f.m * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hfs]; simp
  rw [htoVal] at hlo hhi
  -- Factor: f.e - prec + 1 = e_base + d
  set d := f.e - FloatFormat.prec + 1 - e_base with hd_def
  have hexp_eq : f.e - FloatFormat.prec + 1 = e_base + d := by omega
  rw [hexp_eq, zpow_add₀ (by norm_num : (2:R) ≠ 0)] at hlo hhi
  -- Divide by 2^e_base (positive) to reduce to: f.m * 2^d ∈ (n-1, n+1)
  have hE : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0:R) < 2) _
  -- Factor out 2^e_base from both inequalities
  rw [show ↑f.m * ((2:R)^e_base * (2:R)^d) = ↑f.m * (2:R)^d * (2:R)^e_base from by ring] at hlo hhi
  have hlo' : ((n : ℤ) - 1 : R) < ↑f.m * (2 : R) ^ d := by
    by_contra h; push_neg at h; linarith [mul_le_mul_of_nonneg_right h (le_of_lt hE)]
  have hhi' : (↑f.m : R) * (2 : R) ^ d < ((n : ℤ) + 1 : R) := by
    by_contra h; push_neg at h; linarith [mul_le_mul_of_nonneg_right h (le_of_lt hE)]
  -- Key bound
  have hm_bound : f.m < 2 ^ FloatFormat.prec.toNat := f.valid.2.2.1
  rcases le_or_gt d 0 with hd_le | hd_pos
  · -- d ≤ 0: f.m * 2^d ≤ f.m ≤ n - 1, contradicting hlo'
    have h1 : (↑f.m : R) * (2 : R) ^ d ≤ ↑f.m := by
      calc (↑f.m : R) * (2:R)^d ≤ ↑f.m * 1 := by
            gcongr; exact zpow_le_one_of_nonpos₀ (by norm_num : (1:R) ≤ 2) hd_le
        _ = ↑f.m := mul_one _
    have h2 : (↑f.m : R) ≤ (n : ℤ) - 1 := by
      have : f.m ≤ n - 1 := by omega
      exact_mod_cast show (f.m : ℤ) ≤ (n : ℤ) - 1 from by omega
    linarith
  · -- d ≥ 1: f.m * 2^d is even, n is odd → parity contradiction
    have hd_nat_pos : 0 < d.toNat := by omega
    -- Rewrite as natural number: f.m * 2^d = ↑(f.m * 2^d.toNat)
    have hfm_2d : (↑f.m : R) * (2 : R) ^ d = ↑(f.m * 2 ^ d.toNat) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast (2 : R) d.toNat,
          Int.toNat_of_nonneg (by omega : 0 ≤ d)]
    rw [hfm_2d] at hlo' hhi'
    -- f.m * 2^d.toNat is even (since d.toNat ≥ 1)
    have heven : 2 ∣ f.m * 2 ^ d.toNat := by
      exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) _
    -- f.m * 2^d ≠ n (even ≠ odd)
    have hne : f.m * 2 ^ d.toNat ≠ n := by
      intro heq
      have : 2 ∣ n := heq ▸ heven
      obtain ⟨k, hk⟩ := this; omega
    -- Pull back to integer arithmetic
    have hlo_int : (n : ℤ) - 1 < ↑(f.m * 2 ^ d.toNat) := by exact_mod_cast hlo'
    have hhi_int : (↑(f.m * 2 ^ d.toNat) : ℤ) < ↑n + 1 := by exact_mod_cast hhi'
    -- The only integer in (n-1, n+1) is n
    exact hne (by omega)

/-- A power of 2 is representable as a FiniteFp when the exponent is in range. -/
private theorem exists_representable_pow2 {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (e : ℤ) (he_min : FloatFormat.min_exp ≤ e) (he_max : e ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, f.s = false ∧ 0 < f.m ∧
      (f.toVal : R) = (2 : R) ^ e := by
  set p := FloatFormat.prec.toNat with hp_def
  have hp_ge : 2 ≤ p := by have := FloatFormat.valid_prec; omega
  -- Construct: m = 2^(p-1), exponent = e
  -- toVal = sign' * m * 2^(e - prec + 1) = 1 * 2^(p-1) * 2^(e - prec + 1) = 2^(e + p - 1 - prec + 1) = 2^e
  -- since p = prec.toNat and prec ≥ 2
  refine ⟨⟨false, e, 2 ^ (p - 1), ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩
  · exact he_min
  · exact he_max
  · exact Nat.pow_lt_pow_right (by omega) (by omega)
  · left; constructor
    · rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub, hp_def]
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
  · exact Nat.pos_of_ne_zero (by positivity)
  · unfold FiniteFp.toVal FiniteFp.sign'; simp [FloatFormat.radix_val_eq_two]
    push_cast
    rw [← zpow_natCast (2 : R) (p - 1), ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]
    congr 1
    have : (FloatFormat.prec - 1).toNat = p - 1 := by
      rw [hp_def]; exact FloatFormat.prec_sub_one_toNat_eq_toNat_sub
    omega

/-- The midpoint of two representable floats bounding an odd interval lies outside
    the interval `((n-1)*E, (n+1)*E)`. -/
private theorem midpoint_outside_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (pred_fp succ_fp : FiniteFp)
    (hps : pred_fp.s = false) (hpm : 0 < pred_fp.m)
    (hss : succ_fp.s = false) (hsm : 0 < succ_fp.m)
    (hpred_le : (pred_fp.toVal : R) ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base)
    (hsucc_ge : ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ (succ_fp.toVal : R))
    (hgap : ∀ g : FiniteFp, g.s = false → 0 < g.m →
      (pred_fp.toVal : R) < (g.toVal : R) → (g.toVal : R) < (succ_fp.toVal : R) → False) :
    ((pred_fp.toVal : R) + succ_fp.toVal) / 2 ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base ∨
    ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by
  set E := (2 : R) ^ e_base with hE_def
  set p := FloatFormat.prec.toNat with hp_def
  have hE_pos : (0 : R) < E := zpow_pos (by norm_num : (0:R) < 2) _
  have hE_ne : E ≠ (0 : R) := ne_of_gt hE_pos
  -- Express toVals
  have hpred_toVal : (pred_fp.toVal : R) = ↑pred_fp.m * (2 : R) ^ (pred_fp.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hps]; simp
  have hsucc_toVal : (succ_fp.toVal : R) = ↑succ_fp.m * (2 : R) ^ (succ_fp.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hss]; simp
  -- d_s ≥ 0: succ.toVal ≥ (n+1)*E > 2^(p+3)*E, so e_s - p + 1 > e_base
  set d_s := succ_fp.e - FloatFormat.prec + 1 - e_base with hd_s_def
  have hd_s_nonneg : 0 ≤ d_s := by
    by_contra hd_neg; push_neg at hd_neg
    have hm_s : succ_fp.m < 2 ^ p := succ_fp.valid.2.2.1
    have hexp_lt : succ_fp.e - FloatFormat.prec + 1 < e_base := by omega
    -- succ.toVal < m_s * E (since 2^(e_s-p+1) < 2^e_base = E)
    have h_succ_lt : (succ_fp.toVal : R) < ↑succ_fp.m * E := by
      rw [hsucc_toVal, hE_def]
      have hsm_R : (0 : R) < ↑succ_fp.m := by exact_mod_cast hsm
      have hzpow : (2 : R) ^ (succ_fp.e - FloatFormat.prec + 1) < (2:R) ^ e_base :=
        zpow_lt_zpow_right₀ (by norm_num : (1:R) < 2) hexp_lt
      exact mul_lt_mul_of_pos_left hzpow hsm_R
    -- m_s < 2^p, so succ < 2^p * E
    have h_ms_cast : (↑succ_fp.m : R) < (2 : R) ^ (p : ℤ) := by
      rw [zpow_natCast]; exact_mod_cast hm_s
    have h_succ_lt2 : (succ_fp.toVal : R) < (2 : R) ^ (p : ℤ) * E := by
      calc (succ_fp.toVal : R) < ↑succ_fp.m * E := h_succ_lt
        _ < (2:R) ^ (p : ℤ) * E := by exact mul_lt_mul_of_pos_right h_ms_cast hE_pos
    -- But (n+1)*E ≤ succ and 2^p ≤ n+1
    have hp_le_n : 2 ^ p ≤ n := by
      have : 2 ^ p ≤ 2 ^ (p + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hn_cast : (2 : R) ^ (p : ℤ) ≤ ((n : ℤ) + 1 : R) := by
      rw [zpow_natCast]; push_cast; exact_mod_cast Nat.le_succ_of_le hp_le_n
    linarith [mul_le_mul_of_nonneg_right hn_cast (le_of_lt hE_pos)]
  -- d_p ≥ 0: if d_p < 0, pred < 2^p * E but succ > 2^(p+3) * E, so there's a
  -- representable power of 2 between them, contradicting hgap.
  set d_p := pred_fp.e - FloatFormat.prec + 1 - e_base with hd_p_def
  have hd_p_nonneg : 0 ≤ d_p := by
    by_contra hd_neg; push_neg at hd_neg
    have hm_p : pred_fp.m < 2 ^ p := pred_fp.valid.2.2.1
    have hexp_lt_p : pred_fp.e - FloatFormat.prec + 1 < e_base := by omega
    -- pred < 2^p * E
    have hpred_lt : (pred_fp.toVal : R) < (2 : R) ^ (p : ℤ) * E := by
      rw [hpred_toVal, hE_def]
      have hpm_R : (0 : R) < ↑pred_fp.m := by exact_mod_cast hpm
      have hzpow_lt : (2:R) ^ (pred_fp.e - FloatFormat.prec + 1) < (2:R) ^ e_base :=
        zpow_lt_zpow_right₀ (by norm_num : (1:R) < 2) hexp_lt_p
      have hm_le : (↑pred_fp.m : R) ≤ (2:R) ^ (p:ℤ) := by
        rw [zpow_natCast]; exact_mod_cast Nat.le_of_lt hm_p
      calc ↑pred_fp.m * (2:R) ^ (pred_fp.e - FloatFormat.prec + 1)
          < ↑pred_fp.m * (2:R) ^ e_base := mul_lt_mul_of_pos_left hzpow_lt hpm_R
        _ ≤ (2:R) ^ (p:ℤ) * (2:R) ^ e_base := mul_le_mul_of_nonneg_right hm_le (le_of_lt (zpow_pos (by norm_num : (0:R) < 2) _))
    -- Consider the power of 2 at e_base + p (between pred and succ)
    have he_valid_min : FloatFormat.min_exp ≤ e_base + (p : ℤ) := by
      have := pred_fp.valid.1; omega
    have he_valid_max : e_base + (p : ℤ) ≤ FloatFormat.max_exp := by
      -- From d_s ≥ 0 and succ ≥ (n+1)*E > 2^(p+3)*E, succ_fp.e > p + 2 + e_base
      -- So max_exp ≥ succ_fp.e > p + e_base
      have hm_s : succ_fp.m < 2 ^ p := succ_fp.valid.2.2.1
      have hds_exp : succ_fp.e - FloatFormat.prec + 1 ≥ e_base := by omega
      -- succ = m_s * 2^(d_s + e_base) with d_s ≥ 0
      -- succ ≥ (n+1)*E > 2^(p+3)*E, and m_s < 2^p
      -- so 2^(d_s + e_base) > 2^(p+3+e_base) / 2^p = 2^(3+e_base), i.e., d_s > 3
      -- and succ_fp.e = d_s + prec - 1 + e_base ≥ 4 + prec - 1 + e_base = prec + 3 + e_base
      -- max_exp ≥ succ_fp.e ≥ prec + 3 + e_base > p + e_base
      have := succ_fp.valid.2.1
      -- We just need max_exp ≥ e_base + p, i.e., succ_fp.e ≥ e_base + p
      -- succ_fp.e ≥ e_base + prec - 1 ≥ e_base + p - 1 (not enough, need ≥ e_base + p)
      -- Use: if succ_fp.e = e_base + prec - 1, then d_s = 0, succ = m_s * E,
      -- but m_s < 2^p < n+1, contradicting succ ≥ (n+1)*E
      by_contra h; push_neg at h
      -- succ_fp.e < e_base + p, combined with d_s ≥ 0 (succ_fp.e ≥ e_base + prec - 1)
      -- gives succ_fp.e - prec + 1 = e_base (since d_s = 0)
      have hd_s_eq : d_s = 0 := by
        have : succ_fp.e ≤ e_base + (p : ℤ) - 1 := by omega
        have : d_s ≤ 0 := by
          simp only [hd_s_def, hp_def] at *
          have hprec_eq : FloatFormat.prec = (FloatFormat.prec.toNat : ℤ) :=
            (Int.toNat_of_nonneg (by have := FloatFormat.valid_prec; omega)).symm
          omega
        omega
      -- So succ.toVal = m_s * E
      have hexp_eq : succ_fp.e - FloatFormat.prec + 1 = e_base := by
        simp only [hd_s_def, hp_def] at hd_s_eq
        omega
      have hsucc_eq : (succ_fp.toVal : R) = ↑succ_fp.m * E := by
        rw [hsucc_toVal, hE_def, hexp_eq]
      -- m_s ≥ n+1 from succ ≥ (n+1)*E
      have hms_ge : (n : ℤ) + 1 ≤ succ_fp.m := by
        have h1 : ((n : ℤ) + 1 : R) * E ≤ ↑succ_fp.m * E := by rw [← hsucc_eq]; exact hsucc_ge
        exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
      -- But m_s < 2^p ≤ n < n+1
      have hp_le_n : 2 ^ p ≤ n := Nat.le_of_lt (lt_of_le_of_lt
        (Nat.pow_le_pow_right (by omega) (by omega : p ≤ p + 3)) hn_large)
      have : succ_fp.m < n + 1 := lt_of_lt_of_le hm_s (Nat.le_succ_of_le hp_le_n)
      exact absurd hms_ge (by exact_mod_cast not_le.mpr this)
    obtain ⟨g, hgs, hgm, hgval⟩ := exists_representable_pow2 (R := R) (e_base + p) he_valid_min he_valid_max
    -- g.toVal = 2^(e_base + p) = 2^p * E
    have hg_eq : (g.toVal : R) = (2:R) ^ (p:ℤ) * E := by
      rw [hgval, hE_def, ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]; ring_nf
    -- pred < g < succ
    have hg_gt_pred : (pred_fp.toVal : R) < g.toVal := by rw [hg_eq]; exact hpred_lt
    have hg_lt_succ : (g.toVal : R) < succ_fp.toVal := by
      rw [hg_eq]
      calc (2:R) ^ (p:ℤ) * E < ((n : ℤ) + 1 : R) * E := by
            gcongr
            rw [zpow_natCast]; push_cast; exact_mod_cast Nat.le_succ_of_le (by
              have : 2 ^ p ≤ 2 ^ (p+3) := Nat.pow_le_pow_right (by omega) (by omega); omega)
        _ ≤ succ_fp.toVal := hsucc_ge
    exact hgap g hgs hgm hg_gt_pred hg_lt_succ
  -- Now express toVals as k * E with 16 | k
  -- pred.toVal = m_p * 2^(e_p - prec + 1) = m_p * 2^(d_p + e_base) = (m_p * 2^d_p) * E
  set k_p := pred_fp.m * 2 ^ d_p.toNat with hk_p_def
  set k_s := succ_fp.m * 2 ^ d_s.toNat with hk_s_def
  have hpred_eq : (pred_fp.toVal : R) = (k_p : R) * E := by
    rw [hpred_toVal, hE_def, hk_p_def]
    push_cast
    -- Goal: m * 2^(e-p+1) = m * 2^d_p.toNat * 2^e_base
    have h2ne : (2:R) ≠ 0 := by norm_num
    have hexp : pred_fp.e - FloatFormat.prec + 1 = ↑d_p.toNat + e_base := by
      have : (d_p.toNat : ℤ) = d_p := Int.toNat_of_nonneg hd_p_nonneg; omega
    rw [hexp, zpow_add₀ h2ne, zpow_natCast]; ring
  have hsucc_eq : (succ_fp.toVal : R) = (k_s : R) * E := by
    rw [hsucc_toVal, hE_def, hk_s_def]
    push_cast
    have h2ne : (2:R) ≠ 0 := by norm_num
    have hexp : succ_fp.e - FloatFormat.prec + 1 = ↑d_s.toNat + e_base := by
      have : (d_s.toNat : ℤ) = d_s := Int.toNat_of_nonneg hd_s_nonneg; omega
    rw [hexp, zpow_add₀ h2ne, zpow_natCast]; ring
  -- d_s ≥ 4: from succ ≥ (n+1)*E > 2^(p+3)*E and m_s < 2^p
  have hd_s_ge4 : 4 ≤ d_s.toNat := by
    by_contra hd_lt; push_neg at hd_lt
    have hm_s : succ_fp.m < 2 ^ p := succ_fp.valid.2.2.1
    -- k_s = m_s * 2^d_s < 2^p * 2^3 = 2^(p+3) ≤ n < n+1
    have hks_lt : k_s < 2 ^ (p + 3) := by
      rw [hk_s_def]
      calc succ_fp.m * 2 ^ d_s.toNat
          < 2 ^ p * 2 ^ d_s.toNat := by
            exact (Nat.mul_lt_mul_right (by positivity)).mpr hm_s
        _ ≤ 2 ^ p * 2 ^ 3 := by
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ = 2 ^ (p + 3) := by rw [← Nat.pow_add]
    -- But k_s * E ≥ (n+1)*E, so k_s ≥ n+1 > 2^(p+3)
    have hks_ge : n + 1 ≤ k_s := by
      have h1 : ((n : ℤ) + 1 : R) * E ≤ (k_s : R) * E := by rw [← hsucc_eq]; exact hsucc_ge
      exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
    omega
  -- d_p ≥ 2: if d_p < 2, pred < 2^(p+1)*E, use rep value at 2^(e_base+p+1) for contradiction
  have hd_p_ge2 : 2 ≤ d_p.toNat := by
    by_contra hd_lt; push_neg at hd_lt
    have hm_p : pred_fp.m < 2 ^ p := pred_fp.valid.2.2.1
    have hkp_lt : k_p < 2 ^ (p + 1) := by
      rw [hk_p_def]
      calc pred_fp.m * 2 ^ d_p.toNat
          < 2 ^ p * 2 ^ d_p.toNat := by
            exact (Nat.mul_lt_mul_right (by positivity)).mpr hm_p
        _ ≤ 2 ^ p * 2 ^ 1 := by
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ = 2 ^ (p + 1) := by rw [← Nat.pow_add]
    have hpred_lt : (pred_fp.toVal : R) < (2:R) ^ (e_base + (p : ℤ) + 1) := by
      rw [hpred_eq, hE_def]
      have hkp_R : (k_p : R) < (2:R) ^ (p + 1 : ℕ) := by exact_mod_cast hkp_lt
      calc (k_p : R) * (2:R) ^ e_base
          < (2:R) ^ (p + 1 : ℕ) * (2:R) ^ e_base := by
            exact mul_lt_mul_of_pos_right hkp_R (zpow_pos (by norm_num : (0:R) < 2) e_base)
        _ = (2:R) ^ (e_base + (p : ℤ) + 1) := by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]; congr 1; push_cast; ring
    -- Representable value at 2^(e_base + p + 1)
    have he2_max : e_base + (p : ℤ) + 1 ≤ FloatFormat.max_exp := by
      have := succ_fp.valid.2.1
      have : (d_s.toNat : ℤ) ≥ 4 := by exact_mod_cast hd_s_ge4
      have : (d_s.toNat : ℤ) = d_s := Int.toNat_of_nonneg hd_s_nonneg
      have hp_int : (p : ℤ) = FloatFormat.prec := by
        rw [hp_def]; exact Int.toNat_of_nonneg (by linarith [FloatFormat.valid_prec])
      omega
    have he2_min : FloatFormat.min_exp ≤ e_base + (p : ℤ) + 1 := by
      have := pred_fp.valid.1; omega
    obtain ⟨g, hgs, hgm, hgval⟩ := exists_representable_pow2 (R := R) (e_base + p + 1) he2_min he2_max
    have hg_gt : (pred_fp.toVal : R) < g.toVal := by rw [hgval]; exact hpred_lt
    have hg_lt : (g.toVal : R) < succ_fp.toVal := by
      rw [hgval, hsucc_eq, hE_def]
      have hks_large : 2 ^ (p + 1) < k_s := by
        have : n + 1 ≤ k_s := by
          have h1 : ((n : ℤ) + 1 : R) * E ≤ (k_s : R) * E := by rw [← hsucc_eq]; exact hsucc_ge
          exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
        have : 2 ^ (p + 1) ≤ n := by
          have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show p + 1 ≤ p + 3 by omega)
          omega
        omega
      calc (2:R) ^ (e_base + (p : ℤ) + 1)
          = (2:R) ^ (p + 1 : ℕ) * (2:R) ^ e_base := by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]; congr 1; push_cast; ring
        _ < (k_s : R) * (2:R) ^ e_base := by
            apply mul_lt_mul_of_pos_right _ (zpow_pos (by norm_num : (0:R) < 2) e_base)
            exact_mod_cast hks_large
    exact hgap g hgs hgm hg_gt hg_lt
  -- Now 4 | k_p and 16 | k_s
  have h4_kp : 4 ∣ k_p := by
    rw [hk_p_def]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd_p_ge2) _
  have h16_ks : 16 ∣ k_s := by
    rw [hk_s_def]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd_s_ge4) _
  -- k_p + k_s ≡ 0 mod 4
  have h4_sum : 4 ∣ (k_p + k_s) := Nat.dvd_add h4_kp (dvd_trans (by norm_num : (4:ℕ) ∣ 16) h16_ks)
  -- 2n ≡ 2 mod 4 (n odd), so k_p + k_s ≠ 2n
  have hsum_ne : k_p + k_s ≠ 2 * n := by omega
  -- k_p ≤ n-1 and k_s ≥ n+1
  have hkp_le : k_p ≤ n - 1 := by
    have h1 : (k_p : R) * E ≤ ((n : ℤ) - 1 : R) * E := by rw [← hpred_eq]; exact hpred_le
    have h2 : (k_p : R) ≤ ((n : ℤ) - 1 : R) := le_of_mul_le_mul_right h1 hE_pos
    have hn_ge : 1 ≤ n := by omega
    have : (k_p : ℤ) ≤ (n : ℤ) - 1 := by exact_mod_cast h2
    omega
  have hks_ge : n + 1 ≤ k_s := by
    have h1 : ((n : ℤ) + 1 : R) * E ≤ (k_s : R) * E := by rw [← hsucc_eq]; exact hsucc_ge
    exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
  -- k_p + k_s ≤ 2(n-1) or k_p + k_s ≥ 2(n+1)
  have hsum_bound : k_p + k_s ≤ 2 * n - 2 ∨ 2 * n + 2 ≤ k_p + k_s := by omega
  -- Convert to R
  rcases hsum_bound with h | h
  · left
    rw [hpred_eq, hsucc_eq]
    have : ((k_p + k_s : ℕ) : R) ≤ (2 * n - 2 : ℕ) := by exact_mod_cast h
    have h2le : 2 ≤ 2 * n := by omega
    have hcast : ((2 * n - 2 : ℕ) : R) = 2 * (((n : ℤ) - 1 : R)) := by
      rw [Nat.cast_sub h2le]; push_cast; ring
    calc ((k_p : R) * E + (k_s : R) * E) / 2
        = ((k_p + k_s : ℕ) : R) * E / 2 := by push_cast; ring
      _ ≤ ((2 * n - 2 : ℕ) : R) * E / 2 := by gcongr
      _ = (((n : ℤ) - 1 : R)) * E := by rw [hcast]; ring
  · right
    rw [hpred_eq, hsucc_eq]
    have : (2 * n + 2 : ℕ) ≤ ((k_p + k_s : ℕ) : R) := by exact_mod_cast h
    have hcast : ((2 * n + 2 : ℕ) : R) = 2 * (((n : ℤ) + 1 : R)) := by push_cast; ring
    calc (((n : ℤ) + 1 : R)) * E
        = ((2 * n + 2 : ℕ) : R) * E / 2 := by rw [hcast]; ring
      _ ≤ ((k_p + k_s : ℕ) : R) * E / 2 := by gcongr
      _ = ((k_p : R) * E + (k_s : R) * E) / 2 := by push_cast; ring

/-- No positive representable float has `toVal` strictly inside `(lo, hi)`. -/
abbrev noRepresentableIn [FloatFormat] {R : Type*} [Field R] [LT R] (lo hi : R) : Prop :=
  ∀ f : FiniteFp, f.s = false → 0 < f.m → ¬(lo < (f.toVal : R) ∧ (f.toVal : R) < hi)

/-- `roundDown` is constant on positive open intervals containing no representable float.

    If no positive representable float has `toVal` in `(lo, hi)`, then `roundDown v₁ = roundDown v₂`
    for any `v₁, v₂ ∈ (lo, hi)`. Uses monotonicity + idempotence for the maximality argument. -/
theorem roundDown_eq_of_no_representable {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {lo hi : R} (hlo_pos : 0 < lo)
    (hno_rep : noRepresentableIn lo hi)
    {v₁ v₂ : R} (hv₁_lo : lo < v₁) (hv₁_hi : v₁ < hi) (hv₂_lo : lo < v₂) (hv₂_hi : v₂ < hi) :
    roundDown v₁ = roundDown v₂ := by
  wlog hle : v₁ ≤ v₂ with H
  · exact (H hlo_pos hno_rep hv₂_lo hv₂_hi hv₁_lo hv₁_hi (le_of_lt (not_le.mp hle))).symm
  have hmono := roundDown_mono hle
  by_contra hne
  have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
  have hrd₂ : roundDown v₂ = Fp.finite (findPredecessorPos v₂ hv₂_pos) := by
    unfold roundDown; exact findPredecessor_pos_eq v₂ hv₂_pos
  set g := findPredecessorPos v₂ hv₂_pos
  have hg_le : (g.toVal : R) ≤ v₂ := findPredecessorPos_le v₂ hv₂_pos
  have hgs : g.s = false := findPredecessorPos_sign_false v₂ hv₂_pos
  rcases le_or_gt (g.toVal : R) v₁ with hg_le_v₁ | hg_gt_v₁
  · -- g.toVal ≤ v₁: idempotent + mono gives roundDown(v₂) ≤ roundDown(v₁)
    have hidem := roundDown_idempotent (R := R) g (Or.inl hgs)
    have hge : roundDown v₂ ≤ roundDown v₁ := by
      rw [hrd₂, ← hidem]; exact roundDown_mono hg_le_v₁
    exact hne (Fp.le_antisymm hmono hge)
  · -- g.toVal > v₁ > lo: representable in (lo, hi)
    have hgm : 0 < g.m := by
      by_contra h; push_neg at h
      have : g.m = 0 := by omega
      have : (g.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [this]; simp
      linarith [lt_trans hlo_pos hv₁_lo]
    exact absurd ⟨lt_trans hv₁_lo hg_gt_v₁, lt_of_le_of_lt hg_le hv₂_hi⟩ (hno_rep g hgs hgm)

/-- `roundUp` is constant on positive open intervals containing no representable float. -/
theorem roundUp_eq_of_no_representable {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {lo hi : R} (hlo_pos : 0 < lo)
    (hno_rep : noRepresentableIn lo hi)
    {v₁ v₂ : R} (hv₁_lo : lo < v₁) (hv₁_hi : v₁ < hi) (hv₂_lo : lo < v₂) (hv₂_hi : v₂ < hi) :
    roundUp v₁ = roundUp v₂ := by
  wlog hle : v₁ ≤ v₂ with H
  · exact (H hlo_pos hno_rep hv₂_lo hv₂_hi hv₁_lo hv₁_hi (le_of_lt (not_le.mp hle))).symm
  have hmono := roundUp_mono hle
  by_contra hne
  have hv₁_pos : 0 < v₁ := lt_trans hlo_pos hv₁_lo
  -- Unfold roundUp v₁ to findSuccessorPos
  rw [show roundUp v₁ = findSuccessorPos v₁ hv₁_pos from by
    unfold roundUp; exact findSuccessor_pos_eq v₁ hv₁_pos] at hmono hne
  rcases hfsp : findSuccessorPos v₁ hv₁_pos with g | b | _
  · -- Case: Fp.finite g — successor is a finite float
    rw [hfsp] at hmono hne
    have hg_ge : v₁ ≤ (g.toVal : R) := findSuccessorPos_ge v₁ hv₁_pos g hfsp
    have hg_pos : (0 : R) < g.toVal := lt_of_lt_of_le hv₁_pos hg_ge
    have hgm : 0 < g.m := by
      by_contra h; push_neg at h
      have : g.m = 0 := by omega
      have : (g.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [this]; simp
      linarith
    have hgs : g.s = false := by
      by_contra hs
      have hs_t : g.s = true := by revert hs; cases g.s <;> simp
      have : (g.toVal : R) ≤ 0 := by
        unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hs_t]; simp
        exact mul_nonneg (by positivity) (zpow_pos (by norm_num : (0:R) < 2) _).le
      linarith
    rcases le_or_gt (g.toVal : R) v₂ with hg_le | hg_gt
    · -- g.toVal ≤ v₂: g is representable in (lo, hi)
      exact absurd ⟨lt_of_lt_of_le hv₁_lo hg_ge, lt_of_le_of_lt hg_le hv₂_hi⟩
        (hno_rep g hgs hgm)
    · -- g.toVal > v₂: roundUp(v₂) ≤ g = roundUp(v₁)
      have hidem := roundUp_idempotent (R := R) g (Or.inl hgs)
      have hge : roundUp v₂ ≤ Fp.finite g := by
        rw [← hidem]; exact roundUp_mono (le_of_lt hg_gt)
      exact hne (Fp.le_antisymm hmono hge)
  · -- Case: Fp.infinite b — overflow
    rw [hfsp] at hmono hne
    cases b with
    | true => exact absurd hfsp (findSuccessorPos_ne_neg_inf v₁ hv₁_pos)
    | false =>
      -- roundUp v₁ = +∞, hmono: +∞ ≤ roundUp v₂
      -- Everything ≤ +∞, so Fp.le_antisymm gives equality
      have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
      have hge : roundUp v₂ ≤ Fp.infinite false := by
        rw [show roundUp v₂ = findSuccessorPos v₂ hv₂_pos from by
          unfold roundUp; exact findSuccessor_pos_eq v₂ hv₂_pos]
        rcases hfsp₂ : findSuccessorPos v₂ hv₂_pos with f | c | _
        · rw [Fp.le_def]; left; dsimp [LT.lt]; decide
        · cases c with
          | false => exact Fp.le_refl _
          | true => exact absurd hfsp₂ (findSuccessorPos_ne_neg_inf v₂ hv₂_pos)
        · exact absurd hfsp₂ (findSuccessorPos_ne_nan v₂ hv₂_pos)
      exact hne (Fp.le_antisymm hmono hge)
  · -- Case: Fp.NaN — impossible for findSuccessorPos
    exact absurd hfsp (findSuccessorPos_ne_nan v₁ hv₁_pos)

/-- `roundTowardZero` is constant on positive open intervals with no representable float. -/
theorem roundTowardZero_eq_of_no_representable {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {lo hi : R} (hlo_pos : 0 < lo)
    (hno_rep : noRepresentableIn lo hi)
    {v₁ v₂ : R} (hv₁_lo : lo < v₁) (hv₁_hi : v₁ < hi) (hv₂_lo : lo < v₂) (hv₂_hi : v₂ < hi) :
    roundTowardZero v₁ = roundTowardZero v₂ := by
  have hv₁_pos : 0 < v₁ := lt_trans hlo_pos hv₁_lo
  have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
  rw [roundTowardZero_pos_eq v₁ hv₁_pos, roundTowardZero_pos_eq v₂ hv₂_pos]
  exact roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi

/-- In an odd interval with no representable float, a crossing from roundDown to roundUp
    is impossible for roundNearestTiesToEven. This handles the key sorry case in
    `round_eq_on_odd_interval`. -/
private theorem rnTE_no_crossing {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {v w : R} {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1) (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (hv_pos : 0 < v) (hw_pos : 0 < w)
    (hv_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < v)
    (hv_hi : v < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hw_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < w)
    (hw_hi : w < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hno_rep : noRepresentableIn (((n : ℤ) - 1 : R) * (2 : R) ^ e_base)
        (((n : ℤ) + 1 : R) * (2 : R) ^ e_base))
    (hrd_eq : roundDown v = roundDown w)
    (hru_eq : roundUp v = roundUp w)
    (hrd_ne : roundDown v ≠ roundUp v)
    (hv_rd : roundNearestTiesToEven v = roundDown v)
    (hw_ru : roundNearestTiesToEven w = roundUp w) : False := by
  -- Extract pred_fp from roundDown v
  have hrd_v : roundDown v = Fp.finite (findPredecessorPos v hv_pos) :=
    by unfold roundDown; exact findPredecessor_pos_eq v hv_pos
  set pred_fp := findPredecessorPos v hv_pos with hpred_def
  have hpred_le_v : (pred_fp.toVal : R) ≤ v := findPredecessorPos_le v hv_pos
  have hpred_s : pred_fp.s = false := findPredecessorPos_sign_false v hv_pos
  -- Extract succ from roundUp v
  have hru_v : roundUp v = findSuccessorPos v hv_pos :=
    by unfold roundUp; exact findSuccessor_pos_eq v hv_pos
  -- Rewrite roundUp v everywhere before case-splitting
  rw [hru_v] at hrd_ne hru_eq
  rcases hru_case : findSuccessorPos v hv_pos with succ_fp | b | _
  · -- Case 1: roundUp v = Fp.finite succ_fp
    rw [hrd_v] at hrd_ne hrd_eq
    have hsucc_ge_v : v ≤ (succ_fp.toVal : R) :=
      findSuccessorPos_ge v hv_pos succ_fp hru_case
    -- succ_fp.s = false (positive since toVal ≥ v > 0)
    have hsucc_s : succ_fp.s = false := by
      by_contra hs
      have hs_t : succ_fp.s = true := by revert hs; cases succ_fp.s <;> simp
      have : (succ_fp.toVal : R) ≤ 0 := by
        unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hs_t]; simp
        exact mul_nonneg (by positivity) (zpow_pos (by norm_num : (0:R) < 2) _).le
      linarith
    have hsucc_m : 0 < succ_fp.m := by
      by_contra h; push_neg at h; have : succ_fp.m = 0 := by omega
      have : (succ_fp.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [this]; simp
      linarith
    -- succ_fp.toVal ≥ (n+1)*E (otherwise it's representable in interval)
    have hsucc_bound : ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ (succ_fp.toVal : R) := by
      by_contra h; push_neg at h
      exact hno_rep succ_fp hsucc_s hsucc_m ⟨lt_of_lt_of_le hv_lo hsucc_ge_v, h⟩
    -- pred_fp.m > 0: if m = 0, toVal = 0, but then roundDown_idempotent on
    -- succ_fp gives roundDown(succ_fp.toVal) = succ_fp, and monotonicity gives
    -- pred_fp = roundDown v ≤ roundDown(succ_fp.toVal) = succ_fp; but also
    -- succ_fp.toVal ≥ (n+1)*E and v < (n+1)*E ≤ succ_fp.toVal, so
    -- roundDown(succ_fp.toVal) ≤ roundDown v wouldn't help. Instead:
    -- pred_fp.toVal ≤ v and pred_fp.toVal = 0, so v > 0 = pred_fp.toVal.
    -- No positive representable has toVal ≤ v (since pred is the largest ≤ v and toVal = 0).
    -- But succ_fp is a positive representable with succ_fp.toVal ≥ v > 0, so succ_fp.toVal > 0.
    -- Actually we just need pred for midpoint_outside_odd_interval.
    -- Use: if pred_fp.m = 0, pred_fp.toVal = 0 < (n-1)*E (since n > 8, E > 0).
    -- midpoint = succ_fp.toVal / 2 ≥ (n+1)*E/2.
    -- Since n ≥ 9: (n+1)/2 ≤ n-1, so midpoint might be ≤ (n-1)*E. Either way
    -- this doesn't trivially work for midpoint_outside_odd_interval. So let's
    -- handle pred_fp.m = 0 separately.
    by_cases hpred_m : 0 < pred_fp.m
    · -- Main case: pred_fp.m > 0
      have hpred_bound : (pred_fp.toVal : R) ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base := by
        by_contra h; push_neg at h
        exact hno_rep pred_fp hpred_s hpred_m ⟨h, lt_of_le_of_lt hpred_le_v hv_hi⟩
      -- pred and succ are adjacent: no representable strictly between them
      have hadj : ∀ g : FiniteFp, g.s = false → 0 < g.m →
          (pred_fp.toVal : R) < (g.toVal : R) → (g.toVal : R) < (succ_fp.toVal : R) → False := by
        intro g hgs hgm hg_gt_pred hg_lt_succ
        rcases le_or_gt (g.toVal : R) (((n : ℤ) - 1 : R) * (2 : R) ^ e_base) with hg_le_lo | hg_gt_lo
        · -- g ≤ lo: roundDown_idempotent(g) + roundDown_mono(g ≤ v) gives g ≤ pred
          have hmono : roundDown (g.toVal : R) ≤ roundDown v :=
            roundDown_mono (le_trans (le_of_lt (lt_of_le_of_lt hg_le_lo hv_lo)) (le_refl v))
          rw [hrd_v, roundDown_idempotent (R := R) g (Or.inl hgs)] at hmono
          exact absurd hg_gt_pred (not_lt.mpr (FiniteFp.le_toVal_le R
            ((Fp.finite_le_finite_iff g pred_fp).mp hmono)))
        · rcases lt_or_ge (g.toVal : R) (((n : ℤ) + 1 : R) * (2 : R) ^ e_base) with hg_lt_hi | hg_ge_hi
          · exact hno_rep g hgs hgm ⟨hg_gt_lo, hg_lt_hi⟩
          · -- g ≥ hi ≥ succ: contradiction with g < succ
            have hmono : roundUp v ≤ roundUp (g.toVal : R) :=
              roundUp_mono (le_trans (le_of_lt hv_hi) hg_ge_hi)
            rw [hru_v, hru_case, roundUp_idempotent (R := R) g (Or.inl hgs)] at hmono
            exact absurd hg_lt_succ (not_lt.mpr (FiniteFp.le_toVal_le R
              ((Fp.finite_le_finite_iff succ_fp g).mp hmono)))
      -- Apply midpoint_outside_odd_interval
      -- v, w < overflow threshold (roundUp v = Fp.finite succ_fp, so v ≤ succ_fp ≤ lff < thresh)
      have hsucc_lt_thresh : (succ_fp.toVal : R) <
          FloatFormat.overflowThreshold R :=
        calc (succ_fp.toVal : R)
            ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat succ_fp
          _ < _ := largestFiniteFloat_lt_overflow_threshold
      have hv_lt_thresh : v < FloatFormat.overflowThreshold R :=
        lt_of_le_of_lt hsucc_ge_v hsucc_lt_thresh
      have hw_lt_thresh : w < FloatFormat.overflowThreshold R := by
        -- roundUp w = Fp.finite succ_fp too, so w ≤ succ_fp < thresh
        have hru_w : roundUp w = Fp.finite succ_fp := hru_eq.symm.trans hru_case
        have hw_le_succ : w ≤ (succ_fp.toVal : R) := by
          have hw_pos' : 0 < w := hw_pos
          rw [show roundUp w = findSuccessorPos w hw_pos' from by
            unfold roundUp; exact findSuccessor_pos_eq w hw_pos'] at hru_w
          rcases hfsp : findSuccessorPos w hw_pos' with g | _ | _
          · rw [hfsp, Fp.finite.injEq] at hru_w; rw [← hru_w]
            exact findSuccessorPos_ge w hw_pos' g hfsp
          · rw [hfsp] at hru_w; exact absurd hru_w (by simp)
          · exact absurd hfsp (findSuccessorPos_ne_nan w hw_pos')
        linarith
      have hru_v_eq : roundUp v = Fp.finite succ_fp := hru_v.trans hru_case
      rcases midpoint_outside_odd_interval hn_odd hn_large pred_fp succ_fp
        hpred_s hpred_m hsucc_s hsucc_m hpred_bound hsucc_bound hadj with hmid_lo | hmid_hi
      · -- mid ≤ lo < v: v > mid, so rnTE v = roundUp v, contradicting hv_rd
        have hv_gt_mid : v > ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by linarith
        have hte_up := rnEven_above_mid_roundUp v _ pred_fp succ_fp hv_pos
          hv_lt_thresh hrd_v hru_v_eq rfl hv_gt_mid
        -- hte_up : rnTE v = roundUp v, but hv_rd : rnTE v = roundDown v
        have : roundDown v = roundUp v := hv_rd.symm.trans hte_up
        rw [hrd_v, hru_v] at this; exact hrd_ne this
      · -- mid ≥ hi > w: w < mid, so rnTE w = roundDown w, contradicting hw_ru
        have hw_lt_mid : w < ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by linarith
        have hte_down := rnEven_below_mid_roundDown w _ pred_fp succ_fp hw_pos
          hw_lt_thresh hrd_eq.symm (hru_eq.symm.trans hru_case) rfl hw_lt_mid
        -- hte_down : rnTE w = roundDown w, but hw_ru : rnTE w = roundUp w
        have : roundDown w = roundUp w := hte_down.symm.trans hw_ru
        rw [← hrd_eq, ← hru_eq] at this; exact hrd_ne this
    · -- Degenerate case: pred_fp.m = 0 → pred_fp.toVal = 0
      push_neg at hpred_m; have hm0 : pred_fp.m = 0 := by omega
      have hpred_val : (pred_fp.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [hm0]; simp
      have hmid_outside := midpoint_zero_pred_outside_odd_interval (R := R)
        (e_base := e_base) hn_odd hn_large hsucc_s
      -- Use midpoint position to derive contradiction via rnTE lemmas
      have hsucc_lt_thresh : (succ_fp.toVal : R) <
          FloatFormat.overflowThreshold R :=
        calc (succ_fp.toVal : R)
            ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat succ_fp
          _ < _ := largestFiniteFloat_lt_overflow_threshold
      have hv_lt_thresh := lt_of_le_of_lt hsucc_ge_v hsucc_lt_thresh
      have hru_v_eq : roundUp v = Fp.finite succ_fp := hru_v.trans hru_case
      have hw_lt_thresh : w < FloatFormat.overflowThreshold R := by
        have hru_w : roundUp w = Fp.finite succ_fp := hru_eq.symm.trans hru_case
        have hw_le_succ : w ≤ (succ_fp.toVal : R) := by
          rw [show roundUp w = findSuccessorPos w hw_pos from by
            unfold roundUp; exact findSuccessor_pos_eq w hw_pos] at hru_w
          rcases hfsp : findSuccessorPos w hw_pos with g | _ | _
          · rw [hfsp, Fp.finite.injEq] at hru_w; rw [← hru_w]
            exact findSuccessorPos_ge w hw_pos g hfsp
          · rw [hfsp] at hru_w; exact absurd hru_w (by simp)
          · exact absurd hfsp (findSuccessorPos_ne_nan w hw_pos)
        linarith
      rcases hmid_outside with hmid_lo | hmid_hi
      · have hv_gt_mid : v > ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by
          rw [hpred_val]; linarith [hmid_lo]
        have hte_up := rnEven_above_mid_roundUp v _ pred_fp succ_fp hv_pos
          hv_lt_thresh hrd_v hru_v_eq rfl hv_gt_mid
        have : roundDown v = roundUp v := hv_rd.symm.trans hte_up
        rw [hrd_v, hru_v] at this; exact hrd_ne this
      · have hw_lt_mid : w < ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by
          rw [hpred_val]; linarith [hmid_hi]
        have hte_down := rnEven_below_mid_roundDown w _ pred_fp succ_fp hw_pos
          hw_lt_thresh hrd_eq.symm (hru_eq.symm.trans hru_case) rfl hw_lt_mid
        have : roundDown w = roundUp w := hte_down.symm.trans hw_ru
        rw [← hrd_eq, ← hru_eq] at this; exact hrd_ne this
  · -- Case 2: roundUp v = Fp.infinite b (overflow)
    cases b with
    | true => exact absurd hru_case (findSuccessorPos_ne_neg_inf v hv_pos)
    | false =>
      -- roundUp v = +∞ and roundUp w = +∞
      have hru_v_inf : roundUp v = Fp.infinite false := hru_v.trans hru_case
      have hru_w_inf : roundUp w = Fp.infinite false := hru_eq.symm.trans hru_case
      set OT := FloatFormat.overflowThreshold R
      -- v < OT (otherwise rnTE v = +∞, contradicting hv_rd = roundDown v which is finite)
      have hv_lt_OT : v < OT := by
        by_contra h; push_neg at h
        have := rnEven_ge_inf v h
        rw [hv_rd, hrd_v] at this; exact absurd this (by simp)
      -- w ≥ OT (otherwise rnEven_pos_succ_overflow gives rnTE w = roundDown w, contradicting hw_ru)
      have hw_ge_OT : OT ≤ w := by
        by_contra h; push_neg at h
        have hrd_w : roundDown w = Fp.finite (findPredecessorPos w hw_pos) := by
          unfold roundDown; exact findPredecessor_pos_eq w hw_pos
        have hte_w := rnEven_pos_succ_overflow w (findPredecessorPos w hw_pos)
          hw_pos h hrd_w hru_w_inf
        rw [hw_ru, hru_w_inf] at hte_w; exact absurd hte_w (by simp)
      -- OT ∈ ((n-1)*E, (n+1)*E): from v < OT and (n-1)*E < v, and OT ≤ w < (n+1)*E
      have hOT_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < OT := lt_of_lt_of_le hv_lo hv_lt_OT.le
      have hOT_hi : OT < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base := lt_of_le_of_lt hw_ge_OT hw_hi
      exact overflow_threshold_outside_odd_interval hn_odd hn_large hOT_lo hOT_hi
  · exact absurd hru_case (findSuccessorPos_ne_nan v hv_pos)

/-- In an odd interval, a crossing from roundDown to roundUp is impossible for
    roundNearestTiesAwayFromZero. -/
private theorem rnTA_no_crossing {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {v w : R} {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1) (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (hv_pos : 0 < v) (hw_pos : 0 < w)
    (hv_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < v)
    (hv_hi : v < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hw_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < w)
    (hw_hi : w < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hno_rep : noRepresentableIn (((n : ℤ) - 1 : R) * (2 : R) ^ e_base)
        (((n : ℤ) + 1 : R) * (2 : R) ^ e_base))
    (hrd_eq : roundDown v = roundDown w)
    (hru_eq : roundUp v = roundUp w)
    (hrd_ne : roundDown v ≠ roundUp v)
    (hv_rd : roundNearestTiesAwayFromZero v = roundDown v)
    (hw_ru : roundNearestTiesAwayFromZero w = roundUp w) : False := by
  -- Proof is identical to rnTE_no_crossing with rnAway midpoint lemmas
  have hrd_v : roundDown v = Fp.finite (findPredecessorPos v hv_pos) :=
    by unfold roundDown; exact findPredecessor_pos_eq v hv_pos
  set pred_fp := findPredecessorPos v hv_pos with hpred_def
  have hpred_le_v : (pred_fp.toVal : R) ≤ v := findPredecessorPos_le v hv_pos
  have hpred_s : pred_fp.s = false := findPredecessorPos_sign_false v hv_pos
  have hru_v : roundUp v = findSuccessorPos v hv_pos :=
    by unfold roundUp; exact findSuccessor_pos_eq v hv_pos
  rw [hru_v] at hrd_ne hru_eq
  rcases hru_case : findSuccessorPos v hv_pos with succ_fp | b | _
  · rw [hrd_v] at hrd_ne hrd_eq
    have hsucc_ge_v : v ≤ (succ_fp.toVal : R) :=
      findSuccessorPos_ge v hv_pos succ_fp hru_case
    have hsucc_s : succ_fp.s = false := by
      by_contra hs
      have hs_t : succ_fp.s = true := by revert hs; cases succ_fp.s <;> simp
      have : (succ_fp.toVal : R) ≤ 0 := by
        unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hs_t]; simp
        exact mul_nonneg (by positivity) (zpow_pos (by norm_num : (0:R) < 2) _).le
      linarith
    have hsucc_m : 0 < succ_fp.m := by
      by_contra h; push_neg at h; have : succ_fp.m = 0 := by omega
      have : (succ_fp.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [this]; simp
      linarith
    have hsucc_bound : ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ (succ_fp.toVal : R) := by
      by_contra h; push_neg at h
      exact hno_rep succ_fp hsucc_s hsucc_m ⟨lt_of_lt_of_le hv_lo hsucc_ge_v, h⟩
    by_cases hpred_m : 0 < pred_fp.m
    · have hpred_bound : (pred_fp.toVal : R) ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base := by
        by_contra h; push_neg at h
        exact hno_rep pred_fp hpred_s hpred_m ⟨h, lt_of_le_of_lt hpred_le_v hv_hi⟩
      have hadj : ∀ g : FiniteFp, g.s = false → 0 < g.m →
          (pred_fp.toVal : R) < (g.toVal : R) → (g.toVal : R) < (succ_fp.toVal : R) → False := by
        intro g hgs hgm hg_gt_pred hg_lt_succ
        rcases le_or_gt (g.toVal : R) (((n : ℤ) - 1 : R) * (2 : R) ^ e_base) with hg_le_lo | hg_gt_lo
        · have hmono : roundDown (g.toVal : R) ≤ roundDown v :=
            roundDown_mono (le_trans (le_of_lt (lt_of_le_of_lt hg_le_lo hv_lo)) (le_refl v))
          rw [hrd_v, roundDown_idempotent (R := R) g (Or.inl hgs)] at hmono
          exact absurd hg_gt_pred (not_lt.mpr (FiniteFp.le_toVal_le R
            ((Fp.finite_le_finite_iff g pred_fp).mp hmono)))
        · rcases lt_or_ge (g.toVal : R) (((n : ℤ) + 1 : R) * (2 : R) ^ e_base) with hg_lt_hi | hg_ge_hi
          · exact hno_rep g hgs hgm ⟨hg_gt_lo, hg_lt_hi⟩
          · have hmono : roundUp v ≤ roundUp (g.toVal : R) :=
              roundUp_mono (le_trans (le_of_lt hv_hi) hg_ge_hi)
            rw [hru_v, hru_case, roundUp_idempotent (R := R) g (Or.inl hgs)] at hmono
            exact absurd hg_lt_succ (not_lt.mpr (FiniteFp.le_toVal_le R
              ((Fp.finite_le_finite_iff succ_fp g).mp hmono)))
      have hsucc_lt_thresh : (succ_fp.toVal : R) <
          FloatFormat.overflowThreshold R :=
        calc (succ_fp.toVal : R)
            ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat succ_fp
          _ < _ := largestFiniteFloat_lt_overflow_threshold
      have hv_lt_thresh : v < FloatFormat.overflowThreshold R :=
        lt_of_le_of_lt hsucc_ge_v hsucc_lt_thresh
      have hw_lt_thresh : w < FloatFormat.overflowThreshold R := by
        have hru_w : roundUp w = Fp.finite succ_fp := hru_eq.symm.trans hru_case
        have hw_le_succ : w ≤ (succ_fp.toVal : R) := by
          have hw_pos' : 0 < w := hw_pos
          rw [show roundUp w = findSuccessorPos w hw_pos' from by
            unfold roundUp; exact findSuccessor_pos_eq w hw_pos'] at hru_w
          rcases hfsp : findSuccessorPos w hw_pos' with g | _ | _
          · rw [hfsp, Fp.finite.injEq] at hru_w; rw [← hru_w]
            exact findSuccessorPos_ge w hw_pos' g hfsp
          · rw [hfsp] at hru_w; exact absurd hru_w (by simp)
          · exact absurd hfsp (findSuccessorPos_ne_nan w hw_pos')
        linarith
      have hru_v_eq : roundUp v = Fp.finite succ_fp := hru_v.trans hru_case
      rcases midpoint_outside_odd_interval hn_odd hn_large pred_fp succ_fp
        hpred_s hpred_m hsucc_s hsucc_m hpred_bound hsucc_bound hadj with hmid_lo | hmid_hi
      · have hv_ge_mid : v ≥ ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by linarith
        have hta_up := rnAway_ge_mid_roundUp v _ pred_fp succ_fp hv_pos
          hv_lt_thresh hrd_v hru_v_eq rfl hv_ge_mid
        have : roundDown v = roundUp v := hv_rd.symm.trans hta_up
        rw [hrd_v, hru_v] at this; exact hrd_ne this
      · have hw_lt_mid : w < ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by linarith
        have hta_down := rnAway_lt_mid_roundDown w _ pred_fp succ_fp hw_pos
          hw_lt_thresh hrd_eq.symm (hru_eq.symm.trans hru_case) rfl hw_lt_mid
        have : roundDown w = roundUp w := hta_down.symm.trans hw_ru
        rw [← hrd_eq, ← hru_eq] at this; exact hrd_ne this
    · push_neg at hpred_m; have hm0 : pred_fp.m = 0 := by omega
      have hpred_val : (pred_fp.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [hm0]; simp
      have hmid_outside := midpoint_zero_pred_outside_odd_interval (R := R)
        (e_base := e_base) hn_odd hn_large hsucc_s
      have hsucc_lt_thresh : (succ_fp.toVal : R) <
          FloatFormat.overflowThreshold R :=
        calc (succ_fp.toVal : R)
            ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat succ_fp
          _ < _ := largestFiniteFloat_lt_overflow_threshold
      have hv_lt_thresh := lt_of_le_of_lt hsucc_ge_v hsucc_lt_thresh
      have hru_v_eq : roundUp v = Fp.finite succ_fp := hru_v.trans hru_case
      have hw_lt_thresh : w < FloatFormat.overflowThreshold R := by
        have hru_w : roundUp w = Fp.finite succ_fp := hru_eq.symm.trans hru_case
        have hw_le_succ : w ≤ (succ_fp.toVal : R) := by
          rw [show roundUp w = findSuccessorPos w hw_pos from by
            unfold roundUp; exact findSuccessor_pos_eq w hw_pos] at hru_w
          rcases hfsp : findSuccessorPos w hw_pos with g | _ | _
          · rw [hfsp, Fp.finite.injEq] at hru_w; rw [← hru_w]
            exact findSuccessorPos_ge w hw_pos g hfsp
          · rw [hfsp] at hru_w; exact absurd hru_w (by simp)
          · exact absurd hfsp (findSuccessorPos_ne_nan w hw_pos)
        linarith
      rcases hmid_outside with hmid_lo | hmid_hi
      · have hv_ge_mid : v ≥ ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by
          rw [hpred_val]; linarith [hmid_lo]
        have hta_up := rnAway_ge_mid_roundUp v _ pred_fp succ_fp hv_pos
          hv_lt_thresh hrd_v hru_v_eq rfl hv_ge_mid
        have : roundDown v = roundUp v := hv_rd.symm.trans hta_up
        rw [hrd_v, hru_v] at this; exact hrd_ne this
      · have hw_lt_mid : w < ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by
          rw [hpred_val]; linarith [hmid_hi]
        have hta_down := rnAway_lt_mid_roundDown w _ pred_fp succ_fp hw_pos
          hw_lt_thresh hrd_eq.symm (hru_eq.symm.trans hru_case) rfl hw_lt_mid
        have : roundDown w = roundUp w := hta_down.symm.trans hw_ru
        rw [← hrd_eq, ← hru_eq] at this; exact hrd_ne this
  · cases b with
    | true => exact absurd hru_case (findSuccessorPos_ne_neg_inf v hv_pos)
    | false =>
      -- roundUp v = +∞ and roundUp w = +∞
      have hru_v_inf : roundUp v = Fp.infinite false := hru_v.trans hru_case
      have hru_w_inf : roundUp w = Fp.infinite false := hru_eq.symm.trans hru_case
      set OT := FloatFormat.overflowThreshold R
      -- v < OT (otherwise rnTA v = +∞, contradicting hv_rd = roundDown v which is finite)
      have hv_lt_OT : v < OT := by
        by_contra h; push_neg at h
        have := rnAway_ge_inf v h
        rw [hv_rd, hrd_v] at this; exact absurd this (by simp)
      -- w ≥ OT (otherwise rnAway_pos_succ_overflow gives rnTA w = roundDown w, contradicting hw_ru)
      have hw_ge_OT : OT ≤ w := by
        by_contra h; push_neg at h
        have hrd_w : roundDown w = Fp.finite (findPredecessorPos w hw_pos) := by
          unfold roundDown; exact findPredecessor_pos_eq w hw_pos
        have hta_w := rnAway_pos_succ_overflow w (findPredecessorPos w hw_pos)
          hw_pos h hrd_w hru_w_inf
        rw [hw_ru, hru_w_inf] at hta_w; exact absurd hta_w (by simp)
      -- OT ∈ ((n-1)*E, (n+1)*E)
      have hOT_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < OT := lt_of_lt_of_le hv_lo hv_lt_OT.le
      have hOT_hi : OT < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base := lt_of_le_of_lt hw_ge_OT hw_hi
      exact overflow_threshold_outside_odd_interval hn_odd hn_large hOT_lo hOT_hi
  · exact absurd hru_case (findSuccessorPos_ne_nan v hv_pos)

/-- Any rounding mode is constant on an odd interval `((n-1)*E, (n+1)*E)` with
    `n` odd and `n > 2^(prec+3)`. This combines the directional constancy (Steps 1-2)
    with the parity argument for roundNearest modes. -/
theorem round_eq_on_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    {v₁ v₂ : R}
    (hv₁_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < v₁)
    (hv₁_hi : v₁ < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hv₂_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < v₂)
    (hv₂_hi : v₂ < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base) :
    mode.round v₁ = mode.round v₂ := by
  set lo := ((n : ℤ) - 1 : R) * (2 : R) ^ e_base with hlo_def
  set hi := ((n : ℤ) + 1 : R) * (2 : R) ^ e_base with hhi_def
  have hE_pos : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0:R) < 2) _
  have hn_ge : (1 : ℤ) ≤ (n : ℤ) - 1 := by
    have : 0 < 2 ^ (FloatFormat.prec.toNat + 3) := Nat.pos_of_ne_zero (by positivity)
    omega
  have hlo_pos : 0 < lo := by
    rw [hlo_def]; exact mul_pos (by exact_mod_cast hn_ge) hE_pos
  have hn_prec : 2 ^ FloatFormat.prec.toNat < n := by
    calc 2 ^ FloatFormat.prec.toNat
        ≤ 2 ^ (FloatFormat.prec.toNat + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      _ < n := hn_large
  have hno_rep : noRepresentableIn lo hi := by
    intro f hfs hfm; rw [hlo_def, hhi_def]
    exact no_representable_in_odd_interval hn_odd hn_prec f hfs hfm
  -- Directional modes: use existing constancy lemmas
  cases mode with
  | Down =>
    show roundDown v₁ = roundDown v₂
    exact roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
  | Up =>
    show roundUp v₁ = roundUp v₂
    exact roundUp_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
  | TowardZero =>
    show roundTowardZero v₁ = roundTowardZero v₂
    exact roundTowardZero_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
  | NearestTiesToEven =>
    show roundNearestTiesToEven v₁ = roundNearestTiesToEven v₂
    have hrd : roundDown v₁ = roundDown v₂ :=
      roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
    have hru : roundUp v₁ = roundUp v₂ :=
      roundUp_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
    -- Both rnTE values are in {roundDown, roundUp}
    rcases rnTE_eq_roundDown_or_roundUp' v₁ with h1 | h1 <;>
    rcases rnTE_eq_roundDown_or_roundUp' v₂ with h2 | h2
    · -- (roundDown, roundDown)
      rw [h1, h2, hrd]
    · -- (roundDown, roundUp): use le_total
      rcases le_total v₁ v₂ with hle | hle
      · -- v₁ ≤ v₂: crossing case
        rw [h1, h2]
        by_cases hrDU : roundDown v₁ = roundUp v₁
        · exact hrDU.trans hru
        · exfalso; exact rnTE_no_crossing hn_odd hn_large
            (lt_trans hlo_pos hv₁_lo) (lt_trans hlo_pos hv₂_lo)
            hv₁_lo hv₁_hi hv₂_lo hv₂_hi hno_rep hrd hru hrDU h1 h2
      · -- v₂ ≤ v₁: mono gives ru₂ ≤ rd₁ → rd = ru
        have hmono := roundNearestTE_mono hle
        rw [h2, h1] at hmono  -- roundUp v₂ ≤ roundDown v₁
        rw [hrd] at hmono  -- roundUp v₂ ≤ roundDown v₂
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₂) hmono
        rw [h1, h2]; exact hrd.trans heq
    · -- (roundUp, roundDown): use le_total
      rcases le_total v₁ v₂ with hle | hle
      · -- v₁ ≤ v₂: mono gives ru₁ ≤ rd₂ → rd = ru
        have hmono := roundNearestTE_mono hle
        rw [h1, h2] at hmono  -- roundUp v₁ ≤ roundDown v₂
        rw [← hrd] at hmono  -- roundUp v₁ ≤ roundDown v₁
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₁) hmono
        rw [h1, h2, ← heq, hrd]
      · -- v₂ ≤ v₁: crossing case (symmetric)
        rw [h1, h2]
        by_cases hrDU : roundDown v₂ = roundUp v₂
        · exact hru.trans hrDU.symm
        · exfalso; exact rnTE_no_crossing hn_odd hn_large
            (lt_trans hlo_pos hv₂_lo) (lt_trans hlo_pos hv₁_lo)
            hv₂_lo hv₂_hi hv₁_lo hv₁_hi hno_rep hrd.symm hru.symm hrDU h2 h1
    · -- (roundUp, roundUp)
      rw [h1, h2, hru]
  | NearestTiesAwayFromZero =>
    show roundNearestTiesAwayFromZero v₁ = roundNearestTiesAwayFromZero v₂
    have hrd : roundDown v₁ = roundDown v₂ :=
      roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
    have hru : roundUp v₁ = roundUp v₂ :=
      roundUp_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
    rcases rnTA_eq_roundDown_or_roundUp' v₁ with h1 | h1 <;>
    rcases rnTA_eq_roundDown_or_roundUp' v₂ with h2 | h2
    · rw [h1, h2, hrd]
    · rcases le_total v₁ v₂ with hle | hle
      · -- crossing case: TA, h1=rd, h2=ru, v₁≤v₂
        rw [h1, h2]
        by_cases hrDU : roundDown v₁ = roundUp v₁
        · exact hrDU.trans hru
        · exfalso; exact rnTA_no_crossing hn_odd hn_large
            (lt_trans hlo_pos hv₁_lo) (lt_trans hlo_pos hv₂_lo)
            hv₁_lo hv₁_hi hv₂_lo hv₂_hi hno_rep hrd hru hrDU h1 h2
      · have hmono := roundNearestTA_mono hle
        rw [h2, h1] at hmono
        rw [hrd] at hmono
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₂) hmono
        rw [h1, h2]; exact hrd.trans heq
    · rcases le_total v₁ v₂ with hle | hle
      · have hmono := roundNearestTA_mono hle
        rw [h1, h2] at hmono
        rw [← hrd] at hmono
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₁) hmono
        rw [h1, h2, ← heq, hrd]
      · -- crossing case: TA, h1=ru, h2=rd, v₂≤v₁
        rw [h1, h2]
        by_cases hrDU : roundDown v₂ = roundUp v₂
        · exact hru.trans hrDU.symm
        · exfalso; exact rnTA_no_crossing hn_odd hn_large
            (lt_trans hlo_pos hv₂_lo) (lt_trans hlo_pos hv₁_lo)
            hv₂_lo hv₂_hi hv₁_lo hv₁_hi hno_rep hrd.symm hru.symm hrDU h2 h1
    · rw [h1, h2, hru]

/-! ## Full Correctness -/

/-- `fpDivFinite` correctly rounds the exact quotient for all rounding modes. -/
theorem fpDivFinite_correct {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp)
    (hb : b.m ≠ 0)
    (hquot : (a.toVal : R) / b.toVal ≠ 0) :
    fpDivFinite mode a b = mode.round ((a.toVal : R) / b.toVal) := by
  set q := (a.m * 2 ^ divShift) / b.m with hq_def
  set r := (a.m * 2 ^ divShift) % b.m with hr_def
  -- Case split: exact (r = 0) vs sticky (r ≠ 0)
  by_cases hr : r = 0
  · exact fpDivFinite_correct_exact mode a b hb hquot hr
  · -- Sticky bit case: mag = 2*q + 1
    set mag := 2 * q + 1 with hmag_def
    have hmag_ne : mag ≠ 0 := by omega
    set e_base := a.e - b.e - (2 * FloatFormat.prec + 2) - 1 with he_base_def
    -- fpDivFinite unfolds to roundIntSig mode (a.s ^^ b.s) mag e_base
    have hfpDiv_eq : fpDivFinite mode a b = roundIntSig mode (a.s ^^ b.s) mag e_base := by
      unfold fpDivFinite; simp only [hmag_def, he_base_def, hq_def]
      congr 1; simp [show a.m * 2 ^ divShift % b.m ≠ 0 from hr]
    -- roundIntSig_correct: roundIntSig = mode.round(intSigVal (a.s ^^ b.s) mag e_base)
    have hris := roundIntSig_correct (R := R) mode (a.s ^^ b.s) mag e_base hmag_ne
    rw [hfpDiv_eq, hris]
    -- Need: mode.round(sticky_val) = mode.round(exact_val)
    -- Strategy: both sticky_val and exact_val are in the odd interval ((mag-1)*E, (mag+1)*E)
    -- where E = 2^e_base, mag = 2*q+1 is odd, mag > 2^(prec+3)
    set E := (2 : R) ^ e_base with hE_def
    have hE_pos : (0 : R) < E := zpow_pos (by norm_num : (0:R) < 2) _
    -- mag is odd
    have hmag_odd : mag % 2 = 1 := by omega
    -- mag > 2^(prec+3)
    have ha_pos : 0 < a.m := by
      by_contra h; push_neg at h; apply hquot
      have : a.m = 0 := by omega
      unfold FiniteFp.toVal; rw [this]; simp
    have hb_bound : b.m < 2 ^ FloatFormat.prec.toNat := b.valid.2.2.1
    have hb_pos : 0 < b.m := Nat.pos_of_ne_zero hb
    have hq_lower : 2 ^ (FloatFormat.prec.toNat + 2) ≤ q := by
      rw [hq_def, Nat.le_div_iff_mul_le hb_pos]
      calc 2 ^ (FloatFormat.prec.toNat + 2) * b.m
          ≤ 2 ^ (FloatFormat.prec.toNat + 2) * 2 ^ FloatFormat.prec.toNat := by
            exact Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ divShift := by
            show 2 ^ (FloatFormat.prec.toNat + 2) * 2 ^ FloatFormat.prec.toNat =
              2 ^ (2 * FloatFormat.prec.toNat + 2)
            rw [← Nat.pow_add]; congr 1; omega
        _ ≤ a.m * 2 ^ divShift := Nat.le_mul_of_pos_left _ ha_pos
    have hmag_large : 2 ^ (FloatFormat.prec.toNat + 3) < mag := by
      have : 2 ^ (FloatFormat.prec.toNat + 3) = 2 * 2 ^ (FloatFormat.prec.toNat + 2) :=
        by rw [Nat.pow_succ]; ring
      omega
    -- Get the exact quotient formula
    have hexact_form := fpDivFinite_exact_quotient (R := R) a b hb
    set exact_val := (a.toVal : R) / b.toVal with hexact_def
    -- Remainder bounds: 0 < r < b.m
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hr
    have hr_lt : r < b.m := Nat.mod_lt _ hb_pos
    -- Both |sticky_val| and |exact_val| are in the odd interval ((mag-1)*E, (mag+1)*E)
    -- For sign=false (positive): direct. For sign=true (negative): via round_neg.
    set abs_sticky := (mag : R) * E with habs_sticky_def
    have hbm_pos : (0 : R) < (b.m : R) := Nat.cast_pos.mpr hb_pos
    set abs_exact := ((q : R) + (r : R) / (b.m : R)) * (2 * E) with habs_exact_def
    -- Sticky is in interval: (mag-1)*E < mag*E < (mag+1)*E
    have hs_lo : ((mag : ℤ) - 1 : R) * E < abs_sticky := by
      rw [habs_sticky_def]; apply mul_lt_mul_of_pos_right _ hE_pos
      exact_mod_cast (show (mag : ℤ) - 1 < mag from by omega)
    have hs_hi : abs_sticky < ((mag : ℤ) + 1 : R) * E := by
      rw [habs_sticky_def]; apply mul_lt_mul_of_pos_right _ hE_pos
      exact_mod_cast (show (mag : ℤ) < mag + 1 from by omega)
    -- Exact is in interval
    have he_lo : ((mag : ℤ) - 1 : R) * E < abs_exact := by
      rw [habs_exact_def]
      have hmag_sub : ((mag : ℤ) - 1 : R) = 2 * (q : R) := by
        rw [hmag_def]; push_cast; ring
      rw [hmag_sub]
      have hq_lt : (q : R) < (q : R) + (r : R) / (b.m : R) :=
        lt_add_of_pos_right _ (div_pos (Nat.cast_pos.mpr hr_pos) hbm_pos)
      calc 2 * (q : R) * E = (q : R) * (2 * E) := by ring
        _ < ((q : R) + (r : R) / (b.m : R)) * (2 * E) :=
            mul_lt_mul_of_pos_right hq_lt (by linarith)
    have he_hi : abs_exact < ((mag : ℤ) + 1 : R) * E := by
      rw [habs_exact_def]
      have hmag_add : ((mag : ℤ) + 1 : R) = 2 * ((q : R) + 1) := by
        rw [hmag_def]; push_cast; ring
      rw [hmag_add]
      have hr_bound : (r : R) / (b.m : R) < 1 := by
        rw [div_lt_one hbm_pos]; exact_mod_cast hr_lt
      calc ((q : R) + (r : R) / (b.m : R)) * (2 * E)
          < ((q : R) + 1) * (2 * E) :=
            mul_lt_mul_of_pos_right (by linarith) (by linarith)
        _ = 2 * ((q : R) + 1) * E := by ring
    -- round_eq_on_odd_interval for positive values
    have hround_pos : ∀ m : RoundingMode, m.round abs_sticky = m.round abs_exact :=
      fun m => round_eq_on_odd_interval m hmag_odd hmag_large hs_lo hs_hi he_lo he_hi
    -- Connect sticky_val and exact_val via sign
    -- Both abs values are positive (needed for ne proofs and positivity)
    have hq_ge_one : 1 ≤ q := le_trans (Nat.one_le_two_pow) hq_lower
    have hmag_ge_two : (2 : ℤ) ≤ mag := by exact_mod_cast (show 2 ≤ mag from by omega)
    have hlo_E_pos : (0 : R) < ((mag : ℤ) - 1 : R) * E :=
      mul_pos (by exact_mod_cast (show (0 : ℤ) < (mag : ℤ) - 1 from by omega)) hE_pos
    have habs_pos : 0 < abs_sticky := lt_trans hlo_E_pos hs_lo
    have habs_exact_pos : 0 < abs_exact := lt_trans hlo_E_pos he_lo
    have habs_ne : abs_sticky ≠ 0 := ne_of_gt habs_pos
    have habs_exact_ne : abs_exact ≠ 0 := ne_of_gt habs_exact_pos
    -- Key exponent identity: 2^(a.e - b.e - (2p+2)) = 2 * E
    have h2E : (2 : R) ^ (a.e - b.e - (2 * ↑FloatFormat.prec + 2)) = 2 * E := by
      rw [hE_def, show a.e - b.e - (2 * ↑FloatFormat.prec + 2) = e_base + 1 from by
        rw [he_base_def]; omega]
      rw [zpow_add₀ (by norm_num : (2:R) ≠ 0), zpow_one]; ring
    -- Connect intSigVal and exact_val to ±abs values via sign
    -- Goal: mode.round (intSigVal (a.s ^^ b.s) mag e_base) = mode.round exact_val
    have hexact_form : (a.toVal : R) / b.toVal =
        (if (a.s ^^ b.s) = true then -1 else (1 : R)) *
        ((q : R) + (r : R) / (b.m : R)) *
        (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2)) :=
      fpDivFinite_exact_quotient (R := R) a b hb
    cases hsxor : (a.s ^^ b.s) with
    | false =>
      have hsv : intSigVal (R := R) false mag e_base = abs_sticky := by
        unfold intSigVal; simp [habs_sticky_def, hE_def]
      have hev : exact_val = abs_exact := by
        rw [hexact_def, hexact_form, hsxor]
        simp [habs_exact_def, h2E]
      rw [hsv, hev]; exact hround_pos mode
    | true =>
      have hsv : intSigVal (R := R) true mag e_base = -abs_sticky := by
        unfold intSigVal; simp [habs_sticky_def, hE_def]
      have hev : exact_val = -abs_exact := by
        rw [hexact_def, hexact_form, hsxor]
        simp [habs_exact_def, h2E]; ring
      rw [hsv, hev, RoundingMode.round_neg mode abs_sticky habs_ne,
          RoundingMode.round_neg mode abs_exact habs_exact_ne]
      congr 1; exact hround_pos mode.conjugate

end Div
