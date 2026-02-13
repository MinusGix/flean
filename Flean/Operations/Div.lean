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

/-- Euclidean quotient used in `fpDivFinite` after scaling the dividend by `2^divShift`. -/
abbrev divQ (a b : FiniteFp) : ℕ := (a.m * 2 ^ divShift) / b.m

/-- Euclidean remainder used in `fpDivFinite` after scaling the dividend by `2^divShift`. -/
abbrev divR (a b : FiniteFp) : ℕ := (a.m * 2 ^ divShift) % b.m

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
  letI : RModeExec := rModeExecOf mode
  roundIntSigM sign mag e_base

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
    (a.toVal : R) / b.toVal =
    (if (a.s ^^ b.s) = true then -1 else (1 : R)) *
      ((divQ a b : R) + (divR a b : R) / (b.m : R)) *
      (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2)) := by
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  have hb_pos : (0 : R) < (b.m : R) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
  have hb_ne : (b.m : R) ≠ 0 := ne_of_gt hb_pos
  -- Euclidean division: a.m * 2^shift = b.m * q + r
  have hdiv_eq : a.m * 2 ^ divShift = b.m * divQ a b + divR a b := by
    unfold divQ divR
    exact (Nat.div_add_mod _ _).symm
  -- Cast to R: b.m * q + r = a.m * 2^divShift
  have hcast : (b.m : R) * (divQ a b : R) + (divR a b : R) = (a.m : R) * (2 : R) ^ (divShift : ℕ) := by
    have hnat : (b.m * divQ a b + divR a b : ℕ) = a.m * 2 ^ divShift := hdiv_eq.symm
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
    simp only [divQ, divR, hexact, hq_zero, Nat.cast_zero, zero_div, add_zero, mul_zero, zero_mul] at hexact_form
    exact hexact_form
  have hmag_ne : 2 * q ≠ 0 := by omega
  -- intSigVal equals exact quotient when r = 0
  have hbridge : intSigVal (R := R) (a.s ^^ b.s) (2 * q)
      (a.e - b.e - (2 * FloatFormat.prec + 2) - 1) = (a.toVal : R) / b.toVal := by
    have hexact_form := fpDivFinite_exact_quotient (R := R) a b hb
    have hq_fold : divQ a b = q := by rw [divQ, hq_def]
    simp only [divQ, divR, hexact, hq_fold, Nat.cast_zero, zero_div, add_zero] at hexact_form
    rw [hexact_form]
    unfold intSigVal
    -- (2*q) * 2^(e - 1) = q * 2^e
    have h2q : (↑(2 * q) : R) = 2 * (q : R) := by push_cast; ring
    have hexp : (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2) - 1) =
        (2 : R) ^ (a.e - b.e - (2 * FloatFormat.prec + 2)) / 2 := by
      rw [zpow_sub₀ (by norm_num : (2:R) ≠ 0), zpow_one]
    split_ifs <;> rw [h2q, hexp] <;> ring
  -- Unfold and apply generic roundIntSigM correctness
  show @roundIntSigM _ (rModeExecOf mode) (a.s ^^ b.s)
    (2 * q + (if (a.m * 2 ^ divShift) % b.m = 0 then 0 else 1))
    (a.e - b.e - (2 * FloatFormat.prec + 2) - 1) = _
  rw [hmag_eq, roundIntSigM_correct (R := R) mode _ _ _ hmag_ne]
  rw [hbridge]

/-! ## Full Correctness -/

-- Note: The interval-constancy lemmas (no_representable_in_odd_interval,
-- round_eq_on_odd_interval, etc.) have been extracted to Flean.Rounding.OddInterval.

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
  · -- Sticky bit case: use sticky_roundIntSig_eq_round
    set e_base := a.e - b.e - (2 * FloatFormat.prec + 2) - 1 with he_base_def
    -- fpDivFinite unfolds to roundIntSigM (a.s ^^ b.s) (2*q+1) e_base
    have hfpDiv_eq : fpDivFinite mode a b =
        @roundIntSigM _ (rModeExecOf mode) (a.s ^^ b.s) (2 * q + 1) e_base := by
      unfold fpDivFinite; simp only [he_base_def, hq_def]
      congr 1; simp [show a.m * 2 ^ divShift % b.m ≠ 0 from hr]
    rw [hfpDiv_eq]
    -- q ≥ 2^(prec+2) (operation-specific bound)
    have ha_pos : 0 < a.m := by
      by_contra h; push_neg at h; apply hquot
      have : a.m = 0 := by omega
      unfold FiniteFp.toVal; rw [this]; simp
    have hb_pos : 0 < b.m := Nat.pos_of_ne_zero hb
    have hb_bound : b.m < 2 ^ FloatFormat.prec.toNat := b.valid.2.2.1
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
    -- Remainder bounds
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hr
    have hr_lt : r < b.m := Nat.mod_lt _ hb_pos
    have hbm_pos : (0 : R) < (b.m : R) := Nat.cast_pos.mpr hb_pos
    -- abs_exact = |(a.toVal / b.toVal)| in the interval (2q·E, 2(q+1)·E)
    set E := (2 : R) ^ e_base with hE_def
    have hE_pos : (0 : R) < E := zpow_pos (by norm_num : (0:R) < 2) _
    set abs_exact := ((q : R) + (r : R) / (b.m : R)) * (2 * E) with habs_exact_def
    have he_lo : (2 * (q : R)) * E < abs_exact := by
      rw [habs_exact_def]
      calc 2 * (q : R) * E = (q : R) * (2 * E) := by ring
        _ < ((q : R) + (r : R) / (b.m : R)) * (2 * E) :=
            mul_lt_mul_of_pos_right
              (lt_add_of_pos_right _ (div_pos (Nat.cast_pos.mpr hr_pos) hbm_pos))
              (by linarith)
    have he_hi : abs_exact < (2 * ((q : R) + 1)) * E := by
      rw [habs_exact_def]
      calc ((q : R) + (r : R) / (b.m : R)) * (2 * E)
          < ((q : R) + 1) * (2 * E) :=
            mul_lt_mul_of_pos_right
              (by linarith [show (r : R) / (b.m : R) < 1 from
                (div_lt_one hbm_pos).mpr (by exact_mod_cast hr_lt)])
              (by linarith)
        _ = 2 * ((q : R) + 1) * E := by ring
    -- Apply shared sticky-bit lemma
    rw [sticky_roundIntSig_eq_round (R := R) (mode := mode) (sign := (a.s ^^ b.s)) (q := q)
      (e_base := e_base) (hq_lower := hq_lower) (abs_exact := abs_exact)
      (h_exact_in := ⟨he_lo, he_hi⟩)]
    -- Bridge: if sign then -abs_exact else abs_exact = exact_val
    have h2E : (2 : R) ^ (a.e - b.e - (2 * ↑FloatFormat.prec + 2)) = 2 * E := by
      rw [hE_def, show a.e - b.e - (2 * ↑FloatFormat.prec + 2) = e_base + 1 from by omega]
      rw [zpow_add₀ (by norm_num : (2:R) ≠ 0), zpow_one]; ring
    have hexact_signed : (a.toVal : R) / b.toVal =
        (if (a.s ^^ b.s) = true then -1 else (1 : R)) * abs_exact := by
      have := fpDivFinite_exact_quotient (R := R) a b hb
      simp only [divQ, divR, ← hq_def, ← hr_def] at this
      rw [this, habs_exact_def, h2E]; ring
    congr 1; rw [hexact_signed]
    cases (a.s ^^ b.s) <;> simp

end Div
