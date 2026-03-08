import Flean.Operations.MulPow2
import Flean.Operations.ExactInt

/-! # IEEE 754-2019 §5.3.3: logB and scaleB

- `logB(x)`: Returns the unbiased exponent of x as a signed integer.
  For finite nonzero x, `logB(x) = ⌊log₂|x|⌋`.
  Special cases: `logB(NaN) = NaN`, `logB(±∞) = +∞`, `logB(±0) = -∞`.
  (IEEE specifies logB(±0) signals divisionByZero, but we model just the value.)

- `scaleB(x, N)`: Returns `x × 2^N` with the result rounded.
  Special cases: `scaleB(NaN, _) = NaN`, `scaleB(±∞, _) = ±∞`, `scaleB(±0, _) = ±0`.
  For finite nonzero x, the result is `round(x × 2^N)`.
-/

section LogBScaleB

variable [FloatFormat]

/-! ## logB -/

/-- Extended `logB`: returns the unbiased exponent as `ℤ` for finite nonzero inputs,
or an `Fp` special value (NaN, ±∞) for special inputs. This is the proof-friendly version;
see `Fp.logB` for the IEEE 754-2019 operation that returns an `Fp`. -/
def Fp.logBExt (x : Fp) : ℤ ⊕ Fp :=
  match x with
  | .NaN => .inr .NaN
  | .infinite _ => .inr (.infinite false)  -- +∞
  | .finite f =>
    if f.m = 0 then .inr (.infinite true)  -- -∞ (division by zero)
    else .inl (Int.log 2 |(f.toVal : ℚ)|)

/-- `logBExt` on a finite nonzero float returns the floor of log₂|x|. -/
theorem Fp.logBExt_finite_nonzero (f : FiniteFp) (hm : f.m ≠ 0) :
    Fp.logBExt (.finite f) = .inl (Int.log 2 |(f.toVal : ℚ)|) := by
  simp [Fp.logBExt, hm]

/-- `logBExt` on NaN returns NaN. -/
@[simp] theorem Fp.logBExt_nan : Fp.logBExt .NaN = .inr .NaN := rfl

/-- `logBExt` on ±∞ returns +∞. -/
@[simp] theorem Fp.logBExt_infinite (b : Bool) : Fp.logBExt (.infinite b) = .inr (.infinite false) := rfl

/-- `logBExt` on ±0 returns -∞. -/
theorem Fp.logBExt_zero : Fp.logBExt (.finite (0 : FiniteFp)) = .inr (.infinite true) := by
  simp [Fp.logBExt, FiniteFp.zero_def]

/-- IEEE 754-2019 `logB`: returns the unbiased exponent of a floating-point value as an `Fp`.

For finite nonzero x, this is `⌊log₂|x|⌋` rounded to the float format.
Special cases: `logB(NaN) = NaN`, `logB(±∞) = +∞`, `logB(±0) = -∞`.
(IEEE specifies logB(±0) signals divisionByZero, but we model just the value.)

For well-formed formats, the integer result is always exactly representable,
so the rounding is a no-op in practice. -/
def Fp.logB [RMode ℚ] [RModeExec] (x : Fp) : Fp :=
  match x.logBExt with
  | .inl z => RMode.round ((z : ℚ))
  | .inr fp => fp

/-- `logB` on a finite nonzero float rounds the floor of log₂|x| to an Fp. -/
theorem Fp.logB_finite_nonzero [RMode ℚ] [RModeExec] (f : FiniteFp) (hm : f.m ≠ 0) :
    Fp.logB (.finite f) = RMode.round ((Int.log 2 |(f.toVal : ℚ)| : ℤ) : ℚ) := by
  simp [Fp.logB, Fp.logBExt, hm]

/-- `logB` on NaN returns NaN. -/
@[simp] theorem Fp.logB_nan [RMode ℚ] [RModeExec] : (Fp.NaN).logB = .NaN := rfl

/-- `logB` on ±∞ returns +∞. -/
@[simp] theorem Fp.logB_infinite [RMode ℚ] [RModeExec] (b : Bool) :
    Fp.logB (.infinite b) = .infinite false := rfl

/-- `logB` on ±0 returns -∞. -/
theorem Fp.logB_zero [RMode ℚ] [RModeExec] :
    Fp.logB (.finite (0 : FiniteFp)) = .infinite true := by
  simp [Fp.logB, Fp.logBExt, FiniteFp.zero_def]

/-! ## logBInt: integer-valued logB for finite nonzero inputs -/

/-- Integer-valued `logB` for finite nonzero inputs: `⌊log₂|x.toVal|⌋`.
This is the common case used in error analysis. -/
def FiniteFp.logBInt (f : FiniteFp) : ℤ :=
  Int.log 2 |(f.toVal : ℚ)|

/-- `logBInt` gives the floor of log₂|toVal|. -/
theorem FiniteFp.logBInt_eq (f : FiniteFp) :
    f.logBInt = Int.log 2 |(f.toVal : ℚ)| := rfl

/-- For normal floats (any sign), `logBInt f = f.e`. -/
theorem FiniteFp.logBInt_normal (f : FiniteFp) (hm : 0 < f.m) (hn : f.isNormal) :
    f.logBInt = f.e := by
  unfold logBInt
  -- |f.toVal| = f.m * 2^(f.e - prec + 1) regardless of sign
  have hab : |(f.toVal : ℚ)| = (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by
    rw [← FiniteFp.toVal_mag_toVal_abs (R := ℚ)]
    simp [FiniteFp.toVal_mag, FloatFormat.radix_val_eq_two]
  rw [hab]
  -- f.m ∈ [2^(prec-1), 2^prec), so f.m * 2^(e - prec + 1) ∈ [2^e, 2^(e+1))
  have hm_lower : 2 ^ (FloatFormat.prec - 1).toNat ≤ f.m := by
    unfold FiniteFp.isNormal _root_.isNormal at hn; exact hn.1
  have hm_upper := f.valid.2.2.1
  have hval_pos : (0 : ℚ) < (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by positivity
  have hle : (2 : ℚ) ^ f.e ≤ (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by
    calc (2 : ℚ) ^ f.e
        = (2 : ℚ) ^ (FloatFormat.prec - 1).toNat * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by
          rw [← zpow_natCast (2 : ℚ), FloatFormat.prec_sub_one_toNat_eq, two_zpow_mul]; congr 1; ring
      _ ≤ (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hm_lower
  have hlt : (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) < (2 : ℚ) ^ (f.e + 1) := by
    calc (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
        < (2 : ℚ) ^ FloatFormat.prec.toNat * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by
          apply mul_lt_mul_of_pos_right _ (by positivity)
          exact_mod_cast hm_upper
      _ = (2 : ℚ) ^ (f.e + 1) := by
          rw [← zpow_natCast (2 : ℚ), Int.toNat_of_nonneg (by fomega), two_zpow_mul]; congr 1; ring
  have h1 : f.e ≤ Int.log 2 ((f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hval_pos).mp hle
  have h2 : Int.log 2 ((f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)) < f.e + 1 :=
    (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hval_pos).mp hlt
  omega

/-! ## scaleB -/

/-- IEEE 754-2019 `scaleB`: multiply a floating-point value by `2^N`.

For finite nonzero x, this computes `round(x × 2^N)`. For special values,
the result follows IEEE semantics: NaN→NaN, ±∞→±∞, ±0→±0.

Unlike `fpMul_pow2_exact`, this handles the full `Fp` type and doesn't require
that the result exponent stays in range (overflow/underflow are handled by rounding). -/
def Fp.scaleB [RMode ℚ] [RModeExec] (x : Fp) (N : ℤ) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite b => .infinite b
  | .finite f =>
    if f.m = 0 then .finite f  -- ±0 → ±0
    else RMode.round ((f.toVal : ℚ) * (2 : ℚ) ^ N)

@[simp] theorem Fp.scaleB_nan [RMode ℚ] [RModeExec] (N : ℤ) :
    Fp.scaleB .NaN N = .NaN := rfl

@[simp] theorem Fp.scaleB_infinite [RMode ℚ] [RModeExec] (b : Bool) (N : ℤ) :
    Fp.scaleB (.infinite b) N = .infinite b := rfl

theorem Fp.scaleB_zero [RMode ℚ] [RModeExec] (N : ℤ) :
    Fp.scaleB (.finite (0 : FiniteFp)) N = .finite 0 := by
  simp [Fp.scaleB, FiniteFp.zero_def]

theorem Fp.scaleB_neg_zero [RMode ℚ] [RModeExec] (N : ℤ) :
    Fp.scaleB (.finite (-0 : FiniteFp)) N = .finite (-0) := by
  simp [Fp.scaleB, FiniteFp.neg_def, FiniteFp.zero_def]

/-- `scaleB` of a finite nonzero float applies rounding to `x × 2^N`. -/
theorem Fp.scaleB_finite_nonzero [RMode ℚ] [RModeExec] (f : FiniteFp) (N : ℤ) (hm : f.m ≠ 0) :
    Fp.scaleB (.finite f) N = RMode.round ((f.toVal : ℚ) * (2 : ℚ) ^ N) := by
  simp [Fp.scaleB, hm]

/-- When the result exponent stays in range, `scaleB` produces an exact result. -/
theorem Fp.scaleB_exact [RMode ℚ] [RModeExec] [RoundIntSigMSound ℚ] [RModeIdem ℚ]
    (f : FiniteFp) (N : ℤ) (hm : 0 < f.m) (hfs : f.s = false)
    (he_lo : f.e + N ≥ FloatFormat.min_exp) (he_hi : f.e + N ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp, Fp.scaleB (.finite f) N = .finite g ∧
      (g.toVal : ℚ) = (f.toVal : ℚ) * (2 : ℚ) ^ N := by
  have hm_ne : f.m ≠ 0 := hm.ne'
  rw [Fp.scaleB_finite_nonzero f N hm_ne]
  obtain ⟨g, hgs, hgv⟩ := mul_pow2_representable (R := ℚ) f N hm hfs he_lo he_hi
  refine ⟨g, ?_, hgv⟩
  rw [hgv.symm]
  exact RModeIdem.round_idempotent (R := ℚ) g (Or.inl hgs)

/-- `scaleB` with N = 0 is the identity on finite inputs. -/
theorem Fp.scaleB_zero_exp [RMode ℚ] [RModeExec] [RModeIdem ℚ] (f : FiniteFp) :
    Fp.scaleB (.finite f) 0 = .finite f := by
  by_cases hm : f.m = 0
  · -- f is zero
    simp [Fp.scaleB, hm]
  · rw [Fp.scaleB_finite_nonzero f 0 hm]
    simp only [zpow_zero, mul_one]
    by_cases hnz : f.notNegZero
    · exact RModeIdem.round_idempotent (R := ℚ) f hnz
    · -- f is neg-zero, but f.m ≠ 0 contradicts this
      simp [FiniteFp.notNegZero] at hnz
      omega

/-! ## logB–scaleB relationship -/

/-- For finite nonzero positive normal floats, `2^logBInt(f) ≤ |f.toVal|`. -/
theorem FiniteFp.zpow_logBInt_le (f : FiniteFp) (hm : f.m ≠ 0) :
    (2 : ℚ) ^ f.logBInt ≤ |(f.toVal : ℚ)| := by
  unfold logBInt
  have habs_pos : (0 : ℚ) < |(f.toVal : ℚ)| := by
    rw [abs_pos]
    exact FiniteFp.toVal_ne_zero_of_m_pos f (Nat.pos_of_ne_zero hm)
  exact Int.zpow_log_le_self (by norm_num) habs_pos

/-- For finite nonzero positive floats, `|f.toVal| < 2^(logBInt(f) + 1)`. -/
theorem FiniteFp.lt_zpow_logBInt_succ (f : FiniteFp) (hm : f.m ≠ 0) :
    |(f.toVal : ℚ)| < (2 : ℚ) ^ (f.logBInt + 1) := by
  unfold logBInt
  have habs_pos : (0 : ℚ) < |(f.toVal : ℚ)| := by
    rw [abs_pos]
    exact FiniteFp.toVal_ne_zero_of_m_pos f (Nat.pos_of_ne_zero hm)
  exact Int.lt_zpow_succ_log_self (by norm_num) |(f.toVal : ℚ)|

/-! ## logB exactness -/

/-- `logB` on a finite nonzero float is exact: the integer `⌊log₂|x|⌋` is exactly
representable, so rounding is a no-op. The hypothesis `h_bound` asks that the logB value
fits in the format; this holds for all standard IEEE 754 formats. -/
theorem Fp.logB_exact [RMode ℚ] [RModeExec] [RoundIntSigMSound ℚ] [RModeIdem ℚ]
    (f : FiniteFp) (hm : f.m ≠ 0)
    (h_bound : (Int.log 2 |(f.toVal : ℚ)|).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp, Fp.logB (.finite f) = .finite g ∧
      (g.toVal : ℚ) = (Int.log 2 |(f.toVal : ℚ)| : ℤ) := by
  rw [Fp.logB_finite_nonzero f hm]
  set n := Int.log 2 |(f.toVal : ℚ)|
  by_cases hn : n = 0
  · -- logB = 0: round(0) = round(toVal(+0)), exact by idempotency
    simp only [hn, Int.cast_zero]
    have : (0 : FiniteFp).notNegZero := Or.inl rfl
    exact ⟨0, by simpa using RModeIdem.round_idempotent (R := ℚ) 0 this, by simp⟩
  · obtain ⟨g, hgm, hgv⟩ := int_representable (R := ℚ) n hn h_bound h_exp
    refine ⟨g, ?_, hgv⟩
    rw [← hgv]
    exact RModeIdem.round_idempotent (R := ℚ) g (Or.inr hgm)

/-! ## scaleB overflow -/

/-- `scaleB` overflows to `+∞` when the scaled value exceeds the overflow threshold.
This holds for nearest-mode rounding policies. -/
theorem Fp.scaleB_overflow [RMode ℚ] [RModeExec] [RModeNearest ℚ]
    (f : FiniteFp) (N : ℤ) (hm : f.m ≠ 0)
    (hge : FloatFormat.overflowThreshold ℚ ≤ (f.toVal : ℚ) * (2 : ℚ) ^ N) :
    Fp.scaleB (.finite f) N = .infinite false := by
  rw [Fp.scaleB_finite_nonzero f N hm]
  exact RModeNearest.overflow_pos_inf _ hge

end LogBScaleB
