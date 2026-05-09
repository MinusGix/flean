import Flean.IntegerEquivalence.RoundToIntBits

/-! # FP ↔ Integer equivalence: trunc mid-exp (clear bottom k bits)

Phase 1.9 closure. Mid-exponent case for `Fp.trunc`: when the unbiased
exponent satisfies `0 ≤ e ≤ prec - 2`, the trunc operation clears the
bottom `k = prec - 1 - e` bits of the trailing significand.

Math:
* For normal `f` with `M ∈ [2^(prec-1), 2^prec)` and `0 ≤ e ≤ prec - 2`:
  `|f.toVal| = M · 2^(e - prec + 1) = M / 2^k` (in ℚ).
* `floor(|f.toVal|) = M / 2^k` (as a non-negative integer).
* `trunc(f.toVal) = sign · (M / 2^k)`.
* New significand `M_new = (M / 2^k) · 2^k`. The decoded value matches
  the truncated value:
  `M_new · 2^(e - prec + 1) = (M / 2^k) · 2^k · 2^(-k) = M / 2^k`.

The bit-level operator preserves sign and exponent; only the trailing
significand `T` changes (`T_new = T / 2^k · 2^k`, since `T = M - 2^sigBits`
and `2^sigBits` is a multiple of `2^k`). -/

namespace FiniteFp

variable [FloatFormat]

/-- For normal `f` with `0 ≤ f.e ≤ prec - 2`, the bottom-bit-clear value
`M_new = (f.m / 2^k) · 2^k` (where `k = prec - 1 - f.e`) is in the
normal range `[2^(prec-1), 2^prec)`. -/
private theorem M_new_isNormal_of_normal
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    let k := (FloatFormat.prec - 1 - f.e).toNat
    _root_.isNormal ((f.m / 2 ^ k) * 2 ^ k) := by
  set k := (FloatFormat.prec - 1 - f.e).toNat with hk_def
  have h_prec := FloatFormat.valid_prec
  have h_int : (FloatFormat.prec.toNat : ℤ) = FloatFormat.prec := FloatFormat.prec_toNat_eq
  have h_int_sub : ((FloatFormat.prec - 1).toNat : ℤ) = FloatFormat.prec - 1 :=
    FloatFormat.prec_sub_one_toNat_eq
  have hk_int : (k : ℤ) = FloatFormat.prec - 1 - f.e := by
    rw [hk_def]; exact Int.toNat_of_nonneg (by omega)
  have hk_le_prec_sub_one : k ≤ (FloatFormat.prec - 1).toNat := by omega
  have hm_lower : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f.m := hn.1
  have hm_upper : f.m < 2 ^ FloatFormat.prec.toNat := f.valid.2.2.1
  have h_two_k_pos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
  refine ⟨?_, ?_⟩
  · -- 2^(prec-1) ≤ M_new = (f.m / 2^k) * 2^k.
    -- f.m / 2^k ≥ 2^(prec-1-k) ⇒ M_new ≥ 2^(prec-1-k) * 2^k = 2^(prec-1).
    have h_div_ge : (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) ≤ f.m / 2 ^ k := by
      have h_prod : (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) * 2 ^ k
            = 2 ^ (FloatFormat.prec - 1).toNat := by
        rw [← pow_add]; congr 1; omega
      have h_lower_prod : (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) * 2 ^ k
            ≤ f.m := by rw [h_prod]; exact hm_lower
      exact (Nat.le_div_iff_mul_le h_two_k_pos).mpr h_lower_prod
    calc (2 : ℕ) ^ (FloatFormat.prec - 1).toNat
        = (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) * 2 ^ k := by
          rw [← pow_add]; congr 1; omega
      _ ≤ (f.m / 2 ^ k) * 2 ^ k :=
          Nat.mul_le_mul_right _ h_div_ge
  · -- M_new ≤ M < 2^prec.
    calc (f.m / 2 ^ k) * 2 ^ k ≤ f.m := Nat.div_mul_le_self f.m _
      _ < 2 ^ FloatFormat.prec.toNat := hm_upper

/-- Validity: `⟨f.s, f.e, M_new, _⟩` is a valid FiniteFp. -/
private theorem M_new_valid_of_normal
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    let k := (FloatFormat.prec - 1 - f.e).toNat
    IsValidFiniteVal f.e ((f.m / 2 ^ k) * 2 ^ k) := by
  refine ⟨f.valid.1, f.valid.2.1, ?_, Or.inl ?_⟩
  · calc (f.m / 2 ^ _) * 2 ^ _ ≤ f.m := Nat.div_mul_le_self f.m _
      _ < 2 ^ FloatFormat.prec.toNat := f.valid.2.2.1
  · exact M_new_isNormal_of_normal f hn he_lo he_hi

/-- **Structural form of `trunc` for the mid-exponent case.** For normal
`f` with `0 ≤ f.e ≤ prec - 2`, the FiniteFp form of `trunc(f)` has the
same sign and exponent, with significand reduced to `(f.m / 2^k) · 2^k`. -/
def truncMidExp_FiniteFp
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) : FiniteFp :=
  let k := (FloatFormat.prec - 1 - f.e).toNat
  ⟨f.s, f.e, (f.m / 2 ^ k) * 2 ^ k, M_new_valid_of_normal f hn he_lo he_hi⟩

@[simp] theorem truncMidExp_FiniteFp_s
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    (truncMidExp_FiniteFp f hn he_lo he_hi).s = f.s := rfl

@[simp] theorem truncMidExp_FiniteFp_e
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    (truncMidExp_FiniteFp f hn he_lo he_hi).e = f.e := rfl

@[simp] theorem truncMidExp_FiniteFp_m
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    (truncMidExp_FiniteFp f hn he_lo he_hi).m
      = (f.m / 2 ^ (FloatFormat.prec - 1 - f.e).toNat)
          * 2 ^ (FloatFormat.prec - 1 - f.e).toNat := rfl

/-- For normal `f` with `0 ≤ f.e ≤ prec - 2`, `|f.toVal| = M / 2^k` in ℚ. -/
private theorem toVal_abs_eq_div
    (f : FiniteFp)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    |(f.toVal : ℚ)| = (f.m : ℚ) / (2 : ℚ) ^ (FloatFormat.prec - 1 - f.e).toNat := by
  set k := (FloatFormat.prec - 1 - f.e).toNat with hk_def
  have h_prec := FloatFormat.valid_prec
  have hk_int : (k : ℤ) = FloatFormat.prec - 1 - f.e := by
    rw [hk_def]; exact Int.toNat_of_nonneg (by omega)
  rw [← FiniteFp.toVal_mag_toVal_abs (R := ℚ)]
  show FiniteFp.toVal_mag f (R := ℚ) = _
  unfold FiniteFp.toVal_mag
  rw [FloatFormat.radix_val_eq_two]
  push_cast
  rw [show (f.e - FloatFormat.prec + 1 : ℤ) = -(k : ℤ) from by omega]
  rw [zpow_neg, zpow_natCast]
  ring

/-- For normal `f` with `0 ≤ f.e ≤ prec - 2`, `f.toVal` lies in
`[-2^prec, 2^prec)` and is bounded away from zero. The integer
`floor(|f.toVal|)` equals `f.m / 2^k` (as a non-negative integer cast to ℤ). -/
private theorem floor_abs_toVal_eq_div
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    (⌊|(f.toVal : ℚ)|⌋ : ℤ)
      = ((f.m / 2 ^ (FloatFormat.prec - 1 - f.e).toNat : ℕ) : ℤ) := by
  rw [toVal_abs_eq_div f he_lo he_hi]
  -- Goal: ⌊(f.m : ℚ) / (2 : ℚ) ^ k⌋ = ((f.m / 2^k : ℕ) : ℤ)
  rw [show ((2 : ℚ) ^ (FloatFormat.prec - 1 - f.e).toNat : ℚ)
        = (((2 : ℕ) ^ (FloatFormat.prec - 1 - f.e).toNat : ℕ) : ℚ) from by
      push_cast; rfl]
  rw [Int.floor_div_natCast]
  rw [Int.floor_natCast]
  rfl

/-- `truncMidExp_FiniteFp f hn he_lo he_hi.toVal = sign · (f.m / 2^k)` in ℚ.

For positive `f` (`s = false`), the value is `+(f.m / 2^k)`. For negative
`f` (`s = true`), the value is `-(f.m / 2^k)`. -/
theorem truncMidExp_FiniteFp_toVal {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    (truncMidExp_FiniteFp f hn he_lo he_hi).toVal (R := R)
      = (if f.s then -1 else 1)
        * ((f.m / 2 ^ (FloatFormat.prec - 1 - f.e).toNat : ℕ) : R) := by
  set k := (FloatFormat.prec - 1 - f.e).toNat with hk_def
  set g := truncMidExp_FiniteFp f hn he_lo he_hi with hg_def
  have hg_e : g.e = f.e := rfl
  have hg_m : g.m = (f.m / 2 ^ k) * 2 ^ k := rfl
  have h_prec := FloatFormat.valid_prec
  have hk_int : (k : ℤ) = FloatFormat.prec - 1 - f.e := by
    rw [hk_def]; exact Int.toNat_of_nonneg (by omega)
  have h_exp_eq : (f.e - FloatFormat.prec + 1 : ℤ) = -(k : ℤ) := by omega
  -- (M_new : R) * 2^(-k) = (M / 2^k : R) since M_new = (M/2^k) * 2^k.
  have h_collapse :
      (((f.m / 2 ^ k) * 2 ^ k : ℕ) : R) * (2 : R) ^ (-(k : ℤ))
        = ((f.m / 2 ^ k : ℕ) : R) := by
    rw [zpow_neg, zpow_natCast]
    push_cast
    have h_pow_pos : (0 : R) < (2 : R) ^ k := by positivity
    field_simp
  have hg_s : g.s = f.s := rfl
  by_cases hs : f.s
  · -- Negative case
    have h_neg_g_pos : (-g).s = false := by
      simp [FiniteFp.neg_def, hg_s, hs]
    have h_neg_g_e : (-g).e = f.e := by
      simp [FiniteFp.neg_def, hg_e]
    have h_neg_g_m : (-g).m = (f.m / 2 ^ k) * 2 ^ k := by
      simp [FiniteFp.neg_def, hg_m]
    have h_g_neg : g.toVal (R := R) = -((-g).toVal) := by
      rw [FiniteFp.toVal_neg_eq_neg]; ring
    rw [h_g_neg, FiniteFp.toVal_pos_eq (-g) h_neg_g_pos, h_neg_g_e, h_neg_g_m]
    rw [if_pos hs, h_exp_eq, h_collapse]
    ring
  · -- Positive case
    rw [Bool.not_eq_true] at hs
    have hgs : g.s = false := by show f.s = false; exact hs
    rw [FiniteFp.toVal_pos_eq g hgs, hg_e, hg_m]
    rw [if_neg (by simp [hs]), h_exp_eq, h_collapse]
    ring

/-- The mid-exp truncated FiniteFp has positive `m` (it's normal, so
`m ≥ 2^(prec-1) > 0`). Used for `notNegZero`. -/
private theorem truncMidExp_FiniteFp_m_pos
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    0 < (truncMidExp_FiniteFp f hn he_lo he_hi).m := by
  have hM_normal : _root_.isNormal (truncMidExp_FiniteFp f hn he_lo he_hi).m :=
    M_new_isNormal_of_normal f hn he_lo he_hi
  have h1 : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat
        ≤ (truncMidExp_FiniteFp f hn he_lo he_hi).m := hM_normal.1
  have h2 : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat :=
    Nat.pos_of_ne_zero (by positivity)
  omega

/-- **Connection to `Fp.roundToIntTrunc`.** For normal `f` with
`0 ≤ f.e ≤ prec - 2`, `roundToIntTrunc` returns the structural
`truncMidExp_FiniteFp f hn he_lo he_hi`. -/
theorem roundToIntTrunc_finite_eq_truncMidExp_FiniteFp
    {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (f : FiniteFp) (hn : _root_.isNormal f.m)
    (he_lo : 0 ≤ f.e) (he_hi : f.e ≤ FloatFormat.prec - 2) :
    Fp.roundToIntTrunc (Fp.finite f)
      = Fp.finite (truncMidExp_FiniteFp f hn he_lo he_hi) := by
  set k := (FloatFormat.prec - 1 - f.e).toNat with hk_def
  set g := truncMidExp_FiniteFp f hn he_lo he_hi with hg_def
  -- f.m ≠ 0 (normal).
  have hf_m_pos : 0 < f.m := by
    have h1 : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f.m := hn.1
    have h2 : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat :=
      Nat.pos_of_ne_zero (by positivity)
    omega
  have hf_m_ne : f.m ≠ 0 := by omega
  -- g has positive m, so g.notNegZero.
  have hg_m_pos : 0 < g.m :=
    truncMidExp_FiniteFp_m_pos f hn he_lo he_hi
  have hg_nnz : g.notNegZero := Or.inr hg_m_pos
  -- f.m / 2^k > 0 (= integer truncate of |f.toVal|).
  have h_div_pos : 0 < f.m / 2 ^ k := by
    -- f.m / 2^k ≥ 2^(prec-1-k). With k ≤ prec-1, this is ≥ 1.
    have h_prec := FloatFormat.valid_prec
    have hk_int : (k : ℤ) = FloatFormat.prec - 1 - f.e := by
      rw [hk_def]; exact Int.toNat_of_nonneg (by omega)
    have h_int_sub : ((FloatFormat.prec - 1).toNat : ℤ) = FloatFormat.prec - 1 :=
      FloatFormat.prec_sub_one_toNat_eq
    have hk_le : k ≤ (FloatFormat.prec - 1).toNat := by omega
    have h_two_k_pos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
    have h_lower : (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) ≤ f.m / 2 ^ k := by
      have h_prod : (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) * 2 ^ k
            = 2 ^ (FloatFormat.prec - 1).toNat := by
        rw [← pow_add]; congr 1; omega
      have h_lower_prod : (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) * 2 ^ k
            ≤ f.m := by rw [h_prod]; exact hn.1
      exact (Nat.le_div_iff_mul_le h_two_k_pos).mpr h_lower_prod
    have h_pos_pow : (0 : ℕ) < (2 : ℕ) ^ ((FloatFormat.prec - 1).toNat - k) :=
      Nat.two_pow_pos _
    omega
  -- truncate(f.toVal) = ±(f.m / 2^k : ℤ). We compute this.
  have h_truncate_val : IntRound.truncate (f.toVal : ℚ)
        = (if f.s then -(f.m / 2 ^ k : ℕ) else (f.m / 2 ^ k : ℕ) : ℤ) := by
    by_cases hs : f.s
    · -- Negative: f.toVal ≤ 0, truncate = ⌈⌉.
      rw [if_pos hs]
      have h_neg_pos : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
      have h_toVal_nonneg : (0 : ℚ) ≤ ((-f).toVal : ℚ) :=
        FiniteFp.toVal_nonneg (-f) h_neg_pos
      rw [FiniteFp.toVal_neg_eq_neg] at h_toVal_nonneg
      have h_f_nonpos : (f.toVal : ℚ) ≤ 0 := by linarith
      -- Actually we need to handle the f.toVal < 0 vs = 0 case.
      have h_f_ne_zero : (f.toVal : ℚ) ≠ 0 := by
        intro h_eq
        have h_m_zero : f.m = 0 :=
          (FiniteFp.toVal_significand_zero_iff (R := ℚ)).mpr h_eq
        omega
      have h_f_lt_zero : (f.toVal : ℚ) < 0 :=
        lt_of_le_of_ne h_f_nonpos h_f_ne_zero
      rw [IntRound.truncate_of_neg h_f_lt_zero]
      -- ⌈f.toVal⌉ = -⌊-f.toVal⌋ = -⌊|f.toVal|⌋ = -(f.m / 2^k)
      rw [show (f.toVal : ℚ) = -|(f.toVal : ℚ)| from by rw [abs_of_neg h_f_lt_zero]; ring]
      rw [Int.ceil_neg]
      rw [floor_abs_toVal_eq_div f hn he_lo he_hi]
    · -- Positive
      rw [Bool.not_eq_true] at hs
      rw [if_neg (by simp [hs])]
      have h_toVal_nonneg : (0 : ℚ) ≤ (f.toVal : ℚ) :=
        FiniteFp.toVal_nonneg f hs
      rw [IntRound.truncate_of_nonneg h_toVal_nonneg]
      -- ⌊f.toVal⌋ = ⌊|f.toVal|⌋ = f.m / 2^k
      rw [show (f.toVal : ℚ) = |(f.toVal : ℚ)| from by rw [abs_of_nonneg h_toVal_nonneg]]
      rw [floor_abs_toVal_eq_div f hn he_lo he_hi]
  -- truncate is nonzero (positive in both branches modulo sign).
  have h_truncate_nz :
      (if f.s then -(f.m / 2 ^ k : ℕ) else (f.m / 2 ^ k : ℕ) : ℤ) ≠ 0 := by
    by_cases hs : f.s
    · rw [if_pos hs]; have : (0 : ℤ) < (f.m / 2 ^ k : ℕ) := by exact_mod_cast h_div_pos
      omega
    · rw [if_neg (by simp [hs])]; have : (0 : ℤ) < (f.m / 2 ^ k : ℕ) := by exact_mod_cast h_div_pos
      omega
  -- Apply Fp.roundToInt_finite_nonzero with intRound = truncate.
  unfold Fp.roundToIntTrunc
  rw [Fp.roundToInt_finite_nonzero IntRound.truncate f hf_m_ne]
  rw [h_truncate_val]
  rw [if_neg h_truncate_nz]
  -- Goal: roundDown (n : ℚ) = Fp.finite g, where n = ±(f.m / 2^k : ℕ).
  -- Use roundDown_idempotent at g.toVal.
  have hg_toVal : (g.toVal : ℚ)
        = (if f.s then -(f.m / 2 ^ k : ℕ) else (f.m / 2 ^ k : ℕ) : ℤ) := by
    rw [truncMidExp_FiniteFp_toVal f hn he_lo he_hi]
    by_cases hs : f.s
    · rw [if_pos hs, if_pos hs]
      push_cast
      change (-1 : ℚ) * ((f.m / 2 ^ k : ℕ) : ℚ)
              = -((f.m / 2 ^ k : ℕ) : ℚ)
      ring
    · rw [if_neg (by simp [hs]), if_neg (by simp [hs])]
      push_cast
      change (1 : ℚ) * ((f.m / 2 ^ k : ℕ) : ℚ)
              = ((f.m / 2 ^ k : ℕ) : ℚ)
      ring
  rw [← hg_toVal]
  exact roundDown_idempotent (R := ℚ) g hg_nnz

end FiniteFp

/-! ## Bit-level form of trunc for mid-exp -/

namespace Fp.FloatBits

variable [FloatFormat]

/-- **Bit-level trunc** for the mid-exponent case. Caller supplies `k`,
the number of low bits to clear (= `prec - 1 - b.FpExponent`). The
operation: keep sign and exponent, clear the bottom `k` bits of the
trailing significand. -/
def bitTruncMidExp (b : FloatBits) (k : ℕ) : FloatBits :=
  FloatBits.mk' b.toBitsTriple.sign b.toBitsTriple.exponent
    (BitVec.ofNat FloatFormat.significandBits
      ((b.toBitsTriple.significand.toNat / 2 ^ k) * 2 ^ k))

@[simp] theorem bitTruncMidExp_sign_bv (b : FloatBits) (k : ℕ) :
    (bitTruncMidExp b k).toBitsTriple.sign = b.toBitsTriple.sign :=
  construct_sign_eq_BitsTriple _ _ _

@[simp] theorem bitTruncMidExp_exponent_bv (b : FloatBits) (k : ℕ) :
    (bitTruncMidExp b k).toBitsTriple.exponent = b.toBitsTriple.exponent :=
  construct_exponent_eq_BitsTriple _ _ _

@[simp] theorem bitTruncMidExp_significand_bv (b : FloatBits) (k : ℕ) :
    (bitTruncMidExp b k).toBitsTriple.significand
      = BitVec.ofNat FloatFormat.significandBits
          ((b.toBitsTriple.significand.toNat / 2 ^ k) * 2 ^ k) :=
  construct_significand_eq_BitsTriple _ _ _

@[simp] theorem bitTruncMidExp_sign (b : FloatBits) (k : ℕ) :
    (bitTruncMidExp b k).sign = b.sign := by
  unfold FloatBits.sign; rw [bitTruncMidExp_sign_bv]

end Fp.FloatBits

/-! ## Bit-level decoded match -/

namespace Fp

/-- Helper: `(2 ^ sb + T) / 2 ^ k = 2 ^ (sb - k) + T / 2 ^ k` for `k ≤ sb`
and `T < 2 ^ sb`. -/
private theorem nat_pow_add_div (sb k T : ℕ) (hk_le : k ≤ sb) (hT : T < 2 ^ sb) :
    (2 ^ sb + T) / 2 ^ k = 2 ^ (sb - k) + T / 2 ^ k := by
  have h_pow_eq : (2 : ℕ) ^ sb = 2 ^ k * 2 ^ (sb - k) := by
    rw [← pow_add]; congr 1; omega
  rw [h_pow_eq]
  rw [show 2 ^ k * 2 ^ (sb - k) + T = T + 2 ^ k * 2 ^ (sb - k) from by ring]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
  ring

/-- Helper: for `T_new = (T.toNat / 2^k) * 2^k`,
`T_new.toNat = (T.toNat / 2^k) * 2^k` (mod is identity since the value
is less than 2^sigBits). -/
private theorem T_new_toNat [FloatFormat]
    (T : BitVec FloatFormat.significandBits) (k : ℕ) :
    (BitVec.ofNat FloatFormat.significandBits ((T.toNat / 2 ^ k) * 2 ^ k)).toNat
      = (T.toNat / 2 ^ k) * 2 ^ k := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  calc (T.toNat / 2 ^ k) * 2 ^ k ≤ T.toNat := Nat.div_mul_le_self T.toNat _
    _ < 2 ^ FloatFormat.significandBits := T.isLt

/-- **Bit-level decoded match for `bitTruncMidExp`.** For bit-normal `b`
with `0 ≤ b.FpExponent ≤ prec - 2`, decoding the bit-level operator gives
the structural FiniteFp form. -/
theorem ofBits_bitTruncMidExp_eq_truncMidExp_FiniteFp
    [StdFloatFormat]
    (b : FloatBits) (hn : b.isNormal)
    (he_lo : 0 ≤ b.FpExponent) (he_hi : b.FpExponent ≤ FloatFormat.prec - 2) :
    let f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal
        (FloatBits.notNaN_notInfinite b
          (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h))⟩
    let hf_b_normal : _root_.isNormal f_b.m := by
      refine ⟨?_, ?_⟩
      · show (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ b.FpSignificand
        rw [FloatBits.FpSignificand_def, if_neg hn.1]
        have hmsb : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).msb = true := by
          simp [BitVec.msb, BitVec.getMsbD, BitVec.ofBool_true, BitVec.getLsbD_append]
        have hge := BitVec.toNat_ge_of_msb_true hmsb
        have h_eq : 1 + FloatFormat.significandBits - 1 = FloatFormat.significandBits := by
          have := FloatFormat.significandBits_pos; omega
        rw [h_eq] at hge
        exact hge
      · show b.FpSignificand < (2 : ℕ) ^ FloatFormat.prec.toNat
        rw [FloatBits.FpSignificand_def, if_neg hn.1]
        have h_lt := ((BitVec.ofBool true) ++ b.toBitsTriple.significand).isLt
        exact h_lt.trans_eq (congr_arg (2 ^ ·) FloatFormat.one_plus_significandBits)
    let k := (FloatFormat.prec - 1 - b.FpExponent).toNat
    ofBits (FloatBits.bitTruncMidExp b k)
      = Fp.finite
          (FiniteFp.truncMidExp_FiniteFp f_b hf_b_normal he_lo he_hi) := by
  simp only
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h)
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b⟩ with hf_b_def
  set k := (FloatFormat.prec - 1 - b.FpExponent).toNat with hk_def
  -- Bookkeeping.
  have h_prec := FloatFormat.valid_prec
  have hk_int : (k : ℤ) = FloatFormat.prec - 1 - b.FpExponent := by
    rw [hk_def]; exact Int.toNat_of_nonneg (by omega)
  have h_int_sb : ((FloatFormat.significandBits : ℤ)) = FloatFormat.prec - 1 := by
    rw [FloatFormat.significandBits_eq, FloatFormat.prec_sub_one_toNat_eq]
  have hk_le_sb : k ≤ FloatFormat.significandBits := by
    rw [FloatFormat.significandBits_eq]
    have h_int_sub : ((FloatFormat.prec - 1).toNat : ℤ) = FloatFormat.prec - 1 :=
      FloatFormat.prec_sub_one_toNat_eq
    omega
  -- The bit-level result is finite (E unchanged from b, so non-NaN/non-Inf).
  have hbres_finite : (FloatBits.bitTruncMidExp b k).isFinite := by
    refine ⟨?_, ?_⟩
    · intro ⟨hE, _⟩
      apply hn.2
      unfold FloatBits.isExponentAllOnes at hE ⊢
      rwa [FloatBits.bitTruncMidExp_exponent_bv] at hE
    · intro ⟨hE, _⟩
      apply hn.2
      unfold FloatBits.isExponentAllOnes at hE ⊢
      rwa [FloatBits.bitTruncMidExp_exponent_bv] at hE
  -- E unchanged ⇒ FpExponent unchanged.
  have h_FpExp_eq : (FloatBits.bitTruncMidExp b k).FpExponent = b.FpExponent := by
    rw [FloatBits.FpExponent_def, FloatBits.FpExponent_def,
        FloatBits.bitTruncMidExp_exponent_bv]
  -- E ≠ 0 ⇒ FpSignificand uses the (1 ++ T_new) decoding.
  have h_FpSig_eq : (FloatBits.bitTruncMidExp b k).FpSignificand
        = b.FpSignificand / 2 ^ k * 2 ^ k := by
    rw [FloatBits.FpSignificand_def, FloatBits.bitTruncMidExp_exponent_bv,
        if_neg hn.1]
    rw [FloatBits.bitTruncMidExp_significand_bv]
    rw [BitVec.toNat_append]
    rw [T_new_toNat b.toBitsTriple.significand k]
    -- Goal: (1#1 <<< sigBits) ||| (T.toNat/2^k * 2^k) = (FpSignificand / 2^k) * 2^k
    -- where FpSignificand = 2^sigBits + T.toNat (since E ≠ 0).
    rw [FloatBits.FpSignificand_def, if_neg hn.1]
    rw [BitVec.toNat_append]
    have hT_lt : b.toBitsTriple.significand.toNat
          < 2 ^ FloatFormat.significandBits := b.toBitsTriple.significand.isLt
    have hT_div_lt : b.toBitsTriple.significand.toNat / 2 ^ k * 2 ^ k
          < 2 ^ FloatFormat.significandBits :=
      lt_of_le_of_lt (Nat.div_mul_le_self _ _) hT_lt
    rw [← Nat.shiftLeft_add_eq_or_of_lt hT_lt]
    rw [← Nat.shiftLeft_add_eq_or_of_lt hT_div_lt]
    have hbool : (BitVec.ofBool true).toNat = 1 := by simp
    rw [hbool]
    -- Goal: 1 <<< sigBits + (T.toNat/2^k * 2^k) = (1 <<< sigBits + T.toNat)/2^k * 2^k.
    rw [Nat.shiftLeft_eq, one_mul]
    rw [nat_pow_add_div FloatFormat.significandBits k _ hk_le_sb hT_lt]
    rw [Nat.add_mul]
    congr 1
    rw [← pow_add]; congr 1; omega
  -- Decode the bit-level result.
  rw [ofBits_eq_finite_of_isFinite _ hbres_finite]
  -- The decoded FiniteFp matches truncMidExp_FiniteFp f_b.
  congr 1
  apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · -- sign preserved
    show (FloatBits.bitTruncMidExp b k).sign = f_b.s
    rw [FloatBits.bitTruncMidExp_sign]
  · -- FpExponent preserved
    show (FloatBits.bitTruncMidExp b k).FpExponent = f_b.e
    exact h_FpExp_eq
  · -- FpSignificand = f_b.m / 2^k * 2^k
    show (FloatBits.bitTruncMidExp b k).FpSignificand
          = (f_b.m / 2 ^ k) * 2 ^ k
    exact h_FpSig_eq

/-! ## Headline: `trunc (ofBits b) = ofBits (bitTruncMidExp b k)` -/

/-- **Headline mid-exp bridge.** For bit-normal `b` with
`0 ≤ b.FpExponent ≤ prec - 2`, `Fp.trunc (ofBits b)` equals the bit-level
clear-bottom-bits result. Composes the value-level
`roundToIntTrunc_finite_eq_truncMidExp_FiniteFp` with the bit-level
decoded match `ofBits_bitTruncMidExp_eq_truncMidExp_FiniteFp`. -/
theorem trunc_ofBits_eq_ofBits_bitTruncMidExp
    [StdFloatFormat] {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (b : FloatBits) (hn : b.isNormal)
    (he_lo : 0 ≤ b.FpExponent) (he_hi : b.FpExponent ≤ FloatFormat.prec - 2) :
    let k := (FloatFormat.prec - 1 - b.FpExponent).toNat
    Fp.trunc (ofBits b) = ofBits (FloatBits.bitTruncMidExp b k) := by
  simp only
  -- Decode b.
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h)
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
    FloatBits.isFinite_validFloatVal hf_b⟩ with hf_b_def
  have hofb : ofBits b = Fp.finite f_b := ofBits_eq_finite_of_isFinite b hf_b
  -- f_b is value-level normal.
  have hf_b_normal : _root_.isNormal f_b.m := by
    show _root_.isNormal b.FpSignificand
    refine ⟨?_, ?_⟩
    · rw [FloatBits.FpSignificand_def, if_neg hn.1]
      have hmsb : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).msb = true := by
        simp [BitVec.msb, BitVec.getMsbD, BitVec.ofBool_true, BitVec.getLsbD_append]
      have hge := BitVec.toNat_ge_of_msb_true hmsb
      have h_eq : 1 + FloatFormat.significandBits - 1 = FloatFormat.significandBits := by
        have := FloatFormat.significandBits_pos; omega
      rw [h_eq] at hge
      exact hge
    · rw [FloatBits.FpSignificand_def, if_neg hn.1]
      have h_lt := ((BitVec.ofBool true) ++ b.toBitsTriple.significand).isLt
      exact h_lt.trans_eq (congr_arg (2 ^ ·) FloatFormat.one_plus_significandBits)
  -- Compose the two pieces.
  rw [hofb]
  show Fp.roundToIntTrunc (Fp.finite f_b) = _
  rw [FiniteFp.roundToIntTrunc_finite_eq_truncMidExp_FiniteFp
        (R := R) f_b hf_b_normal he_lo he_hi]
  exact (Fp.ofBits_bitTruncMidExp_eq_truncMidExp_FiniteFp b hn he_lo he_hi).symm

end Fp
